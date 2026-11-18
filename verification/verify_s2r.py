"""Rebuild and audit the new S2R development without overstating its scope.

Default exit codes: 0 = all requested main results checked; 1 = build/audit
failure; 2 = checked components but required main results are still absent.
Use --components-only for a component CI check (exit 0 on component success).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

BASE = Path(__file__).resolve().parent
ROOT = BASE.parent
LAKE = os.environ.get("S2R_LAKE", "lake")
DIRECT_LEAN = os.environ.get("S2R_LEAN")
LEAN = [DIRECT_LEAN] if DIRECT_LEAN else [LAKE, "env", "lean"]
BUILD_LIB = BASE / ".lake/build/lib/lean"
AUDIT = BASE / "audit"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_MAIN = {
    "approximation_guarantee": "S2R.exactApproximationGuarantee",
    "streaming_row_fusion": "S2R.Instance.streamRow_fold",
    "streaming_best_record": "S2R.Instance.streamBest_spec",
    "owned_output_materialization": "S2R.Instance.materializeRecord_correct",
    "owned_output_correctness": "S2R.Instance.ownedImplementation_correct",
    "owned_output_feasibility": "S2R.Instance.ownedImplementation_feasible",
    "streaming_query_equality": "S2R.Instance.streamQueryCount_refines",
    "streaming_operation_bound": "S2R.Instance.ownedTimeImplementation_polynomial",
    "owned_output_space_bound": "S2R.Instance.ownedImplementation_space_polynomial",
    "owned_allocation_prefixes": "S2R.Instance.owned_all_allocation_prefixes",
    "streaming_joint_result": "S2R.Instance.s2r_verified_streaming",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def without_comments(source: str) -> str:
    """Remove nested Lean comments, preserving newlines and line numbers."""
    out = []
    index = depth = 0
    while index < len(source):
        if source.startswith("/-", index):
            depth += 1
            out.extend("  ")
            index += 2
        elif depth and source.startswith("-/", index):
            depth -= 1
            out.extend("  ")
            index += 2
        elif not depth and source.startswith("--", index):
            end = source.find("\n", index)
            if end < 0:
                end = len(source)
            out.extend(" " * (end - index))
            index = end
        else:
            char = source[index]
            out.append(char if not depth or char == "\n" else " ")
            index += 1
    if depth:
        raise ValueError("Unclosed comment")
    return "".join(out)


def declared_theorems(source: str) -> list[str]:
    namespace = []
    stack = []
    result = []
    for line in without_comments(source).splitlines():
        stripped = line.strip()
        match = re.match(r"namespace\s+(\S+)", stripped)
        if match:
            parts = match.group(1).split(".")
            namespace.extend(parts)
            stack.append(len(parts))
        elif re.match(r"(?:noncomputable\s+)?section(?:\s|$)", stripped):
            stack.append(0)
        elif re.match(r"end(?:\s|$)", stripped):
            if stack:
                count = stack.pop()
                if count:
                    del namespace[-count:]
        match = re.match(r"(?:@\[[^]]+\]\s*)?(?:theorem|lemma)\s+([\w']+)", stripped)
        if match:
            result.append(".".join(namespace + [match.group(1)]))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--components-only", action="store_true")
    parser.add_argument("--skip-import-recheck", action="store_true",
                        help="Skip --trust=0; audit theorem axioms without rechecking imports.")
    args = parser.parse_args()
    AUDIT.mkdir(exist_ok=True)
    BUILD_LIB.mkdir(parents=True, exist_ok=True)
    report = {
        "status": "RUNNING",
        "main_result_verified": False,
        "compiler_invocation": "direct Lean" if DIRECT_LEAN else "lake env lean",
        "import_recheck_trust_level": None if args.skip_import_recheck else 0,
        "required_main_results": {},
        "allowed_axioms": sorted(ALLOWED_AXIOMS),
        "modules": [],
        "theorems": {},
        "missing_proof_connections": [],
        "scope": {
            "cost_model": "Unit-cost exact-real RAM; array membership/read/write and bounded record operations; oracle internals, serialization and bit complexity excluded",
            "auxiliary_implementation": "One sorted order; erase each seed once; nonempty borrowed suffix jobs; fused threshold/sweep/record/max loop; terminal scalar reuse; copy a seed winner into the owned output buffer before releasing the cache; no global history table",
            "memory_model": "Abstract RAM words; explicit scoped allocation/release schedule; every event prefix checked; includes input cost cells, output buffer and path histories; excludes oracle-private storage and Lean evaluator heap",
            "not_claimed": ["Machine-code or Lean-evaluator runtime or heap", "Bit or byte complexity of exact real arithmetic", "Journal novelty or acceptance"],
        },
        "streaming_bounds": {
            "preferred_joint_theorem": "S2R.Instance.s2r_verified_streaming",
            "query_polynomial": "Q(n) <= n^3",
            "auxiliary_polynomial": "A(n) + 4*n^2 <= 75*n^3 + 46*n + 24",
            "peak_memory_polynomial_words": "P(n) <= n^2 + 8*n + 57",
            "uniform_n_ge_1": {"queries_cubic": 1, "auxiliary_cubic": 141, "peak_words_quadratic": 66},
            "cost_interpretation": "The abstract count includes row scans and at most one output copy per seed.",
            "bounds_optimality_claimed": False,
        },
    }
    paper = ROOT / "paper.tex"
    report["verifier_sha256"] = sha256(Path(__file__))
    report["lake_manifest_sha256"] = sha256(BASE / "lake-manifest.json")
    report["lean_toolchain_sha256"] = sha256(BASE / "lean-toolchain")
    if paper.exists():
        report["manuscript_sha256"] = sha256(paper)
    bibliography = ROOT / "references.bib"
    if bibliography.exists():
        report["bibliography_sha256"] = sha256(bibliography)
    start = time.monotonic()

    def save():
        report["elapsed_seconds"] = round(time.monotonic() - start, 3)
        (AUDIT / "verification_report.json").write_text(
            json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    def run(command: list[str], log: Path):
        before = time.monotonic()
        try:
            process = subprocess.run(command, cwd=BASE,
                                     text=True, encoding="utf-8", errors="replace",
                                     stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        except OSError as exc:
            process = subprocess.CompletedProcess(command, 1, str(exc))
        log.write_text(process.stdout, encoding="utf-8")
        return process, round(time.monotonic() - before, 3)

    version, _ = run(LEAN + ["--version"], AUDIT / "toolchain.log")
    if version.returncode:
        report["status"] = "TOOLCHAIN_UNAVAILABLE"
        report["error"] = version.stdout
        save()
        print(version.stdout, flush=True)
        return 1
    report["toolchain"] = version.stdout.strip()
    paths = {"S2R." + path.stem: path for path in (BASE / "S2R").glob("*.lean")}
    order, visited = [], set()

    def visit(module):
        if module in visited:
            return
        visited.add(module)
        source = paths[module].read_text(encoding="utf-8-sig")
        for dep in re.findall(r"^import\s+(S2R\.\w+)", source, re.M):
            if dep not in paths:
                raise ValueError(f"Missing local module {dep}")
            visit(dep)
        order.append(module)

    for module in sorted(paths):
        visit(module)
    all_theorems = []
    for module in order:
        path = paths[module]
        source = path.read_text(encoding="utf-8-sig")
        source_hash = sha256(path)
        code = without_comments(source)
        forbidden = re.search(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b", code)
        if forbidden:
            report["status"] = "REJECTED_FORBIDDEN_CONSTRUCT"
            report["error"] = f"{path.name}: {forbidden.group(0)}"
            save()
            print(report["error"], flush=True)
            return 1
        names = declared_theorems(source)
        all_theorems.extend(names)
        print(f"Checking {module} ({len(names)} theorems)...", flush=True)
        output = BUILD_LIB / module.replace(".", "/")
        output = output.with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        process, elapsed = run(LEAN + ["-o", str(output), str(path)],
                               AUDIT / (path.stem + ".log"))
        if sha256(path) != source_hash:
            report["status"] = "SOURCE_CHANGED_DURING_AUDIT"
            report["error"] = f"Source changed while compiling {module}; rerun the audit."
            save()
            print(report["error"], flush=True)
            return 1
        report["modules"].append({"module": module, "source_sha256": source_hash,
                                  "theorem_count": len(names), "exit_code": process.returncode,
                                  "elapsed_seconds": elapsed})
        if process.returncode or "declaration uses 'sorry'" in process.stdout:
            report["status"] = "BUILD_FAILED"
            report["error"] = process.stdout
            save()
            print(process.stdout, flush=True)
            return 1
        save()
    audit_source = AUDIT / "S2RAudit.lean"
    audit_source.write_text("import S2R.All\n\n" + "\n".join(
        "#print axioms " + name for name in all_theorems) + "\n", encoding="utf-8")
    command = LEAN.copy()
    if not args.skip_import_recheck:
        command.append("--trust=0")
    command.append(str(audit_source))
    print(f"Auditing axioms of {len(all_theorems)} theorems"
          + ("; rechecking imports at trust level 0..." if not args.skip_import_recheck else "..."),
          flush=True)
    process, elapsed = run(command, AUDIT / "axioms.log")
    report["axiom_audit_seconds"] = elapsed
    if process.returncode:
        report["status"] = "AXIOM_AUDIT_FAILED"
        report["error"] = process.stdout
        save()
        print(process.stdout, flush=True)
        return 1
    for name, axiom_text in re.findall(r"'([^\n]+)' depends on axioms:\s*\[([^]]*)\]", process.stdout):
        report["theorems"][name] = sorted(part.strip() for part in axiom_text.split(",") if part.strip())
    for name in re.findall(r"'([^\n]+)' does not depend on any axioms", process.stdout):
        report["theorems"][name] = []
    for name in all_theorems:
        if name not in report["theorems"]:
            raise ValueError(f"No axiom-audit output for {name}")
        extra = set(report["theorems"][name]) - ALLOWED_AXIOMS
        if extra:
            report["status"] = "UNEXPECTED_AXIOMS"
            report["error"] = {name: sorted(extra)}
            save()
            print(report["error"], flush=True)
            return 1
    for item in report["modules"]:
        if sha256(paths[item["module"]]) != item["source_sha256"]:
            report["status"] = "SOURCE_CHANGED_DURING_AUDIT"
            report["error"] = f"Source changed after compilation: {item['module']}; rerun the audit."
            save()
            print(report["error"], flush=True)
            return 1
    for path, key in ((paper, "manuscript_sha256"),
                      (bibliography, "bibliography_sha256")):
        if path.exists() and sha256(path) != report[key]:
            report["status"] = "SOURCE_CHANGED_DURING_AUDIT"
            report["error"] = f"{path.name} changed during the audit; rerun it."
            save()
            print(report["error"], flush=True)
            return 1
    report["required_main_results"] = {
        role: {"name": name, "present_and_checked": name in report["theorems"]}
        for role, name in REQUIRED_MAIN.items()
    }
    complete = all(item["present_and_checked"] for item in report["required_main_results"].values())
    report["main_result_verified"] = complete
    report["component_check_passed"] = True
    report["checked_theorem_count"] = len(all_theorems)
    report["status"] = "COMPLETE" if complete else "PARTIAL_MAIN_THEOREM_NOT_FORMALIZED"
    save()
    print(f"{report['status']}: {len(all_theorems)} checked theorems; "
          f"report: {AUDIT / 'verification_report.json'}", flush=True)
    return 0 if complete or args.components_only else 2


if __name__ == "__main__":
    sys.exit(main())
