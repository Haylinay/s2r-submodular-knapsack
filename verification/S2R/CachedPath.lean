import S2R.AuxiliaryComplexity

namespace S2R.Instance
noncomputable section
open S2R.SelectionScan S2R.RAM
variable {n : ℕ} (I : Instance n)

/-- The greedy scan receives the maintained scalar prefix cost. Its
feasibility predicate performs no sum over the current set. -/
def cachedChoose (S : Selection n) (C : ℝ) : Result (Ground n) :=
  select (fun i => i ∉ S ∧ C+I.cost i ≤ I.budget) (fun i => I.density i S) I.itemList

theorem cachedChoose_correct (S : Selection n) (C : ℝ) (hC : C=I.totalCost S) :
    I.cachedChoose S C=I.scanChoose S := by
  have hp : (fun i => i ∉ S ∧ C+I.cost i ≤ I.budget)=(fun i => i ∈ I.available S) := by
    funext i
    apply propext
    rw [hC, I.available_cached]
  unfold cachedChoose scanChoose
  rw [hp]

/-- A sequential path builder carrying the cached cost explicitly. The
charged five operations include the scalar-cost update and the insertion. -/
def cachedPathRun (S : Selection n) (C : ℝ) : ℕ → Run (List (Selection n))
  | 0 => ⟨[S],2*n+2⟩
  | k+1 =>
    let next := I.cachedChoose S C
    let state := match next.choice with
      | none => (S,C)
      | some i => (insert i S,C+I.cost i)
    let r := cachedPathRun state.1 state.2 k
    ⟨S::r.value,r.operations+next.operations+(2*n+2)+5⟩

/-- The cache invariant is derived from the actual selected item and
maintained inductively. Both the path and the operation count are preserved. -/
theorem cachedPathRun_refines (S : Selection n) (C : ℝ) (hC : C=I.totalCost S) (k : ℕ) :
    I.cachedPathRun S C k=I.pathRun S k := by
  induction k generalizing S C with
  | zero => rfl
  | succ k ih =>
    rw [cachedPathRun, I.cachedChoose_correct S C hC]
    unfold pathRun
    cases he : (I.scanChoose S).choice with
    | none =>
      simp only
      rw [ih S C hC]
      simp only [he]
    | some i =>
      have hc : I.choose S=some i := by rw [← I.scanChoose_correct]; exact he
      have hi := (I.mem_available.mp (I.choose_spec hc).1).1
      have hcost : C+I.cost i=I.totalCost (insert i S) := by
        rw [I.totalCost_insert hi, hC]
        ring
      simp only
      rw [ih (insert i S) (C+I.cost i) hcost]
      simp only [he]

theorem cachedSeedPath_refines (a : Ground n) :
    I.cachedPathRun {a} (I.cost a) n=I.pathRun {a} n :=
  I.cachedPathRun_refines {a} (I.cost a) (I.totalCost_singleton a).symm n

end
end S2R.Instance
