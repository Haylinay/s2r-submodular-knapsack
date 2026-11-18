import S2R.GreedyImplementation
import S2R.Compression

/-! A cost semantics for the manuscript's unit-cost real-arithmetic RAM.

Sets are n-entry membership arrays; a membership test, a cell access/update,
an exact real arithmetic operation/comparison and a bounded record operation
cost one. Value-oracle calls are charged separately. The semantics does NOT
measure Lean's evaluator or the internal representation of `Finset` or `Real`.

The implementation uses a quadratic alternative to buckets: store the n+1
prefix membership arrays for the current seed, then temporarily insert and
remove at most two repair elements. Copying these arrays is explicitly charged.
Only the n individual item costs are insertion-sorted; rows of pair thresholds
are already sorted, as proved in RepairImplementation. Thus no pair-sort or
binary-search logarithm is hidden in the bound. -/
namespace S2R.RAM
noncomputable section

structure Run (α : Type*) where
  value : α
  operations : ℕ

/-- A read, predicate test, optional increment, and loop/record update. -/
def countTrue : List Bool → Run ℕ
  | [] => ⟨0,1⟩
  | b::bs => let r := countTrue bs
    ⟨(if b then 1 else 0)+r.value, r.operations+4⟩

theorem countTrue_correct (bs : List Bool) :
    (countTrue bs).value=(bs.filter id).length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [countTrue, ih, Nat.add_comm]
theorem countTrue_operations (bs : List Bool) :
    (countTrue bs).operations=4*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [countTrue, ih]; omega

/-- A membership read, cost read, addition and loop/record update. -/
def sumCells : List ℝ → Run ℝ
  | [] => ⟨0,1⟩
  | x::xs => let r := sumCells xs
    ⟨x+r.value,r.operations+4⟩
theorem sumCells_correct (xs : List ℝ) : (sumCells xs).value=xs.sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumCells, ih]
theorem sumCells_operations (xs : List ℝ) : (sumCells xs).operations=4*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumCells, ih]; omega

theorem filter_ofFn_bool {m : ℕ} (P : Fin m → Prop) [DecidablePred P] :
    ((List.ofFn (fun i => decide (P i))).filter id).length=S2R.OrderedSweep.initialCount P := by
  classical
  rw [List.ofFn_eq_map, List.filter_map, List.length_map]
  let L := (List.finRange m).filter (fun i => decide (P i))
  have hn : L.Nodup := (List.nodup_finRange m).filter _
  have he : L.toFinset=Finset.univ.filter P := by ext i; simp [L]
  change L.length = _
  rw [← List.toFinset_card_of_nodup hn, he]
  unfold OrderedSweep.initialCount
  congr 1
  ext i
  simp

def maxValues {α : Type*} (f : α → ℝ) : List α → Run ℝ
  | [] => ⟨0,1⟩
  | x::xs => let r := maxValues f xs
    ⟨max (f x) r.value,r.operations+4⟩

theorem maxValues_nonneg {α : Type*} (f : α → ℝ) (xs : List α) : 0 ≤ (maxValues f xs).value := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih => exact ih.trans (le_max_right _ _)
theorem maxValues_ge {α : Type*} (f : α → ℝ) {xs : List α} {x : α} (hx : x ∈ xs) :
    f x ≤ (maxValues f xs).value := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih hx).trans (le_max_right _ _)
theorem maxValues_le {α : Type*} (f : α → ℝ) (xs : List α) (M : ℝ)
    (hM : 0 ≤ M) (h : ∀ x ∈ xs, f x ≤ M) : (maxValues f xs).value ≤ M := by
  induction xs with
  | nil => exact hM
  | cons x xs ih =>
    exact max_le (h _ List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))
theorem maxValues_operations {α : Type*} (f : α → ℝ) (xs : List α) :
    (maxValues f xs).operations=4*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [maxValues, ih]; omega

end
end S2R.RAM

namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

/-- Store one membership-array snapshot at each step. The 2n+2 charge
copies n cells and writes its handle; five further operations update the
selected item and path metadata. Selection has its own recursive count. -/
def pathRun (S : Selection n) : ℕ → Run (List (Selection n))
  | 0 => ⟨[S],2*n+2⟩
  | k+1 => let next := I.scanChoose S
    let S' := match next.choice with | none => S | some i => insert i S
    let r := pathRun S' k
    ⟨S::r.value,r.operations+next.operations+(2*n+2)+5⟩

theorem iterate_step (S : Selection n) (k : ℕ) : I.iterate (I.step S) k=I.iterate S (k+1) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ, ih]

theorem pathRun_correct (S : Selection n) (k : ℕ) :
    (I.pathRun S k).value=List.ofFn (fun t : Fin (k+1) => I.iterate S t.val) := by
  induction k generalizing S with
  | zero => simp [pathRun, List.ofFn_succ]
  | succ k ih =>
    change S::(I.pathRun (I.scanStep S) k).value = _
    rw [ih]
    conv_rhs => rw [List.ofFn_succ]
    congr 1
    apply congrArg List.ofFn
    funext t
    rw [I.scanStep_correct, I.iterate_step]
    rfl

theorem pathRun_operations (S : Selection n) (k : ℕ) :
    (I.pathRun S k).operations=(2*n+2)+k*(22*n+8) := by
  induction k generalizing S with
  | zero => simp [pathRun]
  | succ k ih =>
    simp only [pathRun, ih, I.scanChoose_operations]
    ring

def absenceRun (a i : Ground n) : Run ℕ := by
  classical
  exact countTrue (List.ofFn (fun t : Fin (n+1) => decide (i ∉ I.prefixSet a t)))
theorem absenceRun_correct (a i : Ground n) : (I.absenceRun a i).value=I.absenceCount a i := by
  classical
  rw [absenceRun, countTrue_correct, filter_ofFn_bool]
  rfl
theorem absenceRun_operations (a i : Ground n) : (I.absenceRun a i).operations=4*(n+1)+1 := by
  simp [absenceRun, countTrue_operations]

def costRun (S : Selection n) : Run ℝ := by
  classical
  exact sumCells (List.ofFn (fun i : Ground n => if i ∈ S then I.cost i else 0))
theorem costRun_correct (S : Selection n) : (I.costRun S).value=I.totalCost S := by
  classical
  simp [costRun, sumCells_correct, totalCost, List.sum_ofFn]
theorem costRun_operations (S : Selection n) : (I.costRun S).operations=4*n+1 := by
  simp [costRun, sumCells_operations]

/-- Threshold construction (12 per item), amortized pointer sweep (six
RAM operations per sweep tick), and candidate construction/temporary query
edits (32 per record). Cached absence counts and snapshot handles are read
in O(1). Diagonal pairs return the terminal prefix and are harmless. -/
def rowOperationCount (a : Ground n) (i : Option (Ground n)) : ℕ :=
  12*I.costSorted.length+6*(I.rowSweep a i).ticks+32*(I.rowCandidates a i).length+2

theorem rowOperationCount_bound (a : Ground n) (i : Option (Ground n)) :
    I.rowOperationCount a i ≤ 80*n+14 := by
  have h := I.rowSweep_ticks a i
  simp only [rowOperationCount, I.costSorted_length, I.rowCandidates_length]
  omega

theorem implementedPath_length (a : Ground n) : (I.implementedPath a).length=1+n+n*n := by
  simp [implementedPath, List.length_flatMap, I.rowCandidates_length, itemList]
  ring

def implementedCandidates : List (Selection n) := by
  classical
  exact ∅::I.itemList.flatMap (fun a => if I.Feasible {a} then I.implementedPath a else [])

theorem implementedCandidates_correct : I.implementedCandidates.toFinset=I.compressedCandidates := by
  classical
  ext S
  simp only [implementedCandidates, List.mem_toFinset, List.mem_cons, List.mem_flatMap,
    compressedCandidates, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro (rfl | ⟨a,ha,hS⟩)
    · exact Or.inl rfl
    · by_cases hf : I.Feasible {a}
      · rw [if_pos hf] at hS
        exact Or.inr ⟨a,hf,by rw [← I.implementedPath_correct a hf]; exact List.mem_toFinset.mpr hS⟩
      · simp [hf] at hS
  · rintro (rfl | ⟨a,ha,hS⟩)
    · exact Or.inl rfl
    · right
      refine ⟨a,by simp [itemList],?_⟩
      rw [if_pos ha]
      apply List.mem_toFinset.mp
      rw [I.implementedPath_correct a ha]
      exact hS

def implementedOutput : ℝ := (maxValues I.value I.implementedCandidates).value

/-- Correctness of the array/sweep implementation, including the actual
objective maximum, rather than just a bound on an unrelated loop count. -/
theorem implementedOutput_correct : I.implementedOutput=I.output := by
  apply le_antisymm
  · apply maxValues_le _ _ _ I.output_nonneg
    intro S hS
    have hm : S ∈ I.compressedCandidates := by
      rw [← I.implementedCandidates_correct]
      exact List.mem_toFinset.mpr hS
    exact I.output_spec.2 _ (I.compressed_subset_candidates hm)
  · rw [← I.compressedOutput_eq]
    apply maxValues_ge
    apply List.mem_toFinset.mp
    rw [I.implementedCandidates_correct]
    exact I.compressedOutput_spec.1

def seedOperationCount (a : Ground n) : ℕ :=
  (I.pathRun {a} n).operations+
  (∑ i : Ground n, (I.absenceRun a i).operations)+
  (∑ t : Fin (n+1), (I.costRun (I.prefixSet a t)).operations)+
  I.rowOperationCount a none+(∑ i : Ground n, I.rowOperationCount a (some i))+
  (maxValues I.value (I.implementedPath a)).operations+20

theorem seedOperationCount_bound (a : Ground n) :
    I.seedOperationCount a ≤ 150*(n+1)^2 := by
  have hr := I.rowOperationCount_bound a none
  have hs : (∑ i : Ground n, I.rowOperationCount a (some i)) ≤ n*(80*n+14) := by
    calc
      _ ≤ ∑ _i : Ground n, (80*n+14) := Finset.sum_le_sum (fun i _ => I.rowOperationCount_bound a (some i))
      _ = _ := by simp
  simp only [seedOperationCount, I.pathRun_operations, I.absenceRun_operations,
    I.costRun_operations, maxValues_operations, I.implementedPath_length]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  nlinarith

/-- Includes input enumeration, one shared item-cost sort, all feasible-seed
runs, feasibility tests, merging seed maxima, and reconstruction of the best
record. The zero-element instance is also defined. -/
def auxiliaryOperationCount : ℕ := by
  classical
  exact 20*(n+1)+4*sortTicks I.costOrder I.itemList+
    ∑ a : Ground n, if I.Feasible {a} then I.seedOperationCount a+4 else 4

theorem auxiliaryOperationCount_polynomial :
    I.auxiliaryOperationCount ≤ 20*(n+1)+4*(n+1)^2+n*(150*(n+1)^2+4) := by
  classical
  have ht := sortTicks_bound I.costOrder I.itemList
  simp only [itemList, List.length_finRange] at ht
  have hs : (∑ a : Ground n, if I.Feasible {a} then I.seedOperationCount a+4 else 4) ≤
      n*(150*(n+1)^2+4) := by
    calc
      _ ≤ ∑ _a : Ground n, (150*(n+1)^2+4) := by
        apply Finset.sum_le_sum
        intro a _
        split
        · have h := I.seedOperationCount_bound a; omega
        · omega
      _ = _ := by simp
  unfold auxiliaryOperationCount
  change 20*(n+1)+4*sortTicks I.costOrder (List.finRange n)+_ ≤ _
  omega

/-- Cubic auxiliary operations in the explicitly stated cost model. -/
theorem auxiliaryOperationCount_cubic (hn : 1 ≤ n) :
    I.auxiliaryOperationCount ≤ 700*n^3 := by
  have h := I.auxiliaryOperationCount_polynomial
  have hn2 : n ≤ n*n := by nlinarith
  have hn3 : n*n ≤ n^3 := by
    have hm := Nat.mul_le_mul_left n hn2
    nlinarith only [hm]
  nlinarith only [h, hn, hn2, hn3]

end
end S2R.Instance
