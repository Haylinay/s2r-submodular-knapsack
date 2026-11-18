import S2R.Algorithm
import S2R.Analysis

namespace S2R.Instance
noncomputable section
variable {n : ℕ} (I : Instance n)

def rescale (v c : ℝ) (hv : 0 < v) (hc : 0 < c) : Instance n where
  value := fun S => I.value S/v
  cost := fun i => I.cost i/c
  budget := I.budget/c
  cost_pos := fun i => div_pos (I.cost_pos i) hc
  budget_nonneg := div_nonneg I.budget_nonneg hc.le
  normalized := by simp [I.normalized]
  monotone := fun h => div_le_div_of_nonneg_right (I.monotone h) hv.le
  diminishing := by
    intro S T i hST hi
    simp only [← sub_div]
    exact div_le_div_of_nonneg_right (I.diminishing hST hi) hv.le

variable (v c : ℝ) (hv : 0 < v) (hc : 0 < c)
local notation "J" => I.rescale v c hv hc

theorem rescale_cost (S : Selection n) : (I.rescale v c hv hc).totalCost S=I.totalCost S/c := by
  simp only [totalCost, rescale, div_eq_mul_inv, Finset.sum_mul]
theorem rescale_feasible (S : Selection n) : (I.rescale v c hv hc).Feasible S ↔ I.Feasible S := by
  unfold Feasible
  rw [I.rescale_cost]
  change I.totalCost S/c ≤ I.budget/c ↔ _
  exact div_le_div_iff_of_pos_right hc
theorem rescale_density (i : Ground n) (S : Selection n) :
    (I.rescale v c hv hc).density i S=I.density i S*(c/v) := by
  dsimp [density, marginal, rescale]
  field_simp [(I.cost_pos i).ne', hv.ne', hc.ne'] <;> ring <;> simp
theorem rescale_available (S : Selection n) : (I.rescale v c hv hc).available S=I.available S := by
  ext i
  simp only [mem_available, I.rescale_feasible v c hv hc]
theorem rescale_bestSet (S : Selection n) : (I.rescale v c hv hc).bestSet S=I.bestSet S := by
  classical
  ext i
  simp only [bestSet, Finset.mem_filter, I.rescale_available v c hv hc,
    I.rescale_density v c hv hc, mul_le_mul_right (div_pos hc hv)]
theorem rescale_choose (S : Selection n) : (I.rescale v c hv hc).choose S=I.choose S := by
  unfold choose
  simp only [I.rescale_available v c hv hc, I.rescale_bestSet v c hv hc]
theorem rescale_step (S : Selection n) : (I.rescale v c hv hc).step S=I.step S := by
  simp only [step, I.rescale_choose v c hv hc]
theorem rescale_iterate (S : Selection n) (k : ℕ) : (I.rescale v c hv hc).iterate S k=I.iterate S k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterate_succ, I.rescale_step v c hv hc, ih]
theorem rescale_prefix (a : Ground n) (t : Fin (n+1)) : (I.rescale v c hv hc).prefixSet a t=I.prefixSet a t :=
  I.rescale_iterate v c hv hc {a} t.val
theorem rescale_pathCandidates (a : Ground n) : (I.rescale v c hv hc).pathCandidates a=I.pathCandidates a := by
  ext S
  simp only [mem_pathCandidates_iff, I.rescale_feasible v c hv hc, I.rescale_prefix v c hv hc]
theorem rescale_candidates : (I.rescale v c hv hc).candidates=I.candidates := by
  classical
  ext S
  simp only [candidates, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_filter,
    I.rescale_feasible v c hv hc, I.rescale_pathCandidates v c hv hc]
theorem rescale_output : (I.rescale v c hv hc).output=I.output/v := by
  have hcand := I.rescale_candidates v c hv hc
  apply le_antisymm
  · have h := I.output_spec.2 (I.rescale v c hv hc).outputSet (hcand ▸ (I.rescale v c hv hc).output_spec.1)
    exact div_le_div_of_nonneg_right h hv.le
  · have hm : I.outputSet ∈ (I.rescale v c hv hc).candidates := by rw [hcand]; exact I.output_spec.1
    exact (I.rescale v c hv hc).output_spec.2 I.outputSet hm

end
end S2R.Instance


