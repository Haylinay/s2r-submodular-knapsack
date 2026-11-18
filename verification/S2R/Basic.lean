import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! Basic finite-set model. All objective and cost values are real numbers.
The ground set is `Fin n`; its order is used to break density ties. -/
namespace S2R

abbrev Ground (n : ℕ) := Fin n
abbrev Selection (n : ℕ) := Finset (Ground n)

structure Instance (n : ℕ) where
  value : Selection n → ℝ
  cost : Ground n → ℝ
  budget : ℝ
  cost_pos : ∀ i, 0 < cost i
  budget_nonneg : 0 ≤ budget
  normalized : value ∅ = 0
  monotone : ∀ {S T}, S ⊆ T → value S ≤ value T
  diminishing : ∀ {S T} {i}, S ⊆ T → i ∉ T →
    value (insert i T) - value T ≤ value (insert i S) - value S

namespace Instance
noncomputable section
variable {n : ℕ} (I : Instance n)

def totalCost (S : Selection n) : ℝ := ∑ i ∈ S, I.cost i
def Feasible (S : Selection n) : Prop := I.totalCost S ≤ I.budget
def marginal (i : Ground n) (S : Selection n) : ℝ := I.value (insert i S) - I.value S
def density (i : Ground n) (S : Selection n) : ℝ := I.marginal i S / I.cost i

@[simp] theorem totalCost_empty : I.totalCost ∅ = 0 := by simp [totalCost]
@[simp] theorem totalCost_singleton (i : Ground n) : I.totalCost {i} = I.cost i := by
  simp [totalCost]

theorem totalCost_nonneg (S : Selection n) : 0 ≤ I.totalCost S :=
  Finset.sum_nonneg (fun i _ => (I.cost_pos i).le)

theorem totalCost_mono {S T : Selection n} (h : S ⊆ T) :
    I.totalCost S ≤ I.totalCost T :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => (I.cost_pos i).le)

theorem totalCost_insert {S : Selection n} {i : Ground n} (hi : i ∉ S) :
    I.totalCost (insert i S) = I.cost i + I.totalCost S := by
  simp [totalCost, hi]

theorem totalCost_union {S T : Selection n} (h : Disjoint S T) :
    I.totalCost (S ∪ T) = I.totalCost S + I.totalCost T := by
  exact Finset.sum_union h

theorem totalCost_insert_gt {S : Selection n} {i : Ground n} (hi : i ∉ S) :
    I.totalCost S < I.totalCost (insert i S) := by
  rw [I.totalCost_insert hi]
  linarith [I.cost_pos i]

theorem feasible_empty : I.Feasible ∅ := by
  simpa [Feasible] using I.budget_nonneg

theorem feasible_subset {S T : Selection n} (h : S ⊆ T) (hT : I.Feasible T) :
    I.Feasible S := (I.totalCost_mono h).trans hT

theorem value_nonneg (S : Selection n) : 0 ≤ I.value S := by
  simpa [I.normalized] using I.monotone (Finset.empty_subset S)

theorem marginal_nonneg (i : Ground n) (S : Selection n) : 0 ≤ I.marginal i S := by
  exact sub_nonneg.mpr (I.monotone (Finset.subset_insert i S))

@[simp] theorem marginal_of_mem {i : Ground n} {S : Selection n} (h : i ∈ S) :
    I.marginal i S = 0 := by simp [marginal, Finset.insert_eq_of_mem h]

theorem marginal_antitone {S T : Selection n} (h : S ⊆ T) (i : Ground n) :
    I.marginal i T ≤ I.marginal i S := by
  by_cases hi : i ∈ T
  · simpa [I.marginal_of_mem hi] using I.marginal_nonneg i S
  · exact I.diminishing h hi

theorem marginal_le_singleton (i : Ground n) (S : Selection n) :
    I.marginal i S ≤ I.value {i} := by
  simpa [marginal, I.normalized] using I.marginal_antitone (Finset.empty_subset S) i

theorem density_nonneg (i : Ground n) (S : Selection n) : 0 ≤ I.density i S :=
  div_nonneg (I.marginal_nonneg i S) (I.cost_pos i).le

theorem density_antitone {S T : Selection n} (h : S ⊆ T) (i : Ground n) :
    I.density i T ≤ I.density i S :=
  div_le_div_of_nonneg_right (I.marginal_antitone h i) (I.cost_pos i).le

theorem union_gain_le_sum (S T : Selection n) :
    I.value (S ∪ T) - I.value S ≤ ∑ i ∈ T, I.marginal i S := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.sum_insert hi]
    have h := I.marginal_antitone (Finset.subset_union_left : S ⊆ S ∪ T) i
    have heq : S ∪ insert i T = insert i (S ∪ T) := by ext j; simp
    rw [heq]
    unfold marginal at h ih ⊢
    linarith

theorem value_le_singleton_sum (S : Selection n) :
    I.value S ≤ ∑ i ∈ S, I.value {i} := by
  simpa [marginal, I.normalized] using I.union_gain_le_sum ∅ S

noncomputable def feasibleSets : Finset (Selection n) := by
  classical
  exact (Finset.univ : Finset (Ground n)).powerset.filter I.Feasible

@[simp] theorem mem_feasibleSets (S : Selection n) :
    S ∈ I.feasibleSets ↔ I.Feasible S := by classical simp [feasibleSets]

theorem feasibleSets_nonempty : I.feasibleSets.Nonempty :=
  ⟨∅, (I.mem_feasibleSets ∅).mpr I.feasible_empty⟩

noncomputable def optimumSet : Selection n :=
  Classical.choose (I.feasibleSets.exists_max_image I.value I.feasibleSets_nonempty)

theorem optimumSet_spec : I.Feasible I.optimumSet ∧
    ∀ S, I.Feasible S → I.value S ≤ I.value I.optimumSet := by
  have h := Classical.choose_spec
    (I.feasibleSets.exists_max_image I.value I.feasibleSets_nonempty)
  exact ⟨(I.mem_feasibleSets _).mp h.1, fun S hS => h.2 S ((I.mem_feasibleSets S).mpr hS)⟩

noncomputable def optimum : ℝ := I.value I.optimumSet

theorem le_optimum {S : Selection n} (h : I.Feasible S) : I.value S ≤ I.optimum :=
  I.optimumSet_spec.2 S h

theorem optimum_nonneg : 0 ≤ I.optimum := I.value_nonneg _

end
end Instance
end S2R
