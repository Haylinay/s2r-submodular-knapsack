import S2R.Residual
import S2R.Analysis

namespace S2R.Instance
noncomputable section
variable {n : ℕ} (I : S2R.Instance n)

theorem chosen_density_antitone {S T : Selection n} {i j : Ground n}
    (hST : S ⊆ T) (hi : I.choose S = some i) (hj : I.choose T = some j) :
    I.density j T ≤ I.density i S := by
  have hjT := (I.choose_spec hj).1
  exact (I.density_antitone hST j).trans
    ((I.choose_spec hi).2 j (I.available_antitone hST hjT))

theorem chosen_gain {S : Selection n} {i : Ground n} (hi : I.choose S = some i) :
    I.value (I.step S)-I.value S = I.cost i*I.density i S := by
  simp only [step, hi]
  unfold density marginal
  field_simp [(I.cost_pos i).ne']

theorem totalCost_insert_le (S : Selection n) (i : Ground n) :
    I.totalCost (insert i S) ≤ I.totalCost S+I.cost i := by
  classical
  by_cases hi : i ∈ S
  · rw [Finset.insert_eq_of_mem hi]
    linarith [I.cost_pos i]
  · rw [I.totalCost_insert hi]
    ring_nf
    exact le_rfl

theorem residual_le_chosen_density {O S : Selection n} {i j : Ground n}
    (hi : I.choose S = some i) (hbudget : I.totalCost S+I.cost j ≤ I.budget) :
    I.residual O S j ≤ I.density i S*I.cost j := by
  by_cases hj : j ∈ S
  · rw [I.residual_of_mem O hj]
    exact mul_nonneg (I.density_nonneg _ _) (I.cost_pos _).le
  · exact I.chosen_residual_density_bound hi (I.mem_available.mpr
      ⟨hj, (I.totalCost_insert_le S j).trans hbudget⟩)

/-- A repair forces the residual mass outside that repair to be covered by
the current greedy density. This is the finite-prefix source of (2.5). -/
theorem repaired_density_bound {O R : Selection n} {a i : Ground n}
    (ha : I.Feasible {a}) (t : Fin (n+1)) (hR : R ⊆ O) (hR2 : R.card ≤ 2)
    (hf : I.Feasible (I.prefixSet a t ∪ R))
    (hi : I.choose (I.prefixSet a t) = some i)
    (hbudget : ∀ j ∈ O \ R, I.totalCost (I.prefixSet a t)+I.cost j ≤ I.budget) :
    I.value O-I.output ≤ I.density i (I.prefixSet a t)*I.totalCost (O \ R) := by
  have hg := I.value_gap_le_residual_sum O (I.prefixSet a t)
  have hr := I.repair_residual_bound ha hR t hR2 hf
  have he := Finset.sum_sdiff hR (f := I.residual O (I.prefixSet a t))
  have hd : (∑ j ∈ O \ R, I.residual O (I.prefixSet a t) j) ≤
      I.density i (I.prefixSet a t)*I.totalCost (O \ R) := by
    unfold totalCost
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => I.residual_le_chosen_density hi (hbudget j hj))
  linarith

/-- The same argument with a set of discarded residuals, each bounded by p.
For a singleton discard this supplies the third row of (2.5). -/
theorem repaired_density_with_discard {O R D : Selection n} {a i : Ground n} {p : ℝ}
    (ha : I.Feasible {a}) (t : Fin (n+1)) (hR : R ⊆ O) (hR2 : R.card ≤ 2)
    (hD : D ⊆ O \ R) (hp : ∀ j ∈ D, I.residual O (I.prefixSet a t) j ≤ p)
    (hf : I.Feasible (I.prefixSet a t ∪ R))
    (hi : I.choose (I.prefixSet a t) = some i)
    (hbudget : ∀ j ∈ (O \ R) \ D, I.totalCost (I.prefixSet a t)+I.cost j ≤ I.budget) :
    I.value O-I.output-D.card*p ≤
      I.density i (I.prefixSet a t)*I.totalCost ((O \ R) \ D) := by
  have hg := I.value_gap_le_residual_sum O (I.prefixSet a t)
  have hr := I.repair_residual_bound ha hR t hR2 hf
  have he := Finset.sum_sdiff hR (f := I.residual O (I.prefixSet a t))
  have he' := Finset.sum_sdiff hD (f := I.residual O (I.prefixSet a t))
  have hp' : (∑ j ∈ D, I.residual O (I.prefixSet a t) j) ≤ D.card*p := by
    calc
      _ ≤ ∑ _j ∈ D, p := Finset.sum_le_sum hp
      _ = _ := by simp
  have hd : (∑ j ∈ (O \ R) \ D, I.residual O (I.prefixSet a t) j) ≤
      I.density i (I.prefixSet a t)*I.totalCost ((O \ R) \ D) := by
    unfold totalCost
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => I.residual_le_chosen_density hi (hbudget j hj))
  linarith

theorem terminal_contains {O S : Selection n} (ht : I.available S = ∅)
    (hb : ∀ i ∈ O, I.totalCost S+I.cost i ≤ I.budget) : O ⊆ S := by
  intro i hi
  by_contra hn
  have hm : i ∈ I.available S := I.mem_available.mpr
    ⟨hn, (I.totalCost_insert_le S i).trans (hb i hi)⟩
  rw [ht] at hm
  exact Finset.not_mem_empty _ hm

theorem zero_optimum_guarantee (h : I.optimum = 0) :
    (1-Real.exp (-1))*I.optimum ≤ I.output := by
  rw [h, mul_zero]
  exact I.output_nonneg

theorem small_optimum_guarantee {O : Selection n} (hf : I.Feasible O)
    (ho : I.value O = I.optimum) (hc : O.card ≤ 3) :
    (1-Real.exp (-1))*I.optimum ≤ I.output := by
  have h := I.small_solution_le_output hf hc
  rw [ho] at h
  have hnon := mul_nonneg (Real.exp_pos (-1)).le I.optimum_nonneg
  nlinarith

end
end S2R.Instance
