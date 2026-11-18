import S2R.Algorithm

namespace S2R.Instance
noncomputable section
variable {n : ℕ} (I : S2R.Instance n)

def earlier (O : Selection n) (i : Ground n) : Selection n := O.filter (fun j => j < i)
def residual (O S : Selection n) (i : Ground n) : ℝ :=
  I.marginal i (S ∪ earlier O i)

theorem residual_nonneg (O S : Selection n) (i : Ground n) : 0 ≤ I.residual O S i :=
  I.marginal_nonneg _ _

theorem residual_le_marginal (O S : Selection n) (i : Ground n) :
    I.residual O S i ≤ I.marginal i S :=
  I.marginal_antitone Finset.subset_union_left i

theorem residual_le_singleton (O S : Selection n) (i : Ground n) :
    I.residual O S i ≤ I.value {i} :=
  (I.residual_le_marginal O S i).trans (I.marginal_le_singleton i S)

theorem residual_antitone (O : Selection n) {S T : Selection n} (h : S ⊆ T) (i : Ground n) :
    I.residual O T i ≤ I.residual O S i :=
  I.marginal_antitone (Finset.union_subset_union h (Finset.Subset.refl _)) i

theorem residual_of_mem (O : Selection n) {S : Selection n} {i : Ground n} (hi : i ∈ S) :
    I.residual O S i = 0 :=
  I.marginal_of_mem (Finset.mem_union_left _ hi)

/-- Telescoping does not require the comparison set to be disjoint from the prefix. -/
theorem residual_sum (O S : Selection n) :
    ∑ i ∈ O, I.residual O S i = I.value (S ∪ O) - I.value S := by
  classical
  induction O using Finset.induction_on_max with
  | h0 => simp
  | @step a O hmax ih =>
    have ha : a ∉ O := fun h => (lt_irrefl a) (hmax a h)
    have hp : earlier (insert a O) a = O := by
      ext j
      simp only [earlier, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hlt⟩
        · exact False.elim ((lt_irrefl _) hlt)
        · exact hj
      · intro hj; exact ⟨Or.inr hj, hmax j hj⟩
    have hold (i : Ground n) (hi : i ∈ O) : earlier (insert a O) i = earlier O i := by
      ext j
      simp only [earlier, Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨rfl | hj, hlt⟩
        · exact False.elim ((not_lt_of_ge (hmax i hi).le) hlt)
        · exact ⟨hj, hlt⟩
      · rintro ⟨hj, hlt⟩; exact ⟨Or.inr hj, hlt⟩
    rw [Finset.sum_insert ha]
    have hsum : (∑ i ∈ O, I.residual (insert a O) S i) = ∑ i ∈ O, I.residual O S i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [residual, hold i hi]
    rw [hsum, ih]
    have hu : S ∪ insert a O = insert a (S ∪ O) := by ext i; simp
    simp only [residual, hp, marginal, hu]
    ring

theorem value_gap_le_residual_sum (O S : Selection n) :
    I.value O - I.value S ≤ ∑ i ∈ O, I.residual O S i := by
  rw [I.residual_sum]
  exact sub_le_sub_right (I.monotone Finset.subset_union_right) _

theorem residual_sum_le_initial {a : Ground n} {O S : Selection n}
    (haO : a ∈ O) (haS : a ∈ S) :
    ∑ i ∈ O, I.residual O S i ≤ I.value O - I.value {a} := by
  have h : (∑ i ∈ O, I.residual O S i) ≤ ∑ i ∈ O, I.residual O {a} i :=
    Finset.sum_le_sum (fun i _ => I.residual_antitone O (Finset.singleton_subset_iff.mpr haS) i)
  rw [I.residual_sum O {a}] at h
  have hu : {a} ∪ O = O := Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr haO)
  simpa [hu] using h

theorem restricted_residual_sum_le {R O S : Selection n} (hRO : R ⊆ O) :
    ∑ i ∈ R, I.residual O S i ≤ I.value (S ∪ R) - I.value S := by
  rw [← I.residual_sum R S]
  apply Finset.sum_le_sum
  intro i _
  apply I.marginal_antitone
  apply Finset.union_subset_union (Finset.Subset.refl _)
  exact Finset.filter_subset_filter _ hRO

theorem residual_density_bound {O S : Selection n} {i : Ground n} {ρ : ℝ}
    (h : I.density i S ≤ ρ) : I.residual O S i ≤ ρ * I.cost i := by
  have hm : I.marginal i S ≤ ρ * I.cost i := (div_le_iff₀ (I.cost_pos i)).mp h
  exact (I.residual_le_marginal O S i).trans hm

theorem chosen_residual_density_bound {O S : Selection n} {i j : Ground n}
    (hi : I.choose S = some i) (hj : j ∈ I.available S) :
    I.residual O S j ≤ I.density i S * I.cost j :=
  I.residual_density_bound ((I.choose_spec hi).2 j hj)

theorem repair_residual_bound {a : Ground n} (ha : I.Feasible {a})
    {O R : Selection n} (hRO : R ⊆ O) (t : Fin (n + 1)) (hR : R.card ≤ 2)
    (hf : I.Feasible (I.prefixSet a t ∪ R)) :
    ∑ i ∈ R, I.residual O (I.prefixSet a t) i ≤ I.output - I.value (I.prefixSet a t) := by
  exact (I.restricted_residual_sum_le hRO).trans
    (sub_le_sub_right (I.repair_le_output ha t hR hf) _)

end
end S2R.Instance
