import S2R.NormalizedContradiction
import S2R.Scaling

namespace S2R

/-- The approximation guarantee for every finite valid instance. -/
def ExactApproximationGuarantee : Prop :=
  ∀ (n : ℕ) (I : Instance n), (1-Real.exp (-1))*I.optimum ≤ I.output

end S2R

namespace S2R.Instance
noncomputable section
open S2R.Analysis
variable {n : ℕ} (I : Instance n)

/-- Every feasible comparison set satisfies the exact guarantee. The
normalization and the two largest residual costs are constructed here. -/
theorem approximation_for_feasible {O : Selection n} (hf : I.Feasible O) :
    alpha * I.value O ≤ I.output := by
  classical
  by_cases hsmall : O.card ≤ 3
  · have h := I.small_solution_le_output hf hsmall
    have hp := mul_nonneg (Real.exp_pos (-1)).le (I.value_nonneg O)
    unfold alpha b
    nlinarith
  by_contra hn
  have hbad : I.output < alpha*I.value O := lt_of_not_ge hn
  have hv : 0 < I.value O := by
    have hpos : 0 < alpha*I.value O := I.output_nonneg.trans_lt hbad
    exact (mul_pos_iff_of_pos_left alpha_pos).mp hpos
  have hO : O.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha, hmax⟩ := O.exists_max_image (fun i => I.value {i}) hO
  let T := O.erase a
  have hTcard : 3 ≤ T.card := by
    have h := Finset.card_erase_add_one ha
    change T.card+1=O.card at h
    omega
  obtain ⟨j, hj, hjmax⟩ := T.exists_max_image I.cost (Finset.card_pos.mp (by omega))
  have hTjcard : 2 ≤ (T.erase j).card := by
    have h := Finset.card_erase_add_one hj
    omega
  obtain ⟨k, hk, hkmax⟩ := (T.erase j).exists_max_image I.cost
    (Finset.card_pos.mp (by omega))
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hkT : k ∈ T := (Finset.mem_erase.mp hk).2
  let R : Selection n := {j,k}
  have hRsub : R ⊆ T := by
    intro i hi
    simp only [R, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  have htail : (T \ R).Nonempty := by
    have hRc : R.card=2 := by simp [R, Ne.symm hkj]
    have hcard := Finset.card_sdiff_add_card_eq_card hRsub
    exact Finset.card_pos.mp (by omega)
  let c := I.totalCost (T \ R)
  have hc : 0 < c := Finset.sum_pos (fun i _ => I.cost_pos i) htail
  let J := I.rescale (I.value O) c hv hc
  have hJcost (S : Selection n) : J.totalCost S=I.totalCost S/c :=
    I.rescale_cost _ _ _ _ S
  have hJord {i l : Ground n} (h : I.cost i ≤ I.cost l) : J.cost i ≤ J.cost l :=
    div_le_div_of_nonneg_right h hc.le
  have hJR : J.totalCost R=J.cost j+J.cost k := by
    simp [totalCost, R, Ne.symm hkj]
  let D : CertificateData J := {
    optimumSet := O
    seed := a
    repair := R
    seed_mem := ha
    feasible := (I.rescale_feasible _ _ _ _ O).mpr hf
    value_one := div_self hv.ne'
    seed_max := fun i hi => div_le_div_of_nonneg_right (hmax i hi) hv.le
    repair_subset := hRsub
    repair_card := by simp [R, Ne.symm hkj]
    tail_cost := by rw [hJcost]; exact div_self hc.ne'
    individual_cost := fun i hi => by
      rw [hJR]
      have h := hJord (hjmax i hi)
      linarith [J.cost_pos k]
    bad_output := by
      rw [I.rescale_output]
      exact (div_lt_iff₀ hv).mpr hbad }
  let E : D.CostPair := {
    big := j
    small := k
    big_mem := hj
    small_mem := hkT
    distinct := Ne.symm hkj
    repair_eq := rfl
    ordered := hJord (hjmax k hkT)
    largest := fun i hi => hJord (hjmax i hi)
    second := fun i hi hne => hJord (hkmax i (Finset.mem_erase.mpr ⟨hne,hi⟩)) }
  exact E.rootData.impossible

/-- Exact, epsilon-free S2R approximation guarantee for every finite valid
instance; no analytic certificate or counterexample exclusion is assumed. -/
theorem approximation_guarantee :
    (1-Real.exp (-1))*I.optimum ≤ I.output :=
  I.approximation_for_feasible I.optimumSet_spec.1

end
end S2R.Instance

namespace S2R
theorem exactApproximationGuarantee : ExactApproximationGuarantee :=
  fun _ I => I.approximation_guarantee
end S2R
