import S2R.TwoCostPath

namespace S2R.Analysis
noncomputable section
theorem sum_ite_subset {ι : Type*} [DecidableEq ι] (T R : Finset ι) (f : ι → ℝ)
    (hR : R ⊆ T) : (∑ i ∈ T, if i ∈ R then f i else 0) = ∑ i ∈ R, f i := by
  have he : T.filter (fun i => i ∈ R) = R := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hi => ⟨hR hi, hi⟩⟩
  rw [← Finset.sum_filter, he]
end
end S2R.Analysis

namespace S2R.Instance.CertificateData.CostPair
noncomputable section
open S2R.Analysis
variable {n : ℕ} {I : Instance n} {D : I.CertificateData} (E : D.CostPair)

theorem s_pos : 0 < E.s := by unfold s; linarith [E.mu_pos, E.lam_pos]
theorem lam_le_s : E.lam ≤ E.s := by unfold s; linarith [E.lam_le_mu]
theorem u_bounds : 0 ≤ E.u ∧ E.u < 1 := by
  have hp : 0 < E.mu+E.lam := add_pos E.mu_pos E.lam_pos
  constructor
  · exact div_nonneg (sub_nonneg.mpr E.lam_le_mu) hp.le
  · apply (div_lt_iff₀ hp).mpr
    linarith [E.lam_pos]
theorem mu_eq : E.mu = E.s*(1+E.u) := by
  have hp : E.mu+E.lam ≠ 0 := (add_pos E.mu_pos E.lam_pos).ne'
  unfold s u
  field_simp
  ring
theorem lam_eq : E.lam = E.s*(1-E.u) := by
  have hp : E.mu+E.lam ≠ 0 := (add_pos E.mu_pos E.lam_pos).ne'
  unfold s u
  field_simp
  ring
theorem total_cost_s : I.totalCost D.items = 1+2*E.s := by
  rw [E.total_cost]
  unfold s
  ring

theorem constant_certificate {β : ℝ} (hb : 0 < β) (hb1 : β ≤ 1) :
    1+b-β+D.p*β+b*(1+2*E.s)*Real.log β ≤ I.valueAt D.seed 1 := by
  have h := D.unified_density_certificate (fun _ => β) hb (fun _ _ => ⟨le_rfl, hb1⟩)
  simp only [sub_self, Finset.sum_const_zero, sub_zero, ← Finset.sum_mul] at h
  change 1+b-β+D.p*β+b*(I.totalCost D.items*Real.log β) ≤ _ at h
  rw [E.total_cost_s, ← I.valueAt_one] at h
  nlinarith only [h]

theorem modified_certificate (R : Selection n) (hR : R ⊆ D.items) {β κ : ℝ}
    (hb : 0 < β) (hbk : β ≤ κ) (hk1 : κ ≤ 1) :
    1+b-β+D.p*(β-R.card*(κ-β))+
      b*(I.totalCost D.items*Real.log β+I.totalCost R*(Real.log κ-Real.log β)) ≤ I.valueAt D.seed 1 := by
  classical
  let τ : Ground n → ℝ := fun i => if i ∈ R then κ else β
  have h := D.unified_density_certificate τ hb (fun i hi => by
    dsimp [τ]; split_ifs <;> exact ⟨by linarith, by linarith⟩)
  have hd : (∑ i ∈ D.items, (τ i-β)) = R.card*(κ-β) := by
    have he (i : Ground n) : τ i-β = if i ∈ R then κ-β else 0 := by
      dsimp [τ]; split_ifs <;> simp
    simp_rw [he]
    rw [sum_ite_subset D.items R (fun _ => κ-β) hR]
    simp
    ring
  have hl : (∑ i ∈ D.items, I.cost i*Real.log (τ i)) =
      I.totalCost D.items*Real.log β+I.totalCost R*(Real.log κ-Real.log β) := by
    have he (i : Ground n) : I.cost i*Real.log (τ i) = I.cost i*Real.log β+
        (if i ∈ R then I.cost i*(Real.log κ-Real.log β) else 0) := by
      dsimp [τ]; split_ifs <;> ring
    simp_rw [he, Finset.sum_add_distrib]
    rw [sum_ite_subset D.items R (fun i => I.cost i*(Real.log κ-Real.log β)) hR]
    simp only [← Finset.sum_mul, totalCost]
  rw [hd, hl, ← I.valueAt_one] at h
  exact h

theorem pair_certificate {β : ℝ} (hb : 0 < β) (hb2 : β ≤ 2/3) :
    1+b-β+b*(1+2*E.s)*Real.log β+2*b*E.s*Real.log (3/2) ≤ I.valueAt D.seed 1 := by
  have h := modified_certificate (D := D) D.repair D.repair_subset (κ := 3*β/2) hb
    (by linarith) (by linarith)
  rw [E.repair_card_two, E.total_cost_s, E.repair_cost] at h
  have he : Real.log (3*β/2) = Real.log β+Real.log (3/2) := by
    have he : 3*β/2=β*(3/2) := by ring
    rw [he, Real.log_mul hb.ne' (by norm_num : (3/2:ℝ) ≠ 0)]
  rw [he] at h
  have hs : E.mu+E.lam=2*E.s := by unfold s; ring
  rw [hs] at h
  norm_num only [Nat.cast_ofNat] at h
  nlinarith only [h]

theorem uniform_bracket : alpha ≤ I.valueAt D.seed 1+2*E.s*(b-D.p) := by
  let β := Real.exp (Real.exp 1*D.p-1)
  have hb : 0 < β := Real.exp_pos _
  have hp := D.seed_small
  have hbe : Real.exp 1*b=1 := by nlinarith only [b_mul_exp_one]
  have hep : Real.exp 1*D.p < 1 := by
    have h := mul_lt_mul_of_pos_left hp.2 (Real.exp_pos 1)
    linarith
  have hb1 : β ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith
  have h := E.constant_certificate hb hb1
  have hl : Real.log β = Real.exp 1*D.p-1 := Real.log_exp _
  rw [hl] at h
  have hbep : b*(Real.exp 1*D.p)=D.p := by rw [← mul_assoc, b_mul_exp_one, one_mul]
  have hbess : b*(Real.exp 1*D.p)*E.s = D.p*E.s := by rw [hbep]
  have he := uniform_exp_bound D.p_pos.le hp.1.le
  change (1-D.p)*β ≤ b+D.p at he
  unfold alpha
  nlinarith only [h, hbep, hbess, he]

theorem s_lt_quarter : E.s < 1/4 := by
  by_contra hn
  have hs : 1/4 ≤ E.s := le_of_not_gt hn
  let β := min (b*(1+2*E.s)) (2/3)
  have hb : 0 < β := lt_min (mul_pos b_pos (by linarith [E.s_pos])) (by norm_num)
  have hcert := E.pair_certificate hb (min_le_right _ _)
  change largeCostBase E.s ≤ I.valueAt D.seed 1 at hcert
  have hfirst : alpha < I.valueAt D.seed 1+b*E.s/(1+E.s) :=
    (large_cost_strict hs).trans_le (add_le_add_right hcert _)
  have hsecond := E.uniform_bracket
  have hf := E.fundamental_path_bound
  have hlam := E.lam_pos
  have hspos := E.s_pos
  have hls := E.lam_le_s
  have hden : 0 < 1+E.s := by linarith
  have hdenl : 0 < 1+E.lam := by linarith
  have hfrac : b*E.lam/(1+E.s) ≤ b*E.lam/(1+E.lam) := by
    exact div_le_div_of_nonneg_left (mul_nonneg b_pos.le hlam.le) hdenl (by linarith)
  have hfirst' := mul_lt_mul_of_pos_left hfirst hlam
  have hsecond' := mul_le_mul_of_nonneg_left hsecond (sub_nonneg.mpr hls)
  have hsum : E.mu+E.lam=2*E.s := by unfold s; ring
  have hf' := mul_le_mul_of_nonneg_left hf hspos.le
  have hfrac' := mul_le_mul_of_nonneg_left hfrac hspos.le
  have he1 : E.lam*(b*E.s/(1+E.s)) = E.s*(b*E.lam/(1+E.s)) := by ring
  rw [mul_add, he1] at hfirst'
  have he2 : (E.s-E.lam)*2*E.s*(b-D.p) = E.s*(b-D.p)*(E.mu-E.lam) := by
    have h := congrArg (fun t : ℝ => E.s*(b-D.p)*t) hsum
    dsimp only at h
    nlinarith only [h]
  have hb' := D.bad_output
  have hbad := mul_lt_mul_of_pos_left hb' hspos
  nlinarith only [hfirst', hsecond', hf', hfrac', he2, hbad]

theorem single_certificate {β κ : ℝ} (hb : 0 < β) (hbk : β ≤ κ) (hk1 : κ ≤ 1) :
    1+b-β+D.p*(2*β-κ)+b*(E.mu*Real.log κ+(1+E.lam)*Real.log β) ≤ I.valueAt D.seed 1 := by
  have h := modified_certificate (D := D) {E.big} (Finset.singleton_subset_iff.mpr E.big_mem) hb hbk hk1
  rw [Finset.card_singleton, I.totalCost_singleton, E.total_cost] at h
  norm_num only [Nat.cast_one] at h
  change 1+b-β+D.p*(β-1*(κ-β))+b*((1+E.mu+E.lam)*Real.log β+E.mu*(Real.log κ-Real.log β)) ≤ _ at h
  nlinarith only [h]

theorem u_lt_fifth : E.u < 1/5 := by
  by_contra hn
  have hu : 1/5 ≤ E.u := le_of_not_gt hn
  have hu1 := E.u_bounds.2.le
  have hs := E.s_pos
  have hs4 := E.s_lt_quarter.le
  have hpar := unbalanced_parameters hs.le hs4 hu hu1
  have hcert := E.single_certificate hpar.1 hpar.2.1 hpar.2.2
  have hf := E.fundamental_path_bound
  have hU := mul_pos b_pos (unbalanced_cost_positive hs hs4 hu hu1)
  rw [E.mu_eq, E.lam_eq] at hcert hf
  have hident :
      (1+b-b*(1+3*E.s/2)+D.p*(2*(b*(1+3*E.s/2))-(2*b*(1+3*E.s/2)-2*E.s*E.u))+
        b*(E.s*(1+E.u)*Real.log (2*b*(1+3*E.s/2)-2*E.s*E.u)+
          (1+E.s*(1-E.u))*Real.log (b*(1+3*E.s/2))))+
      b*(E.s*(1-E.u))/(1+E.s*(1-E.u))+(b-D.p)*(E.s*(1+E.u)-E.s*(1-E.u)) =
      alpha+b*U E.s E.u := by
    unfold alpha U
    ring
  have hbad := D.bad_output
  nlinarith only [hcert, hf, hident, hU, hbad]

end
end S2R.Instance.CertificateData.CostPair
