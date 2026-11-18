import S2R.EntropyConnection

namespace S2R.Instance.CertificateData.CostPair.RootData
noncomputable section
open S2R.Analysis
variable {n : ℕ} {I : Instance n} {D : I.CertificateData} {E : D.CostPair} (R : E.RootData)

def ell : ℝ := E.mu-R.dbar
def J : ℝ := Real.exp (R.ell/R.A)-1
def compensatedR : ℝ := r E.s E.u R.q-omega E.s E.u R.q*((R.K-2*E.s)/R.A)

theorem ell_bounds : 0 ≤ R.ell ∧ R.ell ≤ E.s*(R.q+E.u) := by
  have hb := R.dbar_bounds
  constructor
  · unfold ell; linarith [E.lam_le_mu]
  · rw [R.root_eq_z] at hb
    dsimp [z] at hb
    unfold ell
    rw [E.mu_eq]
    linarith [hb.2.1]
theorem J_nonneg : 0 ≤ R.J := by
  unfold J
  exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg R.ell_bounds.1 R.A_bounds.1.le))
theorem exponent_bound : R.ell/R.A ≤ tau E.s := by
  have hs := E.s_pos
  have hq := R.q_bounds
  have hu := E.u_bounds.1
  have hu5 := E.u_lt_fifth
  have hA := R.A_partition
  have hK := R.K_bounds.2
  have hden : 0 < 3+4*E.s := by linarith
  have hsmall : 3*R.q+4*E.s*(R.q+E.u) ≤ 1+8*E.s := by
    have hh : R.q+E.u ≤ 2 := by linarith
    have hm := mul_le_mul_of_nonneg_left hh (show 0 ≤ 4*E.s by positivity)
    linarith [hq.2]
  have hpre : (R.q+E.u)*(3+4*E.s) ≤ 4*(1+2*E.s-R.k) := by
    unfold k cutoffK
    nlinarith only [hsmall]
  have hm := mul_le_mul_of_nonneg_left hpre hs.le
  have he := mul_le_mul_of_nonneg_right R.ell_bounds.2 hden.le
  have ha : 1+2*E.s-R.k ≤ R.A := by linarith
  have ham := mul_le_mul_of_nonneg_left ha (show 0 ≤ 4*E.s by positivity)
  unfold tau
  apply (div_le_div_iff₀ R.A_bounds.1 hden).mpr
  nlinarith only [hm, he, ham]
theorem J_bound : R.J ≤ 4*E.s/3 := by
  have hs := E.s_pos
  have hden1 : 0 < 3+4*E.s := by linarith
  have hden2 : 0 < 2+4*E.s/3 := by linarith
  have hlog : tau E.s ≤ Real.log (1+4*E.s/3) := by
    apply le_trans _ (log_lower_fraction (show 0 ≤ 4*E.s/3 by positivity))
    unfold tau
    apply (div_le_div_iff₀ hden1 hden2).mpr
    nlinarith only [sq_nonneg E.s]
  have he := Real.exp_le_exp.mpr (R.exponent_bound.trans hlog)
  rw [Real.exp_log (show 0 < 1+4*E.s/3 by positivity)] at he
  unfold J
  linarith
theorem frozen_product_bound : R.K*R.J ≤ E.lam := by
  have h1 := mul_le_mul_of_nonneg_right R.K_bounds.2 R.J_nonneg
  have h2 := mul_le_mul_of_nonneg_left R.J_bound R.k_bounds.1.le
  have he : R.k*(4*E.s/3)=E.lam := by rw [E.lam_eq]; unfold k cutoffK; ring
  rw [he] at h2
  linarith

theorem frozen_ratio_bound : R.compensatedR ≤
    (E.lam+(1+E.lam-R.K)*R.J)/(1+E.lam) := by
  have hs := E.s_pos
  have hs4 := E.s_lt_quarter.le
  have hu := E.u_bounds.1
  have hu5 := E.u_lt_fifth.le
  have hq := R.q_bounds
  have htr := R.truncation_identity
  change (R.d-min R.d E.lam)*(R.K-2*E.s)=0 at htr
  rw [E.lam_eq] at htr
  have hf := full_F_negative hs hs4 hu hu5 hq.1 hq.2 R.K_bounds.1 R.K_bounds.2 htr
  have ha : 1+2*E.s-R.K=R.A := by linarith [R.A_partition]
  rw [ha, ← E.mu_eq, ← E.lam_eq] at hf
  change (1+E.lam)*R.compensatedR-E.lam-(1-E.mu/R.A)*R.ell < 0 at hf
  have hex := Real.add_one_le_exp (R.ell/R.A)
  have hJ : R.ell/R.A ≤ R.J := by unfold J; linarith
  have hcoef : 1+E.lam-R.K=R.A-E.mu := by
    have hsum : E.mu+E.lam=2*E.s := by unfold s; ring
    linarith [R.A_partition]
  have hc : 0 ≤ 1+E.lam-R.K := by rw [hcoef]; linarith [R.A_bounds.2.1]
  have hm := mul_le_mul_of_nonneg_left hJ hc
  have he : (1+E.lam-R.K)*(R.ell/R.A)=(1-E.mu/R.A)*R.ell := by
    rw [hcoef]
    field_simp [R.A_bounds.1.ne']
  rw [he] at hm
  apply (le_div_iff₀ (show 0 < 1+E.lam by linarith [E.lam_pos])).mpr
  linarith

include R in
/-- All analytic and real-path obligations are discharged for normalized
counterexample data. Main.lean constructs this data from an arbitrary alleged
counterexample, using positive rescaling. -/
theorem impossible : False := by
  have h := E.frozen_comparison R.H R.H_subset R.A_bounds.1
    (R.dbar_bounds.2.2.trans E.lam_le_mu) R.tail_bounded R.compensated_certificate
    R.frozen_product_bound R.frozen_ratio_bound
  exact (not_lt_of_ge h) D.bad_output

end
end S2R.Instance.CertificateData.CostPair.RootData
