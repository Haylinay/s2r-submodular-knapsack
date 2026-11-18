import S2R.CostGrouping
import S2R.Entropy

namespace S2R.Instance.CertificateData.CostPair.RootData
noncomputable section
open S2R.Analysis
variable {n : ℕ} {I : Instance n} {D : I.CertificateData} {E : D.CostPair} (R : E.RootData)

def costEntropy : ℝ := ∑ i ∈ D.items, I.cost i*Real.log (max 1 (I.cost i/R.root))

theorem beta_bound : 0 < b*(1+2*E.s) ∧ b*(1+2*E.s) ≤ 5/9 := by
  have hC : 0 < 1+2*E.s := by linarith [E.s_pos]
  have h1 := mul_le_mul_of_nonneg_right b_bounds.2.le hC.le
  have hs := E.s_lt_quarter.le
  exact ⟨mul_pos b_pos hC, by linarith⟩
theorem beta_mu_le_root : b*(1+2*E.s)*E.mu ≤ R.root := by
  have hmu : E.mu ≤ 6*E.s/5 := by rw [E.mu_eq]; nlinarith [E.s_pos, E.u_lt_fifth]
  have h1 := mul_le_mul_of_nonneg_right (beta_bound (E := E)).2 E.mu_pos.le
  have h2 := mul_le_mul_of_nonneg_left hmu (show (0:ℝ) ≤ 5/9 by norm_num)
  linarith [R.root_bounds.2.1]

theorem entropy_certificate : alpha-b*(4*E.s-(1+2*E.s)*Real.log (1+2*E.s)-R.costEntropy)
    ≤ I.valueAt D.seed 1 := by
  let β := b*(1+2*E.s)
  let τ : Ground n → ℝ := fun i => β*max 1 (I.cost i/R.root)
  have hβ : 0 < β := (beta_bound (E := E)).1
  have hτ (i : Ground n) (hi : i ∈ D.items) : β ≤ τ i ∧ τ i ≤ 1 := by
    constructor
    · dsimp [τ]; nlinarith [le_max_left (1:ℝ) (I.cost i/R.root)]
    · dsimp [τ]
      rw [mul_max_of_nonneg _ _ hβ.le]
      apply max_le
      · have hb := (beta_bound (E := E)).2; change β ≤ 5/9 at hb; linarith
      · have hc := E.largest i hi
        change I.cost i ≤ E.mu at hc
        have hm := mul_le_mul_of_nonneg_left hc hβ.le
        have hb := R.beta_mu_le_root
        change β*E.mu ≤ R.root at hb
        rw [← mul_div_assoc]
        apply (div_le_iff₀ R.positive).mpr
        linarith
  have hextra (i : Ground n) : τ i-β = (β/R.root)*max (I.cost i-R.root) 0 := by
    dsimp [τ]
    by_cases hc : I.cost i ≤ R.root
    · have hd : I.cost i/R.root ≤ 1 := (div_le_iff₀ R.positive).mpr (by simpa using hc)
      rw [max_eq_left hd, max_eq_right (by linarith)]
      ring
    · have hd : 1 ≤ I.cost i/R.root := (le_div_iff₀ R.positive).mpr (by linarith)
      rw [max_eq_right hd, max_eq_left (by linarith)]
      field_simp [R.positive.ne']
      ring
  have hsum : (∑ i ∈ D.items, (τ i-β))=β := by
    simp_rw [hextra]
    rw [← Finset.mul_sum]
    change (β/R.root)*excess D.items I.cost R.root=β
    rw [R.full_root_equation]
    field_simp [R.positive.ne']
  have hlogs : (∑ i ∈ D.items, I.cost i*Real.log (τ i)) =
      (1+2*E.s)*Real.log β+R.costEntropy := by
    have he (i : Ground n) : I.cost i*Real.log (τ i)=
        I.cost i*Real.log β+I.cost i*Real.log (max 1 (I.cost i/R.root)) := by
      dsimp [τ]
      rw [Real.log_mul hβ.ne' (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_max_left _ _)))]
      ring
    simp_rw [he, Finset.sum_add_distrib]
    rw [← Finset.sum_mul]
    change I.totalCost D.items*Real.log β+R.costEntropy=_
    rw [E.total_cost_s]
  have h := D.unified_density_certificate τ hβ hτ
  rw [hsum, sub_self, mul_zero, add_zero, hlogs, ← I.valueAt_one] at h
  have hlog : Real.log β = -1+Real.log (1+2*E.s) := by
    dsimp [β]
    rw [Real.log_mul b_pos.ne' (by linarith [E.s_pos] : 1+2*E.s ≠ 0)]
    simp [b]
  rw [hlog] at h
  dsimp [β] at h
  unfold alpha
  nlinarith only [h]

theorem fraction_log {i : Ground n} : phi (R.fraction i)=Real.log (max 1 (I.cost i/R.root)) := by
  have hc := I.cost_pos i
  unfold fraction phi
  by_cases h : I.cost i ≤ R.root
  · have hd : I.cost i/R.root ≤ 1 := (div_le_iff₀ R.positive).mpr (by simpa using h)
    rw [max_eq_right (by linarith), max_eq_left hd]
    simp
  · have hd : 1 ≤ I.cost i/R.root := (le_div_iff₀ R.positive).mpr (by linarith)
    rw [max_eq_left (by linarith), max_eq_right hd]
    have he : 1-(I.cost i-R.root)/I.cost i=R.root/I.cost i := by field_simp [hc.ne']
    rw [he, Real.log_div R.positive.ne' hc.ne', Real.log_div hc.ne' R.positive.ne']
    ring

theorem entropy_decomposition : R.costEntropy = E.mu*Real.log (E.mu/R.root)+E.lam*Real.log (E.lam/R.root)+
    ∑ i ∈ E.tail, I.cost i*phi (R.fraction i) := by
  classical
  have he := Finset.sum_sdiff D.repair_subset (f := fun i => I.cost i*Real.log (max 1 (I.cost i/R.root)))
  have hpair : (∑ i ∈ D.repair, I.cost i*Real.log (max 1 (I.cost i/R.root))) =
      E.mu*Real.log (E.mu/R.root)+E.lam*Real.log (E.lam/R.root) := by
    have hm : 1 ≤ E.mu/R.root := (le_div_iff₀ R.positive).mpr (by linarith [R.root_bounds.1, E.lam_le_mu])
    have hl : 1 ≤ E.lam/R.root := (le_div_iff₀ R.positive).mpr (by linarith [R.root_bounds.1])
    simp only [E.repair_eq, Finset.sum_pair E.distinct]
    change E.mu*Real.log (max 1 (E.mu/R.root))+E.lam*Real.log (max 1 (E.lam/R.root))=_
    rw [max_eq_right hm, max_eq_right hl]
  rw [hpair] at he
  change (∑ i ∈ E.tail, I.cost i*Real.log (max 1 (I.cost i/R.root)))+_ = R.costEntropy at he
  simp_rw [← R.fraction_log] at he
  linarith

theorem head_entropy : E.mu*Real.log (E.mu/R.root)+E.lam*Real.log (E.lam/R.root) =
    E.s*entropy E.u-2*E.s*Real.log (1-R.q) := by
  have hs := E.s_pos
  have hp : 0 < 1+E.u := by linarith [E.u_bounds.1]
  have hm : 0 < 1-E.u := by linarith [E.u_bounds.2]
  have hq : 0 < 1-R.q := by linarith [R.q_bounds.2]
  rw [E.mu_eq, E.lam_eq, R.root_eq_z]
  unfold z
  rw [Real.log_div (mul_pos hs hp).ne' (mul_pos hs hq).ne',
    Real.log_div (mul_pos hs hm).ne' (mul_pos hs hq).ne',
    Real.log_mul hs.ne' hp.ne', Real.log_mul hs.ne' hm.ne', Real.log_mul hs.ne' hq.ne']
  unfold entropy
  ring

theorem entropy_compensation : E.s*entropy E.u-2*E.s*Real.log (1-R.q)+phi R.mean+
    omega E.s E.u R.q*((R.K-2*E.s)/R.A) ≤ R.costEntropy := by
  have hh : I.totalCost R.heavy < 1 := by
    have hA := R.A_bounds.1
    have hp := R.A_partition
    rw [R.K_decomposition] at hp
    linarith
  have hRcut : R.mean ≤ R.root/R.k := by
    apply (le_div_iff₀ R.k_bounds.1).mpr
    have h := mul_le_mul_of_nonneg_left R.k_bounds.2.2.1.le R.mean_nonneg
    linarith [R.mean_le_root]
  have h := weighted_entropy_compensation E.tail R.heavy I.cost R.fraction
    R.heavy_subset_tail (fun i _ => (I.cost_pos i).le) D.tail_cost' rfl R.fraction_mean hh
    (fun i hi => ⟨(R.fraction_bounds hi).1, (R.fraction_bounds hi).2.trans_lt (by linarith [R.q_bounds.2])⟩)
    R.mean_nonneg R.mean_lt_one hRcut (fun i hi => R.heavy_fraction_lower hi)
  have hheavy : I.totalCost R.heavy=R.K-2*E.s := by linarith [R.K_decomposition]
  have ha : 1-I.totalCost R.heavy=R.A := by linarith [R.K_decomposition, R.A_partition]
  have he : I.totalCost R.heavy/(2*(1-I.totalCost R.heavy))*(R.root/R.k-R.mean)^2 =
      omega E.s E.u R.q*((R.K-2*E.s)/R.A) := by
    rw [ha, hheavy, R.root_eq_z]
    dsimp [omega, k, mean]
    ring
  change phi R.mean+I.totalCost R.heavy/(2*(1-I.totalCost R.heavy))*(R.root/R.k-R.mean)^2 ≤ _ at h
  rw [he] at h
  rw [R.entropy_decomposition, R.head_entropy]
  linarith

theorem compensated_certificate :
    alpha-b*(r E.s E.u R.q-omega E.s E.u R.q*((R.K-2*E.s)/R.A)) ≤ I.valueAt D.seed 1 := by
  have he := R.entropy_compensation
  have h := R.entropy_certificate
  have hm := mul_le_mul_of_nonneg_left he b_pos.le
  have hmean : 1-R.mean=1-E.s+3*E.s*R.q := by unfold mean; ring
  unfold phi at hm
  rw [hmean] at hm
  unfold r
  nlinarith only [hm,h]

end
end S2R.Instance.CertificateData.CostPair.RootData

