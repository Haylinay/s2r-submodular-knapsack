import S2R.Analysis

namespace S2R.Analysis
noncomputable section
open Set

def excess {ι : Type*} (T : Finset ι) (c : ι → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ T, max (c i-z) 0

theorem excess_antitone {ι : Type*} (T : Finset ι) (c : ι → ℝ) : Antitone (excess T c) := by
  intro x y hxy
  exact Finset.sum_le_sum (fun i _ => max_le_max (by linarith) le_rfl)

theorem excess_continuous {ι : Type*} (T : Finset ι) (c : ι → ℝ) : Continuous (excess T c) :=
  continuous_finset_sum T (fun i _ => (continuous_const.sub continuous_id).max continuous_const)

theorem excess_nonneg {ι : Type*} (T : Finset ι) (c : ι → ℝ) (z : ℝ) : 0 ≤ excess T c z :=
  Finset.sum_nonneg (fun i _ => le_max_right _ _)

def rootFunction {ι : Type*} (T : Finset ι) (c : ι → ℝ) (mu lam z : ℝ) : ℝ :=
  max (mu-z) 0+max (lam-z) 0+excess T c z-z

theorem rootFunction_strictAnti {ι : Type*} (T : Finset ι) (c : ι → ℝ) (mu lam : ℝ) :
    StrictAnti (rootFunction T c mu lam) := by
  intro x y hxy
  have h1 : max (mu-y) 0 ≤ max (mu-x) 0 := max_le_max (by linarith) le_rfl
  have h2 : max (lam-y) 0 ≤ max (lam-x) 0 := max_le_max (by linarith) le_rfl
  have h3 := excess_antitone T c hxy.le
  unfold rootFunction
  linarith

theorem cost_root_exists_unique {ι : Type*} (T : Finset ι) (c : ι → ℝ) {mu lam : ℝ}
    (hmu : 0 < mu) (hlam : 0 < lam) (horder : lam ≤ mu)
    (hc : ∀ i ∈ T, 0 < c i ∧ c i ≤ lam) (hsum : ∑ i ∈ T, c i = 1) :
    ∃! z : ℝ, 0 < z ∧ z < mu ∧ rootFunction T c mu lam z = 0 := by
  have hcont : Continuous (rootFunction T c mu lam) :=
    (((continuous_const.sub continuous_id).max continuous_const).add
      ((continuous_const.sub continuous_id).max continuous_const)).add
      (excess_continuous T c) |>.sub continuous_id
  have hzero : rootFunction T c mu lam 0 = mu+lam+1 := by
    unfold rootFunction excess
    simp only [sub_zero, max_eq_left hmu.le, max_eq_left hlam.le]
    have he : (∑ i ∈ T, max (c i) 0) = ∑ i ∈ T, c i :=
      Finset.sum_congr rfl (fun i hi => max_eq_left (hc i hi).1.le)
    rw [he, hsum]
  have htop : rootFunction T c mu lam mu = -mu := by
    have he : excess T c mu = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact max_eq_right (by linarith [(hc i hi).2])
    simp [rootFunction, he, max_eq_right (show lam-mu ≤ 0 by linarith)]
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc' hmu.le hcont.continuousOn
    (show 0 ∈ Icc (rootFunction T c mu lam mu) (rootFunction T c mu lam 0) by
      rw [hzero, htop]; constructor <;> linarith)
  have hz0 : 0 < z := by
    have hn : z ≠ 0 := by intro h; subst z; linarith
    exact lt_of_le_of_ne hz.1 hn.symm
  have hzm : z < mu := by
    have hn : z ≠ mu := by intro h; subst z; linarith
    exact lt_of_le_of_ne hz.2 hn
  refine ⟨z, ⟨hz0, hzm, he⟩, ?_⟩
  intro y hy
  exact (rootFunction_strictAnti T c mu lam).injective (hy.2.2.trans he.symm)

theorem cost_root_bounds {ι : Type*} (T : Finset ι) (c : ι → ℝ) {mu lam z : ℝ}
    (hlam : 0 < lam) (horder : lam ≤ mu) (hbalance : mu < 2*lam)
    (hc : ∀ i ∈ T, c i ≤ lam) (hz : 0 < z)
    (he : rootFunction T c mu lam z = 0) :
    z ≤ lam ∧ (mu+lam)/3 ≤ z ∧ excess T c z = 3*z-mu-lam := by
  have hzl : z ≤ lam := by
    by_contra hnot
    have hlz : lam < z := lt_of_not_ge hnot
    have ht : excess T c z = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact max_eq_right (by linarith [hc i hi])
    have hl : max (lam-z) 0 = 0 := max_eq_right (by linarith)
    unfold rootFunction at he
    rw [ht, hl] at he
    by_cases hmu : mu-z ≤ 0
    · rw [max_eq_right hmu] at he
      linarith
    · rw [max_eq_left (le_of_not_ge hmu)] at he
      linarith
  have hzm : z ≤ mu := hzl.trans horder
  have her : excess T c z = 3*z-mu-lam := by
    unfold rootFunction at he
    rw [max_eq_left (sub_nonneg.mpr hzm), max_eq_left (sub_nonneg.mpr hzl)] at he
    linarith
  exact ⟨hzl, by linarith [excess_nonneg T c z], her⟩

theorem root_q_bounds {s u root : ℝ} (hs : 0 < s) (hu : 0 ≤ u)
    (hrootl : root ≤ s*(1-u)) (hrootmin : 2*s/3 ≤ root) :
    u ≤ 1-root/s ∧ 1-root/s ≤ 1/3 := by
  constructor
  · have h := (div_le_div_iff_of_pos_right hs).mpr hrootl
    have he : s*(1-u)/s = 1-u := by field_simp
    rw [he] at h
    linarith
  · have h := (div_le_div_iff_of_pos_right hs).mpr hrootmin
    have he : (2*s/3)/s = (2/3:ℝ) := by field_simp; ring
    rw [he] at h
    linarith

theorem tail_fraction_bounds {c s q : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hcs : c ≤ s) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ max (c-s*(1-q)) 0/c ∧ max (c-s*(1-q)) 0/c ≤ q := by
  constructor
  · exact div_nonneg (le_max_right _ _) hc.le
  · apply (div_le_iff₀ hc).mpr
    apply max_le
    · nlinarith
    · positivity

theorem tail_fraction_mean {ι : Type*} (T : Finset ι) (c : ι → ℝ) {s q : ℝ}
    (hc : ∀ i ∈ T, 0 < c i) (he : excess T c (s*(1-q)) = s*(1-3*q)) :
    (∑ i ∈ T, c i*(max (c i-s*(1-q)) 0/c i)) = s*(1-3*q) := by
  rw [← he]
  unfold excess
  apply Finset.sum_congr rfl
  intro i hi
  field_simp [(hc i hi).ne']

/-- Threshold grouping consumes at most k total cost; this is the cost-root
argument behind the nontrivial branch of (7.8). -/
theorem threshold_mass_bound {ι : Type*} (T H : Finset ι) (c : ι → ℝ) {root k : ℝ}
    (hHT : H ⊆ T) (hz : 0 < root) (hkz : root < k)
    (hroot : excess T c root = root)
    (hcut : ∀ i ∈ H, root*k/(k-root) ≤ c i) : (∑ i ∈ H, c i) ≤ k := by
  have hk : 0 < k := hz.trans hkz
  have hd : 0 < k-root := sub_pos.mpr hkz
  have hi (i : ι) (hiH : i ∈ H) : root*c i ≤ k*max (c i-root) 0 := by
    have h := (div_le_iff₀ hd).mp (hcut i hiH)
    have hmax := mul_le_mul_of_nonneg_left (le_max_left (c i-root) 0) hk.le
    nlinarith only [h, hmax]
  have hsum := Finset.sum_le_sum hi
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hex : (∑ i ∈ H, max (c i-root) 0) ≤ excess T c root :=
    Finset.sum_le_sum_of_subset_of_nonneg hHT (fun i _ _ => le_max_right _ _)
  rw [hroot] at hex
  have hm := mul_le_mul_of_nonneg_left hex hk.le
  exact (mul_le_mul_left hz).mp (by nlinarith only [hsum, hm])

end
end S2R.Analysis
