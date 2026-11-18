import S2R.LargeCost

namespace S2R.Analysis
noncomputable section
open Set

def U (s u : ℝ) : ℝ :=
  2-(1+3*s/2)+2*s*u+s*(1-u)/(1+s*(1-u))+
  s*(1+u)*Real.log (2*b*(1+3*s/2)-2*s*u)+(1+s*(1-u))*Real.log (b*(1+3*s/2))
def Uu (s u : ℝ) : ℝ := 2*s-s/(1+s*(1-u))^2+
  s*Real.log (2*b*(1+3*s/2)-2*s*u)-2*s^2*(1+u)/(2*b*(1+3*s/2)-2*s*u)-
  s*Real.log (b*(1+3*s/2))
def Uuu (s u : ℝ) : ℝ := -2*s^2/(1+s*(1-u))^3-
  4*s^2/(2*b*(1+3*s/2)-2*s*u)-4*s^3*(1+u)/(2*b*(1+3*s/2)-2*s*u)^2

theorem unbalanced_parameters {s u : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4)
    (hu : 1/5 ≤ u) (hu1 : u ≤ 1) :
    0 < b*(1+3*s/2) ∧ b*(1+3*s/2) ≤ 2*b*(1+3*s/2)-2*s*u ∧
      2*b*(1+3*s/2)-2*s*u ≤ 1 := by
  have hL : 0 < 1+3*s/2 := by linarith
  have hlo := mul_lt_mul_of_pos_right b_bounds.1 hL
  have hhi := mul_lt_mul_of_pos_right (show b < 2/5 by linarith [b_bounds.2]) hL
  have hu0 : 0 ≤ u := by linarith
  refine ⟨mul_pos b_pos hL, ?_, ?_⟩
  · nlinarith
  · nlinarith

theorem deriv_Uu {s u : ℝ} (hy : 1+s*(1-u) ≠ 0)
    (hτ : 2*b*(1+3*s/2)-2*s*u ≠ 0) : HasDerivAt (U s) (Uu s u) u := by
  have hl := ((hasDerivAt_id u).const_sub 1).const_mul s
  have hy' := hl.const_add 1
  have hmu := ((hasDerivAt_id u).const_add 1).const_mul s
  have ht := ((hasDerivAt_id u).const_mul (2*s)).const_sub (2*b*(1+3*s/2))
  convert ((((((hasDerivAt_id u).const_mul (2*s)).const_add (2-(1+3*s/2))).add
    (hl.div hy' hy)).add (hmu.mul (ht.log hτ))).add
    (hy'.mul_const (Real.log (b*(1+3*s/2))))) using 1
  simp only [id_eq]
  dsimp [Uu]
  field_simp
  ring

set_option maxHeartbeats 1500000 in
theorem deriv_Uuu {s u : ℝ} (hy : 1+s*(1-u) ≠ 0)
    (hτ : 2*b*(1+3*s/2)-2*s*u ≠ 0) : HasDerivAt (Uu s) (Uuu s u) u := by
  have hy' := (((hasDerivAt_id u).const_sub 1).const_mul s).const_add 1
  have ht := ((hasDerivAt_id u).const_mul (2*s)).const_sub (2*b*(1+3*s/2))
  convert (((((hasDerivAt_const u (2*s)).sub
    ((hasDerivAt_const u s).div (hy'.pow 2) (pow_ne_zero 2 hy))).add
    ((ht.log hτ).const_mul s)).sub
    ((((hasDerivAt_id u).const_add 1).const_mul (2*s^2)).div ht hτ)).sub_const
    (s*Real.log (b*(1+3*s/2)))) using 1
  simp only [id_eq]
  dsimp [Uuu]
  generalize hB : 2*b*(1+3*s/2)-2*s*u = B0 at hτ ⊢
  generalize hY : 1+s*(1-u) = Y at hy ⊢
  field_simp [hy, hτ]
  ring

theorem U_concave {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) :
    ConcaveOn ℝ (Icc (1/5) 1) (U s) := by
  have hy (u : ℝ) (hu : u ∈ Icc (1/5) 1) : 0 < 1+s*(1-u) := by nlinarith [hu.2]
  have ht (u : ℝ) (hu : u ∈ Icc (1/5) 1) : 0 < 2*b*(1+3*s/2)-2*s*u :=
    (unbalanced_parameters hs hs4 hu.1 hu.2).1.trans_le
      (unbalanced_parameters hs hs4 hu.1 hu.2).2.1
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc _ _)
    (fun u hu => (deriv_Uu (hy u hu).ne' (ht u hu).ne').continuousAt.continuousWithinAt)
    (fun u hu => (deriv_Uu (hy u (interior_subset hu)).ne' (ht u (interior_subset hu)).ne').hasDerivWithinAt)
    (fun u hu => (deriv_Uuu (hy u (interior_subset hu)).ne' (ht u (interior_subset hu)).ne').hasDerivWithinAt)
  intro u hu
  have hu' := interior_subset hu
  have h1 := hy u hu'
  have h2 := ht u hu'
  have h3 : 0 ≤ 1+u := by linarith [hu'.1]
  unfold Uuu
  have ha : 0 ≤ 2*s^2/(1+s*(1-u))^3 := by positivity
  have hb : 0 ≤ 4*s^2/(2*b*(1+3*s/2)-2*s*u) := by positivity
  have hc : 0 ≤ 4*s^3*(1+u)/(2*b*(1+3*s/2)-2*s*u)^2 := by positivity
  simp only [neg_mul, neg_div]
  linarith

def gamma : ℝ := 3/2-Real.exp 1/5
def theta : ℝ := Real.exp 1-3/2
theorem gamma_bounds : (3/4:ℝ) ≤ gamma ∧ gamma ≤ 1 := by
  unfold gamma
  constructor <;> linarith [exp_one_bounds.1, exp_one_bounds.2]
theorem theta_bounds : 0 < theta ∧ theta < 5/4 := by
  unfold theta
  constructor <;> linarith [exp_one_bounds.1, exp_one_bounds.2]

theorem U_left_identity {s : ℝ} (hs : 0 ≤ s) :
    U s (1/5) = (1+4*s/5)*Real.log (1+3*s/2)+6*s/5*Real.log (1+gamma*s)+
      (4*s/5)/(1+4*s/5)+(6*Real.log 2/5-31/10)*s := by
  have hL : 0 < 1+3*s/2 := by linarith
  have hG : 0 < 1+gamma*s := by nlinarith [gamma_bounds.1]
  have he : 2*b*(1+3*s/2)-2*s*(1/5) = (2*b)*(1+gamma*s) := by
    unfold gamma
    have h := congrArg (fun t : ℝ => t*s) b_mul_exp_one
    dsimp only at h
    nlinarith only [h]
  unfold U
  rw [he, Real.log_mul (mul_pos (by norm_num : (0:ℝ) < 2) b_pos).ne' hG.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) b_pos.ne', Real.log_mul b_pos.ne' hL.ne']
  have hb : Real.log b = -1 := by simp [b]
  rw [hb]
  ring

theorem U_left_positive {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4) : 0 < U s (1/5) := by
  rw [U_left_identity hs.le]
  have hg := gamma_bounds
  have hlog := log_lower_fraction (show 0 ≤ 3*s/2 by positivity)
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1+4*s/5 by positivity)
  have hfirst : 3*s/2 ≤ (1+4*s/5)*Real.log (1+3*s/2) := by
    have hden : 0 < 2+3*s/2 := by positivity
    have hr : 3*s/2 ≤ (1+4*s/5)*(2*(3*s/2)/(2+3*s/2)) := by
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hden).mpr
      nlinarith only [sq_nonneg s]
    exact hr.trans hmul
  have hG : 0 ≤ gamma*s := mul_nonneg (by linarith) hs.le
  have hgs : gamma*s ≤ 1/4 := by nlinarith only [hg.1, hg.2, hs, hs4]
  have hsecond : 2*s/3 ≤ Real.log (1+gamma*s) := by
    have hr : 2*s/3 ≤ 2*(gamma*s)/(2+gamma*s) := by
      apply (le_div_iff₀ (show 0 < 2+gamma*s by linarith)).mpr
      have h1 := mul_le_mul_of_nonneg_left hg.1 hs.le
      have h2 := mul_le_mul_of_nonneg_left hgs (show 0 ≤ 2*s/3 by positivity)
      nlinarith only [h1, h2]
    exact hr.trans (log_lower_fraction hG)
  have hsm := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 6*s/5 by positivity)
  have hfrac : 4*s/5-16*s^2/25 ≤ (4*s/5)/(1+4*s/5) := by
    apply (le_div_iff₀ (show 0 < 1+4*s/5 by positivity)).mpr
    nlinarith only [pow_nonneg hs.le 3]
  have hlin : 0 < (6*Real.log 2/5-4/5)*s :=
    mul_pos (by linarith [Real.log_two_gt_d9]) hs
  nlinarith only [hfirst, hsm, hfrac, hlin, sq_nonneg s]

theorem U_right_identity {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) :
    U s 1 = Real.log (1+3*s/2)+2*s*Real.log (1-theta*s)+(2*Real.log 2-3/2)*s := by
  have hL : 0 < 1+3*s/2 := by linarith
  have hT : 0 < 1-theta*s := by nlinarith [theta_bounds.1, theta_bounds.2]
  have he : 2*b*(1+3*s/2)-2*s*1 = (2*b)*(1-theta*s) := by
    unfold theta
    have h := congrArg (fun t : ℝ => t*s) b_mul_exp_one
    dsimp only at h
    nlinarith only [h]
  unfold U
  rw [he, Real.log_mul (mul_pos (by norm_num : (0:ℝ) < 2) b_pos).ne' hT.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) b_pos.ne', Real.log_mul b_pos.ne' hL.ne']
  have hb : Real.log b = -1 := by simp [b]
  rw [hb]
  norm_num
  ring

theorem U_right_positive {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4) : 0 < U s 1 := by
  rw [U_right_identity hs.le hs4]
  have ht := theta_bounds
  have hT : 0 < 1-theta*s := by nlinarith
  have hfirst : 6*s/5 ≤ Real.log (1+3*s/2) := by
    apply le_trans _ (log_lower_fraction (show 0 ≤ 3*s/2 by positivity))
    apply (le_div_iff₀ (show 0 < 2+3*s/2 by positivity)).mpr
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hT)
  rw [Real.log_inv] at hlog
  have hsecond : -2*s ≤ Real.log (1-theta*s) := by
    have hr : (1-theta*s)⁻¹-1 ≤ 2*s := by
      rw [inv_eq_one_div]
      apply sub_le_iff_le_add.mpr
      apply (div_le_iff₀ hT).mpr
      have hm := mul_le_mul_of_nonneg_left ht.2.le (show 0 ≤ 1+2*s by positivity)
      nlinarith only [hm, hs, hs4]
    linarith
  have hm := mul_le_mul_of_nonneg_left hsecond (show 0 ≤ 2*s by positivity)
  have hlin : 0 < (2*Real.log 2-13/10)*s :=
    mul_pos (by linarith [Real.log_two_gt_d9]) hs
  nlinarith only [hfirst, hm, hlin, hs, hs4]

theorem unbalanced_cost_positive {s u : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hu : 1/5 ≤ u) (hu1 : u ≤ 1) : 0 < U s u := by
  have hcon := U_concave hs.le hs4
  let a := 5*(1-u)/4
  let c := (5*u-1)/4
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hc : 0 ≤ c := by dsimp [c]; linarith
  have hac : a+c=1 := by dsimp [a,c]; ring
  have h := hcon.2 (show (1/5:ℝ) ∈ Icc (1/5) 1 by constructor <;> norm_num)
    (show (1:ℝ) ∈ Icc (1/5) 1 by constructor <;> norm_num) ha hc hac
  simp only [smul_eq_mul] at h
  have he : a*(1/5)+c*1=u := by dsimp [a,c]; ring
  rw [he] at h
  have hleft := U_left_positive hs hs4
  have hright := U_right_positive hs hs4
  have hmin : 0 < min (U s (1/5)) (U s 1) := lt_min hleft hright
  have h1 := mul_le_mul_of_nonneg_left (min_le_left (U s (1/5)) (U s 1)) ha
  have h2 := mul_le_mul_of_nonneg_left (min_le_right (U s (1/5)) (U s 1)) hc
  have he' : a*min (U s (1/5)) (U s 1)+c*min (U s (1/5)) (U s 1)=min (U s (1/5)) (U s 1) := by
    rw [← add_mul, hac, one_mul]
  linarith

end
end S2R.Analysis
