import S2R.Entropy
import Mathlib.Data.Complex.ExponentialBounds

namespace S2R.Analysis
noncomputable section
open Set

theorem exp_one_bounds : (27/10:ℝ) < Real.exp 1 ∧ Real.exp 1 < 11/4 := by
  constructor <;> linarith [Real.exp_one_gt_d9, Real.exp_one_lt_d9]
theorem b_bounds : (4/11:ℝ) < b ∧ b < 10/27 := by
  constructor <;> nlinarith [b_mul_exp_one, exp_one_bounds.1, exp_one_bounds.2, b_pos]

theorem log_lower_fraction {x : ℝ} (hx : 0 ≤ x) : 2*x/(2+x) ≤ Real.log (1+x) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt (fun z => Real.log (1+z)-2*z/(2+z))
        (t^2/((1+t)*(2+t)^2)) t := by
    have h1 : 1+t ≠ 0 := by linarith [ht.1]
    have h2 : 2+t ≠ 0 := by linarith [ht.1]
    convert (((hasDerivAt_id t).const_add 1).log h1).sub
      (((hasDerivAt_id t).const_mul 2).div ((hasDerivAt_id t).const_add 2) h2) using 1
    simp only [id_eq]
    field_simp
    ring
  have h := nonneg_of_derivative hx hd (fun t ht => by
    have h1 : 0 < 1+t := by linarith [ht.1]
    have h2 : 0 < 2+t := by linarith [ht.1]
    positivity) (by norm_num)
  linarith

theorem log_lower_quartic {x : ℝ} (hx : 0 ≤ x) :
    x-x^2/2+x^3/3-x^4/4 ≤ Real.log (1+x) := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt (fun z => Real.log (1+z)-(z-z^2/2+z^3/3-z^4/4)) (t^4/(1+t)) t := by
    have h1 : 1+t ≠ 0 := by linarith [ht.1]
    convert (((hasDerivAt_id t).const_add 1).log h1).sub
      ((((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
        (((hasDerivAt_id t).pow 3).div_const 3)).sub (((hasDerivAt_id t).pow 4).div_const 4)) using 1
    simp only [id_eq]
    field_simp
    ring
  have h := nonneg_of_derivative hx hd (fun t ht => by
    have h1 : 0 < 1+t := by linarith [ht.1]
    positivity) (by norm_num)
  linarith

theorem log_upper_cubic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1+x) ≤ x-x^2/2+x^3/3 := by
  have hd (t : ℝ) (ht : t ∈ Icc 0 x) :
      HasDerivAt (fun z => z-z^2/2+z^3/3-Real.log (1+z)) (t^3/(1+t)) t := by
    have h1 : 1+t ≠ 0 := by linarith [ht.1]
    convert (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 3).div_const 3)).sub
      (((hasDerivAt_id t).const_add 1).log h1) using 1
    simp only [id_eq]
    field_simp
    ring
  have h := nonneg_of_derivative hx hd (fun t ht => by
    have h1 : 0 < 1+t := by linarith [ht.1]
    exact div_nonneg (pow_nonneg ht.1 3) h1.le) (by norm_num)
  linarith

theorem log_three_halves_bounds : (2/5:ℝ) < Real.log (3/2) ∧ Real.log (3/2) ≤ 5/12 := by
  have h1 := log_lower_quartic (show (0:ℝ) ≤ 1/2 by norm_num)
  have h2 := log_upper_cubic (show (0:ℝ) ≤ 1/2 by norm_num)
  norm_num at h1 h2
  constructor <;> linarith

/-- The uniform-parameter certificate controls the second bracket of (4.3). -/
theorem uniform_exp_bound {p : ℝ} (hp : 0 ≤ p) (hpmax : p ≤ 1-2*b) :
    (1-p)*Real.exp (Real.exp 1*p-1) ≤ b+p := by
  let e := Real.exp 1
  have he : 0 < e := Real.exp_pos 1
  have he3 : e < 3 := by dsimp [e]; linarith [exp_one_bounds.2]
  have hp1 : 0 < 1-p := by linarith [b_pos]
  have hx : 0 ≤ e*p := mul_nonneg he.le hp
  have hemax : 2+e*p ≤ e := by
    have h := mul_le_mul_of_nonneg_left hpmax he.le
    have hb : b*e=1 := b_mul_exp_one
    nlinarith only [h, hb]
  have hl := log_lower_fraction hx
  have hh : 2*p ≤ 2*(e*p)/(2+e*p) := by
    apply (le_div_iff₀ (show 0 < 2+e*p by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hemax (show 0 ≤ 2*p by positivity)]
  have hm := Real.log_le_sub_one_of_pos hp1
  have hp3 : e*p ≤ 3*p := mul_le_mul_of_nonneg_right he3.le hp
  have hlog : e*p ≤ Real.log (1+e*p)-Real.log (1-p) := by linarith
  have hex := Real.exp_le_exp.mpr hlog
  rw [Real.exp_sub, Real.exp_log (show 0 < 1+e*p by linarith), Real.exp_log hp1] at hex
  have hex' := (le_div_iff₀ hp1).mp hex
  have hmul := mul_le_mul_of_nonneg_left hex' b_pos.le
  have hbe : b*e=1 := b_mul_exp_one
  have heq : Real.exp (e*p-1)=Real.exp (e*p)*b := by rw [sub_eq_add_neg, Real.exp_add]; rfl
  change (1-p)*Real.exp (e*p-1) ≤ b+p
  rw [heq]
  have hbep : b*(e*p)=p := by rw [← mul_assoc, hbe, one_mul]
  nlinarith only [hmul, hbep]

def H0 (s : ℝ) : ℝ := (1+2*s)*Real.log (1+2*s)+2*s*Real.log (3/2)+s/(1+s)-4*s
def H0' (s : ℝ) : ℝ := 2*Real.log (1+2*s)+2*Real.log (3/2)+1/(1+s)^2-2
def H0'' (s : ℝ) : ℝ := 4/(1+2*s)-2/(1+s)^3

theorem deriv_H0 {s : ℝ} (hs : 0 ≤ s) : HasDerivAt H0 (H0' s) s := by
  have h1 : 1+2*s ≠ 0 := by linarith
  have h2 : 1+s ≠ 0 := by linarith
  have hd := ((hasDerivAt_id s).const_mul 2).const_add 1
  convert (((hd.mul (hd.log h1)).add
    (((hasDerivAt_id s).const_mul 2).mul_const (Real.log (3/2)))).add
      ((hasDerivAt_id s).div ((hasDerivAt_id s).const_add 1) h2)).sub
      ((hasDerivAt_id s).const_mul 4) using 1
  simp only [id_eq]
  dsimp [H0']
  field_simp
  ring
theorem deriv_H0' {s : ℝ} (hs : 0 ≤ s) : HasDerivAt H0' (H0'' s) s := by
  have h1 : 1+2*s ≠ 0 := by linarith
  have h2 : (1+s)^2 ≠ 0 := pow_ne_zero _ (by linarith)
  convert (((((((hasDerivAt_id s).const_mul 2).const_add 1).log h1).const_mul 2).add_const
    (2*Real.log (3/2))).add ((hasDerivAt_const s 1).div
      (((hasDerivAt_id s).const_add 1).pow 2) h2)).sub_const 2 using 1
  simp only [id_eq]
  dsimp [H0'']
  field_simp
  ring
theorem H0_second_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ H0'' s := by
  have h1 : 0 < 1+2*s := by linarith
  have h2 : 0 < 1+s := by linarith
  have he : H0'' s = (2+8*s+12*s^2+4*s^3)/((1+2*s)*(1+s)^3) := by
    dsimp [H0'']; field_simp; ring
  rw [he]
  positivity
theorem H0_positive {s : ℝ} (hs : 1/4 ≤ s) : 0 < H0 s := by
  have hs0 : 0 ≤ s := by linarith
  have hd (x : ℝ) (hx : x ∈ Icc 0 s) := deriv_H0 hx.1
  have hd' (x : ℝ) (hx : x ∈ Icc 0 s) := deriv_H0' hx.1
  have hm := monotone_on_interval hd' (fun x hx => H0_second_nonneg hx.1)
  have hquarter : 0 < H0 (1/4) := by
    norm_num [H0]
    linarith [log_three_halves_bounds.1]
  have ht := tangent_lower hd hm (show (1/4:ℝ) ∈ Icc 0 s by constructor <;> linarith)
    (show (0:ℝ) ∈ Icc 0 s by constructor <;> linarith)
  have hzero : H0 0=0 := by norm_num [H0]
  rw [hzero] at ht
  have hpos : 0 < H0' (1/4) := by nlinarith only [ht, hquarter]
  have hg : MonotoneOn H0 (Icc (1/4) s) := by
    apply monotone_on_interval (fun x hx => deriv_H0 (by linarith [hx.1]))
    intro x hx
    exact hpos.le.trans (hm ⟨by norm_num, hs⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1)
  exact hquarter.trans_le (hg ⟨le_rfl, hs⟩ ⟨hs, le_rfl⟩ hs)

def largeCostBase (s : ℝ) : ℝ :=
  let β := min (b*(1+2*s)) (2/3)
  1+b-β+b*(1+2*s)*Real.log β+2*b*s*Real.log (3/2)

theorem large_cost_strict {s : ℝ} (hs : 1/4 ≤ s) :
    alpha < largeCostBase s+b*s/(1+s) := by
  have hs0 : 0 ≤ s := by linarith
  have hC : 0 < 1+2*s := by linarith
  have hS : 0 < 1+s := by linarith
  by_cases hcut : b*(1+2*s) ≤ 2/3
  · have he : largeCostBase s+b*s/(1+s)-alpha = b*H0 s := by
      dsimp [largeCostBase]
      rw [min_eq_left hcut, Real.log_mul b_pos.ne' hC.ne']
      have hb : Real.log b = -1 := by simp [b]
      rw [hb]
      unfold alpha H0
      ring
    have hp := mul_pos b_pos (H0_positive hs)
    linarith
  · have hcut' : 2/3 ≤ b*(1+2*s) := le_of_not_ge hcut
    have hb4 : b < 2/5 := by linarith [b_bounds.2]
    have hs3 : 1/3 ≤ s := by
      have hm := mul_lt_mul_of_pos_right hb4 hC
      nlinarith only [hcut', hm]
    have hfrac : (1/4:ℝ) ≤ s/(1+s) := (le_div_iff₀ hS).mpr (by linarith)
    have he : largeCostBase s = 1/3+b-b*Real.log (3/2) := by
      dsimp [largeCostBase]
      rw [min_eq_right hcut']
      have hl : Real.log (2/3:ℝ) = -Real.log (3/2) := by
        rw [← Real.log_inv]
        norm_num
      rw [hl]
      ring
    rw [he]
    have hlog := mul_le_mul_of_nonneg_left log_three_halves_bounds.2 b_pos.le
    have hfrac' := mul_le_mul_of_nonneg_left hfrac b_pos.le
    simp only [← mul_div_assoc] at hfrac'
    unfold alpha
    nlinarith [b_bounds.1]

end
end S2R.Analysis
