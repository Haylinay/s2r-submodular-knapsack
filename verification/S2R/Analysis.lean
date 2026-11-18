import S2R.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv

namespace S2R.Analysis
noncomputable section
open Set

def b : ℝ := Real.exp (-1)
def alpha : ℝ := 1 - b

theorem b_pos : 0 < b := Real.exp_pos _
theorem b_lt_one : b < 1 := by
  simpa [b] using (Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num))
theorem alpha_pos : 0 < alpha := by unfold alpha; linarith [b_lt_one]
theorem alpha_lt_one : alpha < 1 := by unfold alpha; linarith [b_pos]
theorem b_mul_exp_one : b * Real.exp 1 = 1 := by
  rw [b, ← Real.exp_add]
  norm_num

theorem monotone_on_interval {a c : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc a c, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc a c, 0 ≤ f' x) : MonotoneOn f (Icc a c) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a c)
  · exact fun x hx => (hf x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt
  · exact fun x hx => hn x (interior_subset hx)

theorem nonneg_of_derivative {c : ℝ} (hc : 0 ≤ c) {f f' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 c, HasDerivAt f (f' x) x)
    (hn : ∀ x ∈ Icc 0 c, 0 ≤ f' x) (h0 : 0 ≤ f 0) : 0 ≤ f c :=
  h0.trans (monotone_on_interval hf hn ⟨le_rfl, hc⟩ ⟨hc, le_rfl⟩ hc)

theorem nonneg_of_second_derivative {c : ℝ} (hc : 0 ≤ c) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x ∈ Icc 0 c, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc 0 c, HasDerivAt f' (f'' x) x)
    (hn : ∀ x ∈ Icc 0 c, 0 ≤ f'' x) (h0 : 0 ≤ f 0) (h0' : 0 ≤ f' 0) :
    0 ≤ f c := by
  apply nonneg_of_derivative hc hf _ h0
  intro x hx
  exact h0'.trans (monotone_on_interval hf' hn ⟨le_rfl, hc⟩ hx hx.1)

/-- The elementary supporting-line inequality used in section 3. -/
theorem cap_log_dual {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    min t 1 + max (Real.log t) 0 ≤ τ*t - Real.log τ := by
  by_cases ht1 : 1 ≤ t
  · rw [min_eq_right ht1, max_eq_left (Real.log_nonneg ht1)]
    have h := Real.log_le_sub_one_of_pos (mul_pos hτ ht)
    rw [Real.log_mul hτ.ne' ht.ne'] at h
    linarith
  · have ht1' : t ≤ 1 := le_of_not_ge ht1
    rw [min_eq_left ht1', max_eq_right (Real.log_nonpos ht.le ht1')]
    have h := Real.log_le_sub_one_of_pos hτ
    have hm := mul_le_mul_of_nonneg_left ht1' (sub_nonneg.mpr hτ1)
    nlinarith

theorem log_plus_bound {t : ℝ} (ht : 0 < t) : max (Real.log t) 0 ≤ t / Real.exp 1 := by
  apply max_le
  · have h := Real.exp_one_mul_le_exp (x := Real.log t)
    rw [Real.exp_log ht] at h
    exact (le_div_iff₀ (Real.exp_pos 1)).mpr (by simpa [mul_comm] using h)
  · positivity

def L (s : ℝ) : ℝ := 4*s - (1+2*s)*Real.log (1+2*s) + Real.log (1-s)
def L' (s : ℝ) : ℝ := 2 - 2*Real.log (1+2*s) - 1/(1-s)
def L'' (s : ℝ) : ℝ := -4/(1+2*s) - 1/(1-s)^2

theorem deriv_L {s : ℝ} (hc : 1+2*s ≠ 0) (hs : 1-s ≠ 0) : HasDerivAt L (L' s) s := by
  have hC : HasDerivAt (fun x : ℝ => 1+2*x) 2 s := by
    convert (hasDerivAt_const s 1).add ((hasDerivAt_id s).const_mul 2) using 1 <;> norm_num
  have hS : HasDerivAt (fun x : ℝ => 1-x) (-1) s := by
    convert (hasDerivAt_const s 1).sub (hasDerivAt_id s) using 1 <;> norm_num
  have h := ((hasDerivAt_id s).const_mul 4).sub (hC.mul (hC.log hc))
  convert h.add (hS.log hs) using 1
  dsimp [L']
  field_simp
  ring

theorem deriv_L' {s : ℝ} (hc : 1+2*s ≠ 0) (hs : 1-s ≠ 0) : HasDerivAt L' (L'' s) s := by
  have hC : HasDerivAt (fun x : ℝ => 1+2*x) 2 s := by
    convert (hasDerivAt_const s 1).add ((hasDerivAt_id s).const_mul 2) using 1 <;> norm_num
  have hS : HasDerivAt (fun x : ℝ => 1-x) (-1) s := by
    convert (hasDerivAt_const s 1).sub (hasDerivAt_id s) using 1 <;> norm_num
  convert ((hasDerivAt_const s 2).sub ((hC.log hc).const_mul 2)).sub
    ((hasDerivAt_const s 1).div hS hs) using 1
  dsimp [L'']
  field_simp
  ring

def polyL (s : ℝ) : ℝ := s - 5/2*s^2 + s^3 - 19/12*s^4 + 7/5*s^5
def polyL' (s : ℝ) : ℝ := 1 - 5*s + 3*s^2 - 19/3*s^3 + 7*s^4
def polyL'' (s : ℝ) : ℝ := -5 + 6*s - 19*s^2 + 28*s^3

theorem deriv_polyL (s : ℝ) : HasDerivAt polyL (polyL' s) s := by
  convert (((((hasDerivAt_id s).sub (((hasDerivAt_id s).pow 2).const_mul (5/2))).add
    ((hasDerivAt_id s).pow 3)).sub (((hasDerivAt_id s).pow 4).const_mul (19/12))).add
    (((hasDerivAt_id s).pow 5).const_mul (7/5))) using 1 <;> dsimp [polyL, polyL'] <;> ring

theorem deriv_polyL' (s : ℝ) : HasDerivAt polyL' (polyL'' s) s := by
  convert (((((hasDerivAt_const s 1).sub ((hasDerivAt_id s).const_mul 5)).add
    (((hasDerivAt_id s).pow 2).const_mul 3)).sub (((hasDerivAt_id s).pow 3).const_mul (19/3))).add
    (((hasDerivAt_id s).pow 4).const_mul 7)) using 1 <;> dsimp [polyL', polyL''] <;> ring

theorem L_le_polyL {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) : L s ≤ polyL s := by
  have hd1 (x : ℝ) (hx : x ∈ Icc 0 s) : HasDerivAt (fun z => polyL z-L z) (polyL' x-L' x) x :=
    (deriv_polyL x).sub (deriv_L (by linarith [hx.1]) (by linarith [hx.2]))
  have hd2 (x : ℝ) (hx : x ∈ Icc 0 s) :
      HasDerivAt (fun z => polyL' z-L' z) (polyL'' x-L'' x) x :=
    (deriv_polyL' x).sub (deriv_L' (by linarith [hx.1]) (by linarith [hx.2]))
  have hnon (x : ℝ) (hx : x ∈ Icc 0 s) : 0 ≤ polyL'' x - L'' x := by
    have hC : 0 < 1+2*x := by linarith [hx.1]
    have hS : 0 < 1-x := by linarith [hx.2]
    have he : polyL'' x-L'' x = x^4*(69-122*x+56*x^2) / ((1+2*x)*(1-x)^2) := by
      dsimp [polyL'', L'']
      field_simp
      ring
    rw [he]
    apply div_nonneg
    · apply mul_nonneg (pow_nonneg hx.1 4)
      nlinarith [sq_nonneg x, hx.2]
    · positivity
  have h := nonneg_of_second_derivative hs hd1 hd2 hnon
    (by norm_num [polyL, L]) (by norm_num [polyL', L'])
  linarith

theorem L_reduced_upper {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) :
    (1+s)*L s-s ≤ -(3/2)*s^2*(1+s) - s^4/2 := by
  have h1 := mul_le_mul_of_nonneg_left (L_le_polyL hs hs4) (by linarith : 0 ≤ 1+s)
  have hsq : s^2 ≤ s/4 := by nlinarith
  have hpos : 0 ≤ 5+11*s-84*s^2 := by nlinarith
  have hprod := mul_nonneg (pow_nonneg hs 4) hpos
  dsimp [polyL] at h1
  nlinarith

end
end S2R.Analysis
