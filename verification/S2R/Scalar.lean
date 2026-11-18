import S2R.Analysis

namespace S2R.Analysis
noncomputable section

def B (s q : ℝ) : ℝ := (1+s)*L s-s + 4*s^2*(1-s)/(3+4*s)
  + s^2*(5+s)/(1-s)*q - s*(1+s)*(1+9*s/2)*q^2
def H (s : ℝ) : ℝ := (1+s)*L s-s + 4*s^2*(1-s)/(3+4*s)
  + s^3*(5+s)^2/(2*(1-s)^2*(1+s)*(2+9*s))
def D (s : ℝ) : ℝ := (1-s)^2*(1+s)*(2+9*s)*(3+4*s)
def P (s : ℝ) : ℝ := (1-4*s)*(1-s+42*s^2+8*s^3*(5-s))+24*s^5

theorem D_pos {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) : 0 < D s := by
  have h1 : 0 < 1-s := by linarith
  unfold D
  positivity

theorem P_pos {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4) : 0 < P s := by
  have h1 : 0 ≤ 1-4*s := by linarith
  have h2 : 0 < 1-s := by linarith
  have h3 : 0 < 5-s := by linarith
  unfold P
  positivity

/-- Exact rational identity underlying manuscript equation (10.4). -/
theorem final_rational_identity {s : ℝ} (h1 : 1-s ≠ 0) (h2 : 1+s ≠ 0)
    (h3 : 2+9*s ≠ 0) (h4 : 3+4*s ≠ 0) :
    -(3/2)*s^2*(1+s)-s^4/2 + 4*s^2*(1-s)/(3+4*s)
      + s^3*(5+s)^2/(2*(1-s)^2*(1+s)*(2+9*s)) =
    -s^2*P s/D s - s^6*(1+107*s^2+36*s^3)/(2*D s) := by
  dsimp [D, P]
  field_simp
  ring

theorem H_negative {s : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4) : H s < 0 := by
  have h1 : 1-s ≠ 0 := by linarith
  have h2 : 1+s ≠ 0 := by linarith
  have h3 : 2+9*s ≠ 0 := by linarith
  have h4 : 3+4*s ≠ 0 := by linarith
  have hb := L_reduced_upper hs.le hs4
  have hid := final_rational_identity h1 h2 h3 h4
  have hdp := D_pos hs.le hs4
  have hpp := P_pos hs hs4
  have hneg : -s^2*P s/D s < 0 := div_neg_of_neg_of_pos (by nlinarith [sq_pos_of_pos hs]) hdp
  have hnon : 0 ≤ s^6*(1+107*s^2+36*s^3)/(2*D s) := by positivity
  dsimp [H]
  linarith

theorem B_le_H {s q : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) : B s q ≤ H s := by
  have h1 : 1-s ≠ 0 := by linarith
  have h2 : 1+s ≠ 0 := by linarith
  have h3 : 2+9*s ≠ 0 := by linarith
  have hid : B s q-H s = -(s*(1+s)*(2+9*s)/2) *
      (q-s*(5+s)/((1-s)*(1+s)*(2+9*s)))^2 := by
    dsimp [B, H]
    field_simp
    ring
  have hn : 0 ≤ (s*(1+s)*(2+9*s)/2) *
      (q-s*(5+s)/((1-s)*(1+s)*(2+9*s)))^2 := by positivity
  linarith

/-- The entropy compensation absorbs the full correction term, including the
case where the untruncated difference mu-d is negative. -/
theorem compensation_square {s u t y a ω loss F0 Q : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ht3 : t ≤ 3) (hy : 1 ≤ y) (hw : 0 ≤ ω)
    (hF0 : F0 ≤ Q - 2*s/3*u^2)
    (hloss : loss ≤ s^2*a-s^3/2)
    (hω : s^2*(a-2*u/3) ≤ ω) :
    F0+t*(loss-y*ω) ≤ Q-2*s/3*(u-s*t/2)^2+s^3*t*(t-3)/6 := by
  have hyw : ω ≤ y*ω := by nlinarith
  have hb : loss-y*ω ≤ 2*s^2*u/3-s^3/2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hb ht
  nlinarith

theorem compensation_nonpositive {s u t y a ω loss F0 Q : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ht3 : t ≤ 3) (hy : 1 ≤ y) (hw : 0 ≤ ω)
    (hF0 : F0 ≤ Q - 2*s/3*u^2)
    (hloss : loss ≤ s^2*a-s^3/2)
    (hω : s^2*(a-2*u/3) ≤ ω) : F0+t*(loss-y*ω) ≤ Q := by
  have h := compensation_square hs ht ht3 hy hw hF0 hloss hω
  have hsq : 0 ≤ 2*s/3*(u-s*t/2)^2 := by positivity
  have hprod : s^3*t*(t-3) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  linarith

theorem final_scalar_certificate {s q u t y a ω loss F0 : ℝ}
    (hs : 0 < s) (hs4 : s ≤ 1/4) (ht : 0 ≤ t) (ht3 : t ≤ 3)
    (hy : 1 ≤ y) (hw : 0 ≤ ω)
    (hF0 : F0 ≤ B s q - 2*s/3*u^2)
    (hloss : loss ≤ s^2*a-s^3/2)
    (hω : s^2*(a-2*u/3) ≤ ω) : F0+t*(loss-y*ω) < 0 :=
  lt_of_le_of_lt (compensation_nonpositive hs.le ht ht3 hy hw hF0 hloss hω)
    (lt_of_le_of_lt (B_le_H hs.le hs4) (H_negative hs hs4))

end
end S2R.Analysis
