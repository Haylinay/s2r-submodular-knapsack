import S2R.Analysis

namespace S2R.Analysis
noncomputable section
open Set

theorem L_lower {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) : s-3*s^2 ≤ L s := by
  have hd (x : ℝ) (hx : x ∈ Icc 0 s) :
      HasDerivAt (fun z => L z-z+3*z^2) (L' x-1+6*x) x := by
    convert ((deriv_L (by linarith [hx.1]) (by linarith [hx.2])).sub
      (hasDerivAt_id x)).add (((hasDerivAt_id x).pow 2).const_mul 3) using 1 <;> (try simp only [id_eq]) <;> ring
  have hd' (x : ℝ) (hx : x ∈ Icc 0 s) :
      HasDerivAt (fun z => L' z-1+6*z) (L'' x+6) x := by
    convert ((deriv_L' (by linarith [hx.1]) (by linarith [hx.2])).sub_const 1).add
      ((hasDerivAt_id x).const_mul 6) using 1 <;> (try simp only [id_eq]) <;> ring
  have hn (x : ℝ) (hx : x ∈ Icc 0 s) : 0 ≤ L'' x+6 := by
    have hc : 0 < 1+2*x := by linarith [hx.1]
    have hx1 : 0 < 1-x := by linarith [hx.2]
    have h1 : 4/(1+2*x) ≤ 4 := (div_le_iff₀ hc).mpr (by linarith [hx.1])
    have h2 : 1/(1-x)^2 ≤ 2 := (div_le_iff₀ (sq_pos_of_pos hx1)).mpr (by
      have hh : 3/4 ≤ 1-x := by linarith [hx.2]
      nlinarith [sq_nonneg (1-x-3/4)])
    dsimp [L'']
    simp only [neg_div]
    linarith
  have h := nonneg_of_second_derivative hs hd hd' hn
    (by norm_num [L]) (by norm_num [L'])
  linarith

theorem L_quarter_lower {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) : s/4 ≤ L s := by
  have h := L_lower hs hs4
  nlinarith

def entropy (u : ℝ) : ℝ := (1+u)*Real.log (1+u)+(1-u)*Real.log (1-u)
def entropy' (u : ℝ) : ℝ := Real.log (1+u)-Real.log (1-u)
def entropy'' (u : ℝ) : ℝ := 1/(1+u)+1/(1-u)

theorem deriv_entropy {u : ℝ} (hp : 1+u ≠ 0) (hm : 1-u ≠ 0) :
    HasDerivAt entropy (entropy' u) u := by
  have h1 := (hasDerivAt_id u).const_add 1
  have h2 := (hasDerivAt_id u).const_sub 1
  convert (h1.mul (h1.log hp)).add (h2.mul (h2.log hm)) using 1
  dsimp [entropy']
  field_simp
  ring

theorem deriv_entropy' {u : ℝ} (hp : 1+u ≠ 0) (hm : 1-u ≠ 0) :
    HasDerivAt entropy' (entropy'' u) u := by
  convert (((hasDerivAt_id u).const_add 1).log hp).sub
    (((hasDerivAt_id u).const_sub 1).log hm) using 1
  dsimp [entropy'']
  ring

theorem entropy_lower {u : ℝ} (hu : 0 ≤ u) (hu1 : u < 1) : u^2 ≤ entropy u := by
  have hd (x : ℝ) (hx : x ∈ Icc 0 u) :
      HasDerivAt (fun z => entropy z-z^2) (entropy' x-2*x) x := by
    convert (deriv_entropy (by linarith [hx.1]) (by linarith [hx.2])).sub
      ((hasDerivAt_id x).pow 2) using 1 <;> (try simp only [id_eq]) <;> ring
  have hd' (x : ℝ) (hx : x ∈ Icc 0 u) :
      HasDerivAt (fun z => entropy' z-2*z) (entropy'' x-2) x := by
    convert (deriv_entropy' (by linarith [hx.1]) (by linarith [hx.2])).sub
      ((hasDerivAt_id x).const_mul 2) using 1 <;> (try simp only [id_eq]) <;> ring
  have hn (x : ℝ) (hx : x ∈ Icc 0 u) : 0 ≤ entropy'' x-2 := by
    have hp : 0 < 1+x := by linarith [hx.1]
    have hm : 0 < 1-x := by linarith [hx.2]
    have he : entropy'' x-2 = 2*x^2/((1+x)*(1-x)) := by
      dsimp [entropy'']; field_simp; ring
    rw [he]; positivity
  have h := nonneg_of_second_derivative hu hd hd' hn
    (by norm_num [entropy]) (by norm_num [entropy'])
  linarith

def r (s u q : ℝ) : ℝ := 4*s-(1+2*s)*Real.log (1+2*s)-s*entropy u
  +2*s*Real.log (1-q)+Real.log (1-s+3*s*q)
def rQ' (s q : ℝ) : ℝ := -2*s/(1-q)+3*s/(1-s+3*s*q)
def rQ'' (s q : ℝ) : ℝ := -2*s/(1-q)^2-9*s^2/(1-s+3*s*q)^2

theorem deriv_rQ {s u q : ℝ} (h1 : 1-q ≠ 0) (h2 : 1-s+3*s*q ≠ 0) :
    HasDerivAt (r s u) (rQ' s q) q := by
  have h1d := (hasDerivAt_id q).const_sub 1
  have h2d := ((hasDerivAt_id q).const_mul (3*s)).const_add (1-s)
  convert (((h1d.log h1).const_mul (2*s)).const_add
    (4*s-(1+2*s)*Real.log (1+2*s)-s*entropy u)).add (h2d.log h2) using 1
  dsimp [rQ']; ring

theorem deriv_rQ' {s q : ℝ} (h1 : 1-q ≠ 0) (h2 : 1-s+3*s*q ≠ 0) :
    HasDerivAt (rQ' s) (rQ'' s q) q := by
  have h1d := (hasDerivAt_id q).const_sub 1
  have h2d := ((hasDerivAt_id q).const_mul (3*s)).const_add (1-s)
  convert ((hasDerivAt_const q (-2*s)).div h1d h1).add
    ((hasDerivAt_const q (3*s)).div h2d h2) using 1
  dsimp [rQ'']; ring

theorem r_quadratic_upper {s u q : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4)
    (hq : 0 ≤ q) (hq3 : q ≤ 1/3) :
    r s u q ≤ L s-s*entropy u+s*(1+2*s)/(1-s)*q-s*(1+9*s/2)*q^2 := by
  let a := s*(1+2*s)/(1-s)
  let v := s*(1+9*s/2)
  have hc : 1-s ≠ 0 := by linarith
  have hp (x : ℝ) (hx : x ∈ Icc 0 q) : 0 < 1-s+3*s*x := by
    nlinarith [hx.1]
  have hm (x : ℝ) (hx : x ∈ Icc 0 q) : 0 < 1-x := by linarith [hx.2]
  have hd (x : ℝ) (hx : x ∈ Icc 0 q) :
      HasDerivAt (fun z => L s-s*entropy u+a*z-v*z^2-r s u z)
        (a-2*v*x-rQ' s x) x := by
    convert ((((hasDerivAt_id x).const_mul a).const_add (L s-s*entropy u)).sub
      (((hasDerivAt_id x).pow 2).const_mul v)).sub (deriv_rQ (hm x hx).ne' (hp x hx).ne')
      using 1 <;> (try simp only [id_eq]) <;> ring
  have hd' (x : ℝ) (hx : x ∈ Icc 0 q) :
      HasDerivAt (fun z => a-2*v*z-rQ' s z) (-2*v-rQ'' s x) x := by
    convert (((hasDerivAt_id x).const_mul (2*v)).const_sub a).sub
      (deriv_rQ' (hm x hx).ne' (hp x hx).ne') using 1 <;> (try simp only [id_eq]) <;> ring
  have hn (x : ℝ) (hx : x ∈ Icc 0 q) : 0 ≤ -2*v-rQ'' s x := by
    have hx0 := hx.1
    have hmx : (1-x)^2 ≤ 1 := by nlinarith [hx.2]
    have hpx : 1-s+3*s*x ≤ 1 := by nlinarith [hx.2]
    have hpx2 : (1-s+3*s*x)^2 ≤ 1 := by nlinarith [hp x hx]
    have h1 : 2*s ≤ 2*s/(1-x)^2 := (le_div_iff₀ (sq_pos_of_pos (hm x hx))).mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hmx (show 0 ≤ 2*s by positivity)])
    have h2 : 9*s^2 ≤ 9*s^2/(1-s+3*s*x)^2 :=
      (le_div_iff₀ (sq_pos_of_pos (hp x hx))).mpr
        (by nlinarith [mul_le_mul_of_nonneg_left hpx2 (show 0 ≤ 9*s^2 by positivity)])
    dsimp [v, rQ'']; simp only [neg_mul, neg_div]; nlinarith
  have hz : 0 ≤ a-rQ' s 0 := by
    dsimp [a, rQ']; field_simp; ring_nf; positivity
  have h := nonneg_of_second_derivative hq hd hd' hn
    (by simp [L, r]; ring_nf; exact le_rfl) (by simpa using hz)
  dsimp [a, v] at h
  linarith

end
end S2R.Analysis


