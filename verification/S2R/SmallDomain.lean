import S2R.AnalyticBounds
import S2R.Scalar

namespace S2R.Analysis
noncomputable section

def tau (s : ℝ) : ℝ := 4*s/(3+4*s)
def cutoffK (u : ℝ) : ℝ := 3/4*(1-u)
def z (s q : ℝ) : ℝ := s*(1-q)
def cutoffD (s u q : ℝ) : ℝ := z s q/(1-z s q/cutoffK u)
def omega (s u q : ℝ) : ℝ :=
  (z s q/cutoffK u-s*(1-3*q))^2/2

theorem tau_bounds {s : ℝ} (hs : 0 ≤ s) (hs4 : s ≤ 1/4) :
    s ≤ tau s ∧ tau s ≤ 1/4 := by
  have hp : 0 < 3+4*s := by linarith
  constructor
  · apply (le_div_iff₀ hp).mpr; nlinarith
  · apply (div_le_iff₀ hp).mpr; linarith

theorem omega_lower {s u q : ℝ} (hu : 0 ≤ u) (hu5 : u ≤ 1/5)
    (hq : 0 ≤ q) (hq3 : q ≤ 1/3) :
    s^2*((1+u)*(q+u)-2*u/3) ≤ omega s u q := by
  have hp : 0 < 1-u := by linarith
  have he : omega s u q-s^2*((1+u)*(q+u)-2*u/3) =
      s^2/(18*(1-u)^2) * ((5*q-4/5)^2+9/25
        +3*u*(1-3*q)*(q*(10-9*u)+u)+6*u^3*(5-3*q-3*u)) := by
    dsimp [omega, z, cutoffK]
    field_simp
    ring
  have h1 : 0 ≤ 1-3*q := by linarith
  have h2 : 0 ≤ 10-9*u := by linarith
  have h3 : 0 ≤ 5-3*q-3*u := by linarith
  have hn : 0 ≤ s^2/(18*(1-u)^2) * ((5*q-4/5)^2+9/25
        +3*u*(1-3*q)*(q*(10-9*u)+u)+6*u^3*(5-3*q-3*u)) := by positivity
  linarith

theorem cutoff_bounds {s u q : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hu : 0 ≤ u) (hu5 : u ≤ 1/5) (huq : u ≤ q) (hq3 : q ≤ 1/3) :
    0 < z s q ∧ z s q ≤ s ∧ z s q ≤ s*(1-u) ∧
      0 < cutoffK u-z s q ∧ cutoffK u-z s q ≤ 3/4 := by
  dsimp [z, cutoffK]
  have hq : 0 ≤ q := hu.trans huq
  have hz : 0 < s*(1-q) := mul_pos hs (by linarith)
  have hz1 : s*(1-q) ≤ s := by nlinarith
  have hzl : s*(1-q) ≤ s*(1-u) := by nlinarith
  exact ⟨hz, hz1, hzl, by linarith, by linarith⟩

theorem cutoff_identity {s u q : ℝ} (hk : cutoffK u ≠ 0) :
    cutoffD s u q = z s q*cutoffK u/(cutoffK u-z s q) := by
  unfold cutoffD
  rw [one_sub_div hk, div_div_eq_mul_div]

theorem loss_upper {s u q : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hu : 0 ≤ u) (hu5 : u ≤ 1/5) (huq : u ≤ q) (hq3 : q ≤ 1/3) :
    s*(1+u)*(s*(1+u)-cutoffD s u q) ≤
      s^2*(1+u)*(q+u)-s^3/2 := by
  have hb := cutoff_bounds hs hs4 hu hu5 huq hq3
  have hk : 0 < cutoffK u := by dsimp [cutoffK]; linarith
  have he : s*(1+u)*(s*(1+u)-cutoffD s u q) =
      s^2*(1+u)*(q+u)-s^3*(1+u)*(1-q)^2/(cutoffK u-z s q) := by
    rw [cutoff_identity hk.ne']
    have hd : cutoffK u-s*(1-q) ≠ 0 := hb.2.2.2.1.ne'
    dsimp [z]
    field_simp [hd]
    ring
  have hh : (cutoffK u-z s q)/2 ≤ (1+u)*(1-q)^2 := by
    have hq : 0 ≤ q := hu.trans huq
    have hsq : (2/3:ℝ)^2 ≤ (1-q)^2 := by nlinarith
    have hm := mul_nonneg hu (sq_nonneg (1-q))
    linarith [hb.2.2.2.2]
  have hh' : (1/2:ℝ) ≤ (1+u)*(1-q)^2/(cutoffK u-z s q) :=
    (le_div_iff₀ hb.2.2.2.1).mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hh' (pow_nonneg hs.le 3)
  rw [he]
  simp only [← mul_div_assoc, ← mul_assoc] at hmul
  nlinarith

theorem truncated_cutoff_bounds {s u q : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hu : 0 ≤ u) (hu5 : u ≤ 1/5) (huq : u ≤ q) (hq3 : q ≤ 1/3) :
    let X := (min (cutoffD s u q) (s*(1-u))-z s q)/s
    0 ≤ X ∧ X ≤ q-u ∧ X ≤ (1-u)*tau s := by
  dsimp only
  let X := (min (cutoffD s u q) (s*(1-u))-z s q)/s
  have hb := cutoff_bounds hs hs4 hu hu5 huq hq3
  have hk : 0 < cutoffK u := by dsimp [cutoffK]; linarith
  have hd : z s q ≤ cutoffD s u q := by
    rw [cutoff_identity hk.ne']
    apply (le_div_iff₀ hb.2.2.2.1).mpr
    nlinarith [sq_nonneg (z s q)]
  have hX : s*X = min (cutoffD s u q) (s*(1-u))-z s q := by dsimp [X]; field_simp
  have hX0 : 0 ≤ X := div_nonneg (sub_nonneg.mpr (le_min hd hb.2.2.1)) hs.le
  have hXq : X ≤ q-u := by
    have h := min_le_right (cutoffD s u q) (s*(1-u))
    dsimp [z] at hX
    nlinarith
  have hXd : min (cutoffD s u q) (s*(1-u))*(cutoffK u-z s q) ≤
      z s q*cutoffK u := by
    apply (le_div_iff₀ hb.2.2.2.1).mp
    rw [← cutoff_identity hk.ne']
    exact min_le_left _ _
  have h1 : cutoffK u*X ≤ z s q*(X+1-q) := by
    have hre : min (cutoffD s u q) (s*(1-u)) = s*X+z s q := by linarith [hX]
    rw [hre] at hXd
    dsimp [z] at hX hXd ⊢
    apply (mul_le_mul_left hs).mp
    nlinarith
  have h2 : cutoffK u*X ≤ z s q*(1-u) := by
    nlinarith [mul_nonneg hb.1.le (sub_nonneg.mpr hXq)]
  have h3 : cutoffK u*X ≤ s*(1-u-X)*(1-u) := by
    dsimp [z] at h2
    have hm := mul_le_mul_of_nonneg_right hXq
      (mul_nonneg hs.le (show 0 ≤ 1-u by linarith))
    nlinarith
  have h4 : (3/4:ℝ)*X ≤ s*(1-u-X) := by
    dsimp [cutoffK] at h3
    apply (mul_le_mul_right (show 0 < 1-u by linarith)).mp
    nlinarith
  have hXτ : X ≤ (1-u)*tau s := by
    have hp : 0 < 3+4*s := by linarith
    rw [tau, ← mul_div_assoc]
    exact (le_div_iff₀ hp).mpr (by nlinarith)
  exact ⟨hX0, hXq, hXτ⟩

set_option maxHeartbeats 1000000 in
theorem base_F_upper {s u q X : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hu : 0 ≤ u) (hu5 : u ≤ 1/5) (huq : u ≤ q) (hq3 : q ≤ 1/3)
    (hX : X ≤ (1-u)*tau s) :
    (1+s*(1-u))*r s u q-s*(1-u)-(1-s*(1+u))*s*(q+u-X)
      ≤ B s q-2*s/3*u^2 := by
  have hq : 0 ≤ q := hu.trans huq
  have ht := tau_bounds hs.le hs4
  have hL := L_quarter_lower hs.le hs4
  have hmu : s*(1+u) < 1 := by nlinarith
  have hsu : 0 < 1-u := by linarith
  have hss : 0 < 1-s := by linarith
  have hmup : 0 < 1-s*(1+u) := by linarith
  have hy : 0 ≤ 1+s*(1-u) := by positivity
  have hr := r_quadratic_upper (u := u) hs.le hs4 hq hq3
  have hh := mul_le_mul_of_nonneg_left (entropy_lower hu (by linarith)) hs.le
  have hr' : r s u q ≤ L s-s*u^2+s*(1+2*s)/(1-s)*q-s*(1+9*s/2)*q^2 := by linarith
  have hm := mul_le_mul_of_nonneg_left hr' hy
  have hx := mul_le_mul_of_nonneg_left hX
    (show 0 ≤ (1-s*(1+u))*s by positivity)
  have he : (1+s*(1-u))*(L s-s*u^2+s*(1+2*s)/(1-s)*q-s*(1+9*s/2)*q^2)
      -s*(1-u)-(1-s*(1+u))*s*(q+u-(1-u)*tau s) =
      B s q+s*u*(s-tau s-L s+s*(1+9*s/2)*q^2-3*s^2*q/(1-s))
        -s*u^2*(1-s*(tau s+u)) := by
    dsimp [B, tau]
    have h1 : 1-s ≠ 0 := by linarith
    have h2 : 3+4*s ≠ 0 := by linarith
    field_simp
    ring
  have hqs : q^2 ≤ 1/9 := by nlinarith
  have hv : (1+9*s/2)*q^2 ≤ 1/4 := by
    have hh := mul_le_mul_of_nonneg_left hqs (show 0 ≤ 1+9*s/2 by positivity)
    nlinarith
  have hb : s-tau s-L s+s*(1+9*s/2)*q^2-3*s^2*q/(1-s) ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_left hv hs.le
    have hn : 0 ≤ 3*s^2*q/(1-s) := by positivity
    nlinarith [ht.1]
  have hbu := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ s*u by positivity) hb
  have htu : s*(tau s+u) ≤ 1/3 := by
    have h1 : 0 ≤ tau s+u := by linarith [ht.1]
    nlinarith only [hs, hs4, hu, hu5, ht.2, h1]
  have hsq := mul_le_mul_of_nonneg_left htu (show 0 ≤ s*u^2 by positivity)
  nlinarith only [he, hm, hx, hbu, hsq]

set_option maxHeartbeats 1000000 in
/-- The complete expression in (7.11), with the actual logarithmic function and
the truncated cutoff, is strictly negative throughout the residual domain.
Only numerical domain and grouping constraints are hypotheses here. -/
theorem full_F_negative {s u q K : ℝ} (hs : 0 < s) (hs4 : s ≤ 1/4)
    (hu : 0 ≤ u) (hu5 : u ≤ 1/5) (huq : u ≤ q) (hq3 : q ≤ 1/3)
    (hKlow : 2*s ≤ K) (hKhigh : K ≤ cutoffK u)
    (htrunc : (cutoffD s u q-min (cutoffD s u q) (s*(1-u)))*(K-2*s) = 0) :
    (1+s*(1-u))*(r s u q-omega s u q*((K-2*s)/(1+2*s-K)))-s*(1-u)
      -(1-s*(1+u)/(1+2*s-K))*(s*(1+u)-min (cutoffD s u q) (s*(1-u))) < 0 := by
  let μ := s*(1+u)
  let lam := s*(1-u)
  let A := 1+2*s-K
  let t := (K-2*s)/A
  let d := cutoffD s u q
  let db := min d lam
  let X := (db-z s q)/s
  let F0 := (1+lam)*r s u q-lam-(1-μ)*(μ-db)
  have hk : K ≤ 3/4 := by
    dsimp [cutoffK] at hKhigh
    linarith
  have hA : 0 < A := by dsimp [A]; linarith
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hKlow) hA.le
  have ht3 : t ≤ 3 := by
    apply (div_le_iff₀ hA).mpr
    dsimp [A]
    linarith
  have hy : 1 ≤ 1+lam := by dsimp [lam]; nlinarith
  have hw : 0 ≤ omega s u q := by unfold omega; positivity
  have hX := truncated_cutoff_bounds hs hs4 hu hu5 huq hq3
  have hbase := base_F_upper hs hs4 hu hu5 huq hq3 hX.2.2
  have hxe : s*(q+u-X) = μ-db := by
    dsimp [X, μ, z]
    field_simp
    ring
  change (1+lam)*r s u q-lam-(1-μ)*s*(q+u-X) ≤ B s q-2*s/3*u^2 at hbase
  rw [mul_assoc, hxe] at hbase
  have hloss : μ*(μ-d) ≤ s^2*((1+u)*(q+u))-s^3/2 := by
    dsimp [μ, d]
    nlinarith only [loss_upper hs hs4 hu hu5 huq hq3]
  have hneg := final_scalar_certificate hs hs4 ht ht3 hy hw hbase
    hloss
    (omega_lower (s := s) hu hu5 (hu.trans huq) hq3)
  have hzero : t*μ*(d-db)=0 := by
    calc
      _ = (μ/A)*((d-db)*(K-2*s)) := by dsimp [t]; ring
      _ = 0 := by rw [htrunc]; ring
  have hat : A*(1+t)=1 := by dsimp [t, A]; field_simp
  have hdiv : μ/A = μ*(1+t) := by
    apply (div_eq_iff hA.ne').mpr
    calc
      μ = μ*(A*(1+t)) := by rw [hat]; ring
      _ = μ*(1+t)*A := by ring
  change (1+lam)*(r s u q-omega s u q*t)-lam-(1-μ/A)*(μ-db) < 0
  rw [hdiv]
  change F0+t*(μ*(μ-d)-(1+lam)*omega s u q) < 0 at hneg
  dsimp [F0] at hneg
  nlinarith only [hneg, hzero]

end
end S2R.Analysis

