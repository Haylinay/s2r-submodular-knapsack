import S2R.Analysis

namespace S2R.Analysis
noncomputable section
open Set

theorem tangent_lower {c a x : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ t ∈ Icc 0 c, HasDerivAt f (f' t) t)
    (hm : MonotoneOn f' (Icc 0 c)) (ha : a ∈ Icc 0 c) (hx : x ∈ Icc 0 c) :
    f a+f' a*(x-a) ≤ f x := by
  by_cases hax : a ≤ x
  · have hd (t : ℝ) (ht : t ∈ Icc a x) :
        HasDerivAt (fun z => f z-f' a*(z-a)) (f' t-f' a) t := by
      simpa using (hf t ⟨ha.1.trans ht.1, ht.2.trans hx.2⟩).sub
        (((hasDerivAt_id t).sub_const a).const_mul (f' a))
    have hn (t : ℝ) (ht : t ∈ Icc a x) : 0 ≤ f' t-f' a :=
      sub_nonneg.mpr (hm ha ⟨ha.1.trans ht.1, ht.2.trans hx.2⟩ ht.1)
    have h := monotone_on_interval hd hn ⟨le_rfl, hax⟩ ⟨hax, le_rfl⟩ hax
    nlinarith only [h]
  · have hxa : x ≤ a := le_of_not_ge hax
    have hd (t : ℝ) (ht : t ∈ Icc x a) :
        HasDerivAt (fun z => f' a*(z-a)-f z) (f' a-f' t) t := by
      simpa using (((hasDerivAt_id t).sub_const a).const_mul (f' a)).sub
        (hf t ⟨hx.1.trans ht.1, ht.2.trans ha.2⟩)
    have hn (t : ℝ) (ht : t ∈ Icc x a) : 0 ≤ f' a-f' t :=
      sub_nonneg.mpr (hm ⟨hx.1.trans ht.1, ht.2.trans ha.2⟩ ha ht.2)
    have h := monotone_on_interval hd hn ⟨le_rfl, hxa⟩ ⟨hxa, le_rfl⟩ hxa
    nlinarith only [h]

def phi (x : ℝ) : ℝ := -Real.log (1-x)

theorem phi_strong_tangent {x R : ℝ} (hx : 0 ≤ x) (hx1 : x < 1)
    (hR : 0 ≤ R) (hR1 : R < 1) :
    phi R+(x-R)/(1-R)+(x-R)^2/2 ≤ phi x := by
  let c := max x R
  have hc : c < 1 := max_lt hx1 hR1
  have hd (t : ℝ) (ht : t ∈ Icc 0 c) :
      HasDerivAt (fun z => phi z-z^2/2) (1/(1-t)-t) t := by
    have hn : 1-t ≠ 0 := by linarith [ht.2]
    convert ((((hasDerivAt_id t).const_sub 1).log hn).neg).sub
      (((hasDerivAt_id t).pow 2).div_const 2) using 1
    simp only [id_eq]
    ring
  have hd' (t : ℝ) (ht : t ∈ Icc 0 c) :
      HasDerivAt (fun z : ℝ => 1/(1-z)-z) (1/(1-t)^2-1) t := by
    have hn : 1-t ≠ 0 := by linarith [ht.2]
    convert ((hasDerivAt_const t 1).div ((hasDerivAt_id t).const_sub 1) hn).sub
      (hasDerivAt_id t) using 1
    simp only [id_eq]
    ring
  have hn (t : ℝ) (ht : t ∈ Icc 0 c) : 0 ≤ 1/(1-t)^2-1 := by
    have hp : 0 < 1-t := by linarith [ht.2]
    have hle : (1-t)^2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have h : (1:ℝ) ≤ 1/(1-t)^2 := (le_div_iff₀ (sq_pos_of_pos hp)).mpr (by linarith)
    linarith
  have hm := monotone_on_interval hd' hn
  have h := tangent_lower hd hm ⟨hR, le_max_right x R⟩ ⟨hx, le_max_left x R⟩
  have he : (1/(1-R)-R)*(x-R) = (x-R)/(1-R)-R*(x-R) := by ring
  rw [he] at h
  nlinarith only [h]

theorem weighted_strong_jensen {ι : Type*} (T : Finset ι) (w x : ι → ℝ) (R : ℝ)
    (hw : ∀ i ∈ T, 0 ≤ w i) (hsum : ∑ i ∈ T, w i = 1)
    (hmean : ∑ i ∈ T, w i*x i = R)
    (hx : ∀ i ∈ T, 0 ≤ x i ∧ x i < 1) (hR : 0 ≤ R) (hR1 : R < 1) :
    phi R+(∑ i ∈ T, w i*(x i-R)^2)/2 ≤ ∑ i ∈ T, w i*phi (x i) := by
  have h := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
    (phi_strong_tangent (hx i hi).1 (hx i hi).2 hR hR1) (hw i hi))
  have he : (∑ i ∈ T, w i*(phi R+(x i-R)/(1-R)+(x i-R)^2/2)) =
      phi R+(∑ i ∈ T, w i*(x i-R)^2)/2 := by
    have sum_div (f : ι → ℝ) (d : ℝ) : (∑ i ∈ T, f i/d) = (∑ i ∈ T, f i)/d := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    simp_rw [mul_add, Finset.sum_add_distrib, ← mul_div_assoc, sum_div,
      mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, hmean]
    ring
  rw [he] at h
  exact h

theorem weighted_square {ι : Type*} (T : Finset ι) (w x : ι → ℝ) (a : ℝ)
    (hw : ∀ i ∈ T, 0 ≤ w i) :
    2*a*(∑ i ∈ T, w i*x i)-a^2*(∑ i ∈ T, w i) ≤ ∑ i ∈ T, w i*(x i)^2 := by
  have h : 0 ≤ ∑ i ∈ T, w i*(x i-a)^2 :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  have he : (∑ i ∈ T, w i*(x i-a)^2) =
      (∑ i ∈ T, w i*(x i)^2)-2*a*(∑ i ∈ T, w i*x i)+a^2*(∑ i ∈ T, w i) := by
    simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at h
  linarith

theorem grouped_variance {ι : Type*} (T H : Finset ι) (w x : ι → ℝ) (h δ : ℝ)
    (hHT : H ⊆ T) (hw : ∀ i ∈ T, 0 ≤ w i)
    (hsum : ∑ i ∈ T, w i = 1) (hgroup : ∑ i ∈ H, w i = h)
    (hmean : ∑ i ∈ T, w i*x i = 0) (hh : h < 1) (hδ : 0 ≤ δ)
    (hxH : ∀ i ∈ H, δ ≤ x i) :
    h/(1-h)*δ^2 ≤ ∑ i ∈ T, w i*(x i)^2 := by
  classical
  have hh0 : 0 ≤ h := hgroup ▸ Finset.sum_nonneg (fun i hi => hw i (hHT hi))
  have ha : 0 < 1-h := by linarith
  let t := h*δ/(1-h)
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hT : ∑ i ∈ T \ H, w i = 1-h := by
    have he := Finset.sum_sdiff hHT (f := w)
    rw [hsum, hgroup] at he
    linarith
  have hxT : (∑ i ∈ T \ H, w i*x i) = -(∑ i ∈ H, w i*x i) := by
    have he := Finset.sum_sdiff hHT (f := fun i => w i*x i)
    rw [hmean] at he
    linarith
  have hV := Finset.sum_sdiff hHT (f := fun i => w i*(x i)^2)
  have hH := weighted_square H w x δ (fun i hi => hw i (hHT hi))
  have hC := weighted_square (T \ H) w x (-t) (fun i hi => hw i (Finset.mem_sdiff.mp hi).1)
  rw [hgroup] at hH
  rw [hT, hxT] at hC
  have hv : h*δ ≤ ∑ i ∈ H, w i*x i := by
    rw [← hgroup, Finset.sum_mul]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hxH i hi) (hw i (hHT hi)))
  have hvm := mul_le_mul_of_nonneg_left hv (show 0 ≤ 2*(δ+t) by positivity)
  have he : 2*(δ+t)*(h*δ)-δ^2*h-t^2*(1-h) = h/(1-h)*δ^2 := by
    dsimp [t]
    field_simp
    ring
  nlinarith only [hV, hH, hC, hvm, he]

/-- The finite weighted entropy compensation in (9.1), including empty H. -/
theorem weighted_entropy_compensation {ι : Type*} (T H : Finset ι) (w x : ι → ℝ)
    {R h D : ℝ} (hHT : H ⊆ T) (hw : ∀ i ∈ T, 0 ≤ w i)
    (hsum : ∑ i ∈ T, w i = 1) (hgroup : ∑ i ∈ H, w i = h)
    (hmean : ∑ i ∈ T, w i*x i = R) (hh : h < 1)
    (hx : ∀ i ∈ T, 0 ≤ x i ∧ x i < 1) (hR : 0 ≤ R) (hR1 : R < 1)
    (hD : R ≤ D) (hxH : ∀ i ∈ H, D ≤ x i) :
    phi R+h/(2*(1-h))*(D-R)^2 ≤ ∑ i ∈ T, w i*phi (x i) := by
  have hmean' : (∑ i ∈ T, w i*(x i-R)) = 0 := by
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmean, hsum]
    ring
  have hvar := grouped_variance T H w (fun i => x i-R) h (D-R)
    hHT hw hsum hgroup hmean' hh (sub_nonneg.mpr hD)
    (fun i hi => sub_le_sub_right (hxH i hi) R)
  have hj := weighted_strong_jensen T w x R hw hsum hmean hx hR hR1
  have he : h/(2*(1-h))*(D-R)^2 = (h/(1-h)*(D-R)^2)/2 := by
    have hn : 1-h ≠ 0 := by linarith
    field_simp [hn]
    <;> ring
    <;> simp
  rw [he]
  linarith

end
end S2R.Analysis
