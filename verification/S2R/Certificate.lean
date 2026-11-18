import S2R.Analysis

namespace S2R.Analysis
noncomputable section
open Set

def cappedMass {ι : Type*} (T : Finset ι) (c : ι → ℝ) (p ρ : ℝ) : ℝ :=
  ∑ i ∈ T, min p (ρ*c i)

theorem cappedMass_mono {ι : Type*} (T : Finset ι) (c : ι → ℝ) (p : ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) : Monotone (cappedMass T c p) := by
  intro x y hxy
  exact Finset.sum_le_sum (fun i hi => min_le_min le_rfl (mul_le_mul_of_nonneg_right hxy (hc i hi)))

theorem reference_mass_exists {ι : Type*} (T : Finset ι) (c : ι → ℝ) {p W : ℝ}
    (hT : T.Nonempty) (hc : ∀ i ∈ T, 0 < c i) (hp : 0 < p)
    (hW : 0 < W) (hWp : W ≤ T.card*p) :
    ∃ κ : ℝ, 0 < κ ∧ cappedMass T c p κ = W := by
  obtain ⟨j, hj, hmax⟩ := T.exists_max_image (fun i => p/c i) hT
  let top := p/c j
  have htop : 0 < top := div_pos hp (hc j hj)
  have hcont : Continuous (cappedMass T c p) :=
    continuous_finset_sum T (fun i _ => continuous_const.min (continuous_id.mul continuous_const))
  have hzero : cappedMass T c p 0 = 0 := by simp [cappedMass, min_eq_right hp.le]
  have hcap : cappedMass T c p top = T.card*p := by
    unfold cappedMass
    have he : (∑ i ∈ T, min p (top*c i)) = ∑ _i ∈ T, p := by
      apply Finset.sum_congr rfl
      intro i hi
      exact min_eq_left ((div_le_iff₀ (hc i hi)).mp (hmax i hi))
    rw [he]
    simp
  obtain ⟨κ, hκ, he⟩ := intermediate_value_Icc htop.le hcont.continuousOn
    (show W ∈ Icc (cappedMass T c p 0) (cappedMass T c p top) by
      rw [hzero, hcap]; exact ⟨hW.le, hWp⟩)
  refine ⟨κ, ?_, he⟩
  have hn : κ ≠ 0 := by intro h; subst κ; rw [hzero] at he; linarith
  exact lt_of_le_of_ne hκ.1 hn.symm

theorem capped_reference_identity {ι : Type*} (T : Finset ι) (c : ι → ℝ)
    (p κ ρ : ℝ) (hc : ∀ i ∈ T, 0 ≤ c i) :
    (∑ i ∈ T, min (min p (κ*c i)) (ρ*c i)) =
      min (cappedMass T c p κ) (cappedMass T c p ρ) := by
  by_cases h : ρ ≤ κ
  · rw [min_eq_right (cappedMass_mono T c p hc h)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [min_assoc, min_eq_right (mul_le_mul_of_nonneg_right h (hc i hi))]
  · have h' : κ ≤ ρ := le_of_not_ge h
    rw [min_eq_left (cappedMass_mono T c p hc h')]
    apply Finset.sum_congr rfl
    intro i hi
    exact min_eq_left ((min_le_right p _).trans (mul_le_mul_of_nonneg_right h' (hc i hi)))

def capCost (v c : ℝ) : ℝ := min v (b*c)+b*c*max (Real.log (v/(b*c))) 0

theorem capCost_dual {v c τ : ℝ} (hv : 0 < v) (hc : 0 < c)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) : capCost v c ≤ τ*v-b*c*Real.log τ := by
  have hbc : 0 < b*c := mul_pos b_pos hc
  have h := mul_le_mul_of_nonneg_left (cap_log_dual (div_pos hv hbc) hτ hτ1) hbc.le
  have hmin : b*c*min (v/(b*c)) 1 = min v (b*c) := by
    rw [mul_min_of_nonneg _ _ hbc.le, mul_div_cancel₀ _ hbc.ne', mul_one]
  rw [mul_add, hmin] at h
  have he : b*c*(τ*(v/(b*c))-Real.log τ) = τ*v-b*c*Real.log τ := by
    field_simp
  rw [he] at h
  exact h

/-- Algebraic dualization in section 3. The dynamical bound `hG` remains an
explicit premise; this theorem alone is not the unified density certificate. -/
theorem certificate_dualization {ι : Type*} (T : Finset ι) (c v τ : ι → ℝ)
    {G p β : ℝ} (hc : ∀ i ∈ T, 0 < c i) (hv : ∀ i ∈ T, 0 < v i ∧ v i ≤ p)
    (hβ : 0 < β) (hτ : ∀ i ∈ T, β ≤ τ i ∧ τ i ≤ 1)
    (hsum : ∑ i ∈ T, v i = 1-p)
    (hG : 1+b-(∑ i ∈ T, capCost (v i) (c i)) ≤ G) :
    1+b-β+p*(β-∑ i ∈ T, (τ i-β))+b*(∑ i ∈ T, c i*Real.log (τ i)) ≤ G := by
  have hdual := Finset.sum_le_sum (fun i hi => capCost_dual (hv i hi).1 (hc i hi)
    (hβ.trans_le (hτ i hi).1) (hτ i hi).2)
  have hweight := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hv i hi).2
    (sub_nonneg.mpr (hτ i hi).1))
  have he : (∑ i ∈ T, (τ i*v i-b*c i*Real.log (τ i))) =
      β*(1-p)+(∑ i ∈ T, (τ i-β)*v i)-b*(∑ i ∈ T, c i*Real.log (τ i)) := by
    rw [← hsum]
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he] at hdual
  rw [← Finset.sum_mul] at hweight
  nlinarith only [hdual, hweight, hG]

/-- A single affine greedy segment obeys the exponential comparison even
when the target gap is negative. No sign assumption on `theta-g` is used. -/
theorem affine_exponential_comparison {A theta g ρ δ : ℝ}
    (hA : 0 < A) (hρ : 0 ≤ ρ) (hδ : 0 ≤ δ) (hgap : theta-g ≤ A*ρ) :
    Real.exp (δ/A)*(theta-(g+ρ*δ)) ≤ theta-g := by
  have hd (x : ℝ) (hx : x ∈ Icc 0 δ) :
      HasDerivAt (fun z => theta-g-Real.exp (z/A)*(theta-g-ρ*z))
        (Real.exp (x/A)/A*(A*ρ-(theta-g)+ρ*x)) x := by
    convert ((((hasDerivAt_id x).div_const A).exp).mul
      (((hasDerivAt_id x).const_mul ρ).const_sub (theta-g))).const_sub (theta-g) using 1
    simp only [id_eq]
    field_simp
    ring
  have hn (x : ℝ) (hx : x ∈ Icc 0 δ) :
      0 ≤ Real.exp (x/A)/A*(A*ρ-(theta-g)+ρ*x) := by
    have hh : 0 ≤ A*ρ-(theta-g)+ρ*x := by nlinarith [hx.1]
    positivity
  have h := nonneg_of_derivative hδ hd hn (by simp)
  nlinarith only [h]

/-- The last algebraic step of the frozen comparison lemma. -/
theorem frozen_algebra {M B0 ρ K J lam r0 : ℝ}
    (hJ : 0 ≤ J) (hlam : 0 ≤ lam) (hrho : b/(1+lam) ≤ ρ)
    (hKJ : K*J ≤ lam) (hr : r0 ≤ (lam+(1+lam-K)*J)/(1+lam))
    (hB : B0 = alpha-b*r0)
    (hM : B0+ρ*(lam-K*J)+J ≤ (1+J)*M) : alpha ≤ M := by
  have hy : 0 < 1+lam := by linarith
  have hm := mul_le_mul_of_nonneg_right hrho (sub_nonneg.mpr hKJ)
  have hr' := (le_div_iff₀ hy).mp hr
  have hbr := mul_le_mul_of_nonneg_left hr' b_pos.le
  have he : b/(1+lam)*(lam-K*J)+J-b*r0-(J*alpha) =
      b/(1+lam)*(lam+(1+lam-K)*J-r0*(1+lam)) := by
    unfold alpha
    field_simp
    ring
  have hn : 0 ≤ b/(1+lam)*(lam+(1+lam-K)*J-r0*(1+lam)) := by
    apply mul_nonneg (div_nonneg b_pos.le hy.le)
    linarith
  rw [hB] at hM
  have hmul : (1+J)*alpha ≤ (1+J)*M := by nlinarith only [hM, hm, he, hn]
  exact (mul_le_mul_left (show 0 < 1+J by linarith)).mp hmul

theorem finite_exponential_comparison (F ρ δ : ℕ → ℝ) (m : ℕ) {A theta : ℝ}
    (hA : 0 < A) (hδ : ∀ k < m, 0 ≤ δ k) (hρ : ∀ k < m, 0 ≤ ρ k)
    (hstep : ∀ k < m, F (k+1)=F k+ρ k*δ k)
    (hrate : ∀ k < m, 0 < δ k → theta-F k ≤ A*ρ k) :
    Real.exp ((∑ k ∈ Finset.range m, δ k)/A)*(theta-F m) ≤ theta-F 0 := by
  have hind (k : ℕ) (hk : k ≤ m) :
      Real.exp ((∑ j ∈ Finset.range k, δ j)/A)*(theta-F k) ≤ theta-F 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hkm : k < m := by omega
      have hp := ih (by omega)
      have hs : Real.exp (δ k/A)*(theta-F (k+1)) ≤ theta-F k := by
        rw [hstep k hkm]
        by_cases hz : δ k=0
        · simp [hz]
        · exact affine_exponential_comparison hA (hρ k hkm) (hδ k hkm)
            (hrate k hkm (lt_of_le_of_ne (hδ k hkm) (Ne.symm hz)))
      have hm := mul_le_mul_of_nonneg_left hs (Real.exp_pos ((∑ j ∈ Finset.range k, δ j)/A)).le
      rw [Finset.sum_range_succ, add_div, Real.exp_add]
      nlinarith only [hm, hp]
  exact hind m le_rfl

end
end S2R.Analysis
