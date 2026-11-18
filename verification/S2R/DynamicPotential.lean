import S2R.Certificate

namespace S2R.Analysis
noncomputable section
open Set

structure MassProfile (ι : Type*) where
  items : Finset ι
  cost : ι → ℝ
  mass : ι → ℝ
  nonempty : items.Nonempty
  cost_pos : ∀ i ∈ items, 0 < cost i
  mass_pos : ∀ i ∈ items, 0 < mass i

namespace MassProfile
variable {ι : Type*} (P : MassProfile ι)

def total : ℝ := ∑ i ∈ P.items, P.mass i
def capped (ρ : ℝ) (i : ι) : ℝ := min (P.mass i) (ρ*P.cost i)
def massAt (ρ : ℝ) : ℝ := ∑ i ∈ P.items, P.capped ρ i
def base : ℝ := P.massAt b

theorem total_pos : 0 < P.total := Finset.sum_pos P.mass_pos P.nonempty
theorem massAt_mono : Monotone P.massAt := by
  intro x y hxy
  exact Finset.sum_le_sum (fun i hi => min_le_min le_rfl
    (mul_le_mul_of_nonneg_right hxy (P.cost_pos i hi).le))
theorem massAt_le_total (ρ : ℝ) : P.massAt ρ ≤ P.total :=
  Finset.sum_le_sum (fun i _ => min_le_left _ _)
theorem base_pos : 0 < P.base := by
  apply Finset.sum_pos _ P.nonempty
  intro i hi
  exact lt_min (P.mass_pos i hi) (mul_pos b_pos (P.cost_pos i hi))
theorem base_le_total : P.base ≤ P.total := P.massAt_le_total b

theorem cap_order {x y : ℝ} (hsum : P.massAt x ≤ P.massAt y) :
    ∀ i ∈ P.items, P.capped x i ≤ P.capped y i := by
  intro i hi
  by_cases hxy : x ≤ y
  · exact min_le_min le_rfl (mul_le_mul_of_nonneg_right hxy (P.cost_pos i hi).le)
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hle (j : ι) (hj : j ∈ P.items) : P.capped y j ≤ P.capped x j :=
      min_le_min le_rfl (mul_le_mul_of_nonneg_right hyx (P.cost_pos j hj).le)
    by_contra hnot
    have hstrict := Finset.sum_lt_sum hle ⟨i, hi, lt_of_not_ge hnot⟩
    exact (not_lt_of_ge hsum) hstrict

theorem level_exists {R : ℝ} (hR : 0 < R) (hRT : R ≤ P.total) :
    ∃ κ : ℝ, 0 < κ ∧ P.massAt κ = R := by
  obtain ⟨j, hj, hmax⟩ := P.items.exists_max_image (fun i => P.mass i/P.cost i) P.nonempty
  let top := P.mass j/P.cost j
  have htop : 0 < top := div_pos (P.mass_pos j hj) (P.cost_pos j hj)
  have hcont : Continuous P.massAt := continuous_finset_sum P.items
    (fun i _ => continuous_const.min (continuous_id.mul continuous_const))
  have hz : P.massAt 0 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [capped, min_eq_right (P.mass_pos i hi).le]
  have ht : P.massAt top = P.total := by
    apply Finset.sum_congr rfl
    intro i hi
    exact min_eq_left ((div_le_iff₀ (P.cost_pos i hi)).mp (hmax i hi))
  obtain ⟨κ, hκ, he⟩ := intermediate_value_Icc htop.le hcont.continuousOn
    (show R ∈ Icc (P.massAt 0) (P.massAt top) by rw [hz, ht]; exact ⟨hR.le, hRT⟩)
  have hn : κ ≠ 0 := by intro h; subst κ; rw [hz] at he; linarith
  exact ⟨κ, lt_of_le_of_ne hκ.1 hn.symm, he⟩

def target (R : ℝ) : ℝ := min P.total (max R P.base)
theorem target_pos (R : ℝ) : 0 < P.target R :=
  lt_min P.total_pos (P.base_pos.trans_le (le_max_right _ _))
def level (R : ℝ) : ℝ := Classical.choose
  (P.level_exists (P.target_pos R) (min_le_left _ _))
theorem level_spec (R : ℝ) : 0 < P.level R ∧ P.massAt (P.level R) = P.target R :=
  Classical.choose_spec (P.level_exists (P.target_pos R) (min_le_left _ _))
def weights (R : ℝ) : ι → ℝ := P.capped (P.level R)

theorem weight_pos (R : ℝ) {i : ι} (hi : i ∈ P.items) : 0 < P.weights R i :=
  lt_min (P.mass_pos i hi) (mul_pos (P.level_spec R).1 (P.cost_pos i hi))
theorem weights_sum (R : ℝ) : (∑ i ∈ P.items, P.weights R i) = P.target R :=
  (P.level_spec R).2
theorem target_eq {R : ℝ} (hR : R ≤ P.total) : P.target R = max R P.base :=
  min_eq_right (max_le hR P.base_le_total)
theorem weights_mono {R S : ℝ} (h : R ≤ S) :
    ∀ i ∈ P.items, P.weights R i ≤ P.weights S i := by
  apply P.cap_order
  rw [(P.level_spec R).2, (P.level_spec S).2]
  exact min_le_min le_rfl (max_le_max h le_rfl)
theorem base_le_weights (R : ℝ) : ∀ i ∈ P.items, P.capped b i ≤ P.weights R i := by
  apply P.cap_order
  rw [(P.level_spec R).2]
  exact le_min P.base_le_total (le_max_right _ _)
theorem weights_eq_base {R : ℝ} (hR : R ≤ P.base) :
    ∀ i ∈ P.items, P.weights R i = P.capped b i := by
  intro i hi
  apply le_antisymm _ (P.base_le_weights R i hi)
  apply P.cap_order _ i hi
  rw [(P.level_spec R).2, target, max_eq_right hR, min_eq_right P.base_le_total]
  exact le_rfl
theorem weights_eq_mass : ∀ i ∈ P.items, P.weights P.total i = P.mass i := by
  intro i hi
  have hle (j : ι) (_ : j ∈ P.items) : P.weights P.total j ≤ P.mass j := min_le_left _ _
  apply le_antisymm (hle i hi)
  by_contra hnot
  have hs := Finset.sum_lt_sum hle ⟨i, hi, lt_of_not_ge hnot⟩
  rw [P.weights_sum, target, max_eq_left P.base_le_total, min_self] at hs
  exact (lt_irrefl _) hs
theorem weights_le_density {R ρ : ℝ} (hR : R ≤ P.massAt ρ) (hρ : b ≤ ρ) :
    ∀ i ∈ P.items, P.weights R i ≤ ρ*P.cost i := by
  intro i hi
  apply (P.cap_order _ i hi).trans (min_le_right _ _)
  rw [(P.level_spec R).2]
  exact (min_le_right _ _).trans (max_le hR (P.massAt_mono hρ))

def logTime (R : ℝ) : ℝ :=
  ∑ i ∈ P.items, P.cost i*(Real.log (P.mass i)-Real.log (P.weights R i))
def baseTime : ℝ :=
  ∑ i ∈ P.items, P.cost i*(Real.log (P.mass i)-Real.log (P.capped b i))
def potential (R : ℝ) : ℝ := P.logTime R+(P.target R-R)/b

theorem potential_initial : P.potential P.total = 0 := by
  have hz : P.logTime P.total = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [P.weights_eq_mass i hi, sub_self, mul_zero]
  simp [potential, hz, target, max_eq_left P.base_le_total]
theorem logTime_le_base (R : ℝ) : P.logTime R ≤ P.baseTime := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (P.cost_pos i hi).le
  apply sub_le_sub_left
  exact Real.log_le_log (lt_min (P.mass_pos i hi) (mul_pos b_pos (P.cost_pos i hi)))
    (P.base_le_weights R i hi)

theorem log_segment {x y ρ c : ℝ} (hy : 0 < y) (hyx : y ≤ x)
    (hρ : 0 < ρ) (hxc : x ≤ ρ*c) : x-y ≤ ρ*c*(Real.log x-Real.log y) := by
  have hx := hy.trans_le hyx
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have hlog : 0 ≤ Real.log x-Real.log y := sub_nonneg.mpr (Real.log_le_log hy hyx)
  have hmul := mul_le_mul_of_nonneg_left h hx.le
  have hdiv : x*(y/x)=y := by field_simp
  have hb := mul_le_mul_of_nonneg_right hxc hlog
  nlinarith only [hmul, hdiv, hb]

theorem potential_step {R S ρ : ℝ} (hSR : S ≤ R) (hRT : R ≤ P.total)
    (hρ : b ≤ ρ) (hR : R ≤ P.massAt ρ) :
    R-S ≤ ρ*(P.potential S-P.potential R) := by
  have hρp := b_pos.trans_le hρ
  have hs := Finset.sum_le_sum (fun i hi => log_segment
    (P.weight_pos S hi) (P.weights_mono hSR i hi) hρp (P.weights_le_density hR hρ i hi))
  have he1 : (∑ i ∈ P.items, (P.weights R i-P.weights S i)) = P.target R-P.target S := by
    rw [Finset.sum_sub_distrib, P.weights_sum, P.weights_sum]
  have he2 : (∑ i ∈ P.items, ρ*P.cost i*(Real.log (P.weights R i)-Real.log (P.weights S i))) =
      ρ*(P.logTime S-P.logTime R) := by
    unfold logTime
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he1, he2] at hs
  have hST := hSR.trans hRT
  have hd : 0 ≤ (P.target S-S)-(P.target R-R) := by
    rw [P.target_eq hST, P.target_eq hRT]
    by_cases hr : P.base ≤ R
    · rw [max_eq_left hr]
      linarith [le_max_left S P.base]
    · have hrs : R ≤ P.base := le_of_not_ge hr
      rw [max_eq_right hrs, max_eq_right (hSR.trans hrs)]
      linarith
  have hm := mul_le_mul_of_nonneg_right hρ hd
  have hdiv : b*((P.target S-S)/b-(P.target R-R)/b) = (P.target S-S)-(P.target R-R) := by
    field_simp [b_pos.ne']
  have hm' : (P.target S-S)-(P.target R-R) ≤
      ρ*((P.target S-S)/b-(P.target R-R)/b) := by
    apply (mul_le_mul_left b_pos).mp
    have he := congrArg (fun t : ℝ => ρ*t) hdiv
    nlinarith only [hm, he]
  unfold potential
  nlinarith only [hs, hm']

theorem cap_log_identity {v c : ℝ} (hv : 0 < v) (hc : 0 < c) :
    Real.log v-Real.log (min v (b*c)) = max (Real.log (v/(b*c))) 0 := by
  have hbc := mul_pos b_pos hc
  by_cases h : v ≤ b*c
  · rw [min_eq_left h, sub_self]
    have hr : v/(b*c) ≤ 1 := (div_le_iff₀ hbc).mpr (by simpa using h)
    rw [max_eq_right (Real.log_nonpos (div_nonneg hv.le hbc.le) hr)]
  · have h' : b*c ≤ v := le_of_not_ge h
    rw [min_eq_right h']
    have hr : 1 ≤ v/(b*c) := (le_div_iff₀ hbc).mpr (by simpa using h')
    rw [max_eq_left (Real.log_nonneg hr), Real.log_div hv.ne' hbc.ne']

theorem baseTime_le_total : P.baseTime ≤ P.total := by
  apply Finset.sum_le_sum
  intro i hi
  rw [capped, cap_log_identity (P.mass_pos i hi) (P.cost_pos i hi)]
  have h := mul_le_mul_of_nonneg_left
    (log_plus_bound (div_pos (P.mass_pos i hi) (mul_pos b_pos (P.cost_pos i hi))))
    (P.cost_pos i hi).le
  have he : P.cost i*(P.mass i/(b*P.cost i)/Real.exp 1) = P.mass i := by
    unfold b
    rw [Real.exp_neg]
    field_simp [(P.cost_pos i hi).ne', (Real.exp_pos 1).ne']
    ring
  rwa [he] at h

theorem capCost_sum : (∑ i ∈ P.items, capCost (P.mass i) (P.cost i)) = P.base+b*P.baseTime := by
  unfold base massAt baseTime
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [capped, cap_log_identity (P.mass_pos i hi) (P.cost_pos i hi)]
  unfold capCost
  ring

theorem end_residual_bound {R : ℝ} (hW : P.total < 1) (hR : R ≤ P.total)
    (hP : 1 ≤ P.potential R) :
    R+b ≤ ∑ i ∈ P.items, capCost (P.mass i) (P.cost i) := by
  have hbase : R ≤ P.base := by
    by_contra hn
    have hbr : P.base ≤ R := (lt_of_not_ge hn).le
    have hp : P.potential R = P.logTime R := by
      rw [potential, P.target_eq hR, max_eq_left hbr]
      simp
    rw [hp] at hP
    linarith [P.logTime_le_base R, P.baseTime_le_total]
  have ht : P.logTime R = P.baseTime := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [P.weights_eq_base hbase i hi]
  rw [potential, P.target_eq hR, max_eq_right hbase, ht] at hP
  have hm := mul_le_mul_of_nonneg_left hP b_pos.le
  have hd : b*((P.base-R)/b)=P.base-R := by field_simp [b_pos.ne']
  rw [P.capCost_sum]
  nlinarith only [hm, hd]

/-- A finite trajectory, with arbitrary segment lengths (including a clipped
last segment), satisfies the dynamic cap-cost bound. All local rate premises
will be obtained from the real greedy choices in `DynamicCertificate`. -/
theorem finite_dynamic_bound (R ρ δ : ℕ → ℝ) (m : ℕ)
    (hW : P.total < 1) (hinit : R 0 = P.total)
    (hR : ∀ k ≤ m, R k ≤ P.total)
    (hδ : ∀ k < m, 0 ≤ δ k) (hρ : ∀ k < m, 0 < δ k → b ≤ ρ k)
    (hcap : ∀ k < m, 0 < δ k → R k ≤ P.massAt (ρ k))
    (hstep : ∀ k < m, R (k+1) = R k-ρ k*δ k)
    (htime : ∑ k ∈ Finset.range m, δ k = 1) :
    R m+b ≤ ∑ i ∈ P.items, capCost (P.mass i) (P.cost i) := by
  have hind (k : ℕ) (hk : k ≤ m) : (∑ j ∈ Finset.range k, δ j) ≤ P.potential (R k) := by
    induction k with
    | zero => simp [hinit, P.potential_initial]
    | succ k ih =>
      have hkm : k < m := by omega
      have hp := ih (by omega)
      by_cases hz : δ k = 0
      · simpa [Finset.sum_range_succ, hstep k hkm, hz] using hp
      have hδp : 0 < δ k := lt_of_le_of_ne (hδ k hkm) (Ne.symm hz)
      have hρp := b_pos.trans_le (hρ k hkm hδp)
      have hle : R (k+1) ≤ R k := by rw [hstep k hkm]; nlinarith [hδ k hkm]
      have hb := P.potential_step hle (hR k (by omega)) (hρ k hkm hδp) (hcap k hkm hδp)
      rw [hstep k hkm] at hb
      have hd : δ k ≤ P.potential (R (k+1))-P.potential (R k) := by
        apply (mul_le_mul_left hρp).mp
        rw [hstep k hkm]
        nlinarith only [hb]
      rw [Finset.sum_range_succ]
      linarith
  exact P.end_residual_bound hW (hR m le_rfl) (by simpa [htime] using hind m le_rfl)

end MassProfile
end
end S2R.Analysis
