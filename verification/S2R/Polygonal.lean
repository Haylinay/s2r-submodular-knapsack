import S2R.GreedyCurve

namespace S2R.Instance
noncomputable section
variable {n : ℕ} (I : Instance n)

def durationAt (a : Ground n) (x : ℝ) (k : ℕ) : ℝ :=
  min (I.pathCost a (k+1)) x-min (I.pathCost a k) x
def valueAt (a : Ground n) (x : ℝ) : ℝ := I.value {a}+
  ∑ k ∈ Finset.range n, I.pathDensity a k*I.durationAt a x k
def intervalDuration (a : Ground n) (lo hi : ℝ) (k : ℕ) : ℝ :=
  I.durationAt a hi k-I.durationAt a lo k
def partialValueAt (a : Ground n) (x : ℝ) (m : ℕ) : ℝ := I.value {a}+
  ∑ k ∈ Finset.range m, I.pathDensity a k*I.durationAt a x k

theorem min_increment_nonneg {A B lo hi : ℝ} (hAB : A ≤ B) (hlh : lo ≤ hi) :
    0 ≤ (min B hi-min A hi)-(min B lo-min A lo) := by
  simp only [min_def]
  split_ifs <;> linarith
theorem min_increment_le {A B lo hi : ℝ} (hAB : A ≤ B) (hlh : lo ≤ hi) :
    (min B hi-min A hi)-(min B lo-min A lo) ≤ hi-lo := by
  simp only [min_def]
  split_ifs <;> linarith
theorem durationAt_nonneg (a : Ground n) (x : ℝ) (k : ℕ) : 0 ≤ I.durationAt a x k :=
  sub_nonneg.mpr (min_le_min (I.pathCost_mono a (Nat.le_succ k)) le_rfl)
theorem durationAt_le (a : Ground n) (x : ℝ) (k : ℕ) :
    I.durationAt a x k ≤ I.pathCost a (k+1)-I.pathCost a k := by
  have h := I.pathCost_mono a (Nat.le_succ k)
  unfold durationAt
  simp only [min_def]
  split_ifs <;> linarith
theorem intervalDuration_nonneg (a : Ground n) {lo hi : ℝ} (h : lo ≤ hi) (k : ℕ) :
    0 ≤ I.intervalDuration a lo hi k :=
  min_increment_nonneg (I.pathCost_mono a (Nat.le_succ k)) h
theorem intervalDuration_pos_left {a : Ground n} {lo hi : ℝ} {k : ℕ}
    (hlh : lo ≤ hi) (h : 0 < I.intervalDuration a lo hi k) : I.pathCost a k < hi := by
  by_contra hn
  have hhi := le_of_not_gt hn
  have hlo := hlh.trans hhi
  have hnext := I.pathCost_mono a (Nat.le_succ k)
  simp [intervalDuration, durationAt, min_eq_right hhi, min_eq_right hlo,
    min_eq_right (hhi.trans hnext), min_eq_right (hlo.trans hnext)] at h
theorem intervalDuration_pos_right {a : Ground n} {lo hi : ℝ} {k : ℕ}
    (hlh : lo ≤ hi) (h : 0 < I.intervalDuration a lo hi k) : lo < I.pathCost a (k+1) := by
  by_contra hn
  have hlo := le_of_not_gt hn
  have hhi := hlo.trans hlh
  have hprev := I.pathCost_mono a (Nat.le_succ k)
  simp [intervalDuration, durationAt, min_eq_left hhi, min_eq_left hlo,
    min_eq_left (hprev.trans hhi), min_eq_left (hprev.trans hlo)] at h

theorem durationAt_sum (a : Ground n) {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    (∑ k ∈ Finset.range m, I.durationAt a x k) = min (I.pathCost a m) x := by
  induction m with
  | zero => simp [min_eq_left hx]
  | succ m ih => rw [Finset.sum_range_succ, ih]; unfold durationAt; ring
theorem intervalDuration_sum (a : Ground n) {lo hi : ℝ} (hl : 0 ≤ lo) (hlh : lo ≤ hi)
    (hcover : hi ≤ I.pathCost a n) : (∑ k ∈ Finset.range n, I.intervalDuration a lo hi k) = hi-lo := by
  simp only [intervalDuration, Finset.sum_sub_distrib]
  rw [I.durationAt_sum a (hl.trans hlh), I.durationAt_sum a hl,
    min_eq_right hcover, min_eq_right (hlh.trans hcover)]
theorem valueAt_difference (a : Ground n) (lo hi : ℝ) :
    I.valueAt a hi-I.valueAt a lo =
      ∑ k ∈ Finset.range n, I.pathDensity a k*I.intervalDuration a lo hi k := by
  simp only [valueAt, intervalDuration, mul_sub, Finset.sum_sub_distrib]
  ring
theorem valueAt_mono (a : Ground n) : Monotone (I.valueAt a) := by
  intro lo hi h
  have he := I.valueAt_difference a lo hi
  have hn : 0 ≤ ∑ k ∈ Finset.range n, I.pathDensity a k*I.intervalDuration a lo hi k :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (I.greedyDensity_nonneg _) (I.intervalDuration_nonneg a h k))
  linarith
theorem valueAt_one (a : Ground n) : I.valueAt a 1 = I.curveValue a n := rfl
theorem full_gain_sum (a : Ground n) (m : ℕ) :
    (∑ k ∈ Finset.range m, I.pathDensity a k*(I.pathCost a (k+1)-I.pathCost a k)) =
      I.value (I.iterate {a} m)-I.value {a} := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, ← I.path_gain]; ring
theorem valueAt_le_output {a : Ground n} (ha : I.Feasible {a}) (x : ℝ) : I.valueAt a x ≤ I.output := by
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range n) => mul_le_mul_of_nonneg_left
    (I.durationAt_le a x k) (I.greedyDensity_nonneg (I.iterate {a} k)))
  change (∑ k ∈ Finset.range n, I.pathDensity a k*I.durationAt a x k) ≤
    ∑ k ∈ Finset.range n, I.pathDensity a k*(I.pathCost a (k+1)-I.pathCost a k) at hsum
  rw [I.full_gain_sum] at hsum
  have hterminal := I.prefix_le_output ha (Fin.last n)
  change I.value (I.iterate {a} n) ≤ I.output at hterminal
  unfold valueAt
  linarith
theorem valueAt_zero (a : Ground n) : I.valueAt a 0 = I.value {a} := by
  have hd (k : ℕ) : I.durationAt a 0 k = 0 := by
    simp [durationAt, min_eq_right (I.pathCost_nonneg a k), min_eq_right (I.pathCost_nonneg a (k+1))]
  simp [valueAt, hd]

theorem density_integral_lower {a : Ground n} {lo hi c : ℝ}
    (hl : 0 ≤ lo) (hlh : lo ≤ hi) (hcover : hi ≤ I.pathCost a n)
    (hρ : ∀ k < n, 0 < I.intervalDuration a lo hi k → c ≤ I.pathDensity a k) :
    c*(hi-lo) ≤ I.valueAt a hi-I.valueAt a lo := by
  rw [I.valueAt_difference, ← I.intervalDuration_sum a hl hlh hcover, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hd := I.intervalDuration_nonneg a hlh k
  by_cases hz : I.intervalDuration a lo hi k = 0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hρ k (Finset.mem_range.mp hk) (lt_of_le_of_ne hd (Ne.symm hz))) hd

theorem partialValueAt_succ (a : Ground n) (x : ℝ) (m : ℕ) :
    I.partialValueAt a x (m+1)=I.partialValueAt a x m+I.pathDensity a m*I.durationAt a x m := by
  simp [partialValueAt, Finset.sum_range_succ, add_assoc]
theorem partialValueAt_mono (a : Ground n) (x : ℝ) : Monotone (I.partialValueAt a x) := by
  apply monotone_nat_of_le_succ
  intro m
  rw [I.partialValueAt_succ]
  exact le_add_of_nonneg_right (mul_nonneg (I.greedyDensity_nonneg _) (I.durationAt_nonneg a x m))
theorem partialValueAt_eq_actual {a : Ground n} {x : ℝ} (m : ℕ) (hm : I.pathCost a m ≤ x) :
    I.partialValueAt a x m=I.value (I.iterate {a} m) := by
  induction m with
  | zero => simp [partialValueAt]
  | succ m ih =>
    have hp := (I.pathCost_mono a (Nat.le_succ m)).trans hm
    have hd : I.durationAt a x m=I.pathCost a (m+1)-I.pathCost a m := by
      simp [durationAt, min_eq_left hm, min_eq_left hp]
    rw [I.partialValueAt_succ, ih hp, hd]
    linarith [I.path_gain a m]
theorem partialValueAt_stops {a : Ground n} {x : ℝ} {k m : ℕ} (hkm : k ≤ m)
    (hx : x ≤ I.pathCost a k) : I.partialValueAt a x m=I.partialValueAt a x k := by
  induction m, hkm using Nat.le_induction with
  | base => rfl
  | succ m hkm ih =>
    have h1 := hx.trans (I.pathCost_mono a hkm)
    have h2 := h1.trans (I.pathCost_mono a (Nat.le_succ m))
    have hd : I.durationAt a x m=0 := by simp [durationAt, min_eq_right h1, min_eq_right h2]
    rw [I.partialValueAt_succ, hd, mul_zero, add_zero, ih]
theorem valueAt_at_prefix {a : Ground n} {k : ℕ} (hk : k ≤ n) :
    I.valueAt a (I.pathCost a k)=I.value (I.iterate {a} k) := by
  change I.partialValueAt a (I.pathCost a k) n = _
  rw [I.partialValueAt_stops hk le_rfl, I.partialValueAt_eq_actual k le_rfl]
theorem valueAt_segment {a : Ground n} {x : ℝ} {k : ℕ} (hk : k < n)
    (hx : I.pathCost a k ≤ x) (hx' : x ≤ I.pathCost a (k+1)) :
    I.valueAt a x=I.value (I.iterate {a} k)+I.pathDensity a k*(x-I.pathCost a k) := by
  change I.partialValueAt a x n = _
  rw [I.partialValueAt_stops (Nat.succ_le_of_lt hk) hx', I.partialValueAt_succ,
    I.partialValueAt_eq_actual k hx]
  simp [durationAt, min_eq_right hx', min_eq_left hx]

theorem exists_crossing (a : Ground n) (m : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hcover : x < I.pathCost a m) : ∃ k < m, I.pathCost a k ≤ x ∧ x < I.pathCost a (k+1) := by
  induction m with
  | zero => simp only [I.pathCost_zero] at hcover; linarith
  | succ m ih =>
    by_cases hm : x < I.pathCost a m
    · obtain ⟨k, hk, h1, h2⟩ := ih hm
      exact ⟨k, by omega, h1, h2⟩
    · exact ⟨m, Nat.lt_succ_self _, le_of_not_gt hm, hcover⟩

theorem greedyDensity_antitone {S T : Selection n} (hST : S ⊆ T) :
    I.greedyDensity T ≤ I.greedyDensity S := by
  cases ht : I.choose T with
  | none => simpa [greedyDensity, ht] using I.greedyDensity_nonneg S
  | some j =>
    cases hs : I.choose S with
    | none =>
      have hmem := I.available_antitone hST (I.choose_spec ht).1
      rw [I.choose_none_iff.mp hs] at hmem
      exact False.elim (Finset.not_mem_empty _ hmem)
    | some i => simpa [greedyDensity, hs, ht] using I.chosen_density_antitone hST hs ht
theorem pathDensity_antitone (a : Ground n) : Antitone (I.pathDensity a) := by
  intro j k hjk
  exact I.greedyDensity_antitone (I.iterate_mono {a} hjk)
theorem pathDensity_terminal (a : Ground n) : I.pathDensity a n=0 := by
  have ht := I.choose_none_iff.mpr (I.iterate_terminal {a})
  simp [pathDensity, greedyDensity, ht]

theorem residual_le_greedyDensity {O S : Selection n} {j : Ground n}
    (hbudget : I.totalCost S+I.cost j ≤ I.budget) :
    I.residual O S j ≤ I.greedyDensity S*I.cost j := by
  cases hc : I.choose S with
  | some i => simpa [greedyDensity, hc] using I.residual_le_chosen_density (O := O) hc hbudget
  | none =>
    have hj : j ∈ S := by
      by_contra hn
      have hm := I.mem_available.mpr ⟨hn, (I.totalCost_insert_le S j).trans hbudget⟩
      rw [I.choose_none_iff.mp hc] at hm
      exact Finset.not_mem_empty _ hm
    simp [I.residual_of_mem O hj, greedyDensity, hc]

end
end S2R.Instance
