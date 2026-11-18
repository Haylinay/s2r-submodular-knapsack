import S2R.PathBounds

namespace S2R.Instance
noncomputable section
variable {n : ℕ} (I : Instance n)

def greedyDensity (S : Selection n) : ℝ :=
  match I.choose S with
  | none => 0
  | some i => I.density i S

theorem greedyDensity_nonneg (S : Selection n) : 0 ≤ I.greedyDensity S := by
  unfold greedyDensity
  split
  · exact le_rfl
  · exact I.density_nonneg _ _

theorem step_value_cost (S : Selection n) :
    I.value (I.step S)-I.value S =
      I.greedyDensity S*(I.totalCost (I.step S)-I.totalCost S) := by
  cases h : I.choose S with
  | none => simp [step, greedyDensity, h]
  | some i =>
    have hi := (I.mem_available.mp (I.choose_spec h).1).1
    rw [I.chosen_gain h]
    simp only [step, greedyDensity, h, I.totalCost_insert hi]
    ring

def pathCost (a : Ground n) (k : ℕ) : ℝ := I.totalCost (I.iterate {a} k)-I.cost a
def pathDensity (a : Ground n) (k : ℕ) : ℝ := I.greedyDensity (I.iterate {a} k)
def clippedCost (a : Ground n) (k : ℕ) : ℝ := min (I.pathCost a k) 1
def duration (a : Ground n) (k : ℕ) : ℝ := I.clippedCost a (k+1)-I.clippedCost a k
def curveValue (a : Ground n) (k : ℕ) : ℝ := I.value {a}+
  ∑ j ∈ Finset.range k, I.pathDensity a j*I.duration a j

@[simp] theorem pathCost_zero (a : Ground n) : I.pathCost a 0 = 0 := by simp [pathCost]
theorem pathCost_mono (a : Ground n) : Monotone (I.pathCost a) := by
  intro j k hjk
  exact sub_le_sub_right (I.totalCost_mono (I.iterate_mono {a} hjk)) _
theorem pathCost_nonneg (a : Ground n) (k : ℕ) : 0 ≤ I.pathCost a k := by
  simpa using I.pathCost_mono a (Nat.zero_le k)
theorem duration_nonneg (a : Ground n) (k : ℕ) : 0 ≤ I.duration a k :=
  sub_nonneg.mpr (min_le_min (I.pathCost_mono a (Nat.le_succ k)) le_rfl)
theorem duration_le (a : Ground n) (k : ℕ) :
    I.duration a k ≤ I.pathCost a (k+1)-I.pathCost a k := by
  have h := I.pathCost_mono a (Nat.le_succ k)
  unfold duration clippedCost
  by_cases hk : I.pathCost a k ≤ 1
  · rw [min_eq_left hk]
    linarith [min_le_left (I.pathCost a (k+1)) 1]
  · have hk' : 1 ≤ I.pathCost a k := le_of_not_ge hk
    rw [min_eq_right hk', min_eq_right (hk'.trans h)]
    linarith
theorem duration_pos_left {a : Ground n} {k : ℕ} (h : 0 < I.duration a k) :
    I.pathCost a k < 1 := by
  by_contra hn
  have h1 := le_of_not_gt hn
  have h2 := h1.trans (I.pathCost_mono a (Nat.le_succ k))
  simp [duration, clippedCost, min_eq_right h1, min_eq_right h2] at h

@[simp] theorem curveValue_zero (a : Ground n) : I.curveValue a 0 = I.value {a} := by simp [curveValue]
theorem curveValue_succ (a : Ground n) (k : ℕ) :
    I.curveValue a (k+1) = I.curveValue a k+I.pathDensity a k*I.duration a k := by
  simp [curveValue, Finset.sum_range_succ, add_assoc]
theorem curveValue_mono (a : Ground n) : Monotone (I.curveValue a) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [I.curveValue_succ]
  exact le_add_of_nonneg_right (mul_nonneg (I.greedyDensity_nonneg _) (I.duration_nonneg a k))
theorem path_gain (a : Ground n) (k : ℕ) :
    I.value (I.iterate {a} (k+1))-I.value (I.iterate {a} k) =
      I.pathDensity a k*(I.pathCost a (k+1)-I.pathCost a k) := by
  have h := I.step_value_cost (I.iterate {a} k)
  simpa [iterate_succ, pathDensity, pathCost] using h
theorem curveValue_le_actual (a : Ground n) (k : ℕ) :
    I.curveValue a k ≤ I.value (I.iterate {a} k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := mul_le_mul_of_nonneg_left (I.duration_le a k) (I.greedyDensity_nonneg (I.iterate {a} k))
    have hg := I.path_gain a k
    rw [I.curveValue_succ]
    change I.pathDensity a k*I.duration a k ≤ I.pathDensity a k*(I.pathCost a (k+1)-I.pathCost a k) at h
    linarith
theorem curveValue_eq_actual {a : Ground n} (k : ℕ) (hk : I.pathCost a k ≤ 1) :
    I.curveValue a k = I.value (I.iterate {a} k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp := (I.pathCost_mono a (Nat.le_succ k)).trans hk
    have hd : I.duration a k = I.pathCost a (k+1)-I.pathCost a k := by
      simp [duration, clippedCost, min_eq_left hk, min_eq_left hp]
    rw [I.curveValue_succ, ih hp, hd]
    linarith [I.path_gain a k]
theorem curveValue_le_output {a : Ground n} (ha : I.Feasible {a}) {k : ℕ} (hk : k ≤ n) :
    I.curveValue a k ≤ I.output := by
  have h := I.prefix_le_output ha (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n+1))
  exact (I.curveValue_le_actual a k).trans h
theorem duration_sum (a : Ground n) (k : ℕ) :
    (∑ j ∈ Finset.range k, I.duration a j) = I.clippedCost a k := by
  induction k with
  | zero => simp [clippedCost]
  | succ k ih => rw [Finset.sum_range_succ, ih]; unfold duration; ring

theorem totalCost_union_le (S T : Selection n) :
    I.totalCost (S ∪ T) ≤ I.totalCost S+I.totalCost T := by
  classical
  have he := Finset.sum_union_inter (s₁ := S) (s₂ := T) (f := I.cost)
  have h := I.totalCost_nonneg (S ∩ T)
  unfold totalCost at h ⊢
  linarith

end
end S2R.Instance
