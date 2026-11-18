import S2R.Basic

namespace S2R.Instance
noncomputable section
variable {n : ℕ} (I : S2R.Instance n)

def available (S : Selection n) : Finset (Ground n) := by
  classical
  exact Finset.univ.filter (fun i => i ∉ S ∧ I.Feasible (insert i S))

@[simp] theorem mem_available {S : Selection n} {i : Ground n} :
    i ∈ I.available S ↔ i ∉ S ∧ I.Feasible (insert i S) := by
  classical simp [available]

theorem available_antitone {S T : Selection n} (h : S ⊆ T) :
    I.available T ⊆ I.available S := by
  intro i hi
  rcases I.mem_available.mp hi with ⟨hi, hf⟩
  exact I.mem_available.mpr ⟨fun his => hi (h his),
    I.feasible_subset (Finset.insert_subset_insert i h) hf⟩

def bestSet (S : Selection n) : Finset (Ground n) := by
  classical
  exact (I.available S).filter (fun i => ∀ j ∈ I.available S, I.density j S ≤ I.density i S)

theorem bestSet_nonempty {S : Selection n} (h : (I.available S).Nonempty) :
    (I.bestSet S).Nonempty := by
  classical
  obtain ⟨i, hi, hm⟩ := (I.available S).exists_max_image (fun j => I.density j S) h
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hm⟩⟩

/-- The smallest maximizer implements the fixed tie-breaking order. -/
def choose (S : Selection n) : Option (Ground n) :=
  if h : (I.available S).Nonempty then some ((I.bestSet S).min' (I.bestSet_nonempty h))
  else none

theorem choose_spec {S : Selection n} {i : Ground n} (h : I.choose S = some i) :
    i ∈ I.available S ∧ (∀ j ∈ I.available S, I.density j S ≤ I.density i S) := by
  classical
  unfold choose at h
  split at h
  next hn =>
    have he : (I.bestSet S).min' (I.bestSet_nonempty hn) = i := Option.some.inj h
    have hm := Finset.min'_mem (I.bestSet S) (I.bestSet_nonempty hn)
    rw [he] at hm
    exact Finset.mem_filter.mp hm
  next hn => simp at h

theorem choose_none_iff {S : Selection n} : I.choose S = none ↔ I.available S = ∅ := by
  classical simp [choose, Finset.not_nonempty_iff_eq_empty]

def step (S : Selection n) : Selection n :=
  match I.choose S with
  | none => S
  | some i => insert i S

theorem subset_step (S : Selection n) : S ⊆ I.step S := by
  unfold step
  split
  · exact Finset.Subset.refl _
  · exact Finset.subset_insert _ _

theorem step_feasible {S : Selection n} (h : I.Feasible S) : I.Feasible (I.step S) := by
  unfold step
  split
  · exact h
  next i hc => exact (I.mem_available.mp (I.choose_spec hc).1).2

theorem step_eq_self {S : Selection n} (h : I.available S = ∅) : I.step S = S := by
  simp [step, I.choose_none_iff.mpr h]

theorem step_card {S : Selection n} (h : I.available S ≠ ∅) :
    (I.step S).card = S.card + 1 := by
  unfold step
  split
  next hc => exact False.elim (h (I.choose_none_iff.mp hc))
  next i hc => exact Finset.card_insert_of_not_mem (I.mem_available.mp (I.choose_spec hc).1).1

def iterate (S : Selection n) : ℕ → Selection n
  | 0 => S
  | k + 1 => I.step (iterate S k)

@[simp] theorem iterate_zero (S : Selection n) : I.iterate S 0 = S := rfl
@[simp] theorem iterate_succ (S : Selection n) (k : ℕ) :
    I.iterate S (k + 1) = I.step (I.iterate S k) := rfl

theorem iterate_mono (S : Selection n) : Monotone (I.iterate S) := by
  apply monotone_nat_of_le_succ
  intro k
  exact I.subset_step _

theorem subset_iterate (S : Selection n) (k : ℕ) : S ⊆ I.iterate S k :=
  I.iterate_mono S (Nat.zero_le k)

theorem iterate_feasible {S : Selection n} (h : I.Feasible S) (k : ℕ) :
    I.Feasible (I.iterate S k) := by
  induction k with
  | zero => exact h
  | succ k ih => exact I.step_feasible ih

theorem active_card {S : Selection n} (k : ℕ)
    (h : I.available (I.iterate S k) ≠ ∅) : S.card + k ≤ (I.iterate S k).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : I.available (I.iterate S k) ≠ ∅ := by
      intro he
      have hs := I.step_eq_self he
      apply h
      simpa [iterate_succ, hs] using he
    rw [iterate_succ, I.step_card hp]
    exact Nat.succ_le_succ (ih hp)

theorem active_card_lt {S : Selection n} (h : I.available S ≠ ∅) : S.card < n := by
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr h
  have hnot := (I.mem_available.mp hi).1
  have hc : (insert i S).card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ (insert i S))
  rw [Finset.card_insert_of_not_mem hnot] at hc
  exact hc

/-- After at most n insertions the path has no feasible unselected element. -/
theorem iterate_terminal (S : Selection n) : I.available (I.iterate S n) = ∅ := by
  by_contra h
  have h1 := I.active_card n h
  have h2 := I.active_card_lt h
  omega

def prefixSet (a : Ground n) (t : Fin (n + 1)) : Selection n := I.iterate {a} t.val

theorem prefix_mono (a : Ground n) : Monotone (I.prefixSet a) := by
  intro i j h
  exact I.iterate_mono {a} h

theorem prefix_feasible {a : Ground n} (h : I.Feasible {a}) (t : Fin (n + 1)) :
    I.Feasible (I.prefixSet a t) := I.iterate_feasible h _

def repairSets : Finset (Selection n) := by
  classical
  exact (Finset.univ : Finset (Ground n)).powerset.filter (fun R => R.card ≤ 2)

@[simp] theorem mem_repairSets (R : Selection n) : R ∈ repairSets (n := n) ↔ R.card ≤ 2 := by
  classical simp [repairSets]

def pathCandidates (a : Ground n) : Finset (Selection n) := by
  classical
  exact (Finset.univ.biUnion fun t : Fin (n + 1) =>
    (repairSets (n := n)).image (fun R => I.prefixSet a t ∪ R)).filter I.Feasible

theorem mem_pathCandidates_iff (a : Ground n) (S : Selection n) :
    S ∈ I.pathCandidates a ↔ I.Feasible S ∧
      ∃ t : Fin (n + 1), ∃ R : Selection n, R.card ≤ 2 ∧ S = I.prefixSet a t ∪ R := by
  classical
  simp only [pathCandidates, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ,
    true_and, Finset.mem_image, mem_repairSets]
  constructor
  · rintro ⟨⟨t, R, hR, he⟩, hS⟩
    exact ⟨hS, t, R, hR, he.symm⟩
  · rintro ⟨hS, t, R, hR, he⟩
    exact ⟨⟨t, R, hR, he.symm⟩, hS⟩

def candidates : Finset (Selection n) := by
  classical
  exact insert ∅ ((Finset.univ.filter (fun a => I.Feasible {a})).biUnion I.pathCandidates)

theorem candidates_nonempty : I.candidates.Nonempty := by
  classical exact ⟨∅, Finset.mem_insert_self _ _⟩

theorem candidate_feasible {S : Selection n} (h : S ∈ I.candidates) : I.Feasible S := by
  classical
  rcases Finset.mem_insert.mp h with rfl | h
  · exact I.feasible_empty
  · obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp h
    exact ((I.mem_pathCandidates_iff a S).mp ha).1

def outputSet : Selection n :=
  Classical.choose (I.candidates.exists_max_image I.value I.candidates_nonempty)

theorem output_spec : I.outputSet ∈ I.candidates ∧
    ∀ S ∈ I.candidates, I.value S ≤ I.value I.outputSet :=
  Classical.choose_spec (I.candidates.exists_max_image I.value I.candidates_nonempty)

def output : ℝ := I.value I.outputSet

theorem output_feasible : I.Feasible I.outputSet := I.candidate_feasible I.output_spec.1
theorem output_nonneg : 0 ≤ I.output := I.value_nonneg _
theorem output_le_optimum : I.output ≤ I.optimum := I.le_optimum I.output_feasible

theorem repair_le_output {a : Ground n} (ha : I.Feasible {a})
    (t : Fin (n + 1)) {R : Selection n} (hR : R.card ≤ 2)
    (hf : I.Feasible (I.prefixSet a t ∪ R)) : I.value (I.prefixSet a t ∪ R) ≤ I.output := by
  classical
  apply I.output_spec.2
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨a, ?_, (I.mem_pathCandidates_iff _ _).mpr ⟨hf, t, R, hR, rfl⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ha

theorem prefix_le_output {a : Ground n} (ha : I.Feasible {a}) (t : Fin (n + 1)) :
    I.value (I.prefixSet a t) ≤ I.output := by
  simpa using I.repair_le_output ha t (R := ∅) (by simp)
    (by simpa using I.prefix_feasible ha t)

theorem small_solution_le_output {O : Selection n} (hO : I.Feasible O) (hc : O.card ≤ 3) :
    I.value O ≤ I.output := by
  classical
  by_cases he : O = ∅
  · simpa [he, I.normalized] using I.output_nonneg
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hf : I.Feasible {a} := I.feasible_subset (Finset.singleton_subset_iff.mpr ha) hO
  have hr : (O.erase a).card ≤ 2 := by
    have he := Finset.card_erase_add_one ha
    omega
  have hu : I.prefixSet a (0 : Fin (n + 1)) ∪ O.erase a = O := by
    change {a} ∪ O.erase a = O
    rw [Finset.union_erase_of_mem (Finset.mem_singleton_self a)]
    exact Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr ha)
  have h := I.repair_le_output hf (0 : Fin (n + 1)) hr (by simpa [hu] using hO)
  simpa [hu] using h

end
end S2R.Instance

