import S2R.Algorithm

namespace S2R.Instance
noncomputable section
variable {n : ℕ} (I : S2R.Instance n)

def validPrefixes (a : Ground n) (R : Selection n) : Finset (Fin (n + 1)) := by
  classical
  exact Finset.univ.filter (fun t => Disjoint (I.prefixSet a t) R ∧
    I.Feasible (I.prefixSet a t ∪ R))

@[simp] theorem mem_validPrefixes {a : Ground n} {R : Selection n} {t : Fin (n + 1)} :
    t ∈ I.validPrefixes a R ↔ Disjoint (I.prefixSet a t) R ∧
      I.Feasible (I.prefixSet a t ∪ R) := by classical simp [validPrefixes]

def lastRepair (a : Ground n) (R : Selection n) : Selection n :=
  if h : (I.validPrefixes a R).Nonempty then
    I.prefixSet a ((I.validPrefixes a R).max' h) ∪ R
  else I.prefixSet a (Fin.last n)

def compressedPath (a : Ground n) : Finset (Selection n) :=
  insert (I.prefixSet a (Fin.last n)) ((repairSets (n := n)).image (I.lastRepair a))

theorem lastRepair_mem_path {a : Ground n} (ha : I.Feasible {a})
    {R : Selection n} (hR : R.card ≤ 2) : I.lastRepair a R ∈ I.pathCandidates a := by
  classical
  unfold lastRepair
  split
  next h =>
    have hm := I.mem_validPrefixes.mp (Finset.max'_mem (I.validPrefixes a R) h)
    exact (I.mem_pathCandidates_iff _ _).mpr ⟨hm.2, _, R, hR, rfl⟩
  next h =>
    apply (I.mem_pathCandidates_iff _ _).mpr
    exact ⟨I.prefix_feasible ha _, Fin.last n, ∅, by simp, by simp⟩

theorem compressed_subset_path {a : Ground n} (ha : I.Feasible {a}) :
    I.compressedPath a ⊆ I.pathCandidates a := by
  classical
  intro S hS
  rcases Finset.mem_insert.mp hS with rfl | hS
  · exact (I.mem_pathCandidates_iff _ _).mpr
      ⟨I.prefix_feasible ha _, Fin.last n, ∅, by simp, by simp⟩
  · obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hS
    exact I.lastRepair_mem_path ha ((mem_repairSets _).mp hR)

/-- Every original feasible candidate is contained in a compressed candidate.
The removal of overlap is essential when repair items occur later on the path. -/
theorem candidate_dominated {a : Ground n} {S : Selection n}
    (hS : S ∈ I.pathCandidates a) :
    ∃ T ∈ I.compressedPath a, S ⊆ T := by
  classical
  obtain ⟨hf, t, R, hR, rfl⟩ := (I.mem_pathCandidates_iff _ _).mp hS
  let R' := R \ I.prefixSet a t
  have hcard : R'.card ≤ 2 := (Finset.card_le_card Finset.sdiff_subset).trans hR
  have heq : I.prefixSet a t ∪ R' = I.prefixSet a t ∪ R :=
    Finset.union_sdiff_self_eq_union
  have ht : t ∈ I.validPrefixes a R' := I.mem_validPrefixes.mpr
    ⟨Finset.disjoint_sdiff, by simpa [heq] using hf⟩
  have hn : (I.validPrefixes a R').Nonempty := ⟨t, ht⟩
  refine ⟨I.lastRepair a R', Finset.mem_insert_of_mem ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨R', (mem_repairSets _).mpr hcard, rfl⟩
  · rw [lastRepair, dif_pos hn, ← heq]
    exact Finset.union_subset_union (I.prefix_mono a (Finset.le_max' _ _ ht)) (Finset.Subset.refl _)

def compressedCandidates : Finset (Selection n) := by
  classical
  exact insert ∅ ((Finset.univ.filter (fun a => I.Feasible {a})).biUnion I.compressedPath)

theorem compressed_subset_candidates : I.compressedCandidates ⊆ I.candidates := by
  classical
  intro S hS
  rcases Finset.mem_insert.mp hS with rfl | hS
  · exact Finset.mem_insert_self _ _
  · obtain ⟨a, ha, hS⟩ := Finset.mem_biUnion.mp hS
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨a, ha, I.compressed_subset_path (Finset.mem_filter.mp ha).2 hS⟩)

theorem all_candidates_dominated {S : Selection n} (hS : S ∈ I.candidates) :
    ∃ T ∈ I.compressedCandidates, I.value S ≤ I.value T := by
  classical
  rcases Finset.mem_insert.mp hS with rfl | hS
  · exact ⟨∅, Finset.mem_insert_self _ _, le_rfl⟩
  · obtain ⟨a, ha, hS⟩ := Finset.mem_biUnion.mp hS
    obtain ⟨T, hT, hST⟩ := I.candidate_dominated hS
    exact ⟨T, Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨a, ha, hT⟩), I.monotone hST⟩

theorem compressed_nonempty : I.compressedCandidates.Nonempty :=
  ⟨∅, Finset.mem_insert_self _ _⟩

def compressedOutputSet : Selection n :=
  Classical.choose (I.compressedCandidates.exists_max_image I.value I.compressed_nonempty)

theorem compressedOutput_spec : I.compressedOutputSet ∈ I.compressedCandidates ∧
    ∀ S ∈ I.compressedCandidates, I.value S ≤ I.value I.compressedOutputSet :=
  Classical.choose_spec (I.compressedCandidates.exists_max_image I.value I.compressed_nonempty)

/-- Exact equality of the output values, with no approximation loss. -/
theorem compressedOutput_eq : I.value I.compressedOutputSet = I.output := by
  apply le_antisymm
  · exact I.output_spec.2 _ (I.compressed_subset_candidates I.compressedOutput_spec.1)
  · obtain ⟨T, hT, hval⟩ := I.all_candidates_dominated I.output_spec.1
    exact hval.trans (I.compressedOutput_spec.2 T hT)

theorem repair_shape {R : Selection n} (h : R.card ≤ 2) :
    R = ∅ ∨ (∃ a, R = {a}) ∨ (∃ a b, R = {a, b}) := by
  classical
  by_cases he : R = ∅
  · exact Or.inl he
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
  have hc := Finset.card_erase_add_one ha
  by_cases hr : R.erase a = ∅
  · right; left
    refine ⟨a, ?_⟩
    have hh := Finset.insert_erase ha
    simpa [hr] using hh.symm
  · have hh : (R.erase a).card = 1 := by
      have hp := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hr)
      omega
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hh
    right; right
    refine ⟨a, b, ?_⟩
    have hh := Finset.insert_erase ha
    simpa [hb] using hh.symm

theorem repairSets_card_le : (repairSets (n := n)).card ≤ 1 + n + n * n := by
  classical
  let U : Finset (Ground n) := Finset.univ
  let singles : Finset (Selection n) := U.image (fun a => {a})
  let pairs : Finset (Selection n) := (U ×ˢ U).image (fun p => {p.1, p.2})
  have hsub : repairSets (n := n) ⊆ insert ∅ (singles ∪ pairs) := by
    intro R hR
    rcases repair_shape ((mem_repairSets _).mp hR) with rfl | ⟨a, rfl⟩ | ⟨a, b, rfl⟩
    · exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩)
    · apply Finset.mem_insert_of_mem
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨(a, b), by simp [U], rfl⟩)
  have hsingle : singles.card ≤ n := by
    simpa [U] using (Finset.card_image_le (s := U) (f := fun a : Ground n => ({a} : Selection n)))
  have hpair : pairs.card ≤ n * n := by
    simpa [U] using (Finset.card_image_le (s := U ×ˢ U)
      (f := fun p : Ground n × Ground n => ({p.1, p.2} : Selection n)))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_insert_le (∅ : Selection n) (singles ∪ pairs)
  have h3 := Finset.card_union_le singles pairs
  omega

theorem compressedPath_card_le (a : Ground n) : (I.compressedPath a).card ≤ 2 + n + n*n := by
  have h1 := Finset.card_insert_le (I.prefixSet a (Fin.last n))
    ((repairSets (n := n)).image (I.lastRepair a))
  have h2 := Finset.card_image_le (s := repairSets (n := n)) (f := I.lastRepair a)
  have h3 := repairSets_card_le (n := n)
  unfold compressedPath
  omega

theorem compressedCandidates_card_le : I.compressedCandidates.card ≤ 1 + n * (2+n+n*n) := by
  classical
  let seeds := Finset.univ.filter (fun a => I.Feasible {a})
  have hs : seeds.card ≤ n := by
    simpa using Finset.card_le_card (Finset.filter_subset (fun a => I.Feasible {a}) Finset.univ)
  have h1 := Finset.card_biUnion_le_card_mul seeds I.compressedPath (2+n+n*n)
    (fun a _ => I.compressedPath_card_le a)
  have h2 := Finset.card_insert_le (∅ : Selection n) (seeds.biUnion I.compressedPath)
  have h3 := Nat.mul_le_mul_right (2+n+n*n) hs
  change (insert ∅ (seeds.biUnion I.compressedPath)).card ≤ _
  omega

/-- The oracle queries made by one greedy decision. -/
def stepQueries (S : Selection n) : Finset (Selection n) :=
  insert S ((I.available S).image (fun i => insert i S))

end
end S2R.Instance
