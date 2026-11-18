import S2R.Compression
import S2R.OrderedSweep

namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep
variable {n : ℕ} (I : Instance n)

def costOrder (i j : Ground n) : Prop := I.cost j ≤ I.cost i

instance costOrder_total : IsTotal (Ground n) I.costOrder :=
  ⟨fun i j => le_total (I.cost j) (I.cost i)⟩
instance costOrder_trans : IsTrans (Ground n) I.costOrder :=
  ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩

def itemList (_I : Instance n) : List (Ground n) := List.finRange n
def costSorted : List (Ground n) := by
  classical
  exact I.itemList.insertionSort I.costOrder

theorem costSorted_length : I.costSorted.length=n := by simp [costSorted, itemList]
theorem mem_costSorted (i : Ground n) : i ∈ I.costSorted := by simp [costSorted, itemList]
theorem costSorted_sorted : I.costSorted.Sorted I.costOrder := by
  classical
  exact List.sorted_insertionSort _ _

def prefixCosts (a : Ground n) : List ℝ := List.ofFn (fun t => I.totalCost (I.prefixSet a t))
def budgetCount (a : Ground n) (q : ℝ) : ℕ :=
  initialCount (fun t : Fin (n+1) => I.totalCost (I.prefixSet a t) ≤ q)
def absenceCount (a i : Ground n) : ℕ :=
  initialCount (fun t : Fin (n+1) => i ∉ I.prefixSet a t)

theorem prefixCosts_sorted (a : Ground n) : (I.prefixCosts a).Sorted (· ≤ ·) :=
  (List.sorted_le_ofFn_iff).mpr (fun _ _ h => I.totalCost_mono (I.prefix_mono a h))
theorem prefixCosts_length (a : Ground n) : (I.prefixCosts a).length=n+1 := by
  simp [prefixCosts]

theorem budgetCount_spec (a : Ground n) (q : ℝ) (t : Fin (n+1)) :
    I.totalCost (I.prefixSet a t) ≤ q ↔ t.val < I.budgetCount a q :=
  initialCount_spec _ (fun i j hij hj => (I.totalCost_mono (I.prefix_mono a hij)).trans hj) t

theorem absenceCount_spec (a i : Ground n) (t : Fin (n+1)) :
    i ∉ I.prefixSet a t ↔ t.val < I.absenceCount a i :=
  initialCount_spec (fun t => i ∉ I.prefixSet a t)
    (fun j k hjk hk hmem => hk (I.prefix_mono a hjk hmem)) t

def rowThreshold (i : Option (Ground n)) (j : Ground n) : ℝ :=
  I.budget-((i.map I.cost).getD 0+I.cost j)

def rowSweep (a : Ground n) (i : Option (Ground n)) : Sweep :=
  sweep (I.costSorted.map (I.rowThreshold i)) (I.prefixCosts a) 0

theorem rowThreshold_sorted (i : Option (Ground n)) :
    (I.costSorted.map (I.rowThreshold i)).Sorted (· ≤ ·) := by
  apply List.Pairwise.map
  · intro j k h
    change I.cost k ≤ I.cost j at h
    dsimp [rowThreshold]
    linarith
  · exact I.costSorted_sorted

theorem rowSweep_correct (a : Ground n) (i : Option (Ground n)) :
    (I.rowSweep a i).answers=I.costSorted.map (fun j => I.budgetCount a (I.rowThreshold i j)) := by
  rw [rowSweep, sweep_correct (I.rowThreshold_sorted i) (I.prefixCosts_sorted a)]
  simp only [List.map_map, Nat.zero_add]
  apply List.map_congr_left
  intro j _
  exact filter_ofFn_length _ _

theorem rowSweep_ticks (a : Ground n) (i : Option (Ground n)) :
    (I.rowSweep a i).ticks ≤ 6*n+2 := by
  have h := sweep_ticks (I.costSorted.map (I.rowThreshold i)) (I.prefixCosts a) 0
  rw [List.length_map, I.costSorted_length, I.prefixCosts_length] at h
  change (I.rowSweep a i).ticks+2*(I.rowSweep a i).rest.length ≤ _ at h
  omega

/-- The cutoff is a count, so zero represents the manuscript's index -1.
The array lookup and at most two temporary insertions are constant work. -/
def repairAtCount (a : Ground n) (R : Selection n) (k : ℕ) : Selection n :=
  if h : 0 < k ∧ k ≤ n+1 then I.prefixSet a ⟨k-1, by omega⟩ ∪ R
  else I.prefixSet a (Fin.last n)

theorem repairAtCount_correct (a : Ground n) (R : Selection n) (k : ℕ)
    (hk : k ≤ n+1)
    (hvalid : ∀ t : Fin (n+1), t ∈ I.validPrefixes a R ↔ t.val < k) :
    I.repairAtCount a R k=I.lastRepair a R := by
  classical
  by_cases hp : 0 < k
  · let t : Fin (n+1) := ⟨k-1, by omega⟩
    have ht : t ∈ I.validPrefixes a R := (hvalid t).mpr (by dsimp [t]; omega)
    have hne : (I.validPrefixes a R).Nonempty := ⟨t,ht⟩
    have he : (I.validPrefixes a R).max' hne=t := by
      apply le_antisymm
      · have hm := (hvalid _).mp (Finset.max'_mem _ hne)
        change ((I.validPrefixes a R).max' hne).val ≤ t.val
        dsimp [t]
        omega
      · exact Finset.le_max' _ _ ht
    simp only [repairAtCount, dif_pos (show 0 < k ∧ k ≤ n+1 from ⟨hp,hk⟩),
      lastRepair, dif_pos hne, he]
    rfl
  · have hne : ¬ (I.validPrefixes a R).Nonempty := by
      rintro ⟨t,ht⟩
      have hh := (hvalid t).mp ht
      omega
    simp [repairAtCount, hp, lastRepair, hne]

def rowRepair (a : Ground n) (i : Option (Ground n)) (j : Ground n) (k : ℕ) : Selection n :=
  match i with
  | none => I.repairAtCount a {j} (min (I.absenceCount a j) k)
  | some l => if l=j then I.prefixSet a (Fin.last n) else
      I.repairAtCount a {l,j} (min (I.absenceCount a l) (min (I.absenceCount a j) k))

theorem rowRepair_none (a j : Ground n) :
    I.rowRepair a none j (I.budgetCount a (I.rowThreshold none j))=I.lastRepair a {j} := by
  apply I.repairAtCount_correct
  · exact (min_le_right _ _).trans (initialCount_le _)
  · intro t
    rw [I.mem_validPrefixes]
    simp only [lt_min_iff, ← I.absenceCount_spec, ← I.budgetCount_spec]
    constructor
    · rintro ⟨hd,hf⟩
      have hj : j ∉ I.prefixSet a t := Finset.disjoint_singleton_right.mp hd
      refine ⟨hj, ?_⟩
      have he := I.totalCost_union hd
      simp only [I.totalCost_singleton] at he
      change I.totalCost (I.prefixSet a t ∪ {j}) ≤ I.budget at hf
      change I.totalCost (I.prefixSet a t) ≤ I.budget-(0+I.cost j)
      linarith
    · rintro ⟨hj,hc⟩
      have hd : Disjoint (I.prefixSet a t) {j} := Finset.disjoint_singleton_right.mpr hj
      refine ⟨hd, ?_⟩
      have he := I.totalCost_union hd
      simp only [I.totalCost_singleton] at he
      change I.totalCost (I.prefixSet a t ∪ {j}) ≤ I.budget
      change I.totalCost (I.prefixSet a t) ≤ I.budget-(0+I.cost j) at hc
      linarith

theorem rowRepair_some (a i j : Ground n) (hne : i ≠ j) :
    I.rowRepair a (some i) j (I.budgetCount a (I.rowThreshold (some i) j))=
      I.lastRepair a {i,j} := by
  classical
  rw [rowRepair, if_neg hne]
  apply I.repairAtCount_correct
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (initialCount_le _))
  · intro t
    rw [I.mem_validPrefixes]
    simp only [lt_min_iff, ← I.absenceCount_spec, ← I.budgetCount_spec]
    have hd : Disjoint (I.prefixSet a t) {i,j} ↔ i ∉ I.prefixSet a t ∧ j ∉ I.prefixSet a t := by
      simp
    constructor
    · rintro ⟨hdis,hf⟩
      have he := I.totalCost_union hdis
      have hpair : I.totalCost {i,j}=I.cost i+I.cost j := by simp [totalCost, hne]
      rw [hpair] at he
      change I.totalCost (I.prefixSet a t ∪ {i,j}) ≤ I.budget at hf
      exact ⟨(hd.mp hdis).1, (hd.mp hdis).2, by change _ ≤ I.budget-(I.cost i+I.cost j); linarith⟩
    · rintro ⟨hi,hj,hc⟩
      have hdis := hd.mpr ⟨hi,hj⟩
      refine ⟨hdis, ?_⟩
      have he := I.totalCost_union hdis
      have hpair : I.totalCost {i,j}=I.cost i+I.cost j := by simp [totalCost, hne]
      rw [hpair] at he
      change I.totalCost (I.prefixSet a t ∪ {i,j}) ≤ I.budget
      change I.totalCost (I.prefixSet a t) ≤ I.budget-(I.cost i+I.cost j) at hc
      linarith

def rowCandidates (a : Ground n) (i : Option (Ground n)) : List (Selection n) :=
  (I.costSorted.zip (I.rowSweep a i).answers).map (fun p => I.rowRepair a i p.1 p.2)

theorem rowCandidates_correct (a : Ground n) (i : Option (Ground n)) :
    I.rowCandidates a i=I.costSorted.map
      (fun j => I.rowRepair a i j (I.budgetCount a (I.rowThreshold i j))) := by
  rw [rowCandidates, I.rowSweep_correct]
  generalize I.costSorted = L
  induction L with
  | nil => rfl
  | cons j L ih => simp [ih]

theorem rowCandidates_length (a : Ground n) (i : Option (Ground n)) :
    (I.rowCandidates a i).length=n := by rw [I.rowCandidates_correct, List.length_map, I.costSorted_length]

def implementedPath (a : Ground n) : List (Selection n) :=
  I.prefixSet a (Fin.last n)::(I.rowCandidates a none ++
    I.itemList.flatMap (fun i => I.rowCandidates a (some i)))

theorem lastRepair_empty (a : Ground n) (ha : I.Feasible {a}) :
    I.lastRepair a ∅=I.prefixSet a (Fin.last n) := by
  classical
  have hm : Fin.last n ∈ I.validPrefixes a ∅ := by
    apply I.mem_validPrefixes.mpr
    simp [I.prefix_feasible ha]
  have hn : (I.validPrefixes a ∅).Nonempty := ⟨Fin.last n,hm⟩
  have he : (I.validPrefixes a ∅).max' hn=Fin.last n :=
    le_antisymm (Fin.le_last _) (Finset.le_max' _ _ hm)
  simp [lastRepair, hn, he]

theorem implementedPath_correct (a : Ground n) (ha : I.Feasible {a}) :
    (I.implementedPath a).toFinset=I.compressedPath a := by
  classical
  ext S
  simp only [List.mem_toFinset, implementedPath, List.mem_cons, List.mem_append,
    List.mem_flatMap, compressedPath, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | hS | ⟨i,hi,hS⟩)
    · exact Or.inl rfl
    · rw [I.rowCandidates_correct] at hS
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hS
      right
      exact ⟨{j}, by simp [mem_repairSets], (I.rowRepair_none a j).symm⟩
    · rw [I.rowCandidates_correct] at hS
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hS
      by_cases he : i=j
      · left; simp [rowRepair, he]
      · right
        exact ⟨{i,j}, by simp [mem_repairSets, he], (I.rowRepair_some a i j he).symm⟩
  · rintro (rfl | ⟨R,hR,rfl⟩)
    · exact Or.inl rfl
    · rcases repair_shape ((mem_repairSets _).mp hR) with rfl | ⟨j,rfl⟩ | ⟨i,j,rfl⟩
      · exact Or.inl (I.lastRepair_empty a ha)
      · right; left
        rw [I.rowCandidates_correct]
        exact List.mem_map.mpr ⟨j,I.mem_costSorted j,I.rowRepair_none a j⟩
      · by_cases he : i=j
        · subst i
          right; left
          rw [I.rowCandidates_correct]
          exact List.mem_map.mpr ⟨j,I.mem_costSorted j,by simpa using I.rowRepair_none a j⟩
        · right; right
          refine ⟨i, by simp [itemList], ?_⟩
          rw [I.rowCandidates_correct]
          exact List.mem_map.mpr ⟨j,I.mem_costSorted j,I.rowRepair_some a i j he⟩

end
end S2R.Instance
