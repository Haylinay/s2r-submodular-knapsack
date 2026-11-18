import S2R.SpaceComplexity

/-! A single erased cost order and borrowed suffixes replace the full
ordered-pair grid. Jobs describe loop cursors, not copied suffix arrays. -/
namespace S2R.TailJobs
variable {α : Type*}

def pairs : List α → List (Option α × List α)
  | [] => []
  | x::xs => (some x,xs)::pairs xs

def jobs (xs : List α) : List (Option α × List α) := (none,xs)::pairs xs

theorem pairs_length (xs : List α) : (pairs xs).length=xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [pairs,ih]

theorem jobs_length (xs : List α) : (jobs xs).length=xs.length+1 := by
  simp [jobs,pairs_length]

theorem pairs_weight (xs : List α) :
    2*((pairs xs).map (fun j => j.2.length)).sum+xs.length=xs.length^2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [pairs,List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [ih]

theorem jobs_weight (xs : List α) :
    2*((jobs xs).map (fun j => j.2.length)).sum=xs.length*(xs.length+1) := by
  have h := pairs_weight xs
  simp only [jobs,List.map_cons,List.sum_cons]
  nlinarith only [h]

theorem pairs_suffix {xs : List α} {job : Option α × List α} (h : job ∈ pairs xs) :
    job.2.Sublist xs := by
  induction xs with
  | nil => simp [pairs] at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact List.Sublist.cons _ (List.Sublist.refl _)
    · exact List.Sublist.cons _ (ih h)

theorem jobs_suffix {xs : List α} {job : Option α × List α} (h : job ∈ jobs xs) :
    job.2.Sublist xs := by
  rcases List.mem_cons.mp h with rfl | h
  · exact List.Sublist.refl _
  · exact pairs_suffix h

theorem pairs_cover {xs : List α} {i j : α} (hi : i ∈ xs) (hj : j ∈ xs) (hne : i ≠ j) :
    ∃ job ∈ pairs xs, (job.1=some i ∧ j ∈ job.2) ∨ (job.1=some j ∧ i ∈ job.2) := by
  induction xs with
  | nil => simp at hi
  | cons x xs ih =>
    rcases List.mem_cons.mp hi with rfl | hi
    · have hj' : j ∈ xs := (List.mem_cons.mp hj).resolve_left (Ne.symm hne)
      exact ⟨(some i,xs),List.mem_cons_self,Or.inl ⟨rfl,hj'⟩⟩
    · have hix : i ∈ xs := hi
      rcases List.mem_cons.mp hj with rfl | hj
      · exact ⟨(some j,xs),List.mem_cons_self,Or.inr ⟨rfl,hix⟩⟩
      · obtain ⟨job,hjob,h⟩ := ih hi hj
        exact ⟨job,List.mem_cons_of_mem _ hjob,h⟩

end S2R.TailJobs

namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

def repairOrder (a : Ground n) : List (Ground n) := I.costSorted.erase a

theorem costSorted_nodup : I.costSorted.Nodup := by
  classical
  exact (List.perm_insertionSort I.costOrder I.itemList).nodup_iff.mpr (List.nodup_finRange n)

theorem repairOrder_mem (a j : Ground n) : j ∈ I.repairOrder a ↔ j ≠ a := by
  rw [repairOrder,I.costSorted_nodup.mem_erase_iff]
  simp [I.mem_costSorted]

theorem repairOrder_length (a : Ground n) : (I.repairOrder a).length+1=n := by
  simpa only [repairOrder,I.costSorted_length] using List.length_erase_add_one (I.mem_costSorted a)

theorem repairOrder_sorted (a : Ground n) : (I.repairOrder a).Sorted I.costOrder :=
  I.costSorted_sorted.erase a

def repairJobs (a : Ground n) : List (Option (Ground n) × List (Ground n)) :=
  TailJobs.jobs (I.repairOrder a)

theorem repairJobs_length (a : Ground n) : (I.repairJobs a).length=n := by
  rw [repairJobs,TailJobs.jobs_length,I.repairOrder_length]

theorem repairJobs_weight (a : Ground n) :
    2*((I.repairJobs a).map (fun j => j.2.length)).sum+n=n*n := by
  have h := TailJobs.jobs_weight (I.repairOrder a)
  have hl := I.repairOrder_length a
  change 2*((TailJobs.jobs (I.repairOrder a)).map (fun j => j.2.length)).sum+n=n*n
  nlinarith only [h,hl]

theorem repairJob_sorted (a : Ground n) {job : Option (Ground n) × List (Ground n)}
    (h : job ∈ I.repairJobs a) : job.2.Sorted I.costOrder :=
  (I.repairOrder_sorted a).sublist (TailJobs.jobs_suffix h)

theorem repairJob_length (a : Ground n) {job : Option (Ground n) × List (Ground n)}
    (h : job ∈ I.repairJobs a) : job.2.length+1 ≤ n := by
  have hs := (TailJobs.jobs_suffix h).length_le
  have hl := I.repairOrder_length a
  omega

/-- Any repair containing the seed has no disjoint prefix and collapses
to the already retained terminal prefix. -/
theorem lastRepair_contains_seed (a : Ground n) {R : Selection n} (ha : a ∈ R) :
    I.lastRepair a R=I.prefixSet a (Fin.last n) := by
  classical
  have he : ¬(I.validPrefixes a R).Nonempty := by
    rintro ⟨t,ht⟩
    have hd := (I.mem_validPrefixes.mp ht).1
    have hm : a ∈ I.prefixSet a t := I.subset_iterate {a} t.val (by simp)
    exact Finset.disjoint_left.mp hd hm ha
  simp [lastRepair,he]

/-- A singleton seed leaves at most n-1 insertions. The last charged
greedy batch therefore already contains the final prefix value. -/
theorem terminal_from_last_greedy (a : Ground n) :
    I.prefixSet a (Fin.last n)=I.iterate {a} (n-1) := by
  have hn : 1 ≤ n := by have h := a.isLt; omega
  have ht : I.available (I.iterate {a} (n-1))=∅ := by
    by_contra h
    have h₁ := I.active_card (n-1) h
    have h₂ := I.active_card_lt h
    simp only [Finset.card_singleton] at h₁
    omega
  change I.iterate {a} n=_
  calc
    I.iterate {a} n = I.iterate {a} ((n-1)+1) := congrArg (fun k => I.iterate {a} k) (by omega)
    _ = _ := by rw [I.iterate_succ,I.step_eq_self ht]

theorem terminal_in_greedy_queries (a : Ground n) :
    ∃ k : Fin n, I.prefixSet a (Fin.last n) ∈ I.stepQueries (I.iterate {a} k.val) := by
  have hn : n-1<n := by have h := a.isLt; omega
  refine ⟨⟨n-1,hn⟩,?_⟩
  rw [I.terminal_from_last_greedy]
  exact Finset.mem_insert_self _ _

/-- The monotone sweep works on any sorted suffix of the erased order. -/
theorem runRow_sorted_values (a : Ground n) (order : List (Ground n))
    (hs : order.Sorted I.costOrder) (i : Option (Ground n)) :
    (I.runRow order (I.reuseCache a).value i).value=
      order.map (fun j => I.rowRepair a i j (I.budgetCount a (I.rowThreshold i j))) := by
  have hq : (order.map (I.rowThreshold i)).Sorted (· ≤ ·) := by
    apply List.Pairwise.map
    · intro j k h
      change I.cost k ≤ I.cost j at h
      dsimp [rowThreshold]
      linarith
    · exact hs
  have hw : (sweep (order.map (I.rowThreshold i)) (I.prefixCosts a) 0).answers=
      order.map (fun j => I.budgetCount a (I.rowThreshold i j)) := by
    rw [sweep_correct hq (I.prefixCosts_sorted a)]
    simp only [List.map_map,Nat.zero_add]
    apply List.map_congr_left
    intro j _
    exact filter_ofFn_length _ _
  rw [I.reuseCache_correct]
  simp only [runRow,cachedRowRepair_reference,referenceCache]
  change (order.zip (sweep (order.map (I.rowThreshold i)) (I.prefixCosts a) 0).answers).map _ = _
  rw [hw]
  clear hs hq hw
  induction order with
  | nil => rfl
  | cons j order ih =>
    change cachedRowRepair (I.referenceCache a) i j _ :: _ = _ :: _
    exact congrArg₂ List.cons (I.cachedRowRepair_reference a i j _) ih

def thinPath (a : Ground n) : List (Selection n) :=
  I.prefixSet a (Fin.last n)::(I.repairJobs a).flatMap
    (fun job => (I.runRow job.2 (I.reuseCache a).value job.1).value)

theorem thinPath_correct (a : Ground n) (ha : I.Feasible {a}) :
    (I.thinPath a).toFinset=I.compressedPath a := by
  classical
  have hsingle (j : Ground n) (hj : j ≠ a) : I.lastRepair a {j} ∈ I.thinPath a := by
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨(none,I.repairOrder a),List.mem_cons_self,?_⟩
    rw [I.runRow_sorted_values _ _ (I.repairOrder_sorted a),← I.rowRepair_none a j]
    exact List.mem_map.mpr ⟨j,(I.repairOrder_mem a j).mpr hj,rfl⟩
  have hpair (i j : Ground n) (hi : i ≠ a) (hj : j ≠ a) (hne : i ≠ j) :
      I.lastRepair a {i,j} ∈ I.thinPath a := by
    obtain ⟨job,hjob,h⟩ := TailJobs.pairs_cover
      ((I.repairOrder_mem a i).mpr hi) ((I.repairOrder_mem a j).mpr hj) hne
    have hm : job ∈ I.repairJobs a := List.mem_cons_of_mem _ hjob
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr
    refine ⟨job,hm,?_⟩
    rw [I.runRow_sorted_values _ _ (I.repairJob_sorted a hm)]
    rcases h with ⟨he,hj'⟩ | ⟨he,hi'⟩
    · rw [he]
      exact List.mem_map.mpr ⟨j,hj',I.rowRepair_some a i j hne⟩
    · rw [he]
      refine List.mem_map.mpr ⟨i,hi',?_⟩
      rw [I.rowRepair_some a j i (Ne.symm hne)]
      congr 1
      exact Finset.pair_comm j i
  ext S
  constructor
  · intro h
    rcases List.mem_cons.mp (List.mem_toFinset.mp h) with rfl | h
    · exact Finset.mem_insert_self _ _
    · obtain ⟨job,hjob,hS⟩ := List.mem_flatMap.mp h
      rw [I.runRow_sorted_values _ _ (I.repairJob_sorted a hjob)] at hS
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hS
      cases he : job.1 with
      | none =>
        rw [I.rowRepair_none]
        exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨{j},by simp [mem_repairSets],rfl⟩)
      | some i =>
        by_cases hij : i=j
        · simp [rowRepair,hij,compressedPath]
        · rw [I.rowRepair_some a i j hij]
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨{i,j},by simp [mem_repairSets,hij],rfl⟩)
  · intro h
    apply List.mem_toFinset.mpr
    rcases Finset.mem_insert.mp h with rfl | h
    · exact List.mem_cons_self
    · obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp h
      rcases repair_shape ((mem_repairSets R).mp hR) with rfl | ⟨j,rfl⟩ | ⟨i,j,rfl⟩
      · rw [I.lastRepair_empty a ha]; exact List.mem_cons_self
      · by_cases hj : j=a
        · subst j
          rw [I.lastRepair_contains_seed a (by simp)]
          exact List.mem_cons_self
        · exact hsingle j hj
      · by_cases hi : i=a
        · subst i
          rw [I.lastRepair_contains_seed a (by simp)]
          exact List.mem_cons_self
        · by_cases hj : j=a
          · subst j
            rw [I.lastRepair_contains_seed a (by simp)]
            exact List.mem_cons_self
          · by_cases hij : i=j
            · subst i
              simpa using hsingle j hj
            · exact hpair i j hi hj hij

end
end S2R.Instance
