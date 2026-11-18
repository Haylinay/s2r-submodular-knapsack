import S2R.ReusedCache
import S2R.MemorySemantics

/-! A sequential, compact-record implementation and its independent peak
word-space proof. Sets in denotations are views of cached membership arrays,
not an allocation of one n-word array for every repair candidate. The live
arrays and registers are allocated explicitly in the Memory plan below. -/
namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

/-- Three words: a prefix index and two optional item indices. `none` can
be encoded by a sentinel; an optional item still occupies one RAM word. -/
structure RepairRecord (n : ℕ) where
  cutoff : Fin (n+1)
  first : Option (Ground n)
  second : Option (Ground n)

def RepairRecord.decode (cache : PathCache n) (r : RepairRecord n) : Selection n :=
  cache.states r.cutoff ∪ r.first.toList.toFinset ∪ r.second.toList.toFinset

def terminalRecord : RepairRecord n := ⟨Fin.last n,none,none⟩

/-- Concrete membership-cell representation of the cached sets. -/
def snapshotBits (cache : PathCache n) (t : Fin (n+1)) (i : Ground n) : Bool := by
  classical
  exact decide (i ∈ cache.states t)

theorem snapshotBits_decode (cache : PathCache n) (t : Fin (n+1)) :
    Finset.univ.filter (fun i => snapshotBits cache t i)=cache.states t := by
  classical
  ext i
  simp [snapshotBits]

theorem snapshot_cell_count : Fintype.card (Fin (n+1) × Ground n)=n*(n+1) := by
  simp [Ground,Nat.mul_comm]

theorem history_cell_count : Fintype.card (Ground n × Fin n)=n*n := by
  simp [Ground]

/-- Two temporary membership writes can be undone with two saved bits;
no copy of the whole prefix array is necessary, even for equal indices. -/
theorem two_edits_restore (bits : Ground n → Bool) (i j : Ground n) :
    Function.update (Function.update
      (Function.update (Function.update bits i true) j true) j (bits j)) i (bits i)=bits := by
  classical
  funext x
  by_cases hi : i=x <;> by_cases hj : j=x <;> simp_all [Function.update,eq_comm]

def recordAt (i j : Option (Ground n)) (k : ℕ) : RepairRecord n :=
  if h : 0 < k ∧ k ≤ n+1 then ⟨⟨k-1,by omega⟩,i,j⟩ else terminalRecord

def rowRecord (cache : PathCache n) (i : Option (Ground n))
    (j : Ground n) (k : ℕ) : RepairRecord n :=
  match i with
  | none => recordAt (some j) none (min (cache.absent j) k)
  | some l => if l=j then terminalRecord else
      recordAt (some l) (some j) (min (cache.absent l) (min (cache.absent j) k))

theorem rowRecord_decode (cache : PathCache n) (i : Option (Ground n))
    (j : Ground n) (k : ℕ) :
    (rowRecord cache i j k).decode cache=cachedRowRepair cache i j k := by
  classical
  cases i with
  | none =>
    simp only [rowRecord,cachedRowRepair,recordAt,cachedRepairAt]
    split <;> simp [RepairRecord.decode,terminalRecord]
  | some l =>
    by_cases h : l=j
    · simp [rowRecord,cachedRowRepair,h,RepairRecord.decode,terminalRecord]
    · simp only [rowRecord,cachedRowRepair,if_neg h,recordAt,cachedRepairAt]
      split <;> ext x <;> simp [RepairRecord.decode,terminalRecord,or_left_comm,or_assoc,or_comm]

def rowRecords (order : List (Ground n)) (cache : PathCache n) (i : Option (Ground n)) :
    List (RepairRecord n) :=
  let sw := sweep (order.map (I.rowThreshold i)) (List.ofFn cache.costs) 0
  (order.zip sw.answers).map (fun p => rowRecord cache i p.1 p.2)

theorem rowRecords_decode (order : List (Ground n)) (cache : PathCache n)
    (i : Option (Ground n)) :
    (I.rowRecords order cache i).map (RepairRecord.decode cache)=
      (I.runRow order cache i).value := by
  simp only [rowRecords,runRow,List.map_map]
  apply List.map_congr_left
  intro p _
  exact rowRecord_decode _ _ _ _

theorem sweep_answer_length (qs xs : List ℝ) (offset : ℕ) :
    (sweep qs xs offset).answers.length=qs.length := by
  induction qs generalizing xs offset with
  | nil => rfl
  | cons q qs ih => simp only [sweep,List.length_cons,ih]

theorem rowRecords_length (order : List (Ground n)) (cache : PathCache n)
    (i : Option (Ground n)) : (I.rowRecords order cache i).length=order.length := by
  simp [rowRecords,sweep_answer_length]

theorem fold_max_values {α : Type*} (f : α → ℝ) (xs : List α) (b : ℝ) (hb : 0 ≤ b) :
    xs.foldl (fun z x => max z (f x)) b=max b (maxValues f xs).value := by
  induction xs generalizing b with
  | nil => simp [maxValues,max_eq_left hb]
  | cons x xs ih =>
    rw [List.foldl_cons,ih _ (hb.trans (le_max_left _ _))]
    simp only [maxValues,max_assoc]

theorem max_values_append {α : Type*} (f : α → ℝ) (xs ys : List α) :
    (maxValues f (xs++ys)).value=max (maxValues f xs).value (maxValues f ys).value := by
  induction xs with
  | nil => simp [maxValues,max_eq_right (maxValues_nonneg f ys)]
  | cons x xs ih => simp only [List.cons_append,maxValues,ih,max_assoc]

theorem max_values_map {α β : Type*} (f : β → ℝ) (g : α → β) (xs : List α) :
    (maxValues f (xs.map g)).value=(maxValues (fun x => f (g x)) xs).value := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [maxValues,ih]

/-- One row owns three arrays: thresholds, answers and three-word repair
records. The prefix-cost input and sweep slices are borrowed views. Sixteen
words hold loop indices, the maximum/record and temporary-edit undo data. -/
def spaceRow (order : List (Ground n)) (cache : PathCache n) (i : Option (Ground n))
    (best : ℝ) : Memory.Run ℝ :=
  let qs := order.map (I.rowThreshold i)
  let sw := sweep qs (List.ofFn cache.costs) 0
  let rs := I.rowRecords order cache i
  Memory.scope (qs.length+2) (Memory.scope (sw.answers.length+2)
    (Memory.scope (3*rs.length+2) (Memory.scope 16
      (Memory.pure (rs.foldl (fun z r => max z (I.value (r.decode cache))) best)))))

theorem spaceRow_value (order : List (Ground n)) (cache : PathCache n)
    (i : Option (Ground n)) (best : ℝ) (hb : 0 ≤ best) :
    (I.spaceRow order cache i best).value=
      max best (maxValues I.value (I.runRow order cache i).value).value := by
  simp only [spaceRow,Memory.scope,Memory.pure]
  rw [fold_max_values _ _ _ hb]
  rw [← I.rowRecords_decode, max_values_map]

theorem spaceRow_peak (order : List (Ground n)) (cache : PathCache n)
    (i : Option (Ground n)) (best : ℝ) :
    (I.spaceRow order cache i best).plan.peak=5*order.length+22 := by
  simp only [spaceRow,Memory.scope,Memory.pure,Memory.Plan.peak,
    List.length_map,sweep_answer_length,I.rowRecords_length]
  omega

def rowIndices : List (Option (Ground n)) := none::I.itemList.map some

theorem spaceRows_value (order : List (Ground n)) (cache : PathCache n)
    (is : List (Option (Ground n))) (best : ℝ) (hb : 0 ≤ best) :
    (Memory.fold (I.spaceRow order cache) is best).value =
      max best (maxValues I.value (is.flatMap (fun i => (I.runRow order cache i).value))).value := by
  induction is generalizing best with
  | nil => simp [Memory.fold,Memory.pure,maxValues,max_eq_left hb]
  | cons i is ih =>
    change (Memory.fold _ is (I.spaceRow order cache i best).value).value = _
    rw [I.spaceRow_value _ _ _ _ hb,ih _ (hb.trans (le_max_left _ _))]
    simp only [List.flatMap_cons,max_values_append,max_assoc]

/-- Three persistent arrays per seed, with two-word headers:
the (n+1) by n membership matrix, n+1 scalar prefix costs, n absences. -/
def cacheWords (n : ℕ) : ℕ := (n*(n+1)+2)+(n+1+2)+(n+2)

/-- Current membership array and scan/control registers during path
construction. The resulting snapshots live in the enclosing cache block. -/
def pathWorkspace (n : ℕ) : Memory.Plan := .hold (n+2) (.hold 20 .done)

def spaceSeed (order : List (Ground n)) (a : Ground n) : Memory.Run ℝ :=
  let cache := (I.reuseCache a).value
  Memory.scope (cacheWords n) (Memory.before (pathWorkspace n)
    (Memory.fold (I.spaceRow order cache) I.rowIndices
      (I.value (cache.states (Fin.last n)))))

theorem spaceSeed_value (a : Ground n) :
    (I.spaceSeed I.costSorted a).value=(I.reuseSeed I.costSorted a).value := by
  have hn := I.value_nonneg ((I.reuseCache a).value.states (Fin.last n))
  simp only [spaceSeed,Memory.scope,Memory.before]
  rw [I.spaceRows_value _ _ _ _ hn]
  simp only [reuseSeed,maxValues,rowIndices,List.flatMap_cons,List.flatMap_map]

theorem spaceSeed_peak (a : Ground n) :
    (I.spaceSeed I.costSorted a).plan.peak ≤ n^2+8*n+29 := by
  have hr := Memory.fold_peak (I.spaceRow I.costSorted (I.reuseCache a).value)
    I.rowIndices (I.value ((I.reuseCache a).value.states (Fin.last n))) (5*n+22)
    (fun i _ z => by rw [I.spaceRow_peak,I.costSorted_length])
  simp only [spaceSeed,Memory.scope,Memory.before,Memory.Plan.peak]
  have hp : (pathWorkspace n).peak=n+22 := by simp [pathWorkspace,Memory.Plan.peak]
  rw [hp]
  have hm : max (n+22)
      (Memory.fold (I.spaceRow I.costSorted (I.reuseCache a).value) I.rowIndices
        (I.value ((I.reuseCache a).value.states (Fin.last n)))).plan.peak ≤ 5*n+22 :=
    max_le (by omega) hr
  unfold cacheWords
  nlinarith only [hm]

/-- A temporary sort array plus linear insertion-sort control storage.
The caller separately accounts for the permanent sorted-order array. -/
def sortWorkspace (n : ℕ) : Memory.Plan := .hold (n+2) (.hold (2*(n+1)) .done)

end
end S2R.Instance
