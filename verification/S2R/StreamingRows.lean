import S2R.ThinComplexity

/-! Loop fusion: thresholds, answers and repair records are consumed in
registers. Lists below denote traces, not allocated intermediate arrays. -/
namespace S2R.TailJobs
variable {α β : Type*}

def nonemptyRows (xs : List (Option α × List α)) :=
  xs.filter (fun j => !j.2.isEmpty)

def liveJobs (xs : List α) := nonemptyRows (jobs xs)

theorem nonemptyRows_pairs_length (xs : List α) :
    (nonemptyRows (pairs xs)).length=xs.length-1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simp [nonemptyRows,pairs] at ih ⊢; omega

theorem liveJobs_length (xs : List α) : (liveJobs xs).length=xs.length := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    have h := nonemptyRows_pairs_length (x::xs)
    change (nonemptyRows (pairs (x::xs))).length+1=(x::xs).length
    simp only [List.length_cons] at h ⊢
    omega

theorem nonemptyRows_flatMap (xs : List (Option α × List α))
    (f : (Option α × List α) → List β) (h : ∀ i, f (i,[])=[]) :
    (nonemptyRows xs).flatMap f=xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    rcases j with ⟨i,js⟩
    cases js <;> simp [nonemptyRows,h,ih,nonemptyRows] at *

theorem nonemptyRows_weight (xs : List (Option α × List α)) :
    ((nonemptyRows xs).map (fun j => j.2.length)).sum=(xs.map (fun j => j.2.length)).sum := by
  induction xs with
  | nil => rfl
  | cons j xs ih =>
    rcases j with ⟨i,js⟩
    cases js <;> simp [nonemptyRows,ih,nonemptyRows] at *

end S2R.TailJobs

namespace S2R.ArgMax
noncomputable section
variable {α : Type*}

def offer (f : α → ℝ) (b : α × ℝ) (x : α) : α × ℝ :=
  let v := f x
  if b.2 < v then (x,v) else b

theorem offer_value (f : α → ℝ) (b : α × ℝ) (x : α) :
    (offer f b x).2=max b.2 (f x) := by
  unfold offer
  dsimp only
  split
  · rename_i h; exact (max_eq_right (le_of_lt h)).symm
  · rename_i h; exact (max_eq_left (le_of_not_gt h)).symm

theorem fold_value (f : α → ℝ) (xs : List α) (b : α × ℝ) (hb : 0 ≤ b.2) :
    (xs.foldl (offer f) b).2=max b.2 (RAM.maxValues f xs).value := by
  induction xs generalizing b with
  | nil => simp [RAM.maxValues,max_eq_left hb]
  | cons x xs ih =>
    rw [List.foldl_cons,ih _ (by rw [offer_value]; exact hb.trans (le_max_left _ _)),offer_value]
    simp only [RAM.maxValues,max_assoc]

theorem fold_spec (f : α → ℝ) (P : α → Prop) (xs : List α) (b : α × ℝ)
    (hb : P b.1 ∧ b.2=f b.1) (hx : ∀ x ∈ xs, P x) :
    P (xs.foldl (offer f) b).1 ∧ (xs.foldl (offer f) b).2=f (xs.foldl (offer f) b).1 := by
  induction xs generalizing b with
  | nil => exact hb
  | cons x xs ih =>
    apply ih
    · unfold offer
      dsimp only
      split
      · exact ⟨hx x List.mem_cons_self,rfl⟩
      · exact hb
    · exact fun y hy => hx y (List.mem_cons_of_mem x hy)

end
end S2R.ArgMax

namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

def liveRepairJobs (a : Ground n) := TailJobs.liveJobs (I.repairOrder a)

theorem liveRepairJobs_length (a : Ground n) : (I.liveRepairJobs a).length+1=n := by
  rw [liveRepairJobs,TailJobs.liveJobs_length,I.repairOrder_length]

theorem liveRepairJobs_weight (a : Ground n) :
    2*((I.liveRepairJobs a).map (fun j => j.2.length)).sum+n=n*n := by
  rw [liveRepairJobs,TailJobs.liveJobs,TailJobs.nonemptyRows_weight]
  exact I.repairJobs_weight a

theorem liveRepairJobs_mem (a : Ground n) {job : Option (Ground n) × List (Ground n)}
    (h : job ∈ I.liveRepairJobs a) : job ∈ I.repairJobs a := by
  change job ∈ (I.repairJobs a).filter (fun j => !j.2.isEmpty) at h
  exact (List.mem_filter.mp h).1

/-- A single running best record and value. A consume step advances a
borrowed cost-array cursor; no threshold/answer/record arrays are built. -/
def streamRow (cache : PathCache n) (terminalValue : ℝ) (i : Option (Ground n)) :
    List (Ground n) → List ℝ → ℕ → (RepairRecord n × ℝ) → (RepairRecord n × ℝ)
  | [], _, _, b => b
  | j::js, costs, offset, b =>
    let z := consume (I.rowThreshold i j) costs
    let k := offset+z.taken.length
    let r := rowRecord cache i j k
    streamRow cache terminalValue i js z.rest k
      (ArgMax.offer (I.cachedRecordValue cache terminalValue) b r)

theorem streamRow_fold (cache : PathCache n) (terminalValue : ℝ) (i : Option (Ground n))
    (order : List (Ground n)) (costs : List ℝ) (offset : ℕ) (b : RepairRecord n × ℝ) :
    I.streamRow cache terminalValue i order costs offset b=
      ((order.zip (sweep (order.map (I.rowThreshold i)) costs offset).answers).map
        (fun p => rowRecord cache i p.1 p.2)).foldl
        (ArgMax.offer (I.cachedRecordValue cache terminalValue)) b := by
  induction order generalizing costs offset b with
  | nil => rfl
  | cons j js ih =>
    simpa only [streamRow,List.map_cons,sweep,List.zip_cons_cons,List.foldl_cons] using
      (ih (consume (I.rowThreshold i j) costs).rest
        (offset+(consume (I.rowThreshold i j) costs).taken.length)
        (ArgMax.offer (I.cachedRecordValue cache terminalValue) b
          (rowRecord cache i j (offset+(consume (I.rowThreshold i j) costs).taken.length))))

def streamJob (cache : PathCache n) (terminalValue : ℝ)
    (job : Option (Ground n) × List (Ground n)) (b : RepairRecord n × ℝ) :=
  I.streamRow cache terminalValue job.1 job.2 (List.ofFn cache.costs) 0 b

theorem streamJob_fold (cache : PathCache n) (terminalValue : ℝ)
    (job : Option (Ground n) × List (Ground n)) (b : RepairRecord n × ℝ) :
    I.streamJob cache terminalValue job b=(I.rowRecords job.2 cache job.1).foldl
      (ArgMax.offer (I.cachedRecordValue cache terminalValue)) b := I.streamRow_fold _ _ _ _ _ _ _

theorem streamJobs_fold (cache : PathCache n) (terminalValue : ℝ)
    (jobs : List (Option (Ground n) × List (Ground n))) (b : RepairRecord n × ℝ) :
    jobs.foldl (fun z j => I.streamJob cache terminalValue j z) b=
      (jobs.flatMap (fun j => I.rowRecords j.2 cache j.1)).foldl
        (ArgMax.offer (I.cachedRecordValue cache terminalValue)) b := by
  induction jobs generalizing b with
  | nil => rfl
  | cons j jobs ih => rw [List.foldl_cons,ih,I.streamJob_fold,List.flatMap_cons,List.foldl_append]

def liveRecords (a : Ground n) : List (RepairRecord n) :=
  (I.liveRepairJobs a).flatMap (fun j => I.rowRecords j.2 (I.reuseCache a).value j.1)

theorem liveRecords_eq (a : Ground n) :
    I.liveRecords a=(I.repairJobs a).flatMap (fun j => I.rowRecords j.2 (I.reuseCache a).value j.1) := by
  apply TailJobs.nonemptyRows_flatMap
  intro i
  rfl

def streamBest (a : Ground n) : RepairRecord n × ℝ :=
  (I.liveRepairJobs a).foldl
    (fun z j => I.streamJob (I.reuseCache a).value (I.savedTerminal a) j z)
    (terminalRecord,I.savedTerminal a)

theorem streamBest_fold (a : Ground n) : I.streamBest a=
    (I.liveRecords a).foldl (ArgMax.offer (I.cachedRecordValue (I.reuseCache a).value (I.savedTerminal a)))
      (terminalRecord,I.savedTerminal a) := I.streamJobs_fold _ _ _ _

theorem liveRecords_decode (a : Ground n) :
    (I.liveRecords a).map (RepairRecord.decode (I.reuseCache a).value)=
      (I.repairJobs a).flatMap (fun j => (I.runRow j.2 (I.reuseCache a).value j.1).value) := by
  rw [I.liveRecords_eq,List.map_flatMap]
  apply List.flatMap_congr
  intro j _
  exact I.rowRecords_decode _ _ _

theorem liveRecord_value (a : Ground n) {r : RepairRecord n} (hr : r ∈ I.liveRecords a) :
    I.cachedRecordValue (I.reuseCache a).value (I.savedTerminal a) r=
      I.value (r.decode (I.reuseCache a).value) := by
  obtain ⟨job,_,hr⟩ := List.mem_flatMap.mp hr
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
  rw [I.savedTerminal_correct]
  exact I.cachedRecordValue_correct _ _ _ _

theorem streamBest_value (a : Ground n) : (I.streamBest a).2=(I.thinSeed a).value := by
  rw [I.streamBest_fold,ArgMax.fold_value _ _ _ (I.value_nonneg _),I.thinSeed_path_value]
  have he := max_values_congr
    (I.cachedRecordValue (I.reuseCache a).value (I.savedTerminal a))
    (fun r => I.value (r.decode (I.reuseCache a).value)) (I.liveRecords a)
    (fun r hr => I.liveRecord_value a hr)
  rw [he,← max_values_map,I.liveRecords_decode]
  simp only [thinPath,maxValues,savedTerminal,I.terminal_from_last_greedy]

theorem streamBest_spec (a : Ground n) :
    (I.streamBest a).1.decode (I.reuseCache a).value ∈ I.thinPath a ∧
      (I.streamBest a).2=I.value ((I.streamBest a).1.decode (I.reuseCache a).value) := by
  let P := fun r : RepairRecord n => r=terminalRecord ∨ r ∈ I.liveRecords a
  have h := ArgMax.fold_spec
    (I.cachedRecordValue (I.reuseCache a).value (I.savedTerminal a)) P (I.liveRecords a)
    (terminalRecord,I.savedTerminal a)
    ⟨Or.inl rfl,by simp [cachedRecordValue,terminalRecord]⟩ (fun r hr => Or.inr hr)
  rw [← I.streamBest_fold] at h
  have hc : I.cachedRecordValue (I.reuseCache a).value (I.savedTerminal a) (I.streamBest a).1=
      I.value ((I.streamBest a).1.decode (I.reuseCache a).value) := by
    rcases h.1 with he | he
    · rw [he,I.savedTerminal_correct]
      simp [cachedRecordValue,terminalRecord,RepairRecord.decode]
    · exact I.liveRecord_value a he
  refine ⟨?_,h.2.trans hc⟩
  rcases h.1 with he | he
  · rw [he,I.reuseCache_correct]
    simp [RepairRecord.decode,terminalRecord,referenceCache,thinPath]
  · have hm : (I.streamBest a).1.decode (I.reuseCache a).value ∈
        (I.liveRecords a).map (RepairRecord.decode (I.reuseCache a).value) :=
      List.mem_map.mpr ⟨(I.streamBest a).1,he,rfl⟩
    rw [I.liveRecords_decode] at hm
    exact List.mem_cons_of_mem _ hm

end
end S2R.Instance
