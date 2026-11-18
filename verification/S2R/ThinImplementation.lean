import S2R.TailJobs

/-! Sequential suffix jobs, with terminal-value reuse. The terminal scalar
comes from the final charged greedy batch, as proved in TailJobs. -/
namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

def savedTerminal (a : Ground n) : ℝ := I.value (I.iterate {a} (n-1))

theorem savedTerminal_correct (a : Ground n) :
    I.savedTerminal a=I.value ((I.reuseCache a).value.states (Fin.last n)) := by
  rw [I.reuseCache_correct]
  exact congrArg I.value (I.terminal_from_last_greedy a).symm

def cachedRecordValue (cache : PathCache n) (terminalValue : ℝ) (r : RepairRecord n) : ℝ :=
  if r.first.isSome then I.value (r.decode cache) else terminalValue

theorem cachedRecordValue_correct (cache : PathCache n) (i : Option (Ground n))
    (j : Ground n) (k : ℕ) :
    I.cachedRecordValue cache (I.value (cache.states (Fin.last n))) (rowRecord cache i j k)=
      I.value ((rowRecord cache i j k).decode cache) := by
  cases i with
  | none =>
    simp only [rowRecord,recordAt]
    split <;> simp [cachedRecordValue,terminalRecord,RepairRecord.decode]
  | some l =>
    by_cases h : l=j
    · simp [rowRecord,h,cachedRecordValue,terminalRecord,RepairRecord.decode]
    · simp only [rowRecord,if_neg h,recordAt]
      split <;> simp [cachedRecordValue,terminalRecord,RepairRecord.decode]

theorem max_values_congr {α : Type*} (f g : α → ℝ) (xs : List α)
    (h : ∀ x ∈ xs, f x=g x) : (maxValues f xs).value=(maxValues g xs).value := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [maxValues,h x List.mem_cons_self,ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem cachedRecords_values (order : List (Ground n)) (cache : PathCache n)
    (i : Option (Ground n)) :
    (maxValues (I.cachedRecordValue cache (I.value (cache.states (Fin.last n))))
      (I.rowRecords order cache i)).value=
      (maxValues I.value (I.runRow order cache i).value).value := by
  rw [← I.rowRecords_decode,max_values_map]
  apply max_values_congr
  intro r hr
  obtain ⟨p,_,rfl⟩ := List.mem_map.mp hr
  exact I.cachedRecordValue_correct cache i p.1 p.2

/-- Answers remain live across the sweep/record boundary. Thresholds are
released before records are allocated. Suffixes are borrowed cursor views. -/
def thinRow (cache : PathCache n) (terminalValue : ℝ)
    (job : Option (Ground n) × List (Ground n)) (best : ℝ) : Memory.Run ℝ :=
  let qs := job.2.map (I.rowThreshold job.1)
  let sw := sweep qs (List.ofFn cache.costs) 0
  let rs := I.rowRecords job.2 cache job.1
  Memory.scope 16 (Memory.scope (sw.answers.length+2)
    (Memory.before (.hold (qs.length+2) .done)
      (Memory.scope (3*rs.length+2)
        (Memory.pure (rs.foldl (fun z r => max z (I.cachedRecordValue cache terminalValue r)) best)))))

theorem thinRow_value (cache : PathCache n) (job : Option (Ground n) × List (Ground n))
    (best : ℝ) (hb : 0 ≤ best) :
    (I.thinRow cache (I.value (cache.states (Fin.last n))) job best).value=
      max best (maxValues I.value (I.runRow job.2 cache job.1).value).value := by
  simp only [thinRow,Memory.scope,Memory.before,Memory.pure]
  rw [fold_max_values _ _ _ hb,I.cachedRecords_values]

theorem thinRow_peak (cache : PathCache n) (terminalValue : ℝ)
    (job : Option (Ground n) × List (Ground n)) (best : ℝ) :
    (I.thinRow cache terminalValue job best).plan.peak=4*job.2.length+20 := by
  simp only [thinRow,Memory.scope,Memory.before,Memory.pure,Memory.Plan.peak,
    List.length_map,sweep_answer_length,I.rowRecords_length]
  omega

theorem thinRows_value (cache : PathCache n)
    (jobs : List (Option (Ground n) × List (Ground n))) (best : ℝ) (hb : 0 ≤ best) :
    (Memory.fold (I.thinRow cache (I.value (cache.states (Fin.last n)))) jobs best).value=
      max best (maxValues I.value (jobs.flatMap (fun j => (I.runRow j.2 cache j.1).value))).value := by
  induction jobs generalizing best with
  | nil => simp [Memory.fold,Memory.pure,maxValues,max_eq_left hb]
  | cons job jobs ih =>
    change (Memory.fold _ jobs (I.thinRow _ _ job best).value).value=_
    rw [I.thinRow_value _ _ _ hb,ih _ (hb.trans (le_max_left _ _))]
    simp only [List.flatMap_cons,max_values_append,max_assoc]

def thinSeed (a : Ground n) : Memory.Run ℝ :=
  Memory.scope (cacheWords n) (Memory.before (pathWorkspace n)
    (Memory.scope 1 (Memory.scope ((I.repairOrder a).length+2)
      (Memory.fold (I.thinRow (I.reuseCache a).value (I.savedTerminal a))
        (I.repairJobs a) (I.savedTerminal a)))))

theorem thinSeed_path_value (a : Ground n) :
    (I.thinSeed a).value=(maxValues I.value (I.thinPath a)).value := by
  simp only [thinSeed,Memory.scope,Memory.before,I.savedTerminal_correct]
  rw [I.thinRows_value _ _ _ (I.value_nonneg _)]
  simp only [thinPath,maxValues,I.reuseCache_correct,referenceCache]

theorem max_values_same_members {α : Type*} (f : α → ℝ) (xs ys : List α)
    (h : ∀ x, x ∈ xs ↔ x ∈ ys) : (maxValues f xs).value=(maxValues f ys).value := by
  apply le_antisymm
  · apply maxValues_le _ _ _ (maxValues_nonneg _ _)
    intro x hx
    exact maxValues_ge f ((h x).mp hx)
  · apply maxValues_le _ _ _ (maxValues_nonneg _ _)
    intro x hx
    exact maxValues_ge f ((h x).mpr hx)

theorem thinSeed_value (a : Ground n) (ha : I.Feasible {a}) :
    (I.thinSeed a).value=(I.reuseSeed I.costSorted a).value := by
  rw [I.thinSeed_path_value,I.reuseSeed_value,I.runSeed_correct]
  apply max_values_same_members
  intro S
  rw [← List.mem_toFinset,← List.mem_toFinset,I.thinPath_correct a ha,I.implementedPath_correct a ha]

end
end S2R.Instance
