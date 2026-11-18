import S2R.StreamingRows

/-! Commit a seed winner into one owned output buffer before releasing
that seed's cache. No table of all seeds' path histories is retained. -/
namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)
attribute [local instance] Classical.propDecidable

def setOptional (bits : Ground n → Bool) : Option (Ground n) → Ground n → Bool
  | none => bits
  | some i => Function.update bits i true

theorem setOptional_spec (bits : Ground n → Bool) (o : Option (Ground n)) (x : Ground n) :
    setOptional bits o x=true ↔ bits x=true ∨ x ∈ o.toList := by
  cases o with
  | none => simp [setOptional]
  | some i =>
    by_cases h : i=x
    · subst x; simp [setOptional]
    · simp [setOptional,Function.update,h,Ne.symm h]

def materializeRecord (cache : PathCache n) (r : RepairRecord n) : Selection n := by
  classical
  exact Finset.univ.filter (fun i =>
    setOptional (setOptional (snapshotBits cache r.cutoff) r.first) r.second i)

theorem materializeRecord_correct (cache : PathCache n) (r : RepairRecord n) :
    materializeRecord cache r=r.decode cache := by
  classical
  ext x
  simp [materializeRecord,setOptional_spec,snapshotBits,RepairRecord.decode,or_assoc]

/-- Four words for the best record/value, plus the cached terminal value,
live across rows. The sixteen row registers contain cursors, threshold,
current record and temporary membership-edit undo data. -/
def streamRowMemory (a : Ground n) (job : Option (Ground n) × List (Ground n))
    (b : RepairRecord n × ℝ) : Memory.Run (RepairRecord n × ℝ) :=
  Memory.scope 16 (Memory.pure (I.streamJob (I.reuseCache a).value (I.savedTerminal a) job b))

def commitSeed (a : Ground n) (old : Selection n × ℝ)
    (winner : RepairRecord n × ℝ) : Selection n × ℝ :=
  if old.2 < winner.2 then (materializeRecord (I.reuseCache a).value winner.1,winner.2) else old

theorem commitSeed_value (a : Ground n) (old : Selection n × ℝ)
    (winner : RepairRecord n × ℝ) : (I.commitSeed a old winner).2=max old.2 winner.2 := by
  unfold commitSeed
  split
  · rename_i h; exact (max_eq_right (le_of_lt h)).symm
  · rename_i h; exact (max_eq_left (le_of_not_gt h)).symm

def ownedSeed (a : Ground n) (old : Selection n × ℝ) : Memory.Run (Selection n × ℝ) :=
  let rows := Memory.fold (I.streamRowMemory a) (I.liveRepairJobs a) (terminalRecord,I.savedTerminal a)
  Memory.scope (cacheWords n) (Memory.before (pathWorkspace n)
    (Memory.scope ((I.repairOrder a).length+2) (Memory.scope 5
      (⟨I.commitSeed a old rows.value,rows.plan⟩ : Memory.Run (Selection n × ℝ)))))

theorem ownedSeed_result (a : Ground n) (old : Selection n × ℝ) :
    (I.ownedSeed a old).value=I.commitSeed a old (I.streamBest a) := by
  simp only [ownedSeed,Memory.scope,Memory.before,Memory.fold_value,streamRowMemory,Memory.pure]
  rfl

theorem ownedSeed_value (a : Ground n) (old : Selection n × ℝ) :
    (I.ownedSeed a old).value.2=max old.2 (I.thinSeed a).value := by
  rw [I.ownedSeed_result,I.commitSeed_value,I.streamBest_value]

theorem ownedSeed_valid (a : Ground n) (ha : I.Feasible {a}) (old : Selection n × ℝ)
    (ho : I.Feasible old.1 ∧ old.2=I.value old.1) :
    I.Feasible (I.ownedSeed a old).value.1 ∧
      (I.ownedSeed a old).value.2=I.value (I.ownedSeed a old).value.1 := by
  rw [I.ownedSeed_result]
  unfold commitSeed
  split
  · simp only [materializeRecord_correct]
    have h := I.streamBest_spec a
    have hm : (I.streamBest a).1.decode (I.reuseCache a).value ∈ I.compressedPath a := by
      rw [← I.thinPath_correct a ha]
      exact List.mem_toFinset.mpr h.1
    exact ⟨((I.mem_pathCandidates_iff _ _).mp (I.compressed_subset_path ha hm)).1,h.2⟩
  · exact ho

def ownedVisit (a : Ground n) (old : Selection n × ℝ) : Memory.Run (Selection n × ℝ) := by
  classical
  exact if I.Feasible {a} then I.ownedSeed a old else Memory.pure old

def ownedSharedWords (n : ℕ) : ℕ := 4*(n+2)+20

def ownedImplementation : Memory.Run (Selection n × ℝ) :=
  Memory.scope (ownedSharedWords n) (Memory.before (sortWorkspace n)
    (Memory.fold I.ownedVisit I.itemList (∅,0)))

theorem ownedFold_value (as : List (Ground n)) (old : Selection n × ℝ) (ho : 0 ≤ old.2) :
    (Memory.fold I.ownedVisit as old).value.2=
      max old.2 (maxValues (fun a => if I.Feasible {a} then (I.thinSeed a).value else 0) as).value := by
  classical
  induction as generalizing old with
  | nil => simp [Memory.fold,Memory.pure,maxValues,max_eq_left ho]
  | cons a as ih =>
    change (Memory.fold I.ownedVisit as (I.ownedVisit a old).value).value.2=_
    by_cases ha : I.Feasible {a}
    · have hv : (I.ownedVisit a old).value.2=max old.2 (I.thinSeed a).value := by
        simp only [ownedVisit,if_pos ha,I.ownedSeed_value]
      rw [ih _ (by rw [hv]; exact ho.trans (le_max_left _ _)),hv]
      simp only [maxValues,if_pos ha,max_assoc]
    · simp only [ownedVisit,if_neg ha,Memory.pure]
      rw [ih _ ho]
      simp only [maxValues,if_neg ha]
      rw [max_eq_right (maxValues_nonneg _ _)]

theorem ownedImplementation_correct : I.ownedImplementation.value.2=I.output := by
  classical
  have h := I.ownedFold_value I.itemList (∅,0) le_rfl
  simp only [ownedImplementation,Memory.scope,Memory.before]
  rw [h,max_eq_right (maxValues_nonneg _ _)]
  rw [← I.reuseImplementationRun_correct]
  unfold reuseImplementationRun
  apply max_values_congr
  intro a _
  split
  · rename_i ha
    simpa [ha] using I.thinSeed_value a ha
  · rename_i ha
    simp [ha]

theorem ownedFold_valid (as : List (Ground n)) (old : Selection n × ℝ)
    (ho : I.Feasible old.1 ∧ old.2=I.value old.1) :
    I.Feasible (Memory.fold I.ownedVisit as old).value.1 ∧
      (Memory.fold I.ownedVisit as old).value.2=I.value (Memory.fold I.ownedVisit as old).value.1 := by
  classical
  induction as generalizing old with
  | nil => exact ho
  | cons a as ih =>
    apply ih
    unfold ownedVisit
    split
    · rename_i ha; exact I.ownedSeed_valid a ha old ho
    · exact ho

theorem ownedImplementation_feasible : I.Feasible I.ownedImplementation.value.1 ∧
    I.ownedImplementation.value.2=I.value I.ownedImplementation.value.1 :=
  I.ownedFold_valid I.itemList (∅,0) ⟨I.feasible_empty,I.normalized.symm⟩

theorem ownedSeed_peak (a : Ground n) (old : Selection n × ℝ) :
    (I.ownedSeed a old).plan.peak ≤ n^2+4*n+29 := by
  have hf := Memory.fold_peak (I.streamRowMemory a) (I.liveRepairJobs a)
    (terminalRecord,I.savedTerminal a) 16 (fun _ _ _ => by rfl)
  have hl := I.repairOrder_length a
  have hp : (pathWorkspace n).peak=n+22 := by simp [pathWorkspace,Memory.Plan.peak]
  simp only [ownedSeed,Memory.scope,Memory.before,Memory.Plan.peak,hp]
  have hm : max (n+22) ((I.repairOrder a).length+2+(5+
      (Memory.fold (I.streamRowMemory a) (I.liveRepairJobs a) (terminalRecord,I.savedTerminal a)).plan.peak)) ≤ n+22 := by omega
  unfold cacheWords
  nlinarith only [hm]

theorem ownedImplementation_space_polynomial :
    I.ownedImplementation.plan.peak ≤ n^2+8*n+57 := by
  classical
  have hv (a : Ground n) (b : Selection n × ℝ) : (I.ownedVisit a b).plan.peak ≤ n^2+4*n+29 := by
    unfold ownedVisit
    split
    · exact I.ownedSeed_peak a b
    · exact Nat.zero_le _
  have hf := Memory.fold_peak I.ownedVisit I.itemList (∅,0) (n^2+4*n+29) (fun a _ b => hv a b)
  have hs : (sortWorkspace n).peak=3*n+4 := by simp [sortWorkspace,Memory.Plan.peak]; omega
  change ownedSharedWords n+max (sortWorkspace n).peak _ ≤ _
  rw [hs]
  have hm : max (3*n+4) (Memory.fold I.ownedVisit I.itemList (∅,0)).plan.peak ≤ n^2+4*n+29 :=
    max_le (by omega) hf
  unfold ownedSharedWords
  nlinarith only [hm]

theorem owned_all_allocation_prefixes (k : ℕ) :
    ∃ used, Memory.execute (I.ownedImplementation.plan.events.take k) 0=some used ∧
      used ≤ n^2+8*n+57 := by
  obtain ⟨used,hu,_,hb⟩ := Memory.execute_prefix_bound I.ownedImplementation.plan 0 k
  have hp := I.ownedImplementation_space_polynomial
  exact ⟨used,hu,by omega⟩

theorem ownedImplementation_releases :
    Memory.execute I.ownedImplementation.plan.events 0=some 0 := Memory.execute_balanced _ _

end
end S2R.Instance
