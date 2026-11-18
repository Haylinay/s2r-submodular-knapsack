import S2R.CachedPath

/-! Data-flow refinement of the costed RAM implementation. Prefix snapshots,
their costs, and absence counts are explicitly cached before the row sweeps.
All later repairs read those tables. Lists describe the sequential records;
the finite functions in PathCache describe constant-time RAM arrays. -/
namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

structure PathCache (n : ℕ) where
  states : Fin (n+1) → Selection n
  costs : Fin (n+1) → ℝ
  absent : Ground n → ℕ

def referenceCache (a : Ground n) : PathCache n :=
  ⟨I.prefixSet a, fun t => I.totalCost (I.prefixSet a t), I.absenceCount a⟩

def makeCache (a : Ground n) : Run (PathCache n) := by
  classical
  let p := I.cachedPathRun {a} (I.cost a) n
  let states := fun t : Fin (n+1) => p.value.getD t.val ∅
  let costs := fun t => I.costRun (states t)
  let absent := fun i : Ground n => countTrue
    (List.ofFn (fun t : Fin (n+1) => decide (i ∉ states t)))
  exact ⟨⟨states,fun t => (costs t).value,fun i => (absent i).value⟩,
    p.operations+(∑ t, (costs t).operations)+(∑ i, (absent i).operations)⟩

theorem makeCache_correct (a : Ground n) : (I.makeCache a).value=I.referenceCache a := by
  classical
  have hs (t : Fin (n+1)) : (I.pathRun {a} n).value.getD t.val ∅=I.prefixSet a t := by
    rw [I.pathRun_correct]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos t.isLt,
      Option.getD_some]
    rfl
  unfold makeCache referenceCache
  rw [I.cachedSeedPath_refines]
  simp only [hs, I.costRun_correct, countTrue_correct, filter_ofFn_bool, absenceCount]
  rfl

theorem makeCache_operations (a : Ground n) : (I.makeCache a).operations=
    (I.pathRun {a} n).operations+
      (∑ i : Ground n, (I.absenceRun a i).operations)+
      (∑ t : Fin (n+1), (I.costRun (I.prefixSet a t)).operations) := by
  classical
  simp only [makeCache, I.cachedSeedPath_refines, I.costRun_operations, countTrue_operations,
    List.length_ofFn, I.absenceRun_operations]
  omega

def cachedRepairAt (cache : PathCache n) (R : Selection n) (k : ℕ) : Selection n :=
  if h : 0 < k ∧ k ≤ n+1 then cache.states ⟨k-1,by omega⟩ ∪ R
  else cache.states (Fin.last n)

def cachedRowRepair (cache : PathCache n) (i : Option (Ground n))
    (j : Ground n) (k : ℕ) : Selection n :=
  match i with
  | none => cachedRepairAt cache {j} (min (cache.absent j) k)
  | some l => if l=j then cache.states (Fin.last n) else
      cachedRepairAt cache {l,j} (min (cache.absent l) (min (cache.absent j) k))

theorem cachedRowRepair_reference (a : Ground n) (i : Option (Ground n)) (j : Ground n) (k : ℕ) :
    cachedRowRepair (I.referenceCache a) i j k=I.rowRepair a i j k := by
  cases i <;> rfl

def runRow (order : List (Ground n)) (cache : PathCache n) (i : Option (Ground n)) :
    Run (List (Selection n)) :=
  let qs := order.map (I.rowThreshold i)
  let sw := sweep qs (List.ofFn cache.costs) 0
  let records := (order.zip sw.answers).map (fun p => cachedRowRepair cache i p.1 p.2)
  ⟨records,12*order.length+6*sw.ticks+32*records.length+2⟩

theorem runRow_correct (a : Ground n) (i : Option (Ground n)) :
    (I.runRow I.costSorted (I.makeCache a).value i).value=I.rowCandidates a i := by
  rw [I.makeCache_correct]
  simp only [runRow, cachedRowRepair_reference, referenceCache]
  rfl

theorem runRow_operations (a : Ground n) (i : Option (Ground n)) :
    (I.runRow I.costSorted (I.makeCache a).value i).operations=I.rowOperationCount a i := by
  rw [I.makeCache_correct]
  unfold runRow
  have hv : ((I.costSorted.zip (I.rowSweep a i).answers).map
      (fun p => cachedRowRepair (I.referenceCache a) i p.1 p.2))=I.rowCandidates a i := by
    simp only [cachedRowRepair_reference, rowCandidates]
  change 12*I.costSorted.length+6*(I.rowSweep a i).ticks+
    32*((I.costSorted.zip (I.rowSweep a i).answers).map
      (fun p => cachedRowRepair (I.referenceCache a) i p.1 p.2)).length+2 = _
  rw [hv]
  rfl

def runSeed (order : List (Ground n)) (a : Ground n) : Run ℝ :=
  let cache := I.makeCache a
  let singles := I.runRow order cache.value none
  let rows := fun i : Ground n => I.runRow order cache.value (some i)
  let records := cache.value.states (Fin.last n)::
    (singles.value ++ I.itemList.flatMap (fun i => (rows i).value))
  let best := maxValues I.value records
  ⟨best.value,cache.operations+singles.operations+(∑ i, (rows i).operations)+best.operations+20⟩

theorem runSeed_correct (a : Ground n) :
    (I.runSeed I.costSorted a).value=(maxValues I.value (I.implementedPath a)).value := by
  unfold runSeed
  simp only [I.runRow_correct]
  rw [I.makeCache_correct]
  rfl

theorem runSeed_operations (a : Ground n) :
    (I.runSeed I.costSorted a).operations=I.seedOperationCount a := by
  unfold runSeed
  simp only [I.runRow_correct, I.runRow_operations, I.makeCache_operations]
  rw [I.makeCache_correct]
  rfl

/-- The input order is sorted once and passed to each seed. The global
maximum consumes the seed results; the four operations per seed in the
outer count include this comparison and best-record update. -/
def implementationRun : Run ℝ := by
  classical
  let order := I.costSorted
  let seeds := fun a : Ground n => if I.Feasible {a} then I.runSeed order a else ⟨0,0⟩
  exact ⟨(maxValues (fun a => (seeds a).value) I.itemList).value,
    20*(n+1)+4*sortTicks I.costOrder I.itemList+(∑ a : Ground n, ((seeds a).operations+4))⟩

theorem implementationRun_correct : I.implementationRun.value=I.output := by
  classical
  apply le_antisymm
  · apply maxValues_le _ _ _ I.output_nonneg
    intro a ha
    by_cases hf : I.Feasible {a}
    · simp only [if_pos hf, I.runSeed_correct]
      apply maxValues_le _ _ _ I.output_nonneg
      intro S hS
      have hm : S ∈ I.compressedPath a := by
        rw [← I.implementedPath_correct a hf]
        exact List.mem_toFinset.mpr hS
      exact I.output_spec.2 _ (I.compressed_subset_candidates
        (Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
          ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hf⟩,hm⟩)))
    · simp only [if_neg hf]
      exact I.output_nonneg
  · rw [← I.compressedOutput_eq]
    have hm := I.compressedOutput_spec.1
    rcases Finset.mem_insert.mp hm with he | hm
    · rw [he, I.normalized]
      exact maxValues_nonneg _ _
    · obtain ⟨a,ha,hS⟩ := Finset.mem_biUnion.mp hm
      have hf := (Finset.mem_filter.mp ha).2
      have hp : I.compressedOutputSet ∈ I.implementedPath a := by
        apply List.mem_toFinset.mp
        rw [I.implementedPath_correct a hf]
        exact hS
      have hs := maxValues_ge I.value hp
      have ho := maxValues_ge (fun a : Ground n =>
        (if I.Feasible {a} then I.runSeed I.costSorted a else (⟨0,0⟩ : Run ℝ)).value)
        (show a ∈ I.itemList by simp [itemList])
      simp only [if_pos hf, I.runSeed_correct] at ho
      exact hs.trans ho

theorem implementationRun_operations : I.implementationRun.operations=I.auxiliaryOperationCount := by
  classical
  unfold implementationRun auxiliaryOperationCount
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  split <;> simp [I.runSeed_operations]

/-- One and the same costed implementation returns the specified S2R output
and has a cubic count of auxiliary operations. -/
theorem implementation_verified (hn : 1 ≤ n) :
    I.implementationRun.value=I.output ∧ I.implementationRun.operations ≤ 700*n^3 := by
  exact ⟨I.implementationRun_correct, by rw [I.implementationRun_operations]; exact I.auxiliaryOperationCount_cubic hn⟩

end
end S2R.Instance
