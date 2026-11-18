import S2R.OwnedOutput

namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

/-- Conservative reuse of the previous per-item blocks: 12 threshold,
32 candidate/edit, 2 value-flag/read and 4 best-record operations; each
sweep tick costs 6. Fusion does not lower any unit charges here. -/
def streamRowOperations (i : Option (Ground n)) : List (Ground n) → List ℝ → ℕ
  | [], _ => 6
  | j::js, costs =>
    let z := consume (I.rowThreshold i j) costs
    streamRowOperations i js z.rest+50+6*z.ticks+18

theorem streamRowOperations_exact (i : Option (Ground n)) (order : List (Ground n))
    (costs : List ℝ) (offset : ℕ) :
    I.streamRowOperations i order costs=
      50*order.length+6*(sweep (order.map (I.rowThreshold i)) costs offset).ticks+6 := by
  induction order generalizing costs offset with
  | nil => simp [streamRowOperations,sweep]
  | cons j js ih =>
    simp only [streamRowOperations,List.length_cons,List.map_cons,sweep]
    rw [ih _ (offset+(consume (I.rowThreshold i j) costs).taken.length)]
    ring

def streamJobOperations (a : Ground n) (job : Option (Ground n) × List (Ground n)) : ℕ :=
  I.streamRowOperations job.1 job.2 (List.ofFn (I.reuseCache a).value.costs)

theorem streamJobOperations_refines (a : Ground n) (job : Option (Ground n) × List (Ground n)) :
    I.streamJobOperations a job=I.thinRowOperations a job := by
  rw [streamJobOperations,I.streamRowOperations_exact _ _ _ 0]
  unfold thinRowOperations runRow
  simp only [I.rowRecords_length,List.length_map,List.length_zip,sweep_answer_length,List.length_map,Nat.min_self]
  ring

def streamRepairQueries (a : Ground n) : ℕ :=
  ((I.liveRecords a).filter (fun r => r.first.isSome)).length

theorem streamRepairQueries_refines (a : Ground n) :
    I.streamRepairQueries a=I.thinRepairQueries a := by
  rw [streamRepairQueries,I.liveRecords_eq,List.filter_flatMap,List.length_flatMap]
  rfl

def streamQueryCount : ℕ := by
  classical
  exact ∑ a : Ground n, if I.Feasible {a} then
    (∑ k : Fin n, (I.stepQueries (I.iterate {a} k.val)).card)+I.streamRepairQueries a else 0

theorem streamQueryCount_refines : I.streamQueryCount=I.thinQueryCount := by
  classical
  simp only [streamQueryCount,thinQueryCount,thinSeedQueries,I.streamRepairQueries_refines]

def optionalWriteOperations : Option (Ground n) → ℕ
  | none => 1
  | some _ => 2

/-- Copy n prefix bits into the existing output buffer, then perform at
most two optional writes. No output allocation or history replay occurs. -/
def materializeOperations (r : RepairRecord n) : ℕ :=
  2*n+2+optionalWriteOperations r.first+optionalWriteOperations r.second

theorem materializeOperations_bound (r : RepairRecord n) : materializeOperations r ≤ 2*n+6 := by
  rcases r with ⟨_,i,j⟩
  cases i <;> cases j <;> simp [materializeOperations,optionalWriteOperations]

def streamSeedOperations (a : Ground n) : ℕ :=
  (I.reuseCache a).operations+(6*n+1)+2+
    ((I.liveRepairJobs a).map (I.streamJobOperations a)).sum+5+20

theorem streamSeedOperations_bound (a : Ground n) :
    I.streamSeedOperations a+10*n ≤ 75*n^2+12 := by
  have hs := sum_jobs_linear (I.streamJobOperations a) (fun j => j.2.length)
    (I.liveRepairJobs a) 74 (12*n+18) (fun j _ => by
      rw [I.streamJobOperations_refines]; exact I.thinRowOperations_bound a j)
  have hl := I.liveRepairJobs_length a
  have hw := I.liveRepairJobs_weight a
  unfold streamSeedOperations
  rw [I.reuseCache_operations_polynomial]
  nlinarith only [hs,hl,hw]

/-- Copy once at most per feasible seed. The cost is included even if
that seed does not improve the global incumbent, making this conservative. -/
def ownedTimeImplementation : RAM.Run ℝ := by
  classical
  exact ⟨I.ownedImplementation.value.2,
    20*(n+1)+4*sortTicks I.costOrder I.itemList+
      (∑ a : Ground n, if I.Feasible {a} then
        I.streamSeedOperations a+materializeOperations (I.streamBest a).1+4 else 4)⟩

theorem ownedTimeImplementation_polynomial :
    I.ownedTimeImplementation.operations+4*n^2 ≤ 75*n^3+46*n+24 := by
  classical
  have ht := sortTicks_quadratic I.costOrder I.itemList
  have hl : I.itemList.length=n := by simp [itemList]
  rw [hl] at ht
  have hs : (∑ a : Ground n, ((if I.Feasible {a} then
      I.streamSeedOperations a+materializeOperations (I.streamBest a).1+4 else 4)+8*n)) ≤
      n*(75*n^2+22) := by
    calc
      _ ≤ ∑ _a : Ground n, (75*n^2+22) := by
        apply Finset.sum_le_sum
        intro a _
        split
        · have h := I.streamSeedOperations_bound a
          have hc := materializeOperations_bound (I.streamBest a).1
          omega
        · have hn : 1 ≤ n := by have ha := a.isLt; omega
          nlinarith only [hn]
      _ = _ := by simp
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  change (20*(n+1)+4*sortTicks I.costOrder I.itemList+_)+4*n^2 ≤ _
  nlinarith only [hs,ht]

theorem ownedTimeImplementation_cubic (hn : 1 ≤ n) :
    I.ownedTimeImplementation.operations ≤ 141*n^3 := by
  have h := I.ownedTimeImplementation_polynomial
  have h₂ : n ≤ n*n := by nlinarith only [hn]
  have h₃ : n*n ≤ n^3 := by
    have hm := Nat.mul_le_mul_left n h₂
    nlinarith only [hm]
  by_cases he : n=1
  · subst n; norm_num at h ⊢; omega
  · have hn₂ : 2 ≤ n := by omega
    have h₄ : 2*n ≤ n*n := by nlinarith only [hn₂]
    have h₅ : 2*n*n ≤ n^3 := by
      have hm := Nat.mul_le_mul_left n h₄
      nlinarith only [hm]
    nlinarith only [h,hn₂,h₂,h₃,h₄,h₅]

theorem ownedImplementation_space_quadratic (hn : 1 ≤ n) :
    I.ownedImplementation.plan.peak ≤ 66*n^2 := by
  have h := I.ownedImplementation_space_polynomial
  have h₂ : n ≤ n*n := by nlinarith only [hn]
  nlinarith only [h,hn,h₂]

theorem s2r_verified_streaming (hn : 1 ≤ n) :
    I.Feasible I.ownedImplementation.value.1 ∧
    I.value I.ownedImplementation.value.1=I.output ∧
    (1-Real.exp (-1))*I.optimum ≤ I.ownedTimeImplementation.value ∧
    I.streamQueryCount ≤ n^3 ∧
    I.ownedTimeImplementation.operations ≤ 141*n^3 ∧
    I.ownedImplementation.plan.peak ≤ 66*n^2 := by
  refine ⟨I.ownedImplementation_feasible.1,?_,?_,?_,I.ownedTimeImplementation_cubic hn,
    I.ownedImplementation_space_quadratic hn⟩
  · rw [← I.ownedImplementation_feasible.2]; exact I.ownedImplementation_correct
  · change (1-Real.exp (-1))*I.optimum ≤ I.ownedImplementation.value.2
    rw [I.ownedImplementation_correct]; exact I.approximation_guarantee
  · rw [I.streamQueryCount_refines]; exact I.thinQueryCount_cubic

end
end S2R.Instance
