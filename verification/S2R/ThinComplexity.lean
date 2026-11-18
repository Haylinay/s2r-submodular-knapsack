import S2R.ThinImplementation

namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

/-- Only nonterminal records call the oracle. Flag tests are charged
separately in thinRowOperations. -/
def thinRepairQueries (a : Ground n) : ℕ :=
  ((I.repairJobs a).map (fun job =>
    ((I.rowRecords job.2 (I.reuseCache a).value job.1).filter (fun r => r.first.isSome)).length)).sum

theorem thinRepairQueries_bound (a : Ground n) :
    I.thinRepairQueries a ≤ ((I.repairJobs a).map (fun j => j.2.length)).sum := by
  unfold thinRepairQueries
  apply List.sum_le_sum
  intro job _
  exact (List.length_filter_le _ _).trans (le_of_eq (I.rowRecords_length _ _ _))

def thinSeedQueries (a : Ground n) : ℕ :=
  (∑ k : Fin n, (I.stepQueries (I.iterate {a} k.val)).card)+I.thinRepairQueries a

theorem thinSeedQueries_bound (a : Ground n) : I.thinSeedQueries a ≤ n*n := by
  have hg := I.greedyQueryCount_triangular a
  have hr := I.thinRepairQueries_bound a
  have hw := I.repairJobs_weight a
  unfold thinSeedQueries
  nlinarith only [hg,hr,hw]

def thinQueryCount : ℕ := by
  classical
  exact ∑ a : Ground n, if I.Feasible {a} then I.thinSeedQueries a else 0

theorem thinQueryCount_cubic : I.thinQueryCount ≤ n^3 := by
  classical
  calc
    _ ≤ ∑ _a : Ground n, n*n := by
      apply Finset.sum_le_sum
      intro a _
      split
      · exact I.thinSeedQueries_bound a
      · exact Nat.zero_le _
    _ = _ := by simp; ring

/-- Existing row-construction charge, two flag/read operations and four
max/record operations per result, and four operations per job dispatch. -/
def thinRowOperations (a : Ground n) (job : Option (Ground n) × List (Ground n)) : ℕ :=
  (I.runRow job.2 (I.reuseCache a).value job.1).operations+
    6*(I.rowRecords job.2 (I.reuseCache a).value job.1).length+4

theorem thinRowOperations_bound (a : Ground n) (job : Option (Ground n) × List (Ground n)) :
    I.thinRowOperations a job ≤ 74*job.2.length+12*n+18 := by
  have ht := sweep_ticks (job.2.map (I.rowThreshold job.1))
    (List.ofFn (I.reuseCache a).value.costs) 0
  simp only [List.length_map,List.length_ofFn] at ht
  have hl : (I.runRow job.2 (I.reuseCache a).value job.1).value.length=job.2.length := by
    rw [← I.rowRecords_decode,List.length_map,I.rowRecords_length]
  unfold thinRowOperations
  rw [I.rowRecords_length]
  change 12*job.2.length+6*(sweep _ _ 0).ticks+
    32*(I.runRow job.2 (I.reuseCache a).value job.1).value.length+2+6*job.2.length+4 ≤ _
  rw [hl]
  omega

theorem sum_jobs_linear {α : Type*} (f w : α → ℕ) (xs : List α) (c d : ℕ)
    (h : ∀ x ∈ xs, f x ≤ c*w x+d) :
    (xs.map f).sum ≤ c*(xs.map w).sum+d*xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hx,ht]

theorem reuseCache_operations_polynomial (a : Ground n) :
    (I.reuseCache a).operations=26*n^2+15*n+2 := by
  rw [I.reuseCache_operations]
  simp only [I.pathRun_operations,I.absenceRun_operations,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

end
end S2R.Instance
