import S2R.DynamicCertificate
import S2R.Polygonal
import S2R.UnbalancedCost

namespace S2R.Instance
noncomputable section
open S2R.Analysis
variable {n : ℕ} {I : Instance n}

namespace CertificateData
theorem basic_growth (D : CertificateData I) : D.p+b ≤ I.valueAt D.seed 1 := by
  have h := I.density_integral_lower (a := D.seed) (lo := 0) (hi := 1) (c := b)
    (by norm_num) (by norm_num) D.terminal_crosses.le
    (fun k hk hd => D.density_lower hk.le (I.intervalDuration_pos_left (by norm_num) hd).le)
  rw [I.valueAt_zero] at h
  change b*(1-0) ≤ I.valueAt D.seed 1-D.p at h
  linarith
theorem seed_small (D : CertificateData I) : D.p < 1-2*b ∧ D.p < b := by
  have hg := D.basic_growth
  have hm := I.valueAt_le_output D.seed_feasible 1
  have hb := D.bad_output
  unfold alpha at hb
  constructor <;> linarith [b_bounds.1]

structure CostPair (D : CertificateData I) where
  big : Ground n
  small : Ground n
  big_mem : big ∈ D.items
  small_mem : small ∈ D.items
  distinct : big ≠ small
  repair_eq : D.repair = {big, small}
  ordered : I.cost small ≤ I.cost big
  largest : ∀ i ∈ D.items, I.cost i ≤ I.cost big
  second : ∀ i ∈ D.items, i ≠ big → I.cost i ≤ I.cost small

namespace CostPair
variable {D : CertificateData I} (E : CostPair D)
def mu : ℝ := I.cost E.big
def lam : ℝ := I.cost E.small
def s : ℝ := (E.mu+E.lam)/2
def u : ℝ := (E.mu-E.lam)/(E.mu+E.lam)
theorem mu_pos : 0 < E.mu := I.cost_pos _
theorem lam_pos : 0 < E.lam := I.cost_pos _
theorem lam_le_mu : E.lam ≤ E.mu := E.ordered
theorem repair_cost : I.totalCost D.repair = E.mu+E.lam := by
  rw [E.repair_eq, I.totalCost_insert]
  · simp [mu, lam]
  · simpa using E.distinct
include E in
theorem repair_card_two : D.repair.card = 2 := by
  classical
  simp [E.repair_eq, E.distinct]
theorem total_cost : I.totalCost D.items = 1+E.mu+E.lam := by
  have h := Finset.sum_sdiff D.repair_subset (f := I.cost)
  change I.totalCost (D.items \ D.repair)+I.totalCost D.repair = I.totalCost D.items at h
  rw [D.tail_cost', E.repair_cost] at h
  linarith
theorem budget_bound : I.cost D.seed+1+E.mu+E.lam ≤ I.budget := by
  have h := D.budget_bound
  rw [E.repair_cost] at h
  linarith
theorem without_big_cost : I.totalCost (D.items \ {E.big}) = 1+E.lam := by
  have h := Finset.sum_sdiff (Finset.singleton_subset_iff.mpr E.big_mem) (f := I.cost)
  change I.totalCost (D.items \ {E.big})+I.totalCost {E.big} = I.totalCost D.items at h
  rw [I.totalCost_singleton, E.total_cost] at h
  change I.totalCost (D.items \ {E.big})+E.mu = 1+E.mu+E.lam at h
  linarith
theorem without_pair_cost : I.totalCost ((D.items \ {E.small}) \ {E.big}) = 1 := by
  have he : (D.items \ {E.small}) \ {E.big} = D.items \ D.repair := by
    classical
    rw [E.repair_eq]
    ext i
    simp
    tauto
  rw [he, D.tail_cost']

theorem late_budget {k : ℕ} (hx : I.pathCost D.seed k ≤ 1+E.mu)
    {i : Ground n} (hi : i ∈ D.items) (hne : i ≠ E.big) :
    I.totalCost (I.iterate {D.seed} k)+I.cost i ≤ I.budget := by
  have hc := E.second i hi hne
  have hb := E.budget_bound
  unfold pathCost at hx
  change I.cost i ≤ E.lam at hc
  linarith
theorem has_choice_late {k : ℕ} (hk : k ≤ n) (hx : I.pathCost D.seed k ≤ 1+E.mu) :
    ∃ i, I.choose (I.iterate {D.seed} k) = some i := by
  classical
  cases he : I.choose (I.iterate {D.seed} k) with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have ht : D.items \ {E.big} ⊆ I.iterate {D.seed} k :=
      I.terminal_contains (I.choose_none_iff.mp he) (fun i hi =>
        E.late_budget hx (Finset.mem_sdiff.mp hi).1 (by simpa using (Finset.mem_sdiff.mp hi).2))
    have hsub : D.optimumSet ⊆ insert E.big (I.iterate {D.seed} k) := by
      intro i hi
      rcases Finset.mem_union.mp (D.optimum_subset_union k hi) with h | h
      · exact Finset.mem_insert_of_mem h
      · by_cases heq : i = E.big
        · subst i; exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (ht (Finset.mem_sdiff.mpr ⟨h, by simpa using heq⟩))
    have hval := I.monotone hsub
    rw [D.value_one] at hval
    have hmargin := I.marginal_le_singleton E.big (I.iterate {D.seed} k)
    have hp := D.seed_max E.big (Finset.mem_erase.mp E.big_mem).2
    have hupper := I.prefix_le_output D.seed_feasible (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n+1))
    change I.value (I.iterate {D.seed} k) ≤ I.output at hupper
    change I.value {E.big} ≤ D.p at hp
    unfold marginal at hmargin
    have hbad := D.bad_output
    unfold alpha at hbad
    exact False.elim (by linarith [D.seed_small.2])
theorem terminal_crosses_late : 1+E.mu < I.pathCost D.seed n := by
  by_contra hn
  obtain ⟨i, hi⟩ := E.has_choice_late le_rfl (le_of_not_gt hn)
  have ht := I.choose_none_iff.mpr (I.iterate_terminal {D.seed})
  rw [hi] at ht
  contradiction

theorem density_first {k : ℕ} (hk : k ≤ n) (hx : I.pathCost D.seed k ≤ 1+E.lam) :
    b/(1+E.lam) ≤ I.pathDensity D.seed k := by
  classical
  obtain ⟨i, hi⟩ := E.has_choice_late hk (by linarith [E.lam_le_mu])
  have hbudget (j : Ground n) (hj : j ∈ D.items) :
      I.totalCost (I.iterate {D.seed} k)+I.cost j ≤ I.budget := by
    have hb := E.budget_bound
    have hc := E.largest j hj
    change I.cost j ≤ E.mu at hc
    unfold pathCost at hx
    linarith
  have hrepair : I.Feasible (I.iterate {D.seed} k ∪ {E.big}) := by
    have hc := I.totalCost_union_le (I.iterate {D.seed} k) {E.big}
    rw [I.totalCost_singleton] at hc
    exact hc.trans (hbudget E.big E.big_mem)
  have hr := I.repair_residual_bound D.seed_feasible (Finset.singleton_subset_iff.mpr E.big_mem)
    (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n+1)) (by simp) hrepair
  have he := Finset.sum_sdiff (Finset.singleton_subset_iff.mpr E.big_mem)
    (f := I.residual D.items (I.iterate {D.seed} k))
  have hd : (∑ j ∈ D.items \ {E.big}, I.residual D.items (I.iterate {D.seed} k) j) ≤
      I.density i (I.iterate {D.seed} k)*(1+E.lam) := by
    calc
      _ ≤ ∑ j ∈ D.items \ {E.big}, I.density i (I.iterate {D.seed} k)*I.cost j :=
        Finset.sum_le_sum (fun j hj => I.residual_le_chosen_density hi (hbudget j (Finset.mem_sdiff.mp hj).1))
      _ = _ := by rw [← Finset.mul_sum]; change _*I.totalCost (D.items \ {E.big}) = _; rw [E.without_big_cost]
  have hg := (D.residual_bounds k).1
  change (∑ j ∈ {E.big}, I.residual D.items (I.iterate {D.seed} k) j) ≤
    I.output-I.value (I.iterate {D.seed} k) at hr
  have hb := D.bad_output
  unfold alpha at hb
  simp only [pathDensity, greedyDensity, hi]
  apply (div_le_iff₀ (show 0 < 1+E.lam by linarith [E.lam_pos])).mpr
  linarith

theorem density_second {k : ℕ} (hk : k ≤ n) (hx : I.pathCost D.seed k ≤ 1+E.mu) :
    b-D.p ≤ I.pathDensity D.seed k := by
  classical
  obtain ⟨i, hi⟩ := E.has_choice_late hk hx
  have hrepair : I.Feasible (I.iterate {D.seed} k ∪ {E.small}) := by
    have hc := I.totalCost_union_le (I.iterate {D.seed} k) {E.small}
    rw [I.totalCost_singleton] at hc
    exact hc.trans (E.late_budget hx E.small_mem E.distinct.symm)
  have hr := I.repair_residual_bound D.seed_feasible (Finset.singleton_subset_iff.mpr E.small_mem)
    (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n+1)) (by simp) hrepair
  have he := Finset.sum_sdiff (Finset.singleton_subset_iff.mpr E.small_mem)
    (f := I.residual D.items (I.iterate {D.seed} k))
  have hbmem : E.big ∈ D.items \ {E.small} := by simp [E.big_mem, E.distinct]
  have he' := Finset.sum_sdiff (Finset.singleton_subset_iff.mpr hbmem)
    (f := I.residual D.items (I.iterate {D.seed} k))
  have hp : I.residual D.items (I.iterate {D.seed} k) E.big ≤ D.p :=
    (I.residual_le_singleton D.items _ E.big).trans (D.seed_max E.big (Finset.mem_erase.mp E.big_mem).2)
  have hd : (∑ j ∈ (D.items \ {E.small}) \ {E.big}, I.residual D.items (I.iterate {D.seed} k) j) ≤
      I.density i (I.iterate {D.seed} k) := by
    calc
      _ ≤ ∑ j ∈ (D.items \ {E.small}) \ {E.big}, I.density i (I.iterate {D.seed} k)*I.cost j :=
        Finset.sum_le_sum (fun j hj => I.residual_le_chosen_density hi (E.late_budget hx
          (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hj).1).1 (by simpa using (Finset.mem_sdiff.mp hj).2)))
      _ = _ := by rw [← Finset.mul_sum]; change _*I.totalCost ((D.items \ {E.small}) \ {E.big}) = _; rw [E.without_pair_cost, mul_one]
  have hg := (D.residual_bounds k).1
  change (∑ j ∈ {E.small}, I.residual D.items (I.iterate {D.seed} k) j) ≤
    I.output-I.value (I.iterate {D.seed} k) at hr
  simp only [Finset.sum_singleton] at he he' hr
  have hb := D.bad_output
  unfold alpha at hb
  simp only [pathDensity, greedyDensity, hi]
  linarith

/-- The full real-path inequality (2.7), obtained by finite clipped sums. -/
theorem fundamental_path_bound : I.valueAt D.seed 1+b*E.lam/(1+E.lam)+
    (b-D.p)*(E.mu-E.lam) ≤ I.output := by
  have hl := E.lam_pos
  have hm := E.mu_pos
  have ho := E.lam_le_mu
  have hc := E.terminal_crosses_late
  have h1 := I.density_integral_lower (a := D.seed) (lo := 1) (hi := 1+E.lam) (c := b/(1+E.lam))
    (by norm_num) (by linarith) (by linarith)
    (fun k hk hd => E.density_first hk.le (I.intervalDuration_pos_left (by linarith) hd).le)
  have h2 := I.density_integral_lower (a := D.seed) (lo := 1+E.lam) (hi := 1+E.mu) (c := b-D.p)
    (by linarith) (by linarith) hc.le
    (fun k hk hd => E.density_second hk.le (I.intervalDuration_pos_left (by linarith) hd).le)
  have h3 := I.valueAt_le_output D.seed_feasible (1+E.mu)
  have he : b/(1+E.lam)*((1+E.lam)-1) = b*E.lam/(1+E.lam) := by ring
  rw [he] at h1
  linarith

end CostPair
end CertificateData
end
end S2R.Instance
