import S2R.DynamicPotential
import S2R.GreedyCurve

namespace S2R.Instance
noncomputable section
open S2R.Analysis
variable {n : ℕ} (I : Instance n)

/-- Normalized data for manuscript section 3. The tail outside the seed and
the two repair items has cost one. No density, curve, or certificate conclusion
is included among these fields. -/
structure CertificateData where
  optimumSet : Selection n
  seed : Ground n
  repair : Selection n
  seed_mem : seed ∈ optimumSet
  feasible : I.Feasible optimumSet
  value_one : I.value optimumSet = 1
  seed_max : ∀ i ∈ optimumSet, I.value {i} ≤ I.value {seed}
  repair_subset : repair ⊆ optimumSet.erase seed
  repair_card : repair.card ≤ 2
  tail_cost : I.totalCost ((optimumSet.erase seed) \ repair) = 1
  individual_cost : ∀ i ∈ optimumSet.erase seed, I.cost i ≤ I.totalCost repair
  bad_output : I.output < alpha

namespace CertificateData
variable {I} (D : CertificateData I)
def items : Selection n := D.optimumSet.erase D.seed
def p : ℝ := I.value {D.seed}
theorem tail_cost' : I.totalCost (D.items \ D.repair) = 1 := D.tail_cost

theorem seed_feasible : I.Feasible {D.seed} :=
  I.feasible_subset (Finset.singleton_subset_iff.mpr D.seed_mem) D.feasible
theorem p_lt_one : D.p < 1 := by
  have h := I.prefix_le_output D.seed_feasible (0 : Fin (n+1))
  have hp : D.p ≤ I.output := by simpa [prefixSet, p] using h
  exact hp.trans_lt (D.bad_output.trans alpha_lt_one)
theorem p_pos : 0 < D.p := by
  have h := I.value_le_singleton_sum D.optimumSet
  have hs : (∑ i ∈ D.optimumSet, I.value {i}) ≤ D.optimumSet.card*D.p := by
    calc
      _ ≤ ∑ _i ∈ D.optimumSet, D.p := Finset.sum_le_sum D.seed_max
      _ = _ := by simp
  rw [D.value_one] at h
  by_contra hn
  have hp : D.p ≤ 0 := le_of_not_gt hn
  have hm := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg D.optimumSet.card : (0:ℝ) ≤ _) hp
  linarith
theorem budget_bound : I.cost D.seed+I.totalCost D.repair+1 ≤ I.budget := by
  have hc : I.totalCost D.optimumSet = I.cost D.seed+I.totalCost D.items := by
    rw [← Finset.insert_erase D.seed_mem, I.totalCost_insert (Finset.not_mem_erase _ _)]
    rfl
  have hs := Finset.sum_sdiff D.repair_subset (f := I.cost)
  change I.totalCost (D.items \ D.repair)+I.totalCost D.repair = I.totalCost D.items at hs
  rw [D.tail_cost'] at hs
  have hf := D.feasible
  unfold Feasible at hf
  linarith
theorem seed_in_path (k : ℕ) : D.seed ∈ I.iterate {D.seed} k :=
  I.subset_iterate {D.seed} k (Finset.mem_singleton_self _)
theorem individual_budget {k : ℕ} (hx : I.pathCost D.seed k ≤ 1)
    {i : Ground n} (hi : i ∈ D.items) :
    I.totalCost (I.iterate {D.seed} k)+I.cost i ≤ I.budget := by
  have hc := D.individual_cost i hi
  have hb := D.budget_bound
  unfold pathCost at hx
  linarith
theorem repair_feasible {k : ℕ} (hx : I.pathCost D.seed k ≤ 1) :
    I.Feasible (I.iterate {D.seed} k ∪ D.repair) := by
  have hc := I.totalCost_union_le (I.iterate {D.seed} k) D.repair
  have hb := D.budget_bound
  unfold pathCost at hx
  unfold Feasible
  linarith

theorem optimum_subset_union (k : ℕ) : D.optimumSet ⊆ I.iterate {D.seed} k ∪ D.items := by
  intro i hi
  by_cases he : i = D.seed
  · subst i
    exact Finset.mem_union_left _ (D.seed_in_path k)
  · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨he, hi⟩)
theorem residual_initial : (∑ i ∈ D.items, I.residual D.items {D.seed} i) = 1-D.p := by
  rw [I.residual_sum]
  have he : {D.seed} ∪ D.items = D.optimumSet := by
    calc
      _ = insert D.seed D.items := by ext i; simp
      _ = _ := Finset.insert_erase D.seed_mem
  rw [he, D.value_one]
  rfl
theorem residual_bounds (k : ℕ) :
    1-I.value (I.iterate {D.seed} k) ≤ (∑ i ∈ D.items, I.residual D.items (I.iterate {D.seed} k) i) ∧
    (∑ i ∈ D.items, I.residual D.items (I.iterate {D.seed} k) i) ≤ 1-D.p := by
  constructor
  · rw [I.residual_sum]
    have hm := I.monotone (D.optimum_subset_union k)
    rw [D.value_one] at hm
    linarith
  · rw [← D.residual_initial]
    exact Finset.sum_le_sum (fun i _ => I.residual_antitone D.items (I.subset_iterate {D.seed} k) i)
theorem items_nonempty : D.items.Nonempty := by
  by_contra h
  have he := Finset.not_nonempty_iff_eq_empty.mp h
  have hr := D.residual_initial
  rw [he] at hr
  simp only [Finset.sum_empty] at hr
  linarith [D.p_lt_one]
theorem reference_exists : ∃ κ : ℝ, 0 < κ ∧ cappedMass D.items I.cost D.p κ = 1-D.p := by
  apply reference_mass_exists D.items I.cost D.items_nonempty (fun i _ => I.cost_pos i)
    D.p_pos (by linarith [D.p_lt_one])
  have h : (∑ i ∈ D.items, I.residual D.items {D.seed} i) ≤ ∑ _i ∈ D.items, D.p :=
    Finset.sum_le_sum (fun i hi => (I.residual_le_singleton D.items {D.seed} i).trans
      (D.seed_max i (Finset.mem_erase.mp hi).2))
  rw [D.residual_initial] at h
  simpa using h

theorem has_choice {k : ℕ} (hk : k ≤ n) (hx : I.pathCost D.seed k ≤ 1) :
    ∃ i, I.choose (I.iterate {D.seed} k) = some i := by
  cases he : I.choose (I.iterate {D.seed} k) with
  | some i => exact ⟨i, rfl⟩
  | none =>
    have ht := I.terminal_contains (I.choose_none_iff.mp he) (fun i hi => D.individual_budget hx hi)
    have hsub : D.optimumSet ⊆ I.iterate {D.seed} k := by
      intro i hi
      rcases Finset.mem_union.mp (D.optimum_subset_union k hi) with h | h
      · exact h
      · exact ht h
    have hval := I.monotone hsub
    have hupper := I.prefix_le_output D.seed_feasible (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n+1))
    change I.value (I.iterate {D.seed} k) ≤ I.output at hupper
    rw [D.value_one] at hval
    have hbad := D.bad_output.trans alpha_lt_one
    exact False.elim (by linarith)
theorem terminal_crosses : 1 < I.pathCost D.seed n := by
  by_contra hn
  obtain ⟨i, hi⟩ := D.has_choice le_rfl (le_of_not_gt hn)
  have ht := I.choose_none_iff.mpr (I.iterate_terminal {D.seed})
  rw [hi] at ht
  contradiction

theorem density_lower {k : ℕ} (hk : k ≤ n) (hx : I.pathCost D.seed k ≤ 1) :
    b ≤ I.pathDensity D.seed k := by
  obtain ⟨i, hi⟩ := D.has_choice hk hx
  have hg := (D.residual_bounds k).1
  have hr := I.repair_residual_bound D.seed_feasible D.repair_subset
    (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n+1)) D.repair_card (D.repair_feasible hx)
  change (∑ j ∈ D.repair, I.residual D.items (I.iterate {D.seed} k) j) ≤
    I.output-I.value (I.iterate {D.seed} k) at hr
  have he := Finset.sum_sdiff D.repair_subset (f := I.residual D.items (I.iterate {D.seed} k))
  change (∑ j ∈ D.items \ D.repair, I.residual D.items (I.iterate {D.seed} k) j)+
    (∑ j ∈ D.repair, I.residual D.items (I.iterate {D.seed} k) j) =
    ∑ j ∈ D.items, I.residual D.items (I.iterate {D.seed} k) j at he
  have hd : (∑ j ∈ D.items \ D.repair, I.residual D.items (I.iterate {D.seed} k) j) ≤
      I.density i (I.iterate {D.seed} k) := by
    calc
      _ ≤ ∑ j ∈ D.items \ D.repair, I.density i (I.iterate {D.seed} k)*I.cost j :=
        Finset.sum_le_sum (fun j hj => I.residual_le_chosen_density hi
          (D.individual_budget hx (Finset.mem_sdiff.mp hj).1))
      _ = I.density i (I.iterate {D.seed} k) := by
        rw [← Finset.mul_sum]
        change _*I.totalCost (D.items \ D.repair) = _
        rw [D.tail_cost', mul_one]
  simp only [pathDensity, greedyDensity, hi]
  have hb := D.bad_output
  unfold alpha at hb
  linarith

theorem capped_density_bound {k : ℕ} (hk : k ≤ n) (hx : I.pathCost D.seed k ≤ 1) :
    1-I.value (I.iterate {D.seed} k) ≤
      min (1-D.p) (cappedMass D.items I.cost D.p (I.pathDensity D.seed k)) := by
  obtain ⟨i, hi⟩ := D.has_choice hk hx
  have hsum : (∑ j ∈ D.items, I.residual D.items (I.iterate {D.seed} k) j) ≤
      cappedMass D.items I.cost D.p (I.pathDensity D.seed k) := by
    apply Finset.sum_le_sum
    intro j hj
    apply le_min
    · exact (I.residual_le_singleton D.items _ j).trans (D.seed_max j (Finset.mem_erase.mp hj).2)
    · simpa [pathDensity, greedyDensity, hi] using
        I.residual_le_chosen_density (O := D.items) hi (D.individual_budget hx hj)
  exact le_min ((D.residual_bounds k).1.trans (D.residual_bounds k).2)
    ((D.residual_bounds k).1.trans hsum)

/-- Manuscript (3.1), now proved for the actual greedy path, including its
step crossing cost one. The dynamic lower bound is derived, not assumed. -/
theorem unified_density_certificate {β : ℝ} (τ : Ground n → ℝ)
    (hβ : 0 < β) (hτ : ∀ i ∈ D.items, β ≤ τ i ∧ τ i ≤ 1) :
    1+b-β+D.p*(β-∑ i ∈ D.items, (τ i-β))+
      b*(∑ i ∈ D.items, I.cost i*Real.log (τ i)) ≤ I.curveValue D.seed n := by
  obtain ⟨κ, hκ, hmass⟩ := D.reference_exists
  let P : MassProfile (Ground n) := {
    items := D.items, cost := I.cost, mass := fun i => min D.p (κ*I.cost i),
    nonempty := D.items_nonempty, cost_pos := fun i _ => I.cost_pos i,
    mass_pos := fun i _ => lt_min D.p_pos (mul_pos hκ (I.cost_pos i)) }
  have htotal : P.total = 1-D.p := hmass
  have hW : P.total < 1 := by rw [htotal]; linarith [D.p_pos]
  have hinit : 1-I.curveValue D.seed 0 = P.total := by simp [htotal, p]
  have hres (k : ℕ) (_ : k ≤ n) : 1-I.curveValue D.seed k ≤ P.total := by
    have h := I.curveValue_mono D.seed (Nat.zero_le k)
    rw [I.curveValue_zero] at h
    rw [htotal]
    change 1-I.curveValue D.seed k ≤ 1-I.value {D.seed}
    linarith
  have hrate (k : ℕ) (hk : k < n) (hd : 0 < I.duration D.seed k) :
      b ≤ I.pathDensity D.seed k := D.density_lower hk.le (I.duration_pos_left hd).le
  have hcap (k : ℕ) (hk : k < n) (hd : 0 < I.duration D.seed k) :
      1-I.curveValue D.seed k ≤ P.massAt (I.pathDensity D.seed k) := by
    have hx := (I.duration_pos_left hd).le
    rw [I.curveValue_eq_actual k hx]
    have he := capped_reference_identity D.items I.cost D.p κ (I.pathDensity D.seed k)
      (fun i _ => (I.cost_pos i).le)
    change P.massAt (I.pathDensity D.seed k) = _ at he
    rw [hmass] at he
    rw [he]
    exact D.capped_density_bound hk.le hx
  have hstep (k : ℕ) (_ : k < n) : 1-I.curveValue D.seed (k+1) =
      (1-I.curveValue D.seed k)-I.pathDensity D.seed k*I.duration D.seed k := by
    rw [I.curveValue_succ]; ring
  have ht : (∑ k ∈ Finset.range n, I.duration D.seed k) = 1 := by
    rw [I.duration_sum]
    exact min_eq_right D.terminal_crosses.le
  have hdyn := P.finite_dynamic_bound (fun k => 1-I.curveValue D.seed k)
    (I.pathDensity D.seed) (I.duration D.seed) n hW hinit hres
    (fun k _ => I.duration_nonneg D.seed k) hrate hcap hstep ht
  apply certificate_dualization D.items I.cost (fun i => min D.p (κ*I.cost i)) τ
    (fun i _ => I.cost_pos i) (fun i _ => ⟨lt_min D.p_pos (mul_pos hκ (I.cost_pos i)), min_le_left _ _⟩)
    hβ hτ hmass
  change 1-I.curveValue D.seed n+b ≤ ∑ i ∈ D.items, capCost (min D.p (κ*I.cost i)) (I.cost i) at hdyn
  linarith

end CertificateData
end
end S2R.Instance
