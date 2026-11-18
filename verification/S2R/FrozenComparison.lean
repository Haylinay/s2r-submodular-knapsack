import S2R.RegionExclusion
import S2R.Certificate

namespace S2R.Instance.CertificateData.CostPair
noncomputable section
open S2R.Analysis
variable {n : ℕ} {I : Instance n} {D : I.CertificateData} (E : D.CostPair)

set_option maxHeartbeats 1200000 in
theorem frozen_comparison (H : Selection n) (hH : H ⊆ D.items) {d r0 : ℝ}
    (hA : 0 < I.totalCost (D.items \ H)) (hd : d ≤ E.mu)
    (htail : ∀ i ∈ D.items \ H, I.cost i ≤ d)
    (hG : alpha-b*r0 ≤ I.valueAt D.seed 1)
    (hKJ : I.totalCost H*(Real.exp ((E.mu-d)/I.totalCost (D.items \ H))-1) ≤ E.lam)
    (hr : r0 ≤ (E.lam+(1+E.lam-I.totalCost H)*
      (Real.exp ((E.mu-d)/I.totalCost (D.items \ H))-1))/(1+E.lam)) : alpha ≤ I.output := by
  classical
  let A := I.totalCost (D.items \ H)
  let K := I.totalCost H
  let y := 1+E.lam
  let cut := 1+E.mu+E.lam-d
  let J := Real.exp ((E.mu-d)/A)-1
  have hy0 : 0 ≤ y := by dsimp [y]; linarith [E.lam_pos]
  have hy1 : 1 ≤ y := by dsimp [y]; linarith [E.lam_pos]
  have hcut : y ≤ cut := by dsimp [y, cut]; linarith
  have hyend : y < I.pathCost D.seed n := by dsimp [y]; linarith [E.terminal_crosses_late, E.lam_le_mu]
  obtain ⟨k, hkn, hkleft, hkright⟩ := I.exists_crossing D.seed n hy0 hyend
  let ρ := I.pathDensity D.seed k
  let theta := 1-ρ*K
  have hρlower : b/(1+E.lam) ≤ ρ := E.density_first hkn.le hkleft
  have hbefore : ρ*E.lam ≤ I.valueAt D.seed y-I.valueAt D.seed 1 := by
    have h := I.density_integral_lower (a := D.seed) (lo := 1) (hi := y) (c := ρ)
      (by norm_num) hy1 hyend.le (by
        intro j hj hpos
        have hjleft := I.intervalDuration_pos_left hy1 hpos
        have hjk : j ≤ k := by
          by_contra hn
          have hj' : k+1 ≤ j := by omega
          have hm := I.pathCost_mono D.seed hj'
          linarith
        exact I.pathDensity_antitone D.seed hjk)
    simpa [y] using h
  have hfreeze (j : ℕ) (hkj : k ≤ j) :
      (∑ i ∈ H, I.residual D.items (I.iterate {D.seed} j) i) ≤ ρ*K := by
    have hb (i : Ground n) (hi : i ∈ H) :
        I.totalCost (I.iterate {D.seed} k)+I.cost i ≤ I.budget := by
      have hc := E.largest i (hH hi)
      have hb := E.budget_bound
      change I.cost i ≤ E.mu at hc
      change I.totalCost (I.iterate {D.seed} k)-I.cost D.seed ≤ 1+E.lam at hkleft
      linarith
    calc
      _ ≤ ∑ i ∈ H, ρ*I.cost i := Finset.sum_le_sum (fun i hi =>
        (I.residual_antitone D.items (I.iterate_mono {D.seed} hkj) i).trans
          (I.residual_le_greedyDensity (hb i hi)))
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hrate_actual (j : ℕ) (hkj : k ≤ j) (hjcut : I.pathCost D.seed j ≤ cut) :
      theta-I.value (I.iterate {D.seed} j) ≤ A*I.pathDensity D.seed j := by
    have htailbudget (i : Ground n) (hi : i ∈ D.items \ H) :
        I.totalCost (I.iterate {D.seed} j)+I.cost i ≤ I.budget := by
      have hc := htail i hi
      have hb := E.budget_bound
      dsimp [cut] at hjcut
      unfold pathCost at hjcut
      linarith
    have ht : (∑ i ∈ D.items \ H, I.residual D.items (I.iterate {D.seed} j) i) ≤
        I.pathDensity D.seed j*A := by
      calc
        _ ≤ ∑ i ∈ D.items \ H, I.pathDensity D.seed j*I.cost i :=
          Finset.sum_le_sum (fun i hi => I.residual_le_greedyDensity (htailbudget i hi))
        _ = _ := by rw [← Finset.mul_sum]; rfl
    have hg := (D.residual_bounds j).1
    have he := Finset.sum_sdiff hH (f := I.residual D.items (I.iterate {D.seed} j))
    have hh := hfreeze j hkj
    dsimp [theta]
    nlinarith only [ht, hg, he, hh]
  let δ : ℕ → ℝ := fun j => I.intervalDuration D.seed y cut j+
    if j=n then max (cut-I.pathCost D.seed n) 0 else 0
  let F : ℕ → ℝ := fun m => I.valueAt D.seed y+
    ∑ j ∈ Finset.range m, I.pathDensity D.seed j*δ j
  have hgain (j : ℕ) : I.pathDensity D.seed j*δ j =
      I.pathDensity D.seed j*I.intervalDuration D.seed y cut j := by
    dsimp [δ]
    by_cases hj : j=n
    · subst j; rw [I.pathDensity_terminal]; ring
    · simp [hj]
  have hF (m : ℕ) : F m=I.partialValueAt D.seed cut m+
      (I.valueAt D.seed y-I.partialValueAt D.seed y m) := by
    dsimp [F, partialValueAt]
    simp_rw [hgain, intervalDuration, mul_sub, Finset.sum_sub_distrib]
    ring
  have hFstep (j : ℕ) (_ : j < n+1) : F (j+1)=F j+I.pathDensity D.seed j*δ j := by
    dsimp [F]
    rw [Finset.sum_range_succ]
    ring
  have hFend : F (n+1)=I.valueAt D.seed cut := by
    rw [hFstep n (by omega), I.pathDensity_terminal, zero_mul, add_zero, hF n]
    change I.valueAt D.seed cut+(I.valueAt D.seed y-I.valueAt D.seed y) = _
    ring
  have hδnon (j : ℕ) (_ : j < n+1) : 0 ≤ δ j := by
    dsimp [δ]
    have hi := I.intervalDuration_nonneg D.seed hcut j
    split_ifs <;> linarith [le_max_right (cut-I.pathCost D.seed n) 0]
  have hactive (j : ℕ) (hj : j < n+1) (hp : 0 < δ j) : k ≤ j ∧ I.pathCost D.seed j < cut := by
    by_cases hjn : j=n
    · subst j
      have hc : I.pathCost D.seed (n+1)=I.pathCost D.seed n := by
        simp [pathCost, iterate_succ, I.step_eq_self (I.iterate_terminal {D.seed})]
      have hz : I.intervalDuration D.seed y cut n=0 := by simp [intervalDuration, durationAt, hc]
      simp only [δ, if_pos rfl, hz, zero_add] at hp
      have hpos : 0 < cut-I.pathCost D.seed n := (lt_max_iff.mp hp).resolve_right (lt_irrefl _)
      exact ⟨hkn.le, by linarith⟩
    · have hjn' : j < n := by omega
      have hp' : 0 < I.intervalDuration D.seed y cut j := by simpa [δ, hjn] using hp
      have hl := I.intervalDuration_pos_left hcut hp'
      have hr := I.intervalDuration_pos_right hcut hp'
      have hkj : k ≤ j := by
        by_contra hn
        have hm := I.pathCost_mono D.seed (show j+1 ≤ k by omega)
        linarith
      exact ⟨hkj, hl⟩
  have hrate (j : ℕ) (hj : j < n+1) (hp : 0 < δ j) : theta-F j ≤ A*I.pathDensity D.seed j := by
    obtain ⟨hkj, hjcut⟩ := hactive j hj hp
    have hjn : j ≤ n := by omega
    have hpartial := I.partialValueAt_mono D.seed y hjn
    change I.partialValueAt D.seed y j ≤ I.valueAt D.seed y at hpartial
    have he := I.partialValueAt_eq_actual j hjcut.le
    rw [hF j, he]
    linarith [hrate_actual j hkj hjcut.le]
  have htime : (∑ j ∈ Finset.range (n+1), δ j) = cut-y := by
    have he : (∑ j ∈ Finset.range n, δ j) = ∑ j ∈ Finset.range n, I.intervalDuration D.seed y cut j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≠ n := Nat.ne_of_lt (Finset.mem_range.mp hj)
      simp [δ, hjn]
    have hc : I.pathCost D.seed (n+1)=I.pathCost D.seed n := by
      simp [pathCost, iterate_succ, I.step_eq_self (I.iterate_terminal {D.seed})]
    have hdn : δ n=max (cut-I.pathCost D.seed n) 0 := by
      simp [δ, intervalDuration, durationAt, hc]
    rw [Finset.sum_range_succ, he, hdn]
    simp only [intervalDuration, Finset.sum_sub_distrib]
    rw [I.durationAt_sum D.seed (hy0.trans hcut), I.durationAt_sum D.seed hy0, min_eq_right hyend.le]
    by_cases hh : I.pathCost D.seed n ≤ cut
    · rw [min_eq_left hh, max_eq_left (sub_nonneg.mpr hh)]; ring
    · rw [min_eq_right (le_of_not_ge hh), max_eq_right (by linarith)]; ring
  have hex := finite_exponential_comparison F (I.pathDensity D.seed) δ (n+1) hA hδnon
    (fun j _ => I.greedyDensity_nonneg _) hFstep hrate
  rw [htime, hFend] at hex
  have hFzero : F 0=I.valueAt D.seed y := by simp [F]
  rw [hFzero] at hex
  have he : Real.exp ((cut-y)/A)=1+J := by dsimp [cut, y, J]; congr 1 <;> ring
  rw [he] at hex
  have hJ : 0 ≤ J := by
    dsimp [J]
    have hh : 0 ≤ (E.mu-d)/A := div_nonneg (sub_nonneg.mpr hd) hA.le
    exact sub_nonneg.mpr (Real.one_le_exp_iff.mpr hh)
  have hout := mul_le_mul_of_nonneg_left (I.valueAt_le_output D.seed_feasible cut)
    (show 0 ≤ 1+J by linarith)
  have hM : (alpha-b*r0)+ρ*(E.lam-K*J)+J ≤ (1+J)*I.output := by
    dsimp [theta] at hex
    nlinarith only [hex, hout, hbefore, hG]
  exact frozen_algebra hJ E.lam_pos.le hρlower hKJ hr rfl hM

end
end S2R.Instance.CertificateData.CostPair
