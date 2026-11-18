import S2R.FrozenComparison
import S2R.CostRoot
import S2R.SmallDomain

namespace S2R.Instance.CertificateData.CostPair
noncomputable section
open S2R.Analysis
variable {n : ℕ} {I : Instance n} {D : I.CertificateData}

def tail (_E : D.CostPair) : Selection n := D.items \ D.repair

structure RootData (E : D.CostPair) where
  root : ℝ
  positive : 0 < root
  equation : rootFunction E.tail I.cost E.mu E.lam root = 0

def rootData (E : D.CostPair) : RootData E := by
  have hc (i : Ground n) (hi : i ∈ E.tail) : 0 < I.cost i ∧ I.cost i ≤ E.lam := by
    have hi' := Finset.mem_sdiff.mp hi
    have hn : i ≠ E.big := by
      intro he; subst i
      apply hi'.2
      rw [E.repair_eq]
      exact Finset.mem_insert_self _ _
    exact ⟨I.cost_pos i, E.second i hi'.1 hn⟩
  have he := cost_root_exists_unique E.tail I.cost E.mu_pos E.lam_pos E.lam_le_mu hc D.tail_cost'
  exact ⟨Classical.choose he, (Classical.choose_spec he).1.1, (Classical.choose_spec he).1.2.2⟩

namespace RootData
variable {E : D.CostPair} (R : RootData E)
def q : ℝ := 1-R.root/E.s
def k (_R : RootData E) : ℝ := cutoffK E.u
def d : ℝ := cutoffD E.s E.u R.q
def dbar : ℝ := min R.d E.lam
def heavy : Selection n := E.tail.filter (fun i => R.d < I.cost i)
def H : Selection n := D.repair ∪ R.heavy
def K : ℝ := I.totalCost R.H
def A : ℝ := I.totalCost (D.items \ R.H)
def mean : ℝ := E.s*(1-3*R.q)
def fraction (i : Ground n) : ℝ := max (I.cost i-R.root) 0/I.cost i

theorem root_bounds : R.root ≤ E.lam ∧ 2*E.s/3 ≤ R.root ∧
    excess E.tail I.cost R.root = 3*R.root-E.mu-E.lam := by
  have hb : E.mu < 2*E.lam := by
    rw [E.mu_eq, E.lam_eq]
    nlinarith [E.s_pos, E.u_lt_fifth]
  have hc (i : Ground n) (hi : i ∈ E.tail) : I.cost i ≤ E.lam := by
    apply E.second i (Finset.mem_sdiff.mp hi).1
    intro he; subst i
    have hn := (Finset.mem_sdiff.mp hi).2
    rw [E.repair_eq] at hn
    exact hn (Finset.mem_insert_self _ _)
  have h := cost_root_bounds E.tail I.cost E.lam_pos E.lam_le_mu hb hc R.positive R.equation
  refine ⟨h.1, ?_, h.2.2⟩
  unfold s
  linarith [h.2.1]
theorem q_bounds : E.u ≤ R.q ∧ R.q ≤ 1/3 := by
  apply root_q_bounds E.s_pos E.u_bounds.1
  · rw [← E.lam_eq]; exact R.root_bounds.1
  · exact R.root_bounds.2.1
theorem q_nonneg : 0 ≤ R.q := E.u_bounds.1.trans R.q_bounds.1
theorem root_eq_z : R.root = z E.s R.q := by
  unfold z q
  field_simp [E.s_pos.ne']
theorem root_le_s : R.root ≤ E.s := R.root_bounds.1.trans E.lam_le_s
theorem k_bounds : 0 < R.k ∧ R.k ≤ 3/4 ∧ R.k < 1 ∧ R.root < R.k := by
  have hu := E.u_bounds.1
  have hu5 := E.u_lt_fifth.le
  have hs := E.s_lt_quarter.le
  have hz := R.root_le_s
  unfold k cutoffK
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith
theorem d_formula : R.d=R.root*R.k/(R.k-R.root) := by
  have hk := R.k_bounds.1
  have h := cutoff_identity (s := E.s) (q := R.q) hk.ne'
  change R.d=z E.s R.q*R.k/(R.k-z E.s R.q) at h
  rwa [← R.root_eq_z] at h
theorem root_le_d : R.root ≤ R.d := by
  rw [R.d_formula]
  apply (le_div_iff₀ (sub_pos.mpr R.k_bounds.2.2.2)).mpr
  nlinarith [sq_nonneg R.root]
theorem dbar_bounds : 0 < R.dbar ∧ R.root ≤ R.dbar ∧ R.dbar ≤ E.lam := by
  have hd := R.root_le_d
  have hl := R.root_bounds.1
  exact ⟨lt_min (R.positive.trans_le hd) (R.positive.trans_le hl), le_min hd hl, min_le_right _ _⟩

theorem heavy_subset_tail : R.heavy ⊆ E.tail := Finset.filter_subset _ _
theorem H_subset : R.H ⊆ D.items := Finset.union_subset D.repair_subset
  (R.heavy_subset_tail.trans Finset.sdiff_subset)
theorem repair_disjoint_heavy : Disjoint D.repair R.heavy := by
  exact (show Disjoint D.repair E.tail from Finset.disjoint_sdiff).mono_right R.heavy_subset_tail
theorem K_decomposition : R.K=2*E.s+I.totalCost R.heavy := by
  rw [K, H, I.totalCost_union R.repair_disjoint_heavy, E.repair_cost]
  unfold s
  ring
theorem full_root_equation : excess D.items I.cost R.root=R.root := by
  have he := Finset.sum_sdiff D.repair_subset (f := fun i => max (I.cost i-R.root) 0)
  have hpair : (∑ i ∈ D.repair, max (I.cost i-R.root) 0) =
      max (E.mu-R.root) 0+max (E.lam-R.root) 0 := by
    classical
    simp [E.repair_eq, E.distinct, mu, lam]
  rw [hpair] at he
  change excess E.tail I.cost R.root+(max (E.mu-R.root) 0+max (E.lam-R.root) 0)=
    excess D.items I.cost R.root at he
  have hr := R.equation
  unfold rootFunction at hr
  linarith
theorem heavy_empty_of_lam_le_d (hd : E.lam ≤ R.d) : R.heavy=∅ := by
  classical
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro i hi
  have ht := Finset.mem_filter.mp hi
  have hbig : i ≠ E.big := by
    intro he; subst i
    have hn := (Finset.mem_sdiff.mp ht.1).2
    rw [E.repair_eq] at hn
    exact hn (Finset.mem_insert_self _ _)
  have hc := E.second i (Finset.mem_sdiff.mp ht.1).1 hbig
  change I.cost i ≤ E.lam at hc
  linarith [ht.2]
theorem K_bounds : 2*E.s ≤ R.K ∧ R.K ≤ R.k := by
  constructor
  · rw [R.K_decomposition]; linarith [I.totalCost_nonneg R.heavy]
  · by_cases hd : E.lam ≤ R.d
    · rw [R.K_decomposition, R.heavy_empty_of_lam_le_d hd, I.totalCost_empty, add_zero]
      have hu := E.u_lt_fifth
      have hs := E.s_lt_quarter
      unfold k cutoffK
      linarith
    · apply threshold_mass_bound D.items R.H I.cost R.H_subset R.positive R.k_bounds.2.2.2 R.full_root_equation
      intro i hi
      rw [← R.d_formula]
      rcases Finset.mem_union.mp hi with hi | hi
      · rw [E.repair_eq] at hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact (le_of_not_ge hd).trans E.lam_le_mu
        · have he : i=E.small := Finset.mem_singleton.mp hi
          subst i; exact le_of_not_ge hd
      · exact (Finset.mem_filter.mp hi).2.le
theorem truncation_identity : (R.d-R.dbar)*(R.K-2*E.s)=0 := by
  by_cases hd : R.d ≤ E.lam
  · simp [dbar, min_eq_left hd]
  · have he := R.heavy_empty_of_lam_le_d (le_of_not_ge hd)
    rw [R.K_decomposition, he, I.totalCost_empty]
    ring
theorem A_partition : R.A+R.K=1+2*E.s := by
  have h := Finset.sum_sdiff R.H_subset (f := I.cost)
  change R.A+R.K=I.totalCost D.items at h
  rwa [E.total_cost_s] at h
theorem A_bounds : 0 < R.A ∧ E.mu < R.A ∧ R.A ≤ 1 := by
  have ha := R.A_partition
  have hk := R.K_bounds
  have hb := R.k_bounds
  have hs := E.s_pos
  have hmu : E.mu < 1+2*E.s-R.k := by
    rw [E.mu_eq]
    unfold k cutoffK
    have hu := E.u_bounds.1
    have hs4 := E.s_lt_quarter
    nlinarith
  exact ⟨by linarith, by linarith, by linarith⟩
theorem tail_bounded : ∀ i ∈ D.items \ R.H, I.cost i ≤ R.dbar := by
  classical
  intro i hi
  have hi' := Finset.mem_sdiff.mp hi
  have hnR : i ∉ D.repair := fun h => hi'.2 (Finset.mem_union_left _ h)
  have ht : i ∈ E.tail := Finset.mem_sdiff.mpr ⟨hi'.1, hnR⟩
  have hnot : ¬ R.d < I.cost i := fun h => hi'.2 (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨ht,h⟩))
  apply le_min (le_of_not_gt hnot)
  apply E.second i hi'.1
  intro he; subst i
  rw [E.repair_eq] at hnR
  exact hnR (Finset.mem_insert_self _ _)

theorem mean_nonneg : 0 ≤ R.mean := by
  unfold mean
  exact mul_nonneg E.s_pos.le (by linarith [R.q_bounds.2])
theorem mean_le_root : R.mean ≤ R.root := by
  rw [R.root_eq_z]
  unfold mean z
  nlinarith [R.q_nonneg, E.s_pos]
theorem mean_lt_one : R.mean < 1 :=
  R.mean_le_root.trans_lt (R.root_le_s.trans_lt (E.s_lt_quarter.trans (by norm_num)))
theorem fraction_bounds {i : Ground n} (hi : i ∈ E.tail) : 0 ≤ R.fraction i ∧ R.fraction i ≤ R.q := by
  have hbig : i ≠ E.big := by
    intro he; subst i
    have hn := (Finset.mem_sdiff.mp hi).2
    rw [E.repair_eq] at hn
    exact hn (Finset.mem_insert_self _ _)
  have hc := (E.second i (Finset.mem_sdiff.mp hi).1 hbig).trans E.lam_le_s
  have h := tail_fraction_bounds (I.cost_pos i) E.s_pos hc R.q_nonneg (by linarith [R.q_bounds.2])
  change 0 ≤ max (I.cost i-z E.s R.q) 0/I.cost i ∧ max (I.cost i-z E.s R.q) 0/I.cost i ≤ R.q at h
  rwa [← R.root_eq_z] at h
theorem fraction_mean : (∑ i ∈ E.tail, I.cost i*R.fraction i)=R.mean := by
  have he : excess E.tail I.cost (E.s*(1-R.q))=E.s*(1-3*R.q) := by
    change excess E.tail I.cost (z E.s R.q)=_
    rw [← R.root_eq_z, R.root_bounds.2.2, R.root_eq_z]
    unfold z s
    ring
  have h := tail_fraction_mean E.tail I.cost (fun i _ => I.cost_pos i) he
  change (∑ i ∈ E.tail, I.cost i*(max (I.cost i-z E.s R.q) 0/I.cost i))=R.mean at h
  rwa [← R.root_eq_z] at h
theorem heavy_fraction_lower {i : Ground n} (hi : i ∈ R.heavy) : R.root/R.k ≤ R.fraction i := by
  have ht := Finset.mem_filter.mp hi
  have hci := I.cost_pos i
  have hk := R.k_bounds.1
  have hdiff := sub_pos.mpr R.k_bounds.2.2.2
  have hdc := (div_lt_iff₀ hdiff).mp (by rw [← R.d_formula]; exact ht.2)
  have hrootci : R.root ≤ I.cost i := R.root_le_d.trans ht.2.le
  unfold fraction
  rw [max_eq_left (sub_nonneg.mpr hrootci)]
  apply (div_le_div_iff₀ hk hci).mpr
  nlinarith only [hdc]

end RootData
end
end S2R.Instance.CertificateData.CostPair
