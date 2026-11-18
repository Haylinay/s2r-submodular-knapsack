import S2R.RepairImplementation

namespace S2R.SelectionScan
noncomputable section
variable {α : Type*} [LinearOrder α]

def preferred (score : α → ℝ) (i j : α) : Prop :=
  score j ≤ score i ∧ (score i=score j → i ≤ j)

theorem preferred_refl (score : α → ℝ) (i : α) : preferred score i i := ⟨le_rfl, fun _ => le_rfl⟩
theorem preferred_trans (score : α → ℝ) {i j k : α}
    (hij : preferred score i j) (hjk : preferred score j k) : preferred score i k := by
  refine ⟨hjk.1.trans hij.1, ?_⟩
  intro he
  have h₁ : score i=score j := by linarith [hij.1, hjk.1]
  have h₂ : score j=score k := by linarith [hij.1, hjk.1]
  exact (hij.2 h₁).trans (hjk.2 h₂)
theorem preferred_total (score : α → ℝ) (i j : α) :
    preferred score i j ∨ preferred score j i := by
  rcases lt_trichotomy (score i) (score j) with h | h | h
  · right; exact ⟨h.le, fun he => False.elim (h.ne he.symm)⟩
  · rcases le_total i j with hij | hji
    · left; exact ⟨h.ge, fun _ => hij⟩
    · right; exact ⟨h.le, fun _ => hji⟩
  · left; exact ⟨h.le, fun he => False.elim (h.ne he.symm)⟩

structure Result (α : Type*) where
  choice : Option α
  operations : ℕ

/-- Each item is examined once. Twenty unit operations cover membership,
feasibility, marginal-density arithmetic, lexicographic comparison and the
record update, in the real-arithmetic/array model of the manuscript. -/
def select (P : α → Prop) (score : α → ℝ) : List α → Result α
  | [] => ⟨none,1⟩
  | i::xs => by
    classical
    exact
    let z := select P score xs
    let next := if P i then match z.choice with
      | none => some i
      | some j => if preferred score i j then some i else some j
      else z.choice
    ⟨next,z.operations+20⟩

theorem select_operations (P : α → Prop) (score : α → ℝ) (xs : List α) :
    (select P score xs).operations=20*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [select, ih]; omega

def Spec (P : α → Prop) (score : α → ℝ) (xs : List α) : Option α → Prop
  | none => ∀ j ∈ xs, ¬ P j
  | some i => i ∈ xs ∧ P i ∧ ∀ j ∈ xs, P j → preferred score i j

theorem select_spec (P : α → Prop) (score : α → ℝ) (xs : List α) :
    Spec P score xs (select P score xs).choice := by
  classical
  induction xs with
  | nil => simp [select, Spec]
  | cons i xs ih =>
    simp only [select]
    by_cases hPi : P i
    · simp only [if_pos hPi]
      cases he : (select P score xs).choice with
      | none =>
        rw [he] at ih
        refine ⟨List.mem_cons_self, hPi, ?_⟩
        intro j hj hPj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact preferred_refl _ _
        · exact False.elim (ih j hj hPj)
      | some k =>
        rw [he] at ih
        change k ∈ xs ∧ P k ∧ _ at ih
        by_cases hp : preferred score i k
        · simp only [if_pos hp]
          refine ⟨List.mem_cons_self, hPi, ?_⟩
          intro j hj hPj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact preferred_refl _ _
          · exact preferred_trans _ hp (ih.2.2 j hj hPj)
        · simp only [if_neg hp]
          refine ⟨List.mem_cons_of_mem _ ih.1, ih.2.1, ?_⟩
          intro j hj hPj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact (preferred_total _ _ _).resolve_left hp
          · exact ih.2.2 j hj hPj
    · simp only [if_neg hPi]
      cases he : (select P score xs).choice with
      | none =>
        rw [he] at ih
        intro j hj hPj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hPi hPj
        · exact ih j hj hPj
      | some k =>
        rw [he] at ih
        refine ⟨List.mem_cons_of_mem _ ih.1, ih.2.1, ?_⟩
        intro j hj hPj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact False.elim (hPi hPj)
        · exact ih.2.2 j hj hPj

end
end S2R.SelectionScan

namespace S2R.Instance
noncomputable section
open S2R.SelectionScan
variable {n : ℕ} (I : Instance n)

def scanChoose (S : Selection n) : Result (Ground n) :=
  select (fun i => i ∈ I.available S) (fun i => I.density i S) I.itemList

/-- Availability uses only the cached prefix cost and one membership cell;
the finite-set definition need not be recomputed inside the selection scan. -/
theorem available_cached (S : Selection n) (i : Ground n) :
    i ∈ I.available S ↔ i ∉ S ∧ I.totalCost S+I.cost i ≤ I.budget := by
  rw [I.mem_available]
  constructor
  · rintro ⟨hi,hf⟩
    refine ⟨hi,?_⟩
    change I.totalCost (insert i S) ≤ I.budget at hf
    rw [I.totalCost_insert hi] at hf
    linarith
  · rintro ⟨hi,hc⟩
    refine ⟨hi,?_⟩
    change I.totalCost (insert i S) ≤ I.budget
    rw [I.totalCost_insert hi]
    linarith

theorem scanChoose_operations (S : Selection n) : (I.scanChoose S).operations=20*n+1 := by
  simp [scanChoose, select_operations, itemList]

theorem choose_minimal {S : Selection n} {i : Ground n} (hi : I.choose S=some i)
    {j : Ground n} (hj : j ∈ I.bestSet S) : i ≤ j := by
  unfold choose at hi
  split at hi
  next h =>
    have he := Option.some.inj hi
    rw [← he]
    exact Finset.min'_le _ _ hj
  next h => contradiction

theorem scanChoose_correct (S : Selection n) : (I.scanChoose S).choice=I.choose S := by
  classical
  have hs := select_spec (fun i => i ∈ I.available S) (fun i => I.density i S) I.itemList
  change Spec _ _ _ (I.scanChoose S).choice at hs
  cases he : (I.scanChoose S).choice with
  | none =>
    rw [he] at hs
    apply Eq.symm
    apply I.choose_none_iff.mpr
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro j hj
    exact hs j (by simp [itemList]) hj
  | some i =>
    rw [he] at hs
    have hi : i ∈ I.available S := hs.2.1
    cases hc : I.choose S with
    | none =>
      rw [I.choose_none_iff.mp hc] at hi
      exact False.elim (Finset.not_mem_empty _ hi)
    | some j =>
      have hj := I.choose_spec hc
      have hp := hs.2.2 j (by simp [itemList]) hj.1
      have hd : I.density i S=I.density j S := le_antisymm (hj.2 i hi) hp.1
      have hib : i ∈ I.bestSet S := Finset.mem_filter.mpr
        ⟨hi, fun k hk => (hs.2.2 k (by simp [itemList]) hk).1⟩
      have heq := le_antisymm (hp.2 hd) (I.choose_minimal hc hib)
      simp [heq]

def scanStep (S : Selection n) : Selection n :=
  match (I.scanChoose S).choice with
  | none => S
  | some i => insert i S

theorem scanStep_correct (S : Selection n) : I.scanStep S=I.step S := by
  simp only [scanStep, I.scanChoose_correct, step]
  rfl

def scanIterate (S : Selection n) : ℕ → Selection n
  | 0 => S
  | k+1 => I.scanStep (scanIterate S k)

theorem scanIterate_correct (S : Selection n) (k : ℕ) : I.scanIterate S k=I.iterate S k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [scanIterate, I.scanStep_correct, ih]

/-- Undoing a disjoint temporary repair restores the stored prefix exactly. -/
theorem repair_restore {S R : Selection n} (h : Disjoint S R) : (S ∪ R) \ R=S := by
  classical
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_union]
  constructor
  · rintro ⟨hi,hn⟩
    exact hi.resolve_right hn
  · intro hi
    exact ⟨Or.inl hi,fun hr => Finset.disjoint_left.mp h hi hr⟩

end
end S2R.Instance
