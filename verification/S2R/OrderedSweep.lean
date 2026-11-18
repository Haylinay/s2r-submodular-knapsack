import S2R.Analysis
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Finset.Fin

/-! Costed insertion sorting and an amortized monotone sweep. A tick is a
bounded block of real comparisons, arithmetic, or record operations. The
constant-sized blocks are expanded conservatively in AuxiliaryComplexity. -/
namespace S2R.OrderedSweep
noncomputable section

structure Cut where
  taken : List ℝ
  rest : List ℝ
  ticks : ℕ

def consume (q : ℝ) : List ℝ → Cut
  | [] => ⟨[], [], 1⟩
  | x::xs => if x ≤ q then
      let z := consume q xs
      ⟨x::z.taken, z.rest, z.ticks+2⟩
    else ⟨[], x::xs, 1⟩

theorem consume_append (q : ℝ) (xs : List ℝ) :
    (consume q xs).taken ++ (consume q xs).rest = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [consume]
    split <;> simp_all

theorem consume_length (q : ℝ) (xs : List ℝ) :
    (consume q xs).taken.length+(consume q xs).rest.length=xs.length := by
  simpa using congrArg List.length (consume_append q xs)

theorem consume_ticks (q : ℝ) (xs : List ℝ) :
    (consume q xs).ticks ≤ 2*(consume q xs).taken.length+1 := by
  induction xs with
  | nil => simp [consume]
  | cons x xs ih =>
    simp only [consume]
    split <;> simp_all <;> omega

theorem consume_taken (q : ℝ) (xs : List ℝ) :
    ∀ x ∈ (consume q xs).taken, x ≤ q := by
  induction xs with
  | nil => simp [consume]
  | cons x xs ih =>
    simp only [consume]
    split <;> simp_all

theorem consume_rest (q : ℝ) {xs : List ℝ} (h : xs.Sorted (· ≤ ·)) :
    ∀ x ∈ (consume q xs).rest, q < x := by
  induction xs with
  | nil => simp [consume]
  | cons x xs ih =>
    simp only [consume]
    split
    · exact ih h.of_cons
    next hn =>
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact lt_of_not_ge hn
      · exact (lt_of_not_ge hn).trans_le (List.rel_of_sorted_cons h y hy)

theorem consume_rest_sorted (q : ℝ) {xs : List ℝ} (h : xs.Sorted (· ≤ ·)) :
    (consume q xs).rest.Sorted (· ≤ ·) := by
  have hp := h
  rw [← consume_append q xs] at hp
  exact (List.pairwise_append.mp hp).2.1

theorem consume_filter (q : ℝ) {xs : List ℝ} (h : xs.Sorted (· ≤ ·)) :
    (xs.filter (fun x => decide (x ≤ q))).length=(consume q xs).taken.length := by
  conv_lhs => rw [← consume_append q xs, List.filter_append]
  have ht : (consume q xs).taken.filter (fun x => decide (x ≤ q))=(consume q xs).taken :=
    List.filter_eq_self.mpr (by simpa using consume_taken q xs)
  have hr : (consume q xs).rest.filter (fun x => decide (x ≤ q))=[] :=
    List.filter_eq_nil_iff.mpr (by simpa using fun x hx => (consume_rest q h x hx).not_le)
  rw [ht, hr, List.append_nil]

theorem filter_after_consume {q q' : ℝ} (hq : q ≤ q') (xs : List ℝ) :
    (xs.filter (fun x => decide (x ≤ q'))).length =
      (consume q xs).taken.length+((consume q xs).rest.filter (fun x => decide (x ≤ q'))).length := by
  conv_lhs => rw [← consume_append q xs]
  rw [List.filter_append, List.length_append]
  congr 1
  rw [List.filter_eq_self.mpr]
  simpa using fun x hx => (consume_taken q xs x hx).trans hq

structure Sweep where
  answers : List ℕ
  rest : List ℝ
  ticks : ℕ

def sweep : List ℝ → List ℝ → ℕ → Sweep
  | [], xs, _ => ⟨[], xs, 0⟩
  | q::qs, xs, offset =>
    let z := consume q xs
    let r := sweep qs z.rest (offset+z.taken.length)
    ⟨(offset+z.taken.length)::r.answers, r.rest, z.ticks+r.ticks+3⟩

/-- Repeated failed tests are charged once per query; successful tests can
consume each path entry only once over the entire row. -/
theorem sweep_ticks (qs xs : List ℝ) (offset : ℕ) :
    (sweep qs xs offset).ticks+2*(sweep qs xs offset).rest.length ≤
      4*qs.length+2*xs.length := by
  induction qs generalizing xs offset with
  | nil => simp [sweep]
  | cons q qs ih =>
    have hr := ih (consume q xs).rest (offset+(consume q xs).taken.length)
    have hc := consume_ticks q xs
    have hl := consume_length q xs
    simp only [sweep, List.length_cons]
    omega

theorem sweep_correct {qs xs : List ℝ} (hq : qs.Sorted (· ≤ ·))
    (hx : xs.Sorted (· ≤ ·)) (offset : ℕ) :
    (sweep qs xs offset).answers =
      qs.map (fun q => offset+(xs.filter (fun x => decide (x ≤ q))).length) := by
  induction qs generalizing xs offset with
  | nil => rfl
  | cons q qs ih =>
    simp only [sweep, List.map_cons]
    rw [ih hq.of_cons (consume_rest_sorted q hx)]
    congr 1
    · rw [consume_filter q hx]
    · apply List.map_congr_left
      intro q' hq'
      have he := filter_after_consume (List.rel_of_sorted_cons hq q' hq') xs
      omega

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

def insertTicks (a : α) : List α → ℕ
  | [] => 1
  | b::bs => if r a b then 2 else insertTicks a bs+2

def sortTicks : List α → ℕ
  | [] => 1
  | a::as => sortTicks as+insertTicks r a (as.insertionSort r)+1

theorem insertTicks_bound (a : α) (xs : List α) : insertTicks r a xs ≤ 2*xs.length+1 := by
  induction xs with
  | nil => simp [insertTicks]
  | cons x xs ih => simp only [insertTicks]; split <;> simp_all <;> omega

/-- Cost follows the very same recursive calls as `List.insertionSort` and
`List.orderedInsert`; sorting only n individual costs is sufficient. -/
theorem sortTicks_bound (xs : List α) : sortTicks r xs ≤ (xs.length+1)^2 := by
  induction xs with
  | nil => simp [sortTicks]
  | cons a xs ih =>
    have h := insertTicks_bound r a (xs.insertionSort r)
    rw [List.length_insertionSort] at h
    simp only [sortTicks, List.length_cons]
    nlinarith

def initialCount {m : ℕ} (P : Fin m → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter P).card

theorem initialCount_spec {m : ℕ} (P : Fin m → Prop)
    (hdown : ∀ i j, i ≤ j → P j → P i) (t : Fin m) :
    P t ↔ t.val < initialCount P := by
  classical
  constructor
  · intro ht
    have hs : Finset.Iic t ⊆ Finset.univ.filter P := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdown i t (Finset.mem_Iic.mp hi) ht⟩
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iic] at hc
    exact hc
  · intro ht
    by_contra hn
    have hs : Finset.univ.filter P ⊆ Finset.Iio t := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra hh
      exact hn (hdown t i (le_of_not_gt hh) (Finset.mem_filter.mp hi).2)
    have hc := Finset.card_le_card hs
    rw [Fin.card_Iio] at hc
    exact (not_lt_of_ge hc) ht

theorem initialCount_le {m : ℕ} (P : Fin m → Prop) : initialCount P ≤ m := by
  classical
  simpa [initialCount] using (Finset.univ.filter P).card_le_univ

theorem filter_ofFn_length {m : ℕ} (f : Fin m → ℝ) (q : ℝ) :
    ((List.ofFn f).filter (fun x => decide (x ≤ q))).length =
      initialCount (fun t => f t ≤ q) := by
  classical
  rw [List.ofFn_eq_map, List.filter_map, List.length_map]
  let L := (List.finRange m).filter (fun t => decide (f t ≤ q))
  have hn : L.Nodup := (List.nodup_finRange m).filter _
  have he : L.toFinset=Finset.univ.filter (fun t => f t ≤ q) := by
    ext i
    simp [L]
  change L.length = _
  rw [← List.toFinset_card_of_nodup hn, he]
  rfl

end
end S2R.OrderedSweep
