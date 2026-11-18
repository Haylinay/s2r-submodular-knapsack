import S2R.Main
import S2R.RuntimeRefinement

/-! Arithmetic bounds for sorting and greedy query batches used by the
streamed implementation. -/
namespace S2R.OrderedSweep
noncomputable section
variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

theorem sortTicks_quadratic (xs : List α) :
    sortTicks r xs ≤ xs.length^2+xs.length+1 := by
  induction xs with
  | nil => simp [sortTicks]
  | cons a xs ih =>
    have h := insertTicks_bound r a (xs.insertionSort r)
    rw [List.length_insertionSort] at h
    simp only [sortTicks, List.length_cons]
    nlinarith

end
end S2R.OrderedSweep

namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

theorem available_card_add (S : Selection n) : (I.available S).card+S.card ≤ n := by
  classical
  have hsub : I.available S ⊆ Finset.univ \ S := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,(I.mem_available.mp hi).1⟩
  have hc := Finset.card_le_card hsub
  have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  simp only [Finset.card_univ, Fintype.card_fin] at he
  omega

/-- At the k-th greedy step, at least k+1 items are selected unless the
path has already terminated. A terminated step only queries its base set. -/
theorem stepQueries_card_at_seed (a : Ground n) (k : Fin n) :
    (I.stepQueries (I.iterate {a} k.val)).card+k.val ≤ n := by
  classical
  by_cases he : I.available (I.iterate {a} k.val)=∅
  · have hk : k.val+1 ≤ n := k.isLt
    simpa [stepQueries, he, Nat.add_comm] using hk
  · have hc := I.active_card k.val he
    simp only [Finset.card_singleton] at hc
    have ha := I.available_card_add (I.iterate {a} k.val)
    have h₁ := Finset.card_insert_le (I.iterate {a} k.val)
      ((I.available (I.iterate {a} k.val)).image (fun i => insert i (I.iterate {a} k.val)))
    have h₂ := Finset.card_image_le (s := I.available (I.iterate {a} k.val))
      (f := fun i => insert i (I.iterate {a} k.val))
    change (I.stepQueries (I.iterate {a} k.val)).card ≤ _ at h₁
    omega

theorem twice_sum_fin_indices (m : ℕ) :
    2*(∑ k : Fin m, k.val)+m=m*m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Fin.val_succ, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, zero_add]
    nlinarith

theorem greedyQueryCount_triangular (a : Ground n) :
    2*(∑ k : Fin n, (I.stepQueries (I.iterate {a} k.val)).card) ≤ n*(n+1) := by
  have hs : (∑ k : Fin n, ((I.stepQueries (I.iterate {a} k.val)).card+k.val)) ≤ n*n := by
    calc
      _ ≤ ∑ _k : Fin n, n := Finset.sum_le_sum (fun k _ => I.stepQueries_card_at_seed a k)
      _ = _ := by simp
  rw [Finset.sum_add_distrib] at hs
  have hi := twice_sum_fin_indices n
  nlinarith

end
end S2R.Instance
