import S2R.SharperBounds

/-! Reuse the scalar cost already maintained during greedy construction.
The snapshot charge includes writing its cost cell. This removes the later
full membership-array summations, without changing a greedy decision. -/
namespace S2R.Instance
noncomputable section
open S2R.OrderedSweep S2R.RAM
variable {n : ℕ} (I : Instance n)

def pathWithCosts (S : Selection n) (C : ℝ) : ℕ → Run (List (Selection n × ℝ))
  | 0 => ⟨[(S,C)],2*n+2⟩
  | k+1 =>
    let next := I.cachedChoose S C
    let state := match next.choice with
      | none => (S,C)
      | some i => (insert i S,C+I.cost i)
    let r := pathWithCosts state.1 state.2 k
    ⟨(S,C)::r.value,r.operations+next.operations+(2*n+2)+5⟩

theorem pathWithCosts_refines (S : Selection n) (C : ℝ)
    (hC : C=I.totalCost S) (k : ℕ) :
    I.pathWithCosts S C k =
      ⟨(I.pathRun S k).value.map (fun T => (T,I.totalCost T)),
        (I.pathRun S k).operations⟩ := by
  induction k generalizing S C with
  | zero => simp [pathWithCosts, pathRun, hC]
  | succ k ih =>
    rw [pathWithCosts, I.cachedChoose_correct S C hC]
    unfold pathRun
    cases he : (I.scanChoose S).choice with
    | none =>
      simp only
      rw [ih S C hC]
      simp [he,hC]
    | some i =>
      have hc : I.choose S=some i := by rw [← I.scanChoose_correct]; exact he
      have hi := (I.mem_available.mp (I.choose_spec hc).1).1
      have hcost : C+I.cost i=I.totalCost (insert i S) := by
        rw [I.totalCost_insert hi,hC]; ring
      simp only
      rw [ih (insert i S) (C+I.cost i) hcost]
      simp [he,hC]

def reuseCache (a : Ground n) : Run (PathCache n) := by
  classical
  let p := I.pathWithCosts {a} (I.cost a) n
  let states := fun t : Fin (n+1) => (p.value.getD t.val (∅,0)).1
  let costs := fun t : Fin (n+1) => (p.value.getD t.val (∅,0)).2
  let absent := fun i : Ground n => countTrue
    (List.ofFn (fun t : Fin (n+1) => decide (i ∉ states t)))
  exact ⟨⟨states,costs,fun i => (absent i).value⟩,
    p.operations+(∑ i, (absent i).operations)⟩

theorem reuseCache_correct (a : Ground n) :
    (I.reuseCache a).value=I.referenceCache a := by
  classical
  have hp : (I.pathWithCosts {a} (I.cost a) n).value =
      List.ofFn (fun t : Fin (n+1) => (I.prefixSet a t,I.totalCost (I.prefixSet a t))) := by
    rw [I.pathWithCosts_refines _ _ (I.totalCost_singleton a).symm,
      I.pathRun_correct,List.map_ofFn]
    rfl
  have hg (t : Fin (n+1)) :
      (I.pathWithCosts {a} (I.cost a) n).value.getD t.val (∅,0)=
        (I.prefixSet a t,I.totalCost (I.prefixSet a t)) := by
    rw [hp]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,dif_pos t.isLt,
      Option.getD_some]
  simp only [reuseCache, hg, countTrue_correct, filter_ofFn_bool]
  rfl

theorem reuseCache_operations (a : Ground n) :
    (I.reuseCache a).operations=(I.pathRun {a} n).operations+
      (∑ i : Ground n, (I.absenceRun a i).operations) := by
  classical
  simp only [reuseCache, I.pathWithCosts_refines _ _ (I.totalCost_singleton a).symm,
    countTrue_operations,List.length_ofFn,I.absenceRun_operations]

def reuseSeed (order : List (Ground n)) (a : Ground n) : Run ℝ :=
  let cache := I.reuseCache a
  let singles := I.runRow order cache.value none
  let rows := fun i : Ground n => I.runRow order cache.value (some i)
  let records := cache.value.states (Fin.last n)::
    (singles.value ++ I.itemList.flatMap (fun i => (rows i).value))
  let best := maxValues I.value records
  ⟨best.value,cache.operations+singles.operations+(∑ i, (rows i).operations)+best.operations+20⟩

theorem reuseSeed_value (a : Ground n) :
    (I.reuseSeed I.costSorted a).value=(I.runSeed I.costSorted a).value := by
  simp only [reuseSeed,runSeed,I.reuseCache_correct,I.makeCache_correct]

def reuseImplementationRun : Run ℝ := by
  classical
  let seeds := fun a : Ground n => if I.Feasible {a} then I.reuseSeed I.costSorted a else ⟨0,0⟩
  exact ⟨(maxValues (fun a => (seeds a).value) I.itemList).value,
    20*(n+1)+4*sortTicks I.costOrder I.itemList+(∑ a : Ground n, ((seeds a).operations+4))⟩

theorem reuseImplementationRun_correct : I.reuseImplementationRun.value=I.output := by
  rw [← I.implementationRun_correct]
  simp only [reuseImplementationRun,implementationRun,I.reuseSeed_value]
  congr 2
  funext a
  split <;> simp [I.reuseSeed_value]

end
end S2R.Instance
