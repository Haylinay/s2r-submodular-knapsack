import S2R.Analysis

/-! Independent word-space semantics for scoped, sequential RAM workspaces.
`hold w p` allocates w scalar cells, runs p, and releases those same cells.
`seq` reuses released workspace: its peak is a maximum, not a sum. Lists in
this file describe executions, not extra arrays stored by the RAM program.
An exact real, an index, a Boolean or a pointer occupies one abstract word.
This is not a statement about Lean objects, bits, or oracle-private memory. -/
namespace S2R.Memory

inductive Event where
  | alloc : ℕ → Event
  | release : ℕ → Event

inductive Plan where
  | done : Plan
  | hold : ℕ → Plan → Plan
  | seq : Plan → Plan → Plan

def Plan.events : Plan → List Event
  | .done => []
  | .hold w p => .alloc w :: (p.events ++ [.release w])
  | .seq p q => p.events ++ q.events

def execute : List Event → ℕ → Option ℕ
  | [], used => some used
  | .alloc w :: es, used => execute es (used+w)
  | .release w :: es, used => if w ≤ used then execute es (used-w) else none

theorem execute_append (es fs : List Event) (used : ℕ) :
    execute (es++fs) used=(execute es used).bind (execute fs) := by
  induction es generalizing used with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | alloc w => simpa only [List.cons_append,execute] using ih (used+w)
    | release w =>
      simp only [List.cons_append,execute]
      split
      · exact ih _
      · rfl

/-- Every allocation schedule is balanced; every release is legal, even
when executed with an arbitrary pre-existing live heap. -/
theorem execute_balanced (p : Plan) (base : ℕ) :
    execute p.events base=some base := by
  induction p generalizing base with
  | done => rfl
  | hold w p ih =>
    simp only [Plan.events,execute,execute_append,ih,Option.bind_some]
    simp [execute]
  | seq p q ihp ihq =>
    simp [Plan.events,execute_append,ihp,ihq]

def Plan.peak : Plan → ℕ
  | .done => 0
  | .hold w p => w+p.peak
  | .seq p q => max p.peak q.peak

/-- Live occupancy at any program point, including entry/exit and the
interior of every allocation and every sequential phase. -/
inductive Live : Plan → ℕ → ℕ → Prop where
  | boundary (p : Plan) (base : ℕ) : Live p base base
  | inside {p : Plan} {base w used : ℕ} :
      Live p (base+w) used → Live (.hold w p) base used
  | first {p q : Plan} {base used : ℕ} :
      Live p base used → Live (.seq p q) base used
  | second {p q : Plan} {base used : ℕ} :
      Live q base used → Live (.seq p q) base used

theorem live_bounds {p : Plan} {base used : ℕ} (h : Live p base used) :
    base ≤ used ∧ used ≤ base+p.peak := by
  induction h with
  | boundary p base => omega
  | inside h ih => simp only [Plan.peak]; omega
  | first h ih => simp only [Plan.peak]; omega
  | second h ih => simp only [Plan.peak]; omega

theorem peak_attained (p : Plan) (base : ℕ) : Live p base (base+p.peak) := by
  induction p generalizing base with
  | done => simpa [Plan.peak] using Live.boundary Plan.done base
  | hold w p ih =>
    simpa [Plan.peak,Nat.add_assoc] using Live.inside (ih (base+w))
  | seq p q ihp ihq =>
    rcases le_total p.peak q.peak with h | h
    · simpa [Plan.peak,max_eq_right h] using
        (Live.second (p:=p) (ihq base))
    · simpa [Plan.peak,max_eq_left h] using
        (Live.first (q:=q) (ihp base))

/-- Every finite prefix of the actual allocate/release event list runs
without underflow and its occupancy is one of the live program points. -/
theorem execute_prefix_live (p : Plan) (base k : ℕ) :
    ∃ used, execute (p.events.take k) base=some used ∧ Live p base used := by
  induction p generalizing base k with
  | done => exact ⟨base,by simp [Plan.events,execute],Live.boundary _ _⟩
  | hold w p ih =>
    cases k with
    | zero => exact ⟨base,rfl,Live.boundary _ _⟩
    | succ k =>
      by_cases hk : k ≤ p.events.length
      · have he : (p.events++[Event.release w]).take k=p.events.take k := by
          rw [List.take_append_eq_append_take]
          simp [Nat.sub_eq_zero_of_le hk]
        obtain ⟨used,hu,hl⟩ := ih (base+w) k
        refine ⟨used,?_,Live.inside hl⟩
        simpa only [Plan.events,List.take_succ_cons,execute,he] using hu
      · have hn : (Plan.hold w p).events.length ≤ k+1 := by
          simp only [Plan.events,List.length_cons,List.length_append,List.length_nil]
          omega
        exact ⟨base,by rw [List.take_of_length_le hn,execute_balanced],Live.boundary _ _⟩
  | seq p q ihp ihq =>
    by_cases hk : k ≤ p.events.length
    · obtain ⟨used,hu,hl⟩ := ihp base k
      refine ⟨used,?_,Live.first hl⟩
      simpa [Plan.events,List.take_append_eq_append_take,Nat.sub_eq_zero_of_le hk] using hu
    · obtain ⟨used,hu,hl⟩ := ihq base (k-p.events.length)
      refine ⟨used,?_,Live.second hl⟩
      simp only [Plan.events,List.take_append_eq_append_take,
        List.take_of_length_le (show p.events.length ≤ k by omega),
        execute_append,execute_balanced,Option.bind_some]
      exact hu

theorem execute_prefix_bound (p : Plan) (base k : ℕ) :
    ∃ used, execute (p.events.take k) base=some used ∧
      base ≤ used ∧ used ≤ base+p.peak := by
  obtain ⟨used,hu,hl⟩ := execute_prefix_live p base k
  exact ⟨used,hu,live_bounds hl⟩

structure Run (α : Type*) where
  value : α
  plan : Plan

def pure (a : α) : Run α := ⟨a,.done⟩
def scope (words : ℕ) (r : Run α) : Run α := ⟨r.value,.hold words r.plan⟩
def before (p : Plan) (r : Run α) : Run α := ⟨r.value,.seq p r.plan⟩

/-- Iterative fold. The scalar accumulator is held by the surrounding
scope; the workspace of one body is released before the next iteration. -/
def fold (f : α → β → Run β) : List α → β → Run β
  | [], b => pure b
  | a::as, b =>
    let r := f a b
    let rest := fold f as r.value
    ⟨rest.value,.seq r.plan rest.plan⟩

theorem fold_value (f : α → β → Run β) (xs : List α) (b : β) :
    (fold f xs b).value=xs.foldl (fun z x => (f x z).value) b := by
  induction xs generalizing b with
  | nil => rfl
  | cons a as ih => simpa only [fold,List.foldl_cons] using ih (f a b).value

theorem fold_peak (f : α → β → Run β) (xs : List α) (b : β) (K : ℕ)
    (h : ∀ x ∈ xs, ∀ z, (f x z).plan.peak ≤ K) :
    (fold f xs b).plan.peak ≤ K := by
  induction xs generalizing b with
  | nil => exact Nat.zero_le _
  | cons a as ih =>
    exact max_le (h a List.mem_cons_self b)
      (ih _ (fun x hx z => h x (List.mem_cons_of_mem a hx) z))

end S2R.Memory
