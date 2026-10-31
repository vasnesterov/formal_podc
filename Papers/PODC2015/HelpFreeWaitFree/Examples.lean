import Papers.PODC2015.HelpFreeWaitFree.ExactOrder

/-!
# Examples of (non-)exact order types: queue and stack

[CPT15] states, after Definition 4.5.1, that the FIFO queue and the LIFO stack are exact order
types. We check both claims against `ExactOrder` / `ExactOrderStrong`:

* `queue_exactOrderStrong` — the queue is an exact order type, even in the paper's literal
  (strong) form, with the paper's witnesses `op = enq 1`, `W = enq 2, enq 2, …`,
  `R = deq, deq, …`, `m = n + 1`, and the distinguishing operation the `(n+1)`-st dequeue.
* `stack_exists_equal` — for the stack, for *every* choice of `op`, `W`, `R`, `n`, `m` there are
  executions in `W(n+1) ∘ (R(m) + op?)` and `W(n) ∘ op ∘ (R(m) + W_{n+1}?)` in which all operations
  of `R(m)` return the same results. Hence `stack_not_exactOrder`: the stack is **not** an exact
  order type, refuting the paper's claim (this is Theorem 1 of V. Aksenov, P. Kuznetsov,
  A. Shalyto, *On helping and stacks*, NETYS 2018).

The key step for the stack (`stack_insert`): if a stack differs from another one only below a
prefix `Z` by one operation `w` applied to the rest, then the operation `w` can be inserted into
any sequence of operations run on the second stack, exactly when the prefix `Z` is exhausted, so
that the two runs return the same results.
-/

namespace Podc.HelpFreeWaitFree

open Cslib.SharedMemory

/-! ## General facts about `taggedResps` and `OptIns` -/

section General

variable {α : Type} {A : ObjSpec}

lemma mem_optIns_self (xs : List α) (x : α) : xs ∈ OptIns xs x := Or.inl rfl

lemma cons_mem_optIns (xs : List α) (x : α) : x :: xs ∈ OptIns xs x :=
  Or.inr ⟨0, Nat.zero_le _, by simp⟩

lemma cons_mem_optIns_cons {xs ys : List α} {x : α} (y : α) (h : ys ∈ OptIns xs x) :
    y :: ys ∈ OptIns (y :: xs) x := by
  rcases h with rfl | ⟨k, hk, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k + 1, by simpa using hk, by simp⟩

lemma mem_optIns_nil {u : List α} {x : α} (h : u ∈ OptIns [] x) : u = [] ∨ u = [x] := by
  rcases h with rfl | ⟨k, hk, rfl⟩
  · exact Or.inl rfl
  · simp at hk; subst hk; simp

lemma mem_optIns_cons {u xs : List α} {x y : α} (h : u ∈ OptIns (y :: xs) x) :
    u = x :: y :: xs ∨ ∃ u' ∈ OptIns xs x, u = y :: u' := by
  rcases h with rfl | ⟨k, hk, rfl⟩
  · exact Or.inr ⟨xs, mem_optIns_self xs x, rfl⟩
  · rcases k with _ | k
    · exact Or.inl (by simp)
    · exact Or.inr ⟨xs.insertIdx k x, Or.inr ⟨k, by simpa using hk, rfl⟩, by simp⟩

@[simp] lemma tagged_nil (t : Bool) : tagged t ([] : List A.Op) = [] := rfl

@[simp] lemma tagged_cons (t : Bool) (o : A.Op) (os : List A.Op) :
    tagged t (o :: os) = (t, o) :: tagged t os := rfl

@[simp] lemma taggedResps_nil (q : A.State) : taggedResps A q [] = [] := rfl

@[simp] lemma taggedResps_cons_true (q : A.State) (o : A.Op) (l : List (Bool × A.Op)) :
    taggedResps A q ((true, o) :: l) = (A.δ q o).2 :: taggedResps A (A.δ q o).1 l := rfl

@[simp] lemma taggedResps_cons_false (q : A.State) (o : A.Op) (l : List (Bool × A.Op)) :
    taggedResps A q ((false, o) :: l) = taggedResps A (A.δ q o).1 l := rfl

/-- Untagged operations only move the state: their results are not collected. -/
lemma taggedResps_tagged_false_append (q : A.State) (os : List A.Op)
    (l : List (Bool × A.Op)) :
    taggedResps A q (tagged false os ++ l) = taggedResps A (A.runOps q os) l := by
  induction os generalizing q with
  | nil => rfl
  | cons o os ih => simp [ih]

lemma pre_succ (S : ℕ → α) (n : ℕ) : pre S (n + 1) = pre S n ++ [S n] := by
  simp [pre, List.range_succ]

lemma pre_const (c : α) (n : ℕ) : pre (fun _ => c) n = List.replicate n c := by
  simp [pre]

lemma mem_seqWFirst {op : A.Op} {W R : ℕ → A.Op} {n m : ℕ} {a : List (Bool × A.Op)} :
    a ∈ seqWFirst op W R n m ↔
      ∃ u ∈ OptIns (tagged true (pre R m)) (false, op), a = tagged false (pre W (n + 1)) ++ u :=
  Iff.rfl

lemma mem_seqOpFirst {op : A.Op} {W R : ℕ → A.Op} {n m : ℕ} {b : List (Bool × A.Op)} :
    b ∈ seqOpFirst op W R n m ↔
      ∃ u ∈ OptIns (tagged true (pre R m)) (false, W n),
        b = tagged false (pre W n) ++ (false, op) :: u :=
  Iff.rfl

end General

/-! ## The queue -/

/-- Operations of a FIFO queue of natural numbers. -/
inductive QOp
  /-- Enqueue a value. -/
  | enq (v : ℕ)
  /-- Dequeue the oldest value. -/
  | deq

/-- Sequential specification of a FIFO queue (the state lists the values, front first):
`enq v` appends `v` at the back and returns `none`; `deq` removes and returns the front value,
or returns `none` and leaves the empty queue unchanged. -/
def queueδ : List ℕ → QOp → List ℕ × Option ℕ
  | q, .enq v => (q ++ [v], none)
  | q, .deq => (q.tail, q.head?)

/-- The FIFO queue over `ℕ`, initially empty. -/
abbrev queueSpec : ObjSpec where
  State := List ℕ
  Op := QOp
  Resp := Option ℕ
  init := []
  δ := queueδ

lemma queue_runOps_enq (q : List ℕ) (v n : ℕ) :
    queueSpec.runOps q (List.replicate n (QOp.enq v)) = q ++ List.replicate n v := by
  induction n generalizing q with
  | zero => exact (List.append_nil q).symm
  | succ n ih =>
    rw [List.replicate_succ, ObjSpec.runOps_cons]
    exact (ih _).trans (by simp [queueSpec, queueδ, List.replicate_succ])

/-- `|q|` dequeues on a queue with front part `q` return the elements of `q`, even if one
enqueue is inserted somewhere among them (it goes to the back). -/
lemma queue_deqs (v : ℕ) (q r : List ℕ) (u : List (Bool × QOp))
    (hu : u ∈ OptIns (tagged (A := queueSpec) true (List.replicate q.length QOp.deq))
      (false, QOp.enq v)) :
    taggedResps queueSpec (q ++ r) u = q.map some := by
  induction q generalizing r u with
  | nil =>
    rcases mem_optIns_nil hu with rfl | rfl <;> rfl
  | cons a q ih =>
    rw [List.length_cons, List.replicate_succ, tagged_cons] at hu
    rcases mem_optIns_cons hu with rfl | ⟨u', hu', rfl⟩
    · rw [taggedResps_cons_false, taggedResps_cons_true]
      show some a :: taggedResps queueSpec ((q ++ r) ++ [v]) _ = _
      rw [List.append_assoc, ih (r ++ [v]) _ (mem_optIns_self _ _), List.map_cons]
    · rw [taggedResps_cons_true]
      show some a :: taggedResps queueSpec (q ++ r) u' = _
      rw [ih r u' hu', List.map_cons]

/-- Examples after Definition 4.5.1 of [CPT15]: the queue is an exact order type (in the
paper's literal form). Witnesses: `op = enq 1`, `W = enq 2, enq 2, …`, `R = deq, deq, …`,
`m = n + 1`; the `(n+1)`-st dequeue returns `2` in `W(n+1) ∘ (R(m) + op?)` and `1` in
`W(n) ∘ op ∘ (R(m) + W_{n+1}?)`. -/
theorem queue_exactOrderStrong : ExactOrderStrong queueSpec := by
  refine ⟨QOp.enq 1, fun _ => QOp.enq 2, fun _ => QOp.deq, fun n => ⟨n + 1, by omega, n, by omega,
    fun a ha b hb => ?_⟩⟩
  obtain ⟨u, hu, rfl⟩ := mem_seqWFirst.1 ha
  obtain ⟨u', hu', rfl⟩ := mem_seqOpFirst.1 hb
  rw [pre_const] at hu hu'
  have hA := queue_deqs 1 (List.replicate (n + 1) 2) [] u (by simpa using hu)
  have hB := queue_deqs 2 (List.replicate n 2 ++ [1]) [] u' (by simpa using hu')
  rw [taggedResps_tagged_false_append, taggedResps_tagged_false_append, pre_const, pre_const,
    queue_runOps_enq, queue_runOps_enq, taggedResps_cons_false]
  have e : (queueSpec.δ ([] ++ List.replicate n 2) (QOp.enq 1)).1 =
      List.replicate n 2 ++ [1] ++ [] := by
    simp [queueSpec, queueδ]
  rw [e, hB, show queueSpec.init ++ List.replicate (n + 1) 2 = List.replicate (n + 1) 2 ++ [] from
    by simp, hA]
  simp

/-- The queue is an exact order type (Definition 4.5.1 in the "some result differs" form). -/
theorem queue_exactOrder : ExactOrder queueSpec := queue_exactOrderStrong.exactOrder

/-! ## The stack -/

/-- Operations of a LIFO stack of natural numbers. -/
inductive SOp
  /-- Push a value. -/
  | push (v : ℕ)
  /-- Pop the top value. -/
  | pop

/-- Sequential specification of a LIFO stack (the state lists the values, top first):
`push v` puts `v` on top and returns `none`; `pop` removes and returns the top value, or returns
`none` and leaves the empty stack unchanged. -/
def stackδ : List ℕ → SOp → List ℕ × Option ℕ
  | s, .push v => (v :: s, none)
  | s, .pop => (s.tail, s.head?)

/-- The LIFO stack over `ℕ`, initially empty. -/
abbrev stackSpec : ObjSpec where
  State := List ℕ
  Op := SOp
  Resp := Option ℕ
  init := []
  δ := stackδ

/-- If the stack `Z ++ stackδ s w` (top first) differs from `Z ++ s` only by the operation `w`
applied below the prefix `Z`, then any sequence `rs` run on the first stack returns the same
results as `rs` with `w` inserted (exactly when the prefix `Z` is consumed) run on the second. -/
lemma stack_insert (w : SOp) (s : List ℕ) (rs : List SOp) (Z : List ℕ) :
    ∃ t ∈ OptIns (tagged (A := stackSpec) true rs) (false, w),
      taggedResps stackSpec (Z ++ (stackδ s w).1) (tagged true rs) =
        taggedResps stackSpec (Z ++ s) t := by
  induction rs generalizing Z with
  | nil => exact ⟨[], mem_optIns_self _ _, rfl⟩
  | cons r rs ih =>
    rcases Z with _ | ⟨z, Z⟩
    · exact ⟨_, cons_mem_optIns _ _, rfl⟩
    · rcases r with c | _
      · obtain ⟨t, ht, he⟩ := ih (c :: z :: Z)
        exact ⟨_, cons_mem_optIns_cons _ ht, by
          rw [tagged_cons, taggedResps_cons_true, taggedResps_cons_true]; exact congrArg _ he⟩
      · obtain ⟨t, ht, he⟩ := ih Z
        exact ⟨_, cons_mem_optIns_cons _ ht, by
          rw [tagged_cons, taggedResps_cons_true, taggedResps_cons_true]; exact congrArg _ he⟩

/-- For the stack, *every* choice of `op`, `W`, `R`, `n`, `m` admits an execution in
`W(n+1) ∘ (R(m) + op?)` and one in `W(n) ∘ op ∘ (R(m) + W_{n+1}?)` in which all operations of
`R(m)` return the same results (Aksenov, Kuznetsov, Shalyto 2018, proof of Theorem 1). -/
theorem stack_exists_equal (op : SOp) (W R : ℕ → SOp) (n m : ℕ) :
    ∃ a ∈ seqWFirst (A := stackSpec) op W R n m, ∃ b ∈ seqOpFirst (A := stackSpec) op W R n m,
      taggedResps stackSpec stackSpec.init a = taggedResps stackSpec stackSpec.init b := by
  set s := stackSpec.runOps stackSpec.init (pre W n) with hs
  set rs := pre R m
  -- reduce both sides to runs of `R(m)` (with an insertion) from the states after the prefixes
  suffices h : ∃ u ∈ OptIns (tagged (A := stackSpec) true rs) (false, op),
      ∃ u' ∈ OptIns (tagged (A := stackSpec) true rs) (false, W n),
        taggedResps stackSpec (stackδ s (W n)).1 u = taggedResps stackSpec (stackδ s op).1 u' by
    obtain ⟨u, hu, u', hu', he⟩ := h
    refine ⟨_, mem_seqWFirst.2 ⟨u, hu, rfl⟩, _, mem_seqOpFirst.2 ⟨u', hu', rfl⟩, ?_⟩
    rw [taggedResps_tagged_false_append, taggedResps_tagged_false_append, pre_succ,
      ObjSpec.runOps_append, taggedResps_cons_false, ← hs]
    exact he
  rcases op with x | _ <;> rcases hW : W n with y | _
  · -- `op = push x`, `W_{n+1} = push y`: insert `push y` when `x` is popped
    obtain ⟨t, ht, he⟩ := stack_insert (.push y) s rs [x]
    exact ⟨_, cons_mem_optIns _ _, t, ht, he⟩
  · -- `op = push x`, `W_{n+1} = pop`: insert `pop` when `x` is popped
    obtain ⟨t, ht, he⟩ := stack_insert .pop s rs [x]
    exact ⟨_, cons_mem_optIns _ _, t, ht, he⟩
  · -- `op = pop`, `W_{n+1} = push y`: insert `pop` when `y` is popped
    obtain ⟨t, ht, he⟩ := stack_insert .pop s rs [y]
    exact ⟨t, ht, _, cons_mem_optIns _ _, he.symm⟩
  · -- `op = pop`, `W_{n+1} = pop`: two pops in either order
    exact ⟨_, cons_mem_optIns _ _, _, cons_mem_optIns _ _, rfl⟩

/-- The paper claims (after Definition 4.5.1 of [CPT15]) that the stack is an exact order type;
this is false (Aksenov, Kuznetsov, Shalyto 2018, Theorem 1). -/
theorem stack_not_exactOrder : ¬ ExactOrder stackSpec := by
  rintro ⟨op, W, R, h⟩
  obtain ⟨m, -, hm⟩ := h 0
  obtain ⟨a, ha, b, hb, he⟩ := stack_exists_equal op W R 0 m
  exact hm a ha b hb he

/-- The stack is not an exact order type in the paper's literal form either. -/
theorem stack_not_exactOrderStrong : ¬ ExactOrderStrong stackSpec :=
  fun h => stack_not_exactOrder h.exactOrder

end Podc.HelpFreeWaitFree
