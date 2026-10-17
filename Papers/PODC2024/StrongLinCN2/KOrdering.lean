import Podc.StrongLin.Basic

/-!
# `k`-ordering objects (Definition 11) and the examples of Section 5

Attiya, Castañeda and Enea (PODC 2024), Section 5. Lemma 12 reduces `k`-set agreement among `n`
processes to a lock-free strongly-linearizable implementation `A` of a *`k`-ordering* object:
process `p_i` runs its *proposal sequence* `prop_i` on `A`, takes a snapshot of `A`'s base
objects, locally simulates its *decision sequence* `dec_i` solo, and decides the input of process
`d(i, responses)`. Definition 11 asks that for every sequential execution `α` containing some
complete `prop_j`, the decisions lie in a set `S_α` of `k` processes, for every extension
`α · α' · β_i` in which `p_i` completed `prop_i` (in `α · α'`) and `β_i` consists of `dec_i`.

We formalize, over a *nondeterministic* sequential specification (`NSpec`), with sequential
histories `List (Fin n × Op × Resp)` (process, operation, response):

* `KOrdering` — Definition 11 as stated in the paper;
* `KOrderingI` — the variant that the proof of Lemma 12 actually needs: in the proof,
  `f(F_i) = α · α' · γ` where `γ` is produced by `p_i`'s solo simulation of `dec_i`, but the
  strong linearization function `f` may also linearize, inside `γ`, the operations of other
  processes that are pending in `E_i*` (their next operation of `prop_j`). The paper writes
  `f(F_i) = α · α' · β_i` with `invs(β_i) = dec_i`, ignoring them. Also, validity only needs the
  chosen process `ℓ` to have *started* (its input is written before its first operation), and
  the paper's own stuttering-queue example only provides that.
* `KOrderingW` — a common weakening of both (`KOrdering.toW`, `KOrderingI.toW`).

Results:
* `queue_kOrdering`, `queue_kOrderingI`: queues are 1-ordering in both senses (the paper's
  example; non-vacuity).
* `ooo_not_kOrderingW`: the paper's sequences for `k`-out-of-order queues
  (`prop_i = enq(i)`, `dec_i = deq`) do **not** witness 2-ordering (for `n = 3`), for any `d`,
  in either sense: when `α` contains fewer than `k` enqueues, `α'` contributes to the `k` oldest
  items. The claim "`k`-out-of-order queues are `k`-ordering" in Section 5 is still true (see below); only
  the paper's witness sequences are wrong.
* `ooo_kOrderingI`: repaired with `prop_i = enq(i)^k` (`k` enqueues per process), `k`-out-of-order
  queues are `k`-ordering, even in the strong sense `KOrderingI`.
* `stack_not_kOrderingI`: with the paper's sequences for stacks (`prop_i = push(i)`,
  `dec_i = pop^{n+1}`), no `d` satisfies `KOrderingI` (for `n = 3`): the gap in the proof of
  Lemma 12 is not repairable this way for stacks.
* `stack_kOrdering`: under Definition 11 as stated, the paper's stack example is correct.
-/

namespace StrongLinCN2.KOrd

open Cslib.SharedMemory

variable {Op Resp : Type} {n : ℕ}

/-- Sequential histories: (process, operation, response). -/
abbrev SeqH (Op Resp : Type) (n : ℕ) := List (Fin n × Op × Resp)

/-- The operation/response sequence of a sequential history. -/
def ops (l : SeqH Op Resp n) : List (Op × Resp) := l.map Prod.snd

/-- `invs(l | j)`. -/
def invs (l : SeqH Op Resp n) (j : Fin n) : List Op :=
  (l.filter (fun y => y.1 = j)).map (fun y => y.2.1)

/-- `resps(l | j)`. -/
def resps (l : SeqH Op Resp n) (j : Fin n) : List Resp :=
  (l.filter (fun y => y.1 = j)).map (fun y => y.2.2)

@[simp] lemma invs_nil (j : Fin n) : invs ([] : SeqH Op Resp n) j = [] := rfl
@[simp] lemma resps_nil (j : Fin n) : resps ([] : SeqH Op Resp n) j = [] := rfl

@[simp] lemma invs_append (l l' : SeqH Op Resp n) (j : Fin n) :
    invs (l ++ l') j = invs l j ++ invs l' j := by simp [invs]

@[simp] lemma resps_append (l l' : SeqH Op Resp n) (j : Fin n) :
    resps (l ++ l') j = resps l j ++ resps l' j := by simp [resps]

@[simp] lemma invs_cons (y : Fin n × Op × Resp) (l : SeqH Op Resp n) (j : Fin n) :
    invs (y :: l) j = (if y.1 = j then [y.2.1] else []) ++ invs l j := by
  simp only [invs, List.filter_cons]; split_ifs <;> simp_all

@[simp] lemma resps_cons (y : Fin n × Op × Resp) (l : SeqH Op Resp n) (j : Fin n) :
    resps (y :: l) j = (if y.1 = j then [y.2.2] else []) ++ resps l j := by
  simp only [resps, List.filter_cons]; split_ifs <;> simp_all

@[simp] lemma ops_append (l l' : SeqH Op Resp n) : ops (l ++ l') = ops l ++ ops l' := by
  simp [ops]

/-- Candidate data for Definition 11. -/
structure Data (Op Resp : Type) (n : ℕ) where
  /-- Proposal sequences. -/
  prop : Fin n → List Op
  /-- Decision sequences. -/
  dec : Fin n → List Op
  /-- Decision function. -/
  d : Fin n → List Resp → Fin n

variable (S : NSpec Op Resp)

/-- **Definition 11, as stated** (with the intended reading of its invocation conditions: in `α`
and `α · α'` every process `j` executes a prefix of `prop_j`; the paper only writes
`invs(α) ⊆ ⋃ₓ invs(prop_x)`, which would also allow histories in which a process executes another
process's proposal). `β` consists of `p_i`'s decision sequence only, and the chosen process `ℓ`
has completed `prop_ℓ` in `α · α'`. (`S_α` has at most `k` elements.) -/
def KOrdering (k : ℕ) (D : Data Op Resp n) : Prop :=
  (∀ i, D.prop i ≠ [] ∧ D.dec i ≠ []) ∧
  ∀ α : SeqH Op Resp n, S.Legal S.init (ops α) → (∀ j, invs α j <+: D.prop j) →
    (∃ j, invs α j = D.prop j) →
    ∃ Sα : Finset (Fin n), Sα.card ≤ k ∧
      ∀ (i : Fin n) (α' β : SeqH Op Resp n), S.Legal S.init (ops (α ++ α' ++ β)) →
        (∀ j, invs (α ++ α') j <+: D.prop j) → invs (α ++ α') i = D.prop i →
        (∀ y ∈ β, y.1 = i) → invs β i = D.dec i →
        ∃ ℓ, invs (α ++ α') ℓ = D.prop ℓ ∧ D.d i (resps (α ++ α') i ++ resps β i) = ℓ ∧ ℓ ∈ Sα

/-- **Definition 11 as needed by the proof of Lemma 12.** Histories are those that a strong
linearization of the algorithm can produce: every process `j` executes a prefix of `prop_j`
(followed, for `p_i`, by `dec_i`); `β` contains `dec_i` and, interleaved, operations of other
processes continuing their `prop_j`; the chosen process `ℓ` has started. -/
def KOrderingI (k : ℕ) (D : Data Op Resp n) : Prop :=
  ∀ α : SeqH Op Resp n, S.Legal S.init (ops α) → (∀ j, invs α j <+: D.prop j) →
    (∃ j, invs α j = D.prop j) →
    ∃ Sα : Finset (Fin n), Sα.card ≤ k ∧
      ∀ (i : Fin n) (α' β : SeqH Op Resp n), S.Legal S.init (ops (α ++ α' ++ β)) →
        (∀ j, invs (α ++ α') j <+: D.prop j) → invs (α ++ α') i = D.prop i →
        invs β i = D.dec i → (∀ j, j ≠ i → invs (α ++ α' ++ β) j <+: D.prop j) →
        ∃ ℓ, invs (α ++ α' ++ β) ℓ ≠ [] ∧ D.d i (resps (α ++ α') i ++ resps β i) = ℓ ∧ ℓ ∈ Sα

/-- A common weakening of `KOrdering` and `KOrderingI`: per-process-prefix histories, `β` made
of `dec_i` only, and the chosen process has started. -/
def KOrderingW (k : ℕ) (D : Data Op Resp n) : Prop :=
  ∀ α : SeqH Op Resp n, S.Legal S.init (ops α) → (∀ j, invs α j <+: D.prop j) →
    (∃ j, invs α j = D.prop j) →
    ∃ Sα : Finset (Fin n), Sα.card ≤ k ∧
      ∀ (i : Fin n) (α' β : SeqH Op Resp n), S.Legal S.init (ops (α ++ α' ++ β)) →
        (∀ j, invs (α ++ α') j <+: D.prop j) → invs (α ++ α') i = D.prop i →
        (∀ y ∈ β, y.1 = i) → invs β i = D.dec i →
        ∃ ℓ, invs (α ++ α' ++ β) ℓ ≠ [] ∧ D.d i (resps (α ++ α') i ++ resps β i) = ℓ ∧ ℓ ∈ Sα

lemma mem_prop_of_prefix {D : Data Op Resp n} {l : SeqH Op Resp n}
    (h : ∀ j, invs l j <+: D.prop j) : ∀ y ∈ l, ∃ x, y.2.1 ∈ D.prop x := by
  intro y hy
  refine ⟨y.1, (h y.1).subset ?_⟩
  simp only [invs, List.mem_map, List.mem_filter, decide_eq_true_eq]
  exact ⟨y, ⟨hy, rfl⟩, rfl⟩

lemma invs_eq_nil_of_forall {l : SeqH Op Resp n} {i j : Fin n} (h : ∀ y ∈ l, y.1 = i)
    (hj : j ≠ i) : invs l j = [] := by
  simp only [invs, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  intro y hy h'; exact hj (h' ▸ h y hy)

theorem KOrdering.toW {k : ℕ} {D : Data Op Resp n} (h : KOrdering S k D) : KOrderingW S k D := by
  intro α hα hpre hj
  obtain ⟨Sα, hcard, hS⟩ := h.2 α hα hpre hj
  refine ⟨Sα, hcard, fun i α' β hl hpre' hi hβ hdec => ?_⟩
  obtain ⟨ℓ, h1, h2, h3⟩ := hS i α' β hl hpre' hi hβ hdec
  refine ⟨ℓ, ?_, h2, h3⟩
  rw [invs_append, h1]
  intro he
  exact (h.1 ℓ).1 (List.append_eq_nil_iff.1 he).1

theorem KOrderingI.toW {k : ℕ} {D : Data Op Resp n} (h : KOrderingI S k D) :
    KOrderingW S k D := by
  intro α hα hpre hj
  obtain ⟨Sα, hcard, hS⟩ := h α hα hpre hj
  refine ⟨Sα, hcard, fun i α' β hl hpre' hi hβ hdec => ?_⟩
  refine hS i α' β hl hpre' hi hdec (fun j hji => ?_)
  rw [invs_append, invs_eq_nil_of_forall hβ hji, List.append_nil]
  exact hpre' j

/-! ## Queue-like objects -/

/-- Operations: `put x` (enqueue / push) and `get` (dequeue / pop). -/
inductive QOp where
  | put (x : ℕ)
  | get
  deriving DecidableEq

/-- Responses. -/
inductive QResp where
  | ok
  | empty
  | val (x : ℕ)
  deriving DecidableEq

/-- FIFO queue (state: items, oldest first). -/
abbrev queueSpec : NSpec QOp QResp where
  State := List ℕ
  init := []
  Step q o r q' := match o with
    | .put x => r = .ok ∧ q' = q ++ [x]
    | .get => (q = [] ∧ r = .empty ∧ q' = []) ∨ ∃ x t, q = x :: t ∧ r = .val x ∧ q' = t

/-- `k`-out-of-order queue (Henzinger et al.): a dequeue returns (and removes) one of the `k`
oldest items. -/
abbrev oooSpec (k : ℕ) : NSpec QOp QResp where
  State := List ℕ
  init := []
  Step q o r q' := match o with
    | .put x => r = .ok ∧ q' = q ++ [x]
    | .get => (q = [] ∧ r = .empty ∧ q' = []) ∨
        ∃ m, m < k ∧ ∃ hm : m < q.length, r = .val (q.get ⟨m, hm⟩) ∧ q' = q.eraseIdx m

/-- LIFO stack (state: items, top first). -/
abbrev stackSpec : NSpec QOp QResp where
  State := List ℕ
  init := []
  Step q o r q' := match o with
    | .put x => r = .ok ∧ q' = x :: q
    | .get => (q = [] ∧ r = .empty ∧ q' = []) ∨ ∃ x t, q = x :: t ∧ r = .val x ∧ q' = t

end StrongLinCN2.KOrd

namespace StrongLinCN2.KOrd

/-! ## The paper's sequences for `k`-out-of-order queues fail (`k = 2`, `n = 3`) -/

/-- The paper's data for `k`-out-of-order queues: `prop_i = enq(i)`, `dec_i = deq`, any `d`. -/
def oooData (d : Fin 3 → List QResp → Fin 3) : Data QOp QResp 3 where
  prop i := [.put i]
  dec _ := [.get]
  d := d

lemma participants {l : SeqH QOp QResp 3} {ℓ : Fin 3} (h : invs l ℓ ≠ []) : ∃ y ∈ l, y.1 = ℓ := by
  by_contra hc
  push Not at hc
  exact h (by simp only [invs, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq];
              exact fun y hy => hc y hy)

/-- Three scenarios of a 2-out-of-order queue: `α = enq(a)`, then process `i` enqueues `i` and
dequeues `i` (allowed: `i` is among the two oldest items). -/
lemma ooo_scenario (d : Fin 3 → List QResp → Fin 3) (a : Fin 3)
    (h : KOrderingW (oooSpec 2) 2 (oooData d)) :
    ∃ Sα : Finset (Fin 3), Sα.card ≤ 2 ∧ a ∈ Sα ∧ ∀ i : Fin 3, i ≠ a →
      (d i [.ok, .val i] = i ∨ d i [.ok, .val i] = a) ∧ d i [.ok, .val i] ∈ Sα := by
  obtain ⟨Sα, hcard, hS⟩ := h [(a, .put a, .ok)] ⟨_, ⟨rfl, rfl⟩, trivial⟩
    (fun j => by
      by_cases hj : a = j
      · subst hj; simp [oooData]
      · simp [hj])
    ⟨a, by simp [oooData]⟩
  refine ⟨Sα, hcard, ?_, fun i hia => ?_⟩
  · obtain ⟨ℓ, h1, -, h3⟩ := hS a [] [(a, .get, .val a)]
      ⟨_, ⟨rfl, rfl⟩, _, Or.inr ⟨0, by norm_num, by simp, by simp, rfl⟩,
        trivial⟩
      (fun j => by
        by_cases hj : a = j
        · subst hj; simp [oooData]
        · simp [hj])
      (by simp [oooData]) (by simp) (by simp [oooData])
    obtain ⟨y, hy, hyℓ⟩ := participants h1
    simp only [List.append_nil, List.mem_append, List.mem_singleton] at hy
    rcases hy with h | h <;> (subst h; simp only at hyℓ; rw [← hyℓ] at h3; exact h3)
  obtain ⟨ℓ, h1, h2, h3⟩ := hS i [(i, .put i, .ok)] [(i, .get, .val i)]
    ⟨_, ⟨rfl, rfl⟩, _, ⟨rfl, rfl⟩, _, Or.inr ⟨1, by norm_num, by simp, by simp, rfl⟩, trivial⟩
    (fun j => by
      by_cases hj : a = j
      · subst hj; simp [oooData, hia]
      · by_cases hj' : i = j
        · subst hj'; simp [oooData, hj]
        · simp [hj, hj'])
    (by simp [oooData, Ne.symm hia])
    (by simp) (by simp [oooData])
  have hr : resps ([(a, QOp.put ↑↑a, QResp.ok)] ++ [(i, QOp.put ↑↑i, QResp.ok)]) i ++
      resps [(i, QOp.get, QResp.val ↑↑i)] i = [.ok, .val i] := by simp [Ne.symm hia]
  rw [hr] at h2
  simp only [oooData] at h2
  refine ⟨?_, h2 ▸ h3⟩
  obtain ⟨y, hy, hyℓ⟩ := participants h1
  have : ℓ = a ∨ ℓ = i := by
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with (h | h) | h <;> (subst h; simp only at hyℓ)
    · exact Or.inl hyℓ.symm
    · exact Or.inr hyℓ.symm
    · exact Or.inr hyℓ.symm
  rcases this with rfl | rfl
  · exact Or.inr h2
  · exact Or.inl h2

/-- **The paper's example "`k`-out-of-order queues are `k`-ordering" fails**: for `n = 3`,
`k = 2`, the sequences `prop_i = enq(i)`, `dec_i = deq` admit no decision function `d`, even for
the weak variant `KOrderingW` (hence neither for Definition 11 as stated nor for `KOrderingI`). -/
theorem ooo_not_kOrderingW (d : Fin 3 → List QResp → Fin 3) :
    ¬ KOrderingW (oooSpec 2) 2 (oooData d) := by
  intro h
  -- `d i [ok, val i] = i` for every `i`, using a scenario `α = enq(a)` with `a ≠ i` and a third one
  have hd : ∀ i : Fin 3, d i [.ok, .val i] = i := by
    intro i
    obtain ⟨a, b, hai, hbi, hab⟩ : ∃ a b : Fin 3, a ≠ i ∧ b ≠ i ∧ a ≠ b := by
      fin_cases i
      · exact ⟨1, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 2, by decide, by decide, by decide⟩
      · exact ⟨0, 1, by decide, by decide, by decide⟩
    obtain ⟨_, _, _, ha⟩ := ooo_scenario d a h
    obtain ⟨_, _, _, hb⟩ := ooo_scenario d b h
    rcases (ha i (Ne.symm hai)).1 with h1 | h1
    · exact h1
    · rcases (hb i (Ne.symm hbi)).1 with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) hab
  -- in the scenario `α = enq(1)`, the decisions `0` and `2` and the decision `1` of process 1
  obtain ⟨Sα, hcard, h1, hS⟩ := ooo_scenario d 1 h
  have h0 := (hS 0 (by decide)).2
  have h2 := (hS 2 (by decide)).2
  rw [hd] at h0 h2
  have : ({0, 1, 2} : Finset (Fin 3)) ⊆ Sα := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card this
  simp at this
  omega

/-! ## Stacks: the paper's sequences fail once other pending pushes may be linearized -/

/-- The paper's data for stacks with `n = 3`: `prop_i = push(i)`, `dec_i = pop^{n+1}`. -/
def stackData (d : Fin 3 → List QResp → Fin 3) : Data QOp QResp 3 where
  prop i := [.put i]
  dec _ := [.get, .get, .get, .get]
  d := d

lemma stack_prefix_one (d : Fin 3 → List QResp → Fin 3) (a : Fin 3) :
    ∀ j, invs [((a, .put a, .ok) : Fin 3 × QOp × QResp)] j <+: (stackData d).prop j := by
  intro j
  by_cases hj : a = j
  · subst hj; simp [stackData]
  · simp [hj]

/-- In the scenario `α = push(a)`, process `a` alone pops `a` and then finds the stack empty, so
`S_α` contains `a`; hence `S_α = {a}` when `k = 1`. -/
lemma stack_solo (d : Fin 3 → List QResp → Fin 3) (a : Fin 3)
    (h : KOrderingI stackSpec 1 (stackData d)) :
    ∃ Sα : Finset (Fin 3), Sα.card ≤ 1 ∧ a ∈ Sα ∧
      ∀ (i : Fin 3) (α' β : SeqH QOp QResp 3),
        stackSpec.Legal stackSpec.init (ops ([(a, .put a, .ok)] ++ α' ++ β)) →
        (∀ j, invs ([(a, .put a, .ok)] ++ α') j <+: (stackData d).prop j) →
        invs ([(a, .put a, .ok)] ++ α') i = (stackData d).prop i →
        invs β i = (stackData d).dec i →
        (∀ j, j ≠ i → invs ([(a, .put a, .ok)] ++ α' ++ β) j <+: (stackData d).prop j) →
        d i (resps ([(a, .put a, .ok)] ++ α') i ++ resps β i) ∈ Sα := by
  obtain ⟨Sα, hcard, hS⟩ := h [(a, .put a, .ok)] ⟨_, ⟨rfl, rfl⟩, trivial⟩
    (stack_prefix_one d a) ⟨a, by simp [stackData]⟩
  refine ⟨Sα, hcard, ?_, fun i α' β h1 h2 h3 h4 h5 => ?_⟩
  · obtain ⟨ℓ, h1, -, h3⟩ := hS a [] [(a, .get, .val a), (a, .get, .empty), (a, .get, .empty),
        (a, .get, .empty)]
      ⟨_, ⟨rfl, rfl⟩, _, Or.inr ⟨_, _, rfl, rfl, rfl⟩, _, Or.inl ⟨rfl, rfl, rfl⟩, _,
        Or.inl ⟨rfl, rfl, rfl⟩, _, Or.inl ⟨rfl, rfl, rfl⟩, trivial⟩
      (by simpa using stack_prefix_one d a) (by simp [stackData]) (by simp [stackData])
      (fun j hj => by
        have : a ≠ j := Ne.symm hj
        simp [this])
    obtain ⟨y, hy, hyℓ⟩ := participants h1
    simp only [List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hy
    rcases hy with h | h | h | h | h <;> (subst h; simp only at hyℓ; rw [← hyℓ] at h3; exact h3)
  · obtain ⟨ℓ, -, h2, h3⟩ := hS i α' β h1 h2 h3 h4 h5
    simp only [stackData] at h2
    rw [h2]; exact h3

/-- **With the paper's sequences, stacks are not 1-ordering in the sense needed by the proof of
Lemma 12** (`n = 3`, any `d`): process `0` observes `OK · 0 · 1 · 2 · ε` both when `α = push(1)`,
`α' = push(0)` and the pending `push(2)` of process 2 is linearized between its pops, and when
`α = push(2)`, `α' = push(1) · push(0)`. -/
theorem stack_not_kOrderingI (d : Fin 3 → List QResp → Fin 3) :
    ¬ KOrderingI stackSpec 1 (stackData d) := by
  intro h
  set r : List QResp := [.ok, .val 0, .val 1, .val 2, .empty] with hr
  -- scenario X: α = push(1)
  have hX : d 0 r = 1 := by
    obtain ⟨S, hcard, h1, hS⟩ := stack_solo d 1 h
    have := hS 0 [(0, .put 0, .ok)] [(0, .get, .val 0), (0, .get, .val 1), (2, .put 2, .ok),
      (0, .get, .val 2), (0, .get, .empty)]
      ⟨_, ⟨rfl, rfl⟩, _, ⟨rfl, rfl⟩, _, Or.inr ⟨_, _, rfl, rfl, rfl⟩, _,
        Or.inr ⟨_, _, rfl, rfl, rfl⟩, _, ⟨rfl, rfl⟩, _, Or.inr ⟨_, _, rfl, rfl, rfl⟩, _,
        Or.inl ⟨rfl, rfl, rfl⟩, trivial⟩
      (fun j => by fin_cases j <;> simp [stackData])
      (by simp [stackData]) (by simp [stackData])
      (fun j hj => by fin_cases j <;> simp_all [stackData])
    have hres : resps ([((1 : Fin 3), QOp.put ↑(1 : Fin 3), QResp.ok)] ++
        [((0 : Fin 3), QOp.put 0, QResp.ok)]) 0 ++
        resps [((0 : Fin 3), QOp.get, QResp.val 0), (0, QOp.get, QResp.val 1),
          (2, QOp.put 2, QResp.ok), (0, QOp.get, QResp.val 2), (0, QOp.get, QResp.empty)] 0 = r := by
      simp [hr]
    rw [hres] at this
    exact Finset.card_le_one.1 hcard _ this _ h1
  -- scenario Y: α = push(2)
  have hY : d 0 r = 2 := by
    obtain ⟨S, hcard, h1, hS⟩ := stack_solo d 2 h
    have := hS 0 [(1, .put 1, .ok), (0, .put 0, .ok)] [(0, .get, .val 0), (0, .get, .val 1),
      (0, .get, .val 2), (0, .get, .empty)]
      ⟨_, ⟨rfl, rfl⟩, _, ⟨rfl, rfl⟩, _, ⟨rfl, rfl⟩, _, Or.inr ⟨_, _, rfl, rfl, rfl⟩, _,
        Or.inr ⟨_, _, rfl, rfl, rfl⟩, _, Or.inr ⟨_, _, rfl, rfl, rfl⟩, _,
        Or.inl ⟨rfl, rfl, rfl⟩, trivial⟩
      (fun j => by fin_cases j <;> simp [stackData])
      (by simp [stackData]) (by simp [stackData])
      (fun j hj => by fin_cases j <;> simp_all [stackData])
    have hres : resps ([((2 : Fin 3), QOp.put ↑(2 : Fin 3), QResp.ok)] ++
        [((1 : Fin 3), QOp.put 1, QResp.ok), (0, QOp.put 0, QResp.ok)]) 0 ++
        resps [((0 : Fin 3), QOp.get, QResp.val 0), (0, QOp.get, QResp.val 1),
          (0, QOp.get, QResp.val 2), (0, QOp.get, QResp.empty)] 0 = r := by
      simp [hr]
    rw [hres] at this
    exact Finset.card_le_one.1 hcard _ this _ h1
  rw [hX] at hY
  exact absurd hY (by decide)

/-! ## Repaired sequences for `k`-out-of-order queues (and queues) -/

open Cslib.SharedMemory

variable {Op Resp : Type} {n : ℕ}

section Repair

variable {S : NSpec Op Resp}

/-- Reachability along a sequence of operations with responses. -/
def Reach (S : NSpec Op Resp) : S.State → List (Op × Resp) → S.State → Prop
  | q, [], q' => q' = q
  | q, (o, r) :: l, q' => ∃ q₁, S.Step q o r q₁ ∧ Reach S q₁ l q'

lemma legal_append_split (q : S.State) (l₁ l₂ : List (Op × Resp)) (h : S.Legal q (l₁ ++ l₂)) :
    ∃ q', Reach S q l₁ q' ∧ S.Legal q' l₂ := by
  induction l₁ generalizing q with
  | nil => exact ⟨q, rfl, h⟩
  | cons y l₁ ih =>
    obtain ⟨o, r⟩ := y
    obtain ⟨q₁, hs, hl⟩ := h
    obtain ⟨q', h1, h2⟩ := ih q₁ hl
    exact ⟨q', ⟨q₁, hs, h1⟩, h2⟩

end Repair

/-- The value of a `put`. -/
def putVal : QOp → ℕ
  | .put x => x
  | .get => 0

lemma reach_puts (k : ℕ) (q : List ℕ) (l : List (QOp × QResp)) (h : ∀ y ∈ l, ∃ x, y.1 = .put x)
    (q' : List ℕ) (hr : Reach (oooSpec k) q l q') : q' = q ++ l.map (fun y => putVal y.1) := by
  induction l generalizing q with
  | nil => simp only [Reach] at hr; simp [hr]
  | cons y l ih =>
    obtain ⟨o, r⟩ := y
    obtain ⟨x, hx⟩ := h (o, r) List.mem_cons_self
    simp only at hx; subst hx
    obtain ⟨q₁, ⟨-, rfl⟩, hr⟩ := hr
    rw [ih (q ++ [x]) (fun y hy => h y (List.mem_cons_of_mem _ hy)) hr]
    simp [putVal]

lemma invs_eq_nil_iff (l : SeqH Op Resp n) (i : Fin n) : invs l i = [] ↔ ∀ y ∈ l, y.1 ≠ i := by
  simp [invs, List.filter_eq_nil_iff]

lemma resps_eq_nil_of_invs {l : SeqH Op Resp n} {i : Fin n} (h : invs l i = []) :
    resps l i = [] := by
  rw [invs_eq_nil_iff] at h
  simp only [resps, List.map_eq_nil_iff, List.filter_eq_nil_iff, decide_eq_true_eq]
  exact h

/-- Splitting a history at the unique operation of process `i`. -/
lemma split_single {l : SeqH Op Resp n} {i : Fin n} {o : Op} (h : invs l i = [o]) :
    ∃ l₁ r l₂, l = l₁ ++ (i, o, r) :: l₂ ∧ invs l₁ i = [] ∧ invs l₂ i = [] := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rw [invs_cons] at h
    split_ifs at h with hy
    · simp only [List.singleton_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨j, o', r⟩ := y
      simp only at hy; subst hy
      exact ⟨[], r, l, rfl, rfl, h2⟩
    · simp only [List.nil_append] at h
      obtain ⟨l₁, r, l₂, rfl, h1, h2⟩ := ih h
      refine ⟨y :: l₁, r, l₂, rfl, ?_, h2⟩
      rw [invs_cons, ite_eq_right_iff.2 (fun h => absurd h hy), h1]; rfl

lemma op_eq_of_prefix {l : SeqH QOp QResp n} {k : ℕ} {j : Fin n}
    (h : invs l j <+: List.replicate k (QOp.put j)) {y : Fin n × QOp × QResp} (hy : y ∈ l)
    (hj : y.1 = j) : y.2.1 = .put j := by
  have : y.2.1 ∈ invs l j := by
    simp only [invs, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact ⟨y, ⟨hy, hj⟩, rfl⟩
  exact List.eq_of_mem_replicate (h.subset this)

/-- The repaired data for `k`-out-of-order queues: every process enqueues its index `k` times,
then dequeues once; `d` returns the dequeued value. -/
def oooFixData (n k : ℕ) [NeZero n] : Data QOp QResp n where
  prop i := List.replicate k (.put i)
  dec _ := [.get]
  d i rs := match rs.getLast? with
    | some (.val x) => Fin.ofNat n x
    | _ => i

/-- Core of the repaired example: `S_α` is the set of processes of the first `k` enqueues of
`α`; all of them occur in `α`. -/
theorem ooo_core (n k : ℕ) [NeZero n] (hk : 1 ≤ k) (α : SeqH QOp QResp n)
    (hj : ∃ j, invs α j = (oooFixData n k).prop j) :
    ∃ Sα : Finset (Fin n), Sα.card ≤ k ∧ (∀ ℓ ∈ Sα, invs α ℓ ≠ []) ∧
      ∀ (i : Fin n) (α' β : SeqH QOp QResp n),
        (oooSpec k).Legal (oooSpec k).init (ops (α ++ α' ++ β)) →
        (∀ j, invs (α ++ α') j <+: (oooFixData n k).prop j) →
        invs β i = (oooFixData n k).dec i →
        (∀ j, j ≠ i → invs (α ++ α' ++ β) j <+: (oooFixData n k).prop j) →
        (oooFixData n k).d i (resps (α ++ α') i ++ resps β i) ∈ Sα := by
  obtain ⟨j₀, hj₀⟩ := hj
  have hlen : k ≤ α.length := by
    have := congrArg List.length hj₀
    simp only [oooFixData, List.length_replicate] at this
    rw [← this]
    simp only [invs, List.length_map]
    exact List.length_filter_le _ _
  refine ⟨((α.take k).map Prod.fst).toFinset, ?_, ?_, ?_⟩
  · refine (List.toFinset_card_le _).trans ?_
    simp
  · intro ℓ hℓ
    simp only [List.mem_toFinset, List.mem_map] at hℓ
    obtain ⟨y, hy, rfl⟩ := hℓ
    rw [ne_eq, invs_eq_nil_iff]
    push Not
    exact ⟨y, List.mem_of_mem_take hy, rfl⟩
  · intro i α' β hl hpre' hdec hoth
    obtain ⟨β₁, r, β₂, rfl, h1, h2⟩ := split_single hdec
    have hl' : (oooSpec k).Legal [] (ops (α ++ α' ++ β₁) ++ (QOp.get, r) :: ops β₂) := by
      have := hl
      simp only [ops, List.map_append, List.map_cons, List.append_assoc] at this ⊢
      exact this
    obtain ⟨q, hq, hrest⟩ := legal_append_split (S := oooSpec k) [] _ _ hl'
    obtain ⟨q₂, hstep, -⟩ := hrest
    -- all operations before `p_i`'s dequeue are enqueues of the process index
    have hputs : ∀ y ∈ α ++ α' ++ β₁, y.2.1 = .put y.1 := by
      intro y hy
      by_cases hyi : y.1 = i
      · rcases List.mem_append.1 hy with hy | hy
        · exact op_eq_of_prefix (hpre' y.1) hy rfl
        · exact absurd hyi ((invs_eq_nil_iff _ _).1 h1 y hy)
      · have := hoth y.1 hyi
        exact op_eq_of_prefix this (by simp only [List.mem_append] at hy ⊢; tauto) rfl
    have hqv : q = (α ++ α' ++ β₁).map (fun y => (y.1 : ℕ)) := by
      rw [reach_puts k [] _ (fun y hy => by
        obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
        exact ⟨_, hputs y' hy'⟩) q hq]
      simp only [ops, List.map_map, List.nil_append]
      refine List.map_congr_left (fun y hy => ?_)
      simp [hputs y hy, putVal]
    -- the dequeue returns the value of one of the first `k` enqueues of `α`
    rcases hstep with ⟨hq0, -, -⟩ | ⟨m, hm, hml, hr, -⟩
    · exfalso
      rw [hqv] at hq0
      have h0 := congrArg List.length hq0
      simp only [List.length_map, List.length_append, List.length_nil] at h0
      omega
    · have hmα : m < α.length := by omega
      have hval : q.get ⟨m, hml⟩ = (α[m]'hmα).1 := by
        simp only [List.get_eq_getElem]
        rw [List.getElem_of_eq hqv]
        simp only [List.map_append, List.append_assoc]
        rw [List.getElem_append_left (by simpa using hmα)]
        simp
      have hres : resps (α ++ α') i ++ resps (β₁ ++ (i, QOp.get, r) :: β₂) i =
          resps (α ++ α') i ++ [r] := by
        simp only [resps_append, resps_cons, resps_eq_nil_of_invs h1, resps_eq_nil_of_invs h2]
        simp
      rw [hres]
      simp only [oooFixData, List.getLast?_append, List.getLast?_singleton, Option.some_or, hr,
        hval, Fin.ofNat_val_eq_self]
      simp only [List.mem_toFinset, List.mem_map]
      refine ⟨α[m]'hmα, ?_, rfl⟩
      rw [List.mem_iff_getElem]
      exact ⟨m, by simp; omega, by simp⟩

/-- **Repaired example**: with `prop_i = enq(i)^k` and `dec_i = deq`, `k`-out-of-order queues are
`k`-ordering in the strong sense needed by Lemma 12. -/
theorem ooo_kOrderingI (n k : ℕ) [NeZero n] (hk : 1 ≤ k) :
    KOrderingI (oooSpec k) k (oooFixData n k) := by
  intro α _ hpre hj
  obtain ⟨Sα, hcard, hpart, hS⟩ := ooo_core n k hk α hj
  refine ⟨Sα, hcard, fun i α' β hl hpre' _ hdec hoth => ?_⟩
  have hmem := hS i α' β hl hpre' hdec hoth
  refine ⟨_, ?_, rfl, hmem⟩
  have := hpart _ hmem
  rw [invs_append, invs_append]
  intro he
  exact this (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 he).1).1

lemma queue_legal_iff (q : List ℕ) (l : List (QOp × QResp)) :
    queueSpec.Legal q l ↔ (oooSpec 1).Legal q l := by
  induction l generalizing q with
  | nil => simp
  | cons y l ih =>
    obtain ⟨o, r⟩ := y
    simp only [NSpec.legal_cons]
    refine exists_congr (fun q' => and_congr ?_ (ih q'))
    cases o with
    | put x => rfl
    | get =>
      show ((q = [] ∧ r = .empty ∧ q' = []) ∨ ∃ x t, q = x :: t ∧ r = .val x ∧ q' = t) ↔
        ((q = [] ∧ r = .empty ∧ q' = []) ∨
          ∃ m, m < 1 ∧ ∃ hm : m < q.length, r = .val (q.get ⟨m, hm⟩) ∧ q' = q.eraseIdx m)
      refine or_congr Iff.rfl ⟨?_, ?_⟩
      · rintro ⟨x, t, rfl, rfl, rfl⟩
        exact ⟨0, by norm_num, by simp, by simp, by simp⟩
      · rintro ⟨m, hm, hml, rfl, rfl⟩
        obtain rfl : m = 0 := by omega
        cases q with
        | nil => simp at hml
        | cons x t => exact ⟨x, t, rfl, by simp, by simp⟩

/-- **Queues are 1-ordering** (the paper's example), in the sense of Definition 11 as stated
(with `prop_i = enq(i)`, `dec_i = deq`, `d(i, OK · ℓ) = ℓ`). -/
theorem queue_kOrdering (n : ℕ) [NeZero n] : KOrdering queueSpec 1 (oooFixData n 1) := by
  refine ⟨fun i => ⟨by simp [oooFixData], by simp [oooFixData]⟩, fun α _ hpre hj => ?_⟩
  obtain ⟨Sα, hcard, hpart, hS⟩ := ooo_core n 1 le_rfl α hj
  refine ⟨Sα, hcard, fun i α' β hl hpre' _ hβ hdec => ?_⟩
  have hmem := hS i α' β ((queue_legal_iff _ _).1 hl) hpre' hdec (fun j hji => by
    rw [invs_append, invs_eq_nil_of_forall hβ hji, List.append_nil]; exact hpre' j)
  refine ⟨_, ?_, rfl, hmem⟩
  -- the chosen process occurs in `α`, so it completed its single enqueue
  have h1 := hpart _ hmem
  have h2 := hpre' ((oooFixData n 1).d i (resps (α ++ α') i ++ resps β i))
  simp only [oooFixData, List.replicate_one] at h2 ⊢
  rw [List.prefix_cons_iff] at h2
  rcases h2 with h2 | ⟨t, h2, ht⟩
  · exact absurd (List.append_eq_nil_iff.1 (by rw [← invs_append]; exact h2)).1 h1
  · rw [h2, List.prefix_nil.1 ht]

/-- Queues are also 1-ordering in the strong sense `KOrderingI`. -/
theorem queue_kOrderingI (n : ℕ) [NeZero n] : KOrderingI queueSpec 1 (oooFixData n 1) := by
  intro α hα hpre hj
  obtain ⟨Sα, hcard, hS⟩ := ooo_kOrderingI n 1 le_rfl α ((queue_legal_iff _ _).1 hα) hpre hj
  exact ⟨Sα, hcard, fun i α' β hl => hS i α' β ((queue_legal_iff _ _).1 hl)⟩

/-! ## The stack example is correct for Definition 11 as stated -/

/-- The paper's data for stacks with `n` processes: `prop_i = push(i)`, `dec_i = pop^{n+1}`,
`d(i, rs)` = the last non-`ε` value popped. -/
def stackDataN (n : ℕ) [NeZero n] : Data QOp QResp n where
  prop i := [.put i]
  dec _ := List.replicate (n + 1) .get
  d i rs := match (rs.filterMap (fun r => match r with | .val x => some x | _ => none)).getLast? with
    | some x => Fin.ofNat n x
    | none => i

/-- The values popped. -/
def vals (rs : List QResp) : List ℕ := rs.filterMap (fun r => match r with | .val x => some x | _ => none)

lemma reach_stack_puts (q : List ℕ) (l : List (QOp × QResp)) (h : ∀ y ∈ l, ∃ x, y.1 = .put x)
    (q' : List ℕ) (hr : Reach stackSpec q l q') :
    q' = (l.map (fun y => putVal y.1)).reverse ++ q ∧ ∀ y ∈ l, y.2 = .ok := by
  induction l generalizing q with
  | nil => simp only [Reach] at hr; simp [hr]
  | cons y l ih =>
    obtain ⟨o, r⟩ := y
    obtain ⟨x, hx⟩ := h (o, r) List.mem_cons_self
    simp only at hx; subst hx
    obtain ⟨q₁, ⟨hr1, rfl⟩, hr⟩ := hr
    obtain ⟨h1, h2⟩ := ih (x :: q) (fun y hy => h y (List.mem_cons_of_mem _ hy)) hr
    refine ⟨by rw [h1]; simp [putVal], ?_⟩
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hr1
    · exact h2 y hy

/-- Popping a stack with at least as many pops as items returns all items, then `ε`. -/
lemma legal_stack_pops (q : List ℕ) (rs : List QResp)
    (h : stackSpec.Legal q (rs.map (fun r => (QOp.get, r)))) (hlen : q.length ≤ rs.length) :
    vals rs = q := by
  induction rs generalizing q with
  | nil => simp at hlen; subst hlen; rfl
  | cons r rs ih =>
    obtain ⟨q₁, hs, hl⟩ := h
    rcases hs with ⟨rfl, rfl, rfl⟩ | ⟨x, t, rfl, rfl, rfl⟩
    · have := ih [] hl (by simp)
      simp [vals] at this ⊢; exact this
    · have := ih q₁ hl (by simp at hlen; omega)
      simp only [vals, List.filterMap_cons] at this ⊢
      rw [this]

/-- **The paper's stack example satisfies Definition 11 as stated** (`β` only contains `p_i`'s
pops). -/
theorem stack_kOrdering (n : ℕ) [NeZero n] : KOrdering stackSpec 1 (stackDataN n) := by
  refine ⟨fun i => ⟨by simp [stackDataN], by simp [stackDataN]⟩, fun α _ hpre hj => ?_⟩
  obtain ⟨j₀, hj₀⟩ := hj
  have hne : α ≠ [] := by
    rintro rfl; simp [stackDataN] at hj₀
  obtain ⟨y₀, α₀, hα⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨{y₀.1}, by simp, fun i α' β hl hpre' hi hβ hdec => ?_⟩
  -- operations of `α · α'`: one push of its index per process at most
  have hputs : ∀ y ∈ α ++ α', y.2.1 = .put y.1 := by
    intro y hy
    exact op_eq_of_prefix (k := 1) (by simpa [stackDataN] using hpre' y.1) hy rfl
  have hcount : ∀ (l : SeqH QOp QResp n) (j : Fin n), (l.map Prod.fst).count j = (invs l j).length := by
    intro l j
    induction l with
    | nil => rfl
    | cons y l ih =>
      rw [invs_cons, List.map_cons, List.count_cons, ih]
      by_cases hy : y.1 = j <;> simp [hy]
  have hnd : ((α ++ α').map Prod.fst).Nodup := by
    rw [List.nodup_iff_count_le_one]
    intro j
    rw [hcount]
    have h1 := (hpre' j).length_le
    simpa [stackDataN] using h1
  have hlenαα : (α ++ α').length ≤ n := by
    have := hnd.length_le_card
    simpa using this
  -- `β` consists of `n + 1` pops of `p_i`
  have hinvβ : invs β i = β.map (fun y => y.2.1) := by
    simp only [invs]
    rw [List.filter_eq_self.2 (fun y hy => by simpa using hβ y hy)]
  have hrβ : resps β i = β.map (fun y => y.2.2) := by
    simp only [resps]
    rw [List.filter_eq_self.2 (fun y hy => by simpa using hβ y hy)]
  have hget : ∀ y ∈ β, y.2.1 = .get := by
    intro y hy
    have : y.2.1 ∈ invs β i := by rw [hinvβ]; exact List.mem_map_of_mem hy
    rw [hdec] at this
    exact List.eq_of_mem_replicate this
  have hβeq : ops β = (resps β i).map (fun r => (QOp.get, r)) := by
    rw [hrβ, ops, List.map_map]
    exact List.map_congr_left (fun y hy => Prod.ext (hget y hy) rfl)
  have hlenβ : (resps β i).length = n + 1 := by
    have := congrArg List.length hdec
    rw [hinvβ] at this
    rw [hrβ]; simpa [stackDataN] using this
  -- legality: pushes, then pops
  have hl' : stackSpec.Legal [] (ops (α ++ α') ++ ops β) := by
    have := hl; simp only [ops_append] at this ⊢; exact this
  obtain ⟨q, hq, hrest⟩ := legal_append_split (S := stackSpec) [] _ _ hl'
  obtain ⟨hqv, hok⟩ := reach_stack_puts [] _ (fun y hy => by
    obtain ⟨y', hy', rfl⟩ := List.mem_map.1 hy
    exact ⟨_, hputs y' hy'⟩) q hq
  rw [hβeq] at hrest
  have hv := legal_stack_pops q _ hrest (by
    rw [hqv, hlenβ]; simp only [List.length_append] at hlenαα; simp [ops]; omega)
  -- the last value popped is the bottom of the stack, the first push of `α`
  have hres_i : vals (resps (α ++ α') i) = [] := by
    simp only [vals, List.filterMap_eq_nil_iff]
    intro r hr
    simp only [resps, List.mem_map, List.mem_filter] at hr
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hr
    have := hok (y.2) (List.mem_map.2 ⟨y, hy, rfl⟩)
    rw [this]
  have hlast : (vals (resps (α ++ α') i ++ resps β i)).getLast? = some (y₀.1 : ℕ) := by
    simp only [vals, List.filterMap_append] at hres_i ⊢
    rw [hres_i, List.nil_append]
    change (vals (resps β i)).getLast? = _
    rw [hv, hqv, hα]
    simp [ops, hputs y₀ (by simp [hα]), putVal]
  refine ⟨y₀.1, ?_, ?_, by simp⟩
  · -- `y₀.1` executed its push in `α`
    have hp := hpre' y₀.1
    simp only [stackDataN] at hp ⊢
    rw [List.prefix_cons_iff] at hp
    rcases hp with hp | ⟨t, hp, ht⟩
    · exfalso
      rw [invs_eq_nil_iff] at hp
      exact hp y₀ (by simp [hα]) rfl
    · rw [hp, List.prefix_nil.1 ht]
  · simp only [stackDataN]
    change (match (vals (resps (α ++ α') i ++ resps β i)).getLast? with
      | some x => Fin.ofNat n x | none => i) = y₀.1
    rw [hlast]; exact Fin.ofNat_val_eq_self _

end StrongLinCN2.KOrd
