import Mathlib
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Equiv
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.DetSpec

/-!
# The counterexamples of Sections 3 and 5 of "Linearizability: A Typo"

Sela, Herlihy, Petrank, *Linearizability: A Typo*, PODC 2021 (arXiv 2105.06737).

Concrete objects (registers and a FIFO queue, as deterministic sequential specifications
`detSpec`), the histories of Figures 1–3, and the claims made about them:

* Section 3.1 / 5.1: `H1` (Fig. 1, register) and `H2` (Fig. 2, FIFO queue) are linearizable by
  the original Definition 2.2 (`LinearizableHW`) but not by the amended Definition 4.1
  (`Linearizable`).
* Section 3.2: the original definition is not local (Fig. 3: two registers).
* Section 3.3: the original definition is not nonblocking (`H1`, `H2` with the pending
  invocation of a total operation that cannot be completed).
* Section 5.2: the object subhistories of Fig. 3 are not linearizable by Definition 4.1.

All proofs go through the list characterizations `linearizableHW_iff` / `linearizable_iff`.

-- CSLib candidate (generic helpers only): `reg_run_write`, `queue_run_head`, `queue_run_fifo`,
-- `reg_write_before`, `queue_enq_before`, `Matches.filter_obj`, `idsOf_filter_obj`,
-- `pair_sublist_filter_obj`, `pair_sublist_of_lt`.
-/

namespace Podc2021.LinearizabilityTypo

open Cslib.SharedMemory.HerlihyWing

set_option linter.unusedSectionVars false

/-! ## Processes and objects -/

/-- The two processes `A` and `B` of the figures. -/
inductive Proc | A | B
  deriving DecidableEq, Repr

open Proc

/-! ### Registers -/

/-- Register operations: `Read()` and `Write(v)`. -/
inductive RegOp | read | write (v : ℕ)
  deriving DecidableEq, Repr

/-- Register responses: `ok` (of a write) and `val v` (of a read). -/
inductive RegRes | ok | val (v : ℕ)
  deriving DecidableEq, Repr

/-- Transition function of a register holding a natural number. -/
def regδ : ℕ → RegOp → ℕ × RegRes
  | s, .read => (s, .val s)
  | _, .write v => (v, .ok)

/-- Every object is a register initialized to `0`. -/
def regSpec {P X : Type} [DecidableEq P] [DecidableEq X] : SeqSpec P X RegOp RegRes :=
  fun _ => detSpec 0 regδ

/-! ### FIFO queue -/

/-- Queue operations: `Enq(v)` and `Deq()`. -/
inductive QOp | enq (v : ℕ) | deq
  deriving DecidableEq, Repr

/-- Queue responses: `ok` (of an enqueue), `val v` and `empty` (of a dequeue). -/
inductive QRes | ok | val (v : ℕ) | empty
  deriving DecidableEq, Repr

/-- Transition function of a FIFO queue (state: the list of enqueued items, oldest first). -/
def queueδ : List ℕ → QOp → List ℕ × QRes
  | q, .enq v => (q ++ [v], .ok)
  | [], .deq => ([], .empty)
  | v :: q, .deq => (q, .val v)

/-- Every object is a FIFO queue, initially empty. -/
def queueSpec {P X : Type} [DecidableEq P] [DecidableEq X] : SeqSpec P X QOp QRes :=
  fun _ => detSpec [] queueδ

/-- The two register objects `x` and `y` of Fig. 3. -/
inductive Reg2 | x | y
  deriving DecidableEq, Repr

/-! ## The histories -/

/-- The single-register history pattern of Fig. 1: `p` reads `1` from `o` (complete), then `q`
invokes `Write(1)` on `o` (pending). -/
def readWrite {P X : Type} (p q : P) (o : X) : History P X RegOp RegRes :=
  [.inv p o .read, .res p o (.val 1), .inv q o (.write 1)]

/-- **Fig. 1**: `H1`. -/
def H1 : History Proc Unit RegOp RegRes := readWrite A B ()

/-- **Fig. 2**: `H2` (with `x = 1`, `y = 2`): `A` enqueues `1`; then `B` invokes `Enq(2)`
(pending); then `A` dequeues and gets `2`. -/
def H2 : History Proc Unit QOp QRes :=
  [.inv A () (.enq 1), .res A () .ok, .inv B () (.enq 2), .inv A () .deq, .res A () (.val 2)]

/-- **Fig. 3**: `H`: `A` reads `1` from `x` and `B` reads `1` from `y` (concurrently); then `A`
invokes `y.Write(1)` and `B` invokes `x.Write(1)` (both pending). -/
def H3 : History Proc Reg2 RegOp RegRes :=
  [.inv A .x .read, .inv B .y .read, .res A .x (.val 1), .res B .y (.val 1),
    .inv A .y (.write 1), .inv B .x (.write 1)]

/-! ## Sequential runs of a register and of a FIFO queue -/

section Runs

variable {P X : Type}

/-- In a legal register run from state `s`, a read returning `v ≠ s` is preceded by a write of
`v`. -/
lemma reg_run_write {s : ℕ} {N : List (OpRec P X RegOp RegRes)} (h : runOK regδ s N) {i : ℕ}
    (hi : i < N.length) (hr : N[i].o = .read) {v : ℕ} (hv : N[i].r = .val v) (hvs : v ≠ s) :
    ∃ j, ∃ hj : j < N.length, j < i ∧ N[j].o = .write v := by
  induction N generalizing s i with
  | nil => simp at hi
  | cons e N ih =>
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hr hv
      rw [hr, hv] at h1
      simp [regδ] at h1
      exact absurd h1.symm hvs
    | succ i =>
      simp only [List.getElem_cons_succ] at hr hv
      have hi' : i < N.length := by simpa using hi
      cases heo : e.o with
      | read =>
        rw [heo] at h2
        obtain ⟨j, hj, hji, hjw⟩ := ih h2 hi' hr hv hvs
        exact ⟨j + 1, by simpa using hj, by omega, by simpa using hjw⟩
      | write w =>
        rw [heo] at h2
        by_cases hvw : v = w
        · subst hvw; exact ⟨0, by simp, by omega, by simpa using heo⟩
        · obtain ⟨j, hj, hji, hjw⟩ := ih h2 hi' hr hv hvw
          exact ⟨j + 1, by simpa using hj, by omega, by simpa using hjw⟩

/-- In a legal FIFO-queue run from state `q` without dequeues before position `i`, a dequeue
at position `i` returns the head of `q` (if `q` is nonempty). -/
lemma queue_run_head {q : List ℕ} {N : List (OpRec P X QOp QRes)} (h : runOK queueδ q N)
    {i : ℕ} (hi : i < N.length) (hd : N[i].o = .deq) {v : ℕ} (hv : N[i].r = .val v)
    (hnd : ∀ d (hd : d < N.length), d < i → N[d].o ≠ .deq) (hq : q ≠ []) :
    q.head? = some v := by
  induction N generalizing q i with
  | nil => simp at hi
  | cons e N ih =>
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hd hv
      rw [hd, hv] at h1
      obtain _ | ⟨w, q⟩ := q
      · exact absurd rfl hq
      · simp [queueδ] at h1; simp [h1]
    | succ i =>
      simp only [List.getElem_cons_succ] at hd hv
      have hi' : i < N.length := by simpa using hi
      cases heo : e.o with
      | deq => exact absurd heo (hnd 0 (by simp) (by omega))
      | enq w =>
        rw [heo] at h2
        have hnd' : ∀ d (hd' : d < N.length), d < i → N[d].o ≠ .deq := fun d hd' hdi => by
          have := hnd (d + 1) (by simp; omega) (by omega)
          rwa [List.getElem_cons_succ] at this
        have := ih h2 hi' hd hv hnd' (by simp [queueδ])
        obtain _ | ⟨u, q⟩ := q
        · exact absurd rfl hq
        · simpa [queueδ] using this

/-- FIFO order: in a legal FIFO-queue run from state `q` without dequeues before position `i`,
if the dequeue at position `i` returns `v`, then every enqueue of `u ≠ v` before position `i` is
preceded by an enqueue of `v` (or `v` is the head of the initial state). -/
lemma queue_run_fifo {q : List ℕ} {N : List (OpRec P X QOp QRes)} (h : runOK queueδ q N)
    {i : ℕ} (hi : i < N.length) (hd : N[i].o = .deq) {v : ℕ} (hv : N[i].r = .val v)
    (hnd : ∀ d (hd : d < N.length), d < i → N[d].o ≠ .deq) {j : ℕ} (hj : j < N.length)
    (hji : j < i) {u : ℕ} (hu : N[j].o = .enq u) (huv : u ≠ v) :
    q.head? = some v ∨ ∃ j', ∃ hj' : j' < N.length, j' < j ∧ N[j'].o = .enq v := by
  induction N generalizing q i j with
  | nil => simp at hi
  | cons e N ih =>
    have h' := h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero => omega
    | succ i =>
      simp only [List.getElem_cons_succ] at hd hv
      have hi' : i < N.length := by simpa using hi
      have hnd' : ∀ d (hd' : d < N.length), d < i → N[d].o ≠ .deq := fun d hd' hdi => by
        have := hnd (d + 1) (by simp; omega) (by omega)
        rwa [List.getElem_cons_succ] at this
      cases heo : e.o with
      | deq => exact absurd heo (hnd 0 (by simp) (by omega))
      | enq w =>
        rw [heo] at h2
        have hhead := queue_run_head h2 hi' hd hv hnd' (by simp [queueδ])
        cases j with
        | zero =>
          simp only [List.getElem_cons_zero] at hu
          rw [heo] at hu; cases hu
          obtain _ | ⟨a, q⟩ := q
          · simp [queueδ] at hhead; exact absurd hhead huv
          · left; simpa [queueδ] using hhead
        | succ j =>
          simp only [List.getElem_cons_succ] at hu
          rcases ih h2 hi' hd hv hnd' (by simpa using hj) (by omega) hu with h3 | ⟨j', hj', hj'j, h4⟩
          · obtain _ | ⟨a, q⟩ := q
            · simp [queueδ] at h3; subst h3
              exact Or.inr ⟨0, by simp, by omega, by simpa using heo⟩
            · left; simpa [queueδ] using h3
          · exact Or.inr ⟨j' + 1, by simpa using hj', by omega, by simpa using h4⟩

end Runs

/-! ## From linearization lists to object runs -/

section View

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-- The identities of the records of `M` on object `x`. -/
lemma idsOf_filter_obj (M : List (OpRec P X Op Res)) (x : X) :
    idsOf (M.filter (·.x = x)) = (idsOf M).filter (·.x = x) :=
  idsOf_filter M (fun _ y => decide (y = x))

/-- The `i`-th record on object `x` matches the `i`-th identity on `x`. -/
lemma Matches.filter_obj {H : History P X Op Res} {M : List (OpRec P X Op Res)}
    (hrecs : Matches H M) (x : X) (i : ℕ) (hi : i < (M.filter (·.x = x)).length) :
    opOf H ((idsOf (M.filter (·.x = x)))[i]'(by simpa using hi)) =
        some (M.filter (·.x = x))[i].o ∧
      (Completed H ((idsOf (M.filter (·.x = x)))[i]'(by simpa using hi)) →
        resOf H ((idsOf (M.filter (·.x = x)))[i]'(by simpa using hi)) =
          some (M.filter (·.x = x))[i].r) := by
  apply hrecs
  have hmem : ((idsOf (M.filter (·.x = x)))[i]'(by simpa using hi), (M.filter (·.x = x))[i]) ∈
      (idsOf (M.filter (·.x = x))).zip (M.filter (·.x = x)) := by
    rw [List.mem_iff_getElem]
    exact ⟨i, by simpa using hi, by simp⟩
  have := zip_idsOf_filter M (fun _ y => decide (y = x))
  rw [← this] at hmem
  exact List.mem_of_mem_filter hmem

lemma mem_idsOf_filter_obj {M : List (OpRec P X Op Res)} {x : X} {a : OpId P X} :
    a ∈ idsOf (M.filter (·.x = x)) ↔ a ∈ idsOf M ∧ a.x = x := by
  rw [idsOf_filter_obj]; simp

lemma pair_sublist_filter_obj {M : List (OpRec P X Op Res)} {x : X} {a b : OpId P X}
    (ha : a.x = x) (hb : b.x = x) :
    [a, b].Sublist (idsOf (M.filter (·.x = x))) ↔ [a, b].Sublist (idsOf M) := by
  rw [idsOf_filter_obj]
  constructor
  · intro h; exact h.trans List.filter_sublist
  · intro h
    have := h.filter (fun c : OpId P X => decide (c.x = x))
    simpa [ha, hb] using this

/-- Identities in a duplicate-free list, ordered by position. -/
lemma pair_sublist_of_lt {l : List (OpId P X)} (hl : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (hji : j < i) : [l[j], l[i]].Sublist l := by
  rw [pair_sublist_iff_idxOf hl]
  refine ⟨List.getElem_mem _, List.getElem_mem _, ?_⟩
  rw [hl.idxOf_getElem, hl.idxOf_getElem]; exact hji

/-- **Registers**: in a linearization of `H` (legal for registers initialized to `0`), a read
that returned `v ≠ 0` is preceded by a write of `v` to the same register. -/
lemma reg_write_before {H : History P X RegOp RegRes} {M : List (OpRec P X RegOp RegRes)}
    (hcore : LinCore regSpec H M) {a : OpId P X} (ha : a ∈ idsOf M)
    (hop : opOf H a = some .read) {v : ℕ} (hres : resOf H a = some (.val v)) (hv : v ≠ 0) :
    ∃ b, opOf H b = some (.write v) ∧ b.x = a.x ∧ [b, a].Sublist (idsOf M) := by
  set N := M.filter (·.x = a.x) with hN
  have hnd := nodup_idsOf N
  have haN : a ∈ idsOf N := mem_idsOf_filter_obj.2 ⟨ha, rfl⟩
  have hil := List.idxOf_lt_length_of_mem haN
  set i := (idsOf N).idxOf a
  have hai : (idsOf N)[i] = a := List.getElem_idxOf hil
  have hiN : i < N.length := by simpa using hil
  obtain ⟨h1, h2⟩ := Matches.filter_obj hcore.recs a.x i hiN
  simp only [← hN, hai] at h1 h2
  rw [hop] at h1
  rw [hres] at h2
  have hrun : runOK regδ 0 N :=
    seqHist_mem_detSpec.1 ((legal_seqHist_iff _ _).1 hcore.legal a.x)
  obtain ⟨j, hj, hji, hjw⟩ := reg_run_write hrun hiN (Option.some_injective _ h1).symm
    (Option.some_injective _ (h2 (Completed.of_resOf hres))).symm hv
  have hjl : j < (idsOf N).length := by simpa using hj
  obtain ⟨h3, -⟩ := Matches.filter_obj hcore.recs a.x j hj
  have hbx := (mem_idsOf_filter_obj.1 (List.getElem_mem hjl)).2
  refine ⟨(idsOf N)[j], by rw [h3, hjw], hbx, ?_⟩
  rw [← pair_sublist_filter_obj hbx rfl]
  have := pair_sublist_of_lt hnd hil hjl hji
  rwa [hai] at this

/-- **FIFO queues**: in a linearization of `H` (legal for queues, initially empty), let `a` be a
dequeue that returned `v`, the only dequeue on its object, and let `c` be an enqueue of `u ≠ v`
linearized before `a`. Then an enqueue of `v` is linearized before `c`. -/
lemma queue_enq_before {H : History P X QOp QRes} {M : List (OpRec P X QOp QRes)}
    (hcore : LinCore queueSpec H M) {a : OpId P X} (hop : opOf H a = some .deq) {v : ℕ} (hres : resOf H a = some (.val v))
    (huniq : ∀ d, opOf H d = some .deq → d.x = a.x → d = a) {c : OpId P X}
    (hca : [c, a].Sublist (idsOf M)) (hcx : c.x = a.x) {u : ℕ} (hcop : opOf H c = some (.enq u))
    (huv : u ≠ v) :
    ∃ b, opOf H b = some (.enq v) ∧ b.x = a.x ∧ [b, c].Sublist (idsOf M) := by
  set N := M.filter (·.x = a.x) with hN
  have hnd := nodup_idsOf N
  have hca' := (pair_sublist_filter_obj (M := M) hcx rfl).2 hca
  rw [← hN] at hca'
  have hca'' := (pair_sublist_iff_idxOf hnd).1 hca'
  have haN : a ∈ idsOf N := hca''.2.1
  have hcN : c ∈ idsOf N := hca''.1
  have hil := List.idxOf_lt_length_of_mem haN
  have hcl := List.idxOf_lt_length_of_mem hcN
  set i := (idsOf N).idxOf a
  set jc := (idsOf N).idxOf c
  have hai : (idsOf N)[i] = a := List.getElem_idxOf hil
  have hcj : (idsOf N)[jc] = c := List.getElem_idxOf hcl
  have hiN : i < N.length := by simpa using hil
  have hjN : jc < N.length := by simpa using hcl
  obtain ⟨h1, h2⟩ := Matches.filter_obj hcore.recs a.x i hiN
  simp only [← hN, hai] at h1 h2
  rw [hop] at h1
  rw [hres] at h2
  obtain ⟨h1c, -⟩ := Matches.filter_obj hcore.recs a.x jc hjN
  simp only [← hN, hcj] at h1c
  rw [hcop] at h1c
  have hrun : runOK queueδ [] N :=
    seqHist_mem_detSpec.1 ((legal_seqHist_iff _ _).1 hcore.legal a.x)
  have hnodeq : ∀ d (hd : d < N.length), d < i → N[d].o ≠ .deq := by
    intro d hd hdi hdeq
    have hdl : d < (idsOf N).length := by simpa using hd
    obtain ⟨h3, -⟩ := Matches.filter_obj hcore.recs a.x d hd
    simp only [← hN] at h3
    rw [hdeq] at h3
    have hdx := (mem_idsOf_filter_obj.1 (List.getElem_mem hdl)).2
    have := huniq _ h3 hdx
    have h4 : (idsOf N)[d] = (idsOf N)[i] := this.trans hai.symm
    have := hnd.getElem_inj_iff.1 h4
    omega
  rcases queue_run_fifo hrun hiN (Option.some_injective _ h1).symm
      (Option.some_injective _ (h2 (Completed.of_resOf hres))).symm hnodeq hjN hca''.2.2
      (Option.some_injective _ h1c).symm huv with h | ⟨j, hj, hjj, hjw⟩
  · simp at h
  have hjl : j < (idsOf N).length := by simpa using hj
  obtain ⟨h3, -⟩ := Matches.filter_obj hcore.recs a.x j hj
  have hbx := (mem_idsOf_filter_obj.1 (List.getElem_mem hjl)).2
  refine ⟨(idsOf N)[j], by rw [h3, hjw], hbx, ?_⟩
  rw [← pair_sublist_filter_obj hbx hcx]
  have := pair_sublist_of_lt hnd hcl hjl hjj
  rwa [hcj] at this

end View

/-! ## The register pattern of Fig. 1 -/

section ReadWrite

variable {P X : Type} [DecidableEq P] [DecidableEq X] {p q : P} {o : X}

lemma readWrite_wellFormed (hpq : p ≠ q) : WellFormed (readWrite p q o) := by
  intro r
  by_cases hp : p = r
  · subst hp
    refine ⟨[⟨p, o, .read, .val 1⟩], Or.inl ?_⟩
    simp [restrictP, readWrite, hpq.symm, seqHist, OpRec.events]
  · by_cases hq : q = r
    · subst hq
      refine ⟨[], Or.inr ⟨q, o, .write 1, ?_⟩⟩
      simp [restrictP, readWrite, hp]
    · exact ⟨[], Or.inl (by simp [restrictP, readWrite, hp, hq])⟩

lemma readWrite_opOf (hpq : p ≠ q) {a : OpId P X} {op : RegOp} :
    opOf (readWrite p q o) a = some op ↔
      (a = ⟨p, o, 0⟩ ∧ op = .read) ∨ (a = ⟨q, o, 0⟩ ∧ op = .write 1) := by
  rcases a with ⟨r, y, k⟩
  simp only [opOf, readWrite, opsOf_cons, opsOf_nil, Event.invOf_inv, Event.invOf_res]
  split_ifs with h1 h2 h2 <;> rcases k with _ | _ | k <;> grind

lemma readWrite_completed {a : OpId P X} :
    Completed (readWrite p q o) a ↔ a = ⟨p, o, 0⟩ := by
  rcases a with ⟨r, y, k⟩
  simp only [Completed, readWrite, ressOf_cons, ressOf_nil, Event.resOf_inv, Event.resOf_res]
  split_ifs with h1 <;> grind

lemma readWrite_resOf : resOf (readWrite p q o) ⟨p, o, 0⟩ = some (.val 1) := by
  simp [resOf, readWrite]

lemma readWrite_precedes (hpq : p ≠ q) :
    Precedes (readWrite p q o) ⟨p, o, 0⟩ ⟨q, o, 0⟩ :=
  ⟨[.inv p o .read, .res p o (.val 1)], [.inv q o (.write 1)], rfl,
    by simp [Completed], by simp [Invoked, hpq]⟩

/-- **Section 3.1** (Fig. 1, generalized): `p` reads `1`, then `q` invokes `Write(1)`: this
history is linearizable by the original Definition 2.2, with the linearization
`S = q.Write(1) p.Read()→1`. -/
theorem readWrite_linearizableHW (hpq : p ≠ q) :
    LinearizableHW regSpec (readWrite p q o) := by
  have hwf := readWrite_wellFormed (o := o) hpq
  refine linearizableHW_iff.2 ⟨hwf, [⟨q, o, .write 1, .ok⟩, ⟨p, o, .read, .val 1⟩], ?_⟩
  have hids : idsOf [(⟨q, o, .write 1, .ok⟩ : OpRec P X RegOp RegRes), ⟨p, o, .read, .val 1⟩] =
      [⟨q, o, 0⟩, ⟨p, o, 0⟩] := by
    simp [idsOf, idsGo, cnt, hpq.symm]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a e h
    rw [hids] at h
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨(readWrite_opOf hpq).2 (Or.inr ⟨rfl, rfl⟩), fun hc => ?_⟩
      have := readWrite_completed.1 hc
      simp at this; exact absurd this hpq.symm
    · exact ⟨(readWrite_opOf hpq).2 (Or.inl ⟨rfl, rfl⟩), fun _ => readWrite_resOf⟩
  · intro a ha
    rw [readWrite_completed.1 ha, hids]; simp
  · rw [legal_seqHist_iff]
    intro x
    rw [regSpec, seqHist_mem_detSpec]
    by_cases hx : o = x
    · subst hx; simp [regδ]
    · simp [hx]
  · intro a b hab hpre hb
    have ha := readWrite_completed.1 hpre.completed
    rw [hids] at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst ha
    rcases hb with rfl | rfl
    · exact absurd hab hpq
    · exact absurd hpre (not_precedes_self hwf _)
  · intro a b hpre hb
    have ha := readWrite_completed.1 hpre.completed
    have hb := readWrite_completed.1 hb
    subst ha hb
    exact absurd hpre (not_precedes_self hwf _)

/-- **Section 5.1** (Fig. 1, generalized): the same history is not linearizable by the amended
Definition 4.1. -/
theorem readWrite_not_linearizable (hpq : p ≠ q) :
    ¬ Linearizable regSpec (readWrite p q o) := by
  intro h
  obtain ⟨-, M, hM⟩ := linearizable_iff.1 h
  have hr : (⟨p, o, 0⟩ : OpId P X) ∈ idsOf M := hM.complete _ (readWrite_completed.2 rfl)
  obtain ⟨b, hb, -, hba⟩ := reg_write_before hM.toLinCore hr
    ((readWrite_opOf hpq).2 (Or.inl ⟨rfl, rfl⟩)) readWrite_resOf one_ne_zero
  rcases (readWrite_opOf hpq).1 hb with ⟨-, h⟩ | ⟨rfl, -⟩
  · cases h
  have hab := hM.realtime _ _ (readWrite_precedes hpq) (List.Sublist.subset hba (by simp))
  exact pair_sublist_asymm (nodup_idsOf M) hab hba

/-- **Section 3.3** (Fig. 1, generalized): appending any response of `q`'s pending write yields
a history that is not linearizable by the original Definition 2.2. -/
theorem readWrite_res_not_linearizableHW (hpq : p ≠ q) (r : RegRes) :
    ¬ LinearizableHW regSpec (readWrite p q o ++ [.res q o r]) := by
  intro h
  obtain ⟨-, M, hM⟩ := linearizableHW_iff.1 h
  have hop : ∀ a op, opOf (readWrite p q o ++ [.res q o r]) a = some op ↔
      opOf (readWrite p q o) a = some op := by
    intro a op; simp [opOf]
  have hr : (⟨p, o, 0⟩ : OpId P X) ∈ idsOf M :=
    hM.complete _ (Completed.mono (readWrite_completed.2 rfl))
  obtain ⟨b, hb, -, hba⟩ := reg_write_before hM.toLinCore hr
    ((hop _ _).2 ((readWrite_opOf hpq).2 (Or.inl ⟨rfl, rfl⟩)))
    (by rw [resOf_append_of_completed (readWrite_completed.2 rfl)]; exact readWrite_resOf)
    one_ne_zero
  rcases (readWrite_opOf hpq).1 ((hop _ _).1 hb) with ⟨-, h⟩ | ⟨rfl, -⟩
  · cases h
  have hab := hM.realtime _ _ (readWrite_precedes hpq).mono (by simp [Completed, readWrite])
  exact pair_sublist_asymm (nodup_idsOf M) hab hba

end ReadWrite

/-! ## Fig. 1: `H1` -/

/-- **Section 3.1**: `H1` (Fig. 1) is linearizable by the original Definition 2.2. -/
theorem H1_linearizableHW : LinearizableHW regSpec H1 :=
  readWrite_linearizableHW (by decide)

/-- **Section 5.1**: `H1` (Fig. 1) is not linearizable by the amended Definition 4.1. -/
theorem H1_not_linearizable : ¬ Linearizable regSpec H1 :=
  readWrite_not_linearizable (by decide)

/-- `B`'s `Write(1)` is a pending invocation of `H1`. -/
theorem H1_pendingInv : PendingInv H1 B () (.write 1) := ⟨[], by decide⟩

/-- Register operations are total. -/
theorem regSpec_total {P X : Type} [DecidableEq P] [DecidableEq X] (p : P) (x : X)
    (op : RegOp) : Total regSpec p x op :=
  detSpec_total 0 regδ p x op

/-- **Section 3.3**: completing `B`'s pending write in `H1` (with any response) yields a history
that is not linearizable by the original Definition 2.2. -/
theorem H1_res_not_linearizableHW (r : RegRes) :
    ¬ LinearizableHW regSpec (H1 ++ [.res B () r]) :=
  readWrite_res_not_linearizableHW (by decide) r

/-! ## Fig. 2: `H2` -/

section H2

lemma H2_wellFormed : WellFormed H2 := by
  intro r
  cases r
  · exact ⟨[⟨A, (), .enq 1, .ok⟩, ⟨A, (), .deq, .val 2⟩], Or.inl (by decide)⟩
  · exact ⟨[], Or.inr ⟨B, (), .enq 2, by decide⟩⟩

lemma H2_opOf {a : OpId Proc Unit} {op : QOp} :
    opOf H2 a = some op ↔ (a = ⟨A, (), 0⟩ ∧ op = .enq 1) ∨ (a = ⟨A, (), 1⟩ ∧ op = .deq) ∨
      (a = ⟨B, (), 0⟩ ∧ op = .enq 2) := by
  rcases a with ⟨r, ⟨⟩, k⟩
  simp only [opOf, H2, opsOf_cons, opsOf_nil, Event.invOf_inv, Event.invOf_res]
  cases r <;> rcases k with _ | _ | k <;> simp [eq_comm]

lemma H2_completed {a : OpId Proc Unit} :
    Completed H2 a ↔ a = ⟨A, (), 0⟩ ∨ a = ⟨A, (), 1⟩ := by
  rcases a with ⟨r, ⟨⟩, k⟩
  simp only [Completed, H2, ressOf_cons, ressOf_nil, Event.resOf_inv, Event.resOf_res]
  cases r <;> rcases k with _ | _ | k <;> simp

lemma H2_resOf : resOf H2 ⟨A, (), 1⟩ = some (.val 2) := by decide

lemma H2_precedes_enq_deq : Precedes H2 ⟨A, (), 0⟩ ⟨A, (), 1⟩ :=
  ⟨H2.take 2, H2.drop 2, rfl, by decide, by decide⟩

lemma H2_precedes_enq_enq : Precedes H2 ⟨A, (), 0⟩ ⟨B, (), 0⟩ :=
  ⟨H2.take 2, H2.drop 2, rfl, by decide, by decide⟩

/-- **Section 3.1**: `H2` (Fig. 2) is linearizable by the original Definition 2.2, with the
linearization `S2 = B.Enq(2) A.Enq(1) A.Deq()→2`. -/
theorem H2_linearizableHW : LinearizableHW queueSpec H2 := by
  refine linearizableHW_iff.2 ⟨H2_wellFormed,
    [⟨B, (), .enq 2, .ok⟩, ⟨A, (), .enq 1, .ok⟩, ⟨A, (), .deq, .val 2⟩], ?_⟩
  have hids : idsOf [(⟨B, (), .enq 2, .ok⟩ : OpRec Proc Unit QOp QRes), ⟨A, (), .enq 1, .ok⟩,
      ⟨A, (), .deq, .val 2⟩] = [⟨B, (), 0⟩, ⟨A, (), 0⟩, ⟨A, (), 1⟩] := by decide
  have hno := H2_precedes_enq_deq.not_precedes H2_wellFormed
  have hself := not_precedes_self H2_wellFormed
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a e h
    rw [hids] at h
    simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, Prod.mk.injEq,
      List.not_mem_nil, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      refine ⟨H2_opOf.2 (by simp), fun hc => ?_⟩
    · simp [H2_completed] at hc
    · decide
    · exact H2_resOf
  · intro a ha
    rw [hids]; rcases H2_completed.1 ha with rfl | rfl <;> simp
  · rw [legal_seqHist_iff]
    intro x
    rw [queueSpec, seqHist_mem_detSpec]
    simp [queueδ]
  · intro a b hab hpre hb
    rw [hids] at hb ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases H2_completed.1 hpre.completed with rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;>
        first
        | decide
        | exact absurd hpre (hself _)
        | exact absurd hpre hno
        | exact absurd hab (by decide)
  · intro a b hpre hb
    rw [hids]
    rcases H2_completed.1 hpre.completed with rfl | rfl <;>
      rcases H2_completed.1 hb with rfl | rfl <;>
        first
        | decide
        | exact absurd hpre (hself _)
        | exact absurd hpre hno

/-- **Section 5.1**: `H2` (Fig. 2) is not linearizable by the amended Definition 4.1. -/
theorem H2_not_linearizable : ¬ Linearizable queueSpec H2 := by
  intro h
  obtain ⟨-, M, hM⟩ := linearizable_iff.1 h
  have hd : (⟨A, (), 1⟩ : OpId Proc Unit) ∈ idsOf M := hM.complete _ (H2_completed.2 (by simp))
  have hed := hM.realtime _ _ H2_precedes_enq_deq hd
  obtain ⟨b, hb, -, hbe⟩ := queue_enq_before hM.toLinCore (H2_opOf.2 (by simp)) H2_resOf
    (fun d hd _ => by simpa using H2_opOf.1 hd) hed rfl (u := 1) (H2_opOf.2 (by simp))
    (by decide)
  obtain rfl : b = ⟨B, (), 0⟩ := by simpa using H2_opOf.1 hb
  have heb := hM.realtime _ _ H2_precedes_enq_enq (List.Sublist.subset hbe (by simp))
  exact pair_sublist_asymm (nodup_idsOf M) heb hbe

/-- `B`'s `Enq(2)` is a pending invocation of `H2`. -/
theorem H2_pendingInv : PendingInv H2 B () (.enq 2) := ⟨[], by decide⟩

/-- Queue operations are total. -/
theorem queueSpec_total {P X : Type} [DecidableEq P] [DecidableEq X] (p : P) (x : X)
    (op : QOp) : Total queueSpec p x op :=
  detSpec_total [] queueδ p x op

/-- **Section 3.3**: completing `B`'s pending enqueue in `H2` (with any response) yields a
history that is not linearizable by the original Definition 2.2. -/
theorem H2_res_not_linearizableHW (r : QRes) :
    ¬ LinearizableHW queueSpec (H2 ++ [.res B () r]) := by
  intro h
  obtain ⟨-, M, hM⟩ := linearizableHW_iff.1 h
  have hop : ∀ a op, opOf (H2 ++ [.res B () r]) a = some op ↔ opOf H2 a = some op := by
    intro a op; simp [opOf]
  have hc : Completed (H2 ++ [.res B () r]) ⟨A, (), 1⟩ := (H2_completed.2 (by simp)).mono
  have hd : (⟨A, (), 1⟩ : OpId Proc Unit) ∈ idsOf M := hM.complete _ hc
  have hed := hM.procOrder ⟨A, (), 0⟩ ⟨A, (), 1⟩ rfl H2_precedes_enq_deq.mono hd
  obtain ⟨b, hb, -, hbe⟩ := queue_enq_before hM.toLinCore ((hop _ _).2 (H2_opOf.2 (by simp)))
    (by rw [resOf_append_of_completed (H2_completed.2 (by simp))]; exact H2_resOf)
    (fun d hd _ => by simpa using H2_opOf.1 ((hop _ _).1 hd)) hed rfl
    (u := 1) ((hop _ _).2 (H2_opOf.2 (by simp))) (by decide)
  obtain rfl : b = ⟨B, (), 0⟩ := by simpa using H2_opOf.1 ((hop _ _).1 hb)
  have heb := hM.realtime _ _ H2_precedes_enq_enq.mono (by simp [Completed, H2])
  exact pair_sublist_asymm (nodup_idsOf M) heb hbe

end H2

/-! ## Fig. 3: `H` (two registers) -/

section H3

lemma H3_restrictX_x : restrictX H3 .x = readWrite A B .x := by decide

lemma H3_restrictX_y : restrictX H3 .y = readWrite B A .y := by decide

lemma H3_wellFormed : WellFormed H3 := by
  intro r
  cases r
  · exact ⟨[⟨A, .x, .read, .val 1⟩], Or.inr ⟨A, .y, .write 1, by decide⟩⟩
  · exact ⟨[⟨B, .y, .read, .val 1⟩], Or.inr ⟨B, .x, .write 1, by decide⟩⟩

lemma H3_opOf_write {a : OpId Proc Reg2} (h : opOf H3 a = some (.write 1)) :
    a = ⟨A, .y, 0⟩ ∨ a = ⟨B, .x, 0⟩ := by
  rcases a with ⟨r, ob, k⟩
  simp only [opOf, H3, opsOf_cons, opsOf_nil, Event.invOf_inv] at h
  cases r <;> cases ob <;> rcases k with _ | k <;> simp at h <;> simp

/-- **Section 3.2**: each object subhistory of `H` (Fig. 3) is linearizable by the original
Definition 2.2 (each is a copy of `H1`). -/
theorem H3_restrictX_linearizableHW (o : Reg2) : LinearizableHW regSpec (restrictX H3 o) := by
  cases o
  · rw [H3_restrictX_x]; exact readWrite_linearizableHW (by decide)
  · rw [H3_restrictX_y]; exact readWrite_linearizableHW (by decide)

/-- **Section 3.2**: `H` (Fig. 3) is not linearizable by the original Definition 2.2: the
linearization order would contain the cycle
`x.Read() < y.Write(1) < y.Read() < x.Write(1) < x.Read()`. -/
theorem H3_not_linearizableHW : ¬ LinearizableHW regSpec H3 := by
  intro h
  obtain ⟨hwf, M, hM⟩ := linearizableHW_iff.1 h
  have hnd := nodup_idsOf M
  have hrx : (⟨A, .x, 0⟩ : OpId Proc Reg2) ∈ idsOf M := hM.complete _ (by decide)
  have hry : (⟨B, .y, 0⟩ : OpId Proc Reg2) ∈ idsOf M := hM.complete _ (by decide)
  obtain ⟨b1, hb1, hb1x, h1⟩ := reg_write_before hM.toLinCore hrx (by decide) (v := 1)
    (by decide) one_ne_zero
  obtain ⟨b2, hb2, hb2x, h2⟩ := reg_write_before hM.toLinCore hry (by decide) (v := 1)
    (by decide) one_ne_zero
  obtain rfl : b1 = ⟨B, .x, 0⟩ := by
    rcases H3_opOf_write hb1 with rfl | rfl
    · cases hb1x
    · rfl
  obtain rfl : b2 = ⟨A, .y, 0⟩ := by
    rcases H3_opOf_write hb2 with rfl | rfl
    · rfl
    · cases hb2x
  -- program order: `x.Read() < y.Write(1)` (process `A`), `y.Read() < x.Write(1)` (process `B`)
  have h3 := hM.procOrder ⟨A, .x, 0⟩ ⟨A, .y, 0⟩ rfl
    ⟨H3.take 3, H3.drop 3, rfl, by decide, by decide⟩ (h2.subset (by simp))
  have h4 := hM.procOrder ⟨B, .y, 0⟩ ⟨B, .x, 0⟩ rfl
    ⟨H3.take 4, H3.drop 4, rfl, by decide, by decide⟩ (h1.subset (by simp))
  exact pair_sublist_irrefl hnd _ (pair_sublist_trans hnd
    (pair_sublist_trans hnd (pair_sublist_trans hnd h3 h2) h4) h1)

/-- **Section 5.2** (remark): the object subhistories of `H` (Fig. 3) are not linearizable by
the amended Definition 4.1, so `H` is no counterexample to the locality of Definition 4.1. -/
theorem H3_restrictX_not_linearizable (o : Reg2) : ¬ Linearizable regSpec (restrictX H3 o) := by
  cases o
  · rw [H3_restrictX_x]; exact readWrite_not_linearizable (by decide)
  · rw [H3_restrictX_y]; exact readWrite_not_linearizable (by decide)

end H3

/-! ## Summary: the original definition is neither local nor nonblocking -/

/-- **Section 3.2**: linearizability by the original Definition 2.2 is not local: there is a
well-formed history (`H` of Fig. 3) all of whose object subhistories are linearizable while
the history itself is not. -/
theorem not_local_HW : ∃ (spec : SeqSpec Proc Reg2 RegOp RegRes)
    (H : History Proc Reg2 RegOp RegRes), WellFormed H ∧
      (∀ o, LinearizableHW spec (restrictX H o)) ∧ ¬ LinearizableHW spec H :=
  ⟨regSpec, H3, H3_wellFormed, H3_restrictX_linearizableHW, H3_not_linearizableHW⟩

/-- **Section 3.2**: the locality property fails for the original Definition 2.2. -/
theorem not_forall_local_HW : ¬ ∀ (spec : SeqSpec Proc Reg2 RegOp RegRes)
    (H : History Proc Reg2 RegOp RegRes), WellFormed H →
      (∀ o, LinearizableHW spec (restrictX H o)) → LinearizableHW spec H := by
  intro h
  obtain ⟨spec, H, hwf, hloc, hnot⟩ := not_local_HW
  exact hnot (h spec H hwf hloc)

/-- **Section 3.3** (register, Fig. 1): linearizability by the original Definition 2.2 is not
nonblocking: `H1` is linearizable and has a pending invocation of a total operation, but no
response to it yields a linearizable history. -/
theorem not_nonblocking_HW : ∃ (H : History Proc Unit RegOp RegRes) (p : Proc) (x : Unit)
    (op : RegOp), LinearizableHW regSpec H ∧ PendingInv H p x op ∧ Total regSpec p x op ∧
      ∀ r, ¬ LinearizableHW regSpec (H ++ [.res p x r]) :=
  ⟨H1, B, (), .write 1, H1_linearizableHW, H1_pendingInv, regSpec_total _ _ _,
    H1_res_not_linearizableHW⟩

/-- **Section 3.3** (FIFO queue, Fig. 2): the same with `H2` and `B`'s pending `Enq(y)`. -/
theorem not_nonblocking_HW_queue : ∃ (H : History Proc Unit QOp QRes) (p : Proc) (x : Unit)
    (op : QOp), LinearizableHW queueSpec H ∧ PendingInv H p x op ∧ Total queueSpec p x op ∧
      ∀ r, ¬ LinearizableHW queueSpec (H ++ [.res p x r]) :=
  ⟨H2, B, (), .enq 2, H2_linearizableHW, H2_pendingInv, queueSpec_total _ _ _,
    H2_res_not_linearizableHW⟩

/-- **Section 3.3**: the nonblocking property fails for the original Definition 2.2. -/
theorem not_forall_nonblocking_HW : ¬ ∀ (H : History Proc Unit RegOp RegRes) (p : Proc)
    (x : Unit) (op : RegOp), LinearizableHW regSpec H → PendingInv H p x op →
      Total regSpec p x op → ∃ r, LinearizableHW regSpec (H ++ [.res p x r]) := by
  intro h
  obtain ⟨H, p, x, op, hlin, hpend, htot, hnot⟩ := not_nonblocking_HW
  obtain ⟨r, hr⟩ := h H p x op hlin hpend htot
  exact hnot r hr

end Podc2021.LinearizabilityTypo
