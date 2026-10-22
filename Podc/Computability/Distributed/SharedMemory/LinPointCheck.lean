import Cslib.Computability.Distributed.SharedMemory.LinPoints

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/LinPointCheck.lean

/-!
# Histories annotated with linearization points

A convenient way to show that a concrete (adversarially scheduled) history is linearizable is to
mark, inside the history, the *linearization point* of each operation: a label `lin p` between the
invocation and the response of the operation of `p`. If, running the sequential specification
along the annotated history, every response equals the response that the specification gives at
the linearization point, then **every prefix** of the (unannotated) history is linearizable.

* `LPLabel P A`: labels `inv p o`, `ret p r` and linearization points `lin p`;
  `LPLabel.erase` forgets the linearization points.
* `lpStep`, `lpRun`: the checker. Its configuration is the abstract state together with the status
  of every process (`LPStatus`: idle, pending with operation `o`, or linearized with response `r`).
  `lpRun c l = some c'` means that the annotated history `l` is legal from configuration `c`.
* `LPInv`: the invariant relating a configuration to an (erased) history and a linearization.
* **Main theorem** `isLinearization_of_lpRun`: if `lpRun (A.init, fun _ => .idle) l = some c`
  then every prefix of `l.filterMap LPLabel.erase` has a linearization.

Block lemmas for computing `lpRun` on structured histories: `lpRun_append`,
`lpRun_triple` (a sequential operation `inv p o, lin p, ret p r`), `lpRun_map_single` (one label
per process of a duplicate-free list of processes, each changing only the status of its process).
-/

namespace Cslib.SharedMemory

open List

variable {P : Type} {A : ObjSpec}

/-- History labels annotated with linearization points. -/
inductive LPLabel (P : Type) (A : ObjSpec) where
  /-- `p` invokes `o` -/
  | inv (p : P) (o : A.Op)
  /-- `p` receives response `r` -/
  | ret (p : P) (r : A.Resp)
  /-- linearization point of the pending operation of `p` -/
  | lin (p : P)

/-- Forget linearization points. -/
def LPLabel.erase : LPLabel P A → Option (Label P A)
  | .inv p o => some (.inv p o)
  | .ret p r => some (.ret p r)
  | .lin _ => none

/-- Status of a process while checking an annotated history. -/
inductive LPStatus (A : ObjSpec) where
  /-- no pending operation -/
  | idle
  /-- pending operation `o`, not yet linearized -/
  | pending (o : A.Op)
  /-- pending operation, linearized with response `r` -/
  | linearized (r : A.Resp)

variable [DecidableEq P] [DecidableEq A.Resp]

/-- One step of the linearization-point checker. -/
def lpStep : A.State × (P → LPStatus A) → LPLabel P A → Option (A.State × (P → LPStatus A))
  | (s, st), .inv p o => match st p with
    | .idle => some (s, Function.update st p (.pending o))
    | _ => none
  | (s, st), .lin p => match st p with
    | .pending o => some ((A.δ s o).1, Function.update st p (.linearized (A.δ s o).2))
    | _ => none
  | (s, st), .ret p r => match st p with
    | .linearized r' => if r = r' then some (s, Function.update st p .idle) else none
    | _ => none

/-- Run the linearization-point checker along an annotated history. -/
def lpRun : A.State × (P → LPStatus A) → List (LPLabel P A) → Option (A.State × (P → LPStatus A))
  | c, [] => some c
  | c, ℓ :: l => (lpStep c ℓ).bind (fun c' => lpRun c' l)

@[simp] lemma lpRun_nil (c : A.State × (P → LPStatus A)) : lpRun c [] = some c := rfl

lemma lpRun_cons (c : A.State × (P → LPStatus A)) (ℓ : LPLabel P A) (l : List (LPLabel P A)) :
    lpRun c (ℓ :: l) = (lpStep c ℓ).bind (fun c' => lpRun c' l) := rfl

lemma lpRun_append (c : A.State × (P → LPStatus A)) (l₁ l₂ : List (LPLabel P A)) :
    lpRun c (l₁ ++ l₂) = (lpRun c l₁).bind (fun c' => lpRun c' l₂) := by
  induction l₁ generalizing c with
  | nil => simp
  | cons ℓ l₁ ih =>
    simp only [cons_append, lpRun_cons, ih]
    cases lpStep c ℓ <;> simp

/-- A sequential operation: invocation, linearization point and response in a row. -/
lemma lpRun_triple {s : A.State} {st : P → LPStatus A} {p : P} (o : A.Op)
    (hp : st p = .idle) (l : List (LPLabel P A)) :
    lpRun (s, st) (.inv p o :: .lin p :: .ret p (A.δ s o).2 :: l) =
      lpRun ((A.δ s o).1, st) l := by
  simp only [lpRun_cons, lpStep, hp, Function.update_self, Function.update_idem, Option.bind_some,
    ite_true]
  rw [show Function.update st p LPStatus.idle = st from by
    rw [← hp]; exact Function.update_eq_self p st]

/-- `lpRun_triple` with the response given explicitly. -/
lemma lpRun_triple' {s : A.State} {st : P → LPStatus A} {p : P} (o : A.Op) {r : A.Resp}
    (hp : st p = .idle) (hr : (A.δ s o).2 = r) (l : List (LPLabel P A)) :
    lpRun (s, st) (.inv p o :: .lin p :: .ret p r :: l) = lpRun ((A.δ s o).1, st) l := by
  subst hr; exact lpRun_triple o hp l

/-- Sequential operations of the processes of `ps` (all idle) that do not change the state
`s`. -/
lemma lpRun_flatMap_triple_const (o : P → A.Op) (r : P → A.Resp) {s : A.State}
    (ps : List P) (hδ : ∀ p ∈ ps, A.δ s (o p) = (s, r p)) (st : P → LPStatus A)
    (hst : ∀ p ∈ ps, st p = .idle) :
    lpRun (s, st) (ps.flatMap (fun p => [.inv p (o p), .lin p, .ret p (r p)])) = some (s, st) := by
  induction ps with
  | nil => simp
  | cons q ps ih =>
    rw [flatMap_cons, cons_append, cons_append, cons_append, nil_append,
      lpRun_triple' (o q) (hst q (by simp)) (by rw [hδ q (by simp)])]
    rw [hδ q (by simp)]
    exact ih (fun p hp => hδ p (by simp [hp])) (fun p hp => hst p (by simp [hp]))

/-- Sequential operations of the processes of the nonempty list `ps` (all idle), each of which
leads from any state to the state `s₁`. -/
lemma lpRun_flatMap_triple_set (o : P → A.Op) (r : P → A.Resp) {s s₁ : A.State}
    (ps : List P) (hne : ps ≠ []) (hδ : ∀ p ∈ ps, ∀ t, A.δ t (o p) = (s₁, r p))
    (st : P → LPStatus A) (hst : ∀ p ∈ ps, st p = .idle) :
    lpRun (s, st) (ps.flatMap (fun p => [.inv p (o p), .lin p, .ret p (r p)])) =
      some (s₁, st) := by
  cases ps with
  | nil => exact absurd rfl hne
  | cons q ps =>
    rw [flatMap_cons, cons_append, cons_append, cons_append, nil_append,
      lpRun_triple' (o q) (hst q (by simp)) (by rw [hδ q (by simp)])]
    rw [hδ q (by simp)]
    exact lpRun_flatMap_triple_const o r ps (fun p hp => hδ p (by simp [hp]) s₁)
      st (fun p hp => hst p (by simp [hp]))

/-- One label for each process of a duplicate-free list `ps`; the label of `p` takes `p` from
status `a p` to status `b p` and does not change the abstract state. -/
lemma lpRun_map_single (f : P → LPLabel P A) (a b : P → LPStatus A) {s : A.State}
    (hf : ∀ p (st : P → LPStatus A), st p = a p →
      lpStep (s, st) (f p) = some (s, Function.update st p (b p)))
    (ps : List P) (hps : ps.Nodup) (st : P → LPStatus A) (hst : ∀ p ∈ ps, st p = a p) :
    lpRun (s, st) (ps.map f) =
      some (s, fun p => if p ∈ ps then b p else st p) := by
  induction ps generalizing st with
  | nil => simp
  | cons q ps ih =>
    rw [nodup_cons] at hps
    simp only [map_cons, lpRun_cons, hf q st (hst q (by simp)), Option.bind_some]
    rw [ih hps.2]
    · congr 2; funext p
      by_cases hpq : p = q
      · subst hpq; simp [hps.1]
      · simp [hpq]
    · intro p hp
      rw [Function.update_of_ne (fun h => hps.1 (by rw [← h]; exact hp))]
      exact hst p (by simp [hp])

/-! ## The invariant -/

/-- The status of `p` is consistent with the history `α` and the linearization `L`. -/
def StatusOK (α : List (Label P A)) (L : List (OpId P × A.Op)) (p : P) : LPStatus A → Prop
  | .idle => (opsOf α p).length = (respsOf α p).length
  | .pending o => (opsOf α p).length = (respsOf α p).length + 1 ∧
      opOf α (p, (respsOf α p).length) = some o ∧ (p, (respsOf α p).length) ∉ L.map Prod.fst
  | .linearized r => (opsOf α p).length = (respsOf α p).length + 1 ∧
      A.respIn A.init L (p, (respsOf α p).length) = some r

/-- Invariant of the checker: `L` linearizes `α`, leads to the state `s`, and the statuses are
consistent. -/
structure LPInv (α : List (Label P A)) (s : A.State) (st : P → LPStatus A)
    (L : List (OpId P × A.Op)) : Prop where
  lin : IsLinearization α L
  state : A.runOps A.init (L.map Prod.snd) = s
  status : ∀ p, StatusOK α L p (st p)

omit [DecidableEq A.Resp] in
lemma lpInv_nil : LPInv ([] : List (Label P A)) A.init (fun _ => .idle) [] :=
  ⟨isLinearization_nil, rfl, fun _ => by simp [StatusOK]⟩

omit [DecidableEq A.Resp] in
lemma opsOf_concat_ret (α : List (Label P A)) (p q : P) (r : A.Resp) :
    opsOf (α ++ [.ret p r]) q = opsOf α q := by simp

omit [DecidableEq A.Resp] in
lemma respsOf_concat_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    respsOf (α ++ [.inv p o]) q = respsOf α q := by simp

/-- One step of the checker preserves the invariant. -/
lemma LPInv.step {α : List (Label P A)} {s : A.State} {st : P → LPStatus A}
    {L : List (OpId P × A.Op)} (h : LPInv α s st L) {ℓ : LPLabel P A}
    {c' : A.State × (P → LPStatus A)} (hc : lpStep (s, st) ℓ = some c') :
    ∃ L', LPInv (α ++ (ℓ.erase).toList) c'.1 c'.2 L' := by
  cases ℓ with
  | inv p o =>
    simp only [lpStep] at hc
    split at hc <;> try simp at hc
    rename_i hp
    cases hc
    have hsp := h.status p; rw [hp] at hsp; simp only [StatusOK] at hsp
    refine ⟨L, h.lin.append_inv p o, h.state, fun q => ?_⟩
    simp only [LPLabel.erase, Option.toList_some]
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, StatusOK, respsOf_concat_inv]
      refine ⟨by simp [hsp], ?_, ?_⟩
      · rw [opOf_concat_inv, ite_eq_left (by rw [hsp])]
      · intro hm
        have := h.lin.invoked_of_mem hm
        simp [Invoked] at this; omega
    · rw [Function.update_of_ne hqp]
      have hq := h.status q
      have hops : opsOf (α ++ [.inv p o]) q = opsOf α q := by simp [Ne.symm hqp]
      have hop : ∀ k, opOf (α ++ [.inv p o]) (q, k) = opOf α (q, k) := by
        intro k; simp [opOf, Ne.symm hqp]
      have hres := respsOf_concat_inv α p q o
      cases hst : st q with
      | idle => rw [hst] at hq; simp only [StatusOK, hops, hres]; exact hq
      | pending o' =>
        rw [hst] at hq; obtain ⟨h1, h2, h3⟩ := hq
        simp only [StatusOK, hops, hres, hop]; exact ⟨h1, h2, h3⟩
      | linearized r =>
        rw [hst] at hq; obtain ⟨h1, h2⟩ := hq
        simp only [StatusOK, hops, hres]; exact ⟨h1, h2⟩
  | lin p =>
    simp only [lpStep] at hc
    split at hc <;> try simp at hc
    rename_i o hp
    cases hc
    have hsp := h.status p; rw [hp] at hsp; simp only [StatusOK] at hsp
    obtain ⟨hlen, hop, hnot⟩ := hsp
    refine ⟨L ++ [((p, (respsOf α p).length), o)], ?_, ?_, fun q => ?_⟩
    · simp only [LPLabel.erase, Option.toList_none, append_nil]
      exact h.lin.push hop hnot (by simp [Completed])
    · simp [ObjSpec.runOps_append, h.state]
    · simp only [LPLabel.erase, Option.toList_none, append_nil]
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, StatusOK]
        refine ⟨hlen, ?_⟩
        rw [ObjSpec.respIn_concat_self hnot, h.state]
      · rw [Function.update_of_ne hqp]
        have hq := h.status q
        cases hst : st q with
        | idle => rw [hst] at hq; exact hq
        | pending o' =>
          rw [hst] at hq; obtain ⟨h1, h2, h3⟩ := hq
          refine ⟨h1, h2, ?_⟩
          simp only [map_append, map_cons, map_nil, mem_append, mem_singleton, Prod.mk.injEq,
            not_or]
          exact ⟨h3, fun h' => hqp h'.1⟩
        | linearized r =>
          rw [hst] at hq; obtain ⟨h1, h2⟩ := hq
          exact ⟨h1, ObjSpec.respIn_append_of_eq_some h2 _⟩
  | ret p r =>
    simp only [lpStep] at hc
    split at hc <;> try simp at hc
    rename_i r' hp
    obtain ⟨rfl, hc⟩ := hc
    cases hc
    have hsp := h.status p; rw [hp] at hsp; simp only [StatusOK] at hsp
    obtain ⟨hlen, hr⟩ := hsp
    refine ⟨L, h.lin.append_ret_of_respIn hr, h.state, fun q => ?_⟩
    simp only [LPLabel.erase, Option.toList_some]
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, StatusOK, opsOf_concat_ret]
      simp [hlen]
    · rw [Function.update_of_ne hqp]
      have hq := h.status q
      have hresps : respsOf (α ++ [.ret p r]) q = respsOf α q := by simp [Ne.symm hqp]
      have hop : ∀ k, opOf (α ++ [.ret p r]) (q, k) = opOf α (q, k) := by
        intro k; simp [opOf]
      have hops := opsOf_concat_ret α p q r
      cases hst : st q with
      | idle => rw [hst] at hq; simp only [StatusOK, hops, hresps]; exact hq
      | pending o' =>
        rw [hst] at hq; obtain ⟨h1, h2, h3⟩ := hq
        simp only [StatusOK, hops, hresps, hop]; exact ⟨h1, h2, h3⟩
      | linearized r =>
        rw [hst] at hq; obtain ⟨h1, h2⟩ := hq
        simp only [StatusOK, hops, hresps]; exact ⟨h1, h2⟩

/-- If the checker accepts `l` from a configuration satisfying the invariant for `α`, every
extension of `α` by a prefix of the erasure of `l` is linearizable. -/
theorem LPInv.isLinearization_of_lpRun {l : List (LPLabel P A)} :
    ∀ {α : List (Label P A)} {s : A.State} {st : P → LPStatus A} {L : List (OpId P × A.Op)}
      {c' : A.State × (P → LPStatus A)}, LPInv α s st L → lpRun (s, st) l = some c' →
      ∀ β, β <+: l.filterMap LPLabel.erase → ∃ L', IsLinearization (α ++ β) L' := by
  induction l with
  | nil =>
    intro α s st L c' h _ β hβ
    simp only [filterMap_nil, prefix_nil] at hβ; subst hβ
    exact ⟨L, by simpa using h.lin⟩
  | cons ℓ l ih =>
    intro α s st L c' h hrun β hβ
    rw [lpRun_cons] at hrun
    cases hstep : lpStep (s, st) ℓ with
    | none => rw [hstep] at hrun; simp at hrun
    | some c₁ =>
      rw [hstep, Option.bind_some] at hrun
      obtain ⟨L₁, h₁⟩ := h.step hstep
      rcases β with _ | ⟨b, β⟩
      · exact ⟨L, by simpa using h.lin⟩
      cases he : ℓ.erase with
      | none =>
        rw [filterMap_cons, he] at hβ
        obtain ⟨L', hL'⟩ := ih (α := α ++ (ℓ.erase).toList) h₁ hrun _ hβ
        rw [he] at hL'; exact ⟨L', by simpa using hL'⟩
      | some e =>
        rw [filterMap_cons, he, cons_prefix_cons] at hβ
        obtain ⟨rfl, hβ⟩ := hβ
        obtain ⟨L', hL'⟩ := ih (α := α ++ (ℓ.erase).toList) h₁ hrun _ hβ
        rw [he] at hL'; exact ⟨L', by simpa using hL'⟩

/-- **Linearization points.** If the checker accepts the annotated history `l` from the initial
configuration, every prefix of the history `l.filterMap LPLabel.erase` is linearizable. -/
theorem isLinearization_of_lpRun {l : List (LPLabel P A)} {c' : A.State × (P → LPStatus A)}
    (h : lpRun (A.init, fun _ => .idle) l = some c') {β : List (Label P A)}
    (hβ : β <+: l.filterMap LPLabel.erase) : ∃ L, IsLinearization β L := by
  simpa using lpInv_nil.isLinearization_of_lpRun h β hβ

end Cslib.SharedMemory
