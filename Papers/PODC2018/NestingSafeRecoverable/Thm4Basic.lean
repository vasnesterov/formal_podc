import Podc.Computability.Distributed.SharedMemory.NRL.Indist
import Cslib.Computability.Distributed.SharedMemory.ObjClasses
import Cslib.Computability.Distributed.SharedMemory.Objects.TestAndSet

/-!
# Theorem 4 of [ABH18], part 1: setting and basic facts

Setting of the impossibility proof: an NRL, wait-free implementation `A` of a (non-resettable,
non-readable, one-shot) test&set object from base objects; two processes `p ≠ q` invoke `T&S`
once each (configuration `C0`), and then only steps (of any process) and crashes of `p` happen
(`Reach`). In this file: one-shot bookkeeping, consequences of linearizability for test&set
(`lin_two`, `lin_single`), solo termination (`solo`).
-/

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL Cslib.SharedMemory.NRL.Alg

variable {P : Type} [DecidableEq P]

/-- Each process invokes at most one operation (the paper assumes that a process invokes `T&S`
at most once). -/
def OneShot (h : List (Label P tasObj)) : Prop := ∀ x, (opsOf h x).length ≤ 1

/-- Base objects for which the critical-configuration argument works: two operations on the
same object either absorb one another (the second behaves — new state and response — as if the
first had not happened) or lead to the same object state in both orders. Read/write registers
and test&set objects qualify (`critOK_of_rw_tas`). -/
def CritOK {ι : Type} (T : ι → ObjSpec) : Prop :=
  ∀ i (s : (T i).State) (a b : (T i).Op),
    (T i).δ ((T i).δ s a).1 b = (T i).δ s b ∨ (T i).δ ((T i).δ s b).1 a = (T i).δ s a ∨
      ((T i).δ ((T i).δ s a).1 b).1 = ((T i).δ ((T i).δ s b).1 a).1

lemma critOK_of_rw_tas {ι : Type} {T : ι → ObjSpec}
    (hT : ∀ i, (T i).RWLike ∨ (T i).TASLike) : CritOK T := by
  intro i s a b
  rcases hT i with h | ⟨s₁, h⟩
  · rcases h a with ha | ha
    · exact Or.inl (by rw [ha s])
    · rcases h b with hb | hb
      · exact Or.inr (Or.inl (by rw [hb s]))
      · exact Or.inl (hb _ _)
  · exact Or.inr (Or.inr (by rw [h, h]))

variable (A : Alg P tasObj)

/-- Both `p` and `q` have invoked `T&S`. -/
noncomputable def C0 (p q : P) : A.Cfg := A.init.run [.inv p (), .inv q ()]

/-- The events used in the proof: steps of any process and crashes of `p`. -/
def GEv (p : P) (e : Ev P tasObj) : Prop := (∃ y, e = .step y) ∨ e = .crash p

/-- Configurations reachable from `C0` by steps and crashes of `p`. -/
def Reach (p q : P) (C : A.Cfg) : Prop :=
  ∃ es : List (Ev P tasObj), (∀ e ∈ es, GEv p e) ∧ C = (C0 A p q).run es

/-- The hypotheses of Theorem 4 for the two processes `p ≠ q`. -/
structure Hyp (p q : P) : Prop where
  ne : p ≠ q
  nrl : A.NRL OneShot
  wf : A.WaitFree OneShot
  crit : CritOK A.T

variable {A}

/-- Responses of `x` so far. -/
abbrev resps (C : A.Cfg) (x : P) : List Bool := respsOf (N C.hist) x

/-- `x` has returned `b`. -/
def Ret (C : A.Cfg) (x : P) (b : Bool) : Prop := resps C x = [b]

/-- Steps of the processes in `xs`. -/
abbrev steps (xs : List P) : List (Ev P tasObj) := xs.map Ev.step

/-! ### Invocations -/

lemma ops_ev_of_not_inv (C : A.Cfg) {e : Ev P tasObj} (he : ∀ y o, e ≠ .inv y o) (x : P) :
    opsOf (N (C.ev e).hist) x = opsOf (N C.hist) x := by
  rcases e with ⟨y, o⟩ | y | y
  · exact absurd rfl (he y o)
  · rcases hs : C.st y with _ | ⟨o, pc, v⟩
    · rw [ev_step_of_none C hs]
    · rcases ha : A.act y o pc v with ⟨i, op, pc', k⟩ | ⟨pc', v'⟩ | r
      · rw [ev_step_access C hs ha]
      · rw [ev_step_internal C hs ha]
      · rw [ev_step_ret C hs ha]; simp [opsOf_append]
  · rcases hs : C.st y with _ | ⟨o, pc, v⟩
    · rw [ev_crash_of_none C hs]
    · rw [ev_crash_of_some C hs]; simp

lemma ops_run_of_not_inv (C : A.Cfg) {es : List (Ev P tasObj)}
    (he : ∀ e ∈ es, ∀ y o, e ≠ .inv y o) (x : P) :
    opsOf (N (C.run es).hist) x = opsOf (N C.hist) x := by
  induction es generalizing C with
  | nil => rfl
  | cons e es ih =>
    rw [Cfg.run_cons, ih (C.ev e) (fun e' h => he e' (by simp [h])),
      ops_ev_of_not_inv C (he e (by simp))]

lemma GEv.not_inv {p : P} {e : Ev P tasObj} (h : GEv p e) : ∀ y o, e ≠ .inv y o := by
  rintro y o rfl; rcases h with ⟨z, h⟩ | h <;> cases h

lemma st_none_run (C : A.Cfg) {x : P} (hx : C.st x = none) {es : List (Ev P tasObj)}
    (he : ∀ e ∈ es, ∀ o, e ≠ .inv x o) : (C.run es).st x = none := by
  induction es generalizing C with
  | nil => exact hx
  | cons e es ih =>
    apply ih _ _ (fun e' h => he e' (by simp [h]))
    rcases e with ⟨y, o⟩ | y | y
    · have hyx : x ≠ y := by rintro rfl; exact he _ (by simp) o rfl
      rcases hs : C.st y with _ | z
      · rw [ev_inv_of_none C o hs]; simp [hyx, hx]
      · rw [ev_inv_of_some C o hs, hx]
    · by_cases hyx : x = y
      · subst hyx; rw [ev_step_of_none C hx, hx]
      · rw [ev_step_st_ne hyx, hx]
    · by_cases hyx : x = y
      · subst hyx; rw [ev_crash_of_none C hx, hx]
      · rw [ev_crash_st_ne hyx, hx]

section Basic

variable {p q : P}

lemma C0_hist (hpq : p ≠ q) :
    (C0 A p q).hist = [.inv p (), .inv q ()] ∧ (C0 A p q).mem = A.init.mem ∧
      (C0 A p q).st p = some ((), A.start p ()) ∧ (C0 A p q).st q = some ((), A.start q ()) ∧
      ∀ y, y ≠ p → y ≠ q → (C0 A p q).st y = none := by
  have h1 : (A.init.ev (.inv p ())).st q = none := by
    rw [ev_inv_of_none (p := p) A.init () rfl]; simp [Ne.symm hpq, init]
  simp only [C0, Cfg.run_cons, Cfg.run_nil]
  rw [ev_inv_of_none (p := q) _ () h1, ev_inv_of_none (p := p) A.init () rfl]
  refine ⟨by simp [init], rfl, by simp [hpq], by simp, fun y hyp hyq => by simp [hyp, hyq, init]⟩

lemma ops_C0 (hpq : p ≠ q) (x : P) :
    opsOf (N (C0 A p q).hist) x = if x = p ∨ x = q then [()] else [] := by
  rw [(C0_hist hpq).1]
  by_cases hp : x = p
  · subst hp; simp [opsOf, N, HStep.toLabel, Ne.symm hpq]
  · by_cases hq : x = q
    · subst hq; simp [opsOf, N, HStep.toLabel, hp, Ne.symm hp]
    · simp [opsOf, N, HStep.toLabel, hp, hq, Ne.symm hp, Ne.symm hq]

lemma Reach.c0 : Reach A p q (C0 A p q) := ⟨[], by simp, rfl⟩

lemma Reach.ev {C : A.Cfg} (h : Reach A p q C) {e : Ev P tasObj} (he : GEv p e) :
    Reach A p q (C.ev e) := by
  obtain ⟨es, hes, rfl⟩ := h
  refine ⟨es ++ [e], ?_, by rw [Cfg.run_concat]⟩
  simp only [List.mem_append, List.mem_singleton]
  rintro e' (h | rfl)
  exacts [hes e' h, he]

lemma Reach.run {C : A.Cfg} (h : Reach A p q C) {es : List (Ev P tasObj)}
    (hes : ∀ e ∈ es, GEv p e) : Reach A p q (C.run es) := by
  induction es generalizing C with
  | nil => exact h
  | cons e es ih =>
    exact ih (h.ev (hes e (by simp))) (fun e' h' => hes e' (by simp [h']))

lemma Reach.steps {C : A.Cfg} (h : Reach A p q C) (xs : List P) :
    Reach A p q (C.run (steps xs)) :=
  h.run (by simp only [List.mem_map]; rintro e ⟨y, -, rfl⟩; exact Or.inl ⟨y, rfl⟩)

lemma Reach.ops (hpq : p ≠ q) {C : A.Cfg} (h : Reach A p q C) (x : P) :
    opsOf (N C.hist) x = if x = p ∨ x = q then [()] else [] := by
  obtain ⟨es, hes, rfl⟩ := h
  rw [ops_run_of_not_inv _ (fun e he => (hes e he).not_inv), ops_C0 hpq]

lemma Reach.oneShot (hpq : p ≠ q) {C : A.Cfg} (h : Reach A p q C) : OneShot (N C.hist) := by
  intro x; rw [h.ops hpq]; split_ifs <;> simp

/-- A reachable configuration is reached from the initial configuration. -/
lemma Reach.init {C : A.Cfg} (h : Reach A p q C) :
    ∃ es, C = A.init.run es ∧ ∀ (e : ℕ → Ev P tasObj), (∀ n, ∀ e' ∈ pre e n, GEv p e') →
      ∀ n, Reach A p q ((A.init.run es).run (pre e n)) := by
  obtain ⟨es, hes, rfl⟩ := h
  refine ⟨[.inv p (), .inv q ()] ++ es, by rw [Cfg.run_append]; rfl, fun e he n => ?_⟩
  rw [Cfg.run_append]
  exact (Reach.c0.run hes).run (he n)

lemma Reach.pend {C : A.Cfg} (h : Reach A p q C) (x : P) :
    (opsOf (N C.hist) x).length = (resps C x).length + (if (C.st x).isSome then 1 else 0) := by
  obtain ⟨es, -, rfl⟩ := h
  have := (wfInv_run (A := A) ([.inv p (), .inv q ()] ++ es)).pend x
  rwa [Cfg.run_append] at this

/-- `p` and `q` either run or have returned exactly one value. -/
lemma Reach.status (hpq : p ≠ q) {C : A.Cfg} (h : Reach A p q C) {x : P}
    (hx : x = p ∨ x = q) :
    ((C.st x).isSome ∧ resps C x = []) ∨ (C.st x = none ∧ ∃ b, Ret C x b) := by
  have h1 := h.pend x
  rw [h.ops hpq x, if_pos hx] at h1
  rcases hs : C.st x with _ | z
  · simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero,
      List.length_singleton] at h1
    obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 h1.symm
    exact Or.inr ⟨rfl, b, hb⟩
  · simp only [hs, Option.isSome_some, ↓reduceIte, List.length_singleton] at h1
    exact Or.inl ⟨rfl, List.eq_nil_of_length_eq_zero (by omega)⟩

lemma Reach.other (hpq : p ≠ q) {C : A.Cfg} (h : Reach A p q C) {y : P} (hyp : y ≠ p)
    (hyq : y ≠ q) : C.st y = none := by
  have h1 := h.pend y
  rw [h.ops hpq y, if_neg (by tauto)] at h1
  rcases hs : C.st y with _ | z
  · rfl
  · simp [hs] at h1

lemma Reach.running_iff (hpq : p ≠ q) {C : A.Cfg} (h : Reach A p q C) {x : P}
    (hx : x = p ∨ x = q) : (C.st x).isSome ↔ resps C x = [] := by
  rcases h.status hpq hx with ⟨h1, h2⟩ | ⟨h1, b, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · rw [h1]; simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rw [Ret] at h2; rw [h2]; simp

lemma Reach.ret_of_none (hpq : p ≠ q) {C : A.Cfg} (h : Reach A p q C) {x : P}
    (hx : x = p ∨ x = q) (hn : C.st x = none) : ∃ b, Ret C x b := by
  rcases h.status hpq hx with ⟨h1, -⟩ | ⟨-, h2⟩
  · rw [hn] at h1; simp at h1
  · exact h2

/-- Responses persist. -/
lemma Ret.run (hpq : p ≠ q) {C : A.Cfg} {x : P} {b : Bool} (hr : Ret C x b)
    {es : List (Ev P tasObj)} (h : Reach A p q (C.run es)) (hx : x = p ∨ x = q) :
    Ret (C.run es) x b := by
  unfold Ret resps at hr ⊢
  obtain ⟨hs, he⟩ := run_hist C es
  have hl := h.pend x
  rw [h.ops hpq x, if_pos hx] at hl
  have : resps (C.run es) x = [b] ++ respsOf (N hs) x := by
    simp only [resps, he, N_append, respsOf_append]; rw [hr]
  simp only [resps] at this hl
  rw [this] at hl ⊢
  simp only [List.length_singleton, List.singleton_append, List.length_cons,
    List.length_nil] at hl
  have : respsOf (N hs) x = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [this]; rfl

lemma Ret.unique {C : A.Cfg} {x : P} {b b' : Bool} (h : Ret C x b) (h' : Ret C x b') :
    b = b' := by
  rw [Ret] at h h'; rw [h] at h'; simpa using h'

end Basic

/-! ### Linearizability of test&set -/

section Lin

variable {α : List (Label P tasObj)}

lemma seqOK_true {L : List (OpId P × tasObj.Op)} (h : SeqOK α true L) :
    ∀ y ∈ L, ∀ r, respOf α y.1 = some r → r = true := by
  induction L with
  | nil => simp
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [SeqOK, tasObj_δ] at h
    intro z hz r hr
    rcases List.mem_cons.1 hz with rfl | hz
    · exact (h.1 r hr).symm
    · exact ih h.2 z hz r hr

/-- The first operation of a linearization of test&set returns `false` (if it returns), all
the others return `true`. -/
lemma seqOK_false {y : OpId P × tasObj.Op} {L : List (OpId P × tasObj.Op)}
    (h : SeqOK α false (y :: L)) :
    (∀ r, respOf α y.1 = some r → r = false) ∧ ∀ z ∈ L, ∀ r, respOf α z.1 = some r → r = true := by
  obtain ⟨y, o⟩ := y
  simp only [SeqOK, tasObj_δ] at h
  exact ⟨fun r hr => (h.1 r hr).symm, seqOK_true h.2⟩

lemma respOf_of_resps {x : P} {b : Bool} (h : respsOf α x = [b]) : respOf α (x, 0) = some b := by
  simp [respOf, h]

lemma completed_of_resps {x : P} {b : Bool} (h : respsOf α x = [b]) : Completed α (x, 0) := by
  simp [Completed, h]

lemma eq_of_opOf {y : OpId P} {o : tasObj.Op} (h : opOf α y = some o) {x : P}
    (hx : opsOf α y.1 = [()] ∨ opsOf α y.1 = []) (hxx : opsOf α y.1 = [()] → y.1 = x) :
    y = (x, 0) := by
  simp only [opOf] at h
  rcases hx with hx | hx
  · rw [hx] at h
    obtain ⟨y1, y2⟩ := y
    have : y2 = 0 := by
      rcases y2 with _ | y2
      · rfl
      · simp at h
    simp only at hxx
    rw [this, hxx hx]
  · rw [hx] at h; simp at h

/-- Two completed one-shot `T&S` operations return different values. -/
lemma lin_two {L : List (OpId P × tasObj.Op)} (hL : IsLinearization α L) {p q : P}
    (hpq : p ≠ q) (hops : ∀ x, opsOf α x = if x = p ∨ x = q then [()] else [])
    {bp bq : Bool} (hp : respsOf α p = [bp]) (hq : respsOf α q = [bq]) : bp ≠ bq := by
  have hpL := hL.complete _ (completed_of_resps hp)
  have hqL := hL.complete _ (completed_of_resps hq)
  have hinv : ∀ y ∈ L, y.1 = (p, 0) ∨ y.1 = (q, 0) := by
    intro y hy
    have h := hL.op_eq y hy
    by_cases h1 : y.1.1 = p
    · left; exact eq_of_opOf h (by rw [hops]; simp [h1]) (fun _ => h1)
    · by_cases h2 : y.1.1 = q
      · right; exact eq_of_opOf h (by rw [hops]; simp [h2]) (fun _ => h2)
      · exfalso
        have := eq_of_opOf (x := p) h (by rw [hops]; simp [h1, h2]) (by rw [hops]; simp [h1, h2])
        exact h1 (by rw [this])
  rcases L with _ | ⟨y, L⟩
  · simp at hpL
  have hs := seqOK_false hL.seq
  have hnd := hL.nodup
  simp only [List.map_cons, List.nodup_cons] at hnd
  intro hb; subst hb
  rcases hinv y (by simp) with hy | hy
  · -- `p` is first; `q` is in the rest
    have hqy : (q, 0) ≠ y.1 := by rw [hy]; simp [Ne.symm hpq]
    simp only [List.map_cons, List.mem_cons] at hqL
    rcases hqL with hqL | hqL
    · exact hqy hqL
    obtain ⟨z, hz, hz1⟩ := List.mem_map.1 hqL
    have h1 := hs.1 bp (by rw [hy]; exact respOf_of_resps hp)
    have h2 := hs.2 z hz bp (by rw [hz1]; exact respOf_of_resps hq)
    rw [h1] at h2; simp at h2
  · have hpy : (p, 0) ≠ y.1 := by rw [hy]; simp [hpq]
    simp only [List.map_cons, List.mem_cons] at hpL
    rcases hpL with hpL | hpL
    · exact hpy hpL
    obtain ⟨z, hz, hz1⟩ := List.mem_map.1 hpL
    have h1 := hs.1 bp (by rw [hy]; exact respOf_of_resps hq)
    have h2 := hs.2 z hz bp (by rw [hz1]; exact respOf_of_resps hp)
    rw [h1] at h2; simp at h2

/-- A one-shot `T&S` operation that completes when no other operation was invoked returns
`false`. -/
lemma lin_single {L : List (OpId P × tasObj.Op)} (hL : IsLinearization α L) {q : P}
    (hops : ∀ x, opsOf α x = if x = q then [()] else []) {b : Bool} (hq : respsOf α q = [b]) :
    b = false := by
  have hqL := hL.complete _ (completed_of_resps hq)
  rcases L with _ | ⟨y, L⟩
  · simp at hqL
  have hy : y.1 = (q, 0) := by
    have h := hL.op_eq y (by simp)
    by_cases h1 : y.1.1 = q
    · exact eq_of_opOf h (by rw [hops]; simp [h1]) (fun _ => h1)
    · exact eq_of_opOf h (by rw [hops]; simp [h1]) (by rw [hops]; simp [h1])
  exact (seqOK_false hL.seq).1 b (by rw [hy]; exact respOf_of_resps hq)

end Lin

end Podc.NestingSafeRecoverable
