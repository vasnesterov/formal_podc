import Papers.PODC2022.BluntingAdversary.MDP
import Cslib.Computability.Distributed.SharedMemory.StrongLin

/-!
# Randomized programs using shared objects (Sections 2–4 of the paper)

Attiya, Enea, Welch, *Blunting an Adversary Against Randomized Concurrent Programs with
Linearizable Implementations*, PODC 2022 (arXiv 2106.15554v2).

## Programs (Section 2.3)

A `Program P A C` gives every process `p : P` a deterministic client with states `C`; in every
state the client either computes locally (`loc`), samples uniformly from a set of `m + 1` values
(`rnd`, the paper's `random(V)`), invokes an operation `o` of the shared object `A` and continues
with the response (`call o k`), or has terminated (`done`). A finite set of objects is modelled
as one object whose operations are tagged with the object they belong to (the paper relies on the
locality of its notions, Theorem 3.1, to do the same).

## Objects

An object is used through an `ObjSem`: per-process local states `L`, a shared memory `M`, the
local state after an invocation (or an immediate response, for atomic objects), and the next
internal action of an invocation: a deterministic step on the memory, a uniform random choice
(only used by the transformed objects `O^k`), or a return.

* `implSem I Π`: a deterministic shared-memory implementation `I` (CSLib's `Impl`: base
  objects with sequential specifications accessed atomically, deterministic per-process code)
  together with a *preamble mapping*, given as the set `Π p l` of local states that are still
  inside the preamble of the current operation (Section 3: "`i` passed `Π(M)`" = the local state of
  the invocation is no longer in the preamble).
* `atomSem A`: the atomic object with sequential specification `A` (every invocation returns
  in the same step).
* `iterSem I Π k`: the preamble-iterating transformation `O^k` (Algorithm 2).

## Executions and adversaries (Section 2.4)

`sys Pr O` is the game whose states are configurations (client states, which processes are inside
an operation, object local states, memory) plus two ghost fields: the number of program random
steps so far (`coins`) and a flag `badCoin` recording whether some program random step happened
while some invocation was inside its preamble (i.e. the execution prefix ending with that random
step was not complete w.r.t. `Π`). A strong adversary chooses which process moves next, knowing
the whole configuration (and hence all previous random values). `prob Pr O B` is the paper's
`Prob[P(O) → B]` for a set `B` of *outcomes*, which we take to be predicates on the final client
states (they record whatever the program observed, in particular the values returned by its
invocations).
-/

set_option linter.unusedSectionVars false

-- CSLib candidate (generic infrastructure for randomized programs over shared objects)
namespace Podc.BluntingAdversary

open Cslib.SharedMemory
open scoped Classical

/-! ## Programs -/

/-- A client instruction. -/
inductive CAct (A : ObjSpec) (C : Type) where
  /-- Local computation. -/
  | loc (c : C)
  /-- `random(V)` with `|V| = m + 1`: continue with `g v` for a uniformly random `v`. -/
  | rnd (m : ℕ) (g : Fin (m + 1) → C)
  /-- Invoke operation `o`; continue with `k r` where `r` is the response. -/
  | call (o : A.Op) (k : A.Resp → C)
  /-- The process has terminated. -/
  | done

/-- A randomized program: one deterministic client per process. -/
structure Program (P : Type) (A : ObjSpec) (C : Type) where
  /-- Initial client states. -/
  init : P → C
  /-- The next instruction. -/
  next : P → C → CAct A C

/-! ## Objects -/

/-- The next internal action of an invocation. -/
inductive OMove (A : ObjSpec) (L M : Type) where
  /-- A deterministic step, possibly changing the memory. -/
  | step (l : L) (m : M)
  /-- A uniform random choice among `n + 1` local states (object random step). -/
  | rand (n : ℕ) (g : Fin (n + 1) → L)
  /-- Return response `r`, continue in local state `l`. -/
  | ret (r : A.Resp) (l : L)

/-- The semantics of an object used by the processes `P`. The natural number passed to `call`
and `act` is the number of program random steps so far; it is only used by the ghost
bookkeeping of the transformed objects (which preamble iterations overlap a random step). -/
structure ObjSem (P : Type) (A : ObjSpec) (L M : Type) where
  /-- Initial memory. -/
  memInit : M
  /-- Initial local states. -/
  locInit : P → L
  /-- Invocation: enter the object (`inl`) or return immediately (`inr`, atomic objects). -/
  call : P → L → A.Op → M → ℕ → (L × M) ⊕ (A.Resp × L × M)
  /-- The next internal action of a pending invocation. -/
  act : P → L → M → ℕ → OMove A L M
  /-- Local states inside the preamble of the current invocation. -/
  inPre : P → L → Prop

/-! ## Configurations and the game -/

/-- A configuration of `P(O)`. -/
structure Cfg (P C L M : Type) where
  /-- Client states. -/
  cl : P → C
  /-- Processes inside an object invocation. -/
  busy : P → Bool
  /-- Object local states. -/
  lo : P → L
  /-- Shared memory. -/
  mem : M
  /-- Ghost: number of program random steps so far. -/
  coins : ℕ
  /-- Ghost: some program random step happened while an invocation was inside its preamble. -/
  badCoin : Bool

variable {P : Type} [DecidableEq P] {A : ObjSpec} {C L M : Type}

/-- Some invocation is inside its preamble (the execution is not complete w.r.t. `Π`). -/
def Cfg.inPreamble (O : ObjSem P A L M) (s : Cfg P C L M) : Prop :=
  ∃ q, s.busy q = true ∧ O.inPre q (s.lo q)

/-- The move of process `p`. -/
noncomputable def sysMove (Pr : Program P A C) (O : ObjSem P A L M) (s : Cfg P C L M) (p : P) :
    Move (Cfg P C L M) :=
  if s.busy p then
    match O.act p (s.lo p) s.mem s.coins with
    | .step l m => .det { s with lo := Function.update s.lo p l, mem := m }
    | .rand n g => .rand n fun i => { s with lo := Function.update s.lo p (g i) }
    | .ret r l =>
      match Pr.next p (s.cl p) with
      | .call _ k => .det { s with cl := Function.update s.cl p (k r),
                                   busy := Function.update s.busy p false,
                                   lo := Function.update s.lo p l }
      | _ => .stop
  else
    match Pr.next p (s.cl p) with
    | .loc c => .det { s with cl := Function.update s.cl p c }
    | .rnd m g => .rand m fun i =>
        { s with cl := Function.update s.cl p (g i), coins := s.coins + 1,
                 badCoin := s.badCoin || decide (s.inPreamble O) }
    | .call o k =>
      match O.call p (s.lo p) o s.mem s.coins with
      | .inl (l, m) => .det { s with busy := Function.update s.busy p true,
                                     lo := Function.update s.lo p l, mem := m }
      | .inr (r, l, m) => .det { s with cl := Function.update s.cl p (k r),
                                        lo := Function.update s.lo p l, mem := m }
    | .done => .stop

/-- The game `P(O)` against a strong adversary. -/
noncomputable def sys (Pr : Program P A C) (O : ObjSem P A L M) : MDP P (Cfg P C L M) :=
  ⟨sysMove Pr O⟩

/-- The initial configuration. -/
def initCfg (Pr : Program P A C) (O : ObjSem P A L M) : Cfg P C L M :=
  ⟨Pr.init, fun _ => false, O.locInit, O.memInit, 0, false⟩

/-- Indicator payoff of a set `B` of outcomes. -/
noncomputable def payB (B : (P → C) → Prop) (s : Cfg P C L M) : ℝ := if B s.cl then 1 else 0

/-- Indicator payoff of `B` on executions all of whose program random steps happened at
complete prefixes. -/
noncomputable def paySafe (B : (P → C) → Prop) (s : Cfg P C L M) : ℝ :=
  if B s.cl ∧ s.badCoin = false then 1 else 0

/-- **`Prob[P(O) → B]`**: the maximal probability, over all strong adversaries, that the program
terminates with an outcome in `B`. -/
noncomputable def prob (Pr : Program P A C) (O : ObjSem P A L M) (B : (P → C) → Prop) : ℝ :=
  (sys Pr O).opt (payB B) (initCfg Pr O)

/-- `P(O)` has at most `r` program random steps in every execution. -/
def AtMostRandom (Pr : Program P A C) (O : ObjSem P A L M) (r : ℕ) : Prop :=
  ∀ s, (sys Pr O).Reach (initCfg Pr O) s → s.coins ≤ r

lemma payB_nonneg (B : (P → C) → Prop) (s : Cfg P C L M) : 0 ≤ payB B s := by
  unfold payB; split_ifs <;> norm_num
lemma payB_le_one (B : (P → C) → Prop) (s : Cfg P C L M) : payB B s ≤ 1 := by
  unfold payB; split_ifs <;> norm_num
lemma paySafe_nonneg (B : (P → C) → Prop) (s : Cfg P C L M) : 0 ≤ paySafe B s := by
  unfold paySafe; split_ifs <;> norm_num
lemma paySafe_le_one (B : (P → C) → Prop) (s : Cfg P C L M) : paySafe B s ≤ 1 := by
  unfold paySafe; split_ifs <;> norm_num
lemma paySafe_le_payB (B : (P → C) → Prop) (s : Cfg P C L M) : paySafe B s ≤ payB B s := by
  unfold paySafe payB; split_ifs <;> simp_all

/-! ## The three kinds of objects -/

section Impl

variable {ι : Type} [DecidableEq ι] {Bs : ι → ObjSpec}

/-- Memory of an implementation: the states of its base objects. -/
abbrev Mem (Bs : ι → ObjSpec) := (i : ι) → (Bs i).State

/-- A deterministic implementation `I` of `A` with preamble mapping `Π` (`Pi p l`: the local
state `l` of `p` is inside the preamble of the current invocation). -/
noncomputable def implSem (I : Impl A Bs P L) (Pi : P → L → Prop) : ObjSem P A L (Mem Bs) where
  memInit := I.memInit
  locInit := I.locInit
  call p l o m _ := .inl (I.invoke p l o, m)
  act p l m _ :=
    match I.act p l with
    | .access i o k => .step (k ((Bs i).δ (m i) o).2) (Function.update m i ((Bs i).δ (m i) o).1)
    | .ret r l' => .ret r l'
  inPre := Pi

/-- The preamble mapping is well formed (Section 3): every invocation passes `Π(M)` before it
returns, and once passed it is not re-entered (it is not inside a loop). -/
structure PreambleWF (I : Impl A Bs P L) (Pi : P → L → Prop) : Prop where
  stay : ∀ p l i o k r, ¬ Pi p l → I.act p l = .access i o k → ¬ Pi p (k r)
  ret : ∀ p l r l', I.act p l = .ret r l' → ¬ Pi p l

/-- Effect-free preambles (Section 4.1): every step inside a preamble applies a read-only
primitive (it does not change the state of the base object). -/
def EffectFree (I : Impl A Bs P L) (Pi : P → L → Prop) : Prop :=
  ∀ p l i o k, Pi p l → I.act p l = .access i o k → (Bs i).ReadOnly o

/-- An execution of the object is *complete* w.r.t. `Π` if every pending invocation has passed
its preamble. -/
def Complete (Pi : P → L → Prop) (C : Config A Bs P L) : Prop :=
  ∀ p, C.pend p ≠ none → ¬ Pi p (C.loc p)

/-- **Tail strong linearizability** (Section 3): the object is linearizable, and its
executions that are complete w.r.t. `Π` admit a prefix-preserving linearization function. -/
def TailStronglyLinearizable (I : Impl A Bs P L) (Pi : P → L → Prop) : Prop :=
  I.Linearizable ∧ ∃ f : List (Label P A) → List (OpId P × A.Op),
    (∀ α C, I.run α = some C → Complete Pi C → IsLinearization α (f α)) ∧
    (∀ α β C C', I.run α = some C → I.run β = some C' → Complete Pi C → Complete Pi C' →
      α <+: β → f α <+: f β)

end Impl

/-- The atomic object with sequential specification `A`. -/
def atomSem (A : ObjSpec) : ObjSem P A Unit A.State where
  memInit := A.init
  locInit _ := ()
  call _ _ o q _ := .inr ((A.δ q o).2, (), (A.δ q o).1)
  act _ _ q _ := .step () q
  inPre _ _ := False

/-! ## The preamble-iterating transformation (Algorithm 2) -/

/-- Phase of an invocation of `O^k`. -/
inductive Phase where
  /-- Iterating the preamble. -/
  | pre
  /-- All `k` iterations done; the random choice is next. -/
  | choose
  /-- Running the rest of the code with the chosen iteration's local state. -/
  | tail
  deriving DecidableEq

/-- Local state of `O^k`. Besides the local state `cur` of the original code, an invocation
remembers the local state `prev` before the invocation, the restart point `base` (the local state
right after the invocation), and the results `res` of the completed iterations, each with a ghost
flag telling whether a program random step happened during that iteration. Ghost fields: `sc` =
number of program random steps when the current iteration started, `sp` = the current iteration
overlapped a program random step, `xbad` = some object random step chose an iteration that
overlapped a program random step (the complement of the paper's event `X`). -/
structure LK (L : Type) where
  cur : L
  prev : L
  base : L
  ph : Phase
  res : List (L × Bool)
  sc : ℕ
  sp : Bool
  xbad : Bool

section Iter

variable {ι : Type} [DecidableEq ι] {Bs : ι → ObjSpec}

/-- **The transformed object `O^k`** (Algorithm 2): every invocation runs the preamble `k`
times from the local state reached by the invocation, then picks one of the `k` results
uniformly at random and runs the rest of the code from it. -/
noncomputable def iterSem (I : Impl A Bs P L) (Pi : P → L → Prop) (k : ℕ) :
    ObjSem P A (LK L) (Mem Bs) where
  memInit := I.memInit
  locInit p := ⟨I.locInit p, I.locInit p, I.locInit p, .tail, [], 0, false, false⟩
  call p lk o m c :=
    .inl (⟨I.invoke p lk.cur o, lk.cur, I.invoke p lk.cur o, .pre, [], c, false, lk.xbad⟩, m)
  act p lk m c :=
    match lk.ph with
    | .pre =>
      if Pi p lk.cur then
        match I.act p lk.cur with
        | .access i o κ =>
          .step { lk with cur := κ ((Bs i).δ (m i) o).2,
                          sp := if Pi p (κ ((Bs i).δ (m i) o).2) then lk.sp else decide (c ≠ lk.sc) }
            (Function.update m i ((Bs i).δ (m i) o).1)
        | .ret _ _ => .step lk m
      else
        if lk.res.length + 1 < k then
          .step { lk with cur := lk.base, res := lk.res ++ [(lk.cur, lk.sp)], sc := c, sp := false } m
        else
          .step { lk with res := lk.res ++ [(lk.cur, lk.sp)], ph := .choose } m
    | .choose =>
      .rand (k - 1) fun j =>
        let e := lk.res.getD j (lk.cur, false)
        { lk with cur := e.1, ph := .tail, xbad := lk.xbad || e.2 }
    | .tail =>
      match I.act p lk.cur with
      | .access i o κ =>
        .step { lk with cur := κ ((Bs i).δ (m i) o).2 } (Function.update m i ((Bs i).δ (m i) o).1)
      | .ret r l' => .ret r { lk with cur := l' }
  inPre _ _ := False

/-- Payoff `B ∧ X`: outcome in `B` and every object random step chose a randomization-free
preamble iteration. -/
noncomputable def payBX (B : (P → C) → Prop) (s : Cfg P C (LK L) M) : ℝ :=
  if B s.cl ∧ ∀ p, (s.lo p).xbad = false then 1 else 0

/-- Payoff `¬X`. -/
noncomputable def payNX (s : Cfg P C (LK L) M) : ℝ :=
  if ∃ p, (s.lo p).xbad = true then 1 else 0

end Iter

end Podc.BluntingAdversary
