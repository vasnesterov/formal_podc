import Mathlib

/-!
# Porting non-mutating optimizations (Section 4 of [paper])

Protocols are TLA+-style specifications: an initial predicate and a family of subactions
(`Spec`). `B` refines `A` under a state mapping `f` (Section 4.1) if initial states map to initial
states and every subaction `b_j` of `B` implies a subaction `a_{imp j}` of `A` on the mapped states,
or a stuttering step (`imp j = none`).

A *non-mutating optimization* `A∆` of `A` (Section 4.2) adds new variables `σD`, conjoins extra
clauses `guard i` to the subactions of `A` (an unchanged subaction has `guard i = True`), and adds
new subactions that do not change the variables of `A`.

The porting recipe of Section 4.3 builds `B∆` from `B` and `A∆` (`port`): case 1, an added
subaction of `A∆` with the variables of `A` replaced by `f` of those of `B` (and `B` unchanged);
cases 2–3, every subaction `b_j` conjoined with the clauses added to the subaction it implies
(evaluated at `f` of the states of `B`); a stuttering `b_j` keeps the new variables.

`port_refines_opt` and `port_refines_base` are the two refinements claimed in Section 4.3 ("`B∆`
refines `A∆`", "`B∆` refines `B`"); `Refines.reachable` transfers invariants along a refinement.

The paper's argument, and these theorems, need *single-step* refinement (`b_j ⇒ a_i`). The
refinement of Raft* into MultiPaxos is not single-step (Appendix C: one `AppendEntries` is several
`Phase2a`/`Phase2b` steps). For multi-step refinements, conjoining the added clauses evaluated at
the end points is unsound: `naive_multistep_port_unsound` is a two-line counterexample.
-/

namespace Podc.PaxosRaftRefinement.Porting

open Relation

/-- A specification: initial states and subactions indexed by `ι`. -/
structure Spec (σ ι : Type*) where
  /-- `Init`. -/
  init : σ → Prop
  /-- The subactions; `Next` is their disjunction. -/
  act : ι → σ → σ → Prop

variable {σA σB σD ι κ ν : Type*}

/-- `Next = ∃ i, a_i`. -/
def Spec.Next (A : Spec σA ι) (s s' : σA) : Prop := ∃ i, A.act i s s'

/-- Reachable states (`Init ∧ □[Next]`, stuttering steps add nothing). -/
def Spec.Reachable (A : Spec σA ι) (s : σA) : Prop := ∃ s₀, A.init s₀ ∧ ReflTransGen A.Next s₀ s

/-- Section 4.1: `B` refines `A` under the state mapping `f`, the subaction `b_j` implying
`a_{imp j}` (or a stuttering step if `imp j = none`). -/
structure Refines (B : Spec σB κ) (A : Spec σA ι) (f : σB → σA) (imp : κ → Option ι) : Prop where
  init : ∀ s, B.init s → A.init (f s)
  step : ∀ j s s', B.act j s s' →
    match imp j with
    | some i => A.act i (f s) (f s')
    | none => f s' = f s

/-- Refinement transfers reachability, hence every invariant of `A` holds on the image of the
reachable states of `B`. -/
theorem Refines.reachable {B : Spec σB κ} {A : Spec σA ι} {f : σB → σA} {imp : κ → Option ι}
    (h : Refines B A f imp) {s : σB} (hs : B.Reachable s) : A.Reachable (f s) := by
  obtain ⟨s₀, h₀, hp⟩ := hs
  refine ⟨f s₀, h.init s₀ h₀, ?_⟩
  induction hp with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨j, hj⟩ := hst
    have := h.step j _ _ hj
    revert this
    cases imp j with
    | some i => exact fun hi => ih.tail ⟨i, hi⟩
    | none => intro he; simpa [he] using ih

/-- Section 4.2: a non-mutating optimization of `A` with new variables `σD`. -/
structure Opt (A : Spec σA ι) (σD ν : Type*) where
  /-- Initial values of the new variables (may read the variables of `A`). -/
  initD : σA → σD → Prop
  /-- The clauses conjoined to subaction `a_i` (`True` for an unchanged subaction). -/
  guard : ι → σA × σD → σA × σD → Prop
  /-- The added subactions. -/
  added : ν → σA × σD → σA × σD → Prop
  /-- Added subactions do not mutate the variables of `A`. -/
  added_nonmut : ∀ k x y, added k x y → y.1 = x.1

variable {A : Spec σA ι}

/-- The optimized protocol `A∆`. -/
def Opt.spec (O : Opt A σD ν) : Spec (σA × σD) (ι ⊕ ν) where
  init x := A.init x.1 ∧ O.initD x.1 x.2
  act
    | .inl i => fun x y => A.act i x.1 y.1 ∧ O.guard i x y
    | .inr k => O.added k

/-- `A∆` refines `A` under the identity mapping that drops the new variables (Section 4.2). -/
theorem Opt.refines (O : Opt A σD ν) :
    Refines O.spec A Prod.fst (fun | .inl i => some i | .inr _ => none) where
  init _ h := h.1
  step
    | .inl _, _, _, h => h.1
    | .inr k, x, y, h => O.added_nonmut k x y h

/-- Section 4.3: the ported protocol `B∆`. -/
def port (B : Spec σB κ) (f : σB → σA) (imp : κ → Option ι) (O : Opt A σD ν) :
    Spec (σB × σD) (κ ⊕ ν) where
  init x := B.init x.1 ∧ O.initD (f x.1) x.2
  act
    | .inl j => fun x y => B.act j x.1 y.1 ∧
        match imp j with
        | some i => O.guard i (f x.1, x.2) (f y.1, y.2)
        | none => y.2 = x.2
    | .inr k => fun x y => O.added k (f x.1, x.2) (f y.1, y.2) ∧ y.1 = x.1

/-- **Section 4.3, first claim**: `B∆` refines `A∆` under `(b, d) ↦ (f b, d)`. -/
theorem port_refines_opt {B : Spec σB κ} {f : σB → σA} {imp : κ → Option ι}
    (h : Refines B A f imp) (O : Opt A σD ν) :
    Refines (port B f imp O) O.spec (fun x => (f x.1, x.2))
      (fun | .inl j => (imp j).map Sum.inl | .inr k => some (.inr k)) where
  init x hx := ⟨h.init _ hx.1, hx.2⟩
  step
    | .inl j, x, y, hxy => by
      obtain ⟨hb0, hg⟩ := hxy
      have hb := h.step j _ _ hb0
      cases hi : imp j with
      | some i =>
        simp only [hi] at hb hg ⊢
        exact ⟨hb, hg⟩
      | none =>
        simp only [hi] at hb hg ⊢
        simp [hb, hg]
    | .inr k, x, y, hxy => hxy.1

/-- **Section 4.3, second claim**: `B∆` refines `B` (drop the new variables). -/
theorem port_refines_base {B : Spec σB κ} {f : σB → σA} {imp : κ → Option ι}
    (O : Opt A σD ν) :
    Refines (port B f imp O) B Prod.fst (fun | .inl j => some j | .inr _ => none) where
  init _ hx := hx.1
  step
    | .inl _, _, _, hxy => hxy.1
    | .inr _, _, _, hxy => hxy.2

/-- Consequently every invariant of `A∆` holds on the image of `B∆` and every invariant of `B`
holds on `B∆`: "the derived protocol is guaranteed correct". -/
theorem port_correct {B : Spec σB κ} {f : σB → σA} {imp : κ → Option ι}
    (h : Refines B A f imp) (O : Opt A σD ν) {x : σB × σD} (hx : (port B f imp O).Reachable x) :
    O.spec.Reachable (f x.1, x.2) ∧ B.Reachable x.1 :=
  ⟨(port_refines_opt h O).reachable hx, (port_refines_base O).reachable hx⟩

/-! ### Multi-step refinements

In a multi-step refinement a `B` step implies a *sequence* of `A` steps. Conjoining the clauses
added to those `A` subactions, evaluated at the end points of the `B` step, is not sound.
`A`: a counter `x` with one subaction `x' = x + 1`; `B`: a counter with one subaction
`x' = x + 2` (one `B` step = two `A` steps). `A∆` adds `d' = d + 1`, so `A∆` keeps `d = x`.
The naive port `x' = x + 2 ∧ d' = d + 1` reaches `x = 2, d = 1`. -/

/-- The counter `A`. -/
def cntA : Spec ℕ Unit := ⟨fun x => x = 0, fun _ x y => y = x + 1⟩

/-- The optimization: a second counter `d` incremented with `x`. -/
def cntOpt : Opt cntA ℕ Empty where
  initD _ d := d = 0
  guard _ x y := y.2 = x.2 + 1
  added k := k.elim
  added_nonmut k := k.elim

/-- The naive port to the double-step counter `B` (clauses evaluated at the end points). -/
def naivePort : Spec (ℕ × ℕ) Unit :=
  ⟨fun x => x.1 = 0 ∧ x.2 = 0, fun _ x y => y.1 = x.1 + 2 ∧ y.2 = x.2 + 1⟩

theorem cntOpt_inv {x : ℕ × ℕ} (hx : cntOpt.spec.Reachable x) : x.2 = x.1 := by
  obtain ⟨x₀, ⟨h1, h2⟩, hp⟩ := hx
  induction hp with
  | refl => simp only [cntA, cntOpt] at h1 h2; omega
  | tail _ hst ih =>
    obtain ⟨i, hi⟩ := hst
    rcases i with i | k
    · obtain ⟨ha, hg⟩ := hi
      simp only [cntA] at ha
      simp only [cntOpt] at hg
      omega
    · exact k.elim

/-- The naive multi-step port violates the invariant `d = x` of `A∆`. -/
theorem naive_multistep_port_unsound :
    ∃ x, naivePort.Reachable x ∧ ¬ cntOpt.spec.Reachable x := by
  refine ⟨(2, 1), ⟨(0, 0), ⟨rfl, rfl⟩, ReflTransGen.single ⟨(), rfl, rfl⟩⟩, fun h => ?_⟩
  have := cntOpt_inv h
  simp at this

end Podc.PaxosRaftRefinement.Porting
