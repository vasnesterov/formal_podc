import Papers.PODC2026.ConflictFreedom.Domain

/-!
# Algorithm 2: a read-write implementation of generalized commit-adopt (definitions)

Kuznetsov, Sutra and Toyos-Marfurt, *Conflict-Freedom as a Progress Condition*, PODC 2026,
Section 5.

`n` processes `Fin n` share two atomic snapshot objects `A` and `B` (entries `none` = `⊥`).
Process `i` with input `s_i` executes four atomic steps (local state `GCA.Loc`, program counter
`pc`):

* `pc = 0`: `A[i] ← s_i` (line 2);
* `pc = 1`: `A_i ← A.snap()` (line 3);
* `pc = 2`: `B[i] ← (⊔ A_i^co, A_i = A_i^co)` (lines 4–5);
* `pc = 3`: `B_i ← B.snap()` (line 6);
* `pc = 4`: returned; the output `(β_i, commit_i)` of lines 7–9 is `GCA.Loc.output`.

`GCA.State` is a global state (the two snapshot objects and the local states of the participants,
`none` = not invoked); `GCA.Reach` is the set of reachable states, where at any time a
non-participant may invoke `propose` with an arbitrary input and a participant that has not
returned may take its next step. Crashes are implicit (a process may stop taking steps).

Conventions for `⊥` (Appendix A.4): `comp` and `⊔` ignore `⊥` entries, and `⊥` entries of `A_i`
stay `⊥` in `A_i^co` (the paper's `⊓ S = ⊥` when `⊥ ∈ S`; elsewhere `⊓` is only applied to sets of
non-`⊥` traces). In line 9, `∀ a_k : a_k ≤ β_i ⟹ b_k ≠ ⊥` ranges over the non-`⊥` entries of `A_i`.
-/

namespace Podc.ConflictFreedom

namespace GCA

open Classical

variable {n : ℕ} {T : Type*} [GCADomain T]

/-- The non-`⊥` values of a view. -/
noncomputable def vals {V : Type*} (v : Fin n → Option V) : Finset V :=
  Finset.univ.biUnion fun k => (v k).toFinset

/-- Line 4: `a^co = ⊓ ({a} ∪ {a_j ∈ A_i : ¬ comp({a_j, a})})`. -/
noncomputable def coEntry (v : Fin n → Option T) (a : T) : T :=
  (insert a ((vals v).filter fun b => ¬ Compat ({a, b} : Set T))).inf'
    (Finset.insert_nonempty _ _) id

/-- Line 4: the view `A_i^co`. -/
noncomputable def co (v : Fin n → Option T) : Fin n → Option T := fun k => (v k).map (coEntry v)

/-- Line 5: the candidate `⊔ A_i^co` written to `B`. -/
noncomputable def candidate (v : Fin n → Option T) : T := GCADomain.lub (vals (co v))

/-- Line 5: the compatibility flag `A_i = A_i^co`. -/
noncomputable def compatFlag (v : Fin n → Option T) : Bool := decide (co v = v)

/-- The candidates with a raised flag in a view of `B`. -/
noncomputable def flagged (w : Fin n → Option (T × Bool)) : Finset T :=
  Finset.univ.biUnion fun k => match w k with
    | some (b, true) => {b}
    | _ => ∅

/-- Line 7: the output trace `β_i` (`own` is the candidate `b_i` of the process itself). -/
noncomputable def beta (own : T) (w : Fin n → Option (T × Bool)) : T :=
  if h : (flagged w).Nonempty then (flagged w).inf' h id else own

/-- Line 8: the weak-agreement flag `w_i`. -/
def weakFlag (s : T) (v : Fin n → Option T) (w : Fin n → Option (T × Bool)) : Prop :=
  (∀ k a, v k = some a → a = s) ∧ (∀ k b c, w k = some (b, c) → b = s)

/-- Line 9: whether the process commits `β`. -/
noncomputable def commitFlag (s : T) (v : Fin n → Option T) (w : Fin n → Option (T × Bool))
    (β : T) : Bool :=
  decide (weakFlag s v w ∨
    ((∀ k a, v k = some a → a ≤ β → (w k).isSome) ∧ ∀ k b, w k ≠ some (b, false)))

/-- Local state of a participant of Algorithm 2. -/
structure Loc (n : ℕ) (T : Type*) where
  /-- The input trace `s_i`. -/
  inp : T
  /-- Program counter: number of steps taken (`4` = returned). -/
  pc : ℕ
  /-- The view `A_i` of `A` (meaningful once `pc ≥ 2`). -/
  av : Fin n → Option T
  /-- The view `B_i` of `B` (meaningful once `pc = 4`). -/
  bv : Fin n → Option (T × Bool)

/-- Local state right after the invocation of `propose(s)`. -/
def Loc.init (s : T) : Loc n T := ⟨s, 0, fun _ => none, fun _ => none⟩

/-- The output `(β_i, c_i)` of lines 7–9 (meaningful once `pc = 4`). -/
noncomputable def Loc.output (l : Loc n T) : T × Bool :=
  (beta (candidate l.av) l.bv, commitFlag l.inp l.av l.bv (beta (candidate l.av) l.bv))

/-- A global state of Algorithm 2. -/
structure State (n : ℕ) (T : Type*) where
  /-- The snapshot object `A`. -/
  A : Fin n → Option T
  /-- The snapshot object `B`. -/
  B : Fin n → Option (T × Bool)
  /-- Local states of the participants (`none` = has not invoked `propose`). -/
  loc : Fin n → Option (Loc n T)

/-- The initial state. -/
def State.init : State n T := ⟨fun _ => none, fun _ => none, fun _ => none⟩

/-- The effect of the next step of process `i` in local state `l` on `(A, B, l)`. -/
noncomputable def stepLoc (A : Fin n → Option T) (B : Fin n → Option (T × Bool)) (i : Fin n)
    (l : Loc n T) : (Fin n → Option T) × (Fin n → Option (T × Bool)) × Loc n T :=
  match l.pc with
  | 0 => (Function.update A i (some l.inp), B, { l with pc := 1 })
  | 1 => (A, B, { l with pc := 2, av := A })
  | 2 => (A, Function.update B i (some (candidate l.av, compatFlag l.av)), { l with pc := 3 })
  | 3 => (A, B, { l with pc := 4, bv := B })
  | _ => (A, B, l)

/-- The next step of process `i` (in local state `l`) applied to the global state. -/
noncomputable def State.step (g : State n T) (i : Fin n) (l : Loc n T) : State n T :=
  ⟨(stepLoc g.A g.B i l).1, (stepLoc g.A g.B i l).2.1,
    Function.update g.loc i (some (stepLoc g.A g.B i l).2.2)⟩

/-- Reachable global states: invocations by non-participants and steps of participants that have
not returned, in any order. -/
inductive Reach : State n T → Prop
  | init : Reach State.init
  | invoke {g : State n T} (i : Fin n) (s : T) : Reach g → g.loc i = none →
      Reach { g with loc := Function.update g.loc i (some (Loc.init s)) }
  | step {g : State n T} (i : Fin n) (l : Loc n T) : Reach g → g.loc i = some l → l.pc < 4 →
      Reach (g.step i l)

/-- `i` has returned from `propose` in `g` (`i ∈ P_r`) with local state `l`. -/
def Returned (g : State n T) (i : Fin n) (l : Loc n T) : Prop := g.loc i = some l ∧ l.pc = 4

/-- The input traces of the participants. -/
def inputs (g : State n T) : Set T := {x | ∃ j l, g.loc j = some l ∧ x = l.inp}

/-- The output traces of the processes that have returned. -/
def outputs (g : State n T) : Set T := {x | ∃ j l, Returned g j l ∧ x = l.output.1}

/-! ### The properties of generalized commit-adopt (Section 4.2) -/

/-- (1) Validity: output traces contain only input operations (for any notion of "operations of
a trace" `supp` that is monotone and subadditive on least upper bounds). -/
def Validity (g : State n T) : Prop :=
  ∀ {C : Type} (supp : T → Set C), (∀ x y, x ≤ y → supp x ⊆ supp y) →
    (∀ S : Finset T, Compat (S : Set T) → supp (GCADomain.lub S) ⊆ ⋃ x ∈ S, supp x) →
    ∀ i l, Returned g i l → supp l.output.1 ⊆ ⋃ x ∈ inputs g, supp x

/-- (2) Adoption: a committed trace is extended by every output trace. -/
def Adoption (g : State n T) : Prop :=
  ∀ i li j lj, Returned g i li → Returned g j lj → li.output.2 = true →
    li.output.1 ≤ lj.output.1

/-- (3) Commitment: if all input traces are compatible and all participants have returned, some
process commits an extension of its own input. -/
def Commitment (g : State n T) : Prop :=
  Compat (inputs g) → (∀ j l, g.loc j = some l → l.pc = 4) → (∃ j, g.loc j ≠ none) →
    ∃ j l, Returned g j l ∧ l.inp ≤ l.output.1 ∧ l.output.2 = true

/-- (4) Convergence: output traces are mutually compatible. -/
def Convergence (g : State n T) : Prop := Compat (outputs g)

/-- (5) Common prefix: output traces extend every common prefix of the input traces. -/
def CommonPrefix (g : State n T) : Prop :=
  ∀ x, (∀ y ∈ inputs g, x ≤ y) → ∀ i l, Returned g i l → x ≤ l.output.1

/-- (6) Weak agreement: if all input traces are equal, then no process adopts. -/
def WeakAgreement (g : State n T) : Prop :=
  (∀ x ∈ inputs g, ∀ y ∈ inputs g, x = y) → ∀ i l, Returned g i l → l.output.2 = true

/-- All six properties of generalized commit-adopt. -/
def IsGCA (g : State n T) : Prop :=
  Validity g ∧ Adoption g ∧ Commitment g ∧ Convergence g ∧ CommonPrefix g ∧ WeakAgreement g

end GCA

end Podc.ConflictFreedom
