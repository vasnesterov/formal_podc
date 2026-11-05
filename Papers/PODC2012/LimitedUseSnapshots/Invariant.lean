import Papers.PODC2012.LimitedUseSnapshots.Semantics
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# The invariant of the corrected Algorithm 2

Definitions of the invariant `Inv α C` (execution `α` of `alg P T true` with final configuration
`C`) used to prove that the corrected algorithm satisfies the max-array linearizability criterion
of `Criterion.lean`, and its basic stability lemmas.

The invariant follows the paper's proof (Lemmas 3.1–3.3, Theorem 3.4) and the erratum, flattened
over the whole tree:

* `g1` — `second` of a child is at most `second` of its parent (Lemma 3.2);
* per-process invariants `PInv`: a scan at node `a` has a lower bound `lb` on its future second
  component (Lemma 3.3), its path is consistent with the switches at its invocation (`LeftDom`)
  and with the current switches (`RightDom`), every right step `u` of its path is *guarded*
  (`Guard`: `u.left.second` and all pending left propagations at `u` are `≤ lb`; Lemma 3.1), and
  it carries a candidate *witness* `MaxUpdate0` for its first component;
* `q` — every value of `second` at a node `c` was the value of the root's `second` at a time when
  the path to `c` was consistent with the switches;
* `fs` — every switch that is on was turned on by a `MaxUpdate0` whose descent below the switch is
  complete (`Below`), and whose path above it was consistent with the switches at its invocation;
* `comp`, `compScan`, `hist` — what is known about completed operations.
-/

set_option linter.unusedSectionVars false

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] (T : Shape)

/-- `ℓ` is the address of a leaf. -/
def IsLeaf (ℓ : List Bool) : Prop := T.IsAddr ℓ ∧ T.subD ℓ = .leaf

/-- The descent of `MaxUpdate0(v)` below node `c` (on the path to `v`) is complete: the switches
of all right steps down to some node `e` are on, and `e` is the leaf `v`, or a left step whose
switch is on (where the descent stopped). -/
def Below (C : Cfg P) (c : List Bool) (v : ℕ) : Prop :=
  ∃ e, c <+: e ∧ e <+: T.addr v ∧ (∀ u x, e = u ++ true :: x → c <+: u → sw C u = true) ∧
    (T.subD e = .leaf ∨ (sw C e = true ∧ e ++ [false] <+: T.addr v))

/-- Some leaf reachable through switches that are on has `second ≥ g`. -/
def Good1 (C : Cfg P) (g : ℕ) : Prop := ∃ ℓ, IsLeaf T ℓ ∧ RightDom ℓ (sw C) ∧ g ≤ sc C ℓ

/-- The left child of `u` and all pending left propagations at `u` are `≤ b`. -/
def Guard (C : Cfg P) (u : List Bool) (b : ℕ) : Prop :=
  sc C (u ++ [false]) ≤ b ∧ ∀ q e y, C.loc q = .s3 e u y → y ≤ b

/-- Every right step of the path `c` is guarded by `b`. -/
def RG (C : Cfg P) (c : List Bool) (b : ℕ) : Prop := ∀ u x, c = u ++ true :: x → Guard C u b

/-- Some prefix of `α` ends in a configuration satisfying `Q`. -/
def Past (α : List (Label P maxArrObj)) (Q : Cfg P → Prop) : Prop :=
  ∃ β D, β <+: α ∧ (alg P T true).run β = some D ∧ Q D

/-- `pU` invoked `o` in `α`, and the configuration before the invocation satisfies `Q`. -/
def InvBefore (α : List (Label P maxArrObj)) (pU : P) (o : MAOp)
    (Q : List (Label P maxArrObj) → Cfg P → Prop) : Prop :=
  ∃ β γ D, α = β ++ .inv pU o :: γ ∧ (alg P T true).run β = some D ∧ Q β D

/-- The current operation of `p` is `o`, invoked after the prefix `β` with `Q β (run β)`. -/
def CurInv (α : List (Label P maxArrObj)) (p : P) (o : MAOp)
    (Q : List (Label P maxArrObj) → Cfg P → Prop) : Prop :=
  ∃ β γ D, α = β ++ .inv p o :: γ ∧ (∀ ℓ ∈ γ, ℓ.proc = p → ℓ = .tau p) ∧
    (alg P T true).run β = some D ∧ Q β D

/-- Every operation completed in `β` contributes at most `r`. -/
def SeenLE (β : List (Label P maxArrObj)) (r : ℕ × ℕ) : Prop :=
  ∀ z, Completed β z → contribOf β z ≤ r

/-- Invariant of a scan (embedded if `e`) at node `a`, on the virtual path `c`, with lower bound
`b` on its second component and possibly a value `xo` read from `second`. -/
def ScanInv (α : List (Label P maxArrObj)) (C : Cfg P) (p : P) (e : Bool) (a c : List Bool)
    (b : ℕ) (node : Bool) (xo : Option ℕ) : Prop :=
  (e = false → C.pend p = some .scan ∧
      CurInv T α p .scan (fun _ D => LeftDom c (sw D) ∧ sc D [] ≤ b)) ∧
  (e = true → ∃ v, C.pend p = some (.upd1 v) ∧ v ≤ b ∧ CurInv T α p (.upd1 v) (fun _ _ => True)) ∧
  T.IsAddr a ∧ (node = true → ∃ l r, T.subD a = .node l r) ∧
  RightDom c (sw C) ∧ RG C c b ∧
  (∀ x, xo = some x → x ≤ sc C a ∧ (x = 0 ∨ Past T α (fun D => sc D [] = x ∧ LeftDom c (sw D)))) ∧
  ((∃ u x, c = u ++ true :: x) →
    ∃ pU v, InvBefore T α pU (.upd0 v) (fun _ D => LeftDom c (sw D)) ∧ Below T C c v)

/-- What is known about a completed scan with result `r`. -/
def CompScan (C : Cfg P) (r : ℕ × ℕ) : Prop :=
  r.1 < T.size ∧ RightDom (T.addr r.1) (sw C) ∧ r.2 ≤ sc C (T.addr r.1) ∧ RG C (T.addr r.1) r.2

/-- What is known about the contribution `c` of a completed operation. -/
def CompFacts (C : Cfg P) (c : ℕ × ℕ) : Prop :=
  (∀ ℓ, IsLeaf T ℓ → LeftDom ℓ (sw C) → c.1 ≤ T.lo ℓ) ∧ c.2 ≤ sc C [] ∧ Good1 T C c.2

/-- A scan that is about to return `r`. -/
def ScanDone (α : List (Label P maxArrObj)) (C : Cfg P) (p : P) (r : ℕ × ℕ) : Prop :=
  CurInv T α p .scan (fun β _ => SeenLE β r) ∧
  (0 < r.1 → ∃ pU, InvBefore T α pU (.upd0 r.1) (fun β _ => SeenLE β r)) ∧
  (0 < r.2 → ∃ pU, InvBefore T α pU (.upd1 r.2) (fun β _ => SeenLE β r)) ∧
  CompScan T C r

/-- Per-process invariant, for the local state `l` of `p`. -/
def PInvL (α : List (Label P maxArrObj)) (C : Cfg P) (p : P) : Loc → Prop
  | .idle => C.pend p = none
  | .d0 v a => C.pend p = some (.upd0 v) ∧ v < T.size ∧ a <+: T.addr v ∧
      CurInv T α p (.upd0 v) (fun _ D => LeftDom a (sw D))
  | .up v a => C.pend p = some (.upd0 v) ∧ v < T.size ∧ a <+: T.addr v ∧ Below T C a v ∧
      CurInv T α p (.upd0 v) (fun _ D => LeftDom a (sw D))
  | .w1 v => C.pend p = some (.upd1 v) ∧ CurInv T α p (.upd1 v) (fun _ _ => True)
  | .s1 e a => ScanInv T α C p e a a (sc C a) false none
  | .s2 e a x => ScanInv T α C p e a a x true (some x)
  | .s3 e a x => ScanInv T α C p e a (a ++ [false]) x true (some x)
  | .s4 e a => ScanInv T α C p e a (a ++ [true]) (sc C a) true none
  | .s5 e a x => ScanInv T α C p e a (a ++ [true]) x true (some x)
  | .rt r => (C.pend p = some .scan ∧ ScanDone T α C p r) ∨
      (∃ v, C.pend p = some (.upd1 v) ∧ r = (0, 0) ∧ Good1 T C v ∧ v ≤ sc C [] ∧
        CurInv T α p (.upd1 v) (fun _ _ => True))

/-- Per-process invariant. -/
def PInv (α : List (Label P maxArrObj)) (C : Cfg P) (p : P) : Prop := PInvL T α C p (C.loc p)

lemma pinv_iff {α : List (Label P maxArrObj)} {C : Cfg P} {p : P} {l : Loc} (h : C.loc p = l) :
    PInv T α C p ↔ PInvL T α C p l := by rw [PInv, h]

/-- The history facts about a completed scan `y` with result `r` that feed the criterion. -/
def HFacts (α : List (Label P maxArrObj)) (y : OpId P) (r : ℕ × ℕ) : Prop :=
  (∃ β γ, β ++ .inv y.1 .scan :: γ <+: α ∧ (opsOf β y.1).length = y.2 ∧ SeenLE β r) ∧
  ∃ α', α' <+: α ∧ ¬ Completed α' y ∧
    (0 < r.1 → ∃ pU, InvBefore T α' pU (.upd0 r.1) (fun β _ => SeenLE β r)) ∧
    (0 < r.2 → ∃ pU, InvBefore T α' pU (.upd1 r.2) (fun β _ => SeenLE β r))

/-- The invariant of the corrected Algorithm 2. -/
structure Inv (α : List (Label P maxArrObj)) (C : Cfg P) : Prop where
  pinv : ∀ p, PInv T α C p
  g1 : ∀ a b, sc C (a ++ [b]) ≤ sc C a
  q : ∀ c, 0 < sc C c → Past T α (fun D => sc D [] = sc C c ∧ LeftDom c (sw D))
  fs : ∀ a, sw C a = true → ∃ pU v, InvBefore T α pU (.upd0 v) (fun _ D => LeftDom a (sw D)) ∧
    Below T C (a ++ [true]) v
  w : 0 < sc C [] → ∃ pU, InvBefore T α pU (.upd1 (sc C [])) (fun _ D => sc D [] < sc C [])
  comp : ∀ y, Completed α y → CompFacts T C (contribOf α y)
  compScan : ∀ y r, opOf α y = some .scan → respOf α y = some r → CompScan T C r
  hist : ∀ y r, opOf α y = some .scan → respOf α y = some r → HFacts T α y r
  resp0 : ∀ y o r, opOf α y = some o → respOf α y = some r → o ≠ .scan → r = (0, 0)

/-- Lemma 3.2 iterated: `second` decreases along paths. -/
lemma sc_append_le {C : Cfg P} (hg : ∀ a b, sc C (a ++ [b]) ≤ sc C a) (a : List Bool) :
    ∀ c, sc C (a ++ c) ≤ sc C a := by
  intro c
  induction c using List.reverseRecOn with
  | nil => simp
  | append_singleton c b ih => rw [← List.append_assoc]; exact (hg _ b).trans ih

end Podc.LimitedUseSnapshots
