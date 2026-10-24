import Papers.PODC2015.ABADetection.Defs
import Cslib.Computability.Distributed.SharedMemory.StrongLin
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Foundations.Data.Finset.SumUpdate

/-!
# The ABA-detecting register of Ovens–Woelfel (PODC 2019), Algorithm 2: definitions

Sean Ovens, Philipp Woelfel. *Strongly Linearizable Implementations of Snapshots and Other
Types.* PODC 2019 (arXiv:1908.10826), Section 3.

`n` processes `Fin n` share

* a register `X` (base object `none`) holding a triple `(x, p, s)`, initially `(⊥, ⊥, ⊥)`
  (here `(v₀, none)`), and
* registers `A[q]`, `q : Fin n` (base object `some q`) holding a pair `(p, s)`, initially
  `(⊥, ⊥)` (here `none`; the value component of `A[q]` is unused and stays `v₀`).

All registers have the value type `V × Option (Fin n × Seq n)` where `Seq n = Fin (2n+2)`
(sequence numbers `{0, …, 2n+1}`), i.e. `O(log n + log |V|)` bits.

* `DWrite_p(x)`: `s ← GetSeq()` (one read of `A[c]`, then local computation), `X.write(x,p,s)`.
* `GetSeq_p()` (Algorithm 1, lines 3–14): read `A[c]`; record `(c, sr)` in `na` iff the pair
  read belongs to `p`; `c ← c + 1 mod n`; choose `s ∉ na ∪ usedQ`; push `s` into the queue
  `usedQ` of the last `n + 1` chosen sequence numbers. The "arbitrary" choice is a parameter
  `pick` (any function returning a value outside a list of fewer than `2n+2` excluded values).
* `DRead_q()` (Algorithm 2): repeat { `(x,p,s) ← X.read`; `(r,sr) ← A[q].read`;
  `A[q].write(p,s)`; `(x',p',s') ← X.read`; if `(p,s) ≠ (r,sr)` or `(x,p,s) ≠ (x',p',s')` then
  `changed ← true` } until both equalities hold; return `(x', changed)`.

The implemented object is `abaObj (Fin n) V v₀` of the ABADetection formalization
(`Papers/PODC2015/ABADetection/Defs.lean`): `DRead` carries the reader (`dread q`), and only
`q` may invoke `dread q` (`allowed`).

The implementation is defined for an arbitrary sequential specification with the same
operations and responses (`implG`), so that it can also be compared with the paper's literal
specification (`FirstRead.lean`); `impl` is the instance for `abaObj`.
-/

namespace Podc.StrongLinSnapshots

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

variable (n : ℕ) (V : Type)

/-- Sequence numbers `{0, …, 2n+1}`. -/
abbrev Seq := Fin (2 * n + 2)

/-- A process identifier / sequence number pair, or `⊥` (`none`). -/
abbrev Tag := Option (Fin n × Seq n)

/-- Register contents: `X` holds `(x, (p, s))`; `A[q]` uses only the second component. -/
abbrev Val := V × Tag n

/-- Base objects: `none` is `X`, `some q` is `A[q]`. -/
abbrev Obj := Option (Fin n)

/-- All base objects are registers over `Val n V` with initial value `(v₀, ⊥)`. -/
abbrev B (v₀ : V) : Obj n → ObjSpec := fun _ => register (Val n V) (v₀, none)

/-- The persistent local state of `GetSeq`: the index `c` of the next announcement to read,
the set `na` (as a function: `na c = some s` iff `(c, s) ∈ na`), and `usedQ`, the last chosen
sequence numbers, newest first (at most `n + 1` of them; the paper's initial `⊥` entries are
omitted). -/
structure GS where
  /-- The next announcement register to read. -/
  c : Fin n
  /-- `na c = some s` iff `(c, s) ∈ na`. -/
  na : Fin n → Option (Seq n)
  /-- The last (at most `n + 1`) chosen sequence numbers, newest first. -/
  usedQ : List (Seq n)

/-- Program counters. -/
inductive PC where
  /-- No pending operation. -/
  | idle
  /-- `DWrite(x)`: about to read `A[c]` (line 3). -/
  | wA (x : V)
  /-- `DWrite(x)`: about to write `(x, p, s)` to `X` (line 2). -/
  | wX (x : V) (s : Seq n)
  /-- `DWrite(x)`: about to return. -/
  | wRet (x : V)
  /-- `DRead`: about to read `X` (line 34). -/
  | r34 (ch : Bool)
  /-- `DRead`: about to read `A[q]` (line 35), `v` read on line 34. -/
  | r35 (ch : Bool) (v : Val n V)
  /-- `DRead`: about to write `A[q]` (line 36), `a` read on line 35. -/
  | r36 (ch : Bool) (v : Val n V) (a : Tag n)
  /-- `DRead`: about to read `X` (line 37). -/
  | r37 (ch : Bool) (v : Val n V) (a : Tag n)
  /-- `DRead`: about to return `(x, ch)`. -/
  | rRet (x : V) (ch : Bool)

/-- Local states. -/
structure Loc where
  /-- Program counter. -/
  pc : PC n V
  /-- `GetSeq` state. -/
  gs : GS n

variable {n V}

/-- `c + 1 mod n`. -/
def nextIdx (c : Fin n) : Fin n := ⟨(c.val + 1) % n, Nat.mod_lt _ c.pos⟩

/-- Lines 4–9: update `na` after reading the pair `t` from `A[c]`. -/
def naUpd (p c : Fin n) (na : Fin n → Option (Seq n)) (t : Tag n) : Fin n → Option (Seq n) :=
  Function.update na c (match t with
    | some (r, sr) => if r = p then some sr else none
    | none => none)

/-- The excluded sequence numbers `{i | (j, i) ∈ na} ∪ usedQ` (as a list). -/
def excl (na : Fin n → Option (Seq n)) (usedQ : List (Seq n)) : List (Seq n) :=
  (List.finRange n).filterMap na ++ usedQ

/-- `GetSeq` after reading `t` from `A[c]` (lines 4–14): the chosen sequence number and the
new `GetSeq` state. -/
def getSeq (pick : List (Seq n) → Seq n) (p : Fin n) (g : GS n) (t : Tag n) : Seq n × GS n :=
  let na' := naUpd p g.c g.na t
  let s := pick (excl na' g.usedQ)
  (s, ⟨nextIdx g.c, na', (s :: g.usedQ).take (n + 1)⟩)

/-- A specification with the operations and responses of an ABA-detecting register. -/
abbrev abaSpec (S : Type) (s₀ : S) (δ : S → ABAOp (Fin n) V → S × (V × Bool)) : ObjSpec :=
  ⟨S, ABAOp (Fin n) V, V × Bool, s₀, δ⟩

/-- The operations a process may invoke: `DRead()` only for itself. -/
def allowedOp (p : Fin n) : ABAOp (Fin n) V → Prop
  | .dread q => q = p
  | .dwrite _ => True

instance (p : Fin n) (o : ABAOp (Fin n) V) : Decidable (allowedOp p o) := by
  cases o <;> unfold allowedOp <;> infer_instance

/-- The next action in each program counter. -/
def actG [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) (S : Type) (s₀ : S)
    (δ : S → ABAOp (Fin n) V → S × (V × Bool)) (p : Fin n) (l : Loc n V) :
    Action (abaSpec S s₀ δ) (B n V v₀) (Loc n V) :=
  match l.pc with
  | .idle => .ret (v₀, false) l
  | .wA x => .access (some l.gs.c) .read (fun r => ⟨.wX x (getSeq pick p l.gs r.2).1,
      (getSeq pick p l.gs r.2).2⟩)
  | .wX x s => .access none (.write (x, some (p, s))) (fun _ => ⟨.wRet x, l.gs⟩)
  | .wRet x => .ret (x, true) ⟨.idle, l.gs⟩
  | .r34 ch => .access none .read (fun v => ⟨.r35 ch v, l.gs⟩)
  | .r35 ch v => .access (some p) .read (fun a => ⟨.r36 ch v a.2, l.gs⟩)
  | .r36 ch v a => .access (some p) (.write (v₀, v.2)) (fun _ => ⟨.r37 ch v a, l.gs⟩)
  | .r37 ch v a => .access none .read (fun v' =>
      if a = v.2 ∧ v = v' then ⟨.rRet v'.1 ch, l.gs⟩ else ⟨.r34 true, l.gs⟩)
  | .rRet x ch => .ret (x, ch) ⟨.idle, l.gs⟩

/-- Algorithm 2 (with `GetSeq`/`DWrite` of Algorithm 1) as an implementation of any object with
the operations and responses of an ABA-detecting register. -/
def implG [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) (S : Type) (s₀ : S)
    (δ : S → ABAOp (Fin n) V → S × (V × Bool)) :
    Impl (abaSpec S s₀ δ) (B n V v₀) (Fin n) (Loc n V) where
  memInit _ := (v₀, none)
  locInit p := ⟨.idle, ⟨⟨0, p.pos⟩, fun _ => none, []⟩⟩
  invoke _ l o := match o with
    | .dwrite x => ⟨.wA x, l.gs⟩
    | .dread _ => ⟨.r34 false, l.gs⟩
  act := actG v₀ pick S s₀ δ
  allowed := allowedOp

/-- **Algorithm 2**: the strongly linearizable ABA-detecting register. -/
abbrev impl [DecidableEq V] (v₀ : V) (pick : List (Seq n) → Seq n) :
    Impl (abaObj (Fin n) V v₀) (B n V v₀) (Fin n) (Loc n V) :=
  implG v₀ pick (abaObj (Fin n) V v₀).State (abaObj (Fin n) V v₀).init (abaObj (Fin n) V v₀).δ

/-- The specification of `pick`: it avoids every value of a list of fewer than `2n + 2`
excluded values (such a value exists). -/
def PickSpec (pick : List (Seq n) → Seq n) : Prop :=
  ∀ E : List (Seq n), E.length < 2 * n + 2 → pick E ∉ E

/-- A concrete `pick`: the smallest non-excluded value. -/
def pickMin (E : List (Seq n)) : Seq n :=
  ((List.finRange (2 * n + 2)).find? (fun s => s ∉ E)).getD 0

lemma pickMin_spec : PickSpec (pickMin (n := n)) := by
  intro E hE
  have : ∃ s : Seq n, s ∉ E := by
    by_contra h
    push Not at h
    have hsub : (List.finRange (2 * n + 2)).toFinset ⊆ E.toFinset := fun s _ => by simp [h s]
    have := Finset.card_le_card hsub
    rw [List.toFinset_finRange, Finset.card_univ, Fintype.card_fin] at this
    exact absurd (this.trans (List.toFinset_card_le E)) (by omega)
  obtain ⟨s, hs⟩ := this
  have hfind : ((List.finRange (2 * n + 2)).find? (fun s => s ∉ E)).isSome := by
    rw [List.find?_isSome]
    exact ⟨s, List.mem_finRange s, by simpa using hs⟩
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hfind
  have := List.find?_some ht
  simp only [pickMin, ht, Option.getD_some]
  simpa using this

end Podc.StrongLinSnapshots
