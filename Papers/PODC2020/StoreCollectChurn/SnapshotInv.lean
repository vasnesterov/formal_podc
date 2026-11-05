import Papers.PODC2020.StoreCollectChurn.SnapshotTrace

/-!
# Invariants of Algorithm 7

For an execution `E` allowed by the code (`run pk E ≠ none`) we prove, by induction on the
prefixes of `E`, an invariant of every node's local state together with facts about the events
already executed (`Past`):

* every stored value `x` of node `p` carries `x.val` = argument of `p`'s `x.usqno`-th update,
  and, if `x.usqno ≥ 1`, its `scounts` is the `ssqno`-vector of a collect `L` of `p` (Line 79,
  invoked after the invocation of `p`'s `x.usqno`-th update)
  and its `sview` is *certified* (`Cert`) by a successful double collect that starts after `L`
  returns and ends before the store (this is Lemma 12 of the paper in disguise);
* the result of every scan is certified by a successful double collect inside the scan
  (directly, or via the borrowed view, using the previous point and regularity);
* usqno's of a node's stores are non-decreasing, and bounded by its number of updates.
-/

namespace Podc.StoreCollectChurn.Snap

variable {P V : Type} [DecidableEq P]

/-! ## Counting updates -/

/-- The argument of the event if it is an invocation `UPDATE_p(v)`. -/
def updOf (p : P) : Ev P V → Option V
  | .hinv q (.update v) => if q = p then some v else none
  | _ => none

variable (E : List (Ev P V))

/-- Number of `UPDATE` invocations by `p` among the first `i` events. -/
def updCnt (i : ℕ) (p : P) : ℕ := fIdx (updOf p) E i

/-- Arguments of the updates of `p`, in order. -/
def updArgs (p : P) : List V := E.filterMap (updOf p)

/-- The value of `p`'s `k`-th update (`none` for `k = 0`). -/
def valOf (p : P) (k : ℕ) : Option V := if k = 0 then none else (updArgs E p)[k - 1]?

/-- A *certificate* for the snapshot view `W` inside the interval `(lo, hi)`: a successful double
collect (two collects, the first returning before the second is invoked, with the same `usqno`'s
of real values) invoked after `lo`, returning before `hi`, whose second view gives `W`. -/
def Cert (W : P → Option V) (lo hi : ℕ) : Prop :=
  ∃ i₁ j₁ q₁ W₁ i₂ j₂ q₂ W₂, ColE E i₁ j₁ q₁ W₁ ∧ ColE E i₂ j₂ q₂ W₂ ∧ lo < i₁ ∧ j₁ < i₂ ∧
    j₂ < hi ∧ (∀ r, rU W₁ r = rU W₂ r) ∧ W = rVal W₂

/-- No event of `p` strictly between `a` and `b`. -/
def NoEvIn (p : P) (a b : ℕ) : Prop := ∀ k, a < k → k < b → ∀ e, E[k]? = some e → e.proc ≠ p

/-- Only store-collect events of `p` strictly between `a` and `b`. -/
def NoHIn (p : P) (a b : ℕ) : Prop :=
  ∀ k, a < k → k < b → ∀ e, E[k]? = some e → e.proc = p → ∃ c, e = .sc c

/-- The invariant of a value `x` stored (or about to be stored) by `p`, at time `i`. -/
def StoredOK (i : ℕ) (p : P) (x : SCVal P V) : Prop :=
  x.val = valOf E p x.usqno ∧ (x.usqno = 0 → x.scounts = fun _ => none) ∧
    (1 ≤ x.usqno → ∃ l' l W, ColE E l' l p W ∧ l < i ∧ x.scounts = ssqVec W ∧
      Cert E x.sview l i ∧
      ∃ h v, h < l' ∧ E[h]? = some (.hinv p (.update v)) ∧ updCnt E (h + 1) p = x.usqno)

/-- The context of a pending `UPDATE(v)` of `p` invoked at `h`, whose Line 79 collect has not
returned yet (`usqno` not yet incremented). -/
def UpdCtx (i : ℕ) (p : P) (s : LState P V) (h : ℕ) (v : V) : Prop :=
  E[h]? = some (.hinv p (.update v)) ∧ updCnt E i p = s.usqno + 1 ∧ (updArgs E p)[s.usqno]? = some v

/-- Facts about a pending scan (free-standing or embedded) after its Line 71 store, at `st`. -/
def AfterStore (i : ℕ) (p : P) (s : LState P V) (st : ℕ) : Prop :=
  st < i ∧ StE E st p s.stored ∧ s.stored.ssqno = s.ssqno ∧
    ∀ a < i, ∀ y, StE E a p y → y.ssqno = s.ssqno → st ≤ a

/-- Context of a pending scan of `p`: invoked (or, if embedded, its update invoked) at `h`; if
embedded, the Line 79 collect returned at `l < lo` with `scounts = ssqVec W`. -/
def ScanCtx (i : ℕ) (p : P) (s : LState P V) (emb : Option V) (h lo : ℕ) : Prop :=
  h < i ∧ NoHIn E p h i ∧ s.stored.usqno = s.usqno ∧ h ≤ lo ∧
  match emb with
  | none => E[h]? = some (.hinv p .scan) ∧ s.usqno = updCnt E i p
  | some v => UpdCtx E i p s h v ∧
      ∃ l' l W, ColE E l' l p W ∧ h < l' ∧ l < lo ∧ s.scounts = ssqVec W

/-- The part of the invariant that depends on the program counter. -/
def PCInv (i : ℕ) (p : P) (s : LState P V) : Prop :=
  match s.pc with
  | .idle => s.usqno = updCnt E i p ∧ s.stored.usqno = s.usqno
  | .scStore emb => ∃ h, ScanCtx E i p s emb h i ∧ ∀ a < i, ∀ y, StE E a p y → y.ssqno < s.ssqno
  | .scStoreW emb => ∃ h st, ScanCtx E i p s emb h st ∧ h < st ∧ AfterStore E i p s st
  | .scCol1 emb => ∃ h st, ScanCtx E i p s emb h st ∧ h < st ∧ AfterStore E i p s st
  | .scColW emb true => ∃ h st, ScanCtx E i p s emb h st ∧ h < st ∧ AfterStore E i p s st ∧
      ∃ ic, st < ic ∧ ic < i ∧ E[ic]? = some (.sc (.colInv p)) ∧ NoEvIn E p ic i
  | .scColW emb false => ∃ h st, ScanCtx E i p s emb h st ∧ h < st ∧ AfterStore E i p s st ∧
      ∃ i₁ j₁ ic, st < i₁ ∧ ColE E i₁ j₁ p s.V1 ∧ j₁ < ic ∧ ic < i ∧
        E[ic]? = some (.sc (.colInv p)) ∧ NoEvIn E p ic i
  | .scColN emb => ∃ h st, ScanCtx E i p s emb h st ∧ h < st ∧ AfterStore E i p s st ∧
      ∃ i₁ j₁, st < i₁ ∧ ColE E i₁ j₁ p s.V1 ∧ j₁ < i
  | .scRet W => ∃ h, h < i ∧ E[h]? = some (.hinv p .scan) ∧ NoHIn E p h i ∧ Cert E W h i ∧
      s.usqno = updCnt E i p ∧ s.stored.usqno = s.usqno
  | .upCol v => ∃ h, h < i ∧ NoHIn E p h i ∧ UpdCtx E i p s h v ∧ s.stored.usqno = s.usqno
  | .upColW v => ∃ h, h < i ∧ NoHIn E p h i ∧ UpdCtx E i p s h v ∧ s.stored.usqno = s.usqno ∧
      ∃ ic, h < ic ∧ ic < i ∧ E[ic]? = some (.sc (.colInv p)) ∧ NoEvIn E p ic i
  | .upStore => ∃ h v, h < i ∧ E[h]? = some (.hinv p (.update v)) ∧ NoHIn E p h i ∧
      s.usqno = updCnt E i p ∧ s.stored.usqno + 1 = s.usqno ∧ s.val = valOf E p s.usqno ∧
      ∃ l' l W, ColE E l' l p W ∧ h < l' ∧ l < i ∧ s.scounts = ssqVec W ∧ Cert E s.sview l i
  | .upStoreW => ∃ h v a, h < a ∧ a < i ∧ E[h]? = some (.hinv p (.update v)) ∧ NoHIn E p h i ∧
      StE E a p s.stored ∧ s.stored.usqno = updCnt E i p ∧ s.usqno = s.stored.usqno ∧
      NoEvIn E p a i
  | .upRet => ∃ h v a b, h < a ∧ b < i ∧ E[h]? = some (.hinv p (.update v)) ∧ NoHIn E p h i ∧
      StE E a p s.stored ∧ NextE E a b ∧ s.stored.usqno = updCnt E i p ∧
      s.usqno = s.stored.usqno

/-- The invariant of node `p` with local state `s` after the first `i` events. -/
def NInv (i : ℕ) (p : P) (s : LState P V) : Prop :=
  (∀ a < i, ∀ x, StE E a p x → x.usqno ≤ s.stored.usqno ∧ x.ssqno ≤ s.ssqno) ∧
  s.stored.ssqno ≤ s.ssqno ∧ s.stored.usqno ≤ s.usqno ∧ StoredOK E i p s.stored ∧ PCInv E i p s

/-- What is known about a store event `x` of `p` at position `a`. -/
structure StoreFact (a : ℕ) (p : P) (x : SCVal P V) : Prop where
  ok : StoredOK E a p x
  le_cnt : x.usqno ≤ updCnt E a p
  mono : ∀ a' < a, ∀ x', StE E a' p x' → x'.usqno ≤ x.usqno

/-- What is known about a response event of `p` at position `h'`. -/
def RetFact (h' : ℕ) (p : P) (r : P → Option V) : Prop :=
  ∃ h, h < h' ∧ NoHIn E p h h' ∧
    ((E[h]? = some (.hinv p .scan) ∧ Cert E r h h') ∨
     (∃ v, E[h]? = some (.hinv p (.update v)) ∧ r = (fun _ => none) ∧
        ∃ a b x, h < a ∧ b < h' ∧ StE E a p x ∧ NextE E a b ∧ x.usqno = updCnt E h' p))

/-- Facts about the first `i` events. -/
def Past (i : ℕ) : Prop :=
  (∀ a < i, ∀ p x, StE E a p x → StoreFact E a p x) ∧
  (∀ h < i, ∀ p r, E[h]? = some (.hret p r) → RetFact E h p r)

end Podc.StoreCollectChurn.Snap
