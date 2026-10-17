import Papers.PODC2020.SSLERegular.Model
import Mathlib.Tactic.DeriveFintype

/-!
# Protocol SS-Tree (Section 4) and a counterexample to Theorem 4.3

Chen–Chen, *Self-Stabilizing Leader Election in Regular Graphs*, PODC 2020, Section 4
(Protocols 2, 4, 5, 6).

We transcribe SS-Tree (with its sub-protocols SS-TwoHop, CycleDetector and MultipleRootDetector)
as a nondeterministic population protocol `ssTree k R` for `k`-regular graphs, parameterised by an
arbitrary ring protocol `R` (the paper uses the Ring-Protocol of [11] as a black box; nothing below
depends on it). Colours `1, …, k²` are encoded as `Fin (k ^ 2)` (value `c + 1`); the colour
variables with an extra value `0` (`counterColor`, `loopColor`) are `Fin (k ^ 2 + 1)`.
Randomized rules are resolved by an explicit `TChoice` (all choices are allowed).

Interpretation choices (see `differencies.md`): the SS-TwoHop guard is read as
`u.prevColor = v.color ∧ v.prevColor = u.color ∧ u.colorBit ≠ v.colorBit` (the printed tuple
equality is garbled); the cycle-detector leader test and the opposite-coin test of
MultipleRootDetector are applied to every interacting pair (outside the parent–child guard), the
reading most favourable to error detection; unqualified `errFlag ← True` means `u.errFlag`.

**Main result** (`ssTree_not_solvesSSLE`): for every `k ≥ 2`, every graph of maximum degree `≤ k`
with at least two nodes and every colouring in which the neighbours of each node have distinct
colours (what SS-TwoHop is meant to produce), there is a configuration in which **every node is a
root (a leader) forever**: all nodes are roots whose `parentColor` is the colour of no neighbour,
so no parent–child pair exists, MultipleRootDetector never moves a coin, CycleDetector never runs
the ring protocol, and no error is ever raised. Hence SS-Tree does not solve SSLE
(Theorem 4.3 and Lemma 4.2 are false), e.g. on the complete graphs `K_{k+1}`
(`ssTree_fails_on_complete`).
-/

open Finset

namespace SSLERegular

/-- Coin values `−2, −1, 0, 1, 2` of MultipleRootDetector. -/
inductive Coin | m2 | m1 | z | p1 | p2
  deriving DecidableEq

instance : Fintype Coin := ⟨{.m2, .m1, .z, .p1, .p2}, by intro x; cases x <;> simp⟩

namespace Coin

/-- Integer value. -/
def val : Coin → ℤ
  | m2 => -2 | m1 => -1 | z => 0 | p1 => 1 | p2 => 2

/-- `2 · c` for `|c| = 1`. -/
def dbl : Coin → Coin
  | m1 => m2 | p1 => p2 | c => c

/-- A random coin. -/
def ofBool : Bool → Coin
  | true => p1 | false => m1

end Coin

/-- A ring protocol: a nondeterministic protocol on states `RS` with leader output `lead`. -/
structure RingProtocol (RS : Type*) extends GProtocol RS where
  /-- Leader output. -/
  lead : RS → Bool

variable {RS : Type*}

/-- The state of a node in SS-Tree (Protocols 2, 4, 5, 6). -/
structure TState (k : ℕ) (RS : Type*) where
  color : Fin (k ^ 2)
  parentColor : Fin (k ^ 2)
  prevColor : Fin (k ^ 2)
  colorBit : Bool
  counterColor : Fin (k ^ 2 + 1)
  counter : Fin (k + 1)
  errFlag : Bool
  root : Bool
  ringState : RS
  ringStateCopy : RS
  loopMarker : Bool
  loopChild : Bool
  loopParent : Bool
  loopColor : Fin (k ^ 2 + 1)
  loopCounter : Fin (k + 1)
  coin : Coin

/-- Colour `c ∈ {1,…,k²}` as a value of a colour variable with an extra `0`. -/
def colSucc {k : ℕ} (c : Fin (k ^ 2)) : Fin (k ^ 2 + 1) := ⟨c.val + 1, by omega⟩

/-- Saturating increment of a counter in `{0,…,k}`. -/
def incr {k : ℕ} (c : Fin (k + 1)) : Fin (k + 1) := ⟨min (c.val + 1) k, by omega⟩

/-- The random choices of one interaction. -/
structure TChoice (k : ℕ) (RS : Type*) where
  /-- SS-TwoHop: new colours of `v` and `u` (used only on a detected conflict) and the shared bit. -/
  rc1 : Fin (k ^ 2)
  rc2 : Fin (k ^ 2)
  rb : Bool
  /-- "Randomly: `u.counter ← 0, u.counterColor ← 0`". -/
  resetCounter : Bool
  /-- CycleDetector: "Randomly do: `u.loopCounter ← 0, u.loopColor ← 0`". -/
  resetLoop : Bool
  /-- CycleDetector: "Randomly do: `u.loopMarker ← False`". -/
  unmark : Bool
  /-- Outcome selection of the ring protocol. -/
  ρ : RS → RS → RS × RS
  /-- MultipleRootDetector: the tossed coin and "Randomly do" of the walk back. -/
  toss : Bool
  back : Bool
  /-- Detect-error-and-random-change: `RandomState`, `RandomBit1`, `RandomBit2`. -/
  rand : TState k RS
  b1 : Bool
  b2 : Bool

variable {k : ℕ}

/-- Protocol 2, SS-TwoHop. -/
def twoHop (rc1 rc2 : Fin (k ^ 2)) (rb : Bool) (u v : TState k RS) : TState k RS × TState k RS :=
  let w : TState k RS × TState k RS :=
    if u.prevColor = v.color ∧ v.prevColor = u.color ∧ u.colorBit ≠ v.colorBit then
      ({ u with color := rc2 }, { v with color := rc1 }) else (u, v)
  ({ w.1 with prevColor := w.2.color, colorBit := rb },
    { w.2 with prevColor := w.1.color, colorBit := rb })

/-! The stages of Protocol 4 (ghost-parent check), applied to the initiator `u`. -/

/-- "Randomly: `u.counter ← 0, u.counterColor ← 0`". -/
def ctrReset (r : Bool) (u : TState k RS) : TState k RS :=
  if r then { u with counter := 0, counterColor := 0 } else u

/-- Count the next neighbour colour (non-roots only). -/
def ctrInc (u v : TState k RS) : TState k RS :=
  if u.counterColor.val < v.color.val + 1 ∧ u.root = false then
    { u with counterColor := colSucc v.color, counter := incr u.counter } else u

/-- Reset the counter when meeting the parent. -/
def ctrParent (u v : TState k RS) : TState k RS :=
  if v.color = u.parentColor then { u with counter := 0 } else u

/-- Ghost parent detected. -/
def ctrErr (u : TState k RS) : TState k RS :=
  if u.counter.val = k then { u with errFlag := true } else u

/-! The stages of Protocol 5, CycleDetector. -/

/-- "Randomly do: `u.loopCounter ← 0, u.loopColor ← 0`". -/
def cdReset (r : Bool) (u : TState k RS) : TState k RS :=
  if r then { u with loopCounter := 0, loopColor := 0 } else u

/-- Count the next neighbour colour. -/
def cdInc (u v : TState k RS) : TState k RS :=
  if u.loopColor.val < v.color.val + 1 then
    { u with loopColor := colSucc v.color, loopCounter := incr u.loopCounter } else u

/-- Reset the loop counter when meeting a marked neighbour. -/
def cdMarked (u v : TState k RS) : TState k RS :=
  if v.loopMarker = true then { u with loopCounter := 0 } else u

/-- Mark a starting node of a path. -/
def cdStart (u : TState k RS) : TState k RS :=
  if u.loopCounter.val = k then
    { u with loopMarker := true, loopChild := false, ringStateCopy := u.ringState, loopParent := false }
  else u

/-- "Randomly do: `u.loopMarker ← False`". -/
def cdUnmark (r : Bool) (u : TState k RS) : TState k RS :=
  if r then { u with loopMarker := false } else u

/-- Run the ring protocol on a marked parent–child pair. -/
def cdRing (ρ : RS → RS → RS × RS) (u v : TState k RS) : TState k RS × TState k RS :=
  if u.loopMarker = true ∧ v.loopMarker = true ∧ u.loopChild = true ∧ v.loopParent = true then
    ({ u with ringStateCopy := (ρ u.ringStateCopy v.ringStateCopy).1 },
      { v with ringStateCopy := (ρ u.ringStateCopy v.ringStateCopy).2 }) else (u, v)

/-- Extend a path. -/
def cdExtend (w : TState k RS × TState k RS) : TState k RS × TState k RS :=
  if w.1.loopMarker = false ∧ w.2.loopMarker = true ∧ w.2.loopParent = false then
    ({ w.1 with loopChild := true, ringStateCopy := w.1.ringState, loopMarker := true },
      { w.2 with loopParent := true }) else w

/-- Two paths form a single path or a path forms a cycle. -/
def cdJoin (w : TState k RS × TState k RS) : TState k RS × TState k RS :=
  if w.1.loopMarker = true ∧ w.2.loopMarker = true ∧ w.1.loopChild = false ∧
      w.2.loopParent = false then
    ({ w.1 with loopChild := true }, { w.2 with loopParent := true }) else w

/-- The parent–child part of CycleDetector (`u` is the parent of `v`). -/
def cdParent (ρ : RS → RS → RS × RS) (u v : TState k RS) : TState k RS × TState k RS :=
  if u.color = v.parentColor then cdJoin (cdExtend (cdRing ρ u v)) else (u, v)

/-- A ring leader in the copy means a cycle was detected. -/
def cdErr (R : RingProtocol RS) (u : TState k RS) : TState k RS :=
  if R.lead u.ringStateCopy = true then { u with errFlag := true } else u

/-- Protocol 5, CycleDetector (`R.lead` is the output of the ring protocol). -/
def cycleDetector (R : RingProtocol RS) (ch : TChoice k RS) (u v : TState k RS) :
    TState k RS × TState k RS :=
  let u1 := cdUnmark ch.unmark (cdStart (cdMarked (cdInc (cdReset ch.resetLoop u) v) v))
  let w := cdParent ch.ρ u1 v
  (cdErr R w.1, w.2)

/-- The parent–child part of Protocol 6 (`u` is the parent of `v`). -/
def mrdParent (toss back : Bool) (u v : TState k RS) : TState k RS × TState k RS :=
  let u := if u.root = true ∧ u.coin = .z then { u with coin := Coin.ofBool toss } else u
  let w : TState k RS × TState k RS :=
    if (u.coin = .p1 ∨ u.coin = .m1) ∧ v.coin = .z then
      ({ u with coin := u.coin.dbl }, { v with coin := u.coin }) else (u, v)
  if (w.1.coin = .p2 ∨ w.1.coin = .m2) ∧ w.1.coin.val = 2 * w.2.coin.val ∧ back = true then
    ({ w.1 with coin := w.2.coin }, { w.2 with coin := .z }) else w

/-- Protocol 6, MultipleRootDetector. -/
def multipleRootDetector (ch : TChoice k RS) (u v : TState k RS) : TState k RS × TState k RS :=
  let w : TState k RS × TState k RS :=
    if u.color = v.parentColor then mrdParent ch.toss ch.back u v else (u, v)
  (if w.1.coin.val * w.2.coin.val < 0 then { w.1 with errFlag := true } else w.1, w.2)

/-- Detect-error-and-random-change. -/
def randChange (ch : TChoice k RS) (w : TState k RS × TState k RS) : TState k RS × TState k RS :=
  if w.1.errFlag = true then ({ ch.rand with errFlag := ch.b1 }, { w.2 with errFlag := ch.b2 })
  else w

/-- Protocol 4, SS-Tree: one interaction with initiator `u` and responder `v`, given the random
choices `ch`. -/
def treeStep (R : RingProtocol RS) (ch : TChoice k RS) (u v : TState k RS) :
    TState k RS × TState k RS :=
  let w := twoHop ch.rc1 ch.rc2 ch.rb u v
  let u1 := ctrErr (ctrParent (ctrInc (ctrReset ch.resetCounter w.1) w.2) w.2)
  let w2 := cycleDetector R ch u1 w.2
  randChange ch (multipleRootDetector ch w2.1 w2.2)

/-- A choice is admissible if the ring-protocol selection picks allowed outcomes. -/
def TChoice.Valid (R : RingProtocol RS) (ch : TChoice k RS) : Prop :=
  ∀ a b, ch.ρ a b ∈ R.δ a b

/-- **SS-Tree** as a nondeterministic population protocol. -/
def ssTree (k : ℕ) (R : RingProtocol RS) : GProtocol (TState k RS) where
  δ p q := {o | ∃ ch : TChoice k RS, ch.Valid R ∧ o = treeStep R ch p q}

/-- Output: a node is a leader iff it is a root. -/
def TState.isLeader (s : TState k RS) : Bool := s.root

/-! ### The counterexample -/

section Counterexample

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (R : RingProtocol RS)

/-- The invariant: all nodes are roots with ghost parents, coin `+1`, counter `0`, no error, no
ring leader in `ringState`/`ringStateCopy`, colours fixed to `c`, and matched pairs of SS-TwoHop
have equal bits. -/
def BadInv (c g : V → Fin (k ^ 2)) (C : V → TState k RS) : Prop :=
  (∀ v, (C v).color = c v ∧ (C v).parentColor = g v ∧ (C v).root = true ∧
    (C v).errFlag = false ∧ (C v).counter = 0 ∧ (C v).coin = .p1 ∧
    R.lead (C v).ringState = false ∧ R.lead (C v).ringStateCopy = false) ∧
  (∀ u v, G.Adj u v → (C u).prevColor = c v → (C v).prevColor = c u →
    (C u).colorBit = (C v).colorBit)

variable {G R}

/-- The node-local part of `BadInv`. -/
def NG (R : RingProtocol RS) (c g : Fin (k ^ 2)) (s : TState k RS) : Prop :=
  s.color = c ∧ s.parentColor = g ∧ s.root = true ∧ s.errFlag = false ∧ s.counter = 0 ∧
    s.coin = .p1 ∧ R.lead s.ringState = false ∧ R.lead s.ringStateCopy = false

/-- `NG` holds and the SS-TwoHop memory is unchanged. -/
def NGF (R : RingProtocol RS) (c g : Fin (k ^ 2)) (u s : TState k RS) : Prop :=
  NG R c g s ∧ s.prevColor = u.prevColor ∧ s.colorBit = u.colorBit

lemma NGF.trans {c g : Fin (k ^ 2)} {u s t : TState k RS} (h1 : NGF R c g u s) (h2 : NGF R c g s t) :
    NGF R c g u t :=
  ⟨h2.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

lemma NGF.refl {c g : Fin (k ^ 2)} {u : TState k RS} (h : NG R c g u) : NGF R c g u u :=
  ⟨h, rfl, rfl⟩

section Stages

variable {c g : Fin (k ^ 2)} {u v : TState k RS} (h : NG R c g u)
include h

lemma ng_ctrReset (r : Bool) : NGF R c g u (ctrReset r u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold ctrReset; split_ifs <;> simp_all [NGF, NG]

lemma ng_ctrInc : NGF R c g u (ctrInc u v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold ctrInc; split_ifs <;> simp_all [NGF, NG]

lemma ng_ctrParent : NGF R c g u (ctrParent u v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold ctrParent; split_ifs <;> simp_all [NGF, NG]

lemma ng_ctrErr (hk : 1 ≤ k) : NGF R c g u (ctrErr u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold ctrErr; split_ifs with hc
  · rw [h5] at hc; simp at hc; omega
  · exact NGF.refl ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

lemma ng_cdReset (r : Bool) : NGF R c g u (cdReset r u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold cdReset; split_ifs <;> simp_all [NGF, NG]

lemma ng_cdInc : NGF R c g u (cdInc u v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold cdInc; split_ifs <;> simp_all [NGF, NG]

lemma ng_cdMarked : NGF R c g u (cdMarked u v) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold cdMarked; split_ifs <;> simp_all [NGF, NG]

lemma ng_cdStart : NGF R c g u (cdStart u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold cdStart; split_ifs <;> simp_all [NGF, NG]

lemma ng_cdUnmark (r : Bool) : NGF R c g u (cdUnmark r u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold cdUnmark; split_ifs <;> simp_all [NGF, NG]

lemma ng_cdErr : NGF R c g u (cdErr R u) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold cdErr; split_ifs <;> simp_all [NGF, NG]

end Stages

lemma twoHop_noConflict (rc1 rc2 : Fin (k ^ 2)) (rb : Bool) {u v : TState k RS}
    (h : ¬ (u.prevColor = v.color ∧ v.prevColor = u.color ∧ u.colorBit ≠ v.colorBit)) :
    twoHop rc1 rc2 rb u v = ({ u with prevColor := v.color, colorBit := rb },
      { v with prevColor := u.color, colorBit := rb }) := by
  simp only [twoHop, if_neg h]

/-- One interaction of two invariant nodes with ghost parents keeps them invariant. -/
lemma treeStep_good (hk : 1 ≤ k) (ch : TChoice k RS) {p q : TState k RS}
    {cp cq gp gq : Fin (k ^ 2)} (hp : NG R cp gp p) (hq : NG R cq gq q)
    (hgq : cp ≠ gq)
    (hbit : p.prevColor = cq → q.prevColor = cp → p.colorBit = q.colorBit) :
    NG R cp gp (treeStep R ch p q).1 ∧ NG R cq gq (treeStep R ch p q).2 ∧
      (treeStep R ch p q).1.prevColor = cq ∧ (treeStep R ch p q).2.prevColor = cp ∧
      (treeStep R ch p q).1.colorBit = (treeStep R ch p q).2.colorBit := by
  have hnc : ¬ (p.prevColor = q.color ∧ q.prevColor = p.color ∧ p.colorBit ≠ q.colorBit) := by
    rintro ⟨h1, h2, h3⟩
    exact h3 (hbit (hq.1 ▸ h1) (hp.1 ▸ h2))
  -- after SS-TwoHop
  set p1 : TState k RS := { p with prevColor := q.color, colorBit := ch.rb } with hp1
  set q1 : TState k RS := { q with prevColor := p.color, colorBit := ch.rb } with hq1
  have hp1g : NG R cp gp p1 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hp; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hq1g : NG R cq gq q1 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hq; exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hq1c : q1.color = cq := hq.1
  -- ghost-parent stages
  set p2 := ctrErr (ctrParent (ctrInc (ctrReset ch.resetCounter p1) q1) q1) with hp2
  have hp2g : NGF R cp gp p1 p2 := by
    have a1 := ng_ctrReset hp1g ch.resetCounter
    have a2 := ng_ctrInc (v := q1) a1.1
    have a3 := ng_ctrParent (v := q1) a2.1
    have a4 := ng_ctrErr a3.1 hk
    exact a1.trans (a2.trans (a3.trans a4))
  -- cycle detector
  set p3 := cdUnmark ch.unmark (cdStart (cdMarked (cdInc (cdReset ch.resetLoop p2) q1) q1))
    with hp3
  have hp3g : NGF R cp gp p2 p3 := by
    have a1 := ng_cdReset hp2g.1 ch.resetLoop
    have a2 := ng_cdInc (v := q1) a1.1
    have a3 := ng_cdMarked (v := q1) a2.1
    have a4 := ng_cdStart a3.1
    have a5 := ng_cdUnmark a4.1 ch.unmark
    exact a1.trans (a2.trans (a3.trans (a4.trans a5)))
  have hguard : ¬ p3.color = q1.parentColor := by
    rw [hp3g.1.1, hq1g.2.1]; exact hgq
  have hcd : cycleDetector R ch p2 q1 = (cdErr R p3, q1) := by
    unfold cycleDetector cdParent
    dsimp only
    rw [← hp3, if_neg hguard]
  have hp4g : NGF R cp gp p3 (cdErr R p3) := ng_cdErr hp3g.1
  have hguard' : ¬ (cdErr R p3).color = q1.parentColor := by
    rw [hp4g.1.1, hq1g.2.1]; exact hgq
  have hmrd : multipleRootDetector ch (cdErr R p3) q1 = (cdErr R p3, q1) := by
    simp only [multipleRootDetector, if_neg hguard', hp4g.1.2.2.2.2.2.1, hq1g.2.2.2.2.2.1,
      Coin.val]
    norm_num
  have hfin : treeStep R ch p q = (cdErr R p3, q1) := by
    simp only [treeStep, twoHop_noConflict _ _ _ hnc]
    rw [← hp1, ← hq1, ← hp2, hcd, hmrd]
    simp only [randChange, hp4g.1.2.2.2.1]
    simp
  have hall := hp2g.trans (hp3g.trans hp4g)
  rw [hfin]
  refine ⟨hall.1, hq1g, ?_, ?_, ?_⟩
  · rw [hall.2.1]; exact hq.1
  · exact hp.1
  · rw [hall.2.2]

lemma badInv_closed (hk : 1 ≤ k) {c g : V → Fin (k ^ 2)}
    (hinj : ∀ x u v, G.Adj x u → G.Adj x v → c u = c v → u = v)
    (hghost : ∀ u v, G.Adj u v → c u ≠ g v) :
    TS.IsClosed ((ssTree k R).Step G) (BadInv G R c g) := by
  rintro C D ⟨hng, hbit⟩ ⟨u, v, huv, o, ⟨ch, -, rfl⟩, rfl⟩
  have hne : u ≠ v := G.ne_of_adj huv
  obtain ⟨h1, h2, h3, h4, h5⟩ := treeStep_good (R := R) hk ch (hng u) (hng v) (hghost u v huv)
    (hbit u v huv)
  have hD : ∀ x, NG R (c x) (g x) (upd C u v (treeStep R ch (C u) (C v)) x) := by
    intro x
    by_cases hxv : x = v
    · subst hxv; simpa using h2
    · by_cases hxu : x = u
      · subst hxu; rw [upd_left _ hne]; exact h1
      · rw [upd_other _ hxu hxv]; exact hng x
  refine ⟨hD, ?_⟩
  intro x y hxy hx hy
  set D := upd C u v (treeStep R ch (C u) (C v))
  have hDu : D u = (treeStep R ch (C u) (C v)).1 := upd_left _ hne _
  have hDv : D v = (treeStep R ch (C u) (C v)).2 := upd_right _ _ _ _
  have hDo : ∀ z, z ≠ u → z ≠ v → D z = C z := fun z hzu hzv => upd_other _ hzu hzv _
  by_cases hxu : x = u
  · subst hxu
    by_cases hyv : y = v
    · subst hyv; rw [hDu, hDv]; exact h5
    · exfalso; rw [hDu, h3] at hx; exact hyv (hinj x v y huv hxy hx).symm
  by_cases hxv : x = v
  · subst hxv
    by_cases hyu : y = u
    · subst hyu; rw [hDu, hDv]; exact h5.symm
    · exfalso; rw [hDv, h4] at hx; exact hyu (hinj x u y huv.symm hxy hx).symm
  by_cases hyu : y = u
  · subst hyu; exfalso; rw [hDu, h3] at hy; exact hxv (hinj y v x huv hxy.symm hy).symm
  by_cases hyv : y = v
  · subst hyv; exfalso; rw [hDv, h4] at hy
    exact hxu (hinj y u x huv.symm hxy.symm hy).symm
  rw [hDo x hxu hxv, hDo y hyu hyv] at *
  exact hbit x y hxy hx hy

lemma exists_ghost [Fintype V] [DecidableRel G.Adj] (hk : 2 ≤ k) (hdeg : ∀ v, G.degree v ≤ k)
    (c : V → Fin (k ^ 2)) : ∃ g : V → Fin (k ^ 2), ∀ u v, G.Adj u v → c u ≠ g v := by
  have : ∀ v, ∃ x : Fin (k ^ 2), x ∉ (G.neighborFinset v).image c := by
    intro v
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset (Fin (k ^ 2))) ⊆ (G.neighborFinset v).image c :=
      fun x _ => h x
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_image_le (s := G.neighborFinset v) (f := c)
    rw [Finset.card_univ, Fintype.card_fin, SimpleGraph.card_neighborFinset_eq_degree] at *
    have := hdeg v
    have : k < k ^ 2 := by nlinarith
    omega
  choose g hg using this
  refine ⟨g, fun u v huv h => hg v ?_⟩
  rw [← h]
  exact Finset.mem_image.2 ⟨u, (G.mem_neighborFinset v u).2 huv.symm, rfl⟩

/-- The bad configuration: every node is a root with a ghost parent. -/
def badConfig (c g : V → Fin (k ^ 2)) (r0 : RS) (v : V) : TState k RS where
  color := c v
  parentColor := g v
  prevColor := c v
  colorBit := false
  counterColor := 0
  counter := 0
  errFlag := false
  root := true
  ringState := r0
  ringStateCopy := r0
  loopMarker := false
  loopChild := false
  loopParent := false
  loopColor := 0
  loopCounter := 0
  coin := .p1

/-- **Every node stays a leader forever.** For `k ≥ 2`, any graph of maximum degree `≤ k`, any
colouring in which the neighbours of every node have distinct colours (the output SS-TwoHop is
designed to produce), and any ring protocol with a non-leader state, there is a configuration of
SS-Tree from which every reachable configuration has *all* nodes as roots (leaders). -/
theorem ssTree_all_roots_forever [Fintype V] [DecidableRel G.Adj] (hk : 2 ≤ k)
    (hdeg : ∀ v, G.degree v ≤ k) (c : V → Fin (k ^ 2))
    (hinj : ∀ x u v, G.Adj x u → G.Adj x v → c u = c v → u = v) {r0 : RS} (hr0 : R.lead r0 = false) :
    ∃ C0 : V → TState k RS, ∀ D, (ssTree k R).Reachable G C0 D → ∀ v, (D v).isLeader = true := by
  obtain ⟨g, hg⟩ := exists_ghost (G := G) hk hdeg c
  refine ⟨badConfig c g r0, fun D hD v => ?_⟩
  have h0 : BadInv G R c g (badConfig c g r0) :=
    ⟨fun v => ⟨rfl, rfl, rfl, rfl, rfl, rfl, hr0, hr0⟩, fun _ _ _ _ _ => rfl⟩
  exact ((badInv_closed (by omega) hinj hg).reach h0 hD).1 v |>.2.2.1

lemma TState.finite [Finite RS] : Finite (TState k RS) := by
  refine Finite.of_injective (fun s : TState k RS => (s.color, s.parentColor, s.prevColor,
    s.colorBit, s.counterColor, s.counter, s.errFlag, s.root, s.ringState, s.ringStateCopy,
    s.loopMarker, s.loopChild, s.loopParent, s.loopColor, s.loopCounter, s.coin)) ?_
  intro a b h
  cases a; cases b
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  rfl

lemma ssTree_nonempty (hR : ∀ a b, (R.δ a b).Nonempty) (p q : TState k RS) :
    ((ssTree k R).δ p q).Nonempty := by
  choose ρ hρ using hR
  exact ⟨_, ⟨⟨p.color, p.color, false, false, false, false, ρ, false, false, p, false, false⟩, hρ, rfl⟩⟩

/-- **Theorem 4.3 is false.** For every `k ≥ 2`, every graph with at least two nodes and maximum
degree `≤ k` (e.g. any `k`-regular graph), and every colouring with distinct colours on each
neighbourhood, SS-Tree does not solve SSLE: there is a globally fair execution in which every node
is a leader at all times. This holds for every finite ring protocol with a non-leader state, in
particular for the Ring-Protocol of [11]. -/
theorem ssTree_not_solvesSSLE [Fintype V] [DecidableRel G.Adj] [Finite RS] (hk : 2 ≤ k)
    (hV : 2 ≤ Fintype.card V) (hedge : ∃ u v, G.Adj u v)
    (hdeg : ∀ v, G.degree v ≤ k) (c : V → Fin (k ^ 2))
    (hinj : ∀ x u v, G.Adj x u → G.Adj x v → c u = c v → u = v)
    (hR : ∀ a b, (R.δ a b).Nonempty) {r0 : RS} (hr0 : R.lead r0 = false) :
    ¬ (ssTree k R).SolvesSSLE G TState.isLeader ∧
    ∃ C0, ∃ E : TS.Run ((ssTree k R).Step G), E.st 0 = C0 ∧ E.GloballyFair ∧
      ∀ t, GProtocol.numLeaders TState.isLeader (E.st t) = Fintype.card V := by
  have := TState.finite (k := k) (RS := RS)
  obtain ⟨C0, hC0⟩ := ssTree_all_roots_forever (G := G) (R := R) hk hdeg c hinj hr0
  have hall : ∀ D, (ssTree k R).Reachable G C0 D →
      GProtocol.numLeaders TState.isLeader D = Fintype.card V := by
    intro D hD
    unfold GProtocol.numLeaders
    rw [Finset.filter_true_of_mem (fun v _ => hC0 D hD v), Finset.card_univ]
  have hnot : ∀ D, (ssTree k R).Reachable G C0 D → ¬ (ssTree k R).ValidStable G TState.isLeader D :=
    fun D hD h => by have := h.2; rw [hall D hD] at this; omega
  obtain ⟨E, hE0, hE, -⟩ := GProtocol.not_solvesSSLE_of hedge (ssTree_nonempty hR) C0 hnot
  refine ⟨fun hsol => ?_, C0, E, hE0, hE, fun t => hall _ (hE0 ▸ E.reach_of_le (Nat.zero_le t))⟩
  obtain ⟨T, hT⟩ := hsol E hE
  exact hnot _ (hE0 ▸ E.reach_of_le (Nat.zero_le T)) hT

end Counterexample

/-- **Concrete instance.** For every `k ≥ 2`, SS-Tree fails on the complete graph `K_{k+1}`, which
is connected and `k`-regular, with the Ring-Protocol replaced by any finite ring protocol with a
non-leader state. -/
theorem ssTree_fails_on_complete {RS : Type*} [Finite RS] (R : RingProtocol RS) {k : ℕ}
    (hk : 2 ≤ k) (hR : ∀ a b, (R.δ a b).Nonempty) {r0 : RS} (hr0 : R.lead r0 = false) :
    (⊤ : SimpleGraph (Fin (k + 1))).IsRegularOfDegree k ∧
    ¬ (ssTree k R).SolvesSSLE (⊤ : SimpleGraph (Fin (k + 1))) TState.isLeader := by
  have hreg : (⊤ : SimpleGraph (Fin (k + 1))).IsRegularOfDegree k := by
    intro v; rw [SimpleGraph.complete_graph_degree]; simp
  have hle : k + 1 ≤ k ^ 2 := by nlinarith
  refine ⟨hreg, (ssTree_not_solvesSSLE (G := ⊤) (R := R) hk (by simp; omega) ⟨0, 1, by simp; omega⟩
    (fun v => (hreg v).le) (Fin.castLE hle) ?_ hR hr0).1⟩
  intro x u v _ _ h
  exact Fin.castLE_injective hle h

end SSLERegular
