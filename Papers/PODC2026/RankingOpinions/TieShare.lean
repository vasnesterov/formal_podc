import Papers.PODC2026.RankingOpinions.Circles
import Cslib.Computability.Distributed.PopulationProtocols.Schedules
import Cslib.Computability.Distributed.PopulationProtocols.Eventually
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring

/-!
# Sharing ties (Section 4.2): `Circles_TieSharing`

Breitkopf, Dallot, El-Hayek, Schmid, PODC 2026, Section 4.2 and Appendix 8.4 (Theorem 4.2).

On top of the braket part of Circles (rule (1): ket exchange; Circles' own `out` rule (2) is
dropped), every agent stores an output color `out` and a `status ∈ {winner_spreader, winner,
loser}` (initially `winner`). After the ket exchange, the status rules (1)–(7) and the output
rules (i), (ii) of the paper are applied *in this order*, each rule in both orientations
`(a, b)` then `(b, a)`; all brakets are the ones after the ket exchange.

Interpretation choices (the paper is informal on these points):
* modulo range: `[x, y]_k = {x, x+1, …, x + ((y - x) mod k)}` (so `[i, i]_k = {i}`), i.e.
  `z ∈ [x, y]_k ↔ (z - x) mod k ≤ (y - x) mod k` (`inRng`);
* `[x, y]_k ⊆ [x', y']_k` is set inclusion plus the paper's extra condition `x ≠ y' ∨ y ≠ x'`
  (`RSub`); `⊊` is `⊆` together with "the two sets differ" (`RSSub`);
* the conditions of the rules read the *current* statuses, already updated by the previous rules
  of the same interaction (`pre = false`, the "sequential reading"). With `pre = true` all
  conditions of rules (4)–(7) and (ii) read the statuses *before* the interaction; for this reading
  Theorem 4.2 is false (`tieShare_pre_counterexample`);
* output map: an agent at `winner_spreader`/`winner` outputs its own color (its bra), a `loser`
  outputs its `out` variable (`tsOut`).

Number of states: `k² · k · 3 = 3k³` (`card_TSState`).
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions

open Finset Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

variable {k : ℕ}

/-- The status of an agent. -/
inductive St
  | ws   -- winner_spreader (holds a token)
  | win  -- winner
  | los  -- loser
  deriving DecidableEq, Repr

instance : Fintype St := ⟨{St.ws, St.win, St.los}, by intro x; cases x <;> simp⟩

lemma card_St : Fintype.card St = 3 := rfl

/-- Clockwise distance `(y - x) mod k` from `x` to `y`. -/
def dst (x y : Fin k) : ℕ := if x.val ≤ y.val then y.val - x.val else y.val + k - x.val

/-- `z ∈ [e.1, e.2]_k`. -/
def inRng (e : Braket k) (z : Fin k) : Prop := dst e.1 z ≤ dst e.1 e.2

instance (e : Braket k) (z : Fin k) : Decidable (inRng e z) := by unfold inRng; infer_instance

/-- `[e.1, e.2]_k ⊆ [f.1, f.2]_k` in the sense of the paper (set inclusion and
`e.1 ≠ f.2 ∨ e.2 ≠ f.1`). -/
def RSub (e f : Braket k) : Prop := (∀ z, inRng e z → inRng f z) ∧ (e.1 ≠ f.2 ∨ e.2 ≠ f.1)

/-- `[e.1, e.2]_k ⊊ [f.1, f.2]_k`. -/
def RSSub (e f : Braket k) : Prop := RSub e f ∧ ¬ ∀ z, inRng e z ↔ inRng f z

instance (e f : Braket k) : Decidable (RSub e f) := by unfold RSub; infer_instance
instance (e f : Braket k) : Decidable (RSSub e f) := by unfold RSSub; infer_instance

/-- Is a braket diagonal? -/
def dg (e : Braket k) : Bool := decide (e.1 = e.2)

/-- The facts about two interacting agents `a`, `b` the rules depend on. -/
structure PR where
  /-- the agents exchanged kets -/
  ex : Bool
  /-- `a`, `b` diagonal before the exchange -/
  pa : Bool
  pb : Bool
  /-- `a`, `b` diagonal after the exchange -/
  da : Bool
  db : Bool
  /-- same bra -/
  sb : Bool
  /-- ket of `a` = bra of `b`, and vice versa -/
  kab : Bool
  kba : Bool
  /-- `[a] ⊆ [b]`, `[b] ⊆ [a]` -/
  sab : Bool
  sba : Bool
  /-- `[a] ⊊ [b]`, `[b] ⊊ [a]` -/
  qab : Bool
  qba : Bool

/-- Exchange the roles of the two agents. -/
def PR.swap (r : PR) : PR :=
  ⟨r.ex, r.pb, r.pa, r.db, r.da, r.sb, r.kba, r.kab, r.sba, r.sab, r.qba, r.qab⟩

/-- The status read by a condition: the current one (`pre = false`) or the one before the
interaction (`pre = true`). -/
def rd (pre : Bool) (cur old : St) : St := if pre then old else cur

/-- Rules (1) token generation, (2) token destructor, (3) token destruction. -/
def st123 (r : PR) (sa sb : St) : St × St :=
  let a1 := if r.ex && !r.da then St.ws else sa
  let b1 := if r.ex && !r.db then St.ws else sb
  let a2 := if !r.pa && r.da then St.win else a1
  let b2 := if !r.pb && r.db then St.win else b1
  let b3 := if r.da then (if r.sb then St.win else if !r.db then St.los else b2) else b2
  let a3 := if r.db then (if r.sb then St.win else if !r.da then St.los else a2) else a2
  (a3, b3)

/-- Rule (4), token multiplication, `a` acting on `b` (`oa`, `ob`: statuses before the
interaction; `a`, `b`: current statuses). -/
def r4 (pre : Bool) (r : PR) (oa ob a b : St) : St × St :=
  if rd pre a oa = St.ws ∧ rd pre b ob = St.los ∧ r.kab = true then (a, St.ws) else (a, b)

/-- Rule (5), token ascent. -/
def r5 (pre : Bool) (r : PR) (oa _ob a b : St) : St × St :=
  if rd pre a oa = St.ws ∧ r.qab = true then (if r.sb then St.win else St.los, St.ws) else (a, b)

/-- Rule (6), token simplification. -/
def r6 (pre : Bool) (r : PR) (oa ob a b : St) : St × St :=
  if rd pre a oa = St.ws ∧ rd pre b ob = St.ws ∧ r.sab = true then
    (if r.sb then St.win else St.los, b) else (a, b)

/-- Rule (7), information spreading. -/
def r7 (pre : Bool) (r : PR) (oa _ob a b : St) : St × St :=
  if rd pre a oa = St.ws then
    (if r.sb then (a, St.win) else if r.qba then (a, St.los) else (a, b))
  else (a, b)

/-- Apply a rule in the orientation `(a, b)`, then in the orientation `(b, a)`. -/
def both (f : PR → St → St → St → St → St × St) (r : PR) (oa ob : St) (p : St × St) :
    St × St :=
  let q := f r oa ob p.1 p.2
  let q' := f r.swap ob oa q.2 q.1
  (q'.2, q'.1)

/-- All status rules, in order. -/
def stUpd (pre : Bool) (r : PR) (sa sb : St) : St × St :=
  both (r7 pre) r sa sb (both (r6 pre) r sa sb (both (r5 pre) r sa sb
    (both (r4 pre) r sa sb (st123 r sa sb))))

/-- The new `out` of agent `a`, given its partner's new and old status, its partner's bra and its
old `out`: rule (i), then rule (ii). -/
def outUpd (pre : Bool) (r : PR) (sbNew sbOld : St) (braB oa : Fin k) : Fin k :=
  let o1 := if r.db && !r.da then braB else oa
  if rd pre sbNew sbOld = St.ws ∧ r.sab = true then braB else o1

/-- The facts about two agents with brakets `p`, `q` before and `e`, `f` after the exchange. -/
def mkPR (p q e f : Braket k) : PR :=
  ⟨decide (Profitable p q), dg p, dg q, dg e, dg f, decide (e.1 = f.1), decide (e.2 = f.1),
    decide (f.2 = e.1), decide (RSub e f), decide (RSub f e), decide (RSSub e f),
    decide (RSSub f e)⟩

/-- States of `Circles_TieSharing`: braket, `out`, status. -/
abbrev TSState (k : ℕ) := Braket k × Fin k × St

/-- `Circles_TieSharing` has `3k³` states. -/
theorem card_TSState : Fintype.card (TSState k) = 3 * k ^ 3 := by
  simp only [Fintype.card_prod, Fintype.card_fin, card_St]; ring

/-- The transition function. -/
def tsδ (pre : Bool) (p q : TSState k) : TSState k × TSState k :=
  let e := (exch p.1 q.1).1
  let f := (exch p.1 q.1).2
  let r := mkPR p.1 q.1 e f
  let s := stUpd pre r p.2.2 q.2.2
  ((e, outUpd pre r s.2 q.2.2 f.1 p.2.1, s.1), (f, outUpd pre r.swap s.1 p.2.2 e.1 q.2.1, s.2))

/-- The protocol `Circles_TieSharing` (`pre = false`: the sequential reading). -/
def tieShare (k : ℕ) (pre : Bool) : Protocol (TSState k) := ⟨tsδ pre⟩

/-- Output: a winner (or winner spreader) outputs its own color, a loser its `out`. -/
def tsOut (s : TSState k) : Fin k := if s.2.2 = St.los then s.2.1 else s.1.1

/-- Initial configuration: `⟨i|i⟩`, `out = i`, `winner`. -/
def tsInit {A : Type*} (input : A → Fin k) : Config A (TSState k) :=
  fun a => ((input a, input a), input a, St.win)

/-- Projection onto the braket part. -/
def tsToCore (pre : Bool) : (tieShare k pre).Hom (circlesCore k) where
  f s := s.1
  map_fst _ _ := rfl
  map_snd _ _ := rfl

/-- The facts used in a configuration whose brakets do not change. -/
def relOf (e f : Braket k) : PR := mkPR e f e f

variable {A : Type*} [DecidableEq A]

/-- One interaction, in general. -/
lemma ts_interact (pre : Bool) (C : Config A (TSState k)) {a b : A} (hab : a ≠ b) :
    let r := mkPR (C a).1 (C b).1 (exch (C a).1 (C b).1).1 (exch (C a).1 (C b).1).2
    let s := stUpd pre r (C a).2.2 (C b).2.2
    (tieShare k pre).interact C a b a =
      ((exch (C a).1 (C b).1).1, outUpd pre r s.2 (C b).2.2 (exch (C a).1 (C b).1).2.1 (C a).2.1,
        s.1) ∧
    (tieShare k pre).interact C a b b =
      ((exch (C a).1 (C b).1).2, outUpd pre r.swap s.1 (C a).2.2 (exch (C a).1 (C b).1).1.1
        (C b).2.1, s.2) := by
  refine ⟨?_, ?_⟩
  · simp only [Protocol.interact_self_left, tieShare, tsδ]
  · simp only [Protocol.interact_self_right _ _ hab, tieShare, tsδ]

/-- One interaction in a configuration whose brakets `B` are stable: brakets do not change, and
statuses and outputs are updated using `relOf (B a) (B b)`. -/
lemma ts_interact_stable (pre : Bool) {B : Config A (Braket k)} (hB : Stable B)
    {C : Config A (TSState k)} (hC : ∀ y, (C y).1 = B y) {a b : A} (hab : a ≠ b) :
    let r := relOf (B a) (B b)
    let s := stUpd pre r (C a).2.2 (C b).2.2
    (tieShare k pre).interact C a b a = (B a, outUpd pre r s.2 (C b).2.2 (B b).1 (C a).2.1, s.1) ∧
    (tieShare k pre).interact C a b b =
      (B b, outUpd pre r.swap s.1 (C a).2.2 (B a).1 (C b).2.1, s.2) ∧
    ∀ y, y ≠ a → y ≠ b → (tieShare k pre).interact C a b y = C y := by
  have hex : exch (C a).1 (C b).1 = (B a, B b) := by
    rw [exch, ite_eq_right_iff.2 (fun h => absurd h (by rw [hC, hC]; exact hB a b hab)), hC, hC]
  obtain ⟨h1, h2⟩ := ts_interact pre C hab
  refine ⟨?_, ?_, fun y hya hyb => Protocol.interact_other _ _ hya hyb⟩
  · rw [h1, hex]; simp only [hC, relOf]
  · rw [h2, hex]; simp only [hC, relOf]

/-! ## The "pre-interaction statuses" reading fails -/

section Counterexample

/-- Input: agents `0, 1, 2` with colors `0, 0, 1` (`k = 2`); `0` is the unique majority color. -/
def tsCexInput : Fin 3 → Fin 2 := ![0, 0, 1]

lemma tsCex_majority : IsMajority tsCexInput 0 := by unfold IsMajority inputCount; decide

def allPairs3 : List (Fin 3 × Fin 3) := [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]

/-- The schedule `(0,2), (0,1), (1,2)`, then round robin over all ordered pairs. -/
def tsCexSched (t : ℕ) : Fin 3 × Fin 3 :=
  if t = 0 then (0, 2) else if t = 1 then (0, 1) else if t = 2 then (1, 2)
  else allPairs3[(t - 3) % 6]'(Nat.mod_lt _ (by decide))

lemma tsCexSched_ne (t : ℕ) : (tsCexSched t).1 ≠ (tsCexSched t).2 := by
  unfold tsCexSched
  split_ifs
  · decide
  · decide
  · decide
  · have : ∀ i : Fin 6, (allPairs3[i.val]).1 ≠ (allPairs3[i.val]).2 := by decide
    exact this ⟨_, Nat.mod_lt _ (by decide)⟩

/-- The brakets after the prefix: `⟨0|1⟩, ⟨0|0⟩, ⟨1|0⟩` (stable). -/
def tsCexBrakets : Config (Fin 3) (Braket 2) := ![(0, 1), (0, 0), (1, 0)]

lemma tsCex_stable : Stable tsCexBrakets := by unfold Stable; decide

lemma tsCex_reach :
    (∀ y, ((tieShare 2 true).runSched (tsInit tsCexInput) tsCexSched 3 y).1 = tsCexBrakets y) ∧
    (∀ y, ((tieShare 2 true).runSched (tsInit tsCexInput) tsCexSched 3 y).2.2 ≠ St.ws) ∧
    ((tieShare 2 true).runSched (tsInit tsCexInput) tsCexSched 3 1).2.2 = St.los := by
  decide

lemma tsCex_upd : ∀ a b : Fin 3, a ≠ b → ∀ sa sb : St, sa ≠ St.ws → sb ≠ St.ws →
    (stUpd true (relOf (tsCexBrakets a) (tsCexBrakets b)) sa sb).1 ≠ St.ws ∧
    (stUpd true (relOf (tsCexBrakets a) (tsCexBrakets b)) sa sb).2 ≠ St.ws ∧
    (a = 1 → sa = St.los → (stUpd true (relOf (tsCexBrakets a) (tsCexBrakets b)) sa sb).1 = St.los) ∧
    (b = 1 → sb = St.los → (stUpd true (relOf (tsCexBrakets a) (tsCexBrakets b)) sa sb).2 = St.los) := by
  decide

/-- With brakets `⟨0|1⟩, ⟨0|0⟩, ⟨1|0⟩`, no winner spreader and agent `1` at `loser`, nothing
can change the status of agent `1` in the pre-interaction reading. -/
lemma tsCex_closed : (tieShare 2 true).Closed fun C : Config (Fin 3) (TSState 2) =>
    (∀ y, (C y).1 = tsCexBrakets y) ∧ (∀ y, (C y).2.2 ≠ St.ws) ∧ (C 1).2.2 = St.los := by
  rintro C C' ⟨h1, h2, h3⟩ ⟨a, b, hab, rfl⟩
  obtain ⟨ha, hb, ho⟩ := ts_interact_stable true tsCex_stable h1 hab
  have hu := tsCex_upd a b hab _ _ (h2 a) (h2 b)
  refine ⟨fun y => ?_, fun y => ?_, ?_⟩
  · by_cases hya : y = a
    · subst hya; rw [ha]
    · by_cases hyb : y = b
      · subst hyb; rw [hb]
      · rw [ho y hya hyb, h1]
  · by_cases hya : y = a
    · subst hya; rw [ha]; exact hu.1
    · by_cases hyb : y = b
      · subst hyb; rw [hb]; exact hu.2.1
      · rw [ho y hya hyb]; exact h2 y
  · obtain rfl | hya := eq_or_ne a 1
    · rw [ha]; exact hu.2.2.1 rfl h3
    · obtain rfl | hyb := eq_or_ne b 1
      · rw [hb]; exact hu.2.2.2 rfl h3
      · rw [ho 1 (Ne.symm hya) (Ne.symm hyb)]; exact h3

/-- **Counterexample for the pre-interaction reading of Circles_TieSharing.** If the conditions
of rules (4)–(7) and (ii) read the statuses *before* the interaction, Theorem 4.2 fails: with
3 agents of colors `0, 0, 1` (`k = 2`, unique majority color `0`) there is a weakly fair
execution in which agent `1` (color `0`, braket `⟨0|0⟩`) is a `loser` at every time `t ≥ 3`.
(At time 2 the interaction `(1,2)` makes agent `2` a loser by rule (3), but rule (7) still fires
with its stale `winner_spreader` status and makes agent `1` a loser; no winner spreader remains.) -/
theorem tieShare_pre_counterexample :
    ∃ E : (tieShare 2 true).Execution (Fin 3), E.config 0 = tsInit tsCexInput ∧ E.WeaklyFair ∧
      IsMajority tsCexInput 0 ∧ tsCexInput 1 = 0 ∧ ∀ t ≥ 3, (E.config t 1).2.2 = St.los := by
  set E := Execution.ofSched (tieShare 2 true) (tsInit tsCexInput) tsCexSched tsCexSched_ne
  refine ⟨E, rfl, ?_, tsCex_majority, rfl, fun t ht => (tsCex_closed.execution E tsCex_reach t ht).2.2⟩
  apply Execution.weaklyFair_of_cycle _ allPairs3 (by decide) 3
  · intro t
    show tsCexSched (3 + t) = _
    simp only [tsCexSched]
    split_ifs <;> first | omega | (congr 2; omega)
  · decide

end Counterexample

end RankingOpinions
