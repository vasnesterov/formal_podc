import Papers.PODC2019.RMESubLogBoth.Model

/-!
# Lemma 9 (the 39-condition invariant of Figures 8–14) is false as stated

Lemma 9 claims that the conjunction of Conditions 1–39 holds in every configuration of every run.
Already crash-free runs with `k = 2` ports violate Conditions 4 and 5 (Figure 8):

* Condition 5, conjunct `qnode.CS_Signal = 0 ⇒ qnode.Pred ∈ {NIL, &Crash, &InCS}`: after line 14
  the node of a waiting process points to its predecessor while its `CS_Signal` is still `0`
  (`cond5_csSignal_false`).
* Condition 5, conjunct `qnode.NonNil_Signal = 0 ⇒ qnode.Pred = NIL`: between lines 14 and 15
  `Pred` is already set while `NonNil_Signal` is still `0` (`cond5_nonNil_false`).
* Condition 4, third conjunct `∃ b ∈ [1, k], node_π.Pred⋯Pred (b times) ∈ {NIL, &Crash, &InCS,
  &Exit}`: with `k = 2`, the second process in the queue is three `Pred` hops away from `&Exit`
  (its node → the first node → `SpecialNode` → `&Exit`) (`cond4_false`).

(Condition 18 also uses the real program counter `PC_π'` where `\hat{PC}_π'` is meant; read
literally it fails in the initial configuration, where every `PC_π = 10`.)
-/

namespace Podc.RMESubLogBoth.PaperInv

open Podc.RMESubLogBoth

/-- `qnode.Pred` with the paper's convention that the distinguished nodes `&Crash`, `&InCS`,
`&Exit` point to themselves (`NIL` stays `NIL`). -/
def predPV (c : Cfg k) : PV → PV
  | .node a => c.pred a
  | v => v

/-- `v.Pred⋯Pred` (`b` times). -/
def predIter (c : Cfg k) (b : ℕ) (v : PV) : PV := (predPV c)^[b] v

/-- `v ∈ {NIL, &Crash, &InCS, &Exit}`. -/
def PV.isSentinel : PV → Prop
  | .node _ => False
  | _ => True

/-- Process `0` executes lines 10–14 (crash-free) in a 2-port system. -/
def c1 : Cfg 2 := Cfg.init.setPc 0 .l11
def c2 : Cfg 2 := { c1 with node := Function.update c1.node 0 (some c1.nxt), nxt := c1.nxt + 1,
                            pc := Function.update c1.pc 0 (.l13 c1.nxt) }
def c3 : Cfg 2 := { c2 with tail := 1, pc := Function.update c2.pc 0 (.l14 1 c2.tail) }
def c4 : Cfg 2 := { c3 with pred := Function.update c3.pred 1 (.node 0),
                            pc := Function.update c3.pc 0 (.l15 1 0) }

lemma reach_c4 : Reach c4 := by
  have h1 : Reach c1 := .next (.step 0) .init (Step.l10_nil _ 0 (by simp [Cfg.init]) rfl)
  have h2 : Reach c2 := .next (.step 0) h1 (Step.l11 _ 0 (by simp [c1, Cfg.setPc]))
  have h3 : Reach c3 := .next (.step 0) h2 (Step.l13 _ 0 1 (by simp [c2, c1, Cfg.setPc, Cfg.init]))
  exact .next (.step 0) h3 (Step.l14 _ 0 1 0 (by simp [c3, c2, c1, Cfg.setPc, Cfg.init]))

/-- Lemma 9, Condition 5 (`CS_Signal = 0 ⇒ Pred ∈ {NIL, &Crash, &InCS}`) fails: in a reachable
configuration of a crash-free run with `k = 2`, node `1` (created at line 11) has
`CS_Signal = 0` and `Pred = &SpecialNode`. -/
theorem cond5_csSignal_false :
    ∃ c : Cfg 2, Reach c ∧ ∃ a, a < c.nxt ∧ a ≠ special ∧ c.csig a = false ∧
      c.pred a ∉ ({.nil, .crash, .incs} : Set PV) := by
  refine ⟨c4, reach_c4, 1, by decide, by decide, by decide, ?_⟩
  simp [c4, c3, c2, c1, Cfg.setPc, Cfg.init]

/-- Lemma 9, Condition 5 (`NonNil_Signal = 0 ⇒ Pred = NIL`) fails in the same configuration
(between lines 14 and 15). -/
theorem cond5_nonNil_false :
    ∃ c : Cfg 2, Reach c ∧ ∃ a, a < c.nxt ∧ a ≠ special ∧ c.nn a = false ∧ c.pred a ≠ .nil := by
  refine ⟨c4, reach_c4, 1, by decide, by decide, by decide, ?_⟩
  simp [c4, c3, c2, c1, Cfg.setPc, Cfg.init]

/-! Process `1` now joins the queue behind node `1` (lines 10–14). -/
def d1 : Cfg 2 := c4.setPc 1 .l11
def d2 : Cfg 2 := { d1 with node := Function.update d1.node 1 (some d1.nxt), nxt := d1.nxt + 1,
                            pc := Function.update d1.pc 1 (.l13 d1.nxt) }
def d3 : Cfg 2 := { d2 with tail := 2, pc := Function.update d2.pc 1 (.l14 2 d2.tail) }
def d4 : Cfg 2 := { d3 with pred := Function.update d3.pred 2 (.node 1),
                            pc := Function.update d3.pc 1 (.l15 2 1) }

lemma reach_d4 : Reach d4 := by
  have h1 : Reach d1 := .next (.step 1) reach_c4 (Step.l10_nil _ 1
    (by simp [c4, c3, c2, c1, Cfg.setPc, Cfg.init]) (by simp [c4, c3, c2, c1, Cfg.setPc, Cfg.init]))
  have h2 : Reach d2 := .next (.step 1) h1 (Step.l11 _ 1 (by simp [d1, Cfg.setPc]))
  have h3 : Reach d3 := .next (.step 1) h2
    (Step.l13 _ 1 2 (by simp [d2, d1, c4, c3, c2, c1, Cfg.setPc, Cfg.init]))
  exact .next (.step 1) h3 (Step.l14 _ 1 2 1 (by simp [d3, d2, d1, c4, c3, Cfg.setPc]))

/-- Lemma 9, Condition 4 (third conjunct) fails: with `k = 2`, process `1` is at line 15 with
`node_1 = Node[1] = 2`, and `node_1.Pred⋯Pred` (`b` times) is a node for `b = 1, 2`, so no
`b ∈ [1, k]` reaches `{NIL, &Crash, &InCS, &Exit}`. -/
theorem cond4_false :
    ∃ c : Cfg 2, Reach c ∧ c.pc 1 = .l15 2 1 ∧ c.node 1 = some 2 ∧
      ¬ ∃ b, 1 ≤ b ∧ b ≤ 2 ∧ PV.isSentinel (predIter c b (.node 2)) := by
  refine ⟨d4, reach_d4, by simp [d4, d3, d2, d1, Cfg.setPc], by
    simp [d4, d3, d2, d1, c4, c3, c2, c1, Cfg.setPc, Cfg.init], ?_⟩
  rintro ⟨b, hb1, hb2, hs⟩
  interval_cases b <;>
    simp [predIter, predPV, PV.isSentinel, d4, d3, d2, d1, c4, c3, c2, c1, Cfg.setPc,
      Cfg.init] at hs

end Podc.RMESubLogBoth.PaperInv
