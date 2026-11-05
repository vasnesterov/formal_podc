import Papers.PODC2013.RotorRouterRing.Ring

/-!
# Lemma 2.4 (agent domains on the ring): a counterexample to the first property

Klasing, Kosowski, Pająk, Sauerwald, PODC 2013, Lemma 2.4 ("stated without proof"):
*Consider a deployment in which no two agents ever meet at a node, and let `v_i(t) ∈ V_i(t)` be
the location of the `i`-th agent. Then `V_i(t)` induces a sub-path of the ring, …*, where `V_i(t)`
is the set of nodes whose last visitor up to round `t` is agent `i`.

Domains need agent identities, so we use the labelled version of the model (`lstep`): agent `i`
at node `v` leaves along the arc at cyclic position `ptr v + r`, where `r` is the number of
active agents with smaller index on `v` (the paper releases the agents of a node one by one), and
the pointer of `v` advances by the number of released agents. Stopped agents stay put.

Two agents may **swap along an edge** in one round without ever being on the same node; then the
domains interleave. On the 6-ring with agents on `0` and `3` and pointers `0 → 1`, `1 → 2`,
`2 → 1`, `3 → 2`, after two rounds agent `0` is on `2` and agent `1` is on `1`, so
`V_0(2) = {0, 2}` and `V_1(2) = {1, 3}`. Stopping both agents from then on gives a delayed
deployment in which no two agents ever share a node (`lemma_2_4_false`).

The property holds if "meeting" also covers crossing an edge in opposite directions, or if a swap
is re-read as two bounces (the agents are indistinguishable); the paper does not say so.
-/

open Finset

namespace Podc.RotorRouterRing

variable {n k : ℕ} [NeZero n]

/-- Configuration of the labelled model: agent positions and port pointers. -/
structure LConfig (n k : ℕ) where
  /-- Position of each agent. -/
  pos : Fin k → ZMod n
  /-- Port pointer of each node. -/
  ptr : ZMod n → ℕ

/-- One round of the labelled model; `act i` says whether agent `i` moves in this round. -/
def lstep (c : LConfig n k) (act : Fin k → Bool) : LConfig n k where
  pos i := if act i then
      (ring n).target (c.pos i)
        (c.ptr (c.pos i) + (univ.filter (fun j => j < i ∧ act j = true ∧ c.pos j = c.pos i)).card)
    else c.pos i
  ptr v := c.ptr v + (univ.filter (fun j => act j = true ∧ c.pos j = v)).card

/-- Execution: `act t` are the agents moving in round `t ≥ 1`. -/
def lrun (c₀ : LConfig n k) (act : ℕ → Fin k → Bool) : ℕ → LConfig n k
  | 0 => c₀
  | t + 1 => lstep (lrun c₀ act t) (act (t + 1))

/-- The last agent visiting `x` up to round `t` (the paper's domains `V_i(t)`); a node counts as
visited at time `s` by the agents located on it at the start of round `s + 1`. -/
def lastVisitor (c₀ : LConfig n k) (act : ℕ → Fin k → Bool) (t : ℕ) (x : ZMod n) :
    Option (Fin k) :=
  (List.range (t + 1)).reverse.findSome?
    (fun s => (List.finRange k).find? (fun i => (lrun c₀ act s).pos i = x))

/-- The domain `V_i(t)`. -/
def domain (c₀ : LConfig n k) (act : ℕ → Fin k → Bool) (t : ℕ) (i : Fin k) : Finset (ZMod n) :=
  univ.filter (fun x => lastVisitor c₀ act t x = some i)

/-- `S` induces a sub-path of the ring: it is a set of consecutive nodes `a, a+1, …, a+l-1`. -/
def IsArc (S : Finset (ZMod n)) : Prop :=
  ∃ a : ZMod n, ∃ l ≤ n, S = (range l).image (fun j : ℕ => a + (j : ZMod n))

/-- The counterexample configuration on the 6-ring. -/
def cx : LConfig 6 2 := ⟨![0, 3], ![0, 0, 1, 1, 0, 0]⟩

/-- Rounds 1 and 2 are undelayed; afterwards both agents are stopped. -/
def cxAct : ℕ → Fin 2 → Bool := fun t _ => decide (t ≤ 2)

lemma cx_run_stable (t : ℕ) : lrun cx cxAct (t + 2) = lrun cx cxAct 2 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show lstep (lrun cx cxAct (t + 2)) (cxAct (t + 3)) = _
    rw [ih]
    have : cxAct (t + 3) = fun _ => false := by
      funext i; simp [cxAct]
    rw [this]
    simp only [lstep, Bool.false_eq_true, false_and, and_false, if_false]
    simp

lemma cx_domain : domain cx cxAct 2 0 = {0, 2} := by decide

lemma not_isArc_02 : ¬ IsArc ({0, 2} : Finset (ZMod 6)) := by
  rintro ⟨a, l, hl, h⟩
  interval_cases l <;> revert a <;> decide

/-- **Lemma 2.4 is false as stated** (first property): in a delayed deployment on the 6-ring with
two agents that never share a node, the domain of agent `0` after two rounds is `{0, 2}`, which
does not induce a sub-path of the ring. -/
theorem lemma_2_4_false :
    (∀ t, Function.Injective (lrun cx cxAct t).pos) ∧ ¬ IsArc (domain cx cxAct 2 0) := by
  refine ⟨fun t => ?_, by rw [cx_domain]; exact not_isArc_02⟩
  rcases t with _ | _ | t
  · decide
  · decide
  · rw [cx_run_stable]; decide

end Podc.RotorRouterRing
