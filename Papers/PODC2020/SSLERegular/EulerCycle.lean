import Papers.PODC2020.SSLERegular.SSTree

/-!
# Protocol SS-EulerCycle (Section 3): definitions

Chen–Chen, *Self-Stabilizing Leader Election in Regular Graphs*, PODC 2020, Section 3
(Protocols 1, 2, 3).

SS-EulerCycle for `2k`-regular graphs, parameterised by an arbitrary ring protocol `R`
(`RingProtocol`, the Ring-Protocol of [11] in the paper). Each node has `k` virtual nodes
`node i = (ringState, predecessorColor, successorColor, token, bit)`, a colour, the SS-TwoHop
memory `(prevColor, colorBit)` and `errFlag`. Colours `1, …, 4k²` are `Fin (4 * k ^ 2)`.

`eulerStep bidir R ch u v` is one interaction (initiator `u`, responder `v`) with random choices
`ch`:

* `bidir = false` is the protocol **as printed**: the virtual edge must go from `u` to `v`
  (`u.node[i].successorColor = v.color ∧ v.node[j].predecessorColor = u.color`), otherwise
  `u.errFlag ← True`;
* `bidir = true` is our **repair**: if there is no virtual edge `u → v` but there is one `v → u`,
  the Ring-Protocol and SS-Token are run on it with `v`'s virtual node as the ring initiator.

The node output is "leader iff some virtual node's `ringState` is a ring leader" (`EState.out`).
-/

open Finset

namespace SSLERegular

variable {RS : Type*}

/-- A virtual node. -/
structure VNode (k : ℕ) (RS : Type*) where
  ringState : RS
  pred : Fin (4 * k ^ 2)
  succ : Fin (4 * k ^ 2)
  token : Bool
  bit : Bool

/-- The state of a node of SS-EulerCycle on a `2k`-regular graph. -/
structure EState (k : ℕ) (RS : Type*) where
  node : Fin k → VNode k RS
  color : Fin (4 * k ^ 2)
  prevColor : Fin (4 * k ^ 2)
  colorBit : Bool
  errFlag : Bool

variable {k : ℕ}

/-- `u.node[i] → v.node[j]` is a virtual edge as seen by the coherence check of Protocol 1. -/
def FMatch (u v : EState k RS) (i j : Fin k) : Prop :=
  (u.node i).succ = v.color ∧ (v.node j).pred = u.color

instance (u v : EState k RS) (i j : Fin k) : Decidable (FMatch u v i j) := by
  unfold FMatch; infer_instance

/-- The random choices of one interaction. -/
structure EChoice (k : ℕ) (RS : Type*) where
  /-- SS-TwoHop: new colours of `v` and `u` (used only on a detected conflict) and the shared bit. -/
  rc1 : Fin (4 * k ^ 2)
  rc2 : Fin (4 * k ^ 2)
  rb : Bool
  /-- "Find `i, j`": a selection of a matching pair of virtual nodes. -/
  pick : EState k RS → EState k RS → Fin k × Fin k
  /-- Outcome selection of the ring protocol. -/
  ρ : RS → RS → RS × RS
  /-- Detect-error-and-random-change: `RandState`, `RandBit1`, `RandBit2`. -/
  rand : EState k RS
  b1 : Bool
  b2 : Bool

/-- Admissible choices: `pick` picks a match whenever one exists; `ρ` picks ring outcomes. -/
def EChoice.Valid (R : RingProtocol RS) (ch : EChoice k RS) : Prop :=
  (∀ a b, ch.ρ a b ∈ R.δ a b) ∧
  ∀ u v : EState k RS, (∃ i j, FMatch u v i j) → FMatch u v (ch.pick u v).1 (ch.pick u v).2

/-- Protocol 2, SS-TwoHop. -/
def twoHopE (rc1 rc2 : Fin (4 * k ^ 2)) (rb : Bool) (u v : EState k RS) :
    EState k RS × EState k RS :=
  let w : EState k RS × EState k RS :=
    if u.prevColor = v.color ∧ v.prevColor = u.color ∧ u.colorBit ≠ v.colorBit then
      ({ u with color := rc2 }, { v with color := rc1 }) else (u, v)
  ({ w.1 with prevColor := w.2.color, colorBit := rb },
    { w.2 with prevColor := w.1.color, colorBit := rb })

/-- Protocol 3, SS-Token, on a virtual edge `a → b` (`lead` is the ring protocol's output). -/
def ssToken (lead : RS → Bool) (a b : VNode k RS) : VNode k RS × VNode k RS :=
  let w : VNode k RS × VNode k RS :=
    if lead b.ringState = false ∧ b.bit ≠ a.bit then
      ({ a with token := false }, { b with token := true, bit := a.bit }) else (a, b)
  if lead w.2.ringState = true ∧ w.1.bit = w.2.bit then
    ({ w.1 with token := false }, { w.2 with token := true, bit := !w.2.bit }) else w

/-- Ring-Protocol step followed by SS-Token on the virtual edge `a → b`. -/
def vEdge (R : RingProtocol RS) (ρ : RS → RS → RS × RS) (a b : VNode k RS) :
    VNode k RS × VNode k RS :=
  ssToken R.lead { a with ringState := (ρ a.ringState b.ringState).1 }
    { b with ringState := (ρ a.ringState b.ringState).2 }

/-- Apply `vEdge` to the virtual edge `x.node i → y.node j`. -/
def runEdge (R : RingProtocol RS) (ρ : RS → RS → RS × RS) (x y : EState k RS) (i j : Fin k) :
    EState k RS × EState k RS :=
  ({ x with node := Function.update x.node i (vEdge R ρ (x.node i) (y.node j)).1 },
    { y with node := Function.update y.node j (vEdge R ρ (x.node i) (y.node j)).2 })

/-- The coherence check and the ring/token step of Protocol 1 (`bidir` selects our repair). -/
def ringPart (bidir : Bool) (R : RingProtocol RS) (ch : EChoice k RS) (u v : EState k RS) :
    EState k RS × EState k RS :=
  if ∃ i j, FMatch u v i j then runEdge R ch.ρ u v (ch.pick u v).1 (ch.pick u v).2
  else if bidir = true ∧ ∃ i j, FMatch v u i j then
    (runEdge R ch.ρ v u (ch.pick v u).1 (ch.pick v u).2).swap
  else ({ u with errFlag := true }, v)

/-- "Detect multiple leaders": tokens on both interacting nodes. -/
def tokenDetect (w : EState k RS × EState k RS) : EState k RS × EState k RS :=
  if ∃ p q, (w.2.node p).token = true ∧ (w.1.node q).token = true then
    ({ w.1 with errFlag := true }, w.2) else w

/-- Detect-error-and-random-change. -/
def randChangeE (ch : EChoice k RS) (w : EState k RS × EState k RS) : EState k RS × EState k RS :=
  if w.1.errFlag = true then ({ ch.rand with errFlag := ch.b1 }, { w.2 with errFlag := ch.b2 })
  else w

/-- Protocol 1, SS-EulerCycle: one interaction. -/
def eulerStep (bidir : Bool) (R : RingProtocol RS) (ch : EChoice k RS) (u v : EState k RS) :
    EState k RS × EState k RS :=
  let w := twoHopE ch.rc1 ch.rc2 ch.rb u v
  randChangeE ch (tokenDetect (ringPart bidir R ch w.1 w.2))

/-- **SS-EulerCycle** (`bidir = false`: as printed; `bidir = true`: repaired). -/
def ssEuler (bidir : Bool) (k : ℕ) (R : RingProtocol RS) : GProtocol (EState k RS) where
  δ p q := {o | ∃ ch : EChoice k RS, ch.Valid R ∧ o = eulerStep bidir R ch p q}

/-- Output: a node is a leader iff one of its virtual nodes is a ring leader. -/
def EState.out (R : RingProtocol RS) (s : EState k RS) : Bool :=
  decide (∃ i, R.lead (s.node i).ringState = true)

/-! ### Basic facts -/

lemma VNode.finite [Finite RS] : Finite (VNode k RS) := by
  refine Finite.of_injective (fun s : VNode k RS => (s.ringState, s.pred, s.succ, s.token, s.bit)) ?_
  intro a b h
  cases a; cases b
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  subst h1 h2 h3 h4 h5; rfl

lemma EState.finite [Finite RS] : Finite (EState k RS) := by
  have := VNode.finite (k := k) (RS := RS)
  refine Finite.of_injective (fun s : EState k RS =>
    (s.node, s.color, s.prevColor, s.colorBit, s.errFlag)) ?_
  intro a b h
  cases a; cases b
  simp only [Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  subst h1 h2 h3 h4 h5; rfl

/-- Valid choices exist (given a ring protocol with nonempty transition sets). -/
lemma exists_valid_choice (R : RingProtocol RS) (hR : ∀ a b, (R.δ a b).Nonempty)
    (c : Fin (4 * k ^ 2)) (s : EState k RS) : ∃ ch : EChoice k RS, ch.Valid R ∧ ch.rc1 = c := by
  classical
  choose ρ hρ using hR
  have hpick : ∀ u v : EState k RS, ∃ p : Fin k × Fin k,
      (∃ i j, FMatch u v i j) → FMatch u v p.1 p.2 := by
    intro u v
    by_cases h : ∃ i j, FMatch u v i j
    · obtain ⟨i, j, hij⟩ := h; exact ⟨(i, j), fun _ => hij⟩
    · by_cases hk : Nonempty (Fin k)
      · obtain ⟨i⟩ := hk; exact ⟨(i, i), fun h' => absurd h' h⟩
      · exact absurd ⟨⟨c.val % k, Nat.mod_lt _ (by
          rcases Nat.eq_zero_or_pos k with h0 | h0
          · subst h0; simp at c; exact c.elim0
          · exact h0)⟩⟩ hk
  choose pick hpick using hpick
  exact ⟨⟨c, c, false, fun u v => pick u v, ρ, s, false, false⟩, ⟨hρ, hpick⟩, rfl⟩

lemma ssEuler_nonempty (bidir : Bool) (R : RingProtocol RS) (hR : ∀ a b, (R.δ a b).Nonempty)
    (p q : EState k RS) : ((ssEuler bidir k R).δ p q).Nonempty := by
  obtain ⟨ch, hch, -⟩ := exists_valid_choice R hR p.color p
  exact ⟨_, ch, hch, rfl⟩

end SSLERegular
