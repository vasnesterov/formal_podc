import Cslib.Computability.Distributed.Congest.Randomized
import Mathlib

-- CSLib candidate: Cslib/Computability/Distributed/CongestedClique/Broadcast.lean

/-!
# The broadcast congested clique (CLIQUE-BCAST) and two-party simulations

The **broadcast congested clique** `CLIQUE-BCAST_{n,b}` (equivalently: the number-in-hand
multi-party shared-blackboard model): `n` nodes with known identities (the elements of the finite
type `V`) run in synchronous rounds; in every round every node writes one `b`-bit message on the
blackboard, i.e. broadcasts it to all nodes, and then every node updates its state from its own
state and the messages of all nodes. There are no failures; local computation is free.

* `Bcast.Algorithm V I σ b`: deterministic algorithms with node inputs in `I`; `run`, `Accepts`
  ("all nodes accept after `T` rounds", the usual decision convention).
* `Bcast.Split X Y V I`: a two-party split of the node inputs: nodes with `alice v = true` have
  inputs depending only on Alice's input `x`, the others only on Bob's input `y`.
* `Bcast.Split.simulation`: Alice and Bob simulate `T` rounds with `T · |V| · b + 2` bits
  (each round, each player writes the messages of her/his nodes).
* `Bcast.Split.rand_simulation`: randomized algorithms (private coins `ρ` per node, part of the node
  input) yield private-coin protocols (`Cslib.CommunicationComplexity.Protocol.RandComputes`) with
  the same error and cost.
-/

namespace Cslib.CongestedClique.Bcast

open Cslib.CommunicationComplexity

/-- `b`-bit messages. -/
abbrev Msg (b : ℕ) := Fin b → Bool

/-- A deterministic CLIQUE-BCAST algorithm with `b`-bit messages: node `v` in state `s` broadcasts
`send v s`, then moves to `step v s m` where `m w` is the message broadcast by `w` (all nodes,
including `v` itself). -/
structure Algorithm (V I σ : Type*) (b : ℕ) where
  /-- Initial state from the node's identity and input. -/
  init : V → I → σ
  /-- Message broadcast by `v` in state `s`. -/
  send : V → σ → Msg b
  /-- State update from all broadcast messages. -/
  step : V → σ → (V → Msg b) → σ
  /-- Local output (accept / reject). -/
  out : V → σ → Bool

namespace Algorithm

variable {V I σ : Type*} {b : ℕ}

/-- States after `t` rounds with node inputs `inp`. -/
def run (A : Algorithm V I σ b) (inp : V → I) : ℕ → V → σ
  | 0 => fun v => A.init v (inp v)
  | t + 1 => fun v => A.step v (A.run inp t v) (fun w => A.send w (A.run inp t w))

/-- After `T` rounds all nodes accept. -/
def Accepts (A : Algorithm V I σ b) (inp : V → I) (T : ℕ) : Prop :=
  ∀ v, A.out v (A.run inp T v) = true

/-- Acceptance is decidable on a finite node set. -/
instance [Fintype V] (A : Algorithm V I σ b) (inp : V → I) (T : ℕ) : Decidable (A.Accepts inp T) := by
  unfold Accepts; infer_instance

/-- The states computed by a single node from its own input and a history `h` of all broadcasts
(`h s w` = message of `w` in round `s`). -/
def simState (A : Algorithm V I σ b) (inp : V → I) (h : ℕ → V → Msg b) : ℕ → V → σ
  | 0 => fun v => A.init v (inp v)
  | t + 1 => fun v => A.step v (A.simState inp h t v) (h t)

/-- A node's simulated state is exact if its input is right and the history is right so far. -/
lemma simState_eq (A : Algorithm V I σ b) (inp inp' : V → I) (h : ℕ → V → Msg b) (v : V)
    (hv : inp' v = inp v) :
    ∀ t, (∀ s < t, h s = fun w => A.send w (A.run inp s w)) →
      A.simState inp' h t v = A.run inp t v
  | 0, _ => by simp [simState, run, hv]
  | t + 1, hh => by
      simp only [simState, run]
      rw [simState_eq A inp inp' h v hv t (fun s hs => hh s (by omega)), hh t (by omega)]

/-- Number of random strings `r : V → ρ` on which a randomized algorithm (node `v` gets input
`(inp v, r v)`) gives an answer different from `c`. -/
noncomputable def randErr [Fintype V] {ρ : Type*} [Fintype ρ] (A : Algorithm V (I × ρ) σ b)
    (inp : V → I) (T : ℕ) (c : Bool) : ℕ := by
  classical
  exact (Finset.univ.filter fun r : V → ρ => decide (A.Accepts (fun v => (inp v, r v)) T) ≠ c).card

/-! ### One-shot algorithms: broadcast an `L`-bit string in `⌈L / b⌉` rounds -/

/-- State of `oneShot`: input, round counter, bits received so far from every node. -/
abbrev OneShotState (V I : Type*) (L : ℕ) := I × ℕ × (V → Fin L → Bool)

/-- Bit `j` of a string of length `L` (`false` beyond the end). -/
def getBit {L : ℕ} (f : Fin L → Bool) (j : ℕ) : Bool := if h : j < L then f ⟨j, h⟩ else false

/-- The algorithm in which every node `v` broadcasts the `L`-bit string `msg v (inp v)` in chunks of
`b` bits (round `t` carries bits `t·b, …, t·b + b - 1`), and then evaluates
`dec v (inp v) (all strings)`. After `⌈L / b⌉` rounds every node knows all strings. -/
def oneShot (L b : ℕ) (msg : V → I → Fin L → Bool) (dec : V → I → (V → Fin L → Bool) → Bool) :
    Algorithm V I (OneShotState V I L) b where
  init _ x := (x, 0, fun _ _ => false)
  send v s := fun j => getBit (msg v s.1) (s.2.1 * b + j.1)
  step _ s M := (s.1, s.2.1 + 1, fun w i =>
    if s.2.1 * b ≤ i.1 ∧ i.1 < s.2.1 * b + b then getBit (M w) (i.1 - s.2.1 * b) else s.2.2 w i)
  out v s := dec v s.1 s.2.2

lemma oneShot_run (L b : ℕ) (msg : V → I → Fin L → Bool) (dec : V → I → (V → Fin L → Bool) → Bool)
    (inp : V → I) : ∀ t v, ((oneShot L b msg dec).run inp t v).1 = inp v ∧
      ((oneShot L b msg dec).run inp t v).2.1 = t ∧
      ∀ w (i : Fin L), i.1 < t * b → ((oneShot L b msg dec).run inp t v).2.2 w i = msg w (inp w) i
  | 0, v => by simp [run, oneShot]
  | t + 1, v => by
      obtain ⟨h1, h2, h3⟩ := oneShot_run L b msg dec inp t v
      have hw := fun w => oneShot_run L b msg dec inp t w
      set A := oneShot L b msg dec
      have e1 : (A.run inp (t + 1) v).1 = (A.run inp t v).1 := rfl
      have e2 : (A.run inp (t + 1) v).2.1 = (A.run inp t v).2.1 + 1 := rfl
      have e3 : ∀ w i, (A.run inp (t + 1) v).2.2 w i =
          if (A.run inp t v).2.1 * b ≤ i.1 ∧ i.1 < (A.run inp t v).2.1 * b + b then
            getBit (A.send w (A.run inp t w)) (i.1 - (A.run inp t v).2.1 * b)
          else (A.run inp t v).2.2 w i := fun _ _ => rfl
      refine ⟨e1.trans h1, by rw [e2, h2], fun w i hi => ?_⟩
      rw [e3, h2]
      split_ifs with h
      · have hs : A.send w (A.run inp t w) = fun j => getBit (msg w (A.run inp t w).1)
            ((A.run inp t w).2.1 * b + j.1) := rfl
        rw [hs, (hw w).1, (hw w).2.1]
        simp only [getBit]
        rw [dite_eq_left_of_eq_true (eq_true (by omega)), dite_eq_left_of_eq_true (eq_true (by omega))]
        congr 1
        ext; simp only; omega
      · exact h3 w i (by rw [Nat.add_mul, one_mul] at hi; omega)

/-- After `T` rounds with `L ≤ T · b`, `oneShot` accepts iff every node's decision on the full
collection of strings is `true`. -/
theorem oneShot_accepts (L b : ℕ) (msg : V → I → Fin L → Bool)
    (dec : V → I → (V → Fin L → Bool) → Bool) (inp : V → I) (T : ℕ) (hT : L ≤ T * b) :
    (oneShot L b msg dec).Accepts inp T ↔ ∀ v, dec v (inp v) (fun w => msg w (inp w)) = true := by
  have h : ∀ v, (oneShot L b msg dec).run inp T v = (inp v, T, fun w => msg w (inp w)) := by
    intro v
    obtain ⟨h1, h2, h3⟩ := oneShot_run L b msg dec inp T v
    refine Prod.ext h1 (Prod.ext h2 ?_)
    funext w i; exact h3 w i (by omega)
  unfold Accepts
  simp only [h]
  rfl

end Algorithm

/-- A two-party split of the node inputs. -/
structure Split (X Y V I : Type*) where
  /-- Node inputs for Alice's input `x` and Bob's input `y`. -/
  inp : X → Y → V → I
  /-- `alice v = true` iff `v` is simulated by Alice. -/
  alice : V → Bool
  /-- Alice's nodes' inputs do not depend on `y`. -/
  inp_alice : ∀ x y y' v, alice v = true → inp x y v = inp x y' v
  /-- Bob's nodes' inputs do not depend on `x`. -/
  inp_bob : ∀ x x' y v, alice v = false → inp x y v = inp x' y v

namespace Split

open Protocol

variable {X Y V I σ : Type*} {b : ℕ} (S : Split X Y V I) [DecidableEq V]

/-- Record the messages of round `t` in a history. -/
def record (h : ℕ → V → Msg b) (t : ℕ) (mA : {v // S.alice v = true} → Msg b)
    (mB : {v // S.alice v = false} → Msg b) : ℕ → V → Msg b :=
  fun s w => if s = t then
      (if hw : S.alice w = true then mA ⟨w, hw⟩ else mB ⟨w, by simpa using hw⟩)
    else h s w

/-- The protocol simulating `r` more rounds from round `t` with history `h`: in each round Alice
writes the messages of her nodes, then Bob those of his nodes; at the end each player sends one
bit ("all my nodes accept"). -/
noncomputable def simProt [Fintype V] (A : Algorithm V I σ b) (x₀ : X) (y₀ : Y) :
    ℕ → ℕ → (ℕ → V → Msg b) → Protocol X Y Bool
  | 0, t, h =>
      .alice 2 (fun x => by
          classical exact if ∀ v, S.alice v = true → A.out v (A.simState (S.inp x y₀) h t v) = true
            then 1 else 0)
        fun i => .bob 2 (fun y => by
            classical exact
              if ∀ v, S.alice v = false → A.out v (A.simState (S.inp x₀ y) h t v) = true
              then 1 else 0)
          fun j => .ret (decide (i = 1 ∧ j = 1))
  | r + 1, t, h =>
      .alice (Fintype.card ({v // S.alice v = true} → Msg b))
        (fun x => Fintype.equivFin _ (fun v => A.send v.1 (A.simState (S.inp x y₀) h t v.1)))
        fun i => .bob (Fintype.card ({v // S.alice v = false} → Msg b))
          (fun y => Fintype.equivFin _ (fun v => A.send v.1 (A.simState (S.inp x₀ y) h t v.1)))
          fun j => simProt A x₀ y₀ r (t + 1)
            (S.record h t ((Fintype.equivFin _).symm i) ((Fintype.equivFin _).symm j))

omit [DecidableEq V] in
lemma clog_card (p : V → Prop) [DecidableEq {v // p v}] [Fintype {v // p v}] :
    Nat.clog 2 (Fintype.card ({v // p v} → Msg b)) = Fintype.card {v // p v} * b := by
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  rw [← pow_mul, mul_comm b, Nat.clog_pow _ _ (by norm_num)]

omit [DecidableEq V] in
lemma card_split [Fintype V] :
    Fintype.card {v // S.alice v = true} + Fintype.card {v // S.alice v = false} =
      Fintype.card V := by
  classical
  rw [Fintype.card_subtype, Fintype.card_subtype, ← Finset.card_union_of_disjoint]
  · congr 1; ext v; cases S.alice v <;> simp
  · rw [Finset.disjoint_filter]; intro v _ h1 h2; rw [h1] at h2; simp at h2

/-- The simulating protocol for `r` rounds costs at most `r · |V| · b + 2` bits. -/
lemma simProt_cost [Fintype V] (A : Algorithm V I σ b) (x₀ : X) (y₀ : Y) :
    ∀ r t h, (S.simProt A x₀ y₀ r t h).CostLE (r * (Fintype.card V * b) + 2)
  | 0, t, h => by
      have h2 : Nat.clog 2 2 = 1 := by simpa using Nat.clog_pow 2 1 (by norm_num)
      simp only [simProt, CostLE, zero_mul, zero_add, h2]
      exact ⟨by norm_num, fun i => ⟨by norm_num, fun j => trivial⟩⟩
  | r + 1, t, h => by
      simp only [simProt, CostLE, clog_card]
      have hs := S.card_split
      set a := Fintype.card {v // S.alice v = true}
      set c := Fintype.card {v // S.alice v = false}
      have e : (r + 1) * (Fintype.card V * b) = r * (Fintype.card V * b) + a * b + c * b := by
        rw [← hs]; ring
      refine ⟨by rw [e]; omega, fun i => ⟨by rw [e]; omega, fun j => ?_⟩⟩
      have : (r + 1) * (Fintype.card V * b) + 2 - a * b - c * b = r * (Fintype.card V * b) + 2 := by
        rw [e]; omega
      rw [this]
      exact simProt_cost A x₀ y₀ r (t + 1) _

/-- The simulating protocol computes "all nodes accept", given a correct history. -/
lemma simProt_eval [Fintype V] (A : Algorithm V I σ b) (x₀ : X) (y₀ : Y) (x : X) (y : Y) :
    ∀ r t h, (∀ s < t, h s = fun w => A.send w (A.run (S.inp x y) s w)) →
      (S.simProt A x₀ y₀ r t h).eval x y = decide (A.Accepts (S.inp x y) (t + r))
  | 0, t, h, hh => by
      classical
      have eA : ∀ v, S.alice v = true → A.simState (S.inp x y₀) h t v = A.run (S.inp x y) t v :=
        fun v hv => A.simState_eq _ _ h v (S.inp_alice x y₀ y v hv) t hh
      have eB : ∀ v, S.alice v = false → A.simState (S.inp x₀ y) h t v = A.run (S.inp x y) t v :=
        fun v hv => A.simState_eq _ _ h v (S.inp_bob x₀ x y v hv) t hh
      simp only [simProt, eval, add_zero, Algorithm.Accepts]
      have key : (∀ v, A.out v (A.run (S.inp x y) t v) = true) ↔
          (∀ v, S.alice v = true → A.out v (A.simState (S.inp x y₀) h t v) = true) ∧
            (∀ v, S.alice v = false → A.out v (A.simState (S.inp x₀ y) h t v) = true) := by
        constructor
        · intro h'
          exact ⟨fun v hv => by rw [eA v hv]; exact h' v, fun v hv => by rw [eB v hv]; exact h' v⟩
        · rintro ⟨h1, h2⟩ v
          cases hv : S.alice v
          · rw [← eB v hv]; exact h2 v hv
          · rw [← eA v hv]; exact h1 v hv
      by_cases h1 : ∀ v, S.alice v = true → A.out v (A.simState (S.inp x y₀) h t v) = true <;>
      by_cases h2 : ∀ v, S.alice v = false → A.out v (A.simState (S.inp x₀ y) h t v) = true <;>
      simp [h1, h2, key]
  | r + 1, t, h, hh => by
      simp only [simProt, eval, Equiv.symm_apply_apply]
      rw [simProt_eval A x₀ y₀ x y r (t + 1), show t + 1 + r = t + (r + 1) by omega]
      intro s hs
      funext w
      simp only [record]
      split_ifs with hst hw
      · subst hst
        exact congrArg (A.send w)
          (A.simState_eq _ _ h w (S.inp_alice x y₀ y w hw) s hh)
      · subst hst
        exact congrArg (A.send w)
          (A.simState_eq _ _ h w (S.inp_bob x₀ x y w (by simpa using hw)) s hh)
      · exact congrFun (hh s (by omega)) w

/-- **Simulation.** A `T`-round CLIQUE-BCAST algorithm with `b`-bit messages yields a two-party
protocol computing "all nodes accept" with at most `T · |V| · b + 2` bits. -/
theorem simulation [Fintype V] [Nonempty X] [Nonempty Y] (A : Algorithm V I σ b) (T : ℕ) :
    ∃ P : Protocol X Y Bool, P.CostLE (T * (Fintype.card V * b) + 2) ∧
      P.Computes fun x y => decide (A.Accepts (S.inp x y) T) := by
  refine ⟨S.simProt A (Classical.arbitrary X) (Classical.arbitrary Y) T 0 (fun _ _ _ => false),
    S.simProt_cost A _ _ T 0 _, fun x y => ?_⟩
  rw [S.simProt_eval A _ _ x y T 0 _ (fun s hs => absurd hs (Nat.not_lt_zero s)), zero_add]

/-- **Lower bound from a split (deterministic).** If every protocol computing `f` needs `C` bits
and a `T`-round algorithm accepts exactly when `f x y = true`, then `C ≤ T · |V| · b + 2`. -/
theorem lowerBound [Fintype V] [Nonempty X] [Nonempty Y] (A : Algorithm V I σ b) (T : ℕ)
    (f : X → Y → Bool) (hA : ∀ x y, A.Accepts (S.inp x y) T ↔ f x y = true) (C : ℕ)
    (hC : ∀ (P : Protocol X Y Bool) c, P.Computes f → P.CostLE c → C ≤ c) :
    C ≤ T * (Fintype.card V * b) + 2 := by
  obtain ⟨P, hc, hP⟩ := S.simulation A T
  refine hC P _ (fun x y => ?_) hc
  rw [hP x y]
  cases h : f x y <;> simp [hA, h]

/-! ### Randomized algorithms -/

variable {ρ : Type*}

omit [DecidableEq V] in
/-- Combine Alice's and Bob's random strings. -/
def combine (rA : {v // S.alice v = true} → ρ) (rB : {v // S.alice v = false} → ρ) : V → ρ :=
  fun v => if h : S.alice v = true then rA ⟨v, h⟩ else rB ⟨v, by simpa using h⟩

omit [DecidableEq V] in
/-- `combine` is a bijection. -/
def combineEquiv : ({v // S.alice v = true} → ρ) × ({v // S.alice v = false} → ρ) ≃ (V → ρ) where
  toFun p := S.combine p.1 p.2
  invFun r := (fun v => r v, fun v => r v)
  left_inv p := by
    obtain ⟨rA, rB⟩ := p
    ext ⟨v, hv⟩
    · simp [combine, hv]
    · have : ¬S.alice v = true := by simp [hv]
      simp [combine, this]
  right_inv r := by
    funext v
    by_cases h : S.alice v = true <;> simp [combine, h]

omit [DecidableEq V] in
/-- The split with each node's random string added to its input. -/
def withCoins : Split (X × ({v // S.alice v = true} → ρ)) (Y × ({v // S.alice v = false} → ρ))
    V (I × ρ) where
  inp xr yr v := (S.inp xr.1 yr.1 v, S.combine xr.2 yr.2 v)
  alice := S.alice
  inp_alice xr yr yr' v hv := by
    simp only [Prod.mk.injEq]
    exact ⟨S.inp_alice _ _ _ v hv, by simp [combine, hv]⟩
  inp_bob xr xr' yr v hv := by
    simp only [Prod.mk.injEq]
    have : ¬S.alice v = true := by simp [hv]
    exact ⟨S.inp_bob _ _ _ v hv, by simp [combine, this]⟩

/-- **Simulation (randomized).** A randomized `T`-round CLIQUE-BCAST algorithm yields a
private-coin protocol with at most `T · |V| · b + 2` bits whose number of bad coin pairs on `(x, y)`
equals the number of bad random strings of the algorithm on the inputs `S.inp x y`. -/
theorem rand_simulation [Fintype V] [Fintype ρ] [Nonempty X] [Nonempty Y] [Nonempty ρ]
    (A : Algorithm V (I × ρ) σ b) (T : ℕ) (f : X → Y → Bool) :
    ∃ P : Protocol (X × ({v // S.alice v = true} → ρ)) (Y × ({v // S.alice v = false} → ρ)) Bool,
      P.CostLE (T * (Fintype.card V * b) + 2) ∧
      ∀ x y, P.errCount f x y = A.randErr (S.inp x y) T (f x y) := by
  classical
  obtain ⟨P, hc, hP⟩ := (S.withCoins (ρ := ρ)).simulation A T
  refine ⟨P, hc, fun x y => ?_⟩
  simp only [Protocol.errCount, Algorithm.randErr]
  rw [← Finset.card_map (S.combineEquiv (ρ := ρ)).toEmbedding]
  congr 1
  ext r
  simp only [Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hP]
  have e : S.combine (S.combineEquiv.symm r).1 (S.combineEquiv.symm r).2 = r :=
    S.combineEquiv.apply_symm_apply r
  change decide (A.Accepts (fun v => (S.inp x y v, S.combine (S.combineEquiv.symm r).1
    (S.combineEquiv.symm r).2 v)) T) ≠ f x y ↔ _
  rw [e]

/-- **Lower bound from a split (randomized).** If every private-coin protocol computing `f` with
error `≤ ε` needs `C` bits, and a randomized `T`-round algorithm decides `f` with error `≤ ε` on
every input, then `C ≤ T · |V| · b + 2`. -/
theorem rand_lowerBound [Fintype V] [Fintype ρ] [Nonempty X] [Nonempty Y] [Nonempty ρ]
    (A : Algorithm V (I × ρ) σ b) (T : ℕ) (f : X → Y → Bool) (ε : ℝ)
    (hA : ∀ x y, (A.randErr (S.inp x y) T (f x y) : ℝ) ≤ ε * Fintype.card (V → ρ)) (C : ℕ)
    (hC : ∀ (P : Protocol (X × ({v // S.alice v = true} → ρ))
      (Y × ({v // S.alice v = false} → ρ)) Bool) (c : ℕ),
      P.RandComputes f ε → P.CostLE c → C ≤ c) :
    C ≤ T * (Fintype.card V * b) + 2 := by
  obtain ⟨P, hc, hP⟩ := S.rand_simulation A T f
  refine hC P _ (fun x y => ?_) hc
  rw [hP x y]
  have hcard : (Fintype.card ({v // S.alice v = true} → ρ) : ℝ) *
      Fintype.card ({v // S.alice v = false} → ρ) = Fintype.card (V → ρ) := by
    rw [← Nat.cast_mul, ← Fintype.card_prod, Fintype.card_congr (S.combineEquiv (ρ := ρ))]
  rw [hcard]
  exact hA x y

end Split

end Cslib.CongestedClique.Bcast
