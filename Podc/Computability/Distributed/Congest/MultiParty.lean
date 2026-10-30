import Cslib.Computability.Distributed.Congest.LowerBound
import Podc.Computability.CommunicationComplexity.Blackboard

-- CSLib candidate: Cslib/Computability/Distributed/Congest/MultiParty.lean

/-!
# CONGEST lower bounds from multi-party (blackboard) communication complexity

The `t`-party generalization (Efron–Grossman–Khoury, PODC 2020, Definition 4 and Theorem 5) of the
two-party framework `Cslib.Congest.LBFamily`.

* `MPFamily ι X V I`: a **family of lower bound graphs** for the players `ι`: graphs `G x` on a
  fixed vertex set `V` with node inputs `inp x`, indexed by the players' inputs `x : ∀ i, X i`,
  with a fixed partition `part : V → ι` such that the edges inside `V^i` and the node inputs of
  `V^i` depend only on `x i`, and the cut edges (between different parts) are fixed and contained in
  the finset `Ecut` of *ordered* pairs (so a cut edge is counted twice in `Ecut`).
* `MPFamily.simulation`: the players simulate a `T`-round CONGEST algorithm with `B`-bit messages
  by writing the messages crossing the cut on the blackboard (`T · |Ecut| · B` bits); afterwards
  each player writes a summary `g i (x i) (states) : S` of the final states of its own nodes and
  the output is any function `out` of the summaries (`|ι| · ⌈log₂ |S|⌉` more bits).
* `MPFamily.rand_simulation`: the same for randomized algorithms (node `v` has a private random
  string `r v : ρ`); player `i` draws the random strings of its own nodes, so the protocol is a
  private-coin protocol, and its error count equals the number of bad random strings of the
  algorithm.
* `MPFamily.rand_lowerBound` (Theorem 5): if a randomized algorithm decides (all nodes accept) a
  predicate equivalent to `f` on the family with error `≤ ε`, then every lower bound `C` on the
  cost of private-coin protocols computing `f` with error `≤ ε` satisfies
  `C ≤ T · |Ecut| · B + |ι|`.
-/

namespace Cslib.Congest

open Cslib.CommunicationComplexity Finset

/-- A family of lower bound graphs for the players `ι` (Definition 4 of Efron–Grossman–Khoury):
graphs `G x` and node inputs `inp x` indexed by the inputs `x : ∀ i, X i` of the players, a fixed
partition `part : V → ι` of the nodes, and a finset `Ecut` of ordered pairs containing all edges
between different parts. -/
structure MPFamily (ι : Type*) (X : ι → Type*) (V I : Type*) where
  /-- The graph for the inputs `x`. -/
  G : (∀ i, X i) → SimpleGraph V
  /-- Node inputs (weights, …). -/
  inp : (∀ i, X i) → V → I
  /-- The player simulating each node: `V^i = {v | part v = i}`. -/
  part : V → ι
  /-- A finset of ordered pairs containing all cut edges (in both orientations). -/
  Ecut : Finset (V × V)
  Ecut_sub : ∀ p ∈ Ecut, part p.1 ≠ part p.2
  adj_cut : ∀ x a b, part a ≠ part b → (G x).Adj a b → (a, b) ∈ Ecut
  /-- `G[V^i]` depends only on `x i`. -/
  adj_local : ∀ x x' a b, part a = part b → x (part a) = x' (part a) →
    ((G x).Adj a b ↔ (G x').Adj a b)
  /-- The cut edges do not depend on the inputs. -/
  adj_fixed : ∀ x x' a b, part a ≠ part b → ((G x).Adj a b ↔ (G x').Adj a b)
  /-- The inputs of `V^i`-nodes depend only on `x i`. -/
  inp_local : ∀ x x' v, x (part v) = x' (part v) → inp x v = inp x' v

namespace MPFamily

variable {ι : Type*} {X : ι → Type*} {V I σ : Type*} {B : ℕ} (F : MPFamily ι X V I)

/-! ### Deterministic simulation -/

section Simulation

variable [∀ x, DecidableRel (F.G x).Adj] [DecidableEq ι] [DecidableEq V]

/-- Player `i`'s simulation of the states (meaningful at `V^i`-nodes) from its own input `xi`
(the other players' inputs are replaced by the dummy `x₀`) and the message history `h`
(`h s w v` = message from `w` to `v` in round `s`, read off the blackboard). -/
def sim (A : Algorithm V I σ B) (x₀ : ∀ i, X i) (i : ι) (xi : X i) (h : ℕ → V → V → Msg B) :
    ℕ → V → σ
  | 0 => fun v => A.init v (F.inp (Function.update x₀ i xi) v)
  | t + 1 => fun v => A.step v (sim A x₀ i xi h t v)
      (fun w => if (F.G (Function.update x₀ i xi)).Adj w v then
        some (if F.part w = i then A.send w (sim A x₀ i xi h t w) v else h t w v) else none)

/-- Record the message `m` from `a` to `b` in round `t`. -/
def record (h : ℕ → V → V → Msg B) (t : ℕ) (a b : V) (m : Msg B) : ℕ → V → V → Msg B :=
  fun s w v => if s = t ∧ w = a ∧ v = b then m else h s w v

omit [∀ x, DecidableRel (F.G x).Adj] [DecidableEq ι] [DecidableEq V] in
/-- Adjacency `w – v` only depends on the input of the player owning `v`. -/
lemma adj_iff_of_eq {x x' : ∀ i, X i} {w v : V} (hv : x (F.part v) = x' (F.part v)) :
    (F.G x).Adj w v ↔ (F.G x').Adj w v := by
  by_cases hw : F.part w = F.part v
  · exact F.adj_local x x' w v hw (by rw [hw]; exact hv)
  · exact F.adj_fixed x x' w v hw

/-- The message history `h` is correct on the cut arcs in all rounds `< t`. -/
def Good (A : Algorithm V I σ B) (x : ∀ i, X i) (h : ℕ → V → V → Msg B) (t : ℕ) : Prop :=
  ∀ s < t, ∀ w v, (w, v) ∈ F.Ecut → h s w v = A.send w (A.run (F.G x) (F.inp x) s w) v

omit [DecidableEq V] in
/-- Player `i`'s simulation is exact on `V^i`, given correct cut messages in earlier rounds. -/
lemma sim_eq (A : Algorithm V I σ B) (x x₀ : ∀ i, X i) (i : ι) (h : ℕ → V → V → Msg B) :
    ∀ t, F.Good A x h t → ∀ v, F.part v = i →
      F.sim A x₀ i (x i) h t v = A.run (F.G x) (F.inp x) t v
  | 0, _, v, hv => by
      have e : Function.update x₀ i (x i) (F.part v) = x (F.part v) := by
        rw [hv, Function.update_self]
      simp [sim, Algorithm.run, F.inp_local _ _ v e]
  | t + 1, hh, v, hv => by
      have ih := sim_eq A x x₀ i h t (fun s hs => hh s (Nat.lt_succ_of_lt hs))
      have e : Function.update x₀ i (x i) (F.part v) = x (F.part v) := by
        rw [hv, Function.update_self]
      simp only [sim, Algorithm.run]
      rw [ih v hv]
      congr 1
      funext w
      have hadj : (F.G (Function.update x₀ i (x i))).Adj w v ↔ (F.G x).Adj w v :=
        F.adj_iff_of_eq e
      by_cases hwv : (F.G x).Adj w v
      · simp only [hadj.2 hwv, hwv, ↓reduceIte, Option.some.injEq]
        by_cases hw : F.part w = i
        · simp [hw, ih w hw]
        · simp only [hw, ↓reduceIte]
          exact hh t (Nat.lt_succ_self t) w v (F.adj_cut x w v (by rw [hv]; exact hw) hwv)
      · have h0 : ¬(F.G _).Adj w v := fun h' => hwv (hadj.1 h')
        simp only [h0, hwv, ↓reduceIte]

omit [DecidableEq ι] in
lemma good_record {A : Algorithm V I σ B} {x : ∀ i, X i} {h : ℕ → V → V → Msg B} {t : ℕ}
    (hh : F.Good A x h t) (a b : V) (m : Msg B) : F.Good A x (record h t a b m) t := by
  intro s hs w v hwv
  simp only [record, Nat.ne_of_lt hs, false_and, ↓reduceIte]
  exact hh s hs w v hwv

omit [DecidableEq ι] [DecidableEq V] in
lemma good_succ {A : Algorithm V I σ B} {x : ∀ i, X i} {h : ℕ → V → V → Msg B} {t : ℕ}
    (hh : F.Good A x h t)
    (ht : ∀ p ∈ F.Ecut, h t p.1 p.2 = A.send p.1 (A.run (F.G x) (F.inp x) t p.1) p.2) :
    F.Good A x h (t + 1) := by
  intro s hs w v hwv
  rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
  · exact hh s hs w v hwv
  · exact ht (w, v) hwv

variable [Fintype V] {S α : Type*} [Fintype S]

/-- Write the messages of round `t` along the arcs `L` (each by the player owning the sender), then
continue with `k` applied to the updated history. -/
noncomputable def writeArcs (A : Algorithm V I σ B) (x₀ : ∀ i, X i) (t : ℕ)
    (k : (ℕ → V → V → Msg B) → BBProtocol X α) :
    List (V × V) → (ℕ → V → V → Msg B) → BBProtocol X α
  | [], h => k h
  | p :: L, h => .write (F.part p.1) (Fintype.card (Msg B))
      (fun xi => Fintype.equivFin (Msg B) (A.send p.1 (F.sim A x₀ (F.part p.1) xi h t p.1) p.2))
      (fun j => writeArcs A x₀ t k L (record h t p.1 p.2 ((Fintype.equivFin (Msg B)).symm j)))

/-- After round `t`: the players in `L` write their summaries `g i (x i) (simulated states)`. -/
noncomputable def writeSummaries (A : Algorithm V I σ B) (x₀ : ∀ i, X i) (t : ℕ)
    (h : ℕ → V → V → Msg B) (g : ∀ i, X i → (V → σ) → S) (out : (ι → S) → α) :
    List ι → (ι → S) → BBProtocol X α
  | [], vals => .ret (out vals)
  | i :: L, vals => .write i (Fintype.card S)
      (fun xi => Fintype.equivFin S (g i xi (F.sim A x₀ i xi h t)))
      (fun j => writeSummaries A x₀ t h g out L (Function.update vals i ((Fintype.equivFin S).symm j)))

omit [Fintype V] [Fintype S] in
/-- Evaluation of `writeArcs`: the written messages are the true ones. -/
lemma writeArcs_eval (A : Algorithm V I σ B) (x₀ x : ∀ i, X i) (t : ℕ)
    (k : (ℕ → V → V → Msg B) → BBProtocol X α) (R : α)
    (hk : ∀ h', F.Good A x h' (t + 1) → (k h').eval x = R) :
    ∀ (L : List (V × V)) (h : ℕ → V → V → Msg B), F.Good A x h t →
      (∀ p ∈ F.Ecut, p ∉ L → h t p.1 p.2 = A.send p.1 (A.run (F.G x) (F.inp x) t p.1) p.2) →
      (F.writeArcs A x₀ t k L h).eval x = R
  | [], h, hh, hL => hk h (F.good_succ hh fun p hp => hL p hp List.not_mem_nil)
  | q :: L, h, hh, hL => by
      simp only [writeArcs, BBProtocol.eval_write, Equiv.symm_apply_apply]
      refine writeArcs_eval A x₀ x t k R hk L _ (F.good_record hh _ _ _) ?_
      intro p hp hpL
      by_cases hpq : p = q
      · subst hpq
        simp only [record, and_self, ↓reduceIte]
        rw [F.sim_eq A x x₀ _ h t hh p.1 rfl]
      · have hne : ¬(p.1 = q.1 ∧ p.2 = q.2) := fun h' => hpq (Prod.ext h'.1 h'.2)
        simp only [record, true_and, hne, ↓reduceIte]
        exact hL p hp (by simp [hpq, hpL])

omit [DecidableEq V] [Fintype V] in
/-- Evaluation of `writeSummaries`. -/
lemma writeSummaries_eval (A : Algorithm V I σ B) (x₀ x : ∀ i, X i) (t : ℕ)
    (h : ℕ → V → V → Msg B) (g : ∀ i, X i → (V → σ) → S) (out : (ι → S) → α) :
    ∀ (L : List ι) (vals : ι → S), (F.writeSummaries A x₀ t h g out L vals).eval x =
      out (fun j => if j ∈ L then g j (x j) (F.sim A x₀ j (x j) h t) else vals j)
  | [], vals => by simp [writeSummaries]
  | i :: L, vals => by
      simp only [writeSummaries, BBProtocol.eval_write, Equiv.symm_apply_apply]
      rw [writeSummaries_eval A x₀ x t h g out L]
      congr 1
      funext j
      by_cases hj : j ∈ L
      · simp [hj]
      · by_cases hji : j = i
        · subst hji; simp [hj]
        · simp [hj, hji]

omit [Fintype V] in
lemma clog_card_msg : Nat.clog 2 (Fintype.card (Msg B)) = B := by
  simp only [Msg, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  exact Nat.clog_pow _ _ (by norm_num)

omit [Fintype V] [Fintype S] in
/-- Cost of `writeArcs`. -/
lemma writeArcs_cost (A : Algorithm V I σ B) (x₀ : ∀ i, X i) (t : ℕ)
    (k : (ℕ → V → V → Msg B) → BBProtocol X α) (c : ℕ) (hk : ∀ h', (k h').CostLE c) :
    ∀ (L : List (V × V)) (h : ℕ → V → V → Msg B),
      (F.writeArcs A x₀ t k L h).CostLE (L.length * B + c)
  | [], h => by simpa [writeArcs] using hk h
  | q :: L, h => by
      simp only [writeArcs]
      refine BBProtocol.CostLE.mono (BBProtocol.costLE_write
        fun j => writeArcs_cost A x₀ t k c hk L _) ?_
      rw [clog_card_msg, List.length_cons]
      nlinarith

omit [DecidableEq V] [Fintype V] in
/-- Cost of `writeSummaries`. -/
lemma writeSummaries_cost (A : Algorithm V I σ B) (x₀ : ∀ i, X i) (t : ℕ)
    (h : ℕ → V → V → Msg B) (g : ∀ i, X i → (V → σ) → S) (out : (ι → S) → α) :
    ∀ (L : List ι) (vals : ι → S),
      (F.writeSummaries A x₀ t h g out L vals).CostLE (L.length * Nat.clog 2 (Fintype.card S))
  | [], vals => trivial
  | i :: L, vals => by
      simp only [writeSummaries]
      refine BBProtocol.CostLE.mono (BBProtocol.costLE_write
        fun j => writeSummaries_cost A x₀ t h g out L _) ?_
      rw [List.length_cons]
      nlinarith

variable [Fintype ι] [Nonempty S]

/-- The protocol simulating `r` more rounds from round `t` with history `h`, then writing the
summaries. -/
noncomputable def simProt (A : Algorithm V I σ B) (x₀ : ∀ i, X i) (g : ∀ i, X i → (V → σ) → S)
    (out : (ι → S) → α) : ℕ → ℕ → (ℕ → V → V → Msg B) → BBProtocol X α
  | 0, t, h => F.writeSummaries A x₀ t h g out Finset.univ.toList (fun _ => Classical.arbitrary S)
  | r + 1, t, h => F.writeArcs A x₀ t (fun h' => simProt A x₀ g out r (t + 1) h') F.Ecut.toList h


omit [Fintype V] in
/-- Evaluation of the simulating protocol, given correct cut messages before round `t`. -/
lemma simProt_eval (A : Algorithm V I σ B) (x₀ x : ∀ i, X i) (g : ∀ i, X i → (V → σ) → S)
    (out : (ι → S) → α)
    (hg : ∀ i xi (s s' : V → σ), (∀ v, F.part v = i → s v = s' v) → g i xi s = g i xi s') :
    ∀ r t h, F.Good A x h t →
      (F.simProt A x₀ g out r t h).eval x = out (fun i => g i (x i) (A.run (F.G x) (F.inp x) (t + r)))
  | 0, t, h, hh => by
      simp only [simProt, writeSummaries_eval, Finset.mem_toList, Finset.mem_univ, ↓reduceIte,
        add_zero]
      congr 1
      funext i
      exact hg i (x i) _ _ fun v hv => F.sim_eq A x x₀ i h t hh v hv
  | r + 1, t, h, hh => by
      simp only [simProt]
      refine F.writeArcs_eval A x₀ x t _ _ (fun h' hh' => ?_) _ h hh
        (fun p hp hpL => absurd (Finset.mem_toList.2 hp) hpL)
      rw [simProt_eval A x₀ x g out hg r (t + 1) h' hh', show t + 1 + r = t + (r + 1) by omega]

omit [Fintype V] in
/-- Cost of the simulating protocol. -/
lemma simProt_cost (A : Algorithm V I σ B) (x₀ : ∀ i, X i) (g : ∀ i, X i → (V → σ) → S)
    (out : (ι → S) → α) : ∀ r t h,
      (F.simProt A x₀ g out r t h).CostLE
        (r * (F.Ecut.card * B) + Fintype.card ι * Nat.clog 2 (Fintype.card S))
  | 0, t, h => by
      simp only [simProt, zero_mul, zero_add]
      simpa [Finset.length_toList, Finset.card_univ] using
        F.writeSummaries_cost A x₀ t h g out Finset.univ.toList _
  | r + 1, t, h => by
      simp only [simProt]
      refine BBProtocol.CostLE.mono (F.writeArcs_cost A x₀ t _ _
        (fun h' => simProt_cost A x₀ g out r (t + 1) h') _ h) ?_
      rw [Finset.length_toList]
      nlinarith

omit [Fintype V] in
/-- **Simulation** (Theorem 5 of Efron–Grossman–Khoury, communication part): a `T`-round CONGEST
algorithm with `B`-bit messages on a family of lower bound graphs yields a blackboard protocol
with at most `T · |Ecut| · B + |ι| · ⌈log₂ |S|⌉` bits that computes `out` of the summaries
`g i (x i) (final states)`, provided each `g i` only looks at the states of `V^i`-nodes. -/
theorem simulation [Nonempty (∀ i, X i)] (A : Algorithm V I σ B) (T : ℕ)
    (g : ∀ i, X i → (V → σ) → S) (out : (ι → S) → α)
    (hg : ∀ i xi (s s' : V → σ), (∀ v, F.part v = i → s v = s' v) → g i xi s = g i xi s') :
    ∃ P : BBProtocol X α,
      P.CostLE (T * (F.Ecut.card * B) + Fintype.card ι * Nat.clog 2 (Fintype.card S)) ∧
      ∀ x, P.eval x = out (fun i => g i (x i) (A.run (F.G x) (F.inp x) T)) := by
  refine ⟨F.simProt A (Classical.arbitrary _) g out T 0 (fun _ _ _ _ => false),
    F.simProt_cost A _ g out T 0 _, fun x => ?_⟩
  rw [F.simProt_eval A _ x g out hg T 0 _ (fun s hs => absurd hs (Nat.not_lt_zero s)), zero_add]

end Simulation

/-! ### Randomized algorithms -/

section Randomized

variable {ρ : Type*}

/-- Combine the players' random strings into one random string per node. -/
def combine (r : ∀ i, {v // F.part v = i} → ρ) : V → ρ := fun v => r (F.part v) ⟨v, rfl⟩

/-- `combine` is a bijection. -/
def combineEquiv : (∀ i, {v // F.part v = i} → ρ) ≃ (V → ρ) where
  toFun := F.combine
  invFun f _ u := f u.1
  left_inv r := by
    funext i u
    obtain ⟨v, rfl⟩ := u
    rfl
  right_inv _ := rfl

theorem combineEquiv_apply (r : ∀ i, {v // F.part v = i} → ρ) :
    F.combineEquiv r = F.combine r := rfl

/-- The family with each node's random string added to its input; player `i`'s input is
`(x i, r i)`. -/
def withCoins : MPFamily ι (fun i => X i × ({v // F.part v = i} → ρ)) V (I × ρ) where
  G xr := F.G (fun i => (xr i).1)
  inp xr v := (F.inp (fun i => (xr i).1) v, F.combine (fun i => (xr i).2) v)
  part := F.part
  Ecut := F.Ecut
  Ecut_sub := F.Ecut_sub
  adj_cut _ := F.adj_cut _
  adj_local _ _ a b hab hx := F.adj_local _ _ a b hab (congrArg Prod.fst hx)
  adj_fixed _ _ := F.adj_fixed _ _
  inp_local _ _ v hx :=
    Prod.ext (F.inp_local _ _ v (congrArg Prod.fst hx)) (congrArg (fun p => p.2 ⟨v, rfl⟩) hx)

theorem withCoins_G (xr : ∀ i, X i × ({v // F.part v = i} → ρ)) :
    (F.withCoins (ρ := ρ)).G xr = F.G (fun i => (xr i).1) := rfl

theorem withCoins_inp (xr : ∀ i, X i × ({v // F.part v = i} → ρ)) (v : V) :
    (F.withCoins (ρ := ρ)).inp xr v = (F.inp (fun i => (xr i).1) v, F.combine (fun i => (xr i).2) v) :=
  rfl

theorem withCoins_part : (F.withCoins (ρ := ρ)).part = F.part := rfl

theorem withCoins_Ecut : (F.withCoins (ρ := ρ)).Ecut = F.Ecut := rfl

variable [∀ x, DecidableRel (F.G x).Adj] [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]
  [Fintype ρ] {S : Type*} [Fintype S] [Nonempty S]

/-- Adjacency in the family with coins is adjacency in the original family. -/
instance (xr : ∀ i, X i × ({v // F.part v = i} → ρ)) :
    DecidableRel ((F.withCoins (ρ := ρ)).G xr).Adj :=
  inferInstanceAs (DecidableRel (F.G (fun i => (xr i).1)).Adj)

omit [Fintype ρ] [Fintype V] in
/-- **Simulation, randomized**: a randomized `T`-round algorithm (node `v` gets the private random
string `r v`) yields a private-coin blackboard protocol (player `i` holds the random strings of
`V^i`) with at most `T · |Ecut| · B + |ι| · ⌈log₂ |S|⌉` bits that, on inputs `x` and coins `r`,
outputs `out` of the summaries of the run with random strings `combine r`. -/
theorem rand_simulation [Nonempty (∀ i, X i)] [Nonempty ρ] (A : Algorithm V (I × ρ) σ B) (T : ℕ)
    (g : ∀ i, X i → (V → σ) → S) (out : (ι → S) → Bool)
    (hg : ∀ i xi (s s' : V → σ), (∀ v, F.part v = i → s v = s' v) → g i xi s = g i xi s') :
    ∃ P : BBProtocol (fun i => X i × ({v // F.part v = i} → ρ)) Bool,
      P.CostLE (T * (F.Ecut.card * B) + Fintype.card ι * Nat.clog 2 (Fintype.card S)) ∧
      ∀ x (r : ∀ i, {v // F.part v = i} → ρ), P.eval (fun i => (x i, r i)) =
        out (fun i => g i (x i) (A.run (F.G x) (fun v => (F.inp x v, F.combine r v)) T)) := by
  have : Nonempty (∀ i, X i × ({v // F.part v = i} → ρ)) :=
    ⟨fun i => (Classical.arbitrary (∀ i, X i) i, fun _ => Classical.arbitrary ρ)⟩
  obtain ⟨P, hc, hP⟩ := (F.withCoins (ρ := ρ)).simulation A T (fun i xr s => g i xr.1 s) out
    (fun i xr s s' h => hg i xr.1 s s' h)
  exact ⟨P, hc, fun x r => hP _⟩

omit [∀ x, DecidableRel (F.G x).Adj] in
/-- The error count of the protocol of `rand_simulation` is the number of random strings of the
algorithm on which `out` of the summaries differs from `f x`. -/
theorem errCount_eq_of_eval (P : BBProtocol (fun i => X i × ({v // F.part v = i} → ρ)) Bool)
    (f : (∀ i, X i) → Bool) (x : ∀ i, X i) (Φ : (V → ρ) → Bool)
    (hP : ∀ r : ∀ i, {v // F.part v = i} → ρ, P.eval (fun i => (x i, r i)) = Φ (F.combine r)) :
    P.errCount f x = (univ.filter fun r : V → ρ => Φ r ≠ f x).card := by
  classical
  simp only [BBProtocol.errCount]
  rw [← card_map (F.combineEquiv (ρ := ρ)).toEmbedding]
  congr 1
  ext r
  simp only [mem_map_equiv, mem_filter, mem_univ, true_and]
  rw [hP, ← F.combineEquiv_apply, Equiv.apply_symm_apply]

/-- **Theorem 5 of Efron–Grossman–Khoury (randomized).** If every private-coin blackboard protocol
computing `f` (under the promise `prom`) with error `≤ ε` writes at least `C` bits, and a randomized
`T`-round algorithm with `B`-bit messages decides `f` on the family (all nodes accept iff `f x`)
with error `≤ ε` on every input satisfying the promise, then `C ≤ T · |Ecut| · B + |ι|`. -/
theorem rand_lowerBound [Nonempty (∀ i, X i)] [Nonempty ρ] (A : Algorithm V (I × ρ) σ B) (T : ℕ)
    (prom : (∀ i, X i) → Prop) (f : (∀ i, X i) → Bool) (ε : ℝ)
    (hA : ∀ x, prom x → ((univ.filter fun r : V → ρ =>
      decide (A.Accepts (F.G x) (fun v => (F.inp x v, r v)) T) ≠ f x).card : ℝ) ≤
        ε * Fintype.card (V → ρ))
    (C : ℕ)
    (hC : ∀ (P : BBProtocol (fun i => X i × ({v // F.part v = i} → ρ)) Bool) (c : ℕ),
      P.RandComputes prom f ε → P.CostLE c → C ≤ c) :
    C ≤ T * (F.Ecut.card * B) + Fintype.card ι := by
  obtain ⟨P, hc, hP⟩ := F.rand_simulation (S := Bool) A T
    (fun i _ s => decide (∀ v, F.part v = i → A.out v (s v) = true))
    (fun b => decide (∀ i, b i = true))
    (fun i _ s s' h => by
      simp only [decide_eq_decide]
      exact forall_congr' fun v => imp_congr_right fun hv => by rw [h v hv])
  have h2 : Nat.clog 2 (Fintype.card Bool) = 1 := by
    simpa using Nat.clog_pow 2 1 (by norm_num)
  rw [h2, mul_one] at hc
  refine hC P _ (fun x hx => ?_) hc
  rw [F.errCount_eq_of_eval P f x (fun r => decide (A.Accepts (F.G x) (fun v => (F.inp x v, r v)) T))
    (fun r => by
      rw [hP x r]
      simp only [Algorithm.Accepts, decide_eq_true_eq, decide_eq_decide]
      exact ⟨fun h v => h _ v rfl, fun h i v _ => h v⟩)]
  rw [Fintype.card_congr (F.combineEquiv (ρ := ρ))]
  exact hA x hx

end Randomized

end MPFamily

end Cslib.Congest
