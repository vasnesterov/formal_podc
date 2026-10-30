import Papers.PODC2023.AmortizedByzantineBroadcast.Consistency

/-!
# Lemma 3 and Validity of Algorithm 4 fail

A concrete run of Algorithm 4 with `n = 6`, `f = 2`, `ε = 1/6` (so `f ≤ (1/2 - ε) n`) and
`G_ε = K₆` (an `(n, 2ε, 1 - 2ε)`-expander, `isExpander_K6`), Byzantine nodes `F = {4, 5}`
(indices; the paper's nodes 5 and 6), senders `S₁ = 4`, `S₂ = 0`.

The flaw: in step (8) (Query-1) a node `u` without a commit-proof sends `query₁` to the smallest
node `v` that "has not accused `L_i`" — but an honest `v` that also lacks the commit-proof
accuses `L_i` *in the same round*, so `u` cannot know it. `v` then cannot answer in Respond-1 and
`u` accuses the honest `v` in Query-2. With the help of the Byzantine nodes this yields a
corrupt-proof `thsig(accuse, v)` of an honest node, after which every honest node skips the epochs
led by `v` forever.

The run (slot 1, epoch 0, leader `S₁ = 4`): the Byzantine leader behaves correctly up to the
commit-proof, which it sends to node `3` only. Nodes `0, 1, 2` accuse `4` (only 3 accusations,
`n - f = 4` are needed for a corrupt-proof) and query: `1` and `2` query node `0`, node `0` queries
node `1` — nobody of them has the commit-proof. In Query-2, `1` and `2` accuse node `0`, and so do
the Byzantine nodes `4, 5`: four accusations, a corrupt-proof of the honest node `0`. (Node `3`
then answers the `query₂`s in Respond-2 and slot 1 completes.) In slot 2 the sender is node `0`,
honest, with input `true`: epochs 0 and 1 (both led by node `0`) are skipped by all honest nodes,
and the honest leader of epoch 2 (node `1`) proposes its arbitrary value `false`, which every honest
node commits.

* `not_lemma3`: Lemma 3 ("if the leader `L_i` is honest, all honest nodes commit by the end of
  epoch `i` in each slot") fails — for all three readings of the skip condition.
* `not_validity`: Validity fails (for the two readings in which committed nodes keep answering
  queries): the sender of slot 2 is honest and invoked `bc₂(true)` after all honest nodes
  committed in slot 1, yet no honest node ever commits `true` in slot 2 (they commit `false`).
* `theorem1_applies`: the run satisfies all hypotheses of the consistency theorem.
-/

namespace Podc.AmortizedByzantineBroadcast.Counterexample

open Podc.AmortizedByzantineBroadcast Finset

/-- `n = 6`, `f = 2`, `G_ε = K₆`, `S₁ = 4`, `S_k = 0` for `k ≥ 2`, arbitrary value `false`. -/
def P6 : Params 6 Bool where
  f := 2
  G := fun u w => u != w
  sender := fun k => if k = 1 then 4 else 0
  dflt := fun _ _ _ => false

/-- The honest nodes. -/
def honest6 : List (Fin 6) := [0, 1, 2, 3]

/-- The Byzantine messages: `4` proposes `false` in epoch 0 of slot 1, multicasts the certificate
and sends the commit-proof to node `3` only; `4` and `5` accuse node `0` in Query-2. -/
def advX (r : ℕ) (b : Fin 6) : List (Fin 6 × Item 6 Bool) :=
  if r = 1 ∧ b = 4 then honest6.map fun w => (w, .prop 4 1 0 false none)
  else if r = 4 ∧ b = 4 then honest6.map fun w => (w, .cert 1 0 false)
  else if r = 6 ∧ b = 4 then [(3, .cproof 1 0 false)]
  else if r = 9 ∧ (b = 4 ∨ b = 5) then honest6.map fun w => (w, .accuse b 0)
  else []

/-- The scenario: Byzantine `{4, 5}`, every input `true`. -/
def scX : Scenario 6 Bool where
  F := {4, 5}
  inp := fun _ _ => true
  adv := advX

lemma mem_F {u : Fin 6} : u ∈ scX.F ↔ u = 4 ∨ u = 5 := by simp [scX]

lemma not_mem_F {u : Fin 6} : u ∉ scX.F ↔ u ∈ honest6 := by
  rw [mem_F]; revert u; decide

/-! ### The parameters satisfy the paper's assumptions -/

lemma union_nbrs_K6 (S : Finset (Fin 6)) (hS : 2 ≤ S.card) : S ∪ nbrs P6.G S = univ := by
  ext w
  simp only [mem_union, nbrs, mem_filter, mem_univ, true_and, iff_true]
  right
  obtain ⟨u, hu, huw⟩ := S.exists_mem_ne (by omega) w
  exact ⟨u, hu, by simp [P6, huw]⟩

/-- `K₆` is a `(6, 2ε, 1 - 2ε)`-expander for `ε = 1/6`. -/
theorem isExpander_K6 : IsExpander P6.G (2 * (1 / 6)) (1 - 2 * (1 / 6)) := by
  intro S hS
  have h2 : 2 ≤ S.card := by
    norm_num at hS; exact_mod_cast hS
  rw [union_nbrs_K6 S h2]
  norm_num

lemma f_le : ((P6.f : ℕ) : ℝ) ≤ (1 / 2 - 1 / 6) * (6 : ℕ) := by norm_num [P6]

lemma expands : Expands P6 ∧ 2 * P6.f < 6 :=
  expands_of_isExpander (by norm_num) f_le isExpander_K6

lemma card_F : scX.F.card ≤ P6.f := by decide

/-! ### The adversary respects unforgeability -/

/-- Computed facts used for unforgeability: honest nodes vote for `false` in round 3 and send
shares of `C_{1,0}(false)` in round 5. -/
def advFacts (pol : Skip) : Bool :=
  honest6.all fun u =>
    (outs P6 pol scX 3 (exec P6 pol scX 3) u).contains (4, .vote u 1 0 false) &&
    (outs P6 pol scX 5 (exec P6 pol scX 5) u).contains (4, .cshare u 1 0 false)

set_option maxRecDepth 100000 in
lemma advFacts_true (pol : Skip) : advFacts pol = true := by
  cases pol <;> decide +kernel

lemma honest_sent {pol : Skip} {u : Fin 6} (hu : u ∈ honest6) :
    (4, .vote u 1 0 false) ∈ outs P6 pol scX 3 (exec P6 pol scX 3) u ∧
    (4, .cshare u 1 0 false) ∈ outs P6 pol scX 5 (exec P6 pol scX 5) u := by
  have h := advFacts_true pol
  simp only [advFacts, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem] at h
  exact h u hu

lemma card_honest6 : (honest6.toFinset).card = 4 := by decide

theorem advValid (pol : Skip) : scX.AdvValid P6 pol := by
  intro r b w x hb _ hx
  simp only [scX, advX] at hx
  have hnF : ∀ u ∈ honest6.toFinset, u ∉ scX.F := fun u hu =>
    not_mem_F.mpr (List.mem_toFinset.mp hu)
  split_ifs at hx with h1 h2 h3 h4
  · simp only [List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨_, _, -, rfl⟩ := hx
    exact ⟨Or.inl ⟨4, rfl, by simp [scX]⟩, by simp⟩
  · simp only [List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨_, _, -, rfl⟩ := hx
    obtain ⟨rfl, -⟩ := h2
    refine ⟨honest6.toFinset, by rw [card_honest6]; rfl, fun u hu => Or.inr ?_⟩
    exact ⟨3, by norm_num, u, hnF u hu, 4, (honest_sent (List.mem_toFinset.mp hu)).1⟩
  · simp only [List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨-, rfl⟩ := hx
    obtain ⟨rfl, -⟩ := h3
    refine ⟨honest6.toFinset, by rw [card_honest6]; rfl, fun u hu => Or.inr ?_⟩
    exact ⟨5, by norm_num, u, hnF u hu, 4, (honest_sent (List.mem_toFinset.mp hu)).2⟩
  · simp only [List.mem_map, Prod.mk.injEq] at hx
    obtain ⟨_, _, -, rfl⟩ := hx
    exact Or.inl ⟨b, rfl, hb⟩
  · simp at hx

/-! ### The computed run -/

/-- Computed facts of the run for the readings `epochStart` and `mixed`:
* nobody has committed in slot 2 by the end of epoch 1 (round 66), although the leader of that
  epoch (node `0`) is honest;
* every honest node has committed in slot 1 before slot 2 starts (round 44);
* every honest node holds the commit-proof `thsig(C_{2,2}(false))` at round 88. -/
def runFacts (pol : Skip) : Bool :=
  honest6.all fun u =>
    !(committedIn (held (exec P6 pol scX 66 u) 66) 2) &&
    committedIn (held (exec P6 pol scX 44 u) 44) 1 &&
    (held (exec P6 pol scX 88 u) 88).contains (.cproof 2 2 false)

set_option maxRecDepth 100000 in
lemma runFacts_epochStart : runFacts .epochStart = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma runFacts_mixed : runFacts .mixed = true := by decide +kernel

/-- For the literal reading (`everyStep`): node `3` stops after committing and never answers;
nodes `0, 1, 2` have not committed in slot 1 by the end of epoch 1 (round 22), whose leader
(node `0`) is honest. -/
def runFactsLiteral : Bool :=
  [0, 1, 2].all fun (u : Fin 6) => !(committedIn (held (exec P6 .everyStep scX 22 u) 22) 1)

set_option maxRecDepth 100000 in
lemma runFactsLiteral_true : runFactsLiteral = true := by decide +kernel

/-! ### The statements -/

/-- The statement of Lemma 3 of [WXMRS23] for a run: if the leader `L_i` of epoch `i` of slot `k`
is honest, all honest nodes commit (in slot `k`) by the end of epoch `i`. -/
def Lemma3Claim {n : ℕ} [NeZero n] {V : Type} [DecidableEq V] (P : Params n V) (pol : Skip)
    (sc : Scenario n V) : Prop :=
  ∀ k, 1 ≤ k → ∀ i, i < P.f + 2 → leader P k i ∉ sc.F → ∀ u, u ∉ sc.F →
    committedIn (held (exec P pol sc (roundOf P k (i + 1) 0) u) (roundOf P k (i + 1) 0)) k = true

/-- **Lemma 3 of [WXMRS23] is false**, for every reading of the skip condition: in a run with
`n = 6`, `f = 2`, `ε = 1/6`, an expander `G_ε`, at most `f` Byzantine nodes and an
unforgeability-respecting adversary, an honest leader's epoch does not make all honest nodes
commit. -/
theorem not_lemma3 (pol : Skip) :
    IsExpander P6.G (2 * (1 / 6)) (1 - 2 * (1 / 6)) ∧ ((P6.f : ℕ) : ℝ) ≤ (1 / 2 - 1 / 6) * 6 ∧
    scX.F.card ≤ P6.f ∧ scX.AdvValid P6 pol ∧ ¬ Lemma3Claim P6 pol scX := by
  refine ⟨isExpander_K6, f_le, card_F, advValid pol, fun h => ?_⟩
  cases pol
  · have h' := h 2 (by norm_num) 1 (by decide) (by decide) 0 (by decide)
    have := runFacts_epochStart
    simp only [runFacts, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at this
    have h0 := (this 0 (by decide)).1.1
    rw [show roundOf P6 2 (1 + 1) 0 = 66 by decide] at h'
    rw [h'] at h0; exact Bool.noConfusion h0
  · have h' := h 1 le_rfl 1 (by decide) (by decide) 0 (by decide)
    have := runFactsLiteral_true
    simp only [runFactsLiteral, List.all_eq_true, Bool.not_eq_true'] at this
    have h0 := this 0 (by decide)
    rw [show roundOf P6 1 (1 + 1) 0 = 22 by decide] at h'
    rw [h'] at h0; exact Bool.noConfusion h0
  · have h' := h 2 (by norm_num) 1 (by decide) (by decide) 0 (by decide)
    have := runFacts_mixed
    simp only [runFacts, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at this
    have h0 := (this 0 (by decide)).1.1
    rw [show roundOf P6 2 (1 + 1) 0 = 66 by decide] at h'
    rw [h'] at h0; exact Bool.noConfusion h0

/-- The run satisfies all hypotheses of the consistency theorem `theorem1`. -/
theorem theorem1_applies (pol : Skip) :
    scX.AdvValid P6 pol ∧ scX.F.card ≤ P6.f ∧ Expands P6 ∧ 2 * P6.f < 6 :=
  ⟨advValid pol, card_F, expands.1, expands.2⟩

/-- **Validity (Definition 2) of Algorithm 4 fails** for the readings `epochStart` and `mixed` of
the skip condition. The sender `S₂ = 0` of slot 2 is honest and has input `true`; every honest node
has committed in slot 1 before slot 2 starts (so `bc₂` may be invoked by sequentiality); yet no
honest node ever commits `true` in slot 2. -/
theorem not_validity (pol : Skip) (hpol : pol = .epochStart ∨ pol = .mixed) :
    IsExpander P6.G (2 * (1 / 6)) (1 - 2 * (1 / 6)) ∧ ((P6.f : ℕ) : ℝ) ≤ (1 / 2 - 1 / 6) * 6 ∧
    scX.F.card ≤ P6.f ∧ scX.AdvValid P6 pol ∧
    P6.sender 2 ∉ scX.F ∧ scX.inp (P6.sender 2) 2 = true ∧
    (∀ u, u ∉ scX.F → committedIn (held (exec P6 pol scX (roundOf P6 2 0 0) u)
      (roundOf P6 2 0 0)) 1 = true) ∧
    ∀ u, u ∉ scX.F → ¬ Commits P6 pol scX u 2 true := by
  have hf : runFacts pol = true := by
    rcases hpol with rfl | rfl
    · exact runFacts_epochStart
    · exact runFacts_mixed
  simp only [runFacts, List.all_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_iff_mem] at hf
  refine ⟨isExpander_K6, f_le, card_F, advValid pol, by decide, rfl, fun u hu => ?_,
    fun u hu hc => ?_⟩
  · rw [show roundOf P6 2 0 0 = 44 by decide]
    exact (hf u (not_mem_F.mp hu)).1.2
  · have hfalse : Commits P6 pol scX u 2 false := ⟨88, 2, (hf u (not_mem_F.mp hu)).2⟩
    obtain ⟨h1, h2, h3, h4⟩ := theorem1_applies pol
    exact Bool.noConfusion (theorem1 h1 h2 h3 h4 hu hu hc hfalse)

end Podc.AmortizedByzantineBroadcast.Counterexample
