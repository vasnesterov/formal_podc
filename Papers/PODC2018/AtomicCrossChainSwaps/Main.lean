import Papers.PODC2018.AtomicCrossChainSwaps.Counterexamples

/-!
# Main results: the repaired protocol is uniform and atomic

* `Setting.idleSched`: for every coalition there is an admissible schedule in which the coalition
  does nothing (non-vacuity of `ValidSched`; also the "withhold everything" deviation of Lemma 3.4).
* `Setting.game_uniform`: for a strongly connected digraph, a feedback vertex set of leaders and
  base timeout `B ≥ diam D + 1`, the repaired protocol is uniform (Definition 3.1).
* `Setting.game_atomic`: hence atomic (Definition 3.2) by Lemma 3.3 — the paper's main positive
  claim, for the repaired protocol.
-/

namespace AtomicSwap

namespace Setting

variable {V : Type*} [DecidableEq V] [Fintype V] (P : Setting V) (C : Finset V)

/-- A state-dependent strategy produces a schedule. -/
noncomputable def runStrat (σ : ℕ → St V → Moves V) : ℕ → St V
  | 0 => St.init
  | t + 1 => P.step C t (runStrat σ t) (σ t (runStrat σ t))

lemma run_strat (σ : ℕ → St V → Moves V) (t : ℕ) :
    P.run C (fun t => σ t (P.runStrat C σ t)) t = P.runStrat C σ t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [run, runStrat, ih]

open Classical in
/-- The idle strategy: the coalition does nothing; conforming parties take their first key from
any unlocked leaving arc. -/
noncomputable def idleStrat : ℕ → St V → Moves V := fun _ s =>
  ⟨[], [], fun v ℓ => if h : ∃ w, P.D.Adj v w ∧ (s.unl v w ℓ).isSome then h.choose else v⟩

/-- The idle schedule of coalition `C`. -/
noncomputable def idleSched : ℕ → Moves V := fun t => P.idleStrat t (P.runStrat C P.idleStrat t)

theorem idleSched_valid : P.ValidSched C (P.idleSched C) := by
  intro t
  unfold idleSched
  rw [P.run_strat C P.idleStrat t]
  refine ⟨by simp [idleStrat], by simp [idleStrat], ?_⟩
  intro v ℓ _ _ _ _ h
  simp only [idleStrat, dite_eq_left h]
  exact h.choose_spec

/-- Under the idle schedule, no arc leaving the coalition ever gets a contract. -/
theorem idleSched_no_con {t : ℕ} {u v : V} (hu : u ∈ C) : (P.run C (P.idleSched C) t).con u v = none := by
  cases h : (P.run C (P.idleSched C) t).con u v with
  | none => rfl
  | some c =>
    obtain ⟨-, -, hp | ⟨-, hm⟩⟩ := P.con_origin C _ h
    · exact absurd hu hp.1
    · simp [idleSched, idleStrat] at hm

/-- Coalitions can withhold their assets (the modelling assumption of Lemma 3.4) — provided there
is at least one hashlock. -/
theorem game_canAbstain (hL : P.L.Nonempty) : P.game.CanAbstain := by
  intro S
  classical
  refine ⟨P.Final S.toFinset (P.idleSched S.toFinset),
    ⟨S.toFinset, _, by simp, P.idleSched_valid _, rfl⟩, ?_⟩
  rintro u v ⟨-, hu, -⟩ ⟨t, ht⟩
  obtain ⟨ℓ, hℓ⟩ := hL
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ht ℓ hℓ)
  obtain ⟨c, -, hc⟩ := P.unl_con _ _ (τ := x.1) (p := x.2) (by simpa using hx)
  rw [P.idleSched_no_con _ (by simpa using hu)] at hc
  cases hc

/-- **Definition 3.1 for the repaired protocol.** For a strongly connected swap digraph, a feedback
vertex set of leaders and hashkey timeouts `(diam D + 1 + |p|)Δ`, the repaired protocol is
uniform: if all conform everybody gets Deal, and whatever coalition deviates no conforming party
ends Underwater. -/
theorem game_uniform [Nontrivial V] (hfix : P.fixed = true) (hD : StronglyConnected P.D)
    (hL : IsFVS P.D (P.L : Set V)) (hB : diam P.D + 1 ≤ P.B) : P.game.Uniform := by
  refine ⟨?_, ?_⟩
  · rintro T ⟨C, sch, hC, hsch, rfl⟩ v
    have hC' : C = ∅ := by simpa using hC
    subst hC'
    have hall : ∀ a b, P.D.Adj a b → P.Final ∅ sch a b :=
      fun a b h => ⟨_, theorem_4_7 hfix hsch hD hL hB h⟩
    exact ⟨fun a b h => hall a b h.1, fun a b h => hall a b h.1⟩
  · rintro S T ⟨C, sch, rfl, hsch, rfl⟩ v hv
    exact safety hfix hsch (by simpa using hv)

/-- **The repaired protocol is atomic** (Definition 3.2; Lemma 3.3 + Theorems 4.7 and 4.9). -/
theorem game_atomic [Nontrivial V] (hfix : P.fixed = true) (hD : StronglyConnected P.D)
    (hL : IsFVS P.D (P.L : Set V)) (hB : diam P.D + 1 ≤ P.B) : P.game.Atomic :=
  SwapGame.atomic_of_uniform_of_stronglyConnected hD (P.game_uniform hfix hD hL hB)

/-- **Theorem 4.12 (for this protocol, either variant).** If the leaders do not form a feedback
vertex set, then even when all parties conform some arc is never triggered: no contract is ever
published on an arc of a cycle of followers (each of them waits for the previous one, Lemma 4.11).
-/
theorem not_live_of_not_isFVS (hL : P.L.Nonempty) (hnot : ¬ IsFVS P.D (P.L : Set V))
    {sch : ℕ → Moves V} : ∃ u w, P.D.Adj u w ∧ ¬ P.Final ∅ sch u w := by
  unfold IsFVS at hnot
  push Not at hnot
  obtain ⟨v, hv⟩ := hnot
  obtain ⟨b, hvb, hbv⟩ := Relation.TransGen.tail'_iff.mp hv
  have hvb' : Relation.TransGen (FollowerAdj P.D (P.L : Set V)) v b := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp hvb with h | h
    · subst h; exact hv
    · exact h
  refine ⟨b, v, hbv.1, ?_⟩
  rintro ⟨t, ht⟩
  have hcon : (P.run ∅ sch t).con b v = none := by
    refine no_contract_on_follower_cycle (D := P.D) (L := (P.L : Set V))
      (fun u w => (P.run ∅ sch t).con u w) ?_ b v hbv hvb'
    intro u w c hu hc x hx
    obtain ⟨-, -, hall⟩ := P.con_conforming ∅ sch hc (by simp)
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp (hall (by simpa using hu) x hx)
    have h1 := (P.con_le ∅ sch hc).2
    have h2 := (P.con_le ∅ sch hc').2
    have h3 := (P.con_le ∅ sch hc).1
    exact ⟨c', by omega, P.con_mono ∅ sch (by omega) hc'⟩
  obtain ⟨ℓ, hℓ⟩ := hL
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (ht ℓ hℓ)
  obtain ⟨c, -, hc⟩ := P.unl_con ∅ sch (τ := x.1) (p := x.2) (by simpa using hx)
  rw [hcon] at hc
  cases hc

/-- Non-vacuity: e.g. the three-party swap of §1 satisfies all hypotheses of `game_atomic`. -/
example : (⟨cyc3, {0}, 4, true, false⟩ : Setting (Fin 3)).game.Atomic := by
  apply game_atomic
  · rfl
  · intro u v
    -- the 3-cycle is strongly connected
    have step : ∀ a : Fin 3, Reach cyc3 a (a + 1) := fun a => Relation.ReflTransGen.single rfl
    have : v = u + (v - u) := by abel
    rw [this]
    generalize v - u = k
    fin_cases k
    · simp; exact Relation.ReflTransGen.refl
    · exact step u
    · exact (step u).trans (by
        have := step (u + 1); simp only [show u + 1 + 1 = u + 2 by abel] at this; exact this)
  · intro v hv
    -- every closed walk among the followers {1, 2} would need the arc 2 → 0 or 0 → 1
    have hstep : ∀ a b : Fin 3, FollowerAdj cyc3 ((({0} : Finset (Fin 3)) : Set (Fin 3))) a b →
        a.val < b.val := by
      unfold FollowerAdj cyc3
      simp only [Digraph.deleteVerts_adj, Finset.coe_singleton, Set.mem_singleton_iff]; decide
    have key : ∀ a b, Relation.TransGen (FollowerAdj cyc3 ({0} : Finset (Fin 3))) a b →
        a.val < b.val := by
      intro a b h
      induction h with
      | single h => exact hstep _ _ h
      | tail _ h ih => exact ih.trans (hstep _ _ h)
    exact lt_irrefl _ (key v v hv)
  · rw [diam_cyc3]

end Setting

end AtomicSwap
