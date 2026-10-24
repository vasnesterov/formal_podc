import Papers.PODC2016.StorageCostLowerBounds.RelayLive

/-!
# The paper's storage lower bounds are false (FIFO channels)

The statements of Theorem 4.1, Corollary 4.2, Theorem 5.1, Corollary 5.2, Theorem B.1 and
Corollary B.2, transcribed literally (storage cost of server `i` = `log₂ |S i|`), and refuted by
the relay algorithm (`Relay.lean`): an atomic, live SWSR register emulation without gossip in which
every server has a **single** state, so every storage cost is `0`.

The counterexample instance: `n = 5` servers, `f = 2`, values `Fin 4`.
-/

namespace Podc.StorageCost

open Cslib.ChannelFailures Cslib.SharedMemory

/-- **Theorem 4.1** (as stated): for a regular SWSR emulation without gossip, live with `f ≥ 2`
server failures, and every set `𝒩` of `n - f` servers,
`∑_{𝒩} log|S_i| + max_{𝒩} log|S_i| ≥ log|V| + log(|V| - 1) - log(n - f)`. -/
def Theorem41 : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    2 ≤ f → f < n → IsRegular A → Live A f → NoGossip A → StateBound A S →
    ∀ 𝒩 : Finset (Fin n), 𝒩.card = n - f →
      Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) - Real.logb 2 (n - f : ℕ) ≤
        ∑ i ∈ 𝒩, Real.logb 2 (S i).card + ⨆ i : 𝒩, Real.logb 2 (S i).card

/-- **Corollary 4.2** (as stated). -/
def Corollary42 : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    2 ≤ f → f < n → IsRegular A → Live A f → NoGossip A → StateBound A S →
      (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 1) ≤ maxStorage S ∧
      n * (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 1) ≤ totalStorage S

/-- **Theorem 5.1** (as stated; gossip allowed, any `f`):
`2 max_{𝒩} log|S_i| + ∑_{𝒩} log|S_i| ≥ log|V| + log(|V| - 1) - 2 log(n - f)`. -/
def Theorem51 : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    f < n → IsRegular A → Live A f → StateBound A S →
    ∀ 𝒩 : Finset (Fin n), 𝒩.card = n - f →
      Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          2 * Real.logb 2 (n - f : ℕ) ≤
        2 * (⨆ i : 𝒩, Real.logb 2 (S i).card) + ∑ i ∈ 𝒩, Real.logb 2 (S i).card

/-- **Corollary 5.2** (as stated). -/
def Corollary52 : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    f < n → IsRegular A → Live A f → StateBound A S →
      (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          2 * Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 2) ≤ maxStorage S ∧
      n * (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          2 * Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 2) ≤ totalStorage S

/-- **Theorem B.1** (as stated; the Singleton-type bound, `f ≥ 1`):
`∑_{𝒩} log|S_i| ≥ log|V|`. -/
def TheoremB1 : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    1 ≤ f → f < n → IsRegular A → Live A f → StateBound A S →
    ∀ 𝒩 : Finset (Fin n), 𝒩.card = n - f →
      Real.logb 2 (Fintype.card V) ≤ ∑ i ∈ 𝒩, Real.logb 2 (S i).card

/-- **Corollary B.2** (as stated). -/
def CorollaryB2 : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    1 ≤ f → f < n → IsRegular A → Live A f → StateBound A S →
      Real.logb 2 (Fintype.card V) / (n - f : ℕ) ≤ maxStorage S ∧
      n * Real.logb 2 (Fintype.card V) / (n - f : ℕ) ≤ totalStorage S

/-! ### The counterexample -/

/-- **The relay algorithm** (any `n`, `f` with `2 f < n`, any value set): an atomic (hence
regular), live SWSR register emulation without gossip whose servers have a single state. -/
theorem relay_counterexample {n f : ℕ} (hf : 2 * f < n) {V : Type} (v₀ : V) :
    IsAtomic (Relay.relay v₀ (n - f) : Algorithm (Node n) (register V v₀) _ _) ∧
    IsRegular (Relay.relay v₀ (n - f) : Algorithm (Node n) (register V v₀) _ _) ∧
    Live (Relay.relay v₀ (n - f) : Algorithm (Node n) (register V v₀) _ _) f ∧
    NoGossip (Relay.relay v₀ (n - f) : Algorithm (Node n) (register V v₀) _ _) ∧
    StateBound (Relay.relay v₀ (n - f) : Algorithm (Node n) (register V v₀) _ _)
      (fun _ => {Relay.lInit v₀}) :=
  ⟨Relay.isAtomic _ (by omega) (by omega), Relay.isRegular _ (by omega) (by omega),
    Relay.isLive hf, Relay.noGossip _ _, Relay.stateBound _ _⟩

private lemma logb_one_card {L : Type} (x : L) : Real.logb 2 (({x} : Finset L).card : ℝ) = 0 := by
  simp

private lemma iSup_zero {ι : Type} (S : ι → ℝ) (h : ∀ i, S i = 0) : (⨆ i, S i) = 0 := by
  simp [h]

private lemma logb_four : Real.logb 2 ((Fintype.card (Fin 4) : ℝ)) = 2 := by
  rw [Fintype.card_fin, show ((4 : ℕ) : ℝ) = 2 ^ (2 : ℝ) by norm_num]
  exact Real.logb_rpow (by norm_num) (by norm_num)

private lemma logb_three_pos : 0 < Real.logb 2 (3 : ℝ) :=
  Real.logb_pos (by norm_num) (by norm_num)

private lemma logb_three_lt : Real.logb 2 (3 : ℝ) < 2 := by
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]; norm_num

private lemma card_fin4_sub : ((Fintype.card (Fin 4) : ℝ) - 1) = 3 := by
  simp; norm_num

private lemma cast_five_two : (((5 - 2 : ℕ)) : ℝ) = 3 := by norm_num

/-- The common instance: `n = 5`, `f = 2`, `V = Fin 4`. -/
private abbrev A₀ := (Relay.relay (0 : Fin 4) (5 - 2) : Algorithm (Node 5) (register (Fin 4) 0) _ _)

private lemma hyps₀ : IsAtomic A₀ ∧ IsRegular A₀ ∧ Live A₀ 2 ∧ NoGossip A₀ ∧
    StateBound A₀ (fun _ => {Relay.lInit (0 : Fin 4)}) :=
  relay_counterexample (n := 5) (f := 2) (by norm_num) (0 : Fin 4)

/-- **Theorem 4.1 is false.** -/
theorem not_theorem41 : ¬ Theorem41 := by
  intro h
  obtain ⟨-, hR, hL, hG, hS⟩ := hyps₀
  have := h 5 2 (Fin 4) 0 _ _ A₀ _ le_rfl (by norm_num) hR hL hG hS ({0, 1, 2} : Finset (Fin 5)) (by decide)
  rw [logb_four, card_fin4_sub, cast_five_two] at this
  simp only [logb_one_card, Finset.sum_const_zero, Real.iSup_const_zero, zero_add] at this
  linarith

/-- **Corollary 4.2 is false.** -/
theorem not_corollary42 : ¬ Corollary42 := by
  intro h
  obtain ⟨-, hR, hL, hG, hS⟩ := hyps₀
  have := (h 5 2 (Fin 4) 0 _ _ A₀ _ le_rfl (by norm_num) hR hL hG hS).1
  rw [logb_four, card_fin4_sub, cast_five_two] at this
  simp only [maxStorage, logb_one_card, Real.iSup_const_zero] at this
  have h4 : (0 : ℝ) < (2 + Real.logb 2 3 - Real.logb 2 3) / (3 + 1) := by
    apply div_pos <;> linarith
  linarith

/-- **Theorem 5.1 is false.** -/
theorem not_theorem51 : ¬ Theorem51 := by
  intro h
  obtain ⟨-, hR, hL, -, hS⟩ := hyps₀
  have := h 5 2 (Fin 4) 0 _ _ A₀ _ (by norm_num) hR hL hS ({0, 1, 2} : Finset (Fin 5)) (by decide)
  rw [logb_four, card_fin4_sub, cast_five_two] at this
  simp only [logb_one_card, Finset.sum_const_zero, Real.iSup_const_zero, mul_zero,
    add_zero] at this
  linarith [logb_three_lt]

/-- **Corollary 5.2 is false.** -/
theorem not_corollary52 : ¬ Corollary52 := by
  intro h
  obtain ⟨-, hR, hL, -, hS⟩ := hyps₀
  have := (h 5 2 (Fin 4) 0 _ _ A₀ _ (by norm_num) hR hL hS).1
  rw [logb_four, card_fin4_sub, cast_five_two] at this
  simp only [maxStorage, logb_one_card, Real.iSup_const_zero] at this
  have h4 : (0 : ℝ) < (2 + Real.logb 2 3 - 2 * Real.logb 2 3) / (3 + 2) := by
    apply div_pos <;> linarith [logb_three_lt]
  linarith

/-- **Theorem B.1 is false.** -/
theorem not_theoremB1 : ¬ TheoremB1 := by
  intro h
  obtain ⟨-, hR, hL, -, hS⟩ := hyps₀
  have := h 5 2 (Fin 4) 0 _ _ A₀ _ (by norm_num) (by norm_num) hR hL hS ({0, 1, 2} : Finset (Fin 5)) (by decide)
  rw [logb_four] at this
  simp only [logb_one_card, Finset.sum_const_zero] at this
  linarith

/-- **Corollary B.2 is false.** -/
theorem not_corollaryB2 : ¬ CorollaryB2 := by
  intro h
  obtain ⟨-, hR, hL, -, hS⟩ := hyps₀
  have := (h 5 2 (Fin 4) 0 _ _ A₀ _ (by norm_num) (by norm_num) hR hL hS).1
  rw [logb_four, cast_five_two] at this
  simp only [maxStorage, logb_one_card, Real.iSup_const_zero] at this
  linarith

/-- The relay algorithm violates exactly the hidden assumption of the proofs: a server sends to
the reader although the reader has not taken any step. -/
theorem relay_not_readerQuiet : ¬ ReaderQuiet A₀ := by
  intro h
  have := h [.invoke .wr (RWOp.write 1), .deliver .wr (.srv 0)]
    (by
      intro e he p o hpo
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · simp only [Event.invoke.injEq] at hpo; obtain ⟨rfl, rfl⟩ := hpo
        exact Or.inl ⟨rfl, 1, rfl⟩
      · cases hpo)
    (by intro e he; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> simp) 0
  simp [A₀, Relay.relay, Relay.handle, Algorithm.run, Algorithm.step, Algorithm.initCfg,
    Config.apply, Config.pop, Relay.lInit, msgsTo, Relay.toAll, List.finRange] at this

end Podc.StorageCost
