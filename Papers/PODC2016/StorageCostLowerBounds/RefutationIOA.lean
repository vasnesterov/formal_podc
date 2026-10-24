import Papers.PODC2016.StorageCostLowerBounds.Refutation
import Papers.PODC2016.StorageCostLowerBounds.StreamLive

/-!
# The storage bounds are false also in the I/O-automaton reading

The relay algorithm of `Relay.lean` lets a server receive a message and send two in one atomic
step. In the paper's I/O-automaton model each send is a separate output action, so a server must
keep its pending outputs in its state. `Stream.IOASends` formalizes this restriction (an input
step of a server sends nothing, a spontaneous step at most one message).

The streaming relay (`Stream.lean`) satisfies it and is atomic, live and gossip-free with **36
states per server**, independently of `|V|`. For `n = 5`, `f = 2` and `V = Fin 16 → Bool`
(`|V| = 2^16`) it violates all six bounds, so they are false even restricted to such algorithms.
-/

namespace Podc.StorageCost

open Cslib.ChannelFailures Cslib.SharedMemory

/-- Theorem 4.1 restricted to I/O-automaton-style algorithms. -/
def Theorem41IOA : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    Stream.IOASends A → 2 ≤ f → f < n → IsRegular A → Live A f → NoGossip A → StateBound A S →
    ∀ 𝒩 : Finset (Fin n), 𝒩.card = n - f →
      Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) - Real.logb 2 (n - f : ℕ) ≤
        ∑ i ∈ 𝒩, Real.logb 2 (S i).card + ⨆ i : 𝒩, Real.logb 2 (S i).card

/-- Corollary 4.2 restricted to I/O-automaton-style algorithms. -/
def Corollary42IOA : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    Stream.IOASends A → 2 ≤ f → f < n → IsRegular A → Live A f → NoGossip A → StateBound A S →
      (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 1) ≤ maxStorage S ∧
      n * (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 1) ≤ totalStorage S

/-- Theorem 5.1 restricted to I/O-automaton-style algorithms. -/
def Theorem51IOA : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    Stream.IOASends A → f < n → IsRegular A → Live A f → StateBound A S →
    ∀ 𝒩 : Finset (Fin n), 𝒩.card = n - f →
      Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          2 * Real.logb 2 (n - f : ℕ) ≤
        2 * (⨆ i : 𝒩, Real.logb 2 (S i).card) + ∑ i ∈ 𝒩, Real.logb 2 (S i).card

/-- Theorem B.1 restricted to I/O-automaton-style algorithms. -/
def TheoremB1IOA : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    Stream.IOASends A → 1 ≤ f → f < n → IsRegular A → Live A f → StateBound A S →
    ∀ 𝒩 : Finset (Fin n), 𝒩.card = n - f →
      Real.logb 2 (Fintype.card V) ≤ ∑ i ∈ 𝒩, Real.logb 2 (S i).card

/-- Corollary 5.2 restricted to I/O-automaton-style algorithms. -/
def Corollary52IOA : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    Stream.IOASends A → f < n → IsRegular A → Live A f → StateBound A S →
      (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          2 * Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 2) ≤ maxStorage S ∧
      n * (Real.logb 2 (Fintype.card V) + Real.logb 2 (Fintype.card V - 1) -
          2 * Real.logb 2 (n - f : ℕ)) / ((n - f : ℕ) + 2) ≤ totalStorage S

/-- Corollary B.2 restricted to I/O-automaton-style algorithms. -/
def CorollaryB2IOA : Prop :=
  ∀ (n f : ℕ) (V : Type) [Fintype V] (v₀ : V) (M L : Type)
    (A : Algorithm (Node n) (register V v₀) M L) (S : Fin n → Finset L),
    Stream.IOASends A → 1 ≤ f → f < n → IsRegular A → Live A f → StateBound A S →
      Real.logb 2 (Fintype.card V) / (n - f : ℕ) ≤ maxStorage S ∧
      n * Real.logb 2 (Fintype.card V) / (n - f : ℕ) ≤ totalStorage S

/-- The streaming relay: atomic, regular, live, gossip-free, I/O-automaton style, 36 server
states (any `2 f < n`, any `B > 0`). -/
theorem stream_counterexample {n f B : ℕ} (hf : 2 * f < n) (hB : 0 < B) :
    IsAtomic (Stream.alg (n := n) (B := B) (n - f)) ∧
    IsRegular (Stream.alg (n := n) (B := B) (n - f)) ∧
    Live (Stream.alg (n := n) (B := B) (n - f)) f ∧
    NoGossip (Stream.alg (n := n) (B := B) (n - f)) ∧
    Stream.IOASends (Stream.alg (n := n) (B := B) (n - f)) ∧
    StateBound (Stream.alg (n := n) (B := B) (n - f)) Stream.srvStates ∧
    ∀ i, (Stream.srvStates (n := n) (B := B) i).card = 36 :=
  ⟨Stream.isAtomic _ (by omega) (by omega) hB, Stream.isRegular _ (by omega) (by omega) hB,
    Stream.isLive hf hB, Stream.noGossip _, Stream.ioaSends _, Stream.stateBound _,
    Stream.card_srvStates⟩

/-! ### The instance `n = 5`, `f = 2`, `B = 16` -/

private abbrev A₁ := Stream.alg (n := 5) (B := 16) (5 - 2)

private lemma hyps₁ : IsRegular A₁ ∧ Live A₁ 2 ∧ NoGossip A₁ ∧ Stream.IOASends A₁ ∧
    StateBound A₁ Stream.srvStates ∧ ∀ i, (Stream.srvStates (n := 5) (B := 16) i).card = 36 :=
  let h := stream_counterexample (n := 5) (f := 2) (B := 16) (by norm_num) (by norm_num)
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private lemma cardV : (Fintype.card (Stream.Val 16) : ℝ) = 65536 := by
  simp [Stream.Val]

private lemma lb (a b : ℝ) (ha : 0 < a) (h : a < b) : Real.logb 2 a < Real.logb 2 b :=
  Real.logb_lt_logb (by norm_num) ha h

private lemma logb16 : Real.logb 2 (65536 : ℝ) = 16 := by
  rw [show (65536 : ℝ) = 2 ^ (16 : ℝ) by norm_num]
  exact Real.logb_rpow (by norm_num) (by norm_num)

/-- `4 log 36 + log 3 < log 65536 + log 65535`. -/
private lemma num41 : 4 * Real.logb 2 36 + Real.logb 2 3 <
    Real.logb 2 65536 + Real.logb 2 65535 := by
  have e1 : Real.logb 2 ((36 : ℝ) ^ 4 * 3) = 4 * Real.logb 2 36 + Real.logb 2 3 := by
    rw [Real.logb_mul (by norm_num) (by norm_num), Real.logb_pow]; push_cast; ring
  have e2 : Real.logb 2 ((65536 : ℝ) * 65535) = Real.logb 2 65536 + Real.logb 2 65535 :=
    Real.logb_mul (by norm_num) (by norm_num)
  rw [← e1, ← e2]; exact lb _ _ (by norm_num) (by norm_num)

/-- `5 log 36 + 2 log 3 < log 65536 + log 65535`. -/
private lemma num51 : 5 * Real.logb 2 36 + 2 * Real.logb 2 3 <
    Real.logb 2 65536 + Real.logb 2 65535 := by
  have e1 : Real.logb 2 ((36 : ℝ) ^ 5 * 3 ^ 2) = 5 * Real.logb 2 36 + 2 * Real.logb 2 3 := by
    rw [Real.logb_mul (by norm_num) (by norm_num), Real.logb_pow, Real.logb_pow]; push_cast; ring
  have e2 : Real.logb 2 ((65536 : ℝ) * 65535) = Real.logb 2 65536 + Real.logb 2 65535 :=
    Real.logb_mul (by norm_num) (by norm_num)
  rw [← e1, ← e2]; exact lb _ _ (by norm_num) (by norm_num)

/-- `3 log 36 < 16`. -/
private lemma numB1 : 3 * Real.logb 2 36 < 16 := by
  have e1 : Real.logb 2 ((36 : ℝ) ^ 3) = 3 * Real.logb 2 36 := by
    rw [Real.logb_pow]; push_cast; ring
  rw [← e1, ← logb16]; exact lb _ _ (by norm_num) (by norm_num)

private lemma sum3 (S : Fin 5 → Finset (Stream.LSt 5 16)) (h : ∀ i, (S i).card = 36) :
    ∑ i ∈ ({0, 1, 2} : Finset (Fin 5)), Real.logb 2 (S i).card = 3 * Real.logb 2 36 := by
  simp [h]

private lemma sup3 (S : Fin 5 → Finset (Stream.LSt 5 16)) (h : ∀ i, (S i).card = 36) :
    (⨆ i : ({0, 1, 2} : Finset (Fin 5)), Real.logb 2 (S i).card) = Real.logb 2 36 := by
  have : Nonempty ({0, 1, 2} : Finset (Fin 5)) := ⟨⟨0, by simp⟩⟩
  simp [h]

private lemma maxS (S : Fin 5 → Finset (Stream.LSt 5 16)) (h : ∀ i, (S i).card = 36) :
    maxStorage S = Real.logb 2 36 := by
  simp [maxStorage, h]

private lemma totS (S : Fin 5 → Finset (Stream.LSt 5 16)) (h : ∀ i, (S i).card = 36) :
    totalStorage S = 5 * Real.logb 2 36 := by
  simp [totalStorage, h]

private lemma l3 : (0 : ℝ) < Real.logb 2 3 := Real.logb_pos (by norm_num) (by norm_num)

/-- **Theorem 4.1 is false even for I/O-automaton-style algorithms.** -/
theorem not_theorem41_ioa : ¬ Theorem41IOA := by
  intro h
  obtain ⟨hR, hL, hG, hIO, hS, hc⟩ := hyps₁
  have := h 5 2 (Stream.Val 16) (fun _ => false) _ _ A₁ _ hIO le_rfl (by norm_num) hR hL hG hS
    ({0, 1, 2} : Finset (Fin 5)) (by decide)
  rw [sum3 _ hc, sup3 _ hc, cardV] at this
  norm_num at this
  linarith [num41]

/-- **Corollary 4.2 is false even for I/O-automaton-style algorithms.** -/
theorem not_corollary42_ioa : ¬ Corollary42IOA := by
  intro h
  obtain ⟨hR, hL, hG, hIO, hS, hc⟩ := hyps₁
  have := (h 5 2 (Stream.Val 16) (fun _ => false) _ _ A₁ _ hIO le_rfl (by norm_num) hR hL hG
    hS).1
  rw [maxS _ hc, cardV] at this
  norm_num at this
  rw [div_le_iff₀ (by norm_num)] at this
  linarith [num41]

/-- **Theorem 5.1 is false even for I/O-automaton-style algorithms.** -/
theorem not_theorem51_ioa : ¬ Theorem51IOA := by
  intro h
  obtain ⟨hR, hL, -, hIO, hS, hc⟩ := hyps₁
  have := h 5 2 (Stream.Val 16) (fun _ => false) _ _ A₁ _ hIO (by norm_num) hR hL hS
    ({0, 1, 2} : Finset (Fin 5)) (by decide)
  rw [sum3 _ hc, sup3 _ hc, cardV] at this
  norm_num at this
  linarith [num51]

/-- **Theorem B.1 is false even for I/O-automaton-style algorithms.** -/
theorem not_theoremB1_ioa : ¬ TheoremB1IOA := by
  intro h
  obtain ⟨hR, hL, -, hIO, hS, hc⟩ := hyps₁
  have := h 5 2 (Stream.Val 16) (fun _ => false) _ _ A₁ _ hIO (by norm_num) (by norm_num) hR hL
    hS ({0, 1, 2} : Finset (Fin 5)) (by decide)
  rw [sum3 _ hc, cardV, logb16] at this
  linarith [numB1]

/-- **Corollary 5.2 is false even for I/O-automaton-style algorithms.** -/
theorem not_corollary52_ioa : ¬ Corollary52IOA := by
  intro h
  obtain ⟨hR, hL, -, hIO, hS, hc⟩ := hyps₁
  have := (h 5 2 (Stream.Val 16) (fun _ => false) _ _ A₁ _ hIO (by norm_num) hR hL hS).1
  rw [maxS _ hc, cardV] at this
  norm_num at this
  rw [div_le_iff₀ (by norm_num)] at this
  linarith [num51]

/-- **Corollary B.2 is false even for I/O-automaton-style algorithms.** -/
theorem not_corollaryB2_ioa : ¬ CorollaryB2IOA := by
  intro h
  obtain ⟨hR, hL, -, hIO, hS, hc⟩ := hyps₁
  have := (h 5 2 (Stream.Val 16) (fun _ => false) _ _ A₁ _ hIO (by norm_num) (by norm_num) hR hL
    hS).1
  rw [maxS _ hc, cardV, logb16] at this
  norm_num at this
  rw [div_le_iff₀ (by norm_num)] at this
  linarith [numB1]

end Podc.StorageCost
