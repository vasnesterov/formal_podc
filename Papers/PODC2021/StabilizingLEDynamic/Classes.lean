import Papers.PODC2021.StabilizingLEDynamic.Model
import Mathlib.Data.Nat.ModEq

/-!
# The hierarchy of the nine DG classes (Theorem 1)

Altisen, Devismes, Durand, Johnen, Petit, *On Implementing Stabilizing Leader Election with Weak
Assumptions on Network Dynamics*: Theorem 1 of the journal version (HAL hal-03346225),
Theorem 2.1 of the PODC 2021 version.

* `Kind` and `Timeliness` are ordered: `all ≤ src`, `all ≤ snk` (`src`, `snk` incomparable) and
  `bounded ≤ quasi ≤ recur`.
* `J_mono`: the inclusions of Figure 2, `J k τ Δ V ⊆ J k' τ' Δ V` whenever `k ≤ k'`, `τ ≤ τ'`.
* The witnesses of the paper's proof: the constant out-star `outStar` (`G(1S)`), the constant
  in-star `inStar` (`G(1T)`), `G2` (complete graph at rounds `2^j`, empty otherwise) and `G3`
  (the ring edge number `j mod n` at round `2^j`, empty otherwise).
* `theorem_1`: for `Δ ≥ 1` and `|V| ≥ 3`, `J k τ Δ V ⊆ J k' τ' Δ V ↔ k ≤ k' ∧ τ ≤ τ'`.
* `theorem_1_classes`: Theorem 1 as stated in the paper, for classes of dynamic graphs over all
  (nonempty) vertex sets.
* The paper's proof works inside a fixed vertex set of `n > 1` vertices; for `n = 2` the per-`V`
  statement fails (`theorem_1_false_card_two`, `J_src_eq_snk_of_card_two`,
  `not_theorem_1_card_two`), so the proof needs `n ≥ 3` (a proof slip; the statement is true).

Rounds are 0-indexed: our round `t` is the paper's round `t + 1`, so "round `2^j`" of the paper is
our round `t` with `t + 1 = 2 ^ j` (`Pow2Round t`).
-/

namespace StabilizingLEDynamic

variable {ι : Type*}

/-! ### The orders on kinds and timeliness -/

namespace Kind

/-- `k ≤ k'` iff `k = all` or `k = k'`: "every vertex is a source" is the strongest requirement;
"a source" and "a sink" are incomparable. -/
instance : PartialOrder Kind where
  le a b := a = .all ∨ a = b
  le_refl a := Or.inr rfl
  le_trans a b c := by
    rintro (rfl | rfl) (rfl | rfl) <;> simp
  le_antisymm a b := by
    rintro (rfl | rfl) (h | h) <;> simp_all

theorem le_iff {k k' : Kind} : k ≤ k' ↔ k = .all ∨ k = k' := Iff.rfl

instance : DecidableRel (α := Kind) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a = .all ∨ a = b))

end Kind

namespace Timeliness

/-- Rank used to order timeliness: `bounded < quasi < recur`. -/
def rank : Timeliness → ℕ
  | .bounded => 0
  | .quasi => 1
  | .recur => 2

theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]

/-- `bounded ≤ quasi ≤ recur` (a stronger timeliness requirement is smaller). -/
instance : LinearOrder Timeliness := LinearOrder.lift' rank rank_injective

theorem le_iff {τ τ' : Timeliness} : τ ≤ τ' ↔ τ.rank ≤ τ'.rank := Iff.rfl

theorem le_recur (τ : Timeliness) : τ ≤ .recur := by
  rw [le_iff]; cases τ <;> simp [rank]

end Timeliness

/-! ### Monotonicity (Figure 2) -/

section Conn

variable {τ τ' : Timeliness} {Δ : ℕ} {G : DG ι} {p q : ι}

theorem Conn.refl (τ : Timeliness) (Δ : ℕ) (G : DG ι) (p : ι) : Conn τ Δ G p p := by
  cases τ with
  | recur => exact fun i => ⟨i, .refl _ _ _⟩
  | quasi => exact fun i => ⟨i, le_rfl, tdist_le_iff.mpr (.refl _ _ _)⟩
  | bounded => exact fun i => tdist_le_iff.mpr (.refl _ _ _)

theorem Conn.mono (h : Conn τ Δ G p q) (hτ : τ ≤ τ') : Conn τ' Δ G p q := by
  rw [Timeliness.le_iff] at hτ
  cases τ <;> cases τ' <;> simp only [Timeliness.rank] at hτ <;> try omega
  all_goals first
    | exact h
    | exact fun i => ⟨i, le_rfl, h i⟩
    | exact fun i => ⟨i + Δ, tdist_le_iff.mp (h i)⟩
    | exact fun i => (h i).elim fun j ⟨hj, hd⟩ => ⟨j + Δ, (tdist_le_iff.mp hd).mono_left hj⟩

end Conn

/-- **Figure 2** (inclusions of Theorem 1): `J k τ Δ V ⊆ J k' τ' Δ V` whenever `k ≤ k'` and
`τ ≤ τ'` (for `all ≤ src`/`all ≤ snk`, `V` must be nonempty). -/
theorem J_mono {V : Finset ι} (hV : V.Nonempty) {k k' : Kind} {τ τ' : Timeliness} {Δ : ℕ}
    (hk : k ≤ k') (hτ : τ ≤ τ') : J k τ Δ V ⊆ J k' τ' Δ V := by
  rintro G ⟨hdg, h⟩
  refine ⟨hdg, ?_⟩
  rcases Kind.le_iff.mp hk with rfl | rfl
  · obtain ⟨x, hx⟩ := hV
    cases k' with
    | src => exact ⟨x, hx, fun p hp => (h x hx p hp).mono hτ⟩
    | snk => exact ⟨x, hx, fun p hp => (h p hp x hx).mono hτ⟩
    | all => exact fun p hp q hq => (h p hp q hq).mono hτ
  · cases k with
    | src => obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs, fun p hp => (h p hp).mono hτ⟩
    | snk => obtain ⟨s, hs, h⟩ := h; exact ⟨s, hs, fun p hp => (h p hp).mono hτ⟩
    | all => exact fun p hp q hq => (h p hp q hq).mono hτ

/-- A DG without a `τ`-source is in no class of kind `src` or `all`. -/
theorem not_mem_J_of_no_source {V : Finset ι} {k : Kind} {τ : Timeliness} {Δ : ℕ} {G : DG ι}
    (hV : V.Nonempty) (hk : k ≠ .snk) (h : ∀ s ∈ V, ∃ p ∈ V, ¬ Conn τ Δ G s p) :
    G ∉ J k τ Δ V := by
  rintro ⟨-, hG⟩
  cases k with
  | src =>
    obtain ⟨s, hs, hG⟩ := hG
    obtain ⟨p, hp, hn⟩ := h s hs
    exact hn (hG p hp)
  | snk => exact hk rfl
  | all =>
    obtain ⟨s, hs⟩ := hV
    obtain ⟨p, hp, hn⟩ := h s hs
    exact hn (hG s hs p hp)

/-- A DG without a `τ`-sink is in no class of kind `snk` or `all`. -/
theorem not_mem_J_of_no_sink {V : Finset ι} {k : Kind} {τ : Timeliness} {Δ : ℕ} {G : DG ι}
    (hV : V.Nonempty) (hk : k ≠ .src) (h : ∀ s ∈ V, ∃ p ∈ V, ¬ Conn τ Δ G p s) :
    G ∉ J k τ Δ V := by
  rintro ⟨-, hG⟩
  cases k with
  | src => exact hk rfl
  | snk =>
    obtain ⟨s, hs, hG⟩ := hG
    obtain ⟨p, hp, hn⟩ := h s hs
    exact hn (hG p hp)
  | all =>
    obtain ⟨s, hs⟩ := hV
    obtain ⟨p, hp, hn⟩ := h s hs
    exact hn (hG p hp s hs)

/-! ### Journeys in sparse dynamic graphs -/

namespace Reach

variable {G : DG ι} {p q : ι} {a b : ℕ}

/-- A vertex without outgoing edges reaches only itself. -/
theorem eq_of_no_out (hp : ∀ t r, ¬ G t p r) (h : Reach G p a b q) : p = q := by
  cases h with
  | refl => rfl
  | step _ _ hG _ => exact absurd hG (hp _ _)

/-- A vertex without incoming edges is reached only by itself. -/
theorem eq_of_no_in (hq : ∀ t r, ¬ G t r q) (h : Reach G p a b q) : p = q := by
  revert hq
  induction h with
  | refl => intro; rfl
  | step _ _ hG _ ih =>
    intro hq
    obtain rfl := ih hq
    exact absurd hG (hq _ _)

/-- No journey uses a window `[a, b)` of rounds without edges. -/
theorem eq_of_empty (hG : ∀ t, a ≤ t → t < b → ∀ x y, ¬ G t x y) (h : Reach G p a b q) :
    p = q := by
  cases h with
  | refl => rfl
  | step hat htb hG' _ => exact absurd hG' (hG _ hat htb _ _)

/-- If all edges in the window `[a, b)` occur in the same round, then a journey in this window is
trivial or a single edge. -/
theorem eq_or_edge_of_sparse
    (hG : ∀ t₁ t₂ x₁ y₁ x₂ y₂, a ≤ t₁ → t₁ < b → a ≤ t₂ → t₂ < b → G t₁ x₁ y₁ → G t₂ x₂ y₂ →
      t₁ = t₂)
    (h : Reach G p a b q) : p = q ∨ ∃ t, a ≤ t ∧ t < b ∧ G t p q := by
  cases h with
  | refl => exact .inl rfl
  | @step _ r _ _ _ t hat htb hpr hr =>
    have hrq : r = q := hr.eq_of_empty fun t' h1 h2 x y hxy => by
      have := hG t t' _ _ _ _ hat htb (by omega) h2 hpr hxy
      omega
    subst hrq
    exact .inr ⟨t, hat, htb, hpr⟩

end Reach

/-! ### Powers of two -/

/-- Round `t` (0-indexed) is the paper's round `t + 1`; it is a "power-of-two round" iff
`t + 1 = 2 ^ j` for some `j`. -/
def Pow2Round (t : ℕ) : Prop := ∃ j, t + 1 = 2 ^ j

theorem exists_pow2Round_ge (i : ℕ) : ∃ t, i ≤ t ∧ Pow2Round t :=
  ⟨2 ^ i - 1, by have := @Nat.lt_two_pow_self i; omega,
    i, by have := @Nat.one_le_two_pow i; omega⟩

/-- The window `[2^Δ, 2^Δ + Δ)` contains no power-of-two round: gaps grow unboundedly. -/
theorem not_pow2Round_window (Δ t : ℕ) (h1 : 2 ^ Δ ≤ t) (h2 : t < 2 ^ Δ + Δ) :
    ¬ Pow2Round t := by
  rintro ⟨j, hj⟩
  have hΔ := @Nat.lt_two_pow_self Δ
  rcases le_or_gt j Δ with h | h
  · have := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two h
    omega
  · have := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two (Nat.succ_le_of_lt h)
    rw [pow_succ] at this
    omega

/-- A window `[a, a + Δ)` with `Δ ≤ a` contains at most one power-of-two round. -/
theorem pow2Round_unique {a Δ t₁ t₂ : ℕ} (ha : Δ ≤ a) (h1 : a ≤ t₁) (h1' : t₁ < a + Δ)
    (h2 : a ≤ t₂) (h2' : t₂ < a + Δ) (p1 : Pow2Round t₁) (p2 : Pow2Round t₂) : t₁ = t₂ := by
  obtain ⟨j₁, hj₁⟩ := p1
  obtain ⟨j₂, hj₂⟩ := p2
  rcases lt_trichotomy j₁ j₂ with h | rfl | h
  · have := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two (Nat.succ_le_of_lt h)
    rw [pow_succ] at this
    omega
  · omega
  · have := Nat.pow_le_pow_right (n := 2) Nat.zero_lt_two (Nat.succ_le_of_lt h)
    rw [pow_succ] at this
    omega

/-! ### Small combinatorial helpers -/

theorem exists_mem_ne {V : Finset ι} (hV : 2 ≤ V.card) (a : ι) : ∃ p ∈ V, p ≠ a := by
  classical
  have := @Finset.pred_card_le_card_erase _ V a _
  obtain ⟨p, hp⟩ : (V.erase a).Nonempty := Finset.card_pos.mp (by omega)
  exact ⟨p, Finset.mem_of_mem_erase hp, Finset.ne_of_mem_erase hp⟩

theorem exists_mem_ne_ne {V : Finset ι} (hV : 3 ≤ V.card) (a b : ι) :
    ∃ p ∈ V, p ≠ a ∧ p ≠ b := by
  classical
  have h1 := @Finset.pred_card_le_card_erase _ V a _
  have h2 := @Finset.pred_card_le_card_erase _ (V.erase a) b _
  obtain ⟨p, hp⟩ : ((V.erase a).erase b).Nonempty := Finset.card_pos.mp (by omega)
  have hp' := Finset.mem_of_mem_erase hp
  exact ⟨p, Finset.mem_of_mem_erase hp', Finset.ne_of_mem_erase hp', Finset.ne_of_mem_erase hp⟩

/-! ### Witness 1: the constant out-star and in-star (part (1) of the proof) -/

/-- The constant out-star `G(1S) = S, S, …` centered at `c`: edges `c → q` for all `q ∈ V`,
`q ≠ c`, in every round. -/
def outStar (V : Finset ι) (c : ι) : DG ι := fun _ p q => p = c ∧ q ∈ V ∧ q ≠ c

/-- The constant in-star `G(1T) = T, T, …` centered at `c`: edges `p → c` for all `p ∈ V`,
`p ≠ c`, in every round. -/
def inStar (V : Finset ι) (c : ι) : DG ι := fun _ p q => q = c ∧ p ∈ V ∧ p ≠ c

section Stars

variable {V : Finset ι} {c : ι} {Δ : ℕ}

theorem outStar_mem (hc : c ∈ V) (hΔ : 1 ≤ Δ) : outStar V c ∈ J .src .bounded Δ V := by
  refine ⟨fun t p q h => ⟨h.1 ▸ hc, h.2.1, h.1 ▸ h.2.2.symm⟩, c, hc, fun p hp => ?_⟩
  by_cases hpc : p = c
  · subst hpc; exact Conn.refl _ _ _ _
  · exact fun i => tdist_le_iff.mpr
      ((Reach.single (G := outStar V c) (t := i) ⟨rfl, hp, hpc⟩).mono_right (by omega))

/-- `G(1S)` has no temporal sink (not even a recurrent one), if `|V| ≥ 3`. -/
theorem outStar_no_sink (hV : 3 ≤ V.card) (τ : Timeliness) (Δ : ℕ) :
    ∀ s ∈ V, ∃ p ∈ V, ¬ Conn τ Δ (outStar V c) p s := by
  intro s _
  obtain ⟨p, hp, hpc, hps⟩ := exists_mem_ne_ne hV c s
  refine ⟨p, hp, fun h => ?_⟩
  obtain ⟨b, hb⟩ := (h.mono (Timeliness.le_recur τ)) 0
  exact hps (hb.eq_of_no_out fun t r hr => hpc hr.1)

theorem inStar_mem (hc : c ∈ V) (hΔ : 1 ≤ Δ) : inStar V c ∈ J .snk .bounded Δ V := by
  refine ⟨fun t p q h => ⟨h.2.1, h.1 ▸ hc, h.1 ▸ h.2.2⟩, c, hc, fun p hp => ?_⟩
  by_cases hpc : p = c
  · subst hpc; exact Conn.refl _ _ _ _
  · exact fun i => tdist_le_iff.mpr
      ((Reach.single (G := inStar V c) (t := i) ⟨rfl, hp, hpc⟩).mono_right (by omega))

/-- `G(1T)` has no temporal source (not even a recurrent one), if `|V| ≥ 3`. -/
theorem inStar_no_source (hV : 3 ≤ V.card) (τ : Timeliness) (Δ : ℕ) :
    ∀ s ∈ V, ∃ p ∈ V, ¬ Conn τ Δ (inStar V c) s p := by
  intro s _
  obtain ⟨p, hp, hpc, hps⟩ := exists_mem_ne_ne hV c s
  refine ⟨p, hp, fun h => ?_⟩
  obtain ⟨b, hb⟩ := (h.mono (Timeliness.le_recur τ)) 0
  exact hps (hb.eq_of_no_in fun t r hr => hpc hr.1).symm

end Stars

/-! ### Witness 2: complete graph at power-of-two rounds (part (2) of the proof) -/

/-- `G(2)`: the complete graph on `V` at the paper's rounds `2^j`, no edge otherwise. -/
def G2 (V : Finset ι) : DG ι := fun t p q => Pow2Round t ∧ p ∈ V ∧ q ∈ V ∧ p ≠ q

section G2

variable {V : Finset ι} {Δ : ℕ}

theorem G2_mem (hΔ : 1 ≤ Δ) : G2 V ∈ J .all .quasi Δ V := by
  refine ⟨fun t p q h => h.2, fun p hp q hq => ?_⟩
  by_cases hpq : p = q
  · subst hpq; exact Conn.refl _ _ _ _
  · intro i
    obtain ⟨t, hit, ht⟩ := exists_pow2Round_ge i
    exact ⟨t, hit, tdist_le_iff.mpr
      ((Reach.single (G := G2 V) ⟨ht, hp, hq, hpq⟩).mono_right (by omega))⟩

/-- In `G(2)`, no vertex is a timely source or sink of another vertex. -/
theorem G2_not_conn {p q : ι} (hpq : p ≠ q) : ¬ Conn .bounded Δ (G2 V) p q := by
  intro h
  exact hpq ((tdist_le_iff.mp (h (2 ^ Δ))).eq_of_empty
    fun t h1 h2 x y hxy => not_pow2Round_window Δ t h1 h2 hxy.1)

theorem G2_not_mem (hV : 2 ≤ V.card) (k : Kind) : G2 V ∉ J k .bounded Δ V := by
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hk : k = .snk
  · refine not_mem_J_of_no_sink hne (by simp [hk]) fun s _ => ?_
    obtain ⟨p, hp, hps⟩ := exists_mem_ne hV s
    exact ⟨p, hp, G2_not_conn hps⟩
  · refine not_mem_J_of_no_source hne hk fun s _ => ?_
    obtain ⟨p, hp, hps⟩ := exists_mem_ne hV s
    exact ⟨p, hp, G2_not_conn hps.symm⟩

end G2

/-! ### Witness 3: a ring with one edge per power-of-two round (part (3) of the proof) -/

/-- `G(3)` for the enumeration `v 0, …, v (n-1)` of the vertices: at the paper's round `2^j`
the single ring edge `v (j mod n) → v ((j + 1) mod n)`, no edge otherwise. -/
def G3 (n : ℕ) (v : ℕ → ι) : DG ι :=
  fun t p q => ∃ j, t + 1 = 2 ^ j ∧ p = v (j % n) ∧ q = v ((j + 1) % n)

/-- Every finite set of vertices can be enumerated as `v 0, …, v (|V| - 1)`. -/
theorem exists_enum (V : Finset ι) (hV : V.Nonempty) :
    ∃ v : ℕ → ι, (∀ k < V.card, v k ∈ V) ∧ (∀ a < V.card, ∀ b < V.card, v a = v b → a = b) ∧
      ∀ p ∈ V, ∃ k < V.card, v k = p := by
  obtain ⟨x, hx⟩ := hV
  refine ⟨fun k => if h : k < V.card then (V.equivFin.symm ⟨k, h⟩ : ι) else x, ?_, ?_, ?_⟩
  · intro k hk; simp [hk]
  · intro a ha b hb hab
    simp only [ha, hb, dite_true] at hab
    have := V.equivFin.symm.injective (Subtype.ext hab)
    simpa using this
  · intro p hp
    refine ⟨V.equivFin ⟨p, hp⟩, (V.equivFin ⟨p, hp⟩).isLt, ?_⟩
    simp

section G3

variable {V : Finset ι} {n : ℕ} {v : ℕ → ι} {Δ : ℕ}

theorem G3_pow2Round {t : ℕ} {p q : ι} (h : G3 n v t p q) : Pow2Round t :=
  let ⟨j, hj, _⟩ := h; ⟨j, hj⟩

theorem G3_isDG (hn : 2 ≤ n) (hmem : ∀ k < n, v k ∈ V)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b) : IsDG V (G3 n v) := by
  rintro t p q ⟨j, -, rfl, rfl⟩
  refine ⟨hmem _ (Nat.mod_lt _ (by omega)), hmem _ (Nat.mod_lt _ (by omega)), fun h => ?_⟩
  have h1 := hinj _ (Nat.mod_lt _ (by omega)) _ (Nat.mod_lt _ (by omega)) h
  have h2 : 0 ≡ 1 [MOD n] := Nat.ModEq.add_left_cancel' j h1
  unfold Nat.ModEq at h2
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at h2
  omega

/-- Every vertex of the ring recurrently reaches every vertex. -/
theorem G3_treach (hn : 1 ≤ n) (d a i : ℕ) : TReach (G3 n v) i (v (a % n)) (v ((a + d) % n)) := by
  induction d generalizing a i with
  | zero => exact ⟨i, by simpa using Reach.refl _ _ _⟩
  | succ d ih =>
    set j := a % n + n * i with hj
    have hji : i ≤ j := by
      have : i ≤ n * i := Nat.le_mul_of_pos_left i hn
      omega
    have hjmod : j ≡ a [MOD n] := by
      show j % n = a % n
      rw [hj, Nat.add_mul_mod_self_left, Nat.mod_mod]
    obtain ⟨b, hb⟩ := ih (a + 1) (2 ^ j - 1 + 1)
    have hpow := @Nat.lt_two_pow_self j
    have hedge : G3 n v (2 ^ j - 1) (v (a % n)) (v ((a + 1) % n)) :=
      ⟨j, by omega, by rw [hjmod], by rw [hjmod.add_right 1]⟩
    refine ⟨max b (2 ^ j), ?_⟩
    rw [show a + (d + 1) = a + 1 + d by omega]
    exact .step (t := 2 ^ j - 1) (by omega) (by omega) hedge (hb.mono_right (by omega))

theorem G3_mem (hn : 2 ≤ n) (hmem : ∀ k < n, v k ∈ V)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b) (hsurj : ∀ p ∈ V, ∃ k < n, v k = p) :
    G3 n v ∈ J .all .recur Δ V := by
  refine ⟨G3_isDG hn hmem hinj, fun p hp q hq i => ?_⟩
  obtain ⟨a, ha, rfl⟩ := hsurj p hp
  obtain ⟨b, hb, rfl⟩ := hsurj q hq
  have := G3_treach (n := n) (v := v) (by omega) (b + n - a) a i
  rwa [Nat.mod_eq_of_lt ha, show a + (b + n - a) = b + n by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hb] at this

/-- In a late window `[j, j + Δ)` (`j ≥ Δ`), journeys of `G(3)` are trivial or a single edge. -/
theorem G3_reach_window {j : ℕ} (hj : Δ ≤ j) {p q : ι} (h : Reach (G3 n v) p j (j + Δ) q) :
    p = q ∨ ∃ t, G3 n v t p q := by
  rcases h.eq_or_edge_of_sparse (fun t₁ t₂ _ _ _ _ h1 h1' h2 h2' e1 e2 =>
      pow2Round_unique hj h1 h1' h2 h2' (G3_pow2Round e1) (G3_pow2Round e2)) with h | ⟨t, -, -, h⟩
  · exact .inl h
  · exact .inr ⟨t, h⟩

/-- In `G(3)` the only out-neighbour of `v a` is `v (a + 1)`. -/
theorem G3_out {a t : ℕ} (hn : 1 ≤ n) (ha : a < n) (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b)
    {q : ι} (h : G3 n v t (v a) q) : q = v ((a + 1) % n) := by
  obtain ⟨m, -, hm, rfl⟩ := h
  have : m ≡ a [MOD n] := by
    have := hinj _ ha _ (Nat.mod_lt _ (by omega)) hm
    show m % n = a % n
    rw [Nat.mod_eq_of_lt ha, this]
  rw [this.add_right 1]

/-- In `G(3)` the only in-neighbour of `v b` is `v (b - 1)` (indices mod `n`). -/
theorem G3_in {b t : ℕ} (hn : 1 ≤ n) (hb : b < n) (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b)
    {p : ι} (h : G3 n v t p (v b)) : p = v ((b + n - 1) % n) := by
  obtain ⟨m, -, rfl, hm⟩ := h
  have h1 : m + 1 ≡ b + n - 1 + 1 [MOD n] := by
    have := hinj _ hb _ (Nat.mod_lt _ (by omega)) hm
    show (m + 1) % n = (b + n - 1 + 1) % n
    rw [show b + n - 1 + 1 = b + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hb, this]
  rw [Nat.ModEq.add_right_cancel' 1 h1]

theorem G3_not_mem (hn : 3 ≤ n)
    (hinj : ∀ a < n, ∀ b < n, v a = v b → a = b) (hsurj : ∀ p ∈ V, ∃ k < n, v k = p)
    (hcard : V.card = n) (k : Kind) : G3 n v ∉ J k .quasi Δ V := by
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hk : k = .snk
  · refine not_mem_J_of_no_sink hne (by simp [hk]) fun s hs => ?_
    obtain ⟨b, hb, rfl⟩ := hsurj s hs
    obtain ⟨p, hp, hps, hpr⟩ := exists_mem_ne_ne (hcard ▸ hn) (v b) (v ((b + n - 1) % n))
    refine ⟨p, hp, fun h => ?_⟩
    obtain ⟨j, hj, hd⟩ := h Δ
    rcases G3_reach_window hj (tdist_le_iff.mp hd) with h | ⟨t, ht⟩
    · exact hps h
    · exact hpr (G3_in (by omega) hb hinj ht)
  · refine not_mem_J_of_no_source hne hk fun s hs => ?_
    obtain ⟨a, ha, rfl⟩ := hsurj s hs
    obtain ⟨p, hp, hps, hpr⟩ := exists_mem_ne_ne (hcard ▸ hn) (v a) (v ((a + 1) % n))
    refine ⟨p, hp, fun h => ?_⟩
    obtain ⟨j, hj, hd⟩ := h Δ
    rcases G3_reach_window hj (tdist_le_iff.mp hd) with h | ⟨t, ht⟩
    · exact hps h.symm
    · exact hpr (G3_out (by omega) ha hinj ht)

end G3

/-! ### Theorem 1 -/

/-- **Theorem 1** of [journal version]; **Theorem 2.1** of the PODC version: for `Δ ≥ 1` and at
least three vertices, the inclusions of Figure 2 (`J_mono`) are the only inclusions between the
nine classes (Figure 3). This is the per-vertex-set form used in the paper's proof, which picks
"`n > 1` vertices"; it fails for `n = 2` (`not_theorem_1_card_two`), so the proof needs `n ≥ 3`.
Theorem 1 itself (classes over all vertex sets) is `theorem_1_classes`. -/
theorem theorem_1 {V : Finset ι} {Δ : ℕ} (hΔ : 1 ≤ Δ) (hV : 3 ≤ V.card)
    (k k' : Kind) (τ τ' : Timeliness) :
    J k τ Δ V ⊆ J k' τ' Δ V ↔ k ≤ k' ∧ τ ≤ τ' := by
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hc⟩ := hne
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => J_mono ⟨c, hc⟩ h.1 h.2⟩
  · -- part (1): stars
    by_contra hk
    rw [Kind.le_iff, not_or] at hk
    cases k with
    | all => exact hk.1 rfl
    | src =>
      have hS : outStar V c ∈ J k' τ' Δ V :=
        h (J_mono ⟨c, hc⟩ le_rfl (Timeliness.le_iff.mpr (by cases τ <;> simp [Timeliness.rank]))
          (outStar_mem hc hΔ))
      exact not_mem_J_of_no_sink ⟨c, hc⟩ (Ne.symm hk.2) (outStar_no_sink hV τ' Δ) hS
    | snk =>
      have hT : inStar V c ∈ J k' τ' Δ V :=
        h (J_mono ⟨c, hc⟩ le_rfl (Timeliness.le_iff.mpr (by cases τ <;> simp [Timeliness.rank]))
          (inStar_mem hc hΔ))
      exact not_mem_J_of_no_source ⟨c, hc⟩ (Ne.symm hk.2) (inStar_no_source hV τ' Δ) hT
  · by_contra hτ
    rw [Timeliness.le_iff, not_le] at hτ
    have hall : Kind.all ≤ k := Kind.le_iff.mpr (.inl rfl)
    cases τ' with
    | recur => cases τ <;> simp [Timeliness.rank] at hτ
    | bounded =>
      -- part (2): `G(2)`
      have hq : Timeliness.quasi ≤ τ := by
        rw [Timeliness.le_iff]; cases τ <;> simp_all [Timeliness.rank]
      exact G2_not_mem (by omega) k' (h (J_mono ⟨c, hc⟩ hall hq (G2_mem hΔ)))
    | quasi =>
      -- part (3): `G(3)`
      have hτr : τ = .recur := by cases τ <;> simp_all [Timeliness.rank]
      subst hτr
      obtain ⟨v, hmem, hinj, hsurj⟩ := exists_enum V ⟨c, hc⟩
      exact G3_not_mem hV hinj hsurj rfl k'
        (h (J_mono ⟨c, hc⟩ hall le_rfl (G3_mem (by omega) hmem hinj hsurj)))

/-! ### Theorem 1 is false for `n = 2` -/

theorem card_two_eq {V : Finset ι} (hV : V.card = 2) {a b c : ι} (ha : a ∈ V) (hb : b ∈ V)
    (hc : c ∈ V) (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  classical
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hV
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    simp_all

/-- **The proof of Theorem 1 fails for `n = 2`** (it works with "`n > 1`" vertices). With two vertices,
a journey between the two distinct vertices must start with the direct edge, so recurrent
reachability means the direct edge appears infinitely often, i.e. temporal distance `1 ≤ Δ`
infinitely often: restricted to two vertices, the recurrent class of each kind *equals* the
quasi-timely one. -/
theorem theorem_1_false_card_two {V : Finset ι} {Δ : ℕ} (hV : V.card = 2) (hΔ : 1 ≤ Δ)
    (k : Kind) : J k .recur Δ V = J k .quasi Δ V := by
  have hne : V.Nonempty := Finset.card_pos.mp (by omega)
  refine Set.Subset.antisymm ?_ (J_mono hne le_rfl (Timeliness.le_recur _))
  have key : ∀ G : DG ι, IsDG V G → ∀ p ∈ V, ∀ q ∈ V,
      Conn .recur Δ G p q → Conn .quasi Δ G p q := by
    intro G hdg p hp q hq h
    by_cases hpq : p = q
    · subst hpq; exact Conn.refl _ _ _ _
    intro i
    obtain ⟨b, hb⟩ := h i
    cases hb with
    | refl => exact absurd rfl hpq
    | @step _ r _ _ _ t hat htb hpr _ =>
      obtain ⟨-, hr, hpr'⟩ := hdg _ _ _ hpr
      obtain rfl := card_two_eq hV hp hr hq hpr' hpq
      exact ⟨t, hat, tdist_le_iff.mpr ((Reach.single hpr).mono_right (by omega))⟩
  rintro G ⟨hdg, hG⟩
  refine ⟨hdg, ?_⟩
  cases k with
  | src => obtain ⟨s, hs, hG⟩ := hG; exact ⟨s, hs, fun p hp => key G hdg s hs p hp (hG p hp)⟩
  | snk => obtain ⟨s, hs, hG⟩ := hG; exact ⟨s, hs, fun p hp => key G hdg p hp s hs (hG p hp)⟩
  | all => exact fun p hp q hq => key G hdg p hp q hq (hG p hp q hq)

/-- With two vertices, a vertex is a (`τ`-)source iff the other one is a (`τ`-)sink: the classes
`J_{1,*}^τ(Δ)` and `J_{*,1}^τ(Δ)` coincide, contradicting the non-inclusions of Theorem 1. -/
theorem J_src_eq_snk_of_card_two {V : Finset ι} (hV : V.card = 2) (τ : Timeliness) (Δ : ℕ) :
    J .src τ Δ V = J .snk τ Δ V := by
  have other : ∀ s ∈ V, ∃ t ∈ V, ∀ p ∈ V, p = s ∨ p = t := by
    intro s hs
    obtain ⟨t, ht, hts⟩ := exists_mem_ne (V := V) (by omega) s
    refine ⟨t, ht, fun p hp => ?_⟩
    by_cases hps : p = s
    · exact .inl hps
    · exact .inr (card_two_eq hV hs hp ht (Ne.symm hps) (Ne.symm hts))
  ext G
  constructor
  · rintro ⟨hdg, s, hs, hG⟩
    obtain ⟨t, ht, hst⟩ := other s hs
    refine ⟨hdg, t, ht, fun p hp => ?_⟩
    rcases hst p hp with rfl | rfl
    · exact hG t ht
    · exact Conn.refl _ _ _ _
  · rintro ⟨hdg, s, hs, hG⟩
    obtain ⟨t, ht, hst⟩ := other s hs
    refine ⟨hdg, t, ht, fun p hp => ?_⟩
    rcases hst p hp with rfl | rfl
    · exact hG t ht
    · exact Conn.refl _ _ _ _

/-- The per-vertex-set form of Theorem 1 fails for every set of exactly two vertices. -/
theorem not_theorem_1_card_two {V : Finset ι} {Δ : ℕ} (hV : V.card = 2) (hΔ : 1 ≤ Δ) :
    ¬ ∀ (k k' : Kind) (τ τ' : Timeliness), J k τ Δ V ⊆ J k' τ' Δ V ↔ k ≤ k' ∧ τ ≤ τ' := by
  intro h
  have := (h .src .src .recur .quasi).mp (theorem_1_false_card_two hV hΔ .src).le
  exact absurd this.2 (by decide)

/-- Degenerate case `n = 1`: there are no edges, and all nine classes coincide. -/
theorem J_card_one {V : Finset ι} (hV : V.card = 1) (k k' : Kind) (τ τ' : Timeliness)
    (Δ Δ' : ℕ) : J k τ Δ V = J k' τ' Δ' V := by
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hV
  have key : ∀ (k : Kind) (τ : Timeliness) (Δ : ℕ), J k τ Δ {x} = {G | IsDG {x} G} := by
    intro k τ Δ
    ext G
    simp only [J, Set.mem_ofPred_eq, and_iff_left_iff_imp]
    intro _
    cases k with
    | src =>
      refine ⟨x, Finset.mem_singleton_self x, fun p hp => ?_⟩
      rw [Finset.mem_singleton.mp hp]; exact Conn.refl _ _ _ _
    | snk =>
      refine ⟨x, Finset.mem_singleton_self x, fun p hp => ?_⟩
      rw [Finset.mem_singleton.mp hp]; exact Conn.refl _ _ _ _
    | all =>
      intro p hp q hq
      rw [Finset.mem_singleton.mp hp, Finset.mem_singleton.mp hq]; exact Conn.refl _ _ _ _
  rw [key, key]

/-- A class of dynamic graphs over all nonempty vertex sets (pairs `(V, G)` with `G` a dynamic graph
with vertex set `V`), as in the paper ("a class is a set of dynamic graphs"). -/
def JAll (k : Kind) (τ : Timeliness) (Δ : ℕ) : Set (Finset ι × DG ι) :=
  {x | x.1.Nonempty ∧ x.2 ∈ J k τ Δ x.1}

/-- **Theorem 1** (Theorem 2.1 of the PODC version), for classes over all vertex sets: the
inclusions of Figure 2 hold and are the only ones (Figure 3). -/
theorem theorem_1_classes [Infinite ι] {Δ : ℕ} (hΔ : 1 ≤ Δ) (k k' : Kind) (τ τ' : Timeliness) :
    JAll (ι := ι) k τ Δ ⊆ JAll k' τ' Δ ↔ k ≤ k' ∧ τ ≤ τ' := by
  constructor
  · intro h
    obtain ⟨V, hV⟩ := Infinite.exists_subset_card_eq ι 3
    have hne : V.Nonempty := Finset.card_pos.mp (by omega)
    refine (theorem_1 (V := V) hΔ (by omega) k k' τ τ').mp fun G hG => ?_
    exact (h (show (V, G) ∈ JAll k τ Δ from ⟨hne, hG⟩)).2
  · rintro ⟨hk, hτ⟩ x ⟨hne, hx⟩
    exact ⟨hne, J_mono hne hk hτ hx⟩

end StabilizingLEDynamic
