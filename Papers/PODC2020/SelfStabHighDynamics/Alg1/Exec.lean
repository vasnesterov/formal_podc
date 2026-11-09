import Papers.PODC2020.SelfStabHighDynamics.Alg1.Defs

/-!
# Algorithm 1: one round, executions, and the proofs of Section 4.2

We fix `Δ > 0`. `X G γ t` (`= (alg Δ hΔ).exec G γ t`) is the configuration at the end of the
paper's Round `t` (0-indexed: `exec … 0 = γ`, round `t + 1` uses the snapshot `G t`).

* Round level: `lexMin_mem`, `lexMin_le`, `round_lid_le`, `round_ttl_eq_zero`, `round_ttl_lt`,
  `round_lid_src`, `round_ttl_lb` (lower bounds on `ttl` are propagated: Lemma 1),
  `round_ub` (upper bounds on `ttl` are propagated: Lemmas 3 and 4).
* Execution level: Remark 6, closure of `C_A^V`, Lemma 1, Corollary 4, Lemma 2, Claim (*) of
  Lemma 3 (`claim`), Lemma 3, Corollary 5, Lemma 4, Theorem 4.

The leader `ℓ` is the least element of `V`; we use `IsLeast (V : Set ι) ℓ` so that the
definitions do not need a nonemptiness proof (`isLeast_iff_eq_min'`).
-/

namespace Podc.SelfStabHighDynamics.Alg1

open Cslib.HeardOf StabilizingLEDynamic

variable {ι : Type*} [LinearOrder ι]

/-! ### The lexicographic minimum (line 7) -/

theorem lexMin_mem (mb : Finset (ι × ℕ)) (h : mb.Nonempty) : lexMin mb h ∈ mb := by
  obtain ⟨a, ha, he⟩ := Finset.mem_map.mp (Finset.min'_mem (mb.map toLex.toEmbedding) h.map)
  unfold lexMin
  rw [← he]
  exact ha

/-- The lexicographic minimum is lexicographically below every message. -/
theorem lexMin_le (mb : Finset (ι × ℕ)) (h : mb.Nonempty) {y : ι × ℕ} (hy : y ∈ mb) :
    (lexMin mb h).1 < y.1 ∨ ((lexMin mb h).1 = y.1 ∧ (lexMin mb h).2 ≤ y.2) := by
  have := Finset.min'_le (mb.map toLex.toEmbedding) (toLex y) (Finset.mem_map_of_mem _ hy)
  exact (Prod.Lex.le_iff).mp this

/-! ### One round -/

section Round

variable {Δ : ℕ} {me : ι} {s : St ι} {mb : Finset (ι × ℕ)}

theorem body_def (Δ : ℕ) (me : ι) (s : St ι) (mb : Finset (ι × ℕ)) :
    body Δ me s mb =
      if h : mb.Nonempty then
        (if (lexMin mb h).1 < s.lid then
          updateTTL Δ me ⟨(lexMin mb h).1, s.ttl⟩ ((lexMin mb h).2 + 1)
        else if (lexMin mb h).1 = s.lid then updateTTL Δ me s (min s.ttl (lexMin mb h).2 + 1)
        else updateTTL Δ me s (s.ttl + 1))
      else updateTTL Δ me s (s.ttl + 1) := rfl

theorem updateTTL_cases (Δ : ℕ) (me : ι) (s : St ι) (v : ℕ) :
    updateTTL Δ me s v = ⟨me, 0⟩ ∨ (s.lid ≠ me ∧ v < 2 * Δ ∧ updateTTL Δ me s v = ⟨s.lid, v⟩) ∨
      (s.lid = me ∧ updateTTL Δ me s v = s) := by
  unfold updateTTL
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨h2, by omega, rfl⟩)
  · exact Or.inr (Or.inr ⟨not_not.mp h2, rfl⟩)

theorem updateTTL_of_ne {v : ℕ} (h : s.lid ≠ me) (hv : v < 2 * Δ) :
    updateTTL Δ me s v = ⟨s.lid, v⟩ := by
  unfold updateTTL
  rw [ite_eq_right (by omega), ite_eq_left h]

theorem round_eq (Δ : ℕ) (me : ι) (s : St ι) (mb : Finset (ι × ℕ)) :
    round Δ me s mb = ⟨me, 0⟩ ∨ ((body Δ me s mb).lid < me ∧ round Δ me s mb = body Δ me s mb) := by
  unfold round
  dsimp only
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr ⟨lt_of_not_ge h, rfl⟩

/-- Remark 6 (first part), for one round. -/
theorem round_lid_le : (round Δ me s mb).lid ≤ me := by
  rcases round_eq Δ me s mb with h | ⟨h1, h2⟩
  · rw [h]
  · rw [h2]; exact h1.le

/-- Remark 6 (second part), for one round. -/
theorem round_ttl_eq_zero (h : (round Δ me s mb).lid = me) : (round Δ me s mb).ttl = 0 := by
  rcases round_eq Δ me s mb with h' | ⟨h1, h2⟩
  · rw [h']
  · rw [h2] at h ⊢; exact absurd h h1.ne

theorem updateTTL_ttl_lt (hΔ : 0 < Δ) {v : ℕ} (hs : s.ttl < 2 * Δ) :
    (updateTTL Δ me s v).ttl < 2 * Δ := by
  rcases updateTTL_cases Δ me s v with h | ⟨-, hv, h⟩ | ⟨-, h⟩ <;> rw [h]
  · show 0 < 2 * Δ; omega
  · exact hv
  · exact hs

/-- The `ttl` stays in `{0, …, 2Δ - 1}`. -/
theorem round_ttl_lt (hΔ : 0 < Δ) (hs : s.ttl < 2 * Δ) : (round Δ me s mb).ttl < 2 * Δ := by
  rcases round_eq Δ me s mb with h | ⟨-, h⟩ <;> rw [h]
  · show 0 < 2 * Δ; omega
  · rw [body_def]
    split_ifs <;> exact updateTTL_ttl_lt hΔ hs

theorem body_lid_src :
    (body Δ me s mb).lid = me ∨ (body Δ me s mb).lid = s.lid ∨
      ∃ x ∈ mb, x.1 = (body Δ me s mb).lid := by
  rw [body_def]
  split_ifs with hne h1 h2
  · rcases updateTTL_cases Δ me ⟨(lexMin mb hne).1, s.ttl⟩ ((lexMin mb hne).2 + 1)
      with h' | ⟨-, -, h'⟩ | ⟨-, h'⟩ <;> rw [h']
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨_, lexMin_mem mb hne, rfl⟩)
    · exact Or.inr (Or.inr ⟨_, lexMin_mem mb hne, rfl⟩)
  all_goals
    rcases updateTTL_cases Δ me s _ with h' | ⟨-, -, h'⟩ | ⟨-, h'⟩ <;> rw [h']
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inl rfl)

/-- The new leader is `me`, the old leader, or the leader of a received message. -/
theorem round_lid_src :
    (round Δ me s mb).lid = me ∨ (round Δ me s mb).lid = s.lid ∨
      ∃ x ∈ mb, x.1 = (round Δ me s mb).lid := by
  rcases round_eq Δ me s mb with h | ⟨-, h⟩
  · rw [h]; exact Or.inl rfl
  · rw [h]; exact body_lid_src

/-- Lower bounds on the `ttl` of a non-own leader are propagated with an increment (the core of
Lemma 1): if every received message about the new leader `L ≠ me` has `ttl ≥ T`, and so has
the old state if its leader is `L`, then the new `ttl` is `≥ T + 1`. -/
theorem round_ttl_lb {T : ℕ} (hne : (round Δ me s mb).lid ≠ me)
    (hmb : ∀ x ∈ mb, x.1 = (round Δ me s mb).lid → T ≤ x.2)
    (hs : s.lid = (round Δ me s mb).lid → T ≤ s.ttl) : T + 1 ≤ (round Δ me s mb).ttl := by
  rcases round_eq Δ me s mb with h | ⟨-, h⟩
  · rw [h] at hne; exact absurd rfl hne
  rw [h] at hne hmb hs ⊢
  revert hne hmb hs
  rw [body_def]
  split_ifs with hm h1 h2
  · rcases updateTTL_cases Δ me ⟨(lexMin mb hm).1, s.ttl⟩ ((lexMin mb hm).2 + 1)
      with h' | ⟨-, -, h'⟩ | ⟨h'', h'⟩ <;> rw [h'] <;> intro hne hmb _
    · exact absurd rfl hne
    · have := hmb _ (lexMin_mem mb hm) rfl; dsimp only; omega
    · exact absurd h'' hne
  · rcases updateTTL_cases Δ me s (min s.ttl (lexMin mb hm).2 + 1)
      with h' | ⟨-, -, h'⟩ | ⟨h'', h'⟩ <;> rw [h'] <;> intro hne hmb hs
    · exact absurd rfl hne
    · have h3 := hmb _ (lexMin_mem mb hm) h2
      have h4 := hs rfl
      dsimp only; omega
    · exact absurd h'' hne
  all_goals
    rcases updateTTL_cases Δ me s (s.ttl + 1) with h' | ⟨-, -, h'⟩ | ⟨h'', h'⟩ <;> rw [h'] <;>
      intro hne hmb hs
    · exact absurd rfl hne
    · have := hs rfl; dsimp only; omega
    · exact absurd h'' hne

theorem body_ub {K : ℕ} {L : ι} (hLme : L < me) (hmb : ∀ x ∈ mb, L ≤ x.1)
    (hs : L ≤ s.lid) (hK : K + 1 < 2 * Δ)
    (hsrc : (s.lid = L ∧ s.ttl ≤ K) ∨ ∃ x ∈ mb, x.1 = L ∧ x.2 ≤ K) :
    (body Δ me s mb).lid = L ∧ (body Δ me s mb).ttl ≤ K + 1 := by
  have key : ∀ hm : mb.Nonempty, L ≤ (lexMin mb hm).1 ∧
      ((s.lid = L ∧ s.ttl ≤ K) ∨ ((lexMin mb hm).1 = L ∧ (lexMin mb hm).2 ≤ K)) := by
    intro hm
    refine ⟨hmb _ (lexMin_mem mb hm), ?_⟩
    rcases hsrc with h | ⟨x, hx, hx1, hx2⟩
    · exact Or.inl h
    · rcases lexMin_le mb hm hx with h | ⟨h1, h2⟩
      · exact absurd (hmb _ (lexMin_mem mb hm)) (not_le.mpr (hx1 ▸ h))
      · exact Or.inr ⟨h1.trans hx1, h2.trans hx2⟩
  rw [body_def]
  by_cases hm : mb.Nonempty
  · rw [dite_eq_left hm]
    obtain ⟨hL, hc⟩ := key hm
    by_cases h1 : (lexMin mb hm).1 < s.lid
    · rw [ite_eq_left h1]
      rcases hc with ⟨h3, -⟩ | ⟨h3, h4⟩
      · exact absurd (h3 ▸ h1) (not_lt.mpr hL)
      · rw [updateTTL_of_ne (by show (lexMin mb hm).1 ≠ me; rw [h3]; exact hLme.ne) (by omega)]
        exact ⟨h3, by dsimp only; omega⟩
    · rw [ite_eq_right h1]
      by_cases h2 : (lexMin mb hm).1 = s.lid
      · rw [ite_eq_left h2]
        have hsl : s.lid = L := by
          rcases hc with ⟨h3, -⟩ | ⟨h3, -⟩
          · exact h3
          · exact h2 ▸ h3
        have hv : min s.ttl (lexMin mb hm).2 ≤ K := by
          rcases hc with ⟨-, h4⟩ | ⟨-, h4⟩
          · exact (min_le_left _ _).trans h4
          · exact (min_le_right _ _).trans h4
        rw [updateTTL_of_ne (by rw [hsl]; exact hLme.ne) (by omega)]
        exact ⟨hsl, by dsimp only; omega⟩
      · rw [ite_eq_right h2]
        rcases hc with ⟨h3, h4⟩ | ⟨h3, -⟩
        · rw [updateTTL_of_ne (by rw [h3]; exact hLme.ne) (by omega)]
          exact ⟨h3, by dsimp only; omega⟩
        · exfalso; rw [h3] at h1 h2; exact h1 (lt_of_le_of_ne hs h2)
  · rw [dite_eq_right hm]
    rcases hsrc with ⟨h3, h4⟩ | ⟨x, hx, -⟩
    · rw [updateTTL_of_ne (by rw [h3]; exact hLme.ne) (by omega)]
      exact ⟨h3, by dsimp only; omega⟩
    · exact absurd ⟨x, hx⟩ hm

/-- Upper bounds on the `ttl` of the leader `L ≤ me` are propagated with an increment (the core of
Lemmas 3 and 4): if no received message and not the own state has a leader below `L`, and either
the own state or a received message is `⟨L, k⟩` with `k ≤ K` and `K + 1 < 2Δ`, then the new state
has leader `L` and `ttl ≤ K + 1`. -/
theorem round_ub {K : ℕ} {L : ι} (hLme : L ≤ me) (hmb : ∀ x ∈ mb, L ≤ x.1)
    (hs : L ≤ s.lid) (hK : K + 1 < 2 * Δ)
    (hsrc : (s.lid = L ∧ s.ttl ≤ K) ∨ ∃ x ∈ mb, x.1 = L ∧ x.2 ≤ K) :
    (round Δ me s mb).lid = L ∧ (round Δ me s mb).ttl ≤ K + 1 := by
  rcases eq_or_lt_of_le hLme with rfl | hLme
  · -- `L = me`: every candidate leader is `≥ me`, so `me` resets to `⟨me, 0⟩`.
    have : round Δ L s mb = ⟨L, 0⟩ := by
      rcases round_eq Δ L s mb with h | ⟨h1, -⟩
      · exact h
      · exfalso
        rcases body_lid_src (Δ := Δ) (me := L) (s := s) (mb := mb) with h | h | ⟨x, hx, h⟩
        · exact h1.ne h
        · exact not_le.mpr h1 (h ▸ hs)
        · exact not_le.mpr h1 (h ▸ hmb x hx)
    rw [this]; exact ⟨rfl, Nat.zero_le _⟩
  obtain ⟨h1, h2⟩ := body_ub hLme hmb hs hK hsrc
  have : round Δ me s mb = body Δ me s mb := by
    unfold round
    dsimp only
    rw [ite_eq_right (not_le.mpr (h1 ▸ hLme))]
  rw [this]; exact ⟨h1, h2⟩

end Round

/-! ### Legitimate configurations -/

/-- A quasi-legitimate configuration (Section 4.2): there is no fake ID (`lid(p) ∈ V` for every
`p ∈ V`), and the process `ℓ` with the lowest identifier satisfies `lid(ℓ) = id(ℓ)` and
`ttl(ℓ) = 0`. The lowest identifier is characterized by `IsLeast (V : Set ι) ℓ`
(see `qLegit_iff`). -/
def QLegit (V : Finset ι) (γ : ι → St ι) : Prop :=
  (∀ p ∈ V, (γ p).lid ∈ V) ∧ ∀ p, IsLeast (V : Set ι) p → (γ p).lid = p ∧ (γ p).ttl = 0

/-- A legitimate configuration (Section 4.2): every process `p ∈ V` has a legitimate state,
i.e., `lid(p) = id(ℓ)`, `ttl(p) ≤ Δ`, and `p = ℓ ⇒ ttl(p) = 0`, where `ℓ` is the process with
the lowest identifier (see `legit_iff`). -/
def Legit (Δ : ℕ) (V : Finset ι) (γ : ι → St ι) : Prop :=
  ∀ p ∈ V, IsLeast (V : Set ι) (γ p).lid ∧ (γ p).ttl ≤ Δ ∧ (IsLeast (V : Set ι) p → (γ p).ttl = 0)

theorem isLeast_iff_eq_min' {V : Finset ι} (hV : V.Nonempty) {x : ι} :
    IsLeast (V : Set ι) x ↔ x = V.min' hV :=
  ⟨fun h => h.unique (Finset.isLeast_min' V hV), fun h => h ▸ Finset.isLeast_min' V hV⟩

/-- `QLegit`, with `ℓ = V.min' hV`. -/
theorem qLegit_iff {V : Finset ι} (hV : V.Nonempty) {γ : ι → St ι} :
    QLegit V γ ↔ (∀ p ∈ V, (γ p).lid ∈ V) ∧
      (γ (V.min' hV)).lid = V.min' hV ∧ (γ (V.min' hV)).ttl = 0 := by
  simp only [QLegit, isLeast_iff_eq_min' hV, forall_eq]

/-- `Legit`, with `ℓ = V.min' hV`. -/
theorem legit_iff {Δ : ℕ} {V : Finset ι} (hV : V.Nonempty) {γ : ι → St ι} :
    Legit Δ V γ ↔ ∀ p ∈ V, (γ p).lid = V.min' hV ∧ (γ p).ttl ≤ Δ ∧
      (p = V.min' hV → (γ p).ttl = 0) := by
  simp only [Legit, isLeast_iff_eq_min' hV]

/-- Every legitimate configuration is quasi-legitimate. -/
theorem Legit.qLegit {Δ : ℕ} {V : Finset ι} {γ : ι → St ι} (h : Legit Δ V γ) : QLegit V γ := by
  refine ⟨fun p hp => (h p hp).1.1, fun p hp => ?_⟩
  obtain ⟨h1, -, h3⟩ := h p hp.1
  exact ⟨h1.unique hp, h3 hp⟩

/-! ### Executions -/

section Exec

variable {Δ : ℕ} {hΔ : 0 < Δ} {V : Finset ι} {G : DG ι} {γ : ι → St ι}

theorem exec_succ (G : DG ι) (γ : ι → St ι) (t : ℕ) (p : ι) :
    (alg Δ hΔ).exec G γ (t + 1) p =
      round Δ p ((alg Δ hΔ).exec G γ t p) (rfin sent p (msgs (G t) ((alg Δ hΔ).exec G γ t) p)) := by
  change next (alg Δ hΔ).step (G t) ((alg Δ hΔ).exec G γ t) p = _
  simp only [next, alg, msgs_self, Option.getD_some]

omit [LinearOrder ι] in
/-- The mailbox of `p` in round `t`: the states `⟨lid, ttl⟩` of its current in-neighbours. -/
theorem mem_mb (hG : IsDG V G) {t : ℕ} {C : ι → St ι} {p : ι} {x : ι × ℕ} :
    x ∈ rfin sent p (msgs (G t) C p) ↔ ∃ q, G t q p ∧ x = ((C q).lid, (C q).ttl) := by
  rw [mem_rfin_msgs (f := sent) (fun s => Set.finite_singleton _) hG]
  simp only [sent, Set.mem_singleton_iff]

/-- **Remark 6.** After the first round, `lid(p) ≤ id(p)` and `lid(p) = id(p) ⇒ ttl(p) = 0`
(for every process, in every dynamic graph). -/
theorem remark6 (G : DG ι) (γ : ι → St ι) (t : ℕ) (p : ι) :
    ((alg Δ hΔ).exec G γ (t + 1) p).lid ≤ p ∧
      (((alg Δ hΔ).exec G γ (t + 1) p).lid = p → ((alg Δ hΔ).exec G γ (t + 1) p).ttl = 0) := by
  rw [exec_succ]
  exact ⟨round_lid_le, round_ttl_eq_zero⟩

/-- The configurations of Algorithm 1 for `V` are closed under every round. -/
theorem exec_mem_cfg (G : DG ι) (hγ : γ ∈ (alg Δ hΔ).Cfg V) (t : ℕ) :
    (alg Δ hΔ).exec G γ t ∈ (alg Δ hΔ).Cfg V := by
  induction t with
  | zero => exact hγ
  | succ t ih =>
    intro p hp
    show ((alg Δ hΔ).exec G γ (t + 1) p).ttl < 2 * Δ
    rw [exec_succ]
    exact round_ttl_lt hΔ (ih p hp)

theorem ttl_lt (hγ : γ ∈ (alg Δ hΔ).Cfg V) (t : ℕ) {p : ι} (hp : p ∈ V) :
    ((alg Δ hΔ).exec G γ t p).ttl < 2 * Δ :=
  exec_mem_cfg G hγ t p hp

/-- **Lemma 1.** A process of `V` whose leader is a fake ID `f` at time `t` has `ttl ≥ t`. -/
theorem lemma1 (hG : IsDG V G) (γ : ι → St ι) {f : ι} (hf : f ∉ V) :
    ∀ t, ∀ p ∈ V, ((alg Δ hΔ).exec G γ t p).lid = f → t ≤ ((alg Δ hΔ).exec G γ t p).ttl := by
  intro t
  induction t with
  | zero => intros; exact Nat.zero_le _
  | succ t ih =>
    intro p hp hlid
    rw [exec_succ] at hlid ⊢
    have hne : (round Δ p ((alg Δ hΔ).exec G γ t p)
        (rfin sent p (msgs (G t) ((alg Δ hΔ).exec G γ t) p))).lid ≠ p := by
      rw [hlid]; rintro rfl; exact hf hp
    apply round_ttl_lb hne
    · intro x hx hx1
      obtain ⟨q, hq, rfl⟩ := (mem_mb hG).1 hx
      exact ih q (hG _ _ _ hq).1 (hx1.trans hlid)
    · intro h
      exact ih p hp (h.trans hlid)

/-- **Lemma 2** (one round). Quasi-legitimacy is preserved by every round of a dynamic graph
with vertex set `V`. -/
theorem qLegit_succ (hG : IsDG V G) {t : ℕ} (h : QLegit V ((alg Δ hΔ).exec G γ t)) :
    QLegit V ((alg Δ hΔ).exec G γ (t + 1)) := by
  have hmem : ∀ p ∈ V, ((alg Δ hΔ).exec G γ (t + 1) p).lid ∈ V := by
    intro p hp
    rw [exec_succ]
    rcases round_lid_src (Δ := Δ) (me := p) (s := (alg Δ hΔ).exec G γ t p)
        (mb := rfin sent p (msgs (G t) ((alg Δ hΔ).exec G γ t) p)) with h1 | h1 | ⟨x, hx, h1⟩
    · rw [h1]; exact hp
    · rw [h1]; exact h.1 p hp
    · rw [← h1]
      obtain ⟨q, hq, rfl⟩ := (mem_mb hG).1 hx
      exact h.1 q (hG _ _ _ hq).1
  refine ⟨hmem, fun p hp => ?_⟩
  obtain ⟨h1, h2⟩ := remark6 (hΔ := hΔ) G γ t p
  have : ((alg Δ hΔ).exec G γ (t + 1) p).lid = p :=
    le_antisymm h1 (hp.2 (hmem p hp.1))
  exact ⟨this, h2 this⟩

/-- **Lemma 2.** Quasi-legitimacy is preserved forever. -/
theorem qLegit_exec (hG : IsDG V G) (h : QLegit V γ) :
    ∀ t, QLegit V ((alg Δ hΔ).exec G γ t) := by
  intro t
  induction t with
  | zero => exact h
  | succ t ih => exact qLegit_succ hG ih

/-- **Corollary 4.** At the end of Round `2Δ`, the configuration is quasi-legitimate. -/
theorem cor4 (hG : IsDG V G) (hγ : γ ∈ (alg Δ hΔ).Cfg V) :
    QLegit V ((alg Δ hΔ).exec G γ (2 * Δ)) := by
  have hmem : ∀ p ∈ V, ((alg Δ hΔ).exec G γ (2 * Δ) p).lid ∈ V := by
    intro p hp
    by_contra hf
    have := lemma1 (hΔ := hΔ) hG γ hf (2 * Δ) p hp rfl
    have := ttl_lt (G := G) hγ (2 * Δ) hp
    omega
  refine ⟨hmem, fun p hp => ?_⟩
  obtain ⟨k, hk⟩ : ∃ k, 2 * Δ = k + 1 := ⟨2 * Δ - 1, by omega⟩
  obtain ⟨h1, h2⟩ := remark6 (hΔ := hΔ) G γ k p
  rw [← hk] at h1 h2
  have : ((alg Δ hΔ).exec G γ (2 * Δ) p).lid = p :=
    le_antisymm h1 (hp.2 (hmem p hp.1))
  exact ⟨this, h2 this⟩

omit [LinearOrder ι] in
theorem mem_of_journey (hG : IsDG V G) {i b : ℕ} {x y : ι} (hx : x ∈ V)
    (h : Cslib.DynNet.Journey G i x b y) : y ∈ V :=
  Cslib.DynNet.Journey.of_inv (P := fun _ a => a ∈ V) h hx fun τ a b _ _ ha hab => by
    rcases hab with rfl | hab
    · exact ha
    · exact (hG τ a b hab).2.1

/-- **Claim (*)** in the proof of Lemma 3, in the form of a propagation along journeys: from a
quasi-legitimate configuration at time `i`, every process reached from `ℓ` by a journey in the
rounds `i, …, i + J - 1` (`J < 2Δ`) has `lid = ℓ` and `ttl ≤ J` at time `i + J`. -/
theorem claim (hG : IsDG V G) (hQ : QLegit V γ) {ℓ : ι} (hℓ : IsLeast (V : Set ι) ℓ) :
    ∀ J, J < 2 * Δ → ∀ i p, Cslib.DynNet.Journey G i ℓ (i + J) p →
      ((alg Δ hΔ).exec G γ (i + J) p).lid = ℓ ∧ ((alg Δ hΔ).exec G γ (i + J) p).ttl ≤ J := by
  intro J
  induction J with
  | zero =>
    intro _ i p hj
    rw [Nat.add_zero] at hj ⊢
    obtain rfl := hj.same_time
    obtain ⟨h1, h2⟩ := (qLegit_exec hG hQ i).2 ℓ hℓ
    exact ⟨h1, h2.le⟩
  | succ J ih =>
    intro hJ i p hj
    have hpV : p ∈ V := mem_of_journey hG hℓ.1 hj
    rw [← Nat.add_assoc] at hj ⊢
    obtain ⟨y, hy, hyp⟩ := (Cslib.DynNet.journey_succ_iff (by omega)).1 hj
    obtain ⟨hy1, hy2⟩ := ih (by omega) i y hy
    have hQt := qLegit_exec (hΔ := hΔ) hG hQ (i + J)
    rw [exec_succ]
    refine round_ub (hℓ.2 hpV) ?_ (hℓ.2 (hQt.1 p hpV)) (by omega) ?_
    · intro x hx
      obtain ⟨q, hq, rfl⟩ := (mem_mb hG).1 hx
      exact hℓ.2 (hQt.1 q (hG _ _ _ hq).1)
    · rcases hyp with rfl | hyp
      · exact Or.inl ⟨hy1, hy2⟩
      · exact Or.inr ⟨_, (mem_mb hG).2 ⟨y, hyp, rfl⟩, hy1, hy2⟩

/-- **Lemma 3.** In a dynamic graph of `TC_B(Δ)` (it suffices that `ℓ` is a timely source),
from a quasi-legitimate configuration, the configuration at the end of every Round `r ≥ Δ` is
legitimate. -/
theorem lemma3 (hG : G ∈ JssB Δ V) (hQ : QLegit V γ) :
    ∀ r ≥ Δ, Legit Δ V ((alg Δ hΔ).exec G γ r) := by
  intro r hr p hp
  have hℓ : IsLeast (V : Set ι) (V.min' ⟨p, hp⟩) := Finset.isLeast_min' V ⟨p, hp⟩
  have hd := hG.2 _ hℓ.1 p hp (r - Δ)
  have hj := Cslib.DynNet.tdist_le_iff.1 hd
  obtain ⟨h1, h2⟩ := claim (hΔ := hΔ) hG.1 hQ hℓ Δ (by omega) (r - Δ) p hj
  rw [Nat.sub_add_cancel hr] at h1 h2
  refine ⟨h1 ▸ hℓ, h2, fun hpl => ?_⟩
  exact ((qLegit_exec hG.1 hQ r).2 p hpl).2

/-- **Corollary 5.** In a dynamic graph of `TC_B(Δ)`, from every configuration, the configuration
at the end of every Round `i ≥ 3Δ` is legitimate. -/
theorem cor5 (hG : G ∈ JssB Δ V) (hγ : γ ∈ (alg Δ hΔ).Cfg V) :
    ∀ i ≥ 3 * Δ, Legit Δ V ((alg Δ hΔ).exec G γ i) := by
  intro i hi
  have he := StabilizingLEDynamic.exec_add (alg Δ hΔ).toAlgorithm G γ (2 * Δ) (i - 2 * Δ)
  rw [Nat.add_sub_cancel' (by omega)] at he
  rw [SAlg.exec, he]
  exact lemma3 (J_shift hG (2 * Δ)) (cor4 hG.1 hγ) _ (by omega)

/-- **Lemma 4** (with `r = 0` included). From a legitimate configuration, in every dynamic graph
with vertex set `V`, for `r < Δ`, at the end of Round `r` every process has `lid = ℓ` and
`ttl ≤ Δ + r`. -/
theorem lemma4 (hG : IsDG V G) (hL : Legit Δ V γ) {ℓ : ι} (hℓ : IsLeast (V : Set ι) ℓ) :
    ∀ r < Δ, ∀ p ∈ V, ((alg Δ hΔ).exec G γ r p).lid = ℓ ∧ ((alg Δ hΔ).exec G γ r p).ttl ≤ Δ + r := by
  intro r
  induction r with
  | zero =>
    intro _ p hp
    obtain ⟨h1, h2, -⟩ := hL p hp
    exact ⟨h1.unique hℓ, h2⟩
  | succ r ih =>
    intro hr p hp
    have hQt := qLegit_exec (hΔ := hΔ) hG hL.qLegit r
    obtain ⟨h1, h2⟩ := ih (by omega) p hp
    rw [exec_succ, ← Nat.add_assoc]
    refine round_ub (hℓ.2 hp) ?_ (hℓ.2 (hQt.1 p hp)) (by omega) (Or.inl ⟨h1, h2⟩)
    intro x hx
    obtain ⟨q, hq, rfl⟩ := (mem_mb hG).1 hx
    exact hℓ.2 (hQt.1 q (hG _ _ _ hq).1)

/-- **Theorem 4.** In a dynamic graph of `TC_B(Δ)`, the execution from a legitimate
configuration satisfies `SP_LE`. -/
theorem thm4 (hV : V.Nonempty) (hG : G ∈ JssB Δ V) (hL : Legit Δ V γ) :
    spLE (alg Δ hΔ) V ((alg Δ hΔ).exec G γ) := by
  have hℓ := Finset.isLeast_min' V hV
  refine ⟨V.min' hV, hℓ.1, fun i q hq => ?_⟩
  show ((alg Δ hΔ).exec G γ i q).lid = V.min' hV
  rcases lt_or_ge i Δ with hi | hi
  · exact (lemma4 hG.1 hL hℓ i hi q hq).1
  · exact ((lemma3 hG hL.qLegit i hi q hq).1).unique hℓ

end Exec

end Podc.SelfStabHighDynamics.Alg1
