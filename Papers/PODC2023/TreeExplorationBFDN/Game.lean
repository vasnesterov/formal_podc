import Papers.PODC2023.TreeExplorationBFDN.UrnSum

/-!
# The balls-in-urns game (Section 3, Theorem 3.1)

Cosson, Massoulié, Viennot, PODC 2023 (Brief Announcement), Section 3; full version
arXiv:2301.13307, Section 3, Theorem 3.

The board at time `t` is a load vector `n^t : Fin k → ℕ` (initially `n^0_i = 1`, so there are `k`
balls in total). At time `t` the adversary picks a nonempty urn `a_t`, then the player picks an
urn `b_t` and one ball moves from `a_t` to `b_t`. `U_t` is the set of urns never chosen by the
adversary before time `t`. The game stops at the first time `t` with `n^t_i ≥ Δ` for all `i ∈ U_t`.

The player's strategy: `b_t` minimizes `n^t_i` over `i ∈ U_{t+1} = [k] \ {a_0, …, a_t}` (if this
set is empty the game is over at time `t + 1` anyway and `b_t` is arbitrary).

A `GamePlay` records the whole (infinite) sequence of boards and moves; `IsPlay Δ p T` says that the
first `T` moves are legal, follow the player's strategy, and the game has not stopped before
time `T`. Theorem 3.1 bounds every such `T`.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset

/-- A play of the balls-in-urns game with `k` urns: boards and moves at every time. -/
structure GamePlay (k : ℕ) where
  /-- `load t i = n^t_i`. -/
  load : ℕ → Fin k → ℕ
  /-- The adversary's urn `a_t`. -/
  adv : ℕ → Fin k
  /-- The player's urn `b_t`. -/
  pl : ℕ → Fin k

namespace GamePlay

variable {k : ℕ} (p : GamePlay k)

/-- `U_t`: the urns never chosen by the adversary before time `t`. -/
def unchosen (t : ℕ) : Finset (Fin k) := univ.filter fun i => ∀ s < t, p.adv s ≠ i

/-- The game has stopped at time `t`: every urn of `U_t` holds at least `Δ` balls. -/
def Stopped (Δ : ℕ) (t : ℕ) : Prop := ∀ i ∈ p.unchosen t, Δ ≤ p.load t i

/-- Move `t` is legal: `a_t` is nonempty and one ball moves from `a_t` to `b_t`. -/
def LegalMove (t : ℕ) : Prop :=
  1 ≤ p.load t (p.adv t) ∧
    ∀ i, p.load (t + 1) i + (if i = p.adv t then 1 else 0) =
      p.load t i + (if i = p.pl t then 1 else 0)

/-- At time `t` the player follows the strategy of Section 3: `b_t` has minimum load among
`U_{t+1} = [k] \ {a_0, …, a_t}` (when this set is nonempty). -/
def PlayerFollows (t : ℕ) : Prop :=
  (p.unchosen (t + 1)).Nonempty →
    p.pl t ∈ p.unchosen (t + 1) ∧ ∀ i ∈ p.unchosen (t + 1), p.load t (p.pl t) ≤ p.load t i

/-- The first `T` moves of `p` are legal and follow the player's strategy, starting from the
initial board `n^0 = (1, …, 1)`, and the game has not stopped at any time `t < T`. -/
def IsPlay (Δ : ℕ) (T : ℕ) : Prop :=
  (∀ i, p.load 0 i = 1) ∧
    ∀ t < T, ¬ p.Stopped Δ t ∧ p.LegalMove t ∧ p.PlayerFollows t

/-! ### Accounting lemmas for Theorem 3.1 -/

lemma unchosen_zero : p.unchosen 0 = univ := by ext; simp [unchosen]

lemma unchosen_succ (t : ℕ) : p.unchosen (t + 1) = (p.unchosen t).erase (p.adv t) := by
  ext i
  simp only [unchosen, mem_filter, mem_univ, true_and, mem_erase]
  constructor
  · intro h
    exact ⟨fun e => h t (Nat.lt_succ_self t) e.symm, fun s hs => h s (Nat.lt_succ_of_lt hs)⟩
  · rintro ⟨hne, h⟩ s hs
    rcases Nat.lt_succ_iff_lt_or_eq.mp hs with hs | rfl
    · exact h s hs
    · exact fun e => hne e.symm

lemma load_succ {t : ℕ} (h : p.LegalMove t) {i : Fin k} (hi : i ≠ p.adv t) :
    p.load (t + 1) i = p.load t i + if i = p.pl t then 1 else 0 := by
  have := h.2 i
  simp only [hi, ↓reduceIte, Nat.add_zero] at this
  exact this

lemma exists_lt_of_not_stopped {Δ t : ℕ} (h : ¬ p.Stopped Δ t) :
    ∃ i ∈ p.unchosen t, p.load t i < Δ := by
  simp only [Stopped, not_forall, not_le] at h
  obtain ⟨i, hi, h⟩ := h
  exact ⟨i, hi, h⟩

variable {p}

lemma IsPlay.sum_load {Δ T : ℕ} (hp : p.IsPlay Δ T) : ∀ t ≤ T, ∑ i, p.load t i = k := by
  intro t
  induction t with
  | zero => intro _; simp [hp.1]
  | succ t ih =>
    intro ht
    have hm := (hp.2 t (by omega)).2.1
    have h := sum_congr rfl (fun i (_ : i ∈ (univ : Finset (Fin k))) => hm.2 i)
    rw [sum_add_distrib, sum_add_distrib, sum_ite_eq', sum_ite_eq'] at h
    simp only [mem_univ, ↓reduceIte] at h
    have := ih (by omega)
    omega

lemma IsPlay.balanced {Δ T : ℕ} (hp : p.IsPlay Δ T) :
    ∀ t ≤ T, ∀ i ∈ p.unchosen t, ∀ j ∈ p.unchosen t, p.load t i ≤ p.load t j + 1 := by
  intro t
  induction t with
  | zero => intro _ i _ j _; simp [hp.1]
  | succ t ih =>
    intro ht i hi j hj
    have hstep := hp.2 t (by omega)
    have hU : (p.unchosen (t + 1)).Nonempty := ⟨i, hi⟩
    have hb := hstep.2.2 hU
    have hi' := hi
    have hj' := hj
    rw [p.unchosen_succ, mem_erase] at hi' hj'
    rw [p.load_succ hstep.2.1 hi'.1, p.load_succ hstep.2.1 hj'.1]
    have h1 := ih (by omega) i hi'.2 j hj'.2
    have h2 := ih (by omega) j hj'.2 i hi'.2
    have h3 := hb.2 i hi
    have h4 := hb.2 j hj
    split_ifs with e1 e2 e2
    · omega
    · subst e1; omega
    · subst e2; omega
    · omega

lemma IsPlay.loadSum_le {Δ T : ℕ} (hp : p.IsPlay Δ T) {t : ℕ} (ht : t ≤ T) :
    ∑ i ∈ p.unchosen t, p.load t i ≤ k := by
  exact (sum_le_sum_of_subset (subset_univ _)).trans (hp.sum_load t ht).le

/-- While the game runs, every unchosen urn holds at most `min(Δ, ⌈k/u_t⌉)` balls. -/
lemma IsPlay.load_le {Δ T : ℕ} (hp : p.IsPlay Δ T) {t : ℕ} (ht : t < T) {i : Fin k}
    (hi : i ∈ p.unchosen t) : p.load t i ≤ min Δ (ceilDiv k (p.unchosen t).card) := by
  refine le_min ?_ ?_
  · obtain ⟨j, hj, hlt⟩ := p.exists_lt_of_not_stopped (hp.2 t ht).1
    have := hp.balanced t ht.le i hi j hj
    omega
  · exact le_ceilDiv_of_balanced hi (hp.balanced t ht.le i hi) (hp.loadSum_le ht.le)

/-- The potential inequality `t + k ≤ N_t + ∑_{u = u_t + 1}^{k} min(Δ, ⌈k/u⌉)` for `t < T`. -/
lemma IsPlay.potential {Δ T : ℕ} (hp : p.IsPlay Δ T) : ∀ t < T,
    t + k ≤ ∑ i ∈ p.unchosen t, p.load t i +
      ∑ u ∈ Ioc (p.unchosen t).card k, min Δ (ceilDiv k u) := by
  intro t
  induction t with
  | zero => intro _; simp [hp.1, unchosen_zero]
  | succ t ih =>
    intro ht
    have IH := ih (by omega)
    have hstep := hp.2 t (by omega)
    obtain ⟨i0, hi0, -⟩ := p.exists_lt_of_not_stopped (hp.2 (t + 1) ht).1
    have hb := hstep.2.2 ⟨i0, hi0⟩
    have hbU := hb.1
    rw [p.unchosen_succ, mem_erase] at hbU
    have hNsucc : ∑ i ∈ p.unchosen (t + 1), p.load (t + 1) i =
        ∑ i ∈ p.unchosen (t + 1), p.load t i + 1 := by
      rw [sum_congr rfl (fun i hi => p.load_succ hstep.2.1 (by
        rw [p.unchosen_succ, mem_erase] at hi; exact hi.1)), sum_add_distrib, sum_ite_eq']
      simp only [hb.1, ↓reduceIte]
    by_cases ha : p.adv t ∈ p.unchosen t
    · have hU : p.unchosen (t + 1) = (p.unchosen t).erase (p.adv t) := p.unchosen_succ t
      have hc := card_erase_of_mem ha
      have hc0 : 0 < (p.unchosen t).card := card_pos.mpr ⟨_, ha⟩
      have hck : (p.unchosen t).card ≤ k := card_le_univ _ |>.trans (by simp)
      have hsplit := add_sum_erase (p.unchosen t) (p.load t) ha
      have hla := hp.load_le (by omega) ha
      obtain ⟨c, hcdef⟩ : ∃ c, (p.unchosen t).card = c + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hc0).symm⟩
      have hIoc : Ioc c k = cons (c + 1) (Ioc (c + 1) k) (by simp) := by
        rw [← Finset.Icc_add_one_left_eq_Ioc, Icc_eq_cons_Ioc (by omega)]
      rw [hNsucc, hU, hc, hcdef, Nat.add_sub_cancel, hIoc, sum_cons]
      rw [hcdef] at IH hla
      omega
    · have hU : p.unchosen (t + 1) = p.unchosen t := by
        rw [p.unchosen_succ, erase_eq_of_notMem ha]
      have : ∑ i ∈ p.unchosen (t + 1), p.load t i = ∑ i ∈ p.unchosen t, p.load t i := by rw [hU]
      rw [hNsucc, this, hU]
      omega

/-- Combinatorial core of Theorem 3.1: `T - 1 + k ≤ S_k(Δ)` for every play of length `T ≥ 1`. -/
lemma IsPlay.length_le {Δ T : ℕ} (hp : p.IsPlay Δ T) (hT : 1 ≤ T) :
    T - 1 + k ≤ urnSum k Δ := by
  have ht : T - 1 < T := by omega
  have hpot := hp.potential (T - 1) ht
  set c := (p.unchosen (T - 1)).card with hcdef
  have hck : c ≤ k := card_le_univ _ |>.trans (by simp)
  have hN : ∑ i ∈ p.unchosen (T - 1), p.load (T - 1) i ≤
      ∑ u ∈ Ioc 0 c, min Δ (ceilDiv k u) := by
    calc ∑ i ∈ p.unchosen (T - 1), p.load (T - 1) i
        ≤ ∑ _i ∈ p.unchosen (T - 1), min Δ (ceilDiv k c) := sum_le_sum fun i hi => hp.load_le ht hi
      _ = ∑ _u ∈ Ioc 0 c, min Δ (ceilDiv k c) := by simp [hcdef]
      _ ≤ ∑ u ∈ Ioc 0 c, min Δ (ceilDiv k u) := by
        apply sum_le_sum
        intro u hu
        rw [mem_Ioc] at hu
        exact min_le_min_left _ (ceilDiv_anti k hu.1 hu.2)
  have hsum : ∑ u ∈ Ioc 0 c, min Δ (ceilDiv k u) + ∑ u ∈ Ioc c k, min Δ (ceilDiv k u) =
      urnSum k Δ := by
    rw [sum_Ioc_consecutive _ (Nat.zero_le c) hck, urnSum, ← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  omega

end GamePlay

/-- **Theorem 3.1** of [CMV23] (Theorem 3 of the full version): if the player uses the balancing
strategy, the game ends in at most `k min(log Δ, log k) + k` steps. -/
theorem game_ends {k Δ T : ℕ} (p : GamePlay k) (hp : p.IsPlay Δ T) :
    (T : ℝ) ≤ k * min (Real.log Δ) (Real.log k) + k := by
  rcases Nat.eq_zero_or_pos T with rfl | hT
  · have h1 : 0 ≤ min (Real.log Δ) (Real.log k) :=
      le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    have h2 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    push_cast
    nlinarith
  obtain ⟨i, -, hi⟩ := p.exists_lt_of_not_stopped (hp.2 0 hT).1
  have hk : 1 ≤ k := i.pos
  have hΔ : 1 ≤ Δ := by omega
  have hlen := hp.length_le hT
  have hlen' : (T : ℝ) - 1 + k ≤ urnSum k Δ := by
    have : ((T - 1 + k : ℕ) : ℝ) ≤ urnSum k Δ := by exact_mod_cast hlen
    rw [Nat.cast_add, Nat.cast_sub hT] at this
    simpa using this
  have := urnSum_add_one_le hk hΔ
  linarith

end Podc.TreeExplorationBFDN
