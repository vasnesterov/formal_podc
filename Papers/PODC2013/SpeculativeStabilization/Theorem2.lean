import Papers.PODC2013.SpeculativeStabilization.Theorem1

/-!
# Theorem 2: SSME stabilizes within `⌈diam(g)/2⌉` steps under the synchronous daemon

Let `e` be a synchronous execution of SSME from an arbitrary configuration, `D = diam(g)`.
We show that for every `i ≥ ⌈D/2⌉` at most one process is privileged in `e i`:

* `⌈D/2⌉ ≤ i ≤ D` (Case 1 of the paper): `lemma_1` (a privileged process only executed `NA`
  before), the *light cone* `cone` (every process within distance `i - 1 - j` of a process
  privileged at time `i` is `allCorrect` at time `j`, and registers within the cone differ by at
  most the distance, as integers), and `no_two_priv_early`. This replaces the paper's
  island-based Lemmas 2 and 3 (see `differencies.md`).
* `D < i < 2n` (Case 2): the corrected Lemma 4 (`lemma_4_corrected`): from time `D + 1` on every
  register is `≤ t` or `≥ K - D - 1`, so only the process with identity `n - 1` can be privileged.
  The paper's Lemma 4 (at time `D`) is false (`Lemma4.lean`).
* `i ≥ 2n` (Case 3): the configuration is in `Γ₁` (`ResetUnison.legit_sync`, proved here instead
  of citing [Boulinier, Petit, Villain, Algorithmica 2008]).
-/

namespace Podc.SpeculativeStabilization

open Cslib.SelfStabilization Cslib.SelfStabilization.ResetUnison

variable {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {e : ℕ → V → ℤ}

/-! ### Arithmetic helpers -/

theorem correct_near {K : ℕ} {y z : ℤ} (h : Correct K y z) (hy1 : 1 ≤ y) (hy2 : y ≤ K - 2) :
    |z - y| ≤ 1 := by
  obtain ⟨-, -, h3⟩ := h
  unfold succK at h3
  rw [abs_le]
  rcases h3 with h3 | h3 | h3 <;> (try split_ifs at h3) <;> constructor <;> omega

theorem near_step {K : ℕ} {c y c' t : ℤ} (ht : 0 ≤ t) (hc : Correct K c y)
    (hy : y ≤ t ∨ K - t ≤ y) (hc' : c' = c ∨ (LocLe K c y ∧ c' = succK K c)) :
    c' ≤ t + 1 ∨ K - (t + 1) ≤ c' := by
  obtain ⟨⟨hc0, hcK⟩, ⟨hy0, hyK⟩, h3⟩ := hc
  unfold LocLe at hc'
  unfold succK at *
  rcases hc' with rfl | ⟨h4, rfl⟩ <;> split_ifs at * <;> omega

/-! ### Synchronous executions of SSME -/

section Sync

variable (hconn : G.Connected) {ident : V → ℕ} (hinj : Function.Injective ident)
  (hid : ∀ v, ident v < Fintype.card V) (h : IsSyncExec (ssme G) e) (h0 : SValid G (e 0))

include hconn hid h h0

omit h0 in
/-- **Lemma 1** (strengthened). If `u` is privileged at time `i ≤ diam(g)`, then before `i` it only
executed `NA`: its register at time `j ≤ i` is in `[c - (i - j), c]` (`c` its privileged value),
and `u` is `allCorrect` at every time `j < i`. -/
theorem lemma_1 {u : V} {i : ℕ} (hi : i ≤ G.diam) (hu : Privileged G ident u (e i)) :
    ∀ j, j ≤ i → privVal G ident u - (i - j : ℕ) ≤ e j u ∧ e j u ≤ privVal G ident u ∧
      (j < i → AllCorrect (clockSize G) G (e j) u) := by
  have hu' := h.isUnfairRun
  have hD := diam_lt_card hconn (G := G)
  obtain ⟨hc1, hc2⟩ := privVal_bounds (G := G) hid u
  have hK := clockSize_eq G
  have hbounds : ∀ k j, j + k = i → privVal G ident u - k ≤ e j u ∧ e j u ≤ privVal G ident u := by
    intro k
    induction k with
    | zero => intro j hj; simp only [add_zero] at hj; subst hj; rw [hu]; simp
    | succ k ih =>
      intro j hj
      obtain ⟨ha1, ha2⟩ := ih (j + 1) (by omega)
      have hpos : 0 < e (j + 1) u := by omega
      rcases step_cases hu' j u with h1 | ⟨_, hn, h1⟩ | ⟨_, hc, h1⟩ | ⟨_, h1⟩
      · rw [← h1]; push_cast at ha1 ⊢; omega
      · obtain ⟨w, hw⟩ := exists_adj hconn u
        have h0u := (hn.1 w hw).1.1
        rw [phi_of_nonneg h0u] at h1
        have := succK_of_nonneg (K := clockSize G) h0u (hn.1 w hw).1.2
        push_cast at ha1 ⊢; omega
      · rw [phi_of_neg hc.1.2] at h1; have := hc.1.2; omega
      · omega
  intro j hj
  obtain ⟨hb1, hb2⟩ := hbounds (i - j) j (by omega)
  refine ⟨hb1, hb2, fun hji => ?_⟩
  by_contra hac
  have hpos : 0 < e j u := by omega
  have hr := (sync_ra h ⟨hac, hpos⟩).succ hu'
  have := (hbounds (i - (j + 1)) (j + 1) (by omega)).1
  omega

omit h0 in
/-- Lemma 1 as stated in the paper: a process privileged at time `i ≤ diam(g)` executes neither
`CA` nor `RA` during the first `i` steps. -/
theorem lemma_1' {u : V} {i : ℕ} (hi : i ≤ G.diam) (hu : Privileged G ident u (e i)) :
    ∀ j < i, ¬ ConvergeStep (Fintype.card V) G (e j) u ∧ ¬ ResetInit (clockSize G) G (e j) u := by
  intro j hj
  obtain ⟨h1, -, h3⟩ := lemma_1 hconn hid h hi hu j hj.le
  obtain ⟨-, -⟩ := privVal_bounds (G := G) hid u
  have := (privVal_bounds (G := G) hid u).1
  have hD := diam_lt_card hconn (G := G)
  refine ⟨fun hc => ?_, fun hr => hr.1 (h3 hj)⟩
  have := hc.1.2
  omega

omit h0 in
/-- **The light cone.** If `u` is privileged at time `i ≤ diam(g)`, then for every walk `p` from
`w` to `u` and every time `j` with `j + |p| ≤ i`, the registers of `w` and `u` at time `j` differ
by at most `|p|` (as integers), and `w` is `allCorrect` at time `j` if `j + |p| < i`. -/
theorem cone {u : V} {i : ℕ} (hi : i ≤ G.diam) (hu : Privileged G ident u (e i)) {w : V}
    (p : G.Walk w u) : ∀ j, j + p.length ≤ i →
      |e j w - e j u| ≤ p.length ∧ (j + p.length + 1 ≤ i → AllCorrect (clockSize G) G (e j) w) := by
  have hu' := h.isUnfairRun
  have hD := diam_lt_card hconn (G := G)
  obtain ⟨hc1, hc2⟩ := privVal_bounds (G := G) hid u
  have hL1 := lemma_1 hconn hid h hi hu
  suffices H : ∀ L, ∀ w (p : G.Walk w u), p.length = L → ∀ j, j + L ≤ i →
      |e j w - e j u| ≤ L ∧ (j + L + 1 ≤ i → AllCorrect (clockSize G) G (e j) w) by
    intro j hj; exact H _ w p rfl j hj
  intro L
  induction L with
  | zero =>
    intro w p hp j hj
    cases p with
    | nil => exact ⟨by simp, fun hj' => (hL1 j hj).2.2 (by omega)⟩
    | cons _ _ => simp at hp
  | succ L ih =>
    intro w p hp j hj
    cases p with
    | nil => simp at hp
    | @cons _ x _ hadj p =>
    simp only [SimpleGraph.Walk.length_cons] at hp
    obtain ⟨hx1, hx2⟩ := ih x p (by omega) j (by omega)
    have hxac := hx2 (by omega)
    obtain ⟨hu1, hu2, -⟩ := hL1 j (by omega)
    have hy1 : 1 ≤ e j x := by
      rw [abs_le] at hx1; omega
    have hy2 : e j x ≤ clockSize G - 2 := by
      rw [abs_le] at hx1; omega
    have hwx := correct_near (hxac w hadj.symm) hy1 hy2
    refine ⟨?_, fun hj' => ?_⟩
    · rw [abs_le] at hx1 hwx ⊢; push_cast; constructor <;> omega
    · by_contra hac
      have hw0 := (hxac w hadj.symm).2.1.1
      have hxac' := (ih x p (by omega) (j + 1) (by omega)).2 (by omega)
      have hw1 := (hxac' w hadj.symm).2.1.1
      rcases eq_or_lt_of_le hw0 with hw | hw
      · rw [← hw] at hwx
        rw [abs_le] at hx1 hwx; omega
      · rw [(sync_ra h ⟨hac, hw⟩).succ hu'] at hw1
        have := Fintype.card_pos (α := V); omega

omit h0 in
/-- If `u ≠ v` are both privileged at a time `i` with `⌈D/2⌉ ≤ i ≤ D`: contradiction (Case 1 of
the proof of Theorem 2). -/
theorem no_two_priv_early (hinj : Function.Injective ident) {u v : V} (huv : u ≠ v) {i : ℕ}
    (hi1 : (G.diam + 1) / 2 ≤ i) (hi2 : i ≤ G.diam) (hu : Privileged G ident u (e i))
    (hv : Privileged G ident v (e i)) : False := by
  wlog hlt : ident u < ident v generalizing u v
  · exact this huv.symm hv hu (lt_of_le_of_ne (not_lt.1 hlt) (hinj.ne huv.symm))
  have hu' := h.isUnfairRun
  have hD1 := one_le_diam hconn (G := G)
  have hDn := diam_lt_card hconn (G := G)
  obtain ⟨hcu1, hcu2⟩ := privVal_bounds (G := G) hid u
  obtain ⟨hcv1, hcv2⟩ := privVal_bounds (G := G) hid v
  have hdiff := privVal_sub (G := G) (ident := ident) u v
  -- `c_v - c_u = 2 D m` with `m ≥ 1`
  set m : ℤ := (ident v : ℤ) - ident u with hm
  have hm1 : 1 ≤ m := by omega
  set P : ℤ := (G.diam : ℤ) * m
  have hP1 : (G.diam : ℤ) ≤ P := by
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℤ) ≤ G.diam); simpa using this
  have hP2 : 2 ≤ m → 2 * (G.diam : ℤ) ≤ P := fun h2 => by
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℤ) ≤ G.diam); linarith
  have hdiff' : privVal G ident v - privVal G ident u = 2 * P := by rw [hdiff]; ring
  obtain ⟨hu0a, hu0b, -⟩ := lemma_1 hconn hid h hi2 hu 0 (Nat.zero_le _)
  obtain ⟨hv0a, hv0b, hv0c⟩ := lemma_1 hconn hid h hi2 hv 0 (Nat.zero_le _)
  -- the registers of `u` and `v` at time `0` differ by at most `dist(u, v) ≤ D`
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v u
  have hd := dist_le_diam hconn v u
  have hmid : |e 0 u - e 0 v| ≤ G.dist v u := by
    set k := G.dist v u / 2
    have h1 := (cone hconn hid h hi2 hu (p.drop k) 0 (by
      rw [SimpleGraph.Walk.drop_length]; omega)).1
    have h2 := (cone hconn hid h hi2 hv (p.take k).reverse 0 (by
      rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length]; omega)).1
    rw [SimpleGraph.Walk.drop_length] at h1
    rw [SimpleGraph.Walk.length_reverse, SimpleGraph.Walk.take_length] at h2
    rw [abs_le] at h1 h2 ⊢
    push_cast at h1 h2 ⊢
    constructor <;> omega
  rw [abs_le] at hmid
  have hm2 : ¬ 2 ≤ m := fun h2 => by have := hP2 h2; omega
  have hP : P = G.diam := by
    have : m = 1 := by omega
    simp [P, this]
  -- equality case: `v` moved at step `0`, `i = D`, and `dist(v, u) = D`
  have hiD : i = G.diam := by omega
  have hv0 : e 0 v = privVal G ident v - i := by omega
  have hu0 : e 0 u = privVal G ident u := by omega
  have hduv : G.dist v u = G.diam := by omega
  obtain ⟨hv1a, -, -⟩ := lemma_1 hconn hid h hi2 hv 1 (by omega)
  have hmove : e 1 v ≠ e 0 v := by omega
  have hn : NormalStep (clockSize G) G (e 0) v := by
    have hac := hv0c (by omega)
    rw [show e 1 v = ssme G (e 0) v from congrFun (h 0) v] at hmove
    unfold ssme next at hmove
    split_ifs at hmove with h1 h2 h3
    · exact h1
    · have := h2.1.2; omega
    · exact absurd hac h3.1
    · exact absurd rfl hmove
  -- the neighbour `y` of `v` towards `u`
  cases p with
  | nil => exact huv rfl
  | @cons _ y _ hadj p' =>
    simp only [SimpleGraph.Walk.length_cons] at hp
    have hy := (cone hconn hid h hi2 hu p' 0 (by omega)).1
    have hl := hn.2 y hadj
    unfold LocLe succK at hl
    rw [abs_le] at hy
    split_ifs at hl <;> omega

omit hid in
/-- **Corrected Lemma 4.** If `γ₀ ∉ Γ₁`, then from time `D + 1` on every register is `≤ t` or
`≥ K - D - 1` (the paper claims `init ∪ [K - D, K - 1] ∪ [0, 2D - 1]` at time `D`, which is
false: `Lemma4.lean`). -/
theorem lemma_4_corrected (hnl : ¬ Gamma1 G (e 0)) :
    ∀ w t, G.diam + 1 ≤ t → e t w ≤ t ∨ (clockSize G : ℤ) - (G.diam + 1) ≤ e t w := by
  have hu' := h.isUnfairRun
  have hval := valid_run (by have := three_le_clockSize (G := G); omega) hu' h0
  obtain ⟨b, hb⟩ : ∃ b, ¬ AllCorrect (clockSize G) G (e 0) b := by
    by_contra hall; push Not at hall; exact hnl hall
  -- walks from `w` to `b`
  have hwalk : ∀ L, ∀ w (p : G.Walk w b), p.length = L → e (L + 1) w ≤ L + 1 ∨
      (clockSize G : ℤ) - (L + 1) ≤ e (L + 1) w := by
    intro L
    induction L with
    | zero =>
      intro w p hp
      cases p with
      | cons _ _ => simp at hp
      | nil =>
      left
      push_cast
      by_cases hpos : 0 < e 0 b
      · rw [(sync_ra h ⟨hb, hpos⟩).succ hu']; omega
      · rcases succ_le hu' 0 b with h1 | h1 <;> simp only [zero_add] at h1 <;> omega
    | succ L ih =>
      intro w p hp
      cases p with
      | nil => simp at hp
      | @cons _ x _ hadj p =>
      simp only [SimpleGraph.Walk.length_cons] at hp
      have ihx := ih x p (by omega)
      push_cast at ihx ⊢
      by_cases hc : 0 < e (L + 1) w
      · by_cases hac : AllCorrect (clockSize G) G (e (L + 1)) w
        · have hcor := hac x hadj
          have := near_step (c' := e (L + 1 + 1) w) (t := (L : ℤ) + 1) (by positivity) hcor
            (by convert ihx using 2) (by
            rcases nonneg_cases hu' hc.le (fun hr => hr.2.1 hac) with h1 | ⟨_, hn, h1⟩
            · exact Or.inl h1
            · exact Or.inr ⟨hn.2 x hadj, h1⟩)
          convert this using 2
        · left; rw [(sync_ra h ⟨hac, hc⟩).succ hu']; omega
      · left; rcases succ_le hu' (L + 1) w with h1 | h1 <;> omega
  -- propagation in time
  have hge : ∀ s w, e s w ≤ e (s + 1) w ∨ e (s + 1) w ≤ 0 := by
    intro s w
    rcases step_cases hu' s w with h1 | ⟨_, _, h1⟩ | ⟨_, _, h1⟩ | ⟨_, h1⟩ <;> rw [h1]
    · left; rfl
    all_goals first | (right; omega) | (unfold phi succK; split_ifs <;> omega)
  intro w t ht
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist w b
  have hd := dist_le_diam hconn w b
  have hstart := hwalk _ w p hp
  have key : ∀ s, G.dist w b + 1 ≤ s → e s w ≤ s ∨
      (clockSize G : ℤ) - (G.dist w b + 1) ≤ e s w := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => push_cast at hstart ⊢; exact hstart
    | succ s hs ih =>
      rcases hge s w with h1 | h1
      · rcases ih with ih | ih
        · rcases succ_le hu' s w with h2 | h2 <;> push_cast <;> omega
        · right; omega
      · left; omega
  rcases key t (by omega) with h1 | h1
  · exact Or.inl h1
  · right; omega

/-- **Safety part of Theorem 2.** For every `i ≥ ⌈D/2⌉`, at most one process is privileged at
time `i`. -/
theorem sync_safe (hinj : Function.Injective ident) {i : ℕ} (hi : (G.diam + 1) / 2 ≤ i) {u v : V}
    (hu : Privileged G ident u (e i)) (hv : Privileged G ident v (e i)) : u = v := by
  have hu' := h.isUnfairRun
  have hK := three_le_clockSize (G := G)
  by_cases hL : Gamma1 G (e i)
  · exact legit_safe hconn hinj hid hL hu hv
  have hL0 : ¬ Gamma1 G (e 0) := fun h' => hL (legit_run hK hu' h' i (Nat.zero_le _))
  have hi2n : i < 2 * Fintype.card V := by
    by_contra hge
    exact hL (legit_sync hK le_rfl h h0 i (by omega))
  by_contra huv
  by_cases hiD : i ≤ G.diam
  · exact no_two_priv_early hconn hid h hinj huv hi hiD hu hv
  · have hnear := lemma_4_corrected hconn h h0 hL0
    have hD1 := one_le_diam hconn (G := G)
    have top : ∀ w, Privileged G ident w (e i) → privVal G ident w = clockSize G - G.diam - 1 := by
      intro w hw
      obtain ⟨h1, h2⟩ := privVal_bounds (G := G) hid w
      rcases hnear w i (by omega) with h3 | h3 <;> rw [hw] at h3
      · omega
      · omega
    have heq : privVal G ident u = privVal G ident v := by rw [top u hu, top v hv]
    have hsub := privVal_sub (G := G) (ident := ident) u v
    rw [heq, sub_self] at hsub
    have hD0 : (2 * G.diam : ℤ) ≠ 0 := by positivity
    have : (ident v : ℤ) - ident u = 0 := by
      rcases mul_eq_zero.1 hsub.symm with h' | h'
      · exact absurd h' hD0
      · exact h'
    exact huv (hinj (by omega))

end Sync

/-- **Theorem 2.** `conv_time(SSME, sd) ≤ ⌈diam(g)/2⌉`: from time `⌈D/2⌉` on, every synchronous
execution of SSME (from an arbitrary configuration) satisfies mutual exclusion. -/
theorem theorem_2 (hconn : G.Connected) (ident : V → ℕ) (hinj : Function.Injective ident)
    (hid : ∀ v, ident v < Fintype.card V) :
    PseudoStabilizingWithin (syncExecs (ssme G) (SValid G)) (MutualExclusion (Privileged G ident))
      ((G.diam + 1) / 2) := by
  rintro ω ⟨h, hS, h0⟩
  have hK := three_le_clockSize (G := G)
  have hu := h.isUnfairRun
  have hS' : (fun t => (ω t).2) = syncSet (next := ssme G) (fun t => (ω t).1) := funext hS
  rw [← hS'] at hu
  have hleg := legit_sync hK le_rfl h h0 _ le_rfl
  obtain ⟨-, hlive⟩ := mutualExclusion_of_gamma1 hconn hinj hid hu h0 hleg
  refine ⟨fun t u v hu' hv' => sync_safe hconn hid h h0 hinj (by omega) hu' hv', fun v T => ?_⟩
  obtain ⟨t, ht, h1, h2⟩ := hlive v ((G.diam + 1) / 2 + T)
  exact ⟨t - (G.diam + 1) / 2, by omega, by
    simpa [show (G.diam + 1) / 2 + (t - (G.diam + 1) / 2) = t by omega] using And.intro h1 h2⟩

end Podc.SpeculativeStabilization
