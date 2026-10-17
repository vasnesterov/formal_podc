import Papers.PODC2019.VABA.Safety
import Podc.Probability.CoinGame

/-!
# VABA: each view succeeds with probability `≥ (n - f) / n` (Lemmas 21–24)

An **adversary strategy** `σ` chooses the next action from the history of global states. The
states contain everything (all local states, all signature shares, the corrupted set) except the
coins that have not been revealed yet, so `σ` is an adaptive adversary that also schedules all
messages and corruptions. With a coin sequence `c` this determines a run `run C σ c`.

Let `good σ c j` be the set of proposers whose broadcast of view `j` has a stage-4 certificate at
the moment the coin of view `j` is revealed (all of `P` if it is never revealed). Then
* `good` depends only on the coins of the views before `j` (`good_congr`): the adversary cannot see
  the coin of view `j` before it fixes this set;
* `card_good`: it has at least `Q` elements (Lemma 21);
* `decided_of_hit`: if the leader `c j` of view `j` is in `good σ c j`, every party that leaves view
  `j` has decided (Lemma 22).

Plugging this into the coin game of `Podc/Probability/CoinGame.lean` (uniform coins
`x : Fin k → P` for the views `1, …, k`):
* `card_undecided_le`: the number of coin sequences for which some party completes the first `k`
  views without deciding is at most `f ^ k` out of `n ^ k` (for `Q = n - f`), i.e. probability
  `≤ (f / n) ^ k < (1/3) ^ k` (Lemma 23 iterated, the core of Lemma 24);
* `expected_views_le`: the expected number of views up to the first view whose leader had
  completed its broadcast is at most `n / (n - f) < 3/2` (§3.3.1: "the number of views in
  expectation is less than 3/2"); every party that completes that view has decided.
-/

namespace VABA

open Finset Cslib.Probability

variable {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V}

/-- An adversary strategy: the next action as a function of the history (most recent state
first). -/
abbrev Strategy (P V : Type*) := List (Glob P V) → Act P V

/-- The history of the run of strategy `σ` with coins `c` up to time `t`. -/
noncomputable def hist (C : Cfg P V) (σ : Strategy P V) (c : ℕ → P) : ℕ → List (Glob P V)
  | 0 => [init C]
  | t + 1 => step C c (σ (hist C σ c t)) ((hist C σ c t).headD (init C)) :: hist C σ c t

/-- The state at time `t`. -/
noncomputable def run (C : Cfg P V) (σ : Strategy P V) (c : ℕ → P) (t : ℕ) : Glob P V :=
  (hist C σ c t).headD (init C)

lemma run_zero (σ : Strategy P V) (c : ℕ → P) : run C σ c 0 = init C := rfl

lemma run_succ (σ : Strategy P V) (c : ℕ → P) (t : ℕ) :
    run C σ c (t + 1) = step C c (σ (hist C σ c t)) (run C σ c t) := rfl

lemma reach_run (σ : Strategy P V) (c : ℕ → P) (t : ℕ) : Reach C (run C σ c t) := by
  induction t with
  | zero => exact Reach.init
  | succ t ih => rw [run_succ]; exact Reach.step c _ ih

lemma mono_run (σ : Strategy P V) (c : ℕ → P) {t t' : ℕ} (h : t ≤ t') :
    Mono (run C σ c t) (run C σ c t') := by
  induction h with
  | refl => exact Mono.refl _
  | step _ ih => exact ih.trans (by rw [run_succ]; exact mono_step C c _ _)

/-! ### Coins are used only when revealed -/

/-- Revealing view `j` does not depend on the value of the coin. -/
lemma step_rev_ne_none_iff (c c' : ℕ → P) (a : Act P V) (s : Glob P V) (j : ℕ) :
    (step C c a s).rev j ≠ none ↔ (step C c' a s).rev j ≠ none := by
  unfold step
  split_ifs with hE
  · cases a with
    | invokeElect p =>
      simp only [eff]
      split_ifs <;> simp
    | _ => rfl
  · exact Iff.rfl

/-- Before the coin of view `j` is revealed, a step uses only the coins of earlier views. -/
lemma step_congr {s : Glob P V} (I : Inv C s) {j : ℕ} (hj : 1 ≤ j) (hs : s.rev j = none)
    {c c' : ℕ → P} (hc : ∀ i < j, c i = c' i) (a : Act P V)
    (hnew : (step C c a s).rev j = none) : step C c a s = step C c' a s := by
  unfold step at hnew ⊢
  split_ifs with hE
  · rw [ite_eq_left hE] at hnew
    cases a with
    | invokeElect p =>
      simp only [eff] at hnew ⊢
      congr 1
      funext i
      by_cases hi : i = (s.loc p).view ∧ s.rev (s.loc p).view = none
      · rw [ite_eq_left hi, ite_eq_left hi]
        have hlt : (s.loc p).view < j := by
          rcases lt_trichotomy (s.loc p).view j with h | h | h
          · exact h
          · exfalso
            rw [ite_eq_left ⟨h.symm, hi.2⟩] at hnew; simp at hnew
          · exfalso
            obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp
              (I.lead_some p j hj (Or.inl h))
            rw [(I.lead_spec p j l hl).2] at hs; simp at hs
        rw [hc _ hlt]
      · rw [ite_eq_right hi, ite_eq_right hi]
    | _ => rfl
  · rfl

/-- Runs with coin sequences that agree before view `j` coincide until the coin of view `j` is
revealed. -/
lemma run_congr (σ : Strategy P V) {c c' : ℕ → P} {j : ℕ} (hj : 1 ≤ j)
    (hc : ∀ i < j, c i = c' i) :
    ∀ t, (∀ t' ≤ t, (run C σ c t').rev j = none) → hist C σ c t = hist C σ c' t := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    have ih' := ih (fun t' ht' => h t' (by omega))
    have hrun : run C σ c t = run C σ c' t := by simp only [run, ih']
    show step C c (σ (hist C σ c t)) (run C σ c t) :: hist C σ c t =
      step C c' (σ (hist C σ c' t)) (run C σ c' t) :: hist C σ c' t
    rw [← ih', ← hrun]
    congr 1
    exact step_congr (reach_run (C := C) σ c t).inv hj (h t (by omega)) hc _ (h (t + 1) le_rfl)

/-! ### The set of good leaders of a view -/

open Classical in
/-- The proposers of view `j` whose broadcast has a stage-4 certificate when the coin of view `j`
is revealed (everybody, if it is never revealed). -/
noncomputable def good (C : Cfg P V) (σ : Strategy P V) (c : ℕ → P) (j : ℕ) : Finset P :=
  if h : ∃ t, (run C σ c (t + 1)).rev j ≠ none then completed C.Q (run C σ c (Nat.find h)) j
  else univ

lemma rev_none_before (σ : Strategy P V) (c : ℕ → P) {j : ℕ}
    (h : ∃ t, (run C σ c (t + 1)).rev j ≠ none) :
    ∀ t' ≤ Nat.find h, (run C σ c t').rev j = none := by
  intro t' ht'
  rcases t' with _ | t''
  · rfl
  · have := Nat.find_min h (show t'' < Nat.find h by omega)
    simpa using this

/-- **The adversary fixes the good set before seeing the coin**: `good σ c j` depends only on the
coins of the views before `j`. -/
lemma good_congr (σ : Strategy P V) {c c' : ℕ → P} {j : ℕ} (hj : 1 ≤ j)
    (hc : ∀ i < j, c i = c' i) : good C σ c j = good C σ c' j := by
  classical
  have hc' : ∀ i < j, c' i = c i := fun i hi => (hc i hi).symm
  -- agreement of the runs up to a time where `j` is not yet revealed under `c`
  have key : ∀ t, (∀ t' ≤ t, (run C σ c t').rev j = none) →
      ∀ t' ≤ t, run C σ c t' = run C σ c' t' := by
    intro t ht t' htt'
    have := run_congr σ hj hc t' (fun t'' h'' => ht t'' (by omega))
    simp only [run, this]
  unfold good
  by_cases hex : ∃ t, (run C σ c (t + 1)).rev j ≠ none
  · set T := Nat.find hex with hT
    have hbefore := rev_none_before σ c hex
    have hagree := key T hbefore
    -- at time `T + 1` the coin is revealed under `c'` as well
    have hrevT : (run C σ c' (T + 1)).rev j ≠ none := by
      have h1 : (run C σ c (T + 1)).rev j ≠ none := Nat.find_spec hex
      have hh : hist C σ c T = hist C σ c' T := run_congr σ hj hc T hbefore
      rw [run_succ] at h1 ⊢
      rw [← hh, ← hagree T le_rfl]
      exact (step_rev_ne_none_iff c c' _ _ j).mp h1
    have hex' : ∃ t, (run C σ c' (t + 1)).rev j ≠ none := ⟨T, hrevT⟩
    have hfind : Nat.find hex' = T := by
      apply le_antisymm (Nat.find_min' hex' hrevT)
      by_contra hlt
      push Not at hlt
      have h1 := Nat.find_spec hex'
      rw [← hagree (Nat.find hex' + 1) (by omega)] at h1
      exact h1 (hbefore _ (by omega))
    rw [dite_eq_left hex, dite_eq_left hex', hfind, hagree T le_rfl]
  · have hex' : ¬ ∃ t, (run C σ c' (t + 1)).rev j ≠ none := by
      rintro ⟨t, ht⟩
      apply hex
      refine ⟨t, fun h => ht ?_⟩
      have hall : ∀ t' ≤ t + 1, (run C σ c t').rev j = none := by
        intro t' _
        rcases t' with _ | t''
        · rfl
        · by_contra hne; exact hex ⟨t'', hne⟩
      rw [← key (t + 1) hall (t + 1) le_rfl]; exact h
    rw [dite_eq_right hex, dite_eq_right hex']

/-- Lemma 21: the good set has at least `Q` elements. -/
lemma card_good (hQ : Fintype.card P + C.f < 2 * C.Q) (hQn : C.Q ≤ Fintype.card P)
    (σ : Strategy P V) (c : ℕ → P) (j : ℕ) : C.Q ≤ (good C σ c j).card := by
  classical
  unfold good
  split_ifs with hex
  · set T := Nat.find hex
    have h1 : (run C σ c (T + 1)).rev j ≠ none := Nat.find_spec hex
    have h0 : (run C σ c T).rev j = none := rev_none_before σ c hex T le_rfl
    rw [run_succ] at h1
    set s := run C σ c T
    have I := (reach_run (C := C) σ c T).inv
    unfold step at h1
    split_ifs at h1 with hE
    · cases ha : σ (hist C σ c T) with
      | invokeElect p =>
        (try rw [ha] at hE h1)
        obtain ⟨-, -, hskip⟩ := hE
        simp only [eff] at h1
        have hj : j = (s.loc p).view := by
          by_contra hne
          rw [ite_eq_right (fun h => hne h.1)] at h1; exact h1 h0
        rw [hj]; exact I.completed_of_skipQC hQ hskip
      | recvVC p q j' b =>
        (try rw [ha] at h1); simp only [eff] at h1; split at h1 <;> exact absurd h0 h1
      | deliver => (try rw [ha] at h1); exact absurd h0 h1
      | skipShare => (try rw [ha] at h1); exact absurd h0 h1
      | electReturn => (try rw [ha] at h1); exact absurd h0 h1
      | recvQC => (try rw [ha] at h1); exact absurd h0 h1
      | exitView => (try rw [ha] at h1); exact absurd h0 h1
      | corrupt => (try rw [ha] at h1); exact absurd h0 h1
      | byzSign => (try rw [ha] at h1); exact absurd h0 h1
    · exact absurd h0 h1
  · simpa using hQn

/-- Lemma 22 in a run: if the leader `c j` of view `j` is good, every party that leaves view `j`
(at any time) has decided. -/
lemma decided_of_hit (hQ : Fintype.card P + C.f < 2 * C.Q) (σ : Strategy P V) (c : ℕ → P)
    {j : ℕ} (hj : 1 ≤ j) (hhit : c j ∈ good C σ c j) {t : ℕ} {p : P} (hp : j < ((run C σ c t).loc p).view) :
    ((run C σ c t).loc p).decs.Nonempty := by
  classical
  have It := (reach_run (C := C) σ c t).inv
  -- `p` left view `j`, so the coin of view `j` is revealed at time `t`
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (It.lead_some p j hj (Or.inl hp))
  have hrev := (It.lead_spec p j l hl).2
  unfold good at hhit
  have hex : ∃ t, (run C σ c (t + 1)).rev j ≠ none := by
    rcases t with _ | t
    · simp [run_zero, init] at hrev
    · exact ⟨t, by rw [hrev]; simp⟩
  rw [dite_eq_left hex] at hhit
  set T := Nat.find hex
  obtain ⟨v, hv⟩ := mem_completed.mp hhit
  -- the coin revealed at `T + 1` is `c j`
  have hrevT : (run C σ c (T + 1)).rev j = some (c j) := by
    have h1 : (run C σ c (T + 1)).rev j ≠ none := Nat.find_spec hex
    have h0 : (run C σ c T).rev j = none := rev_none_before σ c hex T le_rfl
    rw [run_succ] at h1 ⊢
    unfold step at h1 ⊢
    split_ifs at h1 ⊢ with hE
    · cases ha : σ (hist C σ c T) with
      | invokeElect q =>
        (try rw [ha] at h1)
        simp only [eff] at h1 ⊢
        by_cases hq : j = ((run C σ c T).loc q).view ∧
            (run C σ c T).rev ((run C σ c T).loc q).view = none
        · rw [ite_eq_left hq]; rw [hq.1]
        · rw [ite_eq_right hq] at h1; exact absurd h0 h1
      | recvVC p q j' b =>
        (try rw [ha] at h1); simp only [eff] at h1; split at h1 <;> exact absurd h0 h1
      | deliver => (try rw [ha] at h1); exact absurd h0 h1
      | skipShare => (try rw [ha] at h1); exact absurd h0 h1
      | electReturn => (try rw [ha] at h1); exact absurd h0 h1
      | recvQC => (try rw [ha] at h1); exact absurd h0 h1
      | exitView => (try rw [ha] at h1); exact absurd h0 h1
      | corrupt => (try rw [ha] at h1); exact absurd h0 h1
      | byzSign => (try rw [ha] at h1); exact absurd h0 h1
    · exact absurd h0 h1
  -- `t > T`, since the coin is not revealed up to time `T`
  have htT : T + 1 ≤ t := by
    by_contra hlt
    rw [rev_none_before σ c hex t (by omega)] at hrev; simp at hrev
  have hm := mono_run (C := C) σ c htT
  have hm' := mono_run (C := C) σ c (show T ≤ t by omega)
  exact ⟨v, It.decide_of_completed hQ (hm.rev _ _ hrevT) (QC_mono hm'.tok hv) hp⟩

/-! ### The coin game -/

/-- The coin sequence with leaders `x 0, …, x (K-1)` for the views `1, …, K` and arbitrary leaders
`tail` elsewhere. -/
def coins {K : ℕ} (x : Fin K → P) (tail : ℕ → P) : ℕ → P :=
  fun m => if h : 1 ≤ m ∧ m ≤ K then x ⟨m - 1, by omega⟩ else tail m

/-- The adversary of the coin game induced by the strategy `σ`: the good set of wave `i` (view
`i + 1`) as a function of the coins of the earlier views. -/
noncomputable def advOf (C : Cfg P V) (σ : Strategy P V) (tail : ℕ → P) :
    CoinGame.Adversary P :=
  fun i h => good C σ (coins h tail) (i + 1)

lemma hit_iff (σ : Strategy P V) (tail : ℕ → P) {K : ℕ} (x : Fin K → P) (i : ℕ) (hi : i < K) :
    CoinGame.Hit (advOf C σ tail) x i hi ↔
      coins x tail (i + 1) ∈ good C σ (coins x tail) (i + 1) := by
  unfold CoinGame.Hit advOf
  have hx : x ⟨i, hi⟩ = coins x tail (i + 1) := by
    simp only [coins, show 1 ≤ i + 1 ∧ i + 1 ≤ K from ⟨by omega, by omega⟩]; rfl
  rw [hx, good_congr σ (by omega : 1 ≤ i + 1) (c' := coins x tail)]
  intro m hm
  simp only [coins]
  by_cases h1 : 1 ≤ m
  · rw [dite_eq_left ⟨h1, by omega⟩, dite_eq_left ⟨h1, by omega⟩]
  · rw [dite_eq_right (fun h => h1 h.1), dite_eq_right (fun h => h1 h.1)]

open Classical in
/-- **Lemmas 23–24.** For every adversary strategy, among the `n ^ k` equally likely leader
sequences of the views `1, …, k`, at most `(n - Q) ^ k` let some party complete the first `k`
views without deciding. -/
theorem card_undecided_le (hQ : Fintype.card P + C.f < 2 * C.Q) (hQn : C.Q ≤ Fintype.card P)
    (σ : Strategy P V) (tail : ℕ → P) (k : ℕ) :
    (univ.filter (fun x : Fin k → P => ∃ t p, k < ((run C σ (coins x tail) t).loc p).view ∧
      ((run C σ (coins x tail) t).loc p).decs = ∅)).card ≤ (Fintype.card P - C.Q) ^ k := by
  refine le_trans (card_le_card ?_)
    (CoinGame.card_misses_le (advOf C σ tail) (fun i h => card_good hQ hQn σ _ _) k)
  intro x hx
  simp only [mem_filter, mem_univ, true_and] at hx
  obtain ⟨t, p, hp, hdec⟩ := hx
  simp only [CoinGame.misses, CoinGame.missesIn, mem_filter, mem_univ, true_and]
  intro i hi _ _ hhit
  rw [hit_iff] at hhit
  have := decided_of_hit hQ σ (coins x tail) (by omega : 1 ≤ i + 1) hhit (t := t) (p := p)
    (by omega)
  rw [hdec] at this; exact Set.not_nonempty_empty this

open Classical in
/-- Lemmas 23–24 with the paper's parameters (`n > 3f`, `Q = n - f`): the probability that some
party completes `k` views without deciding is at most `(f / n) ^ k`, and `f / n < 1/3`. -/
theorem prob_undecided_le (hn : 3 * C.f < Fintype.card P) (hQ : C.Q = Fintype.card P - C.f)
    (σ : Strategy P V) (tail : ℕ → P) (k : ℕ) :
    ((univ.filter (fun x : Fin k → P => ∃ t p, k < ((run C σ (coins x tail) t).loc p).view ∧
      ((run C σ (coins x tail) t).loc p).decs = ∅)).card : ℝ) / (Fintype.card P : ℝ) ^ k ≤
        ((C.f : ℝ) / Fintype.card P) ^ k ∧ (C.f : ℝ) / Fintype.card P < 1 / 3 := by
  have hn0 : (0 : ℝ) < Fintype.card P := by exact_mod_cast (show 0 < Fintype.card P by omega)
  have h := card_undecided_le (C := C) (by omega) (by omega) σ tail k
  rw [show Fintype.card P - C.Q = C.f by omega] at h
  constructor
  · rw [div_pow, div_le_div_iff_of_pos_right (by positivity)]
    exact_mod_cast h
  · rw [div_lt_div_iff₀ hn0 (by norm_num)]
    have : (3 * C.f : ℝ) < Fintype.card P := by exact_mod_cast hn
    linarith

/-- The number of views up to and including the first view whose leader had completed its
broadcast when the coin was revealed (truncated at the horizon `K`). -/
noncomputable def firstGoodView (C : Cfg P V) (σ : Strategy P V) (tail : ℕ → P) (K : ℕ)
    (x : Fin K → P) : ℕ :=
  CoinGame.T (advOf C σ tail) K x

/-- Every party that completes view `firstGoodView` has decided (if that view is within the
horizon). -/
theorem decided_of_firstGoodView (hQ : Fintype.card P + C.f < 2 * C.Q) (σ : Strategy P V)
    (tail : ℕ → P) {K : ℕ} (x : Fin K → P)
    (hhit : ∃ i, ∃ h : i < K, CoinGame.Hit (advOf C σ tail) x i h) {t : ℕ} {p : P}
    (hp : firstGoodView C σ tail K x < ((run C σ (coins x tail) t).loc p).view) :
    ((run C σ (coins x tail) t).loc p).decs.Nonempty := by
  classical
  let s := Nat.find hhit
  obtain ⟨hs, hhs⟩ := Nat.find_spec hhit
  have hT : firstGoodView C σ tail K x = s + 1 :=
    CoinGame.T_eq_of_first_hit _ x hs hhs
      (fun i h hi hh => Nat.find_min hhit hi ⟨h, hh⟩)
  rw [hT] at hp
  rw [hit_iff] at hhs
  exact decided_of_hit hQ σ _ (by omega) hhs hp

/-- **Expected number of views** (§3.3.1): the expected number of views up to and including the
first view whose leader had completed its broadcast is at most `n / Q`. -/
theorem expected_views_le (hQ : Fintype.card P + C.f < 2 * C.Q) (hQn : C.Q ≤ Fintype.card P)
    (σ : Strategy P V) (tail : ℕ → P) (K : ℕ) :
    (∑ x : Fin K → P, (firstGoodView C σ tail K x : ℚ)) / (Fintype.card P : ℚ) ^ K ≤
      (Fintype.card P : ℚ) / C.Q :=
  CoinGame.expected_waves_le (advOf C σ tail) (fun i h => card_good hQ hQn σ _ _)
    (by omega) hQn K

/-- With the paper's parameters (`n > 3f`, `Q = n - f`) the expected number of views is less than
`3/2`. -/
theorem expected_views_lt (hn : 3 * C.f < Fintype.card P) (hQ : C.Q = Fintype.card P - C.f)
    (σ : Strategy P V) (tail : ℕ → P) (K : ℕ) :
    (∑ x : Fin K → P, (firstGoodView C σ tail K x : ℚ)) / (Fintype.card P : ℚ) ^ K < 3 / 2 := by
  refine lt_of_le_of_lt (expected_views_le (by omega) (by omega) σ tail K) ?_
  have hQ0 : (0 : ℚ) < C.Q := by exact_mod_cast (show 0 < C.Q by omega)
  rw [div_lt_div_iff₀ hQ0 (by norm_num), hQ]
  have : (3 * C.f : ℚ) < Fintype.card P := by exact_mod_cast hn
  rw [Nat.cast_sub (by omega)]
  linarith

end VABA
