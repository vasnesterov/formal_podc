import Papers.PODC2019.LocalMessageReduction.Trial

/-!
# Lemma 4.3 for one node: all `2h` trials of the first step of `Cluster_j`

We run the first step of `Cluster_j` (Pseudocode 2, lines 4–12) at a fixed node `v` whose
neighbourhood in `G_j` is `N` with volumes `vol`. The state is the set `R` of neighbours not yet
queried; the loop runs while fewer than `L` trials were made, `X_v ≠ ∅` (`R ≠ ∅`) and
`|F_v| = |N \ R| < τ`. A trial draws `s` edges of `X_v` uniformly with replacement and removes the
queried neighbours from `R`.

**Randomness.** The trials are adaptive (`X_v` depends on the earlier trials). To keep a single
finite uniform sample space we draw, for every trial `t < L` and sample `i < s`, a uniform number in
`Fin M` with `M = (vol N)!`; it is decoded into a uniform edge of the current `X_v` (whose size divides
`M`) by `decodeEdge`. The decoded samples of a trial are exactly uniform (`uprob_decode`), whatever the
history, which is all the paper's conditioning ("we treat those events as if they necessarily occur")
needs.

**Result** (`lemma_4_3_node`). With `L` classes of ratio `b`, all volumes in `[1, b^L)`, `α ≥ 6`,
`τ ≤ α/3` and `θ = 1/(L α b)`, after the loop `v` is light (`R = ∅`) or heavy (`|N \ R| ≥ τ`), except
with probability at most `L · |N| · (1 − θ)^s`. With the paper's parameters
(`L = 2h`, `b = n^ε`, `α = 3c n^{2^j δ} log² n / h`, `s = c² n^{2^j δ + ε} log³ n`,
`τ = c n^{2^j δ} log n`) this is `≤ 2h · n · n^{−c/6}` (`theta_mul_samples`).
-/

namespace Podc.LocalMessageReduction

open Finset Cslib.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {vol : ι → ℕ}

/-! ### Uniform decoding -/

section Decode

variable {M : ℕ}

/-- Decode a uniform number `a < M` into an edge of `X_v = Edges vol R`, when `|X_v| = vol R`
divides `M`. -/
noncomputable def decodeEdge (R : Finset ι) (h : 0 < volOf vol R ∧ volOf vol R ∣ M) (a : Fin M) :
    Edges vol R :=
  (Fintype.equivFinOfCardEq (card_edges R)).symm
    (finProdFinEquiv.symm (finCongr (Nat.mul_div_cancel' h.2).symm a)).1

/-- **Uniformity of decoding.** For `a` uniform in `Fin s → Fin M`, the decoded samples are uniform
in `Fin s → X_v`. -/
lemma uprob_decode (R : Finset ι) (h : 0 < volOf vol R ∧ volOf vol R ∣ M) (hM0 : 0 < M) {s : ℕ}
    (P : (Fin s → Edges vol R) → Prop) :
    uprob (fun a : Fin s → Fin M => P fun i => decodeEdge R h (a i)) = uprob P := by
  set m := volOf vol R
  have hM : M = m * (M / m) := (Nat.mul_div_cancel' h.2).symm
  have hd : 0 < M / m := Nat.div_pos (Nat.le_of_dvd hM0 h.2) h.1
  let eR := Fintype.equivFinOfCardEq (card_edges (vol := vol) R)
  let E1 : (Fin s → Fin M) ≃ (Fin s → Fin m × Fin (M / m)) :=
    Equiv.arrowCongr (Equiv.refl _) ((finCongr hM).trans finProdFinEquiv.symm)
  let E2 := Equiv.arrowProdEquivProdArrow (Fin s) (fun _ => Fin m) (fun _ => Fin (M / m))
  let E3 : (Fin s → Fin m) ≃ (Fin s → Edges vol R) := Equiv.arrowCongr (Equiv.refl _) eR.symm
  have hne : Nonempty (Fin s → Fin (M / m)) := ⟨fun _ => ⟨0, hd⟩⟩
  have h1 : uprob (fun a : Fin s → Fin M => P fun i => decodeEdge R h (a i)) =
      uprob (fun p : (Fin s → Fin m) × (Fin s → Fin (M / m)) => P (E3 p.1) ∧ True) := by
    rw [← uprob_comp_equiv (E1.trans E2)]
    simp only [and_true]
    rfl
  have h2 := uprob_prod (fun g : Fin s → Fin m => P (E3 g)) (fun _ : Fin s → Fin (M / m) => True)
  rw [h1, h2, uprob_true_eq_one, mul_one]
  exact uprob_comp_equiv E3 P

end Decode

/-! ### The first step of `Cluster_j` at one node -/

/-- The data of the first step at a node `v`: neighbourhood `N` with volumes `vol`, class ratio `b`,
number of classes = number of trials `L` (`= 2h`), group parameter `α`, threshold `τ`, samples per
trial `s`. -/
structure Setup (ι : Type*) where
  vol : ι → ℕ
  N : Finset ι
  b : ℝ
  L : ℕ
  α : ℝ
  τ : ℕ
  s : ℕ

namespace Setup

variable (P : Setup ι)

/-- `M = (vol N)!`: divisible by the size of every nonempty `X_v`. -/
def M : ℕ := (volOf P.vol P.N).factorial

omit [Fintype ι] [DecidableEq ι] in
lemma M_pos : 0 < P.M := Nat.factorial_pos _

/-- The loop condition (Pseudocode 2, line 4, apart from the trial counter): `X_v ≠ ∅` and
`|F_v| < τ`. -/
def Running (R : Finset ι) : Prop := R.Nonempty ∧ #(P.N \ R) < P.τ

open Classical in
/-- The maximum-volume class `K^i(v)` of the not-yet-queried neighbours `R`. -/
noncomputable def maxClass (R : Finset ι) : Finset ι :=
  if h : ∃ x < P.L, volOf P.vol R ≤ P.L * volOf P.vol (R.filter fun u => cls P.vol P.b u = x) then
    R.filter fun u => cls P.vol P.b u = h.choose
  else ∅

open Classical in
/-- The neighbours queried in a trial from state `R`, with raw randomness `a`. -/
noncomputable def trialQ (R : Finset ι) (a : Fin P.s → Fin P.M) : Finset ι :=
  if h : 0 < volOf P.vol R ∧ volOf P.vol R ∣ P.M then
    queried P.vol (fun i => decodeEdge R h (a i))
  else ∅

open Classical in
/-- The set `R` of not-yet-queried neighbours after `t` iterations of the loop. -/
noncomputable def stateR (ω : Fin P.L → Fin P.s → Fin P.M) : ℕ → Finset ι
  | 0 => P.N
  | t + 1 =>
    if h : t < P.L ∧ P.Running (stateR ω t) then
      stateR ω t \ P.trialQ (stateR ω t) (ω ⟨t, h.1⟩)
    else stateR ω t

/-- A *good* trial from state `R`: every group of the maximum class is hit. -/
def Good (R Q : Finset ι) : Prop :=
  ∀ l < numGroups (P.maxClass R) P.α,
    (Q ∩ group (P.maxClass R) (beta (P.maxClass R) P.α) l).Nonempty

/-- Number of nonempty classes among `R`. -/
noncomputable def pot (R : Finset ι) : ℕ :=
  #((range P.L).filter fun x => ∃ u ∈ R, cls P.vol P.b u = x)

lemma trialQ_subset (R : Finset ι) (a : Fin P.s → Fin P.M) : P.trialQ R a ⊆ R := by
  unfold trialQ
  split_ifs
  · exact queried_subset _
  · exact empty_subset _

lemma stateR_subset (ω : Fin P.L → Fin P.s → Fin P.M) (t : ℕ) : P.stateR ω t ⊆ P.N := by
  induction t with
  | zero => exact subset_rfl
  | succ t ih =>
    rw [stateR]
    split_ifs
    · exact sdiff_subset.trans ih
    · exact ih

lemma stateR_succ_of_running (ω : Fin P.L → Fin P.s → Fin P.M) {t : ℕ} (ht : t < P.L)
    (hr : P.Running (P.stateR ω t)) :
    P.stateR ω (t + 1) = P.stateR ω t \ P.trialQ (P.stateR ω t) (ω ⟨t, ht⟩) := by
  rw [stateR, dite_eq_left_of_eq_true (eq_true ⟨ht, hr⟩)]

lemma stateR_succ_of_not_running (ω : Fin P.L → Fin P.s → Fin P.M) {t : ℕ}
    (hr : ¬ P.Running (P.stateR ω t)) : P.stateR ω (t + 1) = P.stateR ω t := by
  rw [stateR, dite_eq_right_of_eq_false (eq_false (fun h => hr h.2))]

/-- The state before trial `t` does not depend on the randomness of trials `≥ t`. -/
lemma stateR_update (ω : Fin P.L → Fin P.s → Fin P.M) (w : Fin P.L) (a : Fin P.s → Fin P.M) :
    ∀ t ≤ w.1, P.stateR (Function.update ω w a) t = P.stateR ω t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih (by omega)
    by_cases hr : P.Running (P.stateR ω t)
    · have htL : t < P.L := by have := w.2; omega
      have hr' : P.Running (P.stateR (Function.update ω w a) t) := ih ▸ hr
      rw [P.stateR_succ_of_running _ htL hr', P.stateR_succ_of_running _ htL hr, ih,
        Function.update_of_ne (fun e => by rw [Fin.ext_iff] at e; simp at e; omega)]
    · have hr' : ¬ P.Running (P.stateR (Function.update ω w a) t) := ih ▸ hr
      rw [P.stateR_succ_of_not_running _ hr', P.stateR_succ_of_not_running _ hr, ih]

omit [Fintype ι] [DecidableEq ι] in
/-- Properties of the maximum class, when all volumes lie in `[1, b^L)`. -/
lemma maxClass_spec (hb : 1 < P.b) (hL : 0 < P.L)
    (hvol : ∀ u ∈ P.N, 1 ≤ P.vol u ∧ (P.vol u : ℝ) < P.b ^ P.L) {R : Finset ι} (hR : R ⊆ P.N) :
    ∃ x < P.L, P.maxClass R = R.filter (fun u => cls P.vol P.b u = x) ∧
      volOf P.vol R ≤ P.L * volOf P.vol (P.maxClass R) := by
  have hex := exists_heavy_class hb hL R (fun u hu => hvol u (hR hu))
  refine ⟨hex.choose, hex.choose_spec.1, ?_, ?_⟩
  · simp only [maxClass, dite_eq_left_of_eq_true (eq_true hex)]
  · simp only [maxClass, dite_eq_left_of_eq_true (eq_true hex)]; exact hex.choose_spec.2

omit [Fintype ι] [DecidableEq ι] in
lemma volOf_pos {R : Finset ι} (hR : R ⊆ P.N) (hvol : ∀ u ∈ P.N, 1 ≤ P.vol u)
    (hne : R.Nonempty) : 0 < volOf P.vol R := by
  obtain ⟨u, hu⟩ := hne
  exact lt_of_lt_of_le (hvol u (hR hu)) (single_le_sum (fun _ _ => Nat.zero_le _) hu)

/-- **Deterministic part of Lemma 4.3 (peeling).** If every trial made while the loop runs is good,
then after `L` trials `v` is light (`R = ∅`) or heavy (`|N \ R| ≥ τ`). Each good trial either queries
the whole maximum class — which then stays empty — or at least `α/3 ≥ τ` nodes. -/
theorem light_or_heavy_of_good (hb : 1 < P.b) (hL : 0 < P.L) (hα : 6 ≤ P.α)
    (hτ : (P.τ : ℝ) ≤ P.α / 3) (hvol : ∀ u ∈ P.N, 1 ≤ P.vol u ∧ (P.vol u : ℝ) < P.b ^ P.L)
    (ω : Fin P.L → Fin P.s → Fin P.M)
    (hgood : ∀ t (ht : t < P.L), P.Running (P.stateR ω t) →
      P.Good (P.stateR ω t) (P.trialQ (P.stateR ω t) (ω ⟨t, ht⟩))) :
    P.stateR ω P.L = ∅ ∨ P.τ ≤ #(P.N \ P.stateR ω P.L) := by
  -- invariant: stopped, or few nonempty classes left
  have inv : ∀ t ≤ P.L, ¬ P.Running (P.stateR ω t) ∨ P.pot (P.stateR ω t) + t ≤ P.L := by
    intro t ht
    induction t with
    | zero =>
      right
      simp only [pot, add_zero]
      exact (card_filter_le _ _).trans (by simp)
    | succ t ih =>
      have htL : t < P.L := by omega
      by_cases hr : P.Running (P.stateR ω t)
      · set R := P.stateR ω t with hRdef
        set Q := P.trialQ R (ω ⟨t, htL⟩)
        have hRN : R ⊆ P.N := P.stateR_subset ω t
        have hnext : P.stateR ω (t + 1) = R \ Q := P.stateR_succ_of_running ω htL hr
        rw [hnext]
        obtain ⟨x, hx, hK, hheavy⟩ := P.maxClass_spec hb hL hvol hRN
        have hKne : (P.maxClass R).Nonempty := by
          rw [← card_pos]
          by_contra h0
          have hz : volOf P.vol (P.maxClass R) = 0 := by
            rw [Nat.not_lt, Nat.le_zero, card_eq_zero] at h0; rw [h0]; rfl
          have := P.volOf_pos hRN (fun u hu => (hvol u hu).1) hr.1
          rw [hz, mul_zero] at hheavy
          omega
        rcases subset_or_le_card_of_hit hKne hα (hgood t htL hr) with hsub | hcard
        · -- the class `x` is emptied
          right
          have hlt : P.pot (R \ Q) < P.pot R := by
            apply card_lt_card
            refine ⟨?_, ?_⟩
            · intro y hy
              simp only [mem_filter] at hy ⊢
              obtain ⟨hy1, u, hu, hcu⟩ := hy
              exact ⟨hy1, u, (mem_sdiff.mp hu).1, hcu⟩
            · intro hsub'
              obtain ⟨u, hu⟩ := hKne
              have hu' := hu
              rw [hK, mem_filter] at hu'
              have : x ∈ (range P.L).filter fun y => ∃ u ∈ R, cls P.vol P.b u = y :=
                mem_filter.mpr ⟨mem_range.mpr hx, u, hu'.1, hu'.2⟩
              obtain ⟨-, w, hw, hcw⟩ := mem_filter.mp (hsub' this)
              have hwK : w ∈ P.maxClass R := by
                rw [hK, mem_filter]; exact ⟨(mem_sdiff.mp hw).1, hcw⟩
              exact (mem_sdiff.mp hw).2 (hsub hwK)
          rcases ih (by omega) with h | h
          · exact absurd hr h
          · omega
        · -- at least `τ` nodes queried: the loop stops
          left
          intro hr'
          have hQ : Q ⊆ P.N \ (R \ Q) := by
            intro u hu
            have huR := P.trialQ_subset R _ hu
            simp only [mem_sdiff, not_and, not_not]
            exact ⟨hRN huR, fun _ => hu⟩
          have h1 : (P.τ : ℝ) ≤ #(Q ∩ P.maxClass R) := hτ.trans hcard
          have h2 : #(Q ∩ P.maxClass R) ≤ #(P.N \ (R \ Q)) :=
            (card_le_card inter_subset_left).trans (card_le_card hQ)
          have h3 : (P.τ : ℝ) ≤ #(P.N \ (R \ Q)) := h1.trans (by exact_mod_cast h2)
          have : P.τ ≤ #(P.N \ (R \ Q)) := by exact_mod_cast h3
          exact absurd hr'.2 (not_lt.mpr this)
      · left
        rw [P.stateR_succ_of_not_running ω hr]
        exact hr
  rcases inv P.L le_rfl with h | h
  · unfold Running at h
    rw [not_and_or, not_nonempty_iff_eq_empty, not_lt] at h
    exact h
  · left
    have hpot : P.pot (P.stateR ω P.L) = 0 := by omega
    rw [pot, card_eq_zero, filter_eq_empty_iff] at hpot
    rw [eq_empty_iff_forall_notMem]
    intro u hu
    have huN := P.stateR_subset ω P.L hu
    exact hpot (mem_range.mpr (cls_lt hb (hvol u huN).1 (hvol u huN).2)) ⟨u, hu, rfl⟩


omit [Fintype ι] [DecidableEq ι] in
lemma maxClass_nonempty (hb : 1 < P.b) (hL : 0 < P.L)
    (hvol : ∀ u ∈ P.N, 1 ≤ P.vol u ∧ (P.vol u : ℝ) < P.b ^ P.L) {R : Finset ι} (hR : R ⊆ P.N)
    (hne : R.Nonempty) : (P.maxClass R).Nonempty := by
  obtain ⟨x, -, -, hheavy⟩ := P.maxClass_spec hb hL hvol hR
  rw [nonempty_iff_ne_empty]
  intro h0
  have hz : volOf P.vol (P.maxClass R) = 0 := by rw [h0]; rfl
  have := P.volOf_pos hR (fun u hu => (hvol u hu).1) hne
  rw [hz, mul_zero] at hheavy
  omega

/-- **One trial is bad with small probability.** From any running state `R`, the probability that
some group of the maximum class is missed is at most `|N| (1 − θ)^s`, `θ = 1/(L α b)`. -/
theorem uprob_not_good_le (hb : 1 < P.b) (hL : 0 < P.L) (hα : 6 ≤ P.α)
    (hvol : ∀ u ∈ P.N, 1 ≤ P.vol u ∧ (P.vol u : ℝ) < P.b ^ P.L) {R : Finset ι} (hRN : R ⊆ P.N)
    (hr : P.Running R) :
    uprob (fun a : Fin P.s → Fin P.M => ¬ P.Good R (P.trialQ R a)) ≤
      #P.N * (1 - 1 / (P.L * P.α * P.b)) ^ P.s := by
  have hpos := P.volOf_pos hRN (fun u hu => (hvol u hu).1) hr.1
  have hdvd : volOf P.vol R ∣ P.M := Nat.dvd_factorial hpos (sum_le_sum_of_subset hRN)
  have h : 0 < volOf P.vol R ∧ volOf P.vol R ∣ P.M := ⟨hpos, hdvd⟩
  have hα0 : 0 < P.α := by linarith
  have hb0 : 0 < P.b := by linarith
  have hL1 : (1 : ℝ) ≤ P.L := by exact_mod_cast hL
  obtain ⟨x, -, hK, hheavy⟩ := P.maxClass_spec hb hL hvol hRN
  have hKne := P.maxClass_nonempty hb hL hvol hRN hr.1
  set K := P.maxClass R with hKdef
  set β := beta K P.α
  set q := numGroups K P.α
  set θ : ℝ := 1 / (P.L * P.α * P.b) with hθ
  have hKR : K ⊆ R := by rw [hK]; exact filter_subset _ _
  have hcls : ∀ u ∈ K, ∀ w ∈ K, (P.vol u : ℝ) < P.b * P.vol w := by
    intro u hu w hw
    rw [hK, mem_filter] at hu hw
    exact vol_lt_of_cls_eq hb (hvol u (hRN hu.1)).1 (hvol w (hRN hw.1)).1 (hu.2.trans hw.2.symm)
  -- reduce to the decoded samples
  have hstep : ∀ a : Fin P.s → Fin P.M, ¬ P.Good R (P.trialQ R a) →
      (fun f : Fin P.s → Edges P.vol R => ∃ l < q, ∀ i, (f i).1.1 ∉ group K β l)
        (fun i => decodeEdge R h (a i)) := by
    intro a ha
    simp only [Good, not_forall, not_nonempty_iff_eq_empty] at ha
    obtain ⟨l, hl, hempty⟩ := ha
    refine ⟨l, hl, fun i hi => ?_⟩
    have hmem : (decodeEdge R h (a i)).1.1 ∈ P.trialQ R a ∩ group K β l := by
      rw [mem_inter]
      refine ⟨?_, hi⟩
      simp only [trialQ, dite_eq_left_of_eq_true (eq_true h)]
      exact mem_image.mpr ⟨i, mem_univ _, rfl⟩
    rw [hempty] at hmem
    exact absurd hmem (notMem_empty _)
  refine (uprob_mono hstep).trans ((uprob_decode R h P.M_pos (fun f : Fin P.s → Edges P.vol R =>
    ∃ l < q, ∀ i, (f i).1.1 ∉ group K β l)).le.trans ?_)
  have hθ1 : θ ≤ 1 := by
    have h1 : (6 : ℝ) ≤ P.L * P.α := by nlinarith
    have h2 : (6 : ℝ) ≤ P.L * P.α * P.b := by nlinarith
    rw [hθ, div_le_one (by positivity)]
    linarith
  refine (uprob_exists_miss_le (group K β) (fun l _ => (group_subset K β l).trans hKR) hθ1
    (fun l hl => ?_) P.s).trans ?_
  · have hβ := beta_pos hKne hα0
    have hcard : #(group K β l) = β := card_group hβ ((Nat.le_div_iff_mul_le hβ).mp hl)
    have := volOf_group_ge hb hL hKR hcls hheavy (group_subset K β l) hα0 hcard
    rw [hθ, one_div_mul_eq_div]
    exact this
  · have hq : q ≤ #P.N :=
      (Nat.div_le_self _ _).trans ((card_le_card hKR).trans (card_le_card hRN))
    have h0 : (0 : ℝ) ≤ (1 - θ) ^ P.s := pow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hq) h0

/-- **Lemma 4.3 for one node.** With volumes in `[1, b^L)`, `α ≥ 6` and `τ ≤ α/3`, after the at most
`L = 2h` trials of the first step, node `v` is light (`R = ∅`: all neighbours queried) or heavy
(`|F_v| = |N \ R| ≥ τ`), except with probability at most `L · |N| · (1 − 1/(L α b))^s`. The trials
are adaptive; the bound is the union bound over trials of the conditional failure probability. -/
theorem lemma_4_3_node (hb : 1 < P.b) (hL : 0 < P.L) (hα : 6 ≤ P.α)
    (hτ : (P.τ : ℝ) ≤ P.α / 3) (hvol : ∀ u ∈ P.N, 1 ≤ P.vol u ∧ (P.vol u : ℝ) < P.b ^ P.L) :
    uprob (fun ω : Fin P.L → Fin P.s → Fin P.M =>
        ¬ (P.stateR ω P.L = ∅ ∨ P.τ ≤ #(P.N \ P.stateR ω P.L))) ≤
      P.L * (#P.N * (1 - 1 / (P.L * P.α * P.b)) ^ P.s) := by
  set p : ℝ := #P.N * (1 - 1 / (P.L * P.α * P.b)) ^ P.s
  let Bad : ℕ → (Fin P.L → Fin P.s → Fin P.M) → Prop := fun t ω =>
    ∃ ht : t < P.L, P.Running (P.stateR ω t) ∧
      ¬ P.Good (P.stateR ω t) (P.trialQ (P.stateR ω t) (ω ⟨t, ht⟩))
  have hsub : ∀ ω : Fin P.L → Fin P.s → Fin P.M,
      ¬ (P.stateR ω P.L = ∅ ∨ P.τ ≤ #(P.N \ P.stateR ω P.L)) → ∃ t ∈ range P.L, Bad t ω := by
    intro ω hω
    by_contra hno
    push Not at hno
    apply hω
    refine P.light_or_heavy_of_good hb hL hα hτ hvol ω (fun t ht hr => ?_)
    by_contra hg
    exact hno t (mem_range.mpr ht) ⟨ht, hr, hg⟩
  have hp : 0 ≤ p := by
    have : (0 : ℝ) ≤ 1 - 1 / (P.L * P.α * P.b) := by
      have hL1 : (1 : ℝ) ≤ P.L := by exact_mod_cast hL
      have h1 : (6 : ℝ) ≤ P.L * P.α := by nlinarith
      have h2 : (6 : ℝ) ≤ P.L * P.α * P.b := by nlinarith
      rw [sub_nonneg, div_le_one (by linarith)]
      linarith
    positivity
  have hbad : ∀ t < P.L, uprob (Bad t) ≤ p := by
    intro t ht
    let w : Fin P.L := ⟨t, ht⟩
    have hfib := uprob_and_le_fiber (α := fun _ : Fin P.L => Fin P.s → Fin P.M) w
      (A := fun _ => True) (B := Bad t) (fun _ _ => Iff.rfl) (q := p) (fun x => ?_)
    · simp only [true_and] at hfib
      refine hfib.trans ?_
      calc p * uprob (fun _ : Fin P.L → Fin P.s → Fin P.M => True) ≤ p * 1 :=
            mul_le_mul_of_nonneg_left (uprob_le_one _) hp
        _ = p := mul_one p
    · have hst : ∀ a, P.stateR (Function.update x w a) t = P.stateR x t :=
        fun a => P.stateR_update x w a t le_rfl
      by_cases hr : P.Running (P.stateR x t)
      · refine (uprob_mono fun a ha => ?_).trans
          (P.uprob_not_good_le hb hL hα hvol (P.stateR_subset x t) hr)
        obtain ⟨ht', -, hg⟩ := ha
        have hw : (⟨t, ht'⟩ : Fin P.L) = w := rfl
        rw [hst a, hw, Function.update_self] at hg
        exact hg
      · refine (uprob_mono (E' := fun _ => False) fun a ha => ?_).trans (uprob_false.le.trans hp)
        obtain ⟨-, hr', -⟩ := ha
        exact hr (hst a ▸ hr')
  refine (uprob_mono hsub).trans ((uprob_exists_le _ _).trans ?_)
  calc ∑ t ∈ range P.L, uprob (Bad t) ≤ ∑ _t ∈ range P.L, p :=
        sum_le_sum fun t ht => hbad t (mem_range.mp ht)
    _ = P.L * p := by simp

lemma card_trialQ_le (R : Finset ι) (a : Fin P.s → Fin P.M) : #(P.trialQ R a) ≤ P.s := by
  unfold trialQ
  split_ifs
  · exact card_queried_le _
  · simp

/-- **Corrected size bound per node (Lemma 4.7).** The loop only tests `|F_v| < τ` *between* trials,
and one trial adds up to `s` edges, so `|F_v| = |N \ R| < τ + s` — and not `O(τ)`: the last trial
may overshoot by `s = c² n^{2^j δ + ε} log³ n`, a factor `n^ε` more than the paper's count. -/
theorem card_F_lt (hτ : 0 < P.τ) (ω : Fin P.L → Fin P.s → Fin P.M) (t : ℕ) :
    #(P.N \ P.stateR ω t) < P.τ + P.s := by
  induction t with
  | zero => simp [stateR]; omega
  | succ t ih =>
    by_cases hr : t < P.L ∧ P.Running (P.stateR ω t)
    · rw [P.stateR_succ_of_running ω hr.1 hr.2]
      have hsub : P.N \ (P.stateR ω t \ P.trialQ (P.stateR ω t) (ω ⟨t, hr.1⟩)) ⊆
          (P.N \ P.stateR ω t) ∪ P.trialQ (P.stateR ω t) (ω ⟨t, hr.1⟩) := by
        intro u hu
        simp only [mem_sdiff, not_and, not_not, mem_union] at hu ⊢
        by_cases h : u ∈ P.stateR ω t
        · exact Or.inr (hu.2 h)
        · exact Or.inl ⟨hu.1, h⟩
      have h1 := (card_le_card hsub).trans (card_union_le _ _)
      have h2 := P.card_trialQ_le (P.stateR ω t) (ω ⟨t, hr.1⟩)
      have h3 := hr.2.2
      omega
    · rw [stateR, dite_eq_right_of_eq_false (eq_false hr)]
      exact ih

end Setup

end Podc.LocalMessageReduction
