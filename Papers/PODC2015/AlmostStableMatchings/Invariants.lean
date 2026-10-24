import Papers.PODC2015.AlmostStableMatchings.Algorithm

/-!
# Invariants of `ASM`; Lemmas 3.1 and 3.2

`Inv` collects the invariants of the reachable states of `ASM`:

* partner consistency (`pm m = some w ↔ pw w = some m`), `A ⊆ Q ⊆ N(m)`, `A ≠ ∅ ⇒` unmatched,
  partner `∈ Q`;
* `A` is a whole quantile of `Q`, and it is the best one (`A_best`, `A_closed`); a matched man's
  partner lies in his best nonempty quantile (`p_best`);
* `witness`: a woman who rejected `m` is matched to a man in the same or a better quantile;
* `rejected`: a matched woman has rejected every acceptable man in her partner's quantile or a
  worse one.

`Inv` holds initially and is preserved by `ProposalRound` and by the initialization of
`QuantileMatch`. From it we get Lemma 3.1 (women's partners only improve, strictly in quantile)
and Lemma 3.2 (after `QuantileMatch`, every `A` is empty).
-/

set_option linter.unusedSectionVars false

namespace Papers.PODC2015.AlmostStableMatchings

open Finset

variable {M W : Type*} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

namespace Prefs

variable (P : Prefs M W) (k : ℕ)

/-- Invariants of the reachable states. -/
structure Inv (s : St M W) : Prop where
  cons : ∀ m w, s.pm m = some w ↔ s.pw w = some m
  Q_sub : ∀ m, s.Q m ⊆ P.NM m
  A_sub : ∀ m, s.A m ⊆ s.Q m
  A_unm : ∀ m w, w ∈ s.A m → s.pm m = none
  p_mem : ∀ m w, s.pm m = some w → w ∈ s.Q m
  A_best : ∀ m, ∀ w ∈ s.A m, ∀ w' ∈ s.Q m, P.qM k m w ≤ P.qM k m w'
  A_closed : ∀ m, ∀ w ∈ s.A m, ∀ w' ∈ s.Q m, P.qM k m w' = P.qM k m w → w' ∈ s.A m
  p_best : ∀ m w, s.pm m = some w → ∀ w' ∈ s.Q m, P.qM k m w ≤ P.qM k m w'
  witness : ∀ m w, w ∈ P.NM m → w ∉ s.Q m →
    ∃ m', s.pw w = some m' ∧ P.qW k w m' ≤ P.qW k w m
  rejected : ∀ w m' m, s.pw w = some m' → m ∈ P.NW w → m ≠ m' →
    P.qW k w m' ≤ P.qW k w m → w ∉ s.Q m

variable {P k}

lemma Inv.mem_NM {s : St M W} (hI : P.Inv k s) {m : M} {w : W} (h : w ∈ s.Q m) :
    w ∈ P.man m := (P.mem_NM).1 (hI.Q_sub m h)

lemma Inv.pw_mem {s : St M W} (hI : P.Inv k s) {m : M} {w : W} (h : s.pw w = some m) :
    m ∈ P.woman w :=
  (P.mem_iff m w).1 (hI.mem_NM (hI.p_mem m w ((hI.cons m w).2 h)))

/-- A proposer is in a strictly better quantile than the woman's current partner. -/
lemma Inv.proposer_better {s : St M W} (hI : P.Inv k s) {m m' : M} {w : W} (hw : w ∈ s.A m)
    (hp : s.pw w = some m') : P.qW k w m < P.qW k w m' := by
  by_contra h
  have hne : m ≠ m' := by
    rintro rfl
    have := hI.A_unm m w hw
    rw [(hI.cons m w).2 hp] at this; cases this
  have hmem : m ∈ P.NW w := (P.mem_NW).2 ((P.mem_iff m w).1 (hI.mem_NM (hI.A_sub m hw)))
  exact hI.rejected w m' m hp hmem hne (not_lt.1 h) (hI.A_sub m hw)

theorem inv_init : P.Inv k P.init where
  cons m w := by simp [init, St.Q, St.A, St.pm]
  Q_sub m := by simp [init, St.Q, St.A, St.pm]
  A_sub m := by simp [init, St.Q, St.A, St.pm]
  A_unm m w := by simp [init, St.Q, St.A, St.pm]
  p_mem m w := by simp [init, St.Q, St.A, St.pm]
  A_best m := by simp [init, St.Q, St.A, St.pm]
  A_closed m := by simp [init, St.Q, St.A, St.pm]
  p_best m := by simp [init, St.Q, St.A, St.pm]
  witness m w h h' := by simp [init, St.Q] at h'; exact absurd (P.mem_NM.1 h) h'
  rejected w m' m := by simp [init, St.Q, St.A, St.pm]

/-! ## Unfolding `ProposalRound` -/

section PR

variable (mm : MMOracle M W) (s : St M W)

lemma rejects_eq_true {w : W} {p0 : Option M} {m : M} :
    P.rejects k w p0 m = true ↔ ∃ m0, p0 = some m0 ∧ m ∈ P.NW w ∧ m ≠ m0 ∧
      P.qW k w m0 ≤ P.qW k w m := by
  cases p0 <;> simp [rejects]

lemma rejects_eq_false {w : W} {p0 : Option M} {m : M} :
    P.rejects k w p0 m = false ↔ ¬ ∃ m0, p0 = some m0 ∧ m ∈ P.NW w ∧ m ≠ m0 ∧
      P.qW k w m0 ≤ P.qW k w m := by
  rw [← rejects_eq_true]; simp

lemma mem_Q_prStep {m : M} {w : W} : w ∈ (P.prStep k mm s).Q m ↔
    w ∈ s.Q m ∧ P.rejects k w ((P.mmOut k mm s).pw w) m = false := by
  simp [prStep, manUpdate, St.Q]

lemma mem_A_prStep {m : M} {w : W} : w ∈ (P.prStep k mm s).A m ↔
    (P.mmOut k mm s).pm m = none ∧ w ∈ s.A m ∧
      P.rejects k w ((P.mmOut k mm s).pw w) m = false := by
  simp only [prStep, manUpdate, St.A]
  cases (P.mmOut k mm s).pm m <;> simp

lemma pm_prStep_eq_some {m : M} {w : W} : (P.prStep k mm s).pm m = some w ↔
    (P.mmOut k mm s).pm m = some w ∨ ((P.mmOut k mm s).pm m = none ∧ s.pm m = some w ∧
      P.rejects k w ((P.mmOut k mm s).pw w) m = false) := by
  simp only [prStep, manUpdate, St.pm]
  cases (P.mmOut k mm s).pm m <;> cases (s.man m).p <;> simp [Option.filter]
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨rfl, h1⟩
  · rintro ⟨rfl, h1⟩; exact ⟨h1, rfl⟩

lemma pm_prStep_eq_none {m : M} : (P.prStep k mm s).pm m = none ↔
    (P.mmOut k mm s).pm m = none ∧ ∀ w, s.pm m = some w →
      P.rejects k w ((P.mmOut k mm s).pw w) m = true := by
  simp only [prStep, manUpdate, St.pm]
  cases (P.mmOut k mm s).pm m <;> cases (s.man m).p <;> simp [Option.filter]

lemma pw_prStep {w : W} : (P.prStep k mm s).pw w =
    ((P.mmOut k mm s).pw w).or (s.pw w) := rfl

lemma pw_prStep_eq_some {w : W} {m : M} : (P.prStep k mm s).pw w = some m ↔
    (P.mmOut k mm s).pw w = some m ∨ ((P.mmOut k mm s).pw w = none ∧ s.pw w = some m) := by
  rw [pw_prStep]; cases (P.mmOut k mm s).pw w <;> simp

/-- The subroutine's partners: a man matched in `M₀` proposed and was accepted. -/
lemma mmOut_pm {m : M} {w : W} (h : (P.mmOut k mm s).pm m = some w) :
    m ∈ P.proposers s w ∧ ∀ m' ∈ P.proposers s w, P.qW k w m ≤ P.qW k w m' := by
  have := ((mm.isMaximal (P.acceptGraph k s)).2.1 m w h)
  simpa [acceptGraph, accepts] using this

lemma mmOut_cons {m : M} {w : W} :
    (P.mmOut k mm s).pm m = some w ↔ (P.mmOut k mm s).pw w = some m :=
  (mm.isMaximal (P.acceptGraph k s)).1 m w

lemma mem_proposers {m : M} {w : W} : m ∈ P.proposers s w ↔ m ∈ P.NW w ∧ w ∈ s.A m := by
  simp [proposers]

/-- Maximality of `M₀`, specialized: an accepted proposal has a matched endpoint. -/
lemma mmOut_max {m : M} {w : W} (hm : m ∈ P.proposers s w)
    (hb : ∀ m' ∈ P.proposers s w, P.qW k w m ≤ P.qW k w m') :
    (P.mmOut k mm s).pm m ≠ none ∨ (P.mmOut k mm s).pw w ≠ none :=
  (mm.isMaximal (P.acceptGraph k s)).2.2 m w (by
    simp only [acceptGraph, accepts, decide_eq_true_eq]; exact ⟨hm, hb⟩)

variable {mm s}

lemma mmOut_pw {w : W} {m0 : M} (h : (P.mmOut k mm s).pw w = some m0) :
    m0 ∈ P.proposers s w ∧ ∀ m' ∈ P.proposers s w, P.qW k w m0 ≤ P.qW k w m' :=
  P.mmOut_pm mm s ((P.mmOut_cons mm s).2 h)

lemma mmOut_pm_A {m : M} {w : W} (h : (P.mmOut k mm s).pm m = some w) :
    w ∈ s.A m := ((P.mem_proposers s).1 (P.mmOut_pm mm s h).1).2

lemma Inv.mmOut_pw_better (hI : P.Inv k s) {w : W} {m0 m' : M}
    (h : (P.mmOut k mm s).pw w = some m0) (hp : s.pw w = some m') :
    P.qW k w m0 < P.qW k w m' :=
  hI.proposer_better ((P.mem_proposers s).1 (P.mmOut_pw h).1).2 hp

lemma mmOut_pm_unmatched (hI : P.Inv k s) {m : M} {w : W}
    (h : (P.mmOut k mm s).pm m = some w) : s.pm m = none :=
  hI.A_unm m w ((P.mem_proposers s).1 (P.mmOut_pm mm s h).1).2

/-- `ProposalRound` preserves the invariants. -/
theorem Inv.prStep (hI : P.Inv k s) : P.Inv k (P.prStep k mm s) where
  cons m w := by
    rw [pm_prStep_eq_some, pw_prStep_eq_some, P.mmOut_cons mm s]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · refine Or.inr ⟨?_, (hI.cons m w).1 h2⟩
        by_contra hne
        obtain ⟨m0, hm0⟩ := Option.ne_none_iff_exists'.1 hne
        have hb := hI.mmOut_pw_better hm0 ((hI.cons m w).1 h2)
        have hm0m : m ≠ m0 := by
          rintro rfl; rw [← P.mmOut_cons mm s] at hm0; rw [hm0] at h1; cases h1
        rw [hm0, rejects_eq_false] at h3
        exact h3 ⟨m0, rfl, (P.mem_NW).2 (hI.pw_mem ((hI.cons m w).1 h2)), hm0m, hb.le⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨?_, (hI.cons m w).2 h2, by rw [h1]; rfl⟩
        by_contra hne
        obtain ⟨w', hw'⟩ := Option.ne_none_iff_exists'.1 hne
        have := mmOut_pm_unmatched hI hw'
        rw [(hI.cons m w).2 h2] at this; cases this
  Q_sub m := fun w hw => hI.Q_sub m ((mem_Q_prStep mm s).1 hw).1
  A_sub m := fun w hw => by
    rw [mem_A_prStep] at hw; rw [mem_Q_prStep]; exact ⟨hI.A_sub m hw.2.1, hw.2.2⟩
  A_unm m w hw := by
    rw [mem_A_prStep] at hw
    rw [pm_prStep_eq_none]
    refine ⟨hw.1, fun w' hw' => ?_⟩
    rw [hI.A_unm m w hw.2.1] at hw'; cases hw'
  p_mem m w h := by
    rw [mem_Q_prStep]
    rcases (pm_prStep_eq_some mm s).1 h with h | ⟨-, h2, h3⟩
    · refine ⟨hI.A_sub m (mmOut_pm_A h), ?_⟩
      rw [(P.mmOut_cons mm s).1 h, rejects_eq_false]
      rintro ⟨m0, e, -, hne, -⟩; cases e; exact hne rfl
    · exact ⟨hI.p_mem m w h2, h3⟩
  A_best m w hw w' hw' :=
    hI.A_best m w ((mem_A_prStep mm s).1 hw).2.1 w' ((mem_Q_prStep mm s).1 hw').1
  A_closed m w hw w' hw' he := by
    rw [mem_A_prStep] at hw ⊢; rw [mem_Q_prStep] at hw'
    exact ⟨hw.1, hI.A_closed m w hw.2.1 w' hw'.1 he, hw'.2⟩
  p_best m w h w' hw' := by
    have hw'Q := ((mem_Q_prStep mm s).1 hw').1
    rcases (pm_prStep_eq_some mm s).1 h with h | ⟨-, h2, -⟩
    · exact hI.A_best m w (mmOut_pm_A h) w' hw'Q
    · exact hI.p_best m w h2 w' hw'Q
  witness m w hN hQ := by
    rw [mem_Q_prStep, not_and_or, Bool.not_eq_false, rejects_eq_true] at hQ
    rcases hQ with hQ | ⟨m0, h0, -, -, hle⟩
    · obtain ⟨m', hm', hle⟩ := hI.witness m w hN hQ
      cases h0 : (P.mmOut k mm s).pw w with
      | none => exact ⟨m', by rw [pw_prStep, h0]; simpa using hm', hle⟩
      | some m0 =>
        exact ⟨m0, by rw [pw_prStep, h0]; rfl, (hI.mmOut_pw_better h0 hm').le.trans hle⟩
    · exact ⟨m0, by rw [pw_prStep, h0]; rfl, hle⟩
  rejected w m' m h hN hne hle := by
    rw [mem_Q_prStep, not_and_or]
    rcases (pw_prStep_eq_some mm s).1 h with h | ⟨-, h2⟩
    · right; rw [h, Bool.not_eq_false, rejects_eq_true]; exact ⟨m', rfl, hN, hne, hle⟩
    · left; exact hI.rejected w m' m h2 hN hne hle

/-! ## Basic monotonicity of `ProposalRound` -/

lemma Q_prStep_subset (m : M) : (P.prStep k mm s).Q m ⊆ s.Q m :=
  fun _ h => ((mem_Q_prStep mm s).1 h).1

lemma A_prStep_subset (m : M) : (P.prStep k mm s).A m ⊆ s.A m :=
  fun _ h => ((mem_A_prStep mm s).1 h).2.1

/-- A man who is unmatched before and matched after a `ProposalRound` was proposing. -/
lemma A_nonempty_of_newly_matched {m : M} (h0 : s.pm m = none)
    (h1 : (P.prStep k mm s).pm m ≠ none) : (s.A m).Nonempty := by
  rw [ne_eq, pm_prStep_eq_none, not_and_or] at h1
  rcases h1 with h1 | h1
  · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h1
    exact ⟨w, ((P.mem_proposers s).1 (P.mmOut_pm mm s hw).1).2⟩
  · exact absurd (fun w hw => by rw [h0] at hw; cases hw) h1

/-- A woman's new partner was proposing to her. -/
lemma pw_prStep_new {w : W} {m : M} (h : (P.prStep k mm s).pw w = some m)
    (hne : (P.prStep k mm s).pw w ≠ s.pw w) : w ∈ s.A m := by
  rcases (pw_prStep_eq_some mm s).1 h with h' | ⟨-, h2⟩
  · exact ((P.mem_proposers s).1 (P.mmOut_pw h').1).2
  · exact absurd (h.trans h2.symm) hne

end PR

/-! ## The woman's potential `ψ` and Lemma 3.1 -/

variable (P k) in
/-- `ψ_w`: the quantile of `w`'s partner, `k + 1` if unmatched. -/
def psi (s : St M W) (w : W) : ℕ :=
  match s.pw w with
  | none => k + 1
  | some m => P.qW k w m

variable (P k) in
lemma psi_le (hk : 1 ≤ k) {s : St M W} (hI : P.Inv k s) (w : W) : P.psi k s w ≤ k + 1 := by
  unfold psi
  split
  · exact le_rfl
  · rename_i m h; exact (Finset.mem_Icc.1 (P.qW_mem_Icc hk (hI.pw_mem h))).2.trans (by omega)

variable (P k) in
lemma one_le_psi (hk : 1 ≤ k) {s : St M W} (hI : P.Inv k s) (w : W) : 1 ≤ P.psi k s w := by
  unfold psi
  split
  · omega
  · rename_i m h; exact (Finset.mem_Icc.1 (P.qW_mem_Icc hk (hI.pw_mem h))).1

/-- **Lemma 3.1 (monotonicity).** After a `ProposalRound`, a matched woman stays matched, her
partner's quantile does not get worse, and if her partner changes, the new one is in a strictly
better quantile (in particular she accepts only strictly better proposals). -/
theorem lemma_3_1 {mm : MMOracle M W} {s : St M W} (hk : 1 ≤ k) (hI : P.Inv k s) (w : W) :
    (s.pw w ≠ none → (P.prStep k mm s).pw w ≠ none) ∧
    ((P.prStep k mm s).pw w ≠ s.pw w → P.psi k (P.prStep k mm s) w < P.psi k s w) := by
  refine ⟨fun h => by rw [pw_prStep]; cases (P.mmOut k mm s).pw w <;> simpa using h, fun hne => ?_⟩
  unfold psi
  rw [pw_prStep] at hne ⊢
  cases h0 : (P.mmOut k mm s).pw w with
  | none => simp [h0] at hne
  | some m0 =>
    simp only [Option.some_or]
    cases hp : s.pw w with
    | none =>
      have := (Finset.mem_Icc.1 (P.qW_mem_Icc hk (P.mem_NW.1
        ((P.mem_proposers s).1 (P.mmOut_pw h0).1).1))).2
      simp only; omega
    | some m' => exact hI.mmOut_pw_better h0 hp

lemma psi_prStep_le {mm : MMOracle M W} {s : St M W} (hk : 1 ≤ k) (hI : P.Inv k s) (w : W) :
    P.psi k (P.prStep k mm s) w ≤ P.psi k s w := by
  by_cases h : (P.prStep k mm s).pw w = s.pw w
  · unfold psi; rw [h]
  · exact ((lemma_3_1 hk hI w).2 h).le

/-! ## Initialization of `QuantileMatch` -/

section Init

variable {act : Finset M} {s : St M W}

@[simp] lemma initQM_Q (m : M) : (P.initQM k act s).Q m = s.Q m := by
  simp only [initQM, St.Q]; split_ifs <;> rfl

@[simp] lemma initQM_pm (m : M) : (P.initQM k act s).pm m = s.pm m := by
  simp only [initQM, St.pm]; split_ifs <;> rfl

@[simp] lemma initQM_pw : (P.initQM k act s).pw = s.pw := rfl

lemma initQM_A (m : M) : (P.initQM k act s).A m =
    if m ∈ act ∧ s.pm m = none then P.bestQ k m (s.Q m) else s.A m := by
  simp only [initQM, St.A]; split_ifs <;> rfl

lemma mem_bestQ {m : M} {Q : Finset W} {w : W} :
    w ∈ P.bestQ k m Q ↔ w ∈ Q ∧ ∀ w' ∈ Q, P.qM k m w ≤ P.qM k m w' := by
  simp [bestQ]

theorem Inv.initQM (hI : P.Inv k s) : P.Inv k (P.initQM k act s) where
  cons m w := by simpa using hI.cons m w
  Q_sub m := by simpa using hI.Q_sub m
  A_sub m := by
    rw [initQM_A, initQM_Q]; split_ifs
    · exact Finset.filter_subset _ _
    · exact hI.A_sub m
  A_unm m w := by
    rw [initQM_A, initQM_pm]; split_ifs with h
    · exact fun _ => h.2
    · exact hI.A_unm m w
  p_mem m w := by simpa using hI.p_mem m w
  A_best m w hw w' hw' := by
    rw [initQM_A] at hw; rw [initQM_Q] at hw'; split_ifs at hw
    · exact (mem_bestQ.1 hw).2 w' hw'
    · exact hI.A_best m w hw w' hw'
  A_closed m w hw w' hw' he := by
    rw [initQM_A] at hw ⊢; rw [initQM_Q] at hw'; split_ifs at hw ⊢
    · exact mem_bestQ.2 ⟨hw', fun w'' h'' => he ▸ (mem_bestQ.1 hw).2 w'' h''⟩
    · exact hI.A_closed m w hw w' hw' he
  p_best m w h := by simpa using hI.p_best m w (by simpa using h)
  witness m w h := by simpa using hI.witness m w h
  rejected w m' m := by simpa using hI.rejected w m' m

end Init

lemma Inv.prStep_iterate {mm : MMOracle M W} {s : St M W} (hI : P.Inv k s) (t : ℕ) :
    P.Inv k ((P.prStep k mm)^[t] s) := by
  induction t generalizing s with
  | zero => exact hI
  | succ t ih => rw [Function.iterate_succ_apply]; exact ih hI.prStep

lemma Inv.quantileMatch {mm : MMOracle M W} {act : Finset M} {s : St M W} (hI : P.Inv k s) :
    P.Inv k (P.quantileMatch k mm act s) := hI.initQM.prStep_iterate k

lemma Inv.outer {mm : MMOracle M W} {ℓ i : ℕ} {s : St M W} (hI : P.Inv k s) :
    P.Inv k (P.outer k mm ℓ i s) := by
  unfold Prefs.outer
  generalize P.active i s = act
  induction ℓ generalizing s with
  | zero => exact hI
  | succ t ih => rw [Function.iterate_succ_apply]; exact ih hI.quantileMatch

lemma inv_stage (mm : MMOracle M W) (ℓ : ℕ) : ∀ i, P.Inv k (P.stage k mm ℓ i)
  | 0 => inv_init
  | i + 1 => (inv_stage mm ℓ i).outer

/-! ## Lemma 3.2 -/

/-- One `ProposalRound` raises the least quantile of the proposers to each woman: if every
proposal `(m, w)` has `q^w(m) > t`, then afterwards every proposal has `q^w(m) > t + 1`. -/
lemma prStep_quantile_gt {mm : MMOracle M W} {s : St M W} (hI : P.Inv k s) {t : ℕ}
    (ht : ∀ m w, w ∈ s.A m → t < P.qW k w m) :
    ∀ m w, w ∈ (P.prStep k mm s).A m → t + 1 < P.qW k w m := by
  intro m w hw
  rw [mem_A_prStep] at hw
  obtain ⟨hμ, hwA, hrej⟩ := hw
  have h1 := ht m w hwA
  by_contra hc
  have heq : P.qW k w m = t + 1 := by omega
  have hprop : m ∈ P.proposers s w := (P.mem_proposers s).2
    ⟨P.mem_NW.2 ((P.mem_iff m w).1 (hI.mem_NM (hI.A_sub m hwA))), hwA⟩
  have hbest : ∀ m' ∈ P.proposers s w, P.qW k w m ≤ P.qW k w m' := by
    intro m' hm'
    have := ht m' w ((P.mem_proposers s).1 hm').2; omega
  rcases P.mmOut_max mm s hprop hbest with h | h
  · exact h hμ
  · obtain ⟨m0, hm0⟩ := Option.ne_none_iff_exists'.1 h
    have hne : m ≠ m0 := by
      rintro rfl; rw [← P.mmOut_cons mm s] at hm0; rw [hm0] at hμ; cases hμ
    rw [hm0, rejects_eq_false] at hrej
    exact hrej ⟨m0, rfl, ((P.mem_proposers s).1 hprop).1, hne, (P.mmOut_pw hm0).2 m hprop⟩

/-- **Lemma 3.2 (QuantileMatch guarantee).** `k` iterations of `ProposalRound` empty every `A`
(from any reachable state). -/
theorem lemma_3_2 {mm : MMOracle M W} {s : St M W} (hk : 1 ≤ k) (hI : P.Inv k s) (m : M) :
    ((P.prStep k mm)^[k] s).A m = ∅ := by
  have key : ∀ t, ∀ m w, w ∈ ((P.prStep k mm)^[t] s).A m → t < P.qW k w m := by
    intro t
    induction t with
    | zero =>
      intro m w hw
      exact (Finset.mem_Icc.1 (P.qW_mem_Icc hk ((P.mem_iff m w).1
        (hI.mem_NM (hI.A_sub m hw))))).1
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact prStep_quantile_gt (hI.prStep_iterate t) ih
  refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
  have h1 := key k m w hw
  have hI' := hI.prStep_iterate (mm := mm) k
  have h2 := (Finset.mem_Icc.1 (P.qW_mem_Icc hk ((P.mem_iff m w).1
    (hI'.mem_NM (hI'.A_sub m hw))))).2
  omega

lemma quantileMatch_A {mm : MMOracle M W} {act : Finset M} {s : St M W} (hk : 1 ≤ k)
    (hI : P.Inv k s) (m : M) : (P.quantileMatch k mm act s).A m = ∅ :=
  lemma_3_2 hk hI.initQM m

end Prefs

end Papers.PODC2015.AlmostStableMatchings
