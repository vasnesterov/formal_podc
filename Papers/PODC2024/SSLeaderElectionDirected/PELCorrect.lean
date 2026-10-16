import Papers.PODC2024.SSLeaderElectionDirected.PEL

/-!
# Partial correctness of PEL (Corollary 4, Lemmas 14, 15) and Theorem 3

Let `SC` be the unique source component and `ℓ ∈ SC` the process of `SC` with the smallest
identifier (`mid = ℓ.Id`). In every terminal configuration of PEL:

* Corollary 4: `p.MI.M = mid` for `p ∈ SC`;
* Lemma 14: `p.A.M = 1 ↔ p.MI.M = mid`;
* Lemma 15: `p.E.M = (0, mid)`, hence `L(p) = mid`, for every process `p` (both for the paper's
  `I_E` and for the fixed `I_E` used for unison).

`theorem3`: PEL is silent self-stabilizing for leader election under the distributed unfair daemon,
in every digraph with a unique source component, and is terminal after `3α + 3MAD + 6` rounds.
-/

set_option linter.unusedSectionVars false

open Podc.AtomicState

namespace Papers.PODC2024.SSLeaderElectionDirected

namespace CMAI

variable {V : Type*} [Fintype V] {G : Digraph V} {D : Type*} [LinearOrder D]

theorem minI_eq {J : V → D} {p : V} {c : D} (h1 : ∀ q, Anc G q p → c ≤ J q)
    (h2 : ∃ q, Anc G q p ∧ J q = c) : minI G J p = c := by
  obtain ⟨q, hq, hc⟩ := h2
  obtain ⟨q', hq', hq''⟩ := exists_minI (G := G) (I := J) p
  exact le_antisymm (hc ▸ minI_le hq) (hq'' ▸ h1 q' hq')

theorem minI_bool_eq_true {J : V → Bool} {p : V} :
    minI G J p = true ↔ ∀ q, Anc G q p → J q = true := by
  constructor
  · intro h q hq
    have := minI_le (G := G) (I := J) hq
    rw [h] at this
    revert this; cases J q <;> decide
  · intro h
    exact minI_eq (fun q hq => (h q hq).symm ▸ le_rfl) ⟨p, Anc.refl p, h p (Anc.refl p)⟩

end CMAI

namespace PEL

open CMAI

variable {V : Type*} [Fintype V] {G : Digraph V} {ID : Type*} [LinearOrder ID] {α : ℕ}
  {fixed : Bool} {ι : V → ID}

/-- In a terminal configuration of PEL (with `α ≥ MAD`), each layer holds its target keys. -/
theorem terminal_keys (hα : MADLe G α) {γ : V → PState ID α}
    (hγ : Terminal (next G α fixed ι) γ) :
    (∀ p, (γ p).mi.1 = target G ι p) ∧ (∀ p, (γ p).a.1 = target G (IA G γ) p) ∧
      (∀ p, (γ p).e.1 = target G (IE fixed ι γ) p) := by
  obtain ⟨h1, h2, h3⟩ := terminal_iff.mp hγ
  exact ⟨fun p => eq_target_of_terminal hα (CMAI.terminal_iff.mp h1) p,
    fun p => eq_target_of_terminal hα (CMAI.terminal_iff.mp h2) p,
    fun p => eq_target_of_terminal hα (CMAI.terminal_iff.mp h3) p⟩

/-- The process with the smallest identifier in a (source) component. -/
theorem exists_mid {SC : Set V} (hSC : IsSourceComponent G SC) :
    ∃ ℓ ∈ SC, ∀ x ∈ SC, ι ℓ ≤ ι x := by
  classical
  obtain ⟨ℓ, hℓ, h⟩ := (SC.toFinite.toFinset).exists_min_image ι
    (by simpa using hSC.nonempty)
  exact ⟨ℓ, by simpa using hℓ, fun x hx => h x (by simpa using hx)⟩

section Correctness

variable {SC : Set V} (hSC : IsSourceComponent G SC)
  (huniq : ∀ S, IsSourceComponent G S → S = SC) {ℓ : V} (hℓ : ℓ ∈ SC)
  (hℓmin : ∀ x ∈ SC, ι ℓ ≤ ι x)
include hSC huniq hℓ hℓmin

omit hℓmin in
theorem anc_mid (p : V) : Anc G ℓ p := subset_anc_of_unique hSC huniq p hℓ

omit huniq in
theorem minI_of_mem_SC {x : V} (hx : x ∈ SC) : minI G ι x = ι ℓ := by
  have hSCx := hSC.eq_anc hx
  refine minI_eq (fun q hq => hℓmin q ?_) ⟨ℓ, hSC.anc_of_mem hℓ hx, rfl⟩
  rw [hSCx]; exact hq

theorem minI_le_mid (p : V) : minI G ι p ≤ ι ℓ := minI_le (anc_mid hSC huniq hℓ p)

variable (hα : MADLe G α) {γ : V → PState ID α} (hγ : Terminal (next G α fixed ι) γ)
include hα hγ

/-- **Corollary 4.** -/
theorem corollary4 {x : V} (hx : x ∈ SC) : (γ x).mi.1.M = ι ℓ := by
  rw [(terminal_keys hα hγ).1 x]
  exact minI_of_mem_SC hSC hℓ hℓmin hx

/-- **Lemma 14.** `p.A.M = 1 ↔ p.MI.M = mid` in every terminal configuration. -/
theorem lemma14 (p : V) : (γ p).a.1.M = true ↔ (γ p).mi.1.M = ι ℓ := by
  obtain ⟨hmi, ha, -⟩ := terminal_keys hα hγ
  rw [ha p]
  simp only [target]
  rw [minI_bool_eq_true]
  constructor
  · intro h
    -- all ancestors of `p` agree with `p` on `MI.M`
    have hagree : ∀ q, Anc G q p → (γ q).mi.1.M = (γ p).mi.1.M := by
      intro q hq
      induction hq using Relation.ReflTransGen.head_induction_on with
      | refl => rfl
      | head hab hbc ih =>
        rename_i a b
        have hIA := h b hbc
        simp only [IA, decide_eq_true_eq] at hIA
        exact (hIA a hab).trans ih
    rw [← hagree ℓ (anc_mid hSC huniq hℓ p)]
    exact corollary4 hSC huniq hℓ hℓmin hα hγ hℓ
  · intro h
    have hall : ∀ q, Anc G q p → (γ q).mi.1.M = ι ℓ := by
      intro q hq
      rw [hmi q]
      apply le_antisymm (minI_le_mid hSC huniq hℓ hℓmin q)
      have := minI_mono (G := G) (I := ι) hq
      rw [hmi p] at h
      simp only [target] at h
      rw [← h]; exact this
    intro q hq
    simp only [IA, decide_eq_true_eq]
    intro x hx
    rw [hall q hq, hall x ((Anc.of_adj hx).trans hq)]

/-- **Lemma 15.** `p.E.M = (0, mid)` in every terminal configuration (for both choices of `I_E`). -/
theorem lemma15 (p : V) : (γ p).e.1.M = toLex (false, ι ℓ) := by
  obtain ⟨hmi, -, he⟩ := terminal_keys hα hγ
  rw [he p]
  simp only [target]
  apply minI_eq
  · intro q _
    simp only [IE]
    by_cases hq : (γ q).a.1.M = true
    · have h14 := (lemma14 hSC huniq hℓ hℓmin hα hγ q).mp hq
      rw [hq]
      apply Prod.Lex.toLex_le_toLex.mpr
      refine Or.inr ⟨rfl, ?_⟩
      cases fixed
      · simp [h14]
      · simp only [ite_true]
        rw [← h14, hmi q]
        exact minI_le_self q
    · have : (γ q).a.1.M = false := by simpa using hq
      rw [this]
      exact (Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by simp))).le
  · refine ⟨ℓ, anc_mid hSC huniq hℓ p, ?_⟩
    have h1 := corollary4 hSC huniq hℓ hℓmin hα hγ hℓ
    have h2 := (lemma14 hSC huniq hℓ hℓmin hα hγ ℓ).mpr h1
    simp only [IE, h2]
    cases fixed <;> simp [h1]

/-- In a terminal configuration, every process appoints `mid` as leader. -/
theorem leader_eq (p : V) : leader γ p = ι ℓ := by
  simp [leader, lemma15 hSC huniq hℓ hℓmin hα hγ p]

end Correctness

/-- The leader-election predicate: all processes appoint the identifier of one process. -/
def LEPred (ι : V → ID) (γ : V → PState ID α) : Prop := ∃ ℓ, ∀ p, leader γ p = ι ℓ

/-- **Theorem 3.** Assume `α ≥ MAD`. In every digraph with a unique source component, PEL (with
either `I_E`) is silent self-stabilizing for leader election under the distributed unfair daemon;
the leader is the process of the source component with the smallest identifier (uniqueness of
identifiers is not needed for this statement). -/
theorem theorem3 (hα : MADLe G α) {SC : Set V} (hSC : IsSourceComponent G SC)
    (huniq : ∀ S, IsSourceComponent G S → S = SC) :
    SilentSelfStab (next G α fixed ι) (IsExec (next G α fixed ι)) (LEPred ι) := by
  refine ⟨fun e ⟨S, hS⟩ => silent hS, fun γ hγ => ?_⟩
  obtain ⟨ℓ, hℓ, hℓmin⟩ := exists_mid (ι := ι) hSC
  exact ⟨ℓ, leader_eq hSC huniq hℓ hℓmin hα hγ⟩

/-- **Theorem 3 (stabilization time).** Every execution of PEL under the distributed unfair daemon
is terminal — hence legitimate — after at most `3α + 3·MAD + 6` rounds. -/
theorem theorem3_time {e : ℕ → V → PState ID α} {S : ℕ → Set V}
    (h : IsRun (next G α fixed ι) e S) (hα : MADLe G α) {r : ℕ → ℕ}
    (hr : RoundBounds (next G α fixed ι) e S r) :
    ∀ t, r (3 * α + 3 * mad G + 6) ≤ t → Terminal (next G α fixed ι) (e t) := by
  intro t ht
  exact terminal_within h madLe_mad (mad_le hα) hr t (by
    rw [show 3 * (α + mad G + 2) = 3 * α + 3 * mad G + 6 by ring]; exact ht)

end PEL

end Papers.PODC2024.SSLeaderElectionDirected
