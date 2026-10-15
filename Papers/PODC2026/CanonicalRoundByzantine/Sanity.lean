import Cslib.Computability.Distributed.Byzantine.CanonicalRounds.Liveness
import Papers.PODC2026.CanonicalRoundByzantine.Problems

/-!
# Non-vacuity: one-round crusader agreement for `n > 5f`

[AFW26] H. Attiya, I. Flam, J. L. Welch. *Why Canonical-Round Algorithms Fail for Optimal Byzantine
Resilience.* PODC 2026.

The paper shows that for `3f < n ≤ 5f` no canonical-round algorithm solves a nontrivial
convergence problem (e.g. crusader agreement) with a bounded number of rounds (Theorems 1 and 7),
and remarks (abstract, Section 6) that bounded canonical-round algorithms *do* exist for `n > 5f`.
This file checks that remark in our model (`Cslib.Byzantine.CanonicalRounds`), which guards the impossibility
results against being vacuously true there (e.g. because of an over-restrictive notion of
admissibility or of round complexity), and shows that the resilience threshold `5f` of
Theorems 1/7 is sharp for crusader agreement.

`caAlg n f` is a deterministic, communication-closed, one-round canonical-round algorithm: every
process sends its input in round 1; once the communication-closed view of its history contains
round-1 messages from `n - f` senders, it decides `(w, 1)` if some value `w` was received (in
round-1 messages) from at least `n - 2f` senders, and `(⊥, 0)` otherwise.

* `caAlg_commClosed`: it is communication-closed (Section 3.2).
* `caAlg_safe`: for `n > 5f` it is safe for crusader agreement (`connectedConsensusSpec 1`).
  Agreement uses exactly `n > 5f`: two different non-`⊥` decisions would need
  `2(n - 2f - |F|)` correct processes among `n - |F|`.
* `caAlg_allDecideBy`, `caAlg_rounds`, `caAlg_expRounds`: in every admissible execution every
  correct process decides in its round `1` (for every `n`, `f`), so the (expected) round complexity
  is at most `1` for every adversary and every tape distribution.
* `rrAdv_admissible` (in `Cslib/Computability/Distributed/Byzantine/CanonicalRounds/Liveness.lean`) provides admissible adversaries for
  any faulty set of size `≤ f`, so these statements are not vacuous; `caAlg_allDecide_rrAdv`.
* `exists_bounded_crusader`: the summary statement contrasting Theorems 1/7.

Design choice: a value `w` is counted for a sender `q` if *some* round-1 message of `q` in the
view carries `w` (`valSenders`); a Byzantine sender may thus be counted for several values, which
does not hurt the counting arguments, and avoids selecting "the first" message of each sender.
-/

namespace Podc2026.CanonicalRound

open Cslib.Byzantine.CanonicalRounds Classical

variable {n : ℕ} {V R : Type*}

/-- The processes from which a round-1 message with content `w` is in the history `l`. -/
noncomputable def valSenders (w : V) (l : Log n R V) : Finset (Fin n) :=
  Finset.univ.filter fun q => Entry.recv q 1 w ∈ l

theorem mem_valSenders {w : V} {l : Log n R V} {q : Fin n} :
    q ∈ valSenders w l ↔ Entry.recv q 1 w ∈ l := by
  simp [valSenders]

/-- The decision rule of `caAlg` (applied to the communication-closed view of the history). -/
noncomputable def caRule (n f : ℕ) (l : Log n R V) : Option (Option V × ℕ) :=
  if n - f ≤ (senders 1 l).card then
    if h : ∃ w, n - 2 * f ≤ (valSenders w l).card then some (some h.choose, 1)
    else some (none, 0)
  else none

/-- One-round crusader agreement as a canonical-round algorithm: send the input; once round-1
messages from `n - f` senders are in the communication-closed view, decide `(w, 1)` if `w` was
received from `n - 2f` of them, and `(⊥, 0)` otherwise. -/
noncomputable def caAlg (n f : ℕ) : CanonAlg n V R V (Option V × ℕ) where
  msg _ v _ := v
  dec _ _ h := caRule n f (ccView h)

/-- `caAlg` is communication-closed (Section 3.2). -/
theorem caAlg_commClosed (f : ℕ) : (caAlg n f (V := V) (R := R)).CommClosed := by
  intro p v l l' h
  exact ⟨rfl, by simp only [caAlg, h]⟩

/-! ### Safety -/

/-- A history is *truthful* if every round-1 message from a correct sender carries its input. -/
def Truthful (F : Finset (Fin n)) (I : Fin n → V) (l : Log n R V) : Prop :=
  ∀ q ∉ F, ∀ w, Entry.recv q 1 w ∈ l → w = I q

theorem caRule_eq_some {f : ℕ} {l : Log n R V} {o : Option V × ℕ} (h : caRule n f l = some o) :
    n - f ≤ (senders 1 l).card ∧
    ((∃ w, o = (some w, 1) ∧ n - 2 * f ≤ (valSenders w l).card) ∨
      (o = (none, 0) ∧ ∀ w, (valSenders w l).card < n - 2 * f)) := by
  unfold caRule at h
  split_ifs at h with h1 h2
  · cases h; exact ⟨h1, Or.inl ⟨_, rfl, h2.choose_spec⟩⟩
  · cases h; push Not at h2; exact ⟨h1, Or.inr ⟨rfl, h2⟩⟩

theorem caRule_isSome {f : ℕ} {l : Log n R V} (h : n - f ≤ (senders 1 l).card) :
    (caRule n f l).isSome := by
  unfold caRule
  split_ifs <;> rfl

/-- Correct senders counted for `w` have input `w`. -/
theorem card_valSenders_le {F : Finset (Fin n)} {I : Fin n → V} {l : Log n R V}
    (hl : Truthful F I l) (w : V) :
    (valSenders w l).card ≤ (Finset.univ.filter fun q => q ∉ F ∧ I q = w).card + F.card := by
  refine le_trans (Finset.card_le_card_sdiff_add_card (t := F)) (Nat.add_le_add_right
    (Finset.card_le_card fun q hq => ?_) _)
  rw [Finset.mem_sdiff, mem_valSenders] at hq
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hq.2, (hl q hq.2 w hq.1).symm⟩

/-- Agreement: with `n > 5f`, two truthful views cannot both have `n - 2f` senders for different
values. -/
theorem eq_of_heavy {f : ℕ} (hn : 5 * f < n) {F : Finset (Fin n)} (hF : F.card ≤ f)
    {I : Fin n → V} {l l' : Log n R V} (hl : Truthful F I l) (hl' : Truthful F I l') {v w : V}
    (hv : n - 2 * f ≤ (valSenders v l).card) (hw : n - 2 * f ≤ (valSenders w l').card) :
    v = w := by
  by_contra hvw
  have h1 := card_valSenders_le hl v
  have h2 := card_valSenders_le hl' w
  have hdisj : Disjoint (Finset.univ.filter fun q => q ∉ F ∧ I q = v)
      (Finset.univ.filter fun q => q ∉ F ∧ I q = w) := by
    rw [Finset.disjoint_filter]
    rintro q - ⟨-, rfl⟩ ⟨-, h⟩
    exact hvw h
  have hsub : (Finset.univ.filter fun q => q ∉ F ∧ I q = v) ∪
      (Finset.univ.filter fun q => q ∉ F ∧ I q = w) ⊆ Fᶜ := by
    intro q hq
    simp only [Finset.mem_union, Finset.mem_filter] at hq
    rw [Finset.mem_compl]; rcases hq with h | h <;> exact h.2.1
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_compl, Fintype.card_fin] at h3
  omega

/-- Validity: a value with `n - 2f > f` senders in a truthful view is the input of a correct
process. -/
theorem exists_correct_of_heavy {f : ℕ} (hn : 3 * f < n) {F : Finset (Fin n)} (hF : F.card ≤ f)
    {I : Fin n → V} {l : Log n R V} (hl : Truthful F I l) {w : V}
    (hw : n - 2 * f ≤ (valSenders w l).card) : ∃ q ∉ F, I q = w := by
  by_contra hc
  push Not at hc
  have : valSenders w l ⊆ F := fun q hq => by
    by_contra hqF
    exact hc q hqF (hl q hqF w (mem_valSenders.1 hq)).symm
  have := Finset.card_le_card this
  omega

/-- If all correct processes have input `I p`, a truthful view with `n - f` round-1 senders has
`n - 2f` senders for `I p`. -/
theorem heavy_of_unanimous {f : ℕ} {F : Finset (Fin n)} (hF : F.card ≤ f) {I : Fin n → V}
    {l : Log n R V} (hl : Truthful F I l) {p : Fin n}
    (hI : ∀ q ∉ F, I q = I p) (hS : n - f ≤ (senders 1 l).card) :
    n - 2 * f ≤ (valSenders (I p) l).card := by
  have hsub : senders 1 l \ F ⊆ valSenders (I p) l := by
    intro q hq
    rw [Finset.mem_sdiff, mem_senders] at hq
    obtain ⟨⟨m, hm⟩, hqF⟩ := hq
    rw [mem_valSenders, ← hI q hqF, ← hl q hqF m hm]
    exact hm
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_le_card_sdiff_add_card (s := senders 1 l) (t := F)
  omega

/-- Views of correct processes are truthful: a correct sender's round-1 message carries its
input (`msg` is constant). -/
theorem truthful_ccView (f : ℕ) (I : Fin n → V) (ρ : Tape n R) (A : Adversary n R V) (k : ℕ)
    (p : Fin n) {h : Log n R V} (hh : h <+: ((caAlg n f).exec f I ρ A k).log p) :
    Truthful A.F I (ccView h) := by
  intro q hq w hw
  have hw' := hh.subset ((ccView_sublist h).subset hw)
  obtain ⟨_, _, _, _, hm⟩ := (caAlg n f).exists_msg_of_recv f I ρ A k hq hw'
  exact hm

/-- **Safety of `caAlg`.** For `n > 5f`, `caAlg` is safe for crusader agreement
(`connectedConsensusSpec 1`): at every prefix of every admissible execution, decisions are in
`{(⊥, 0)} ∪ {(v, 1)}`, non-`⊥` decisions of correct processes agree and are inputs of correct
processes, and if all correct inputs are equal every correct decision has grade `1`. -/
theorem caAlg_safe {f : ℕ} (hn : 5 * f < n) :
    (caAlg n f (V := V) (R := R)).Safe f (connectedConsensusSpec 1) := by
  intro I A hA ρ k
  have hF := hA.1
  have key : ∀ p o, (caAlg n f).decision p (I p) (((caAlg n f).exec f I ρ A k).log p) = some o →
      ∃ l : Log n R V, Truthful A.F I l ∧ caRule n f l = some o := by
    intro p o hd
    obtain ⟨h', hh', he⟩ := List.exists_of_findSome?_eq_some hd
    exact ⟨ccView h', truthful_ccView f I ρ A k p (List.mem_inits _ _ |>.1 hh'), he⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p _ a g hd
    obtain ⟨l, -, hl⟩ := key p _ hd
    rcases (caRule_eq_some hl).2 with ⟨w, hw, -⟩ | ⟨hw, -⟩
    · cases hw; exact Or.inr ⟨by simp, le_rfl, le_rfl⟩
    · cases hw; exact Or.inl ⟨rfl, rfl⟩
  · intro p _ q _ a g b g' hdp hdq
    obtain ⟨l, hlt, hl⟩ := key p _ hdp
    obtain ⟨l', hlt', hl'⟩ := key q _ hdq
    rcases (caRule_eq_some hl).2 with ⟨v, hv, hv'⟩ | ⟨hv, -⟩ <;>
      rcases (caRule_eq_some hl').2 with ⟨w, hw, hw'⟩ | ⟨hw, -⟩
    · cases hv; cases hw
      exact ⟨le_rfl.trans (by omega), by omega,
        Or.inr (Or.inr (by rw [eq_of_heavy hn hF hlt hlt' hv' hw']))⟩
    · cases hv; cases hw; exact ⟨by omega, by omega, Or.inr (Or.inl rfl)⟩
    · cases hv; cases hw; exact ⟨by omega, by omega, Or.inl rfl⟩
    · cases hv; cases hw; exact ⟨by omega, by omega, Or.inl rfl⟩
  · intro p _ v g hd
    obtain ⟨l, hlt, hl⟩ := key p _ hd
    rcases (caRule_eq_some hl).2 with ⟨w, hw, hw'⟩ | ⟨hw, -⟩
    · cases hw; exact exists_correct_of_heavy (by omega) hF hlt hw'
    · cases hw
  · intro p hp a g hd hI
    obtain ⟨l, hlt, hl⟩ := key p _ hd
    obtain ⟨hS, h⟩ := caRule_eq_some hl
    rcases h with ⟨w, hw, -⟩ | ⟨-, hlow⟩
    · cases hw; rfl
    · have := heavy_of_unanimous hF hlt (fun q hq => hI q hq p hp) hS
      exact absurd (hlow (I p)) (not_lt.2 this)

/-! ### Termination in one round -/

/-- In every admissible execution, every correct process decides in its round `1` (for any `n`,
`f`): by fairness it eventually holds round-1 messages of all `≥ n - f` correct processes, and
it cannot have started round `2` without a quorum of round-1 messages, all of which are in its
communication-closed view (`exists_ccQuorum_one_of_fair`). -/
theorem caAlg_allDecideBy {f : ℕ} (I : Fin n → V) (A : Adversary n R V)
    (hA : (caAlg n f).Admissible f I A) (ρ : Tape n R) :
    (caAlg n f).AllDecideBy f I ρ A 1 := by
  intro p hp
  obtain ⟨k, h, hpre, hr, hq⟩ :=
    (caAlg n f).exists_ccQuorum_one_of_fair f I ρ A (hA.2 ρ) hA.1 hp
  exact ⟨k, h, (List.mem_inits _ _).2 hpre, hr, caRule_isSome hq⟩

/-- The round complexity of `caAlg` is at most `1` in every admissible execution. -/
theorem caAlg_rounds {f : ℕ} (I : Fin n → V) (A : Adversary n R V)
    (hA : (caAlg n f).Admissible f I A) (ρ : Tape n R) :
    (caAlg n f).rounds f I ρ A ≤ 1 := by
  exact_mod_cast (caAlg n f).rounds_le_of_allDecideBy f I ρ (caAlg_allDecideBy I A hA ρ)

/-- The expected round complexity of `caAlg` is at most `1`, for every admissible adversary and
every probability distribution of the tape. -/
theorem caAlg_expRounds {f : ℕ} [MeasurableSpace R] (μ : MeasureTheory.Measure (Tape n R))
    [MeasureTheory.IsProbabilityMeasure μ] (I : Fin n → V) (A : Adversary n R V)
    (hA : (caAlg n f).Admissible f I A) : (caAlg n f).expRounds f I μ A ≤ 1 := by
  exact_mod_cast (caAlg n f).expRounds_le_of_rounds_le f I μ (r := 1)
    fun ρ => by exact_mod_cast caAlg_rounds I A hA ρ

/-- Non-vacuity: under the (admissible) round-robin adversary with any faulty set of size `≤ f`,
every correct process decides. -/
theorem caAlg_allDecide_rrAdv {f : ℕ} (I : Fin n → V) {F : Finset (Fin n)} (hF : F.card ≤ f)
    (ρ : Tape n R) : (caAlg n f).AllDecide f I ρ (rrAdv F) :=
  (caAlg n f).allDecide_of_allDecideBy f I ρ
    (caAlg_allDecideBy I _ ((caAlg n f).rrAdv_admissible f I hF) ρ)

/-- **Bounded canonical-round crusader agreement exists for `n > 5f`** (the remark in the
abstract and Section 6 of [AFW26]): a communication-closed canonical-round algorithm that is safe
for crusader agreement and terminates within one round in every admissible execution (hence with
expected round complexity `≤ 1` for every tape distribution). Admissible adversaries exist
(`rrAdv_admissible`). So the bound `n ≤ 5f` in Theorems 1 and 7 is sharp for crusader
agreement. -/
theorem exists_bounded_crusader {f : ℕ} (hn : 5 * f < n) :
    ∃ alg : CanonAlg n V R V (Option V × ℕ), alg.CommClosed ∧
      alg.Safe f (connectedConsensusSpec 1) ∧
      ∀ I A, alg.Admissible f I A → ∀ ρ, alg.rounds f I ρ A ≤ 1 :=
  ⟨caAlg n f, caAlg_commClosed f, caAlg_safe hn, fun I A hA ρ => caAlg_rounds I A hA ρ⟩

end Podc2026.CanonicalRound
