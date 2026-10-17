import Papers.PODC2025.BAWithPredictions.RoundLowerBound

/-!
# An unconditional early-deciding lower bound (`f + 1` rounds) and a weak Theorem 13

The paper's Theorem 13 relies on the Dolev–Reischuk–Strong early-deciding bound
`min (f + 2) (t + 1)` (`EarlyDecidingLB`, a hypothesis). Here we prove, in the same lock-step
Byzantine model, the classical weaker bound: every deterministic Byzantine agreement algorithm
(without predictions) for `n ≥ t + 2` processes tolerating `t` Byzantine faults has, for every
`f ≤ t`, a reliable execution with at most `f` Byzantine processes in which some honest process has
not decided after `f` rounds (`earlyDecidingLB_weak`). Plugged into the reduction this gives
Theorem 13 with `+1` instead of `+2`, unconditionally (`roundLowerBound_weak`).

The proof is the classical chain argument over *send-omission* runs (`osc x O`: inputs `x`,
omission pattern `O r a b` = "the round-`r` message of `a` to `b` is lost"); a run whose omitters lie
in `F` is turned into a reliable run with Byzantine set `F` by `padScenario`. With `k = f`:

* `claim j`: runs with the same inputs, omitters in `F`, `|F| + j ≤ k + 1`, `|F| ≤ k`, whose
  patterns agree on rounds `< k - j` lead to the same decision (`SameVal`). The step changes the
  round-`(k - j - 1)` messages one receiver `b` at a time; for `j ≥ 1` the receiver is first
  silenced in all later rounds (`claim j` with `F ∪ {b}`), so only `b` notices
  (`hist_osc_swap`); in the last round nothing needs to be silenced.
* Changing one input: silence its owner in all `k` rounds (`claim k` with `F = {a}`).
-/

namespace BAWithPredictions

open Cslib.Byzantine.LockStep Finset

section Chain

variable {Q V M : Type*}

/-- Send-omission runs: no Byzantine processes, inputs `x`, omitted messages `O`. -/
def osc (x : Q → V) (O : ℕ → Q → Q → Prop) : Scenario Q V M where
  byz := ∅
  input := x
  adv _ _ _ := none
  drop := O

variable [DecidableEq Q] (alg : Protocol Q V M V)

/-- **Swap lemma.** Two omission runs whose inputs agree except possibly at `b` (only if `b` is
silent from round `0`, i.e. `c = 0`), whose patterns agree on rounds `< k` except for the messages
into `b` in round `c - 1`, and in which `b` is silent in rounds `c, …, k - 1`, cannot be
distinguished by any process `≠ b` within `k` rounds. -/
theorem hist_osc_swap {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {k c : ℕ} {b : Q}
    (hx : ∀ p, p ≠ b ∨ 0 < c → x₁ p = x₂ p)
    (hag : ∀ m < k, ∀ a d, (m + 1 = c → d ≠ b) → (O₁ m a d ↔ O₂ m a d))
    (hsil : ∀ m, c ≤ m → m < k → ∀ d, O₁ m b d ∧ O₂ m b d) :
    ∀ m ≤ k, ∀ q, (q ≠ b ∨ m < c) →
      hist ⊤ alg (osc x₁ O₁) m q = hist ⊤ alg (osc x₂ O₂) m q := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro hm q hq
    rw [hist_succ, hist_succ, ih (by omega) q (hq.imp_right fun h => by omega)]
    congr 2
    funext p
    unfold deliver
    by_cases hpq : p = q
    · simp [hpq]
    have hO : O₁ m p q ↔ O₂ m p q :=
      hag m (by omega) p q (fun h => by rcases hq with hq | hq; exact hq; omega)
    by_cases h1 : O₁ m p q
    · simp [osc, hpq, h1, hO.1 h1]
    · have h2 : ¬ O₂ m p q := fun h => h1 (hO.2 h)
      by_cases hpb : p = b
      · subst hpb
        by_cases hmc : c ≤ m
        · exact absurd (hsil m hmc (by omega) q).1 h1
        · have := ih (by omega) p (Or.inr (by omega))
          simp [osc, hpq, h1, h2, hx p (Or.inr (by omega))] at this ⊢
          rw [this]
      · have := ih (by omega) p (Or.inl hpb)
        simp [osc, hpq, h1, h2, hx p (Or.inl hpb)] at this ⊢
        rw [this]

end Chain

section Chain2

variable {Q V M : Type*} [Fintype Q] [DecidableEq Q] {alg : Protocol Q V M V} {t' k : ℕ}

/-- The omitters of `O` lie in `F`, and `|F| ≤ k`. -/
def ValidPat (k : ℕ) (O : ℕ → Q → Q → Prop) (F : Finset Q) : Prop :=
  (∀ r a d, O r a d → a ∈ F) ∧ F.card ≤ k

/-- All processes outside `F` decide the same value in the two runs. -/
def SameVal (alg : Protocol Q V M V) (x₁ : Q → V) (O₁ : ℕ → Q → Q → Prop) (x₂ : Q → V)
    (O₂ : ℕ → Q → Q → Prop) (F : Finset Q) : Prop :=
  ∀ p₁ ∉ F, ∀ p₂ ∉ F, ∀ v w, Decides ⊤ alg (osc x₁ O₁) p₁ v → Decides ⊤ alg (osc x₂ O₂) p₂ w →
    v = w

variable (hBA : Solves ⊤ alg {S | S.ncard ≤ t'} BA) (hk : k ≤ t')
  (hfast : ∀ s : Scenario Q V M, s.Reliable → s.byz.ncard ≤ k →
    ∀ q ∉ s.byz, ∃ r ≤ k, status ⊤ alg s r q ≠ none)

omit [Fintype Q] [DecidableEq Q] in
include hBA hk in
theorem osc_BA {x : Q → V} {O : ℕ → Q → Q → Prop} {F : Finset Q} (hv : ValidPat k O F) :
    BA x (↑F)ᶜ (Decides ⊤ alg (osc x O)) := by
  have h := hBA (padScenario ⊤ alg (osc x O) ↑F)
    (by simp only [Set.mem_ofPred_eq, padScenario, osc, Set.empty_union, Set.ncard_coe_finset]
        have := hv.2; omega)
    (reliable_padScenario _ _ fun r p q hd => hv.1 r p q hd)
  have hD : Decides ⊤ alg (padScenario ⊤ alg (osc x O) ↑F) = Decides ⊤ alg (osc x O) := by
    funext p o
    exact propext (decides_padScenario _ _ _ _ _ _)
  rw [hD] at h
  simpa [padScenario, osc, Scenario.honest] using h

omit [Fintype Q] [DecidableEq Q] in
include hfast in
theorem osc_fast {x : Q → V} {O : ℕ → Q → Q → Prop} {F : Finset Q} (hv : ValidPat k O F)
    {q : Q} (hq : q ∉ F) : ∃ r ≤ k, status ⊤ alg (osc x O) r q ≠ none := by
  obtain ⟨r, hr, h⟩ := hfast (padScenario ⊤ alg (osc x O) ↑F)
    (reliable_padScenario _ _ fun r p q hd => hv.1 r p q hd)
    (by simp only [padScenario, osc, Set.empty_union, Set.ncard_coe_finset]; exact hv.2) q
    (by simpa [padScenario, osc] using hq)
  exact ⟨r, hr, by rwa [status_padScenario] at h⟩

omit [Fintype Q] [DecidableEq Q] in
include hBA hk in
theorem SameVal.upgrade {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F G : Finset Q}
    (hv₁ : ValidPat k O₁ F) (hv₂ : ValidPat k O₂ F) (hFG : F ⊆ G) {p : Q} (hp : p ∉ G)
    (h : SameVal alg x₁ O₁ x₂ O₂ G) : SameVal alg x₁ O₁ x₂ O₂ F := by
  intro p₁ hp₁ p₂ hp₂ v w hv hw
  have hpF : p ∉ F := fun h => hp (hFG h)
  obtain ⟨u₁, hu₁⟩ := (osc_BA hBA hk hv₁ (x := x₁)).1 p (by simpa using hpF)
  obtain ⟨u₂, hu₂⟩ := (osc_BA hBA hk hv₂ (x := x₂)).1 p (by simpa using hpF)
  have e1 := (osc_BA hBA hk hv₁).2.2 p₁ (by simpa using hp₁) p (by simpa using hpF) v u₁ hv hu₁
  have e2 := (osc_BA hBA hk hv₂).2.2 p (by simpa using hpF) p₂ (by simpa using hp₂) u₂ w hu₂ hw
  rw [e1, h p hp p hp u₁ u₂ hu₁ hu₂, e2]

omit [Fintype Q] [DecidableEq Q] in
include hBA hk in
theorem SameVal.trans {x₁ x₂ x₃ : Q → V} {O₁ O₂ O₃ : ℕ → Q → Q → Prop} {F : Finset Q}
    (hv₂ : ValidPat k O₂ F) {p : Q} (hp : p ∉ F)
    (h₁ : SameVal alg x₁ O₁ x₂ O₂ F) (h₂ : SameVal alg x₂ O₂ x₃ O₃ F) :
    SameVal alg x₁ O₁ x₃ O₃ F := by
  intro p₁ hp₁ p₃ hp₃ v w hv hw
  obtain ⟨u, hu⟩ := (osc_BA hBA hk hv₂ (x := x₂)).1 p (by simpa using hp)
  rw [h₁ p₁ hp₁ p hp v u hv hu, h₂ p hp p₃ hp₃ u w hu hw]

omit [Fintype Q] [DecidableEq Q] in
theorem SameVal.symm {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q}
    (h : SameVal alg x₁ O₁ x₂ O₂ F) : SameVal alg x₂ O₂ x₁ O₁ F :=
  fun p₁ hp₁ p₂ hp₂ v w hv hw => (h p₂ hp₂ p₁ hp₁ w v hw hv).symm

omit [Fintype Q] [DecidableEq Q] in
include hBA hk in
theorem SameVal.refl {x : Q → V} {O : ℕ → Q → Q → Prop} {F : Finset Q} (hv : ValidPat k O F) :
    SameVal alg x O x O F := fun p₁ hp₁ p₂ hp₂ v w hv' hw =>
  (osc_BA hBA hk hv).2.2 p₁ (by simpa using hp₁) p₂ (by simpa using hp₂) v w hv' hw

omit [Fintype Q] [DecidableEq Q] in
include hBA hk hfast in
/-- One witness outside `F` that cannot distinguish the runs within `k` rounds suffices. -/
theorem sameVal_of_hist {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q}
    (hv₁ : ValidPat k O₁ F) (hv₂ : ValidPat k O₂ F) {p : Q} (hp : p ∉ F) (hx : x₁ p = x₂ p)
    (hh : hist ⊤ alg (osc x₁ O₁) k p = hist ⊤ alg (osc x₂ O₂) k p) :
    SameVal alg x₁ O₁ x₂ O₂ F := by
  intro p₁ hp₁ p₂ hp₂ v w hv hw
  obtain ⟨u, hu⟩ := (osc_BA hBA hk hv₁ (x := x₁)).1 p (by simpa using hp)
  have hu' := (decides_iff_of_hist ⊤ alg (s₁ := osc x₁ O₁) (s₂ := osc x₂ O₂) hx hh
    (osc_fast hfast hv₁ hp) u).1 hu
  rw [(osc_BA hBA hk hv₁).2.2 p₁ (by simpa using hp₁) p (by simpa using hp) v u hv hu,
    (osc_BA hBA hk hv₂).2.2 p (by simpa using hp) p₂ (by simpa using hp₂) u w hu' hw]

omit [DecidableEq Q] in
theorem exists_not_mem_of_card_lt (G : Finset Q) (h : G.card < Fintype.card Q) : ∃ p, p ∉ G := by
  by_contra hc
  push Not at hc
  have : G = univ := eq_univ_iff_forall.2 hc
  rw [this, card_univ] at h
  exact lt_irrefl _ h

/-- Round `r₀` messages into receivers in `S` follow `O₂`, others `O₁`; earlier rounds follow `O₁`,
later rounds have no omissions. -/
def mixPat (O₁ O₂ : ℕ → Q → Q → Prop) (r₀ : ℕ) (S : Finset Q) : ℕ → Q → Q → Prop :=
  fun m a d => if m < r₀ then O₁ m a d else if m = r₀ then (if d ∈ S then O₂ m a d else O₁ m a d)
    else False

/-- `O`, with `b` additionally silent after round `r₀`. -/
def silPat (O : ℕ → Q → Q → Prop) (b : Q) (r₀ : ℕ) : ℕ → Q → Q → Prop :=
  fun m a d => O m a d ∨ (a = b ∧ r₀ < m)

include hBA hk hfast in
/-- **The chain claim.** Runs with the same inputs, omitters in `F` (`|F| + j ≤ k + 1`, `|F| ≤ k`)
and patterns agreeing on rounds `< k - j` give the same decision. -/
theorem sameVal_claim (hn : k + 2 ≤ Fintype.card Q) (x : Q → V) :
    ∀ j ≤ k, ∀ F : Finset Q, F.card + j ≤ k + 1 → F.card ≤ k →
      ∀ O₁ O₂ : ℕ → Q → Q → Prop, (∀ r a d, O₁ r a d → a ∈ F) → (∀ r a d, O₂ r a d → a ∈ F) →
        (∀ m < k - j, ∀ a d, O₁ m a d ↔ O₂ m a d) → SameVal alg x O₁ x O₂ F := by
  intro j
  induction j with
  | zero =>
    intro _ F _ hFk O₁ O₂ h₁ h₂ hag
    obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt F (by omega)
    exact sameVal_of_hist hBA hk hfast ⟨h₁, hFk⟩ ⟨h₂, hFk⟩ hp rfl
      (hist_osc_swap alg (c := k + 1) (b := p) (fun _ _ => rfl)
        (fun m hm a d _ => hag m (by omega) a d) (fun m h1 h2 => by omega) k le_rfl p
        (Or.inr (by omega)))
  | succ j ih =>
    intro hj F hF hFk O₁ O₂ h₁ h₂ hag
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ + 1 = k - j := ⟨k - j - 1, by omega⟩
    have hmixv : ∀ S, ValidPat k (mixPat O₁ O₂ r₀ S) F := fun S =>
      ⟨fun r a d h => by
        unfold mixPat at h
        split_ifs at h
        exacts [h₁ _ _ _ h, h₂ _ _ _ h, h₁ _ _ _ h], hFk⟩
    obtain ⟨p₀, hp₀⟩ := exists_not_mem_of_card_lt F (by omega)
    have hstart : SameVal alg x O₁ x (mixPat O₁ O₂ r₀ ∅) F :=
      ih (by omega) F (by omega) hFk O₁ _ h₁ (hmixv ∅).1 fun m hm a d => by
        unfold mixPat
        by_cases h : m < r₀
        · simp [h]
        · have : m = r₀ := by omega
          simp [this]
    have hend : SameVal alg x (mixPat O₁ O₂ r₀ univ) x O₂ F :=
      ih (by omega) F (by omega) hFk _ O₂ (hmixv univ).1 h₂ fun m hm a d => by
        unfold mixPat
        by_cases h : m < r₀
        · simpa [h] using hag m (by omega) a d
        · have : m = r₀ := by omega
          simp [this]
    have hone : ∀ S b, SameVal alg x (mixPat O₁ O₂ r₀ S) x (mixPat O₁ O₂ r₀ (insert b S)) F := by
      intro S b
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · -- last round: only `b` can notice the change
        obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt (insert b F)
          (lt_of_le_of_lt (card_insert_le _ _) (by omega))
        have hpb : p ≠ b := fun h => hp (h ▸ mem_insert_self _ _)
        have hpF : p ∉ F := fun h => hp (mem_insert_of_mem h)
        refine sameVal_of_hist hBA hk hfast (hmixv S) (hmixv _) hpF rfl
          (hist_osc_swap alg (c := k) (b := b) (fun _ _ => rfl) (fun m hm a d hdb => ?_)
            (fun m h1 h2 => by omega) k le_rfl p (Or.inl hpb))
        unfold mixPat
        by_cases h : m < r₀
        · simp [h]
        · have hm' : m = r₀ := by omega
          have hdb' : d ≠ b := hdb (by omega)
          simp [hm', hdb']
      · -- silence `b` after round `r₀` first
        set F' := insert b F with hF'
        have hF'c : F'.card ≤ F.card + 1 := card_insert_le _ _
        have hsilv : ∀ S', ∀ r a d, silPat (mixPat O₁ O₂ r₀ S') b r₀ r a d → a ∈ F' :=
          fun S' r a d h => h.elim (fun h => mem_insert_of_mem ((hmixv S').1 r a d h))
            (fun h => h.1 ▸ mem_insert_self _ _)
        have hagsil : ∀ S', ∀ m < k - j, ∀ a d,
            mixPat O₁ O₂ r₀ S' m a d ↔ silPat (mixPat O₁ O₂ r₀ S') b r₀ m a d := by
          intro S' m hm a d
          have : ¬ r₀ < m := by omega
          simp [silPat, this]
        obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt F' (by omega)
        have hpb : p ≠ b := fun h => hp (h ▸ mem_insert_self _ _)
        have h1 := ih (by omega) F' (by omega) (by omega) _ _
          (fun r a d h => mem_insert_of_mem ((hmixv S).1 r a d h)) (hsilv S) (hagsil S)
        have h3 := (ih (by omega) F' (by omega) (by omega) _ _
          (fun r a d h => mem_insert_of_mem ((hmixv (insert b S)).1 r a d h))
          (hsilv (insert b S)) (hagsil (insert b S))).symm
        have h2 : SameVal alg x (silPat (mixPat O₁ O₂ r₀ S) b r₀) x
            (silPat (mixPat O₁ O₂ r₀ (insert b S)) b r₀) F' := by
          refine sameVal_of_hist hBA hk hfast ⟨hsilv S, by omega⟩ ⟨hsilv _, by omega⟩ hp rfl
            (hist_osc_swap alg (c := r₀ + 1) (b := b) (fun _ _ => rfl)
              (fun m hm a d hdb => ?_) (fun m h1 h2 d => ⟨Or.inr ⟨rfl, by omega⟩,
                Or.inr ⟨rfl, by omega⟩⟩) k le_rfl p (Or.inl hpb))
          unfold silPat mixPat
          by_cases h : m < r₀
          · simp [h]
          · by_cases hm' : m = r₀
            · have hdb' : d ≠ b := hdb (by omega)
              simp [hm', hdb']
            · simp [h, hm']
        have h13 := SameVal.trans hBA hk ⟨hsilv S, by omega⟩ hp h1
          (SameVal.trans hBA hk ⟨hsilv _, by omega⟩ hp h2 h3)
        exact SameVal.upgrade hBA hk (hmixv S) (hmixv _) (subset_insert _ _) hp h13
    have hchain : ∀ S, SameVal alg x (mixPat O₁ O₂ r₀ ∅) x (mixPat O₁ O₂ r₀ S) F := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact SameVal.refl hBA hk (hmixv ∅)
      | insert b S _ ihS => exact SameVal.trans hBA hk (hmixv S) hp₀ ihS (hone S b)
    exact SameVal.trans hBA hk (hmixv ∅) hp₀ hstart
      (SameVal.trans hBA hk (hmixv univ) hp₀ (hchain univ) hend)

/-- **Early-deciding lower bound, weak form** (classical; the `f + 1` part of [DRS90]), proved in
the Byzantine lock-step model: for `t' + 2 ≤ |Q|` and at least two values, every deterministic
Byzantine agreement algorithm tolerating `t'` Byzantine faults has, for every `f' ≤ t'`, a
reliable execution with at most `f'` Byzantine processes in which some honest process has not
decided after `f'` rounds. (The Byzantine processes only omit messages.) -/
theorem earlyDecidingLB_weak {Q V : Type*} [Fintype Q] [DecidableEq Q] [Nontrivial V] {t' : ℕ}
    (hn : t' + 2 ≤ Fintype.card Q) : EarlyDecidingLBWith (fun f' _ => f' + 1) Q V t' := by
  intro M alg hBA k hk
  by_contra hcon
  have hfast : ∀ s : Scenario Q V M, s.Reliable → s.byz.ncard ≤ k →
      ∀ q ∉ s.byz, ∃ r ≤ k, status ⊤ alg s r q ≠ none := by
    intro s hs hc q hq
    by_contra h
    push Not at h
    exact hcon ⟨s, hs, hc, q, hq, fun r hr => h r (by beta_reduce at hr; omega)⟩
  have hn' : k + 2 ≤ Fintype.card Q := by omega
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  let xs : Finset Q → Q → V := fun S p => if p ∈ S then v₁ else v₀
  let O0 : ℕ → Q → Q → Prop := fun _ _ _ => False
  have hv0 : ValidPat k O0 ∅ := ⟨fun _ _ _ h => h.elim, by simp⟩
  have hstep : ∀ S a, SameVal alg (xs S) O0 (xs (insert a S)) O0 ∅ := by
    intro S a
    let G : Finset Q := if k = 0 then ∅ else {a}
    let Sa : ℕ → Q → Q → Prop := fun m a' _ => a' = a ∧ m < k
    have hGc : G.card ≤ 1 := by
      simp only [G]; split_ifs <;> simp
    have hGk : G.card ≤ k := by
      simp only [G]; split_ifs with h <;> simp; omega
    have hSa : ∀ r a' d, Sa r a' d → a' ∈ G := by
      rintro r a' d ⟨rfl, hr⟩
      simp only [G]
      split_ifs with h
      · omega
      · simp
    obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt ({a} : Finset Q) (by simp; omega)
    have hpa : p ≠ a := by simpa using hp
    have hpG : p ∉ G := by
      simp only [G]; split_ifs <;> simp [hpa]
    have h1 := sameVal_claim hBA hk hfast hn' (xs S) k le_rfl G (by omega) hGk O0 Sa
      (fun _ _ _ h => h.elim) hSa (fun m hm => by omega)
    have h3 := (sameVal_claim hBA hk hfast hn' (xs (insert a S)) k le_rfl G (by omega) hGk O0 Sa
      (fun _ _ _ h => h.elim) hSa (fun m hm => by omega)).symm
    have hx : ∀ q, q ≠ a ∨ 0 < 0 → xs S q = xs (insert a S) q := by
      rintro q (hq | hq)
      · simp [xs, hq]
      · omega
    have h2 : SameVal alg (xs S) Sa (xs (insert a S)) Sa G :=
      sameVal_of_hist hBA hk hfast ⟨hSa, hGk⟩ ⟨hSa, hGk⟩ hpG (hx p (Or.inl hpa))
        (hist_osc_swap alg (c := 0) (b := a) hx (fun _ _ _ _ _ => Iff.rfl)
          (fun m _ hm _ => ⟨⟨rfl, hm⟩, ⟨rfl, hm⟩⟩) k le_rfl p (Or.inl hpa))
    have h13 := SameVal.trans hBA hk ⟨hSa, hGk⟩ hpG h1
      (SameVal.trans hBA hk ⟨hSa, hGk⟩ hpG h2 h3)
    exact SameVal.upgrade hBA hk hv0 hv0 (empty_subset _) hpG h13
  have hchain : ∀ S, SameVal alg (xs ∅) O0 (xs S) O0 ∅ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact SameVal.refl hBA hk hv0
    | insert b S _ ihS => exact SameVal.trans hBA hk hv0 (notMem_empty b) ihS (hstep S b)
  obtain ⟨p⟩ : Nonempty Q := Fintype.card_pos_iff.1 (by omega)
  have d0 := (osc_BA hBA hk hv0 (x := xs ∅)).2.1 v₀ (fun q _ => by simp [xs]) p (by simp)
  have d1 := (osc_BA hBA hk hv0 (x := xs univ)).2.1 v₁ (fun q _ => by simp [xs]) p (by simp)
  exact hne (hchain univ p (notMem_empty _) p (notMem_empty _) v₀ v₁ d0 d1)

end Chain2

/-- **Theorem 13 of [BDEG25], weak form, unconditional.** For every deterministic algorithm `alg`
solving Byzantine agreement with classification predictions against `t` Byzantine faults (for all
predictions), with at least two values, every `f ≤ t < n - 1` and every bound `Bd` on the number of
wrong prediction bits, there is a reliable execution with exactly `f` Byzantine processes and at
most `Bd` wrong bits given to honest processes in which some honest process has not decided before
round `min (f + 1) (⌊Bd/(n - f)⌋ + 1)`. (The full `+2` version is `theorem13` in
`RoundLowerBoundStrong.lean`.) -/
theorem roundLowerBound_weak {P V : Type*} [Fintype P] [DecidableEq P] [Nontrivial V] {M : Type}
    {alg : Protocol P (V × (P → Bool)) M V} {t f : ℕ}
    (hA : Solves ⊤ alg {S | S.ncard ≤ t} BAP) (hft : f ≤ t) (htn : t + 2 ≤ Fintype.card P)
    (Bd : ℕ) :
    ∃ (s : Scenario P (V × (P → Bool)) M) (F : Finset P),
      s.Reliable ∧ s.byz = ↑F ∧ F.card = f ∧ wrongBits F (fun i => (s.input i).2) ≤ Bd ∧
      ∃ p ∉ F, ∀ r < min (f + 1) (Bd / (Fintype.card P - f) + 1), status ⊤ alg s r p = none := by
  obtain ⟨s, F, h1, h2, h3, h4, p, hp, hslow⟩ :=
    roundLowerBoundWith (fun f' _ => f' + 1) hA hft htn Bd fun X hX => earlyDecidingLB_weak (Q := {p // p ∉ X}) (by
      rw [Fintype.card_subtype_compl, Fintype.card_coe]; omega)
  exact ⟨s, F, h1, h2, h3, h4, p, hp, fun r hr => hslow r (by omega)⟩

end BAWithPredictions
