import Papers.PODC2025.BAWithPredictions.RoundLowerBoundChain

/-!
# The Byzantine early-deciding bound `min (f + 2) (t + 1)` and Theorem 13, unconditionally

`RoundLowerBound.lean` reduces Theorem 13 to the early-deciding lower bound of
Dolev–Reischuk–Strong for algorithms *without* predictions (`EarlyDecidingLB`, the paper's
citation [21]); `RoundLowerBoundChain.lean` proves the classical `f + 1` part. Here we prove the
full Byzantine bound: for `f < t`, deciding by round `f + 1` in all executions with at most `f`
Byzantine processes is impossible (`earlyDecidingLB_strong`), and hence Theorem 13 holds as stated
(`theorem13`), for every value type with at least two values.

**The extra round.** The chain argument of `RoundLowerBoundChain.lean` (send-omission runs with
at most `f` omitters) is run with decision round `K = f + 1`. Changing the round-`(K - 1)` messages
into one receiver `b` used to require silencing `b` in round `K` (one more omitter). Instead we use
the `(f + 1)`-st fault allowed by `f < t` as a **Byzantine** `b` that, in round `K`, sends to one
honest process `q` what it sends in the second run and to everybody else what it sends in the first
run (`hybrid`, `sameVal_hybrid`): then `q` sees the second run and another honest process sees the
first one, so Agreement in the hybrid execution identifies the two decisions. This equivocation is
exactly what makes the bound `f + 2` hold for Byzantine (but not for crash) failures.
-/

set_option linter.unusedSectionVars false

namespace BAWithPredictions

open Cslib.Byzantine.LockStep Finset

section Strong

variable {Q V M : Type*} [Fintype Q] [DecidableEq Q] {alg : Protocol Q V M V} {t' k : ℕ}

/-- The hybrid execution: `F ∪ {b}` are Byzantine; they replay the run `osc x₁ O₁`, except that in
round `k` the process `b` sends to `q` what it sends in `osc x₂ O₂`. -/
noncomputable def hybrid (alg : Protocol Q V M V) (x₁ x₂ : Q → V) (O₁ O₂ : ℕ → Q → Q → Prop)
    (F : Finset Q) (b q : Q) (k : ℕ) : Scenario Q V M where
  byz := ↑(insert b F)
  input := x₁
  adv m a d := if a = b ∧ m = k ∧ d = q then
      deliver ⊤ alg (osc x₂ O₂) (hist ⊤ alg (osc x₂ O₂) k) k b q
    else deliver ⊤ alg (osc x₁ O₁) (hist ⊤ alg (osc x₁ O₁) m) m a d

omit [Fintype Q] in
theorem deliver_osc_self (x : Q → V) (O : ℕ → Q → Q → Prop) (h : Q → History Q M) (m : ℕ)
    (a : Q) : deliver ⊤ alg (osc x O) h m a a = none := by
  unfold deliver; simp

omit [Fintype Q] in
theorem deliver_osc_of (x : Q → V) {O : ℕ → Q → Q → Prop} (h : Q → History Q M) {m : ℕ}
    {a d : Q} (hO : O m a d) : deliver ⊤ alg (osc x O) h m a d = none := by
  unfold deliver; simp [osc, hO]

omit [Fintype Q] in
theorem deliver_osc_of_not (x : Q → V) {O : ℕ → Q → Q → Prop} (h : Q → History Q M) {m : ℕ}
    {a d : Q} (had : a ≠ d) (hO : ¬ O m a d) :
    deliver ⊤ alg (osc x O) h m a d = alg.send a (x a) (h a) d := by
  unfold deliver; simp [osc, hO, had]

omit [Fintype Q] in
theorem deliver_hybrid_mem {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q} {b q a : Q}
    (ha : a ∈ insert b F) (h : Q → History Q M) (m : ℕ) (d : Q) :
    deliver ⊤ alg (hybrid alg x₁ x₂ O₁ O₂ F b q k) h m a d =
      if a = d then none else (hybrid alg x₁ x₂ O₁ O₂ F b q k).adv m a d := by
  have : a ∈ (hybrid alg x₁ x₂ O₁ O₂ F b q k).byz := by simpa [hybrid] using ha
  unfold deliver
  by_cases had : a = d <;> simp [had, this]

omit [Fintype Q] in
theorem deliver_hybrid_not_mem {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q}
    {b q a : Q} (ha : a ∉ insert b F) (h : Q → History Q M) (m : ℕ) (d : Q) :
    deliver ⊤ alg (hybrid alg x₁ x₂ O₁ O₂ F b q k) h m a d =
      if a = d then none else alg.send a (x₁ a) (h a) d := by
  have : a ∉ (hybrid alg x₁ x₂ O₁ O₂ F b q k).byz := by simpa [hybrid] using ha
  simp only [mem_insert, not_or] at ha
  unfold deliver
  by_cases had : a = d <;> simp [had, hybrid, ha.1, ha.2]

omit [Fintype Q] in
theorem hist_hybrid_left {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q} {b q : Q}
    (hO₁ : ∀ r a d, O₁ r a d → a ∈ F) :
    ∀ m ≤ k + 1, ∀ p ∉ insert b F, (m ≤ k ∨ p ≠ q) →
      hist ⊤ alg (hybrid alg x₁ x₂ O₁ O₂ F b q k) m p = hist ⊤ alg (osc x₁ O₁) m p := by
  intro m
  induction m with
  | zero => intros; rfl
  | succ m ih =>
    intro hm p hp hpq
    rw [hist_succ, hist_succ, ih (by omega) p hp (Or.inl (by omega))]
    congr 2
    funext a
    have hcond : ¬ (a = b ∧ m = k ∧ p = q) := by
      rintro ⟨-, rfl, rfl⟩; rcases hpq with h | h
      · omega
      · exact h rfl
    by_cases hab : a ∈ insert b F
    · rw [deliver_hybrid_mem hab]
      simp only [hybrid, hcond, ite_false]
      by_cases hap : a = p
      · subst hap; simp [deliver_osc_self]
      · simp [hap]
    · have h2 : ¬ O₁ m a p := fun h => hab (mem_insert_of_mem (hO₁ _ _ _ h))
      rw [deliver_hybrid_not_mem hab, ih (by omega) a hab (Or.inl (by omega))]
      by_cases hap : a = p
      · subst hap; simp [deliver_osc_self]
      · simp [hap, deliver_osc_of_not _ _ hap h2]

omit [Fintype Q] in
theorem hist_hybrid_right {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q} {b q : Q}
    (hO₁ : ∀ r a d, O₁ r a d → a ∈ F) (hO₂ : ∀ r a d, O₂ r a d → a ∈ F)
    (hx : ∀ p, p ≠ b → x₁ p = x₂ p)
    (hh : ∀ p, p ≠ b → hist ⊤ alg (osc x₁ O₁) k p = hist ⊤ alg (osc x₂ O₂) k p)
    (hag : ∀ a, a ≠ b → ∀ d, O₁ k a d ↔ O₂ k a d) (hq : q ∉ insert b F) :
    hist ⊤ alg (hybrid alg x₁ x₂ O₁ O₂ F b q k) (k + 1) q = hist ⊤ alg (osc x₂ O₂) (k + 1) q := by
  have hqb : q ≠ b := fun h => hq (h ▸ mem_insert_self _ _)
  rw [hist_succ, hist_succ, hist_hybrid_left hO₁ k (by omega) q hq (Or.inl le_rfl), hh q hqb]
  congr 2
  funext a
  by_cases hab : a ∈ insert b F
  · rw [deliver_hybrid_mem hab]
    by_cases hb : a = b
    · subst hb
      simp only [hybrid, true_and, ite_true]
      by_cases haq : a = q
      · subst haq; simp [deliver_osc_self]
      · simp [haq]
    · simp only [hybrid, hb, false_and, ite_false]
      by_cases haq : a = q
      · subst haq; simp [deliver_osc_self]
      · simp only [haq, ite_false]
        by_cases hO : O₁ k a q
        · rw [deliver_osc_of _ _ hO, deliver_osc_of _ _ ((hag a hb q).1 hO)]
        · rw [deliver_osc_of_not _ _ haq hO, deliver_osc_of_not _ _ haq (fun h => hO ((hag a hb q).2 h)),
            hx a hb, hh a hb]
  · have hb : a ≠ b := fun h => hab (h ▸ mem_insert_self _ _)
    have h2 : ¬ O₂ k a q := fun h => hab (mem_insert_of_mem (hO₂ _ _ _ h))
    rw [deliver_hybrid_not_mem hab, hist_hybrid_left hO₁ k (by omega) a hab (Or.inl le_rfl),
      hx a hb, hh a hb]
    by_cases haq : a = q
    · subst haq; simp [deliver_osc_self]
    · simp [haq, deliver_osc_of_not _ _ haq h2]

variable (hBA : Solves ⊤ alg {S | S.ncard ≤ t'} BA) (hk : k + 1 ≤ t')
  (hfast : ∀ s : Scenario Q V M, s.Reliable → s.byz.ncard ≤ k →
    ∀ q ∉ s.byz, ∃ r ≤ k + 1, status ⊤ alg s r q ≠ none)

omit [Fintype Q] [DecidableEq Q] in
include hfast in
theorem osc_fast2 {x : Q → V} {O : ℕ → Q → Q → Prop} {F : Finset Q} (hv : ValidPat k O F)
    {q : Q} (hq : q ∉ F) : ∃ r ≤ k + 1, status ⊤ alg (osc x O) r q ≠ none := by
  obtain ⟨r, hr, h⟩ := hfast (padScenario ⊤ alg (osc x O) ↑F)
    (reliable_padScenario _ _ fun r p q hd => hv.1 r p q hd)
    (by simp only [padScenario, osc, Set.empty_union, Set.ncard_coe_finset]; exact hv.2) q
    (by simpa [padScenario, osc] using hq)
  exact ⟨r, hr, by rwa [status_padScenario] at h⟩

omit [Fintype Q] [DecidableEq Q] in
include hBA hk hfast in
theorem sameVal_of_hist2 {x₁ x₂ : Q → V} {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q}
    (hv₁ : ValidPat k O₁ F) (hv₂ : ValidPat k O₂ F) {p : Q} (hp : p ∉ F) (hx : x₁ p = x₂ p)
    (hh : hist ⊤ alg (osc x₁ O₁) (k + 1) p = hist ⊤ alg (osc x₂ O₂) (k + 1) p) :
    SameVal alg x₁ O₁ x₂ O₂ F := by
  have hk' : k ≤ t' := by omega
  intro p₁ hp₁ p₂ hp₂ v w hv hw
  obtain ⟨u, hu⟩ := (osc_BA hBA hk' hv₁ (x := x₁)).1 p (by simpa using hp)
  have hu' := (decides_iff_of_hist ⊤ alg (s₁ := osc x₁ O₁) (s₂ := osc x₂ O₂) hx hh
    (osc_fast2 hfast hv₁ hp) u).1 hu
  rw [(osc_BA hBA hk' hv₁).2.2 p₁ (by simpa using hp₁) p (by simpa using hp) v u hv hu,
    (osc_BA hBA hk' hv₂).2.2 p (by simpa using hp) p₂ (by simpa using hp₂) u w hu' hw]

include hBA hk hfast in
/-- **The hybrid step.** If two omission runs (omitters in `F`, `|F| ≤ k`) can be told apart after
`k` rounds only by `b`, and differ in round `k` only in the messages of `b`, then they lead to the
same decision: a Byzantine `b` (fault number `k + 1 ≤ t'`) shows each run to one honest process. -/
theorem sameVal_hybrid (hn : k + 3 ≤ Fintype.card Q) {x₁ x₂ : Q → V}
    {O₁ O₂ : ℕ → Q → Q → Prop} {F : Finset Q} {b : Q} (hv₁ : ValidPat k O₁ F)
    (hv₂ : ValidPat k O₂ F) (hx : ∀ p, p ≠ b → x₁ p = x₂ p)
    (hh : ∀ p, p ≠ b → hist ⊤ alg (osc x₁ O₁) k p = hist ⊤ alg (osc x₂ O₂) k p)
    (hag : ∀ a, a ≠ b → ∀ d, O₁ k a d ↔ O₂ k a d) : SameVal alg x₁ O₁ x₂ O₂ F := by
  have hk' : k ≤ t' := by omega
  have hFc := hv₁.2
  obtain ⟨q, hq⟩ := exists_not_mem_of_card_lt (insert b F)
    (lt_of_le_of_lt (card_insert_le _ _) (by omega))
  obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt (insert q (insert b F))
    (lt_of_le_of_lt (card_insert_le _ _) (lt_of_le_of_lt (Nat.succ_le_succ (card_insert_le _ _))
      (by omega)))
  have hpq : p ≠ q := fun h => hp (h ▸ mem_insert_self _ _)
  have hp' : p ∉ insert b F := fun h => hp (mem_insert_of_mem h)
  have hpF : p ∉ F := fun h => hp' (mem_insert_of_mem h)
  have hqF : q ∉ F := fun h => hq (mem_insert_of_mem h)
  have hqb : q ≠ b := fun h => hq (h ▸ mem_insert_self _ _)
  set γ := hybrid alg x₁ x₂ O₁ O₂ F b q k
  have hγ : (γ.byz).ncard ≤ t' := by
    simp only [γ, hybrid, Set.ncard_coe_finset]
    have := card_insert_le b F; omega
  have hBAγ := hBA γ hγ (fun _ _ _ h => h)
  -- `p` sees the first run, `q` the second
  obtain ⟨u, hu⟩ := (osc_BA hBA hk' hv₁ (x := x₁)).1 p (by simpa using hpF)
  obtain ⟨w, hw⟩ := (osc_BA hBA hk' hv₂ (x := x₂)).1 q (by simpa using hqF)
  have hu' : Decides ⊤ alg γ p u :=
    (decides_iff_of_hist ⊤ alg (s₁ := osc x₁ O₁) (s₂ := γ) rfl
      (hist_hybrid_left hv₁.1 (k + 1) le_rfl p hp' (Or.inr hpq)).symm
      (osc_fast2 hfast hv₁ hpF) u).1 hu
  have hw' : Decides ⊤ alg γ q w :=
    (decides_iff_of_hist ⊤ alg (s₁ := osc x₂ O₂) (s₂ := γ) (hx q hqb).symm
      (hist_hybrid_right hv₁.1 hv₂.1 hx hh hag hq).symm (osc_fast2 hfast hv₂ hqF) w).1 hw
  have huw : u = w := hBAγ.2.2 p (by simpa [Scenario.honest, γ, hybrid] using hp') q
    (by simpa [Scenario.honest, γ, hybrid] using hq) u w hu' hw'
  intro p₁ hp₁ p₂ hp₂ v v' hv hv'
  rw [(osc_BA hBA hk' hv₁).2.2 p₁ (by simpa using hp₁) p (by simpa using hpF) v u hv hu, huw,
    (osc_BA hBA hk' hv₂).2.2 q (by simpa using hqF) p₂ (by simpa using hp₂) w v' hw hv']

include hBA hk hfast in
/-- **The chain claim with decision round `k + 1`.** Runs with the same inputs, omitters in `F`
(`|F| + j ≤ k + 2`, `|F| ≤ k`) and patterns agreeing on rounds `< k + 1 - j` give the same
decision. -/
theorem sameVal_claim2 (hn : k + 3 ≤ Fintype.card Q) (x : Q → V) :
    ∀ j ≤ k + 1, ∀ F : Finset Q, F.card + j ≤ k + 2 → F.card ≤ k →
      ∀ O₁ O₂ : ℕ → Q → Q → Prop, (∀ r a d, O₁ r a d → a ∈ F) → (∀ r a d, O₂ r a d → a ∈ F) →
        (∀ m < k + 1 - j, ∀ a d, O₁ m a d ↔ O₂ m a d) → SameVal alg x O₁ x O₂ F := by
  have hk' : k ≤ t' := by omega
  intro j
  induction j with
  | zero =>
    intro _ F _ hFk O₁ O₂ h₁ h₂ hag
    obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt F (by omega)
    exact sameVal_of_hist2 hBA hk hfast ⟨h₁, hFk⟩ ⟨h₂, hFk⟩ hp rfl
      (hist_osc_swap alg (k := k + 1) (c := k + 2) (b := p) (fun _ _ => rfl)
        (fun m hm a d _ => hag m (by omega) a d) (fun m h1 h2 => by omega) (k + 1) le_rfl p
        (Or.inr (by omega)))
  | succ j ih =>
    intro hj F hF hFk O₁ O₂ h₁ h₂ hag
    obtain ⟨r₀, hr₀⟩ : ∃ r₀, r₀ + 1 = k + 1 - j := ⟨k - j, by omega⟩
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
      have hagb : ∀ m < k + 1, ∀ a d, (m + 1 = r₀ + 1 → d ≠ b) →
          (mixPat O₁ O₂ r₀ S m a d ↔ mixPat O₁ O₂ r₀ (insert b S) m a d) := by
        intro m _ a d hdb
        unfold mixPat
        by_cases h : m < r₀
        · simp [h]
        · by_cases hm' : m = r₀
          · have hdb' : d ≠ b := hdb (by omega)
            simp [hm', hdb']
          · simp [h, hm']
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
        · -- last round: only `b` can notice the change
          obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt (insert b F)
            (lt_of_le_of_lt (card_insert_le _ _) (by omega))
          have hpb : p ≠ b := fun h => hp (h ▸ mem_insert_self _ _)
          have hpF : p ∉ F := fun h => hp (mem_insert_of_mem h)
          exact sameVal_of_hist2 hBA hk hfast (hmixv S) (hmixv _) hpF rfl
            (hist_osc_swap alg (k := k + 1) (c := r₀ + 1) (b := b) (fun _ _ => rfl)
              (fun m hm a d hdb => hagb m hm a d hdb)
              (fun m h1 h2 => by omega) (k + 1) le_rfl p (Or.inl hpb))
        · -- second-to-last round: the Byzantine hybrid
          refine sameVal_hybrid hBA hk hfast hn (b := b) (hmixv S) (hmixv _) (fun _ _ => rfl)
            (fun p hpb => hist_osc_swap alg (k := k) (c := r₀ + 1) (b := b) (fun _ _ => rfl)
              (fun m hm a d hdb => hagb m (by omega) a d hdb) (fun m h1 h2 => by omega) k le_rfl p
              (Or.inl hpb)) fun a _ d => ?_
          have : ¬ k < r₀ := by omega
          have h' : k ≠ r₀ := by omega
          simp [mixPat, this, h']
      · -- silence `b` after round `r₀` first
        set F' := insert b F with hF'
        have hF'c : F'.card ≤ F.card + 1 := card_insert_le _ _
        have hsilv : ∀ S', ∀ r a d, silPat (mixPat O₁ O₂ r₀ S') b r₀ r a d → a ∈ F' :=
          fun S' r a d h => h.elim (fun h => mem_insert_of_mem ((hmixv S').1 r a d h))
            (fun h => h.1 ▸ mem_insert_self _ _)
        have hagsil : ∀ S', ∀ m < k + 1 - j, ∀ a d,
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
          refine sameVal_of_hist2 hBA hk hfast ⟨hsilv S, by omega⟩ ⟨hsilv _, by omega⟩ hp rfl
            (hist_osc_swap alg (k := k + 1) (c := r₀ + 1) (b := b) (fun _ _ => rfl)
              (fun m hm a d hdb => ?_) (fun m h1 h2 d => ⟨Or.inr ⟨rfl, by omega⟩,
                Or.inr ⟨rfl, by omega⟩⟩) (k + 1) le_rfl p (Or.inl hpb))
          unfold silPat
          rw [hagb m hm a d hdb]
        have h13 := SameVal.trans hBA hk' ⟨hsilv S, by omega⟩ hp h1
          (SameVal.trans hBA hk' ⟨hsilv _, by omega⟩ hp h2 h3)
        exact SameVal.upgrade hBA hk' (hmixv S) (hmixv _) (subset_insert _ _) hp h13
    have hchain : ∀ S, SameVal alg x (mixPat O₁ O₂ r₀ ∅) x (mixPat O₁ O₂ r₀ S) F := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact SameVal.refl hBA hk' (hmixv ∅)
      | insert b S _ ihS => exact SameVal.trans hBA hk' (hmixv S) hp₀ ihS (hone S b)
    exact SameVal.trans hBA hk' (hmixv ∅) hp₀ hstart
      (SameVal.trans hBA hk' (hmixv univ) hp₀ (hchain univ) hend)

end Strong

/-- **The early-deciding lower bound of [DRS90] in the Byzantine model** (the result the paper
cites as [21] in the proof of Theorem 13), proved: for `t' + 2 ≤ |Q|` and at least two values, every
deterministic Byzantine agreement algorithm tolerating `t'` Byzantine faults has, for every
`f' ≤ t'`, a reliable execution with at most `f'` Byzantine processes in which some honest process
has not decided before round `min (f' + 2) (t' + 1)`. -/
theorem earlyDecidingLB_strong {Q V : Type*} [Fintype Q] [DecidableEq Q] [Nontrivial V] {t' : ℕ}
    (hn : t' + 2 ≤ Fintype.card Q) : EarlyDecidingLB Q V t' := by
  intro M alg hBA k hk
  rcases Nat.lt_or_ge k t' with hkt | hkt
  · -- `k < t'`: deciding by round `k + 1` is impossible
    by_contra hcon
    have hk1 : k + 1 ≤ t' := hkt
    have hfast : ∀ s : Scenario Q V M, s.Reliable → s.byz.ncard ≤ k →
        ∀ q ∉ s.byz, ∃ r ≤ k + 1, status ⊤ alg s r q ≠ none := by
      intro s hs hc q hq
      by_contra h
      push Not at h
      exact hcon ⟨s, hs, hc, q, hq, fun r hr => h r (by simp only at hr; omega)⟩
    have hn' : k + 3 ≤ Fintype.card Q := by omega
    have hk' : k ≤ t' := hk
    obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
    let xs : Finset Q → Q → V := fun S p => if p ∈ S then v₁ else v₀
    let O0 : ℕ → Q → Q → Prop := fun _ _ _ => False
    have hv0 : ValidPat k O0 ∅ := ⟨fun _ _ _ h => h.elim, by simp⟩
    have hx : ∀ S a, ∀ q, q ≠ a → xs S q = xs (insert a S) q := by
      intro S a q hq; simp [xs, hq]
    have hstep : ∀ S a, SameVal alg (xs S) O0 (xs (insert a S)) O0 ∅ := by
      intro S a
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · -- `f' = 0`: `a` equivocates in the first round
        exact sameVal_hybrid hBA hk1 hfast hn' (b := a) hv0 hv0 (hx S a) (fun _ _ => rfl)
          (fun _ _ _ => Iff.rfl)
      · let G : Finset Q := {a}
        let Sa : ℕ → Q → Q → Prop := fun m a' _ => a' = a ∧ m < k + 1
        have hGk : G.card ≤ k := by simp [G]; omega
        have hSa : ∀ r a' d, Sa r a' d → a' ∈ G := by
          rintro r a' d ⟨rfl, -⟩; simp [G]
        obtain ⟨p, hp⟩ := exists_not_mem_of_card_lt ({a} : Finset Q) (by simp; omega)
        have hpa : p ≠ a := by simpa using hp
        have hpG : p ∉ G := by simp [G, hpa]
        have h1 := sameVal_claim2 hBA hk1 hfast hn' (xs S) (k + 1) le_rfl G (by simp only [G, card_singleton]; omega)
          hGk O0 Sa (fun _ _ _ h => h.elim) hSa (fun m hm => by omega)
        have h3 := (sameVal_claim2 hBA hk1 hfast hn' (xs (insert a S)) (k + 1) le_rfl G
          (by simp only [G, card_singleton]; omega) hGk O0 Sa (fun _ _ _ h => h.elim) hSa (fun m hm => by omega)).symm
        have hx' : ∀ q, q ≠ a ∨ 0 < 0 → xs S q = xs (insert a S) q := by
          rintro q (hq | hq)
          · exact hx S a q hq
          · omega
        have h2 : SameVal alg (xs S) Sa (xs (insert a S)) Sa G :=
          sameVal_of_hist2 hBA hk1 hfast ⟨hSa, hGk⟩ ⟨hSa, hGk⟩ hpG (hx' p (Or.inl hpa))
            (hist_osc_swap alg (k := k + 1) (c := 0) (b := a) hx' (fun _ _ _ _ _ => Iff.rfl)
              (fun m _ hm _ => ⟨⟨rfl, hm⟩, ⟨rfl, hm⟩⟩) (k + 1) le_rfl p (Or.inl hpa))
        have h13 := SameVal.trans hBA hk' ⟨hSa, hGk⟩ hpG h1
          (SameVal.trans hBA hk' ⟨hSa, hGk⟩ hpG h2 h3)
        exact SameVal.upgrade hBA hk' hv0 hv0 (empty_subset _) hpG h13
    have hchain : ∀ S, SameVal alg (xs ∅) O0 (xs S) O0 ∅ := by
      intro S
      induction S using Finset.induction_on with
      | empty => exact SameVal.refl hBA hk' hv0
      | insert b S _ ihS => exact SameVal.trans hBA hk' hv0 (notMem_empty b) ihS (hstep S b)
    obtain ⟨p⟩ : Nonempty Q := Fintype.card_pos_iff.1 (by omega)
    have d0 := (osc_BA hBA hk' hv0 (x := xs ∅)).2.1 v₀ (fun q _ => by simp [xs]) p (by simp)
    have d1 := (osc_BA hBA hk' hv0 (x := xs univ)).2.1 v₁ (fun q _ => by simp [xs]) p (by simp)
    exact hne (hchain univ p (notMem_empty _) p (notMem_empty _) v₀ v₁ d0 d1)
  · -- `k = t'`: the bound is `t' + 1 = k + 1`, the classical one
    obtain ⟨s, hs, hc, q, hq, h⟩ := earlyDecidingLB_weak (V := V) hn M alg hBA k hk
    exact ⟨s, hs, hc, q, hq, fun r hr => h r (by beta_reduce at hr ⊢; omega)⟩

/-- The cited bound holds for every value type with at least two values. -/
theorem drsBound (V : Type*) [Nontrivial V] : DRSBound V :=
  fun _ _ _ hn => by classical exact earlyDecidingLB_strong hn

/-- **Theorem 13 of [BDEG25]**, unconditional. For every deterministic algorithm `alg` solving
Byzantine agreement with classification predictions against `t` Byzantine faults (for all
predictions), with at least two values, every `f ≤ t < n - 1` and every bound `Bd` on the number of
wrong prediction bits, there is a reliable execution with exactly `f` Byzantine processes and at
most `Bd` wrong bits given to honest processes, in which some honest process has not decided before
round `min {f + 2, t + 1, ⌊Bd/(n - f)⌋ + 2, ⌊Bd/(n - t)⌋ + 1}`. -/
theorem theorem13 {P V : Type} [Fintype P] [DecidableEq P] [Nontrivial V] {M : Type}
    {alg : Cslib.Byzantine.LockStep.Protocol P (V × (P → Bool)) M V} {t f : ℕ}
    (hA : Solves ⊤ alg {S | S.ncard ≤ t} BAP) (hft : f ≤ t) (htn : t + 2 ≤ Fintype.card P)
    (Bd : ℕ) :
    ∃ (s : Scenario P (V × (P → Bool)) M) (F : Finset P),
      s.Reliable ∧ s.byz = ↑F ∧ F.card = f ∧ wrongBits F (fun i => (s.input i).2) ≤ Bd ∧
      ∃ p ∉ F, ∀ r < min (min (f + 2) (t + 1))
          (min (Bd / (Fintype.card P - f) + 2) (Bd / (Fintype.card P - t) + 1)),
        status ⊤ alg s r p = none :=
  roundLowerBound_of_DRS hA hft htn Bd (drsBound V)

end BAWithPredictions
