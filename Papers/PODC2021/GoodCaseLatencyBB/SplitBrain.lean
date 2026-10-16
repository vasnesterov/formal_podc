import Papers.PODC2021.GoodCaseLatencyBB.Basic

/-!
# The "split-brain" lower bounds: Theorems 4, 6 and 8

Abraham–Nayak–Ren–Xiang, PODC 2021: Theorem 4 (asynchronous BRB needs 2 rounds), Theorem 6
(partially synchronous BB needs 2 rounds), Theorem 8 (synchronous BRB needs `2δ`), all for
`f ≥ 1`. The three proofs are the same argument: a Byzantine broadcaster sends `a` to some honest
`x` and `b` to another honest `y`; before any message sent *after* receiving the proposal arrives,
`x` (resp. `y`) cannot distinguish this from the good-case execution with input `a` (resp. `b`).

We prove one generic statement (`split_brain`) for an arbitrary fixed delivery schedule `dl` in
which nothing is processed before time `Q` and everything sent from time `Q` on is processed after
time `H`; in the runs used, Byzantine processes behave like correct processes with some input
before time `Q` and are silent afterwards (`templateRun` of CSLib's `RoundOne`).

* Lock-step schedule (`dl = nextRound D`): `Q = D + 1`, `H = 2D` — Theorems 4 and 6.
* Uniform effective delay `δ` (`dl = τ + δ − 1`): `Q = δ`, `H = 2δ − 1` — Theorem 8.

All three statements need `n ≥ 3`; for `n = 2` Theorems 4 and 8 are false (see `SmallCases.lean`).
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

variable {P M S V K : Type*} [DecidableEq P]

section generic

variable (A : Algorithm P M S V V)

/-- A schedule in which nothing is processed before time `Q` and every batch sent at a time
`≥ Q` is delivered at a time `≥ H` (hence processed after time `H`). -/
structure EarlySched (Q H : ℕ) (dl : P → ℕ → P → ℕ) : Prop where
  late : ∀ q τ x, Q ≤ dl q τ x + 1
  after : ∀ q τ x, Q ≤ τ → H ≤ dl q τ x

variable {A} {Q H : ℕ} {dl : P → ℕ → P → ℕ}

theorem templateRun_st_quiet (hS : EarlySched Q H dl) {F : Finset P} {I : P → V} {G : ℕ}
    {r1 : P → P → Option V} {later : P → ℕ → P → List M} (x : P) :
    ∀ τ, τ < Q → (templateRun A Q F I G r1 later dl).st A τ x = quiet A x (I x) τ := by
  intro τ hτ
  induction τ with
  | zero => rfl
  | succ τ ih =>
    rw [Run.st_succ, ih (by omega)]
    change _ = A.step x (quiet A x (I x) τ) fun _ => []
    congr 1
    funext q
    rw [Run.inbox_eq_flatMap]
    apply List.flatMap_eq_nil_iff.mpr
    intro τ' _
    exact Run.dlv_eq_nil_of_ne _ _ (by
      change dl q τ' x ≠ τ
      have := hS.late q τ' x; omega)

theorem templateRun_out_quiet (hS : EarlySched Q H dl) {F : Finset P} {I : P → V} {G : ℕ}
    {r1 : P → P → Option V} {later : P → ℕ → P → List M} {τ : ℕ} (hτ : τ < Q) (q x : P) :
    (templateRun A Q F I G r1 later dl).out A q τ x = round1 A q (templateEff F I r1 q x) τ x := by
  by_cases hq : q ∈ F
  · rw [Run.out_of_faulty _ _ hq]
    simp [templateRun, templateEff, hq, hτ]
  · rw [Run.out_of_correct _ _ hq, templateRun_st_quiet hS q τ hτ]
    simp [templateEff, hq, round1]

/-- Two template runs with the same schedule give `x` the same states up to time `H` if `x` has
the same input and the same "effective" early view. -/
theorem templateRun_st_eq (hS : EarlySched Q H dl) {F F' : Finset P} {I I' : P → V} {G G' : ℕ}
    {r1 r1' : P → P → Option V} {later later' : P → ℕ → P → List M} {x : P} (hI : I x = I' x)
    (heff : ∀ q, templateEff F I r1 q x = templateEff F' I' r1' q x) :
    ∀ τ ≤ H, (templateRun A Q F I G r1 later dl).st A τ x =
      (templateRun A Q F' I' G' r1' later' dl).st A τ x := by
  intro τ hτ
  refine (templateRun A Q F I G r1 later dl).st_eq_of_inbox_eq A
    (ref := fun _ => templateRun A Q F' I' G' r1' later' dl) (X := {x}) (T := H) ?_ ?_ τ hτ x rfl
  · rintro p rfl; exact hI
  · rintro τ hτ _ p rfl
    apply Run.inbox_eq_of_dlv_eq
    intro q τ' hτ'
    simp only [Run.dlv]
    change (if dl q τ' p = τ then _ else _) = (if dl q τ' p = τ then _ else _)
    by_cases hd : dl q τ' p = τ
    · have hτ'Q : τ' < Q := by
        by_contra hc; have := hS.after q τ' p (by omega); omega
      simp only [hd, ite_true]
      rw [templateRun_out_quiet hS hτ'Q, templateRun_out_quiet hS hτ'Q, heff q]
    · simp [hd]

/-- A template run whose Byzantine processes are silent from time `Q` on respects
unforgeability. -/
theorem templateRun_authValid {Au : Auth P M K} [Fintype P] (hU : A.Unforging Au) {F : Finset P}
    {I : P → V} {G : ℕ} {r1 : P → P → Option V} :
    (templateRun A Q F I G r1 (fun _ _ _ => []) dl).AuthValid Au A := by
  intro b hb τ r _ m hm k hk
  simp only [templateRun] at hm
  split_ifs at hm
  · left; rw [round1_tokens A hU hm hk]; exact hb
  · simp at hm

/-- **The split-brain argument.** Let `s, x, y` be distinct. Suppose that in the fault-free
template runs where the broadcaster has input `a` (resp. `b`), `x` commits `a` (resp. `y` commits
`b`) by time `H`. Then agreement fails in the run where the Byzantine broadcaster behaves towards
`y` as with input `b` and towards everybody else as with input `a`. -/
theorem split_brain (hS : EarlySched Q H dl) {s x y : P} (hxy : x ≠ y) (hxs : x ≠ s)
    (hys : y ≠ s) {I : P → V} {G : ℕ} {a b : V} (hab : a ≠ b)
    (hx : ∃ τ ≤ H, A.decide x ((templateRun A Q ∅ (Function.update I s a) G
      (fun q _ => some (Function.update I s a q)) (fun _ _ _ => []) dl).st A τ x) = some a)
    (hy : ∃ τ ≤ H, A.decide y ((templateRun A Q ∅ (Function.update I s b) G
      (fun q _ => some (Function.update I s b q)) (fun _ _ _ => []) dl).st A τ y) = some b)
    (hag : ∀ v w, (templateRun (M := M) A Q {s} I G
        (fun q z => if q = s then (if z = y then some b else some a) else some (I q))
        (fun _ _ _ => []) dl).Decides A x v → (templateRun (M := M) A Q {s} I G
        (fun q z => if q = s then (if z = y then some b else some a) else some (I q))
        (fun _ _ _ => []) dl).Decides A y w → v = w) : False := by
  obtain ⟨τx, hτx, hdx⟩ := hx
  obtain ⟨τy, hτy, hdy⟩ := hy
  refine hab (hag a b ⟨τx, ?_⟩ ⟨τy, ?_⟩)
  · rw [templateRun_st_eq hS (I' := Function.update I s a) (by simp [hxs]) (fun q => ?_) τx hτx]
    · exact hdx
    · by_cases hq : q = s
      · subst hq; simp [templateEff, hxy]
      · simp [templateEff, hq]
  · rw [templateRun_st_eq hS (I' := Function.update I s b) (by simp [hys]) (fun q => ?_) τy hτy]
    · exact hdy
    · by_cases hq : q = s
      · subst hq; simp [templateEff]
      · simp [templateEff, hq]

end generic

/-! ### Instances -/

section instances

variable [Fintype P] {A : Algorithm P M S V V} {Au : Auth P M K}

/-- Three distinct processes. -/
theorem exists_three (s : P) (h3 : 3 ≤ Fintype.card P) : ∃ x y : P, x ≠ y ∧ x ≠ s ∧ y ≠ s := by
  have : 1 < (univ.erase s).card := by rw [card_erase_of_mem (mem_univ s)]; simp; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp this
  exact ⟨x, y, hxy, ne_of_mem_erase hx, ne_of_mem_erase hy⟩

/-- The lock-step schedule: round-`r` messages are delivered at time `r D`. -/
theorem earlySched_nextRound {D : ℕ} (hD : 0 < D) :
    EarlySched (P := P) (D + 1) (2 * D) (fun _ τ _ => nextRound D τ) where
  late _ τ _ := by
    rcases Nat.lt_or_ge τ D with h | h
    · show D + 1 ≤ nextRound D τ + 1; rw [nextRound_of_lt h]
    · have := two_le_nextRound (D := D) h; show D + 1 ≤ nextRound D τ + 1; omega
  after _ τ _ h := two_le_nextRound (by omega)

theorem nextRound_valid {D f : ℕ} (hD : 0 < D) {F : Finset P} (hF : F.card ≤ f) {I : P → V}
    {r1 : P → P → Option V} {later : P → ℕ → P → List M} :
    (templateRun A (D + 1) F I 0 r1 later (fun _ τ _ => nextRound D τ)).Valid f D where
  card_faulty := hF
  dl_ge _ _ _ _ _ := (le_nextRound hD).le
  dl_le _ _ _ _ _ := nextRound_le.trans (by simp [templateRun])

/-- The uniform schedule with effective delay `δ`. -/
theorem earlySched_uniform {δ : ℕ} (hδ : 1 ≤ δ) :
    EarlySched (P := P) δ (2 * δ - 1) (fun _ τ _ => τ + δ - 1) where
  late _ _ _ := by omega
  after _ _ _ _ := by omega

theorem uniform_syncValid {δ f : ℕ} (hδ : 1 ≤ δ) {F : Finset P} (hF : F.card ≤ f) {I : P → V}
    {G : ℕ} {r1 : P → P → Option V} {later : P → ℕ → P → List M} :
    SyncValid f δ (templateRun A δ F I G r1 later (fun _ τ _ => τ + δ - 1)) where
  card_faulty := hF
  dl_ge _ _ _ _ _ := by simp only [templateRun]; omega
  dl_lt _ _ _ _ _ := by simp only [templateRun]; omega

/-- Agreement + validity + latency in the good-case template runs give the decisions needed by
`split_brain`. -/
theorem good_decision (hU : A.Unforging Au) {s : P} {Adm : Set (Run P M V)}
    (hA : IsBRB Au A s Adm) {T : ℕ} (hlat : LatencyWithin Au A s Adm T) {Q : ℕ} {I : P → V} {G : ℕ}
    {dl : P → ℕ → P → ℕ} {c : V}
    (hR : templateRun (M := M) A Q ∅ (Function.update I s c) G
      (fun q _ => some (Function.update I s c q)) (fun _ _ _ => []) dl ∈ Adm) (x : P) :
    ∃ τ ≤ T, A.decide x ((templateRun A Q ∅ (Function.update I s c) G
      (fun q _ => some (Function.update I s c q)) (fun _ _ _ => []) dl).st A τ x) = some c := by
  set R := templateRun (M := M) A Q ∅ (Function.update I s c) G
      (fun q _ => some (Function.update I s c q)) (fun _ _ _ => []) dl
  have hRA : R.AuthValid Au A := templateRun_authValid hU
  have hx : x ∉ R.faulty := by simp [R, templateRun]
  have hs : s ∉ R.faulty := by simp [R, templateRun]
  have hval := hA.validity R hR hRA hs x hx
  simp only [R, templateRun, Function.update_self] at hval
  exact (hlat R hR hRA hs x hx).eq_of_agreement
    (fun w h1 h2 => hA.agreement R hR hRA x hx x hx w c h1 h2) hval

/-- **Theorem 4 of [ANRX21]** (asynchronous BRB needs 2 rounds). A Byzantine reliable broadcast
protocol for asynchronous runs (all runs of the model) resilient to `f ≥ 1` faults, with `n ≥ 3`,
does not commit, in every lock-step good-case execution (round length `D`, round-`r` messages
delivered at time `rD`), before receiving the round-2 messages (state at time `2D`). In
particular its good-case latency is not 1 round. -/
theorem theorem_4 (hU : A.Unforging Au) {s : P} {f D : ℕ} (hD : 0 < D) (hf : 1 ≤ f)
    (h3 : 3 ≤ Fintype.card P) {a b : V} (hab : a ≠ b) (hA : IsBRB Au A s (asyncRuns f)) :
    ¬ LatencyWithin Au A s ((psyncGoodRuns f D) ∩ asyncRuns f) (2 * D) := by
  intro hlat
  obtain ⟨x, y, hxy, hxs, hys⟩ := exists_three s h3
  have hS := earlySched_nextRound (P := P) hD
  have mem : ∀ {F : Finset P} (_ : F.card ≤ f) {I : P → V} {r1 : P → P → Option V},
      templateRun (M := M) A (D + 1) F I 0 r1 (fun _ _ _ => []) (fun _ τ _ => nextRound D τ) ∈
        (psyncGoodRuns f D) ∩ asyncRuns f :=
    fun hF => ⟨⟨nextRound_valid hD hF, rfl⟩, ⟨D, nextRound_valid hD hF⟩⟩
  have hA' : IsBRB Au A s ((psyncGoodRuns f D) ∩ asyncRuns f) :=
    ⟨fun R hR => hA.agreement R hR.2, fun R hR => hA.validity R hR.2,
      fun R hR => hA.termination R hR.2⟩
  let I : P → V := fun _ => a
  refine split_brain hS hxy hxs hys (I := I) (G := 0) hab
    (good_decision hU hA' hlat (mem (by simp)) x) (good_decision hU hA' hlat (mem (by simp)) y) ?_
  intro v w hv hw
  have hR := mem (F := {s}) (I := I) (by simp; omega)
    (r1 := fun q z => if q = s then (if z = y then some b else some a) else some (I q))
  exact hA.agreement _ hR.2 (templateRun_authValid hU) x (by simp [templateRun, hxs]) y
    (by simp [templateRun, hys]) v w hv hw

/-- **Theorem 6 of [ANRX21]** (partially synchronous BB needs 2 rounds), stated like Theorem 4. -/
theorem theorem_6 (hU : A.Unforging Au) {s : P} {f D : ℕ} (hD : 0 < D) (hf : 1 ≤ f)
    (h3 : 3 ≤ Fintype.card P) {a b : V} (hab : a ≠ b) (hA : IsPsyncBB Au A s f D) :
    ¬ LatencyWithin Au A s (psyncGoodRuns f D) (2 * D) := by
  intro hlat
  obtain ⟨x, y, hxy, hxs, hys⟩ := exists_three s h3
  have hS := earlySched_nextRound (P := P) hD
  have mem : ∀ {F : Finset P} (_ : F.card ≤ f) {I : P → V} {r1 : P → P → Option V},
      templateRun (M := M) A (D + 1) F I 0 r1 (fun _ _ _ => []) (fun _ τ _ => nextRound D τ) ∈
        psyncGoodRuns f D :=
    fun hF => ⟨nextRound_valid hD hF, rfl⟩
  have hA' : IsBRB Au A s (psyncGoodRuns f D) :=
    ⟨fun R hR => hA.agreement R hR.1, fun R hR hRA => hA.validity R hR.1 hRA hR.2,
      fun R hR hRA _ => hA.termination R hR.1 hRA⟩
  let I : P → V := fun _ => a
  refine split_brain hS hxy hxs hys (I := I) (G := 0) hab
    (good_decision hU hA' hlat (mem (by simp)) x) (good_decision hU hA' hlat (mem (by simp)) y) ?_
  intro v w hv hw
  have hR := mem (F := {s}) (I := I) (by simp; omega)
    (r1 := fun q z => if q = s then (if z = y then some b else some a) else some (I q))
  exact hA.agreement _ hR.1 (templateRun_authValid hU) x (by simp [templateRun, hxs]) y
    (by simp [templateRun, hys]) v w hv hw

/-- Theorem 6 in the paper's formulation: the good-case latency is not 1 round. -/
theorem theorem_6_rounds (hU : A.Unforging Au) {s : P} {f D : ℕ} (hD : 0 < D) (hf : 1 ≤ f)
    (h3 : 3 ≤ Fintype.card P) {a b : V} (hab : a ≠ b) (hA : IsPsyncBB Au A s f D) :
    ¬ PsyncGoodCaseRounds Au A s f D 1 := fun h =>
  theorem_6 hU hD hf h3 hab hA fun R hR hRA hs p hp => by
    obtain ⟨v, τ, hτ, hd⟩ := h R hR hRA hs p hp
    exact ⟨v, τ, by omega, hd⟩

/-- **Theorem 8 of [ANRX21]** (synchronous BRB needs `2δ`). A Byzantine reliable broadcast
protocol for synchronous runs with known delay bound `Δ`, resilient to `f ≥ 1` faults, with
`n ≥ 3`: for every actual delay bound `1 ≤ δ ≤ Δ`, in some good-case run with delays `≤ δ` some
honest process has not committed before time `2δ`. -/
theorem theorem_8 (hU : A.Unforging Au) {s : P} {f Δ δ : ℕ} (hδ : 1 ≤ δ) (hδΔ : δ ≤ Δ)
    (hf : 1 ≤ f) (h3 : 3 ≤ Fintype.card P) {a b : V} (hab : a ≠ b)
    (hA : IsBRB Au A s (syncRuns f Δ)) : ¬ LatencyWithin Au A s (syncRuns f δ) (2 * δ - 1) := by
  intro hlat
  obtain ⟨x, y, hxy, hxs, hys⟩ := exists_three s h3
  have hS := earlySched_uniform (P := P) hδ
  have mem : ∀ {F : Finset P} (_ : F.card ≤ f) {I : P → V} {r1 : P → P → Option V},
      templateRun (M := M) A δ F I 0 r1 (fun _ _ _ => []) (fun _ τ _ => τ + δ - 1) ∈
        syncRuns f δ :=
    fun hF => uniform_syncValid hδ hF
  have hA' : IsBRB Au A s (syncRuns f δ) :=
    ⟨fun R hR => hA.agreement R (SyncValid.mono hR hδΔ),
      fun R hR => hA.validity R (SyncValid.mono hR hδΔ),
      fun R hR => hA.termination R (SyncValid.mono hR hδΔ)⟩
  let I : P → V := fun _ => a
  refine split_brain hS hxy hxs hys (I := I) (G := 0) hab
    (good_decision hU hA' hlat (mem (by simp)) x) (good_decision hU hA' hlat (mem (by simp)) y) ?_
  intro v w hv hw
  have hR := mem (F := {s}) (I := I) (by simp; omega)
    (r1 := fun q z => if q = s then (if z = y then some b else some a) else some (I q))
  exact hA'.agreement _ hR (templateRun_authValid hU) x (by simp [templateRun, hxs]) y
    (by simp [templateRun, hys]) v w hv hw

end instances

end GoodCaseLatencyBB
