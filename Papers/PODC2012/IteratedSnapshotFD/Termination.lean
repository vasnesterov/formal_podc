import Papers.PODC2012.IteratedSnapshotFD.Consensus

/-!
# Termination of the consensus algorithm of Figure 5 (Lemma 2) and Theorem 5

`Ω*` (Section 2.6 applied to `Ω`): there is a strongly correct process `ℓ` and a round after which
every process reads `ℓ` from its failure detector (`OmegaStar`).

* `Exec.termination` (Lemma 2): every strongly correct process decides. In fact every *correct*
  process decides (`Exec.termination_correct`): once a strongly correct process has decided, the
  decision reaches all correct processes, weakly correct ones included.
* `theorem5`: Figure 5 solves consensus in `IIS_n[Ω*]` (validity, agreement, termination).
-/

set_option linter.unusedSectionVars false

namespace Podc.IteratedSnapshotFD

variable {P V : Type} [DecidableEq P]

/-- The failure detector class `Ω*`: after some round all processes read the same leader `ℓ`, and
`ℓ` is strongly correct. -/
def OmegaStar (σ : Schedule P) (ld : ℕ → P → P) : Prop :=
  ∃ l ∈ σ.SC, ∃ R, ∀ r ≥ R, ∀ i ∈ (σ.rd r).part, ld r i = l

namespace Exec

variable {σ : Schedule P} {input : P → V} (E : Exec σ input)

/-- Decisions are stable. -/
theorem dec_succ {r : ℕ} {i : P} (h : (E.st r i).dec = true) : (E.st (r + 1) i).dec = true := by
  by_cases hi : i ∈ (σ.rd r).part
  · have hU := E.step' r i hi
    have hW : (E.W r i).dec = true := by simp [W, h]
    generalize E.st (r + 1) i = t at hU
    cases hU with
    | done => exact hW
    | seeDec => rfl
    | unanim => rfl
    | adopt h0 => simp [hW] at h0
    | keep h0 => simp [hW] at h0
    | mixAdopt h0 => simp [hW] at h0
    | mixKeep h0 => simp [hW] at h0
  · rw [E.frozen r i hi]; exact h

/-- A process that sees a decided tuple decides (line 8). -/
theorem dec_of_sees {r : ℕ} {i j : P} (hs : σ.Sees r j i) (h : (E.st r i).dec = true) :
    (E.st (r + 1) j).dec = true := by
  have hU := E.step' r j hs.1
  have hW : (E.W r i).dec = true := by simp [W, h]
  generalize E.st (r + 1) j = t at hU
  cases hU with
  | done h' => exact h'
  | seeDec => rfl
  | unanim => rfl
  | adopt _ hnd => simp [hnd i hs.2] at hW
  | keep _ hnd => simp [hnd i hs.2] at hW
  | mixAdopt _ hnd => simp [hnd i hs.2] at hW
  | mixKeep _ hnd => simp [hnd i hs.2] at hW

/-- Once a strongly correct process has decided, every correct process decides. -/
theorem all_decide_of_SC {i : P} (hi : i ∈ σ.SC) {r : ℕ} (h : (E.st r i).dec = true) :
    ∀ j, σ.Correct j → ∃ r, (E.st r j).dec = true :=
  σ.propagate (fun r i => (E.st r i).dec = true) (fun _ _ _ h => E.dec_succ h)
    (fun _ _ _ _ hs h => E.dec_of_sees hs h) hi h

/-- **Lemma 2 (termination)**, in the stronger form: in `IIS_n[Ω*]` every correct process
decides. -/
theorem termination_correct [Finite P] (hΩ : OmegaStar σ E.ld) :
    ∀ j, σ.Correct j → ∃ r, (E.st r j).dec = true := by
  obtain ⟨l, hlSC, R₀, hR₀⟩ := hΩ
  by_cases hex : ∃ i ∈ σ.SC, ∃ r, (E.st r i).dec = true
  · obtain ⟨i, hi, r, h⟩ := hex
    exact E.all_decide_of_SC hi h
  exfalso
  push Not at hex
  obtain ⟨R₁, hR₁⟩ := σ.eventually_view_SC
  set R := max R₀ R₁ with hR
  have hcorr : ∀ i ∈ σ.SC, ∀ r, i ∈ (σ.rd r).part := fun i hi => σ.correct_of_mem_SC hi
  -- facts on the round-`r` tuples seen by a strongly correct process after round `R`
  have hview : ∀ r ≥ R, ∀ j ∈ σ.SC, ∀ k ∈ (σ.rd r).view j,
      k ∈ σ.SC ∧ (E.W r k).dec = false ∧ (E.W r k).rl = some l := by
    intro r hr j hj k hk
    have hkSC := hR₁ r (le_trans (le_max_right _ _) hr) j hj (hcorr j hj r) k hk
    refine ⟨hkSC, by simp [W, hex k hkSC r], ?_⟩
    simp [W, hR₀ r (le_trans (le_max_left _ _) hr) k (hcorr k hkSC r)]
  -- the step of a strongly correct process after round `R` that sees `ℓ` or a `true` flag
  have hstep : ∀ r ≥ R, ∀ j ∈ σ.SC,
      (∃ k ∈ (σ.rd r).view j, (E.W r k).vls = true ∨ k = l) →
      (E.st (r + 1) j).vls = true ∧ (E.st (r + 1) j).rl = some l := by
    intro r hr j hj hk
    have hU := E.step' r j (hcorr j hj r)
    have hjv := (σ.rd r).self_mem j (hcorr j hj r)
    have hnd := hex j hj (r + 1)
    have hWj := (hview r hr j hj j hjv).2.2
    generalize E.st (r + 1) j = t at hU hnd
    cases hU with
    | done h => simp [(hview r hr j hj j hjv).2.1] at h
    | seeDec _ k hk hd => simp [(hview r hr j hj k hk).2.1] at hd
    | unanim => simp at hnd
    | adopt _ _ _ l' hl' v hv =>
      refine ⟨rfl, ?_⟩
      show (E.W r j).rl = some l
      exact hWj
    | keep _ _ _ l' hl' hc =>
      have : l' = some l := by rw [← hl' j hjv, hWj]
      subst this
      obtain ⟨k, hk, hk'⟩ := hk
      rcases hk' with hk' | rfl
      · exact absurd (Or.inr ⟨k, hk, hk', rfl⟩) (hc _)
      · exact absurd (Or.inl ⟨k, hk, rfl, rfl⟩) (hc _)
    | mixAdopt _ _ _ hnl => exact absurd (fun k hk => (hview r hr j hj k hk).2.2) (hnl _)
    | mixKeep _ _ _ hnl => exact absurd (fun k hk => (hview r hr j hj k hk).2.2) (hnl _)
  have hWvls : ∀ r ≥ R, ∀ k ∈ σ.SC, (E.st r k).vls = true → (E.st r k).rl = some l →
      (E.W r k).vls = true := by
    intro r hr k hk hv hrl
    simp [W, wr, hrl, hR₀ r (le_trans (le_max_left _ _) hr) k (hcorr k hk r), hv]
  -- propagate the flag `val_ld_seen = true` among the strongly correct processes
  let Good : ℕ → P → Prop := fun r i =>
    R ≤ r ∧ (i ∈ σ.SC → (E.st r i).vls = true ∧ (E.st r i).rl = some l)
  have hGood : ∀ j, σ.Correct j → ∃ r, Good r j := by
    refine σ.propagate Good ?_ ?_ hlSC (r₀ := R + 1) ?_
    · rintro r i - ⟨hr, hg⟩
      refine ⟨by omega, fun hi => ?_⟩
      obtain ⟨hv, hrl⟩ := hg hi
      exact hstep r hr i hi ⟨i, (σ.rd r).self_mem i (hcorr i hi r),
        Or.inl (hWvls r hr i hi hv hrl)⟩
    · rintro r i j - hs ⟨hr, hg⟩
      refine ⟨by omega, fun hj => ?_⟩
      have hiSC := (hview r hr j hj i hs.2).1
      obtain ⟨hv, hrl⟩ := hg hiSC
      exact hstep r hr j hj ⟨i, hs.2, Or.inl (hWvls r hr i hiSC hv hrl)⟩
    · refine ⟨by omega, fun _ => hstep R le_rfl l hlSC ⟨l, (σ.rd R).self_mem l (hcorr l hlSC R),
        Or.inr rfl⟩⟩
  -- the property is stable for strongly correct processes
  have hstay : ∀ i ∈ σ.SC, ∀ r r', r ≤ r' → Good r i → Good r' i := by
    intro i hi r r' hrr' h
    induction hrr' with
    | refl => exact h
    | step _ ih =>
      obtain ⟨hr, hg⟩ := ih
      refine ⟨by omega, fun _ => ?_⟩
      obtain ⟨hv, hrl⟩ := hg hi
      exact hstep _ hr i hi ⟨i, (σ.rd _).self_mem i (hcorr i hi _),
        Or.inl (hWvls _ hr i hi hv hrl)⟩
  -- a common round where all strongly correct processes have the flag
  classical
  have := Fintype.ofFinite P
  choose! T hT using hGood
  let r := R + Finset.univ.sup T
  have hall : ∀ i ∈ σ.SC, Good r i := fun i hi =>
    hstay i hi _ _ (le_trans (Finset.le_sup (f := T) (Finset.mem_univ i)) (Nat.le_add_left _ _))
      (hT i (σ.correct_of_mem_SC hi))
  have hr : R ≤ r := Nat.le_add_right _ _
  -- now `ℓ` decides at line 9 (Claim C1), a contradiction
  have hU := E.step' r l (hcorr l hlSC r)
  have hlv := (σ.rd r).self_mem l (hcorr l hlSC r)
  have hvlsk : ∀ k ∈ (σ.rd r).view l, (E.W r k).vls = true ∧ (E.W r k).dec = false := by
    intro k hk
    obtain ⟨hkSC, hkd, -⟩ := hview r hr l hlSC k hk
    obtain ⟨hv, hrl⟩ := (hall k hkSC).2 hkSC
    exact ⟨hWvls r hr k hkSC hv hrl, hkd⟩
  have hun : Unanim (E.W r) ((σ.rd r).view l) (E.W r l).est := by
    intro k hk
    refine ⟨(hvlsk k hk).1, ?_⟩
    exact ((E.inv r).1 k ((σ.rd r).view_sub l (hcorr l hlSC r) hk) l (hcorr l hlSC r)
      (hvlsk k hk).1 (hvlsk k hk).2 (hvlsk l hlv).1 (hvlsk l hlv).2).1
  have hnd := hex l hlSC (r + 1)
  generalize E.st (r + 1) l = t at hU hnd
  cases hU with
  | done h => simp [(hvlsk l hlv).2] at h
  | seeDec _ k hk hd => simp [(hvlsk k hk).2] at hd
  | unanim => simp at hnd
  | adopt _ _ hnu => exact hnu _ hun
  | keep _ _ hnu => exact hnu _ hun
  | mixAdopt _ _ hnu => exact hnu _ hun
  | mixKeep _ _ hnu => exact hnu _ hun

/-- **Lemma 2 (termination).** In `IIS_n[Ω*]` every strongly correct process decides. -/
theorem termination [Finite P] (hΩ : OmegaStar σ E.ld) :
    ∀ i ∈ σ.SC, ∃ r, (E.st r i).dec = true :=
  fun i hi => E.termination_correct hΩ i (σ.correct_of_mem_SC hi)

end Exec

/-- **Theorem 5.** The algorithm of Figure 5 solves consensus in `IIS_n[Ω*]`: every decided value
is proposed (validity), no two processes decide differently (agreement), and every strongly
correct process — in fact every correct process — decides (termination). Validity and agreement
hold for arbitrary leader outputs. -/
theorem theorem5 [Finite P] {σ : Schedule P} {input : P → V} (E : Exec σ input)
    (hΩ : OmegaStar σ E.ld) :
    (∀ i v, E.Decides i v → ∃ j, v = input j) ∧
    (∀ i j v v', E.Decides i v → E.Decides j v' → v = v') ∧
    (∀ i, σ.Correct i → ∃ v, E.Decides i v) := by
  refine ⟨fun i v h => E.validity h, fun i j v v' h h' => E.agreement h h', fun i hi => ?_⟩
  obtain ⟨r, hr⟩ := E.termination_correct hΩ i hi
  exact ⟨_, r, hr, rfl⟩

end Podc.IteratedSnapshotFD
