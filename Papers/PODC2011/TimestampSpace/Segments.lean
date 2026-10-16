import Papers.PODC2011.TimestampSpace.EFR

/-!
# Paused solo segments

Building blocks of the covering construction of Section 4 (Lemma 4.1): a process `p` invokes
`getTS` and runs solo until it either returns or is *poised to change a base object outside a
set `R`* (`WritesOut R`). The resulting label list is `seg R p Z`. If the segment ends with `p`
poised to write outside `R` we say that `p` is *paused* (`Paused`); for read/write-like base
objects it then covers an object outside `R`.

A list of processes run one after the other in this way gives `segMoves R Z L` (a list of
"moves": process and its labels). `AllPaused R Z L` says that every process of `L` pauses.
Everything only depends on what the moving processes can observe (`AllPaused_agreeOn`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} (I : Impl (tsObj T) B P L)

/-- An action that changes a base object outside `R` (a non-read-only access to an object
`i ∉ R`). -/
def WritesOut (R : Set ι) : Action (tsObj T) B L → Prop
  | .access i o _ => i ∉ R ∧ ¬ (B i).ReadOnly o
  | .ret _ _ => False

/-- Stopping condition of a segment: `p` has returned or is poised to write outside `R`. -/
def Stop (R : Set ι) (p : P) (Z : Config (tsObj T) B P L) : Prop :=
  Z.pend p = none ∨ WritesOut R (I.act p (Z.loc p))

/-- `p` is paused: pending and poised to write outside `R`. -/
def Paused (R : Set ι) (p : P) (Z : Config (tsObj T) B P L) : Prop :=
  Z.pend p ≠ none ∧ WritesOut R (I.act p (Z.loc p))

/-- Number of solo steps until the stopping condition holds (`0` if it never does). -/
noncomputable def pauseTime (R : Set ι) (p : P) (Z : Config (tsObj T) B P L) : ℕ := by
  classical
  exact if h : ∃ m, Stop I R p ((I.soloStep p)^[m] Z) then Nat.find h else 0

/-- A segment: `p` invokes `getTS` and runs solo until it stops. -/
noncomputable def seg (R : Set ι) (p : P) (Z : Config (tsObj T) B P L) :
    List (Label P (tsObj T)) :=
  match I.step Z (.inv p .getTS) with
  | some Z₁ => .inv p .getTS :: I.soloLabels p Z₁ (pauseTime I R p Z₁)
  | none => []

/-- Moves: process and its labels. -/
abbrev flat (ms : List (P × List (Label P (tsObj T)))) : List (Label P (tsObj T)) :=
  ms.flatMap Prod.snd

/-- Segments of the processes of `L`, one after the other, starting from `Z`. -/
noncomputable def segMoves (R : Set ι) :
    Config (tsObj T) B P L → List P → List (P × List (Label P (tsObj T)))
  | _, [] => []
  | Z, p :: ps => (p, seg I R p Z) :: segMoves R ((I.runFrom Z (seg I R p Z)).getD Z) ps

/-- Every process of `L` pauses in its segment. -/
def AllPaused (R : Set ι) : Config (tsObj T) B P L → List P → Prop
  | _, [] => True
  | Z, p :: ps => ∃ Z', I.runFrom Z (seg I R p Z) = some Z' ∧ Paused I R p Z' ∧ AllPaused R Z' ps

variable {I}

lemma pauseTime_lt {R : Set ι} {p : P} {Z : Config (tsObj T) B P L} {j : ℕ}
    (hj : j < pauseTime I R p Z) : ¬ Stop I R p ((I.soloStep p)^[j] Z) := by
  classical
  unfold pauseTime at hj
  split_ifs at hj with h
  · exact Nat.find_min h hj
  · omega

lemma pauseTime_spec {R : Set ι} {p : P} {Z : Config (tsObj T) B P L}
    (h : ∃ m, Stop I R p ((I.soloStep p)^[m] Z)) :
    Stop I R p ((I.soloStep p)^[pauseTime I R p Z] Z) := by
  classical
  unfold pauseTime
  rw [dite_eq_left h]; exact Nat.find_spec h

lemma not_writesOut_access {R : Set ι} {a : Action (tsObj T) B L} (h : ¬ WritesOut R a) :
    ∀ i o k, a = .access i o k → i ∉ R → (B i).ReadOnly o := by
  intro i o k ha hi
  subst ha
  by_contra hro
  exact h ⟨hi, hro⟩

lemma iterate_mem_of_lt_pauseTime {R : Set ι} {p : P} {Z : Config (tsObj T) B P L} :
    ∀ i ∉ R, ((I.soloStep p)^[pauseTime I R p Z] Z).mem i = Z.mem i := by
  apply iterate_soloStep_mem_of_readOnly
  intro j hj i o k hact hi
  have hns := pauseTime_lt hj
  simp only [Stop, not_or] at hns
  exact not_writesOut_access hns.2 i o k hact hi

lemma seg_procs (R : Set ι) (p : P) (Z : Config (tsObj T) B P L) :
    ∀ ℓ ∈ seg I R p Z, ℓ.proc = p := by
  unfold seg
  split
  · intro ℓ hℓ
    rcases List.mem_cons.1 hℓ with rfl | hℓ
    · rfl
    · exact I.soloLabels_proc p _ _ ℓ hℓ
  · simp

lemma opsOf_seg_length (R : Set ι) (p q : P) (Z : Config (tsObj T) B P L) :
    (opsOf (seg I R p Z) q).length ≤ if q = p then 1 else 0 := by
  by_cases hq : q = p
  · subst hq
    unfold seg
    split
    · rw [opsOf_cons, opsOf_soloLabels]; simp
    · simp
  · rw [opsOf_eq_nil_of_proc_ne (fun ℓ hℓ h => hq (h.symm.trans (seg_procs R p Z ℓ hℓ)))]
    simp [hq]

lemma getTSCount_seg_le (R : Set ι) (p q : P) (Z : Config (tsObj T) B P L) :
    getTSCount (seg I R p Z) q ≤ if q = p then 1 else 0 :=
  (getTSCount_le_length _ _).trans (opsOf_seg_length R p q Z)

lemma getTSCount_seg_le' (R : Set ι) (p q : P) (Z : Config (tsObj T) B P L) :
    getTSCount (seg I R p Z) q ≤ if p = q then 1 else 0 := by
  have := getTSCount_seg_le (I := I) R p q Z
  rcases eq_or_ne p q with e | e
  · subst e; simpa using this
  · simpa [e, Ne.symm e] using this

lemma seg_mem {R : Set ι} {p : P} {Z Z' : Config (tsObj T) B P L}
    (h : I.runFrom Z (seg I R p Z) = some Z') : ∀ i ∉ R, Z'.mem i = Z.mem i := by
  unfold seg at h
  split at h
  · rename_i Z₁ hs
    rw [runFrom_cons, hs, Option.bind_some, runFrom_soloLabels] at h
    cases h
    intro i hi
    rw [iterate_mem_of_lt_pauseTime i hi, (step_inv hs).2.2.2.2]
  · cases h; intro _ _; rfl

/-- The segment of `p`, started from a configuration reached by an admissible execution in which
`p` is idle, stops; if `p` has returned it has completed exactly one `getTS`. -/
lemma seg_spec {os : Bool} (hI : IsTS I os) (R : Set ι) (p : P) {α : List (Label P (tsObj T))}
    {Z : Config (tsObj T) B P L} (hα : I.run α = some Z) (hp : Z.pend p = none)
    (hadm : Adm os (α ++ [.inv p .getTS])) :
    ∃ Z', I.runFrom Z (seg I R p Z) = some Z' ∧ Stop I R p Z' ∧
      opsOf (seg I R p Z) p = [.getTS] ∧ (Z'.pend p = none → (respsOf (seg I R p Z) p).length = 1) := by
  classical
  obtain ⟨Z₁, hs⟩ : ∃ Z₁, I.step Z (.inv p .getTS) = some Z₁ := by
    simp [step, hp, hI.allowed p]
  have hZ₁p : Z₁.pend p ≠ none := by
    have := (step_inv hs).2.2.1; simp [this]
  have hrun₁ : I.run (α ++ [.inv p .getTS]) = some Z₁ := by
    rw [run_append_of_eq I hα, runFrom_singleton, hs]
  obtain ⟨K, hK⟩ := hI.progress _ Z₁ p hrun₁ hadm hZ₁p
  have hex : ∃ m, Stop I R p ((I.soloStep p)^[m] Z₁) := ⟨K, Or.inl hK⟩
  have hseg : seg I R p Z = .inv p .getTS :: I.soloLabels p Z₁ (pauseTime I R p Z₁) := by
    simp only [seg, hs]
  have hrun : I.runFrom Z (seg I R p Z) =
      some ((I.soloStep p)^[pauseTime I R p Z₁] Z₁) := by
    rw [hseg, runFrom_cons, hs, Option.bind_some, runFrom_soloLabels]
  refine ⟨_, hrun, pauseTime_spec hex, ?_, ?_⟩
  · rw [hseg, opsOf_cons, opsOf_soloLabels]; simp
  · intro hpn
    have := I.runFrom_counts hrun p 0 0 (Or.inl ⟨hp, rfl⟩)
    rw [hseg, opsOf_cons, opsOf_soloLabels] at this
    simp only [hpn, true_and, ne_eq, not_true_eq_false, false_and, or_false] at this
    rw [hseg]; simpa using this.symm

lemma pauseTime_eq_of_agree {R : Set ι} {p : P} {Z Z₂ : Config (tsObj T) B P L}
    (h : Agree p Z Z₂) : pauseTime I R p Z = pauseTime I R p Z₂ := by
  classical
  have hiff : ∀ k, Stop I R p ((I.soloStep p)^[k] Z) ↔ Stop I R p ((I.soloStep p)^[k] Z₂) := by
    intro k
    have hk := iterate_soloStep_agree (I := I) h k
    simp only [Stop, hk.pend, hk.loc]
  have hex : (∃ k, Stop I R p ((I.soloStep p)^[k] Z)) ↔
      ∃ k, Stop I R p ((I.soloStep p)^[k] Z₂) := exists_congr hiff
  unfold pauseTime
  by_cases h1 : ∃ k, Stop I R p ((I.soloStep p)^[k] Z)
  · have h2 := hex.1 h1
    rw [dite_eq_left h1, dite_eq_left h2]
    apply le_antisymm
    · exact Nat.find_min' h1 ((hiff _).2 (Nat.find_spec h2))
    · exact Nat.find_min' h2 ((hiff _).1 (Nat.find_spec h1))
  · rw [dite_eq_right h1, dite_eq_right (fun h2 => h1 (hex.2 h2))]

lemma seg_eq_of_agree {R : Set ι} {p : P} {Z Z₂ : Config (tsObj T) B P L} (h : Agree p Z Z₂) :
    seg I R p Z = seg I R p Z₂ := by
  unfold seg
  cases hC : I.step Z (.inv p .getTS) with
  | none =>
    rw [(step_eq_none_iff_of_agree h (rfl : (Label.inv p (TSOp.getTS : (tsObj T).Op)).proc = p)).1 hC]
  | some Z₁ =>
    obtain ⟨D', hD', hag⟩ := step_agree h rfl hC
    rw [hD']
    simp only
    rw [pauseTime_eq_of_agree hag, soloLabels_eq_of_agree hag]

lemma Paused.covers (hB : RWLike B) {R : Set ι} {p : P} {Z : Config (tsObj T) B P L}
    (h : Paused I R p Z) : ∃ r ∉ R, I.Covers Z p r := by
  obtain ⟨hp, hw⟩ := h
  revert hw
  cases hact : I.act p (Z.loc p) with
  | access i o k =>
    intro hw
    obtain ⟨hi, hro⟩ := hw
    exact ⟨i, hi, hp, o, k, hact, (hB i o).resolve_left hro⟩
  | ret r l => intro hw; exact hw.elim

lemma Paused.congr {R : Set ι} {p : P} {Z Z₂ : Config (tsObj T) B P L}
    (hl : Z.loc p = Z₂.loc p) (hpe : Z.pend p = Z₂.pend p) (h : Paused I R p Z) :
    Paused I R p Z₂ := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨hpe ▸ h1, hl ▸ h2⟩

/-! ### Lists of segments -/

lemma segMoves_map_fst (R : Set ι) (Z : Config (tsObj T) B P L) (Ls : List P) :
    (segMoves I R Z Ls).map Prod.fst = Ls := by
  induction Ls generalizing Z with
  | nil => rfl
  | cons p ps ih => simp [segMoves, ih]

lemma segMoves_procs (R : Set ι) (Z : Config (tsObj T) B P L) (Ls : List P) :
    ∀ m ∈ segMoves I R Z Ls, ∀ ℓ ∈ m.2, ℓ.proc = m.1 := by
  induction Ls generalizing Z with
  | nil => simp [segMoves]
  | cons p ps ih =>
    intro m hm
    simp only [segMoves, List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact seg_procs R p Z
    · exact ih _ m hm

lemma flat_procs {ms : List (P × List (Label P (tsObj T)))}
    (h : ∀ m ∈ ms, ∀ ℓ ∈ m.2, ℓ.proc = m.1) : ∀ ℓ ∈ flat ms, ℓ.proc ∈ ms.map Prod.fst := by
  intro ℓ hℓ
  obtain ⟨m, hm, hℓm⟩ := List.mem_flatMap.1 hℓ
  rw [h m hm ℓ hℓm]; exact List.mem_map_of_mem hm

lemma getTSCount_segMoves_le (R : Set ι) (Z : Config (tsObj T) B P L) (Ls : List P) (q : P) :
    getTSCount (flat (segMoves I R Z Ls)) q ≤ Ls.count q := by
  induction Ls generalizing Z with
  | nil => simp [segMoves, getTSCount, opsOf]
  | cons p ps ih =>
    have h1 := getTSCount_seg_le (I := I) R p q Z
    have h2 := ih ((I.runFrom Z (seg I R p Z)).getD Z)
    show getTSCount (seg I R p Z ++ flat (segMoves I R _ ps)) q ≤ _
    rw [getTSCount_append, List.count_cons]
    by_cases hq : q = p
    · subst hq; simp at h1 ⊢; omega
    · simp [hq, Ne.symm hq] at h1 ⊢; omega

/-- Running a list of paused segments: the run exists, does not change the memory outside `R`
nor the processes outside the list, and every process is paused right after its own segment. -/
lemma AllPaused.run {R : Set ι} {Z : Config (tsObj T) B P L} {Ls : List P}
    (h : AllPaused I R Z Ls) :
    ∃ V, I.runFrom Z (flat (segMoves I R Z Ls)) = some V ∧ (∀ i ∉ R, V.mem i = Z.mem i) ∧
      (∀ q ∉ Ls, V.loc q = Z.loc q ∧ V.pend q = Z.pend q) ∧
      (∀ M' m M'', segMoves I R Z Ls = M' ++ m :: M'' →
        ∃ Y, I.runFrom Z (flat (M' ++ [m])) = some Y ∧ Paused I R m.1 Y) := by
  induction Ls generalizing Z with
  | nil =>
    refine ⟨Z, rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun M' m M'' hM => ?_⟩
    simp [segMoves] at hM
  | cons p ps ih =>
    obtain ⟨Z', hZ', hpZ', hrest⟩ := h
    obtain ⟨V, hV, hVm, hVo, hVs⟩ := ih hrest
    have hdef : segMoves I R Z (p :: ps) = (p, seg I R p Z) :: segMoves I R Z' ps := by
      simp [segMoves, hZ']
    refine ⟨V, ?_, ?_, ?_, ?_⟩
    · rw [hdef]
      show I.runFrom Z (seg I R p Z ++ flat (segMoves I R Z' ps)) = _
      rw [runFrom_append_of_eq I hZ']; exact hV
    · intro i hi; rw [hVm i hi, seg_mem hZ' i hi]
    · intro q hq
      have hq1 : q ≠ p := fun h => hq (by simp [h])
      have hq2 : q ∉ ps := fun h => hq (by simp [h])
      have := I.runFrom_other hZ' (fun ℓ hℓ he => hq1 (he.symm.trans (seg_procs R p Z ℓ hℓ)))
      rw [(hVo q hq2).1, (hVo q hq2).2, this.1, this.2]; exact ⟨rfl, rfl⟩
    · intro M' m M'' hM
      rw [hdef] at hM
      cases M' with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at hM
        obtain ⟨rfl, -⟩ := hM
        exact ⟨Z', by simpa using hZ', hpZ'⟩
      | cons m₀ M₁ =>
        simp only [List.cons_append, List.cons.injEq] at hM
        obtain ⟨rfl, hM⟩ := hM
        obtain ⟨Y, hY, hpY⟩ := hVs M₁ m M'' hM
        refine ⟨Y, ?_, hpY⟩
        show I.runFrom Z (seg I R p Z ++ flat (M₁ ++ [m])) = _
        rw [runFrom_append_of_eq I hZ']; exact hY

/-- Paused segments only depend on what the moving processes observe. -/
lemma AllPaused.of_agreeOn {R : Set ι} {Q : Set P} {Z Z₂ : Config (tsObj T) B P L} {Ls : List P}
    (hag : AgreeOn Q Z Z₂) (hQ : ∀ p ∈ Ls, p ∈ Q) (h : AllPaused I R Z Ls) :
    segMoves I R Z Ls = segMoves I R Z₂ Ls ∧ AllPaused I R Z₂ Ls := by
  induction Ls generalizing Z Z₂ with
  | nil => exact ⟨rfl, trivial⟩
  | cons p ps ih =>
    obtain ⟨Z', hZ', hpZ', hrest⟩ := h
    have hpQ : p ∈ Q := hQ p (by simp)
    have hseq : seg I R p Z = seg I R p Z₂ := seg_eq_of_agree (hag.agree hpQ)
    obtain ⟨Z₂', hZ₂', hag'⟩ := runFrom_agreeOn (I := I) hag
      (fun ℓ hℓ => by rw [seg_procs R p Z ℓ hℓ]; exact hpQ) hZ'
    rw [hseq] at hZ₂'
    obtain ⟨h1, h2⟩ := ih hag' (fun q hq => hQ q (by simp [hq])) hrest
    refine ⟨?_, Z₂', hZ₂', hpZ'.congr (hag'.loc p hpQ) (hag'.pend p hpQ), h2⟩
    simp only [segMoves]
    rw [hZ', Option.getD_some, h1, hseq, hZ₂', Option.getD_some]

lemma AllPaused.append_single {R : Set ι} {Z V : Config (tsObj T) B P L} {Ls : List P} {q : P}
    (h : AllPaused I R Z Ls) (hV : I.runFrom Z (flat (segMoves I R Z Ls)) = some V)
    (hq : ∃ Z', I.runFrom V (seg I R q V) = some Z' ∧ Paused I R q Z') :
    AllPaused I R Z (Ls ++ [q]) := by
  induction Ls generalizing Z with
  | nil =>
    simp only [segMoves, List.flatMap_nil, runFrom_nil, Option.some.injEq] at hV
    subst hV
    obtain ⟨Z', h1, h2⟩ := hq
    exact ⟨Z', h1, h2, trivial⟩
  | cons p ps ih =>
    obtain ⟨Z', hZ', hpZ', hrest⟩ := h
    refine ⟨Z', hZ', hpZ', ih hrest ?_⟩
    simp only [segMoves, hZ', Option.getD_some, List.flatMap_cons] at hV
    rw [runFrom_append_of_eq I hZ'] at hV; exact hV

lemma AllPaused.of_append_single {R : Set ι} {Z : Config (tsObj T) B P L} {Ls : List P} {q : P}
    (h : AllPaused I R Z (Ls ++ [q])) :
    AllPaused I R Z Ls ∧ ∀ V, I.runFrom Z (flat (segMoves I R Z Ls)) = some V →
      ∃ Z', I.runFrom V (seg I R q V) = some Z' ∧ Paused I R q Z' := by
  induction Ls generalizing Z with
  | nil =>
    obtain ⟨Z', h1, h2, -⟩ := h
    refine ⟨trivial, fun V hV => ?_⟩
    simp only [segMoves, List.flatMap_nil, runFrom_nil, Option.some.injEq] at hV
    subst hV; exact ⟨Z', h1, h2⟩
  | cons p ps ih =>
    obtain ⟨Z', hZ', hpZ', hrest⟩ := h
    obtain ⟨h1, h2⟩ := ih hrest
    refine ⟨⟨Z', hZ', hpZ', h1⟩, fun V hV => h2 V ?_⟩
    simp only [segMoves, hZ', Option.getD_some, List.flatMap_cons] at hV
    rw [runFrom_append_of_eq I hZ'] at hV; exact hV

end Cslib.SharedMemory.Timestamp
