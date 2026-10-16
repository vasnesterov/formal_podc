import Papers.PODC2011.TimestampSpace.Segments

/-!
# Lemma 4.1 of the paper

Let `C` be reachable by a one-shot execution, let `B₀, B₁, B₂` be disjoint sets of processes each
covering a set `R` of base objects, and let `U` be a list of at least two idle processes. Then
there is a schedule `β σ β' σ'` where `{β, β'}` are the block writes by `B₀` and `B₁`, `σ` and `σ'`
are concatenations of paused solo segments of distinct processes of `U` (every one of them is,
right after its own segment, poised to write outside `R`), `|σ| + |σ'| = |U| - 1` and
`|σ| ≥ ⌊|U|/2⌋`.

We return the schedule as *moves* (process, labels), which is what the proof of Theorem 1.2 needs:
`M₀` (the segments of `σ`) and `M₁` (those of `σ'`), with the covering property stated right after
each segment. Since the processes of a segment never move again, the covering also holds at the
end (part (b) of the lemma), see `SD.moved_U` in `OneShotStep.lean`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp

open Cslib.SharedMemory Impl

variable {P : Type} [DecidableEq P] {T : Type} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
  {L : Type} {I : Impl (tsObj T) B P L}

/-- The setting of Lemma 4.1: `C` reached by the one-shot execution `α`; `b₀, b₁, b₂` disjoint
lists of (process, object) pairs covering `R`. -/
structure CovSetup (I : Impl (tsObj T) B P L) (α : List (Label P (tsObj T)))
    (C : Config (tsObj T) B P L) (R : Set ι) (b₀ b₁ b₂ : List (P × ι)) : Prop where
  run : I.run α = some C
  adm : Adm true α
  nd : (b₀.map Prod.fst ++ b₁.map Prod.fst ++ b₂.map Prod.fst).Nodup
  cov : ∀ c ∈ b₀ ++ b₁ ++ b₂, I.Covers C c.1 c.2
  R₀ : ∀ i, i ∈ R ↔ i ∈ b₀.map Prod.snd
  R₁ : ∀ i, i ∈ R ↔ i ∈ b₁.map Prod.snd
  R₂ : ∀ i, i ∈ R ↔ i ∈ b₂.map Prod.snd

lemma CovSetup.swap {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L} {R : Set ι}
    {b₀ b₁ b₂ : List (P × ι)} (S : CovSetup I α C R b₀ b₁ b₂) : CovSetup I α C R b₁ b₀ b₂ where
  run := S.run
  adm := S.adm
  nd := by
    have := S.nd
    refine (List.perm_append_comm.append_right _).nodup_iff.1 this
  cov := fun c hc => S.cov c (by simp only [List.mem_append] at hc ⊢; tauto)
  R₀ := S.R₁
  R₁ := S.R₀
  R₂ := S.R₂

lemma pend_none_of_idle {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L}
    (h : I.run α = some C) {p : P} (hp : opsOf α p = []) : C.pend p = none := by
  rcases I.run_counts h p with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact h1
  · rw [hp] at h2; simp at h2

lemma not_idle_of_pend {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L}
    (h : I.run α = some C) {p : P} (hp : C.pend p ≠ none) : opsOf α p ≠ [] :=
  fun h' => hp (pend_none_of_idle h h')

/-- Admissibility of an extension in which only previously idle processes invoke `getTS`, each at
most once. -/
lemma adm_append_of_count {α β : List (Label P (tsObj T))} (hα : Adm true α) (c : P → ℕ)
    (hc : ∀ p, c p ≤ 1) (hidle : ∀ p, c p ≠ 0 → opsOf α p = [])
    (hβ : ∀ p, getTSCount β p ≤ c p) : Adm true (α ++ β) := by
  intro _ p
  rw [getTSCount_append]
  have h1 := hβ p
  by_cases hp : c p = 0
  · have := hα rfl p; omega
  · have h2 : getTSCount α p = 0 := by simp [getTSCount, hidle p hp]
    have := hc p; omega

lemma getTSCount_inv_getTS (q p : P) :
    getTSCount [(.inv q .getTS : Label P (tsObj T))] p = if q = p then 1 else 0 := by
  by_cases h : q = p
  · subst h; simp [getTSCount, opsOf, TSOp.isGetTS]
  · simp [getTSCount, opsOf, Label.invOf, h]

variable {α : List (Label P (tsObj T))} {C : Config (tsObj T) B P L} {R : Set ι}
  {b₀ b₁ b₂ : List (P × ι)}

lemma CovSetup.pend_of_mem (S : CovSetup I α C R b₀ b₁ b₂) {c : P × ι} (hc : c ∈ b₀ ++ b₁ ++ b₂) :
    C.pend c.1 ≠ none := (S.cov c hc).1

lemma CovSetup.not_idle (S : CovSetup I α C R b₀ b₁ b₂) {c : P × ι} (hc : c ∈ b₀ ++ b₁ ++ b₂)
    {p : P} (hp : opsOf α p = []) : c.1 ≠ p := by
  intro h; subst h
  exact S.pend_of_mem hc (pend_none_of_idle S.run hp)

/-- Running the paused segments of `L₀` after the block write by `b₀`. -/
lemma CovSetup.side (S : CovSetup I α C R b₀ b₁ b₂) {W : Config (tsObj T) B P L}
    (hW : I.runFrom C (bw b₀) = some W) {Ls : List P} (hL : AllPaused I R W Ls) :
    ∃ V, I.runFrom W (flat (segMoves I R W Ls)) = some V ∧
      I.run (α ++ bw b₀ ++ flat (segMoves I R W Ls)) = some V ∧
      (∀ i ∉ R, V.mem i = C.mem i) ∧
      (∀ q, q ∉ Ls → q ∉ b₀.map Prod.fst → V.loc q = C.loc q ∧ V.pend q = C.pend q) := by
  obtain ⟨V, hV, hVm, hVo, -⟩ := hL.run
  obtain ⟨W', hW', hWo, hWm⟩ := blockWrite_run (I := I) (cs := b₀)
    (by have := S.nd; exact (this.sublist (by simp)))
    (fun c hc => S.cov c (by simp [hc]))
  rw [hW] at hW'; cases hW'
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · rw [List.append_assoc, run_append_of_eq I S.run, runFrom_append_of_eq I hW, hV]
  · intro i hi
    rw [hVm i hi, hWm i (fun h => hi ((S.R₀ i).2 h))]
  · intro q hq1 hq2
    rw [(hVo q hq1).1, (hVo q hq1).2, (hWo q hq2).1, (hWo q hq2).2]; exact ⟨rfl, rfl⟩

/-- One application of Lemma 2.1 inside the proof of Lemma 4.1: of the two pending complete
`getTS` segments, at least one pauses (is poised to write outside `R` before returning). -/
lemma two_choice (hI : IsTS I true) (S : CovSetup I α C R b₀ b₁ b₂) {W₀ W₁ : Config (tsObj T) B P L}
    (hW₀ : I.runFrom C (bw b₀) = some W₀) (hW₁ : I.runFrom C (bw b₁) = some W₁)
    (L₀ L₁ : List P) (q₀ q₁ : P) (hnd : (L₀ ++ [q₀] ++ L₁ ++ [q₁]).Nodup)
    (hidle : ∀ p ∈ L₀ ++ [q₀] ++ L₁ ++ [q₁], opsOf α p = [])
    (h₀ : AllPaused I R W₀ L₀) (h₁ : AllPaused I R W₁ L₁) :
    AllPaused I R W₀ (L₀ ++ [q₀]) ∨ AllPaused I R W₁ (L₁ ++ [q₁]) := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  -- counting
  set cK : P → ℕ := fun p =>
    L₀.count p + (if q₀ = p then 1 else 0) + L₁.count p + (if q₁ = p then 1 else 0) with hcK
  have hKc : ∀ p, cK p ≤ 1 := by
    intro p; have := List.nodup_iff_count_le_one.1 hnd p
    simpa only [List.count_append, List.count_singleton, beq_iff_eq] using this
  have hKmem : ∀ p, cK p ≠ 0 → opsOf α p = [] := by
    intro p hp
    apply hidle
    simp only [List.mem_append, List.mem_singleton]
    by_contra hn
    simp only [not_or] at hn
    apply hp
    simp only [hcK, List.count_eq_zero_of_not_mem hn.1.1.1, List.count_eq_zero_of_not_mem hn.1.2,
      ite_eq_right (Ne.symm hn.1.1.2), ite_eq_right (Ne.symm hn.2)]
  have hq₀L₀ : q₀ ∉ L₀ := fun h => by
    have h1 := hKc q₀; have h2 := List.count_pos_iff.2 h
    simp only [hcK, ite_true] at h1; omega
  have hq₁L₁ : q₁ ∉ L₁ := fun h => by
    have h1 := hKc q₁; have h2 := List.count_pos_iff.2 h
    simp only [hcK, ite_true] at h1; omega
  have hdisj : ∀ p, (p ∈ L₀ ∨ p = q₀) → (p ∈ L₁ ∨ p = q₁) → False := by
    intro p h0 h1
    have hk := hKc p
    have a0 : 1 ≤ L₀.count p + (if q₀ = p then 1 else 0) := by
      rcases h0 with h | rfl
      · have := List.count_pos_iff.2 h; omega
      · simp
    have a1 : 1 ≤ L₁.count p + (if q₁ = p then 1 else 0) := by
      rcases h1 with h | rfl
      · have := List.count_pos_iff.2 h; omega
      · simp
    simp only [hcK] at hk; omega
  have hidq₀ : opsOf α q₀ = [] := hidle q₀ (by simp)
  have hidq₁ : opsOf α q₁ = [] := hidle q₁ (by simp)
  obtain ⟨V₀, hV₀, hrV₀, hV₀m, hV₀o⟩ := S.side hW₀ h₀
  obtain ⟨V₁, hV₁, hrV₁, hV₁m, hV₁o⟩ := S.swap.side hW₁ h₁
  have hq_b : ∀ q, opsOf α q = [] → ∀ (b : List (P × ι)), (∀ c ∈ b, c ∈ b₀ ++ b₁ ++ b₂) →
      q ∉ b.map Prod.fst := by
    intro q hq b hb h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
    exact S.not_idle (hb c hc) hq rfl
  have hpV₀ : V₀.pend q₀ = none := by
    rw [(hV₀o q₀ hq₀L₀ (hq_b q₀ hidq₀ b₀ (fun c hc => by simp [hc]))).2]
    exact pend_none_of_idle S.run hidq₀
  have hpV₁ : V₁.pend q₁ = none := by
    rw [(hV₁o q₁ hq₁L₁ (hq_b q₁ hidq₁ b₁ (fun c hc => by simp [hc]))).2]
    exact pend_none_of_idle S.run hidq₁
  -- admissibility of the segment executions
  have hadm₀ : Adm true (α ++ bw b₀ ++ flat (segMoves I R W₀ L₀) ++ [.inv q₀ .getTS]) := by
    rw [List.append_assoc, List.append_assoc]
    refine adm_append_of_count S.adm cK hKc hKmem (fun p => ?_)
    have h1 := getTSCount_segMoves_le (I := I) R W₀ L₀ p
    simp only [getTSCount_append, getTSCount_blockWrite, getTSCount_inv_getTS, hcK]
    omega
  have hadm₁ : Adm true (α ++ bw b₁ ++ flat (segMoves I R W₁ L₁) ++ [.inv q₁ .getTS]) := by
    rw [List.append_assoc, List.append_assoc]
    refine adm_append_of_count S.adm cK hKc hKmem (fun p => ?_)
    have h1 := getTSCount_segMoves_le (I := I) R W₁ L₁ p
    simp only [getTSCount_append, getTSCount_blockWrite, getTSCount_inv_getTS, hcK]
    omega
  obtain ⟨Z₀, hZ₀, hst₀, hops₀, hresp₀⟩ := seg_spec (I := I) (os := true) hI R q₀ hrV₀ hpV₀ hadm₀
  obtain ⟨Z₁, hZ₁, hst₁, hops₁, hresp₁⟩ := seg_spec (I := I) (os := true) hI R q₁ hrV₁ hpV₁ hadm₁
  have hnp₀ : ¬ Paused I R q₀ Z₀ := fun hp => hcon.1 (h₀.append_single hV₀ ⟨Z₀, hZ₀, hp⟩)
  have hnp₁ : ¬ Paused I R q₁ Z₁ := fun hp => hcon.2 (h₁.append_single hV₁ ⟨Z₁, hZ₁, hp⟩)
  have hfin₀ : Z₀.pend q₀ = none := by
    rcases hst₀ with h | h
    · exact h
    · by_contra hn; exact hnp₀ ⟨hn, h⟩
  have hfin₁ : Z₁.pend q₁ = none := by
    rcases hst₁ with h | h
    · exact h
    · by_contra hn; exact hnp₁ ⟨hn, h⟩
  have hnotq : ∀ (W : Config (tsObj T) B P L) (Ls : List P) (q : P), q ∉ Ls →
      ∀ ℓ ∈ flat (segMoves I R W Ls), ℓ.proc ≠ q := by
    intro W Ls q hq ℓ hℓ he
    have := flat_procs (segMoves_procs (I := I) R W Ls) ℓ hℓ
    rw [segMoves_map_fst, he] at this; exact hq this
  have hbidle : ∀ c ∈ b₀ ++ b₁ ++ b₂, ∀ p, (p ∈ L₀ ∨ p = q₀) ∨ (p ∈ L₁ ∨ p = q₁) → c.1 ≠ p := by
    intro c hc p hp
    apply S.not_idle hc
    apply hidle
    simp only [List.mem_append, List.mem_singleton]; tauto
  -- apply Lemma 2.1
  refine lemma_2_1 (os := true) hI S.run b₀ b₁ b₂ S.nd S.cov R S.R₀ S.R₁ S.R₂
    {p | p ∈ L₀ ∨ p = q₀} {p | p ∈ L₁ ∨ p = q₁}
    (Set.disjoint_left.2 fun p hp h => hdisj p hp h)
    (fun c hc => ⟨fun h => hbidle c hc c.1 (Or.inl h) rfl,
      fun h => hbidle c hc c.1 (Or.inr h) rfl⟩)
    (flat (segMoves I R W₀ L₀) ++ seg I R q₀ V₀) (flat (segMoves I R W₁ L₁) ++ seg I R q₁ V₁)
    ?_ ?_ hW₀ (by rw [runFrom_append_of_eq I hV₀]; exact hZ₀)
    hW₁ (by rw [runFrom_append_of_eq I hV₁]; exact hZ₁)
    (fun i hi => by rw [seg_mem hZ₀ i hi, hV₀m i hi])
    (fun i hi => by rw [seg_mem hZ₁ i hi, hV₁m i hi])
    q₀ q₁ (Or.inr rfl) (Or.inr rfl) (pend_none_of_idle S.run hidq₀)
    (pend_none_of_idle S.run hidq₁) ?_ ?_ ?_ ?_ hfin₀ ?_
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with h | h
    · have := flat_procs (segMoves_procs (I := I) R W₀ L₀) ℓ h
      rw [segMoves_map_fst] at this; exact Or.inl this
    · exact Or.inr (seg_procs R q₀ V₀ ℓ h)
  · intro ℓ hℓ
    rcases List.mem_append.1 hℓ with h | h
    · have := flat_procs (segMoves_procs (I := I) R W₁ L₁) ℓ h
      rw [segMoves_map_fst] at this; exact Or.inl this
    · exact Or.inr (seg_procs R q₁ V₁ ℓ h)
  · rw [opsOf_append, hops₀, opsOf_eq_nil_of_proc_ne (hnotq W₀ L₀ q₀ hq₀L₀)]; rfl
  · rw [respsOf_append, respsOf_eq_nil_of_proc_ne (hnotq W₀ L₀ q₀ hq₀L₀), List.nil_append]
    exact hresp₀ hfin₀
  · rw [opsOf_append, hops₁, opsOf_eq_nil_of_proc_ne (hnotq W₁ L₁ q₁ hq₁L₁)]; rfl
  · rw [respsOf_append, respsOf_eq_nil_of_proc_ne (hnotq W₁ L₁ q₁ hq₁L₁), List.nil_append]
    exact hresp₁ hfin₁
  · rw [List.append_assoc]
    refine adm_append_of_count S.adm cK hKc hKmem (fun p => ?_)
    have h1 := getTSCount_segMoves_le (I := I) R W₀ L₀ p
    have h2 := getTSCount_segMoves_le (I := I) R W₁ L₁ p
    have h3 := getTSCount_seg_le' (I := I) R q₀ p V₀
    have h4 := getTSCount_seg_le' (I := I) R q₁ p V₁
    simp only [getTSCount_append, hcK]
    omega

lemma CovSetup.disj01 (S : CovSetup I α C R b₀ b₁ b₂) : ∀ c ∈ b₁, c.1 ∉ b₀.map Prod.fst := by
  intro c hc h
  have := S.nd
  simp only [List.nodup_append, List.mem_append, List.mem_map] at this
  obtain ⟨c', hc', he⟩ := List.mem_map.1 h
  exact this.1.2.2 _ ⟨c', hc', rfl⟩ _ ⟨c, hc, rfl⟩ he

/-- The induction in the proof of Lemma 4.1: iterating `two_choice` over the remaining idle
processes. -/
lemma iter (hI : IsTS I true) (S : CovSetup I α C R b₀ b₁ b₂) {W₀ W₁ : Config (tsObj T) B P L}
    (hW₀ : I.runFrom C (bw b₀) = some W₀) (hW₁ : I.runFrom C (bw b₁) = some W₁) :
    ∀ (rest L₀ L₁ : List P) (q₀ q₁ : P), (L₀ ++ [q₀] ++ L₁ ++ [q₁] ++ rest).Nodup →
      (∀ p ∈ L₀ ++ [q₀] ++ L₁ ++ [q₁] ++ rest, opsOf α p = []) →
      AllPaused I R W₀ L₀ → AllPaused I R W₁ L₁ →
      ∃ L₀' L₁' x, AllPaused I R W₀ L₀' ∧ AllPaused I R W₁ L₁' ∧
        (L₀' ++ L₁' ++ [x]).Perm (L₀ ++ [q₀] ++ L₁ ++ [q₁] ++ rest) := by
  intro rest
  induction rest with
  | nil =>
    intro L₀ L₁ q₀ q₁ hnd hid h₀ h₁
    simp only [List.append_nil] at hnd hid
    rcases two_choice hI S hW₀ hW₁ L₀ L₁ q₀ q₁ hnd hid h₀ h₁ with h | h
    · exact ⟨L₀ ++ [q₀], L₁, q₁, h, h₁, by simp⟩
    · exact ⟨L₀, L₁ ++ [q₁], q₀, h₀, h,
        List.perm_iff_count.2 fun a => by
          simp only [List.count_append, List.count_cons, List.count_nil, List.cons_append,
            List.nil_append, List.append_assoc]; omega⟩
  | cons u rest ih =>
    intro L₀ L₁ q₀ q₁ hnd hid h₀ h₁
    have hnd' : (L₀ ++ [q₀] ++ L₁ ++ [q₁]).Nodup := hnd.sublist (List.sublist_append_left _ _)
    have hid' : ∀ p ∈ L₀ ++ [q₀] ++ L₁ ++ [q₁], opsOf α p = [] :=
      fun p hp => hid p (List.mem_append_left _ hp)
    rcases two_choice hI S hW₀ hW₁ L₀ L₁ q₀ q₁ hnd' hid' h₀ h₁ with h | h
    · have hperm : (L₀ ++ [q₀] ++ [u] ++ L₁ ++ [q₁] ++ rest).Perm
          (L₀ ++ [q₀] ++ L₁ ++ [q₁] ++ u :: rest) :=
        List.perm_iff_count.2 fun a => by
          simp only [List.count_append, List.count_cons, List.count_nil, List.cons_append,
            List.nil_append, List.append_assoc]; omega
      obtain ⟨A, A', x, hA, hA', hP⟩ := ih (L₀ ++ [q₀]) L₁ u q₁ (hperm.nodup_iff.2 hnd)
        (fun p hp => hid p (hperm.subset hp)) h h₁
      exact ⟨A, A', x, hA, hA', hP.trans hperm⟩
    · have hperm : (L₀ ++ [q₀] ++ (L₁ ++ [q₁]) ++ [u] ++ rest).Perm
          (L₀ ++ [q₀] ++ L₁ ++ [q₁] ++ u :: rest) :=
        List.perm_iff_count.2 fun a => by
          simp only [List.count_append, List.count_cons, List.count_nil, List.cons_append,
            List.nil_append, List.append_assoc]
      obtain ⟨A, A', x, hA, hA', hP⟩ := ih L₀ (L₁ ++ [q₁]) q₀ u (hperm.nodup_iff.2 hnd)
        (fun p hp => hid p (hperm.subset hp)) h₀ h
      exact ⟨A, A', x, hA, hA', hP.trans hperm⟩

/-- Assembling the schedule `πB₀ σ πB₁ σ'` from the two lists of paused segments: the segments
of `σ'`, computed after `πB₁` alone, can be replayed after `πB₀ σ πB₁` (indistinguishability
after the block write `πB₁`). Every process is poised to write outside `R` right after its own
segment. -/
lemma assemble (hB : RWLike B) (S : CovSetup I α C R b₀ b₁ b₂) {W₀ W₁ : Config (tsObj T) B P L}
    (hW₀ : I.runFrom C (bw b₀) = some W₀) (hW₁ : I.runFrom C (bw b₁) = some W₁)
    (L₀ L₁ : List P) (hnd : (L₀ ++ L₁).Nodup) (hid : ∀ p ∈ L₀ ++ L₁, opsOf α p = [])
    (h₀ : AllPaused I R W₀ L₀) (h₁ : AllPaused I R W₁ L₁) :
    (∃ X, I.runFrom C (bw b₀ ++ flat (segMoves I R W₀ L₀) ++ bw b₁ ++
        flat (segMoves I R W₁ L₁)) = some X) ∧
    (∀ M' m M'', segMoves I R W₀ L₀ = M' ++ m :: M'' →
      ∃ Y, I.runFrom C (bw b₀ ++ flat (M' ++ [m])) = some Y ∧ ∃ r ∉ R, I.Covers Y m.1 r) ∧
    (∀ M' m M'', segMoves I R W₁ L₁ = M' ++ m :: M'' →
      ∃ Y, I.runFrom C (bw b₀ ++ flat (segMoves I R W₀ L₀) ++ bw b₁ ++ flat (M' ++ [m])) = some Y ∧
        ∃ r ∉ R, I.Covers Y m.1 r) := by
  classical
  obtain ⟨V₀, hV₀, -, hV₀m, hV₀o⟩ := S.side hW₀ h₀
  obtain ⟨-, -, -, -, hs₀⟩ := h₀.run
  set Q : Set P := {q | q ∉ L₀ ∧ q ∉ b₀.map Prod.fst} with hQ
  have hb₁Q : ∀ c ∈ b₁, c.1 ∈ Q := by
    intro c hc
    refine ⟨fun h => S.not_idle (by simp [hc]) (hid c.1 (by simp [h])) rfl, S.disj01 c hc⟩
  have hb₁nd : (b₁.map Prod.fst).Nodup := S.nd.sublist (by simp)
  obtain ⟨Y, W₁', hY, hW₁', hagY⟩ := blockWrite_agreeOn (I := I) (Q := Q) (cs := b₁) hb₁nd
    (fun c hc => hb₁Q c hc) (C := V₀) (D := C)
    (fun c hc => covers_congr (hV₀o c.1 (hb₁Q c hc).1 (hb₁Q c hc).2).1.symm
      (hV₀o c.1 (hb₁Q c hc).1 (hb₁Q c hc).2).2.symm (S.cov c (by simp [hc])))
    (fun q hq => (hV₀o q hq.1 hq.2).1) (fun q hq => (hV₀o q hq.1 hq.2).2)
    (fun i hi => hV₀m i (fun h => hi ((S.R₁ i).1 h)))
  rw [hW₁] at hW₁'; cases hW₁'
  have hL₁Q : ∀ p ∈ L₁, p ∈ Q := by
    intro p hp
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have := List.nodup_append.1 hnd
      exact this.2.2 p h p hp rfl
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 h
      exact S.not_idle (by simp [hc]) (hid c.1 (by simp [hp])) rfl
  obtain ⟨hseq, hY₁⟩ := AllPaused.of_agreeOn hagY.symm hL₁Q h₁
  obtain ⟨X, hX, -, -, hs₁⟩ := hY₁.run
  refine ⟨⟨X, ?_⟩, ?_, ?_⟩
  · rw [List.append_assoc, List.append_assoc, runFrom_append_of_eq I hW₀,
      runFrom_append_of_eq I hV₀, runFrom_append_of_eq I hY, hseq, hX]
  · intro M' m M'' hM
    obtain ⟨Y', hY', hp⟩ := hs₀ M' m M'' hM
    exact ⟨Y', by rw [runFrom_append_of_eq I hW₀, hY'], hp.covers hB⟩
  · intro M' m M'' hM
    rw [hseq] at hM
    obtain ⟨Y', hY', hp⟩ := hs₁ M' m M'' hM
    refine ⟨Y', ?_, hp.covers hB⟩
    rw [List.append_assoc, List.append_assoc, runFrom_append_of_eq I hW₀,
      runFrom_append_of_eq I hV₀, runFrom_append_of_eq I hY, hY']

/-- **Lemma 4.1** (in the form used for Theorem 1.2). From a configuration `C` reached by a
one-shot execution `α`, with `b₀, b₁, b₂` disjoint block writes covering `R` and a list `U` of at
least two idle processes, there are an ordering `(c₀, c₁)` of the block writes `b₀, b₁` and two
lists of moves `M₀`, `M₁` (paused solo segments of distinct processes of `U`) such that
* the schedule `πc₀ M₀ πc₁ M₁` can be run from `C`;
* `|M₀| + |M₁| = |U| - 1` and `|M₀| ≥ ⌊|U|/2⌋`;
* every process of `M₀`/`M₁`, right after its own segment, covers an object outside `R`. -/
theorem lemma_4_1 (hI : IsTS I true) (hB : RWLike B) (S : CovSetup I α C R b₀ b₁ b₂)
    (U : List P) (hUnd : U.Nodup) (hU2 : 2 ≤ U.length) (hUid : ∀ u ∈ U, opsOf α u = []) :
    ∃ (c₀ c₁ : List (P × ι)) (M₀ M₁ : List (P × List (Label P (tsObj T)))),
      ((c₀ = b₀ ∧ c₁ = b₁) ∨ (c₀ = b₁ ∧ c₁ = b₀)) ∧
      ((M₀ ++ M₁).map Prod.fst).Nodup ∧ (∀ m ∈ M₀ ++ M₁, m.1 ∈ U) ∧
      M₀.length + M₁.length + 1 = U.length ∧ U.length / 2 ≤ M₀.length ∧
      (∀ m ∈ M₀ ++ M₁, ∀ ℓ ∈ m.2, ℓ.proc = m.1) ∧
      (∀ p, getTSCount (flat (M₀ ++ M₁)) p ≤ ((M₀ ++ M₁).map Prod.fst).count p) ∧
      (∃ X, I.runFrom C (bw c₀ ++ flat M₀ ++ bw c₁ ++ flat M₁) = some X) ∧
      (∀ M' m M'', M₀ = M' ++ m :: M'' →
        ∃ Y, I.runFrom C (bw c₀ ++ flat (M' ++ [m])) = some Y ∧ ∃ r ∉ R, I.Covers Y m.1 r) ∧
      (∀ M' m M'', M₁ = M' ++ m :: M'' →
        ∃ Y, I.runFrom C (bw c₀ ++ flat M₀ ++ bw c₁ ++ flat (M' ++ [m])) = some Y ∧
          ∃ r ∉ R, I.Covers Y m.1 r) := by
  obtain ⟨u₀, u₁, rest, rfl⟩ : ∃ u₀ u₁ rest, U = u₀ :: u₁ :: rest := by
    match U, hU2 with
    | u₀ :: u₁ :: rest, _ => exact ⟨u₀, u₁, rest, rfl⟩
  obtain ⟨W₀, hW₀, -, -⟩ := blockWrite_run (I := I) (cs := b₀) (S.nd.sublist (by simp))
    (fun c hc => S.cov c (by simp [hc]))
  obtain ⟨W₁, hW₁, -, -⟩ := blockWrite_run (I := I) (cs := b₁) (S.nd.sublist (by simp))
    (fun c hc => S.cov c (by simp [hc]))
  have hperm0 : ([] ++ [u₀] ++ [] ++ [u₁] ++ rest) = u₀ :: u₁ :: rest := by simp
  obtain ⟨L₀, L₁, x, h₀, h₁, hP⟩ := iter hI S hW₀ hW₁ rest [] [] u₀ u₁ (by rw [hperm0]; exact hUnd)
    (by rw [hperm0]; exact hUid) trivial trivial
  rw [hperm0] at hP
  have hnd : (L₀ ++ L₁).Nodup := (hP.nodup_iff.2 hUnd).sublist (List.sublist_append_left _ _)
  have hmem : ∀ p ∈ L₀ ++ L₁, p ∈ u₀ :: u₁ :: rest :=
    fun p hp => hP.subset (List.mem_append_left _ hp)
  have hid : ∀ p ∈ L₀ ++ L₁, opsOf α p = [] := fun p hp => hUid p (hmem p hp)
  have hlen : L₀.length + L₁.length + 1 = (u₀ :: u₁ :: rest).length := by
    have := hP.length_eq; simp only [List.length_append, List.length_cons, List.length_nil] at this ⊢; omega
  have hl0 := congrArg List.length (segMoves_map_fst (I := I) R W₀ L₀)
  have hl1 := congrArg List.length (segMoves_map_fst (I := I) R W₁ L₁)
  simp only [List.length_map] at hl0 hl1
  have hcnt : ∀ (Z Z' : Config (tsObj T) B P L) (A A' : List P) p,
      getTSCount (flat (segMoves I R Z A ++ segMoves I R Z' A')) p ≤
        ((segMoves I R Z A ++ segMoves I R Z' A').map Prod.fst).count p := by
    intro Z Z' A A' p
    simp only [List.flatMap_append, getTSCount_append, List.map_append, segMoves_map_fst,
      List.count_append]
    have h1 : getTSCount (List.flatMap Prod.snd (segMoves I R Z A)) p ≤ A.count p :=
      getTSCount_segMoves_le (I := I) R Z A p
    have h2 : getTSCount (List.flatMap Prod.snd (segMoves I R Z' A')) p ≤ A'.count p :=
      getTSCount_segMoves_le (I := I) R Z' A' p
    omega
  have hprocs : ∀ (Z Z' : Config (tsObj T) B P L) (A A' : List P),
      ∀ m ∈ segMoves I R Z A ++ segMoves I R Z' A', ∀ ℓ ∈ m.2, ℓ.proc = m.1 := by
    intro Z Z' A A' m hm
    rcases List.mem_append.1 hm with h | h
    · exact segMoves_procs R Z A m h
    · exact segMoves_procs R Z' A' m h
  by_cases hle : L₁.length ≤ L₀.length
  · obtain ⟨hX, hc₀, hc₁⟩ := assemble hB S hW₀ hW₁ L₀ L₁ hnd hid h₀ h₁
    refine ⟨b₀, b₁, segMoves I R W₀ L₀, segMoves I R W₁ L₁, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_,
      hprocs _ _ _ _, hcnt _ _ _ _, ?_, hc₀, hc₁⟩
    · simpa [segMoves_map_fst] using hnd
    · intro m hm
      have : m.1 ∈ (segMoves I R W₀ L₀ ++ segMoves I R W₁ L₁).map Prod.fst :=
        List.mem_map_of_mem hm
      simp only [List.map_append, segMoves_map_fst] at this
      exact hmem _ this
    · omega
    · simp only [List.length_cons] at hlen ⊢; omega
    · obtain ⟨X, hX⟩ := hX; exact ⟨X, by simpa [List.append_assoc] using hX⟩
  · have hnd' : (L₁ ++ L₀).Nodup := (List.perm_append_comm.nodup_iff).1 hnd
    have hid' : ∀ p ∈ L₁ ++ L₀, opsOf α p = [] :=
      fun p hp => hid p (List.perm_append_comm.subset hp)
    obtain ⟨hX, hc₀, hc₁⟩ := assemble hB S.swap hW₁ hW₀ L₁ L₀ hnd' hid' h₁ h₀
    refine ⟨b₁, b₀, segMoves I R W₁ L₁, segMoves I R W₀ L₀, Or.inr ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_,
      hprocs _ _ _ _, hcnt _ _ _ _, ?_, hc₀, hc₁⟩
    · simpa [segMoves_map_fst] using hnd'
    · intro m hm
      have : m.1 ∈ (segMoves I R W₁ L₁ ++ segMoves I R W₀ L₀).map Prod.fst :=
        List.mem_map_of_mem hm
      simp only [List.map_append, segMoves_map_fst] at this
      exact hmem _ (List.perm_append_comm.subset this)
    · omega
    · simp only [List.length_cons] at hlen ⊢; omega
    · obtain ⟨X, hX⟩ := hX; exact ⟨X, by simpa [List.append_assoc] using hX⟩

end Cslib.SharedMemory.Timestamp
