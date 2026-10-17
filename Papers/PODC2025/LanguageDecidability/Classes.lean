import Papers.PODC2025.LanguageDecidability.Characterization
import Papers.PODC2025.LanguageDecidability.Extend

/-!
# Section 4.2: stability lemmas and Theorem 4.1 (`SD ⊆ WAD = WOD = WD`)

* `lemma_4_1` (Figure 2, a shared flag): an algorithm that strongly decides `L` can be made to
  report `NO` forever, at every process, once some process reported `NO`.
* `lemma_4_2` (Figure 3, shared counters `C`, compared with the previous snapshot): a weak-all
  decider becomes a weak decider.
* `lemma_4_3` — Lemma 4.3 with a **corrected** construction (`wodAlg`): a process reports `NO`
  only when *every* counter has grown since the last time it reported `NO`. The construction of
  Figure 4 (every counter compared with the previous snapshot) is wrong; see
  `Fig4Counterexample.lean`.
* `thm_4_1` — Theorem 4.1: `SD ⊆ WAD`, `WAD = WOD`, `WAD = WD`.
-/

namespace Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type}

/-! ### Finite and infinite sets of times -/

lemma infinite_iff_frequently {S : Set ℕ} : S.Infinite ↔ ∀ N, ∃ t, N ≤ t ∧ t ∈ S := by
  constructor
  · intro h N
    by_contra hc
    push_neg at hc
    exact h ((Set.finite_Iio N).subset fun t ht => by
      by_contra h'; exact hc t (by simpa using h') ht)
  · intro h
    exact Set.infinite_of_forall_exists_gt fun a => by
      obtain ⟨t, ht, hS⟩ := h (a + 1); exact ⟨t, hS, by omega⟩

lemma finite_iff_eventually {S : Set ℕ} : S.Finite ↔ ∃ N, ∀ t, N ≤ t → t ∉ S := by
  rw [← not_iff_not, Set.not_finite, infinite_iff_frequently]; push_neg; rfl

/-! ### Lemma 4.1 (Figure 2) -/

/-- Line 06 of Figure 2: report `NO` if the flag is set; otherwise set the flag if `V` reports
`NO`, and report what `V` reports. -/
def fFlag (_ : Fin n) (_ : Unit) (flag : Bool) (d : Verdict) : Unit × Bool × Verdict :=
  if flag then ((), true, .no) else if d = .no then ((), true, .no) else ((), false, d)

/-- The algorithm `W` of Figure 2. -/
def flagAlg (V : Alg n I O Verdict) : Alg n I O Verdict := V.extend (fun _ => ()) false fFlag

section flag

variable (o : ℕ → Option (Fin n × Verdict))

local notation "FR" => tRun fFlag (fun _ => ()) false o
local notation "FO" => tOut fFlag (fun _ => ()) false o

lemma flag_false (h : ∀ t p, o t ≠ some (p, .no)) : ∀ t, (FR t).2 = false
  | 0 => rfl
  | t + 1 => by
    have ih := flag_false h t
    simp only [tRun]
    rcases ho : o t with _ | ⟨p, d⟩
    · simpa [tStep] using ih
    · have : d ≠ .no := fun hd => h t p (by rw [ho, hd])
      simp [tStep, fFlag, ih, this]

lemma tOut_flag_of_no_no (h : ∀ t p, o t ≠ some (p, .no)) : FO = o := by
  funext t
  rcases ho : o t with _ | ⟨p, d⟩
  · simp [tOut, ho]
  · have : d ≠ .no := fun hd => h t p (by rw [ho, hd])
    simp [tOut, ho, fFlag, flag_false o h t, this]

lemma flag_true {t₀ : ℕ} {p : Fin n} (h : o t₀ = some (p, .no)) :
    ∀ t, t₀ < t → (FR t).2 = true := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base =>
    simp only [tRun, h, tStep, fFlag]
    split_ifs <;> rfl
  | succ t ht ih =>
    simp only [tRun]
    rcases ho : o t with _ | ⟨q, d⟩
    · simpa [tStep] using ih
    · simp [tStep, fFlag, ih]

lemma tOut_flag_no {t₀ : ℕ} {p : Fin n} (h : o t₀ = some (p, .no)) :
    ∀ t, t₀ ≤ t → ∀ q d, FO t = some (q, d) → d = .no := by
  intro t ht q d hq
  rcases ht.eq_or_lt with rfl | ht
  · simp only [tOut, h, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨-, rfl⟩ := hq
    simp only [fFlag]; split_ifs <;> rfl
  · rcases ho : o t with _ | ⟨q', d'⟩
    · simp [tOut, ho] at hq
    · simp only [tOut, ho, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨-, rfl⟩ := hq
      simp [fFlag, flag_true o h t ht]

lemma noSet_flag_infinite (hf : FairTrace o) {t₀ : ℕ} {p : Fin n} (h : o t₀ = some (p, .no))
    (q : Fin n) : (NoSet FO q).Infinite := by
  rw [infinite_iff_frequently]
  intro N
  obtain ⟨t, ht, d, hd⟩ := hf q (N + t₀)
  refine ⟨t, by omega, ?_⟩
  have hsome : FO t = some (q, (fFlag q ((FR t).1 q) (FR t).2 d).2.2) := by simp [tOut, hd]
  have := tOut_flag_no o h t (by omega) q _ hsome
  simp only [NoSet, Set.mem_setOf_eq, hsome, this]

end flag

/-- **Lemma 4.1**: if `V` strongly decides `L`, then so does `W = flagAlg V`, and in every
execution with `x(E) ∉ L`, eventually every process always reports `NO`. -/
theorem lemma_4_1 {V : Alg n I O Verdict} {L : Set (Word I O)} (hV : StronglyDecides V L) :
    StronglyDecides (flagAlg V) L ∧
      ∀ s x, IsExec s → HasInput s x → x ∉ L →
        ∃ T, ∀ t, T ≤ t → ∀ p d, (flagAlg V).outs s t = some (p, d) → d = .no := by
  have key : ∀ s x, IsExec s → HasInput s x → x ∉ L →
      ∃ t₀ p, V.outs s t₀ = some (p, .no) := by
    intro s x hs hx hxL
    have : ¬ PSD (V.outs s) := fun h => hxL ((hV s x hs hx).2 h)
    simp only [PSD, not_forall] at this
    obtain ⟨p, hp⟩ := this
    obtain ⟨t₀, ht₀⟩ := Set.nonempty_iff_ne_empty.2 hp
    exact ⟨t₀, p, ht₀⟩
  refine ⟨fun s x hs hx => ?_, fun s x hs hx hxL => ?_⟩
  · unfold flagAlg; rw [outs_extend]
    constructor
    · intro hxL
      have h := (hV s x hs hx).1 hxL
      have hno : ∀ t p, V.outs s t ≠ some (p, .no) := fun t p ht => by
        have := h p; rw [Set.eq_empty_iff_forall_notMem] at this; exact this t ht
      rwa [tOut_flag_of_no_no _ hno]
    · intro hP
      by_contra hxL
      obtain ⟨t₀, p, ht₀⟩ := key s x hs hx hxL
      have := hP p
      exact (noSet_flag_infinite _ (IsExec.fairTrace V hs) ht₀ p).nonempty.ne_empty this
  · obtain ⟨t₀, p, ht₀⟩ := key s x hs hx hxL
    refine ⟨t₀, fun t ht q d hq => ?_⟩
    unfold flagAlg at hq; rw [outs_extend] at hq
    exact tOut_flag_no _ ht₀ t ht q d hq

/-! ### Shared counters of `NO` reports (Figures 3 and 4) -/

/-- `C[p] ← C[p] + 1` if `V` reports `NO` at `p`. -/
def cUpd (p : Fin n) (C : Fin n → ℕ) (d : Verdict) : Fin n → ℕ :=
  if d = .no then Function.update C p (C p + 1) else C

/-- The counters along a report trace. -/
def cRun (o : ℕ → Option (Fin n × Verdict)) : ℕ → Fin n → ℕ
  | 0 => fun _ => 0
  | t + 1 => match o t with
    | none => cRun o t
    | some (p, d) => cUpd p (cRun o t) d

section counters

variable (o : ℕ → Option (Fin n × Verdict))

lemma cRun_succ_le (t : ℕ) (j : Fin n) : cRun o t j ≤ cRun o (t + 1) j := by
  simp only [cRun]
  rcases o t with _ | ⟨p, d⟩
  · exact le_rfl
  · simp only [cUpd]
    split_ifs
    · by_cases hj : j = p
      · subst hj; simp
      · simp [Function.update_of_ne hj]
    · exact le_rfl

lemma cRun_mono {t t' : ℕ} (h : t ≤ t') (j : Fin n) : cRun o t j ≤ cRun o t' j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (cRun_succ_le o _ j)

lemma cRun_succ_of_ne {t : ℕ} {j : Fin n} (h : o t ≠ some (j, .no)) :
    cRun o (t + 1) j = cRun o t j := by
  simp only [cRun]
  rcases ho : o t with _ | ⟨p, d⟩
  · rfl
  · simp only [cUpd]
    split_ifs with hd
    · subst hd
      have : j ≠ p := fun hj => h (by rw [ho, hj])
      simp [Function.update_of_ne this]
    · rfl

lemma cRun_succ_of_eq {t : ℕ} {j : Fin n} (h : o t = some (j, .no)) :
    cRun o (t + 1) j = cRun o t j + 1 := by
  simp [cRun, h, cUpd]

lemma cRun_eventually_const {j : Fin n} (h : (NoSet o j).Finite) :
    ∃ T, ∀ t, T ≤ t → cRun o t j = cRun o T j := by
  obtain ⟨T, hT⟩ := finite_iff_eventually.1 h
  refine ⟨T, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [cRun_succ_of_ne o (hT t ht), ih]

lemma cRun_unbounded {j : Fin n} (h : (NoSet o j).Infinite) (B : ℕ) : ∃ t, B ≤ cRun o t j := by
  induction B with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ B ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨t', ht', hno⟩ := infinite_iff_frequently.1 h t
    refine ⟨t' + 1, ?_⟩
    rw [cRun_succ_of_eq o hno]
    have := cRun_mono o ht' j
    omega

lemma cRun_eventually_gt (h : ∀ j, (NoSet o j).Infinite) (ℓ : Fin n → ℕ) :
    ∃ T, ∀ t, T ≤ t → ∀ j, ℓ j < cRun o t j := by
  choose T hT using fun j => cRun_unbounded o (h j) (ℓ j + 1)
  refine ⟨Finset.univ.sup T, fun t ht j => ?_⟩
  have h1 : T j ≤ t := le_trans (Finset.le_sup (Finset.mem_univ j)) ht
  have := cRun_mono o h1 j
  have := hT j
  omega

end counters

/-! ### Lemma 4.2 (Figure 3) -/

/-- Line 06 of Figure 3: update `C`, snapshot it, report `NO` iff some entry grew since the
previous snapshot. -/
noncomputable def fWAD (p : Fin n) (prev : Fin n → ℕ) (C : Fin n → ℕ) (d : Verdict) :
    (Fin n → ℕ) × (Fin n → ℕ) × Verdict :=
  haveI := Classical.dec
  (cUpd p C d, cUpd p C d, if ∃ j, prev j < cUpd p C d j then .no else .yes)

/-- The algorithm `W` of Figure 3. -/
noncomputable def wadAlg (V : Alg n I O Verdict) : Alg n I O Verdict :=
  V.extend (fun _ _ => 0) (fun _ => 0) fWAD

/-- The algorithm of the corrected Lemma 4.3: report `NO` iff every counter grew since the last
time this process reported `NO`. -/
noncomputable def fWOD (p : Fin n) (last : Fin n → ℕ) (C : Fin n → ℕ) (d : Verdict) :
    (Fin n → ℕ) × (Fin n → ℕ) × Verdict :=
  haveI := Classical.dec
  if ∀ j, last j < cUpd p C d j then (cUpd p C d, cUpd p C d, .no) else (last, cUpd p C d, .yes)

/-- The corrected algorithm `W` of Lemma 4.3. -/
noncomputable def wodAlg (V : Alg n I O Verdict) : Alg n I O Verdict :=
  V.extend (fun _ _ => 0) (fun _ => 0) fWOD

section counterAlgs

variable (o : ℕ → Option (Fin n × Verdict))

lemma tRun_fWAD_C : ∀ t, (tRun fWAD (fun _ _ => 0) (fun _ => 0) o t).2 = cRun o t
  | 0 => rfl
  | t + 1 => by
    simp only [tRun, cRun]
    rcases o t with _ | ⟨p, d⟩
    · exact tRun_fWAD_C t
    · simp [tStep, fWAD, tRun_fWAD_C t]

lemma tRun_fWOD_C : ∀ t, (tRun fWOD (fun _ _ => 0) (fun _ => 0) o t).2 = cRun o t
  | 0 => rfl
  | t + 1 => by
    simp only [tRun, cRun]
    rcases o t with _ | ⟨p, d⟩
    · exact tRun_fWOD_C t
    · simp only [tStep, fWOD, tRun_fWOD_C t]; split_ifs <;> rfl

lemma cRun_succ_some {t : ℕ} {p : Fin n} {d : Verdict} (h : o t = some (p, d)) :
    cRun o (t + 1) = cUpd p (cRun o t) d := by simp [cRun, h]

local notation "WR" => tRun fWAD (fun _ _ => 0) (fun _ => 0) o
local notation "WO" => tOut fWAD (fun _ _ => 0) (fun _ => 0) o

/-- The local state of `q` changes only at `q`'s reports. -/
lemma tRun_fWAD_loc {t : ℕ} {q : Fin n} (h : ∀ d, o t ≠ some (q, d)) :
    (WR (t + 1)).1 q = (WR t).1 q := by
  simp only [tRun]
  rcases ho : o t with _ | ⟨p, d⟩
  · rfl
  · have : q ≠ p := fun hq => h d (by rw [ho, hq])
    simp [tStep, Function.update_of_ne this]

lemma tRun_fWAD_loc_self {t : ℕ} {q : Fin n} {d : Verdict} (h : o t = some (q, d)) :
    (WR (t + 1)).1 q = cRun o (t + 1) := by
  simp [tRun, h, tStep, fWAD, tRun_fWAD_C, cRun_succ_some o h]

lemma tOut_fWAD {t : ℕ} {q : Fin n} {d : Verdict} (h : o t = some (q, d)) :
    WO t = some (q, haveI := Classical.dec
      if ∃ j, (WR t).1 q j < cRun o (t + 1) j then .no else .yes) := by
  simp [tOut, h, fWAD, tRun_fWAD_C, cRun_succ_some o h]

/-- If every process reports `NO` finitely often in `V`, so does every process in `W`. -/
lemma fWAD_finite (hf : FairTrace o) (h : ∀ p, (NoSet o p).Finite) (q : Fin n) :
    (NoSet WO q).Finite := by
  choose T hT using fun j => cRun_eventually_const o (h j)
  set T₀ := Finset.univ.sup T
  have hconst : ∀ t, T₀ ≤ t → cRun o t = cRun o T₀ := by
    intro t ht; funext j
    have h1 : T j ≤ T₀ := Finset.le_sup (Finset.mem_univ j)
    rw [hT j t (h1.trans ht), hT j T₀ h1]
  obtain ⟨t₁, ht₁, d₁, hd₁⟩ := hf q T₀
  -- after `t₁`, `q`'s previous snapshot is the final value of the counters
  have hprev : ∀ t, t₁ + 1 ≤ t → (WR t).1 q = cRun o T₀ := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rw [tRun_fWAD_loc_self o hd₁, hconst _ (by omega)]
    | succ t ht ih =>
      by_cases hq : ∃ d, o t = some (q, d)
      · obtain ⟨d, hd⟩ := hq; rw [tRun_fWAD_loc_self o hd, hconst _ (by omega)]
      · push_neg at hq; rw [tRun_fWAD_loc o hq, ih]
  rw [finite_iff_eventually]
  refine ⟨t₁ + 1, fun t ht hno => ?_⟩
  simp only [NoSet, Set.mem_setOf_eq] at hno
  rcases ho : o t with _ | ⟨p, d⟩
  · simp [tOut, ho] at hno
  · have hp : p = q := by simp [tOut, ho] at hno; exact hno.1
    subst hp
    rw [tOut_fWAD o ho, hprev t ht, hconst (t + 1) (by omega)] at hno
    simp at hno

/-- If some process reports `NO` infinitely often in `V`, every process reports `NO` infinitely
often in `W`. -/
lemma fWAD_infinite (hf : FairTrace o) {p : Fin n} (h : (NoSet o p).Infinite) (q : Fin n) :
    (NoSet WO q).Infinite := by
  intro hfin
  obtain ⟨T, hT⟩ := finite_iff_eventually.1 hfin
  set c := (WR T).1 q p
  -- after `T`, `q` always reports `YES`, so its snapshot of `C[p]` never grows
  have hyes : ∀ t, T ≤ t → ∀ d, o t = some (q, d) → cRun o (t + 1) p ≤ (WR t).1 q p := by
    intro t ht d hd
    have h1 := hT t ht
    simp only [NoSet, Set.mem_setOf_eq, tOut_fWAD o hd] at h1
    by_contra hlt
    push_neg at hlt
    exact h1 (by rw [if_pos ⟨p, hlt⟩])
  have hbound : ∀ t, T ≤ t → (WR t).1 q p ≤ c := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact le_rfl
    | succ t ht ih =>
      by_cases hq : ∃ d, o t = some (q, d)
      · obtain ⟨d, hd⟩ := hq
        rw [tRun_fWAD_loc_self o hd]; exact (hyes t ht d hd).trans ih
      · push_neg at hq; rw [tRun_fWAD_loc o hq]; exact ih
  obtain ⟨t₂, ht₂⟩ := cRun_unbounded o h (c + 1)
  obtain ⟨t₃, ht₃, d, hd⟩ := hf q (T + t₂)
  have h1 := hyes t₃ (by omega) d hd
  have h2 := hbound t₃ (by omega)
  have h3 := cRun_mono o (show t₂ ≤ t₃ + 1 by omega) p
  omega

end counterAlgs

/-- **Lemma 4.2**: if `V` weakly-all decides `L`, then `W = wadAlg V` weakly decides `L` (in
particular, if `x(E) ∉ L`, every process reports `NO` infinitely often). -/
theorem lemma_4_2 {V : Alg n I O Verdict} {L : Set (Word I O)} (hV : WeakAllDecides V L) :
    WeaklyDecides (wadAlg V) L := by
  intro s x hs hx
  unfold wadAlg; rw [outs_extend]
  have hf := IsExec.fairTrace V hs
  refine ⟨fun hxL q => fWAD_finite _ hf ((hV s x hs hx).1 hxL) q, fun hxL q => ?_⟩
  have : ¬ PWAD (V.outs s) := fun h => hxL ((hV s x hs hx).2 h)
  simp only [PWAD, not_forall] at this
  obtain ⟨p, hp⟩ := this
  exact fWAD_infinite _ hf hp q

section wod

variable (o : ℕ → Option (Fin n × Verdict))

local notation "UR" => tRun fWOD (fun _ _ => 0) (fun _ => 0) o
local notation "UO" => tOut fWOD (fun _ _ => 0) (fun _ => 0) o

lemma tOut_fWOD {t : ℕ} {q : Fin n} {d : Verdict} (h : o t = some (q, d)) :
    UO t = some (q, haveI := Classical.dec
      if ∀ j, (UR t).1 q j < cRun o (t + 1) j then .no else .yes) := by
  simp only [tOut, h, Option.map_some, fWOD, tRun_fWOD_C, cRun_succ_some o h]
  split_ifs <;> rfl

/-- The local state of `q` changes only when `q` reports `NO`, to the current counters. -/
lemma tRun_fWOD_loc {t : ℕ} {q : Fin n} :
    (UR (t + 1)).1 q = if UO t = some (q, .no) then cRun o (t + 1) else (UR t).1 q := by
  simp only [tRun]
  rcases ho : o t with _ | ⟨p, d⟩
  · simp [tStep, tOut, ho]
  · by_cases hq : q = p
    · subst hq
      rw [tOut_fWOD o ho]
      simp only [tStep, Function.update_self, fWOD, tRun_fWOD_C, cRun_succ_some o ho]
      split_ifs <;> simp_all
    · simp [tStep, Function.update_of_ne hq, tOut, ho, Ne.symm hq]

lemma fWOD_finite {p : Fin n} (h : (NoSet o p).Finite) (q : Fin n) : (NoSet UO q).Finite := by
  obtain ⟨T, hT⟩ := cRun_eventually_const o h
  -- after a `NO` of `q` at `t₁ ≥ T`, `q`'s last snapshot of `C[p]` is final
  have hlast : ∀ t₁, T ≤ t₁ → UO t₁ = some (q, .no) → ∀ t, t₁ + 1 ≤ t →
      (UR t).1 q p = cRun o T p := by
    intro t₁ ht₁ hno t ht
    induction t, ht using Nat.le_induction with
    | base => rw [tRun_fWOD_loc, if_pos hno, hT _ (by omega)]
    | succ t ht ih =>
      rw [tRun_fWOD_loc]; split_ifs
      · rw [hT _ (by omega)]
      · exact ih
  have hone : ∀ t₁ t₂, T ≤ t₁ → t₁ < t₂ → UO t₁ = some (q, .no) → UO t₂ ≠ some (q, .no) := by
    intro t₁ t₂ ht₁ ht₂ h₁ h₂
    rcases ho : o t₂ with _ | ⟨p', d⟩
    · simp [tOut, ho] at h₂
    · have hp' : p' = q := by simp [tOut, ho] at h₂; exact h₂.1
      subst hp'
      rw [tOut_fWOD o ho] at h₂
      simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h₂
      split_ifs at h₂ with hall
      have := hall p
      rw [hlast t₁ ht₁ h₁ t₂ (by omega), hT (t₂ + 1) (by omega)] at this
      exact lt_irrefl _ this
  by_cases hex : ∃ t₁, T ≤ t₁ ∧ UO t₁ = some (q, .no)
  · obtain ⟨t₁, ht₁, h₁⟩ := hex
    exact finite_iff_eventually.2 ⟨t₁ + 1, fun t ht h => hone t₁ t ht₁ (by omega) h₁ h⟩
  · push_neg at hex
    exact finite_iff_eventually.2 ⟨T, fun t ht h => hex t ht h⟩

lemma fWOD_infinite (hf : FairTrace o) (h : ∀ p, (NoSet o p).Infinite) (q : Fin n) :
    (NoSet UO q).Infinite := by
  intro hfin
  obtain ⟨T, hT⟩ := finite_iff_eventually.1 hfin
  have hconst : ∀ t, T ≤ t → (UR t).1 q = (UR T).1 q := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih =>
      have : ¬ UO t = some (q, .no) := hT t ht
      rw [tRun_fWOD_loc, if_neg this, ih]
  obtain ⟨T', hT'⟩ := cRun_eventually_gt o h ((UR T).1 q)
  obtain ⟨t, ht, d, hd⟩ := hf q (T + T')
  apply hT t (by omega)
  simp only [NoSet, Set.mem_setOf_eq]
  rw [tOut_fWOD o hd, if_pos]
  intro j
  rw [hconst t (by omega)]
  exact (hT' t (by omega) j).trans_le (cRun_mono o (Nat.le_succ t) j)

end wod

/-- **Lemma 4.3** (with the corrected construction `wodAlg`): if `V` weakly-one decides `L`, then
`W = wodAlg V` weakly decides `L`; in particular, if `x(E) ∈ L`, every process reports `NO`
finitely often (so eventually always `YES`). -/
theorem lemma_4_3 {V : Alg n I O Verdict} {L : Set (Word I O)} (hV : WeakOneDecides V L) :
    WeaklyDecides (wodAlg V) L := by
  intro s x hs hx
  unfold wodAlg; rw [outs_extend]
  have hf := IsExec.fairTrace V hs
  refine ⟨fun hxL q => ?_, fun hxL q => ?_⟩
  · obtain ⟨p, hp⟩ := (hV s x hs hx).1 hxL
    exact fWOD_finite _ hp q
  · have : ¬ PWOD (V.outs s) := fun h => hxL ((hV s x hs hx).2 h)
    simp only [PWOD, not_exists, Set.not_finite] at this
    exact fWOD_infinite _ hf this q

/-- A weak decider also weakly-one decides. -/
theorem WeaklyDecides.weakOneDecides {V : Alg n I O Verdict} {L : Set (Word I O)}
    (h : WeaklyDecides V L) : WeakOneDecides V L := by
  intro s x hs hx
  refine ⟨fun hxL => ⟨(x 0).1, (h s x hs hx).1 hxL _⟩, fun ⟨p, hp⟩ => by_contra fun hxL => ?_⟩
  exact (h s x hs hx).2 hxL p hp

/-- **Theorem 4.1**: `SD ⊆ WAD = WOD`; moreover both equal `WD`. -/
theorem thm_4_1 (L : Set (Word I O)) :
    (SD L → WAD L) ∧ (WAD L ↔ WOD L) ∧ (WAD L ↔ WD L) := by
  have hWAD_WD : WAD L → WD L := fun ⟨V, hV⟩ => ⟨_, lemma_4_2 hV⟩
  have hWD_WAD : WD L → WAD L := fun ⟨V, hV⟩ => ⟨V, hV.weakAllDecides⟩
  have hWOD_WD : WOD L → WD L := fun ⟨V, hV⟩ => ⟨_, lemma_4_3 hV⟩
  have hWD_WOD : WD L → WOD L := fun ⟨V, hV⟩ => ⟨V, hV.weakOneDecides⟩
  refine ⟨fun ⟨V, hV⟩ => ⟨flagAlg V, fun s x hs hx => ?_⟩,
    ⟨fun h => hWD_WOD (hWAD_WD h), fun h => hWD_WAD (hWOD_WD h)⟩, ⟨hWAD_WD, hWD_WAD⟩⟩
  obtain ⟨hW, hstab⟩ := lemma_4_1 hV
  constructor
  · intro hxL p
    have := (hW s x hs hx).1 hxL p
    simp [this]
  · intro hfin
    by_contra hxL
    obtain ⟨T, hT⟩ := hstab s x hs hx hxL
    have hf := IsExec.fairTrace (flagAlg V) hs
    obtain ⟨p⟩ : Nonempty (Fin n) := ⟨(x 0).1⟩
    have hinf : (NoSet ((flagAlg V).outs s) p).Infinite := by
      rw [infinite_iff_frequently]
      intro N
      obtain ⟨t, ht, d, hd⟩ := hf p (N + T)
      exact ⟨t, by omega, by simp only [NoSet, Set.mem_setOf_eq, hd, hT t (by omega) p d hd]⟩
    exact hinf (hfin p)

end Podc2025.LanguageDecidability
