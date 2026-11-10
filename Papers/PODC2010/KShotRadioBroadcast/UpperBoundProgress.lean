import Papers.PODC2010.KShotRadioBroadcast.Model

/-!
# The progress argument behind Theorem 4.3 (schedule-independent part)

The paper measures *progress* as the number of informed nodes plus the number of *complete*
nodes (informed nodes all of whose out-neighbours are informed); progress is at most `2n` and,
when all nodes are reachable from the source, broadcasting is complete as soon as no node is
*active* (informed but not complete).

This file proves, for an arbitrary oblivious schedule `σ` cut into *stages* of `S` steps
(stage `g` = steps `g S + 1, …, (g + 1) S`), the repaired form of Lemma 4.2:

if `f` nodes are active at the start of stage `g`, then during the next `2f` stages the
progress grows by at least `f` (`progress_add_le`),

under three abstract properties of the schedule, which `UpperBoundSchedule.lean` establishes for
algorithm *Oblivious k-Shot* (with `p` the prime of the construction):

* `hlone` (Lemma 4.1 with a time bound): a node informed at step `r` transmits alone (transmission
  set `{v}`) at one of its `k` transmission steps, at the latest at the end of stage
  `r / S + p`;
* `happ`: every node appears in the schedule in every stage;
* `hline`: two distinct nodes appear together in at most one step of any window of `p + 1`
  consecutive stages.

The amortization (`complete_of_progress`) then gives completion within `2(2n - 1)` stages.
-/

namespace Podc.KShotRadioBroadcast

open Finset

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {σ : Schedule V} {k : ℕ} {E : V → V → Prop} {s : V}

section recv

/-- The reception step of a node is a fixed point: at its reception step the node is already
informed. -/
theorem recvTime_self {t : ℕ} {v : V} {r : ℕ} (h : recvTime σ k E s t v = some r) :
    recvTime σ k E s r v = some r := by
  induction t generalizing r with
  | zero =>
    have := recvTime_le h
    have hr : r = 0 := by omega
    subst hr; exact h
  | succ t ih =>
    cases h' : recvTime σ k E s t v with
    | some r' =>
      rw [recvTime_succ_of_some h'] at h
      cases h; exact ih h'
    | none =>
      have h2 := h
      rw [recvTime_succ_of_none h'] at h2
      split_ifs at h2 with hc
      cases h2; exact h

/-- A node informed at step `r` is informed (at step `r`) at every step `t' ≥ r`. -/
theorem recvTime_of_le {t t' : ℕ} {v : V} {r : ℕ} (h : recvTime σ k E s t v = some r)
    (hr : r ≤ t') : recvTime σ k E s t' v = some r :=
  recvTime_mono hr (recvTime_self h)

end recv

/-! ## Informed, complete and active nodes; progress -/

/-- Node `v` is informed after step `t`. -/
def Informed (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) (v : V) : Prop :=
  (recvTime σ k E s t v).isSome

/-- Node `v` is *complete* after step `t`: it and all its out-neighbours are informed. -/
def Done (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) (v : V) : Prop :=
  Informed σ k E s t v ∧ ∀ w, E v w → Informed σ k E s t w

open Classical in
/-- The informed nodes after step `t`. -/
noncomputable def informedSet (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) :
    Finset V :=
  univ.filter (Informed σ k E s t)

open Classical in
/-- The complete nodes after step `t`. -/
noncomputable def doneSet (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) :
    Finset V :=
  univ.filter (Done σ k E s t)

/-- The active nodes (informed, not complete) after step `t`. -/
noncomputable def activeSet (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) :
    Finset V :=
  informedSet σ k E s t \ doneSet σ k E s t

/-- The paper's progress measure: number of informed plus number of complete nodes. -/
noncomputable def progress (σ : Schedule V) (k : ℕ) (E : V → V → Prop) (s : V) (t : ℕ) : ℕ :=
  (informedSet σ k E s t).card + (doneSet σ k E s t).card

theorem informed_iff {t : ℕ} {v : V} :
    Informed σ k E s t v ↔ ∃ r, recvTime σ k E s t v = some r :=
  Option.isSome_iff_exists

theorem Informed.mono {t t' : ℕ} (htt : t ≤ t') {v : V} (h : Informed σ k E s t v) :
    Informed σ k E s t' v := by
  obtain ⟨r, hr⟩ := informed_iff.1 h
  exact informed_iff.2 ⟨r, recvTime_mono htt hr⟩

theorem Done.mono {t t' : ℕ} (htt : t ≤ t') {v : V} (h : Done σ k E s t v) :
    Done σ k E s t' v :=
  ⟨h.1.mono htt, fun w hw => (h.2 w hw).mono htt⟩

theorem mem_informedSet {t : ℕ} {v : V} : v ∈ informedSet σ k E s t ↔ Informed σ k E s t v := by
  classical
  simp [informedSet]

theorem mem_doneSet {t : ℕ} {v : V} : v ∈ doneSet σ k E s t ↔ Done σ k E s t v := by
  classical
  simp [doneSet]

theorem informedSet_mono {t t' : ℕ} (htt : t ≤ t') :
    informedSet σ k E s t ⊆ informedSet σ k E s t' := fun _ hv =>
  mem_informedSet.2 ((mem_informedSet.1 hv).mono htt)

theorem doneSet_mono {t t' : ℕ} (htt : t ≤ t') : doneSet σ k E s t ⊆ doneSet σ k E s t' :=
  fun _ hv => mem_doneSet.2 ((mem_doneSet.1 hv).mono htt)

theorem progress_mono {t t' : ℕ} (htt : t ≤ t') : progress σ k E s t ≤ progress σ k E s t' :=
  Nat.add_le_add (card_le_card (informedSet_mono htt)) (card_le_card (doneSet_mono htt))

theorem progress_le (t : ℕ) : progress σ k E s t ≤ 2 * Fintype.card V := by
  unfold progress
  have h1 := card_le_univ (informedSet σ k E s t)
  have h2 := card_le_univ (doneSet σ k E s t)
  omega

theorem one_le_progress_zero : 1 ≤ progress σ k E s 0 := by
  have : s ∈ informedSet σ k E s 0 := mem_informedSet.2 (by simp [Informed])
  have := card_pos.2 ⟨s, this⟩
  unfold progress; omega

/-- If no node is active and every node is reachable from the source, broadcasting is
complete. -/
theorem complete_of_activeSet_eq_empty (hreach : ∀ v, Relation.ReflTransGen E s v) {t : ℕ}
    (h : activeSet σ k E s t = ∅) : Complete σ k E s t := by
  have hs : Informed σ k E s t s := (show Informed σ k E s 0 s by simp [Informed]).mono (by omega)
  intro v
  induction hreach v with
  | refl => exact hs
  | @tail u c _ huv ih =>
    have hu : u ∈ informedSet σ k E s t := mem_informedSet.2 ih
    have hd : u ∈ doneSet σ k E s t := by
      by_contra hc
      have : u ∈ activeSet σ k E s t := mem_sdiff.2 ⟨hu, hc⟩
      rw [h] at this; simp at this
    exact (mem_doneSet.1 hd).2 _ huv

/-! ## Collisions -/

/-- A node transmitting alone (transmission set `{u}`) informs all its out-neighbours. -/
theorem informed_of_transmits_alone {t : ℕ} {u w : V} (hu : Transmits σ k E s t u)
    (hσ : σ (t + 1) = {u}) (huw : E u w) : Informed σ k E s (t + 1) w := by
  classical
  cases hw : recvTime σ k E s t w with
  | some r => exact informed_iff.2 ⟨r, recvTime_succ_of_some hw⟩
  | none =>
    rw [Informed, recvTime_succ_of_none hw, ite_eq_left]
    · rfl
    refine ⟨u, ⟨huw, hu⟩, fun u' hu' => ?_⟩
    obtain ⟨r, -, hr⟩ := hu'.2
    have := hr.2.1
    rw [hσ] at this
    simpa using this

/-- If a transmitting in-neighbour `v` does not inform `w`, another in-neighbour of `w`
transmits at the same step (a collision at `w`). -/
theorem exists_collider {t : ℕ} {v w : V} (hv : Transmits σ k E s t v) (hvw : E v w)
    (hw : ¬ Informed σ k E s (t + 1) w) : ∃ u, u ≠ v ∧ E u w ∧ Transmits σ k E s t u := by
  classical
  have hw0 : recvTime σ k E s t w = none := by
    cases h : recvTime σ k E s t w with
    | none => rfl
    | some r => exact absurd (informed_iff.2 ⟨r, recvTime_succ_of_some h⟩) hw
  have hne : ¬ ∃! u, E u w ∧ Transmits σ k E s t u := by
    intro hex
    apply hw
    rw [Informed, recvTime_succ_of_none hw0, ite_eq_left hex]
    rfl
  by_contra hc
  push Not at hc
  exact hne ⟨v, ⟨hvw, hv⟩, fun u hu => by_contra fun h => hc u h hu.1 hu.2⟩

/-- If all nodes active after step `τ` are complete after step `τ' ≥ τ`, the progress grows by
at least the number of these nodes. -/
theorem progress_add_le_of_done {τ τ' : ℕ} (hττ : τ ≤ τ')
    (hall : ∀ v ∈ activeSet σ k E s τ, Done σ k E s τ' v) :
    progress σ k E s τ + (activeSet σ k E s τ).card ≤ progress σ k E s τ' := by
  have hI := card_le_card (informedSet_mono (σ := σ) (k := k) (E := E) (s := s) hττ)
  have hsub : doneSet σ k E s τ ∪ activeSet σ k E s τ ⊆ doneSet σ k E s τ' := by
    intro v hv
    rcases mem_union.1 hv with hv | hv
    · exact doneSet_mono hττ hv
    · exact mem_doneSet.2 (hall v hv)
  have hdisj : Disjoint (doneSet σ k E s τ) (activeSet σ k E s τ) := by
    rw [activeSet]; exact disjoint_sdiff
  have := card_le_card hsub
  rw [card_union_of_disjoint hdisj] at this
  unfold progress
  omega

/-! ## The key lemma (Lemma 4.2, repaired) -/

section key

variable {S p : ℕ}

/-- **Lemma 4.2 (repaired).** If `f` nodes are active at the start of stage `g`, the progress
grows by at least `f` during the next `2 f` stages.

(The paper claims an average progress per stage of `min(1/r, 1 - 1/r)` over `r|F|` stages when
`|F| ≤ k/r`; for `r = 2` this is the statement here, without the hypothesis `|F| ≤ k/2`.) -/
theorem progress_add_le (hS : 0 < S)
    (hlone : ∀ (v : V) (r : ℕ), ∃ t, TransmitsAt σ k r v t ∧ σ t = {v} ∧ t ≤ (r / S + p + 1) * S)
    (happ : ∀ (G : ℕ) (v : V), ∃ t, G * S < t ∧ t ≤ (G + 1) * S ∧ v ∈ σ t)
    (hline : ∀ (t t' : ℕ) (u v : V), 0 < t → t < t' → (t' - 1) / S ≤ (t - 1) / S + p →
      u ∈ σ t → v ∈ σ t → u ∈ σ t' → v ∈ σ t' → u = v)
    (g : ℕ) :
    progress σ k E s (g * S) + (activeSet σ k E s (g * S)).card ≤
      progress σ k E s ((g + 2 * (activeSet σ k E s (g * S)).card) * S) := by
  classical
  set τ := g * S with hτ
  set F := activeSet σ k E s τ with hF
  set f := F.card with hf
  set τ' := (g + 2 * f) * S with hτ'
  have hττ : τ ≤ τ' := Nat.mul_le_mul_right _ (by omega)
  have hI := card_le_card (informedSet_mono (σ := σ) (k := k) (E := E) (s := s) hττ)
  have hD := card_le_card (doneSet_mono (σ := σ) (k := k) (E := E) (s := s) hττ)
  by_cases hall : ∀ v ∈ F, Done σ k E s τ' v
  · -- every active node is complete after the `2f` stages
    exact progress_add_le_of_done hττ hall
  · push Not at hall
    obtain ⟨v, hvF, hvd⟩ := hall
    have hvI : Informed σ k E s τ v := mem_informedSet.1 (mem_sdiff.1 hvF).1
    obtain ⟨rv, hrv⟩ := informed_iff.1 hvI
    have hrvτ : rv ≤ τ := recvTime_le hrv
    obtain ⟨w, hvw, hw⟩ : ∃ w, E v w ∧ ¬ Informed σ k E s τ' w := by
      by_contra hc; push Not at hc
      exact hvd ⟨hvI.mono hττ, hc⟩
    -- `v` transmitting at step `t ≤ τ'` (after its reception)
    have htr : ∀ t, rv < t → TransmitsAt σ k rv v t → Transmits σ k E s (t - 1) v := by
      intro t h1 h2
      refine ⟨rv, recvTime_of_le hrv (by omega), ?_⟩
      rwa [Nat.sub_add_cancel (by omega)]
    -- the lone transmission of `v` (Lemma 4.1) happens after `τ'`
    obtain ⟨ts, hts, hσts, htsle⟩ := hlone v rv
    have hτts : τ' < ts := by
      by_contra hc; push Not at hc
      have h1 := informed_of_transmits_alone (htr ts hts.1 hts) (by
        rwa [Nat.sub_add_cancel (by have := hts.1; omega)]) hvw
      rw [Nat.sub_add_cancel (by have := hts.1; omega)] at h1
      exact hw (h1.mono hc)
    -- hence the window of `2f` stages has at most `p + 1` stages
    have hfp : 2 * f ≤ p + 1 := by
      by_contra hc
      have h1 : rv / S ≤ g := by
        rw [Nat.div_le_iff_le_mul_add_pred hS]; nlinarith
      have : ts ≤ τ' := htsle.trans (by rw [hτ']; exact Nat.mul_le_mul_right _ (by omega))
      omega
    -- the appearance of `v` in each stage `g + i`
    choose T hT1 hT2 hT3 using happ
    have hti_tr : ∀ i, i < 2 * f → Transmits σ k E s (T (g + i) v - 1) v := by
      intro i hi
      have h1 : g * S < T (g + i) v := by
        have := hT1 (g + i) v; have : g * S ≤ (g + i) * S := Nat.mul_le_mul_right _ (by omega)
        omega
      have h2 : T (g + i) v ≤ τ' := (hT2 (g + i) v).trans (Nat.mul_le_mul_right _ (by omega))
      refine htr _ (by omega) ⟨by omega, hT3 _ _, ?_⟩
      exact lt_of_le_of_lt (count_mono (by omega)) hts.2.2
    have hti_w : ∀ i, i < 2 * f → ¬ Informed σ k E s (T (g + i) v - 1 + 1) w := by
      intro i hi hc
      have := hT1 (g + i) v
      have h2 : T (g + i) v ≤ τ' := (hT2 (g + i) v).trans (Nat.mul_le_mul_right _ (by omega))
      exact hw (hc.mono (by omega))
    -- colliders
    have hcol : ∀ i, ∃ u, i < 2 * f → u ≠ v ∧ E u w ∧ Transmits σ k E s (T (g + i) v - 1) u := by
      intro i
      by_cases hi : i < 2 * f
      · obtain ⟨u, hu⟩ := exists_collider (hti_tr i hi) hvw (hti_w i hi)
        exact ⟨u, fun _ => hu⟩
      · exact ⟨v, fun h => absurd h hi⟩
    choose U hU using hcol
    set New := informedSet σ k E s τ' \ informedSet σ k E s τ with hNew
    have hUmem : ∀ i ∈ range (2 * f), U i ∈ F.erase v ∪ New := by
      intro i hi
      rw [mem_range] at hi
      obtain ⟨hUv, hUw, hUt⟩ := hU i hi
      obtain ⟨ru, hru, -⟩ := hUt
      have h2 : T (g + i) v ≤ τ' := (hT2 (g + i) v).trans (Nat.mul_le_mul_right _ (by omega))
      have hUI : Informed σ k E s τ' (U i) :=
        (informed_iff.2 ⟨ru, hru⟩).mono (by omega)
      by_cases h : Informed σ k E s τ (U i)
      · refine mem_union_left _ (mem_erase.2 ⟨hUv, mem_sdiff.2 ⟨mem_informedSet.2 h, ?_⟩⟩)
        intro hd
        exact hw (((mem_doneSet.1 hd).2 w hUw).mono hττ)
      · exact mem_union_right _ (mem_sdiff.2 ⟨mem_informedSet.2 hUI, fun h' => h
          (mem_informedSet.1 h')⟩)
    have hUinj : Set.InjOn U (range (2 * f)) := by
      intro i hi j hj hij
      simp only [coe_range, Set.mem_Iio] at hi hj
      by_contra hne
      -- two transmission steps of `v` sharing the collider `U i = U j`
      have key : ∀ a b, a < b → b < 2 * f → U a = U b → False := by
        intro a b hab hb hUab
        have ha : a < 2 * f := by omega
        have ha1 := hT1 (g + a) v
        have ha2 := hT2 (g + a) v
        have hb1 := hT1 (g + b) v
        have hb2 := hT2 (g + b) v
        have hlt : T (g + a) v < T (g + b) v := by
          have : (g + a + 1) * S ≤ (g + b) * S := Nat.mul_le_mul_right _ (by omega)
          omega
        have hstage : (T (g + b) v - 1) / S ≤ (T (g + a) v - 1) / S + p := by
          have e1 : (T (g + b) v - 1) / S ≤ g + b := by
            rw [Nat.div_le_iff_le_mul_add_pred hS]
            have : (g + b + 1) * S = S * (g + b) + S := by ring
            omega
          have e2 : g + a ≤ (T (g + a) v - 1) / S := by
            rw [Nat.le_div_iff_mul_le hS]; omega
          omega
        obtain ⟨hUa, -, ⟨ra, -, hra⟩⟩ := hU a ha
        obtain ⟨-, -, ⟨rb, -, hrb⟩⟩ := hU b hb
        have hua : U a ∈ σ (T (g + a) v) := by
          have := hra.2.1; rwa [Nat.sub_add_cancel (by omega)] at this
        have hub : U b ∈ σ (T (g + b) v) := by
          have := hrb.2.1; rwa [Nat.sub_add_cancel (by omega)] at this
        rw [← hUab] at hub
        exact hUa (hline (T (g + a) v) (T (g + b) v) (U a) v (by omega) hlt hstage hua
          (hT3 _ _) hub (hT3 _ _))
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact key i j h hj hij
      · exact key j i h hi hij.symm
    have hcard := card_le_card_of_injOn U (fun i hi => hUmem i hi) hUinj
    rw [card_range] at hcard
    have h1 := card_union_le (F.erase v) New
    have h2 : (F.erase v).card = f - 1 := card_erase_of_mem hvF
    have h3 : (informedSet σ k E s τ').card = (informedSet σ k E s τ).card + New.card := by
      rw [hNew, card_sdiff_of_subset (informedSet_mono hττ)]
      omega
    have hf1 : 1 ≤ f := card_pos.2 ⟨v, hvF⟩
    unfold progress
    omega

/-- **Amortization.** If, from every stage boundary, the progress grows by the number `f` of
active nodes within `2f` stages, then broadcasting completes within `2(2n - 1)` stages. -/
theorem complete_of_progress (hreach : ∀ v, Relation.ReflTransGen E s v)
    (hprog : ∀ g, progress σ k E s (g * S) + (activeSet σ k E s (g * S)).card ≤
      progress σ k E s ((g + 2 * (activeSet σ k E s (g * S)).card) * S)) :
    Complete σ k E s (2 * (2 * Fintype.card V - 1) * S) := by
  have main : ∀ m g, 2 * Fintype.card V ≤ progress σ k E s (g * S) + m →
      Complete σ k E s ((g + 2 * m) * S) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro g hg
      set f := (activeSet σ k E s (g * S)).card with hf
      rcases Nat.eq_zero_or_pos f with h0 | hpos
      · have := complete_of_activeSet_eq_empty hreach (card_eq_zero.1 h0)
        exact this.mono (Nat.mul_le_mul_right _ (by omega))
      · have h1 := hprog g
        rw [← hf] at h1
        have h2 := progress_le (σ := σ) (k := k) (E := E) (s := s) ((g + 2 * f) * S)
        have := ih (m - f) (by omega) (g + 2 * f) (by omega)
        rwa [show g + 2 * f + 2 * (m - f) = g + 2 * m by omega] at this
  have := main (2 * Fintype.card V - 1) 0 (by
    have := one_le_progress_zero (σ := σ) (k := k) (E := E) (s := s); simp; omega)
  simpa using this

/-- Completion within `2(2n - 1)` stages for schedules with the three properties above. -/
theorem complete_of_stages (hS : 0 < S)
    (hlone : ∀ (v : V) (r : ℕ), ∃ t, TransmitsAt σ k r v t ∧ σ t = {v} ∧ t ≤ (r / S + p + 1) * S)
    (happ : ∀ (G : ℕ) (v : V), ∃ t, G * S < t ∧ t ≤ (G + 1) * S ∧ v ∈ σ t)
    (hline : ∀ (t t' : ℕ) (u v : V), 0 < t → t < t' → (t' - 1) / S ≤ (t - 1) / S + p →
      u ∈ σ t → v ∈ σ t → u ∈ σ t' → v ∈ σ t' → u = v)
    (hreach : ∀ v, Relation.ReflTransGen E s v) :
    Complete σ k E s (2 * (2 * Fintype.card V - 1) * S) :=
  complete_of_progress hreach (progress_add_le hS hlone happ hline)

end key

end Podc.KShotRadioBroadcast
