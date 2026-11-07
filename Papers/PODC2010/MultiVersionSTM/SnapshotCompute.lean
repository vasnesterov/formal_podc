import Papers.PODC2010.MultiVersionSTM.SnapshotProofs
import Papers.PODC2010.MultiVersionSTM.Forced

/-!
# Computing with the snapshot STMs on histories without aborts

On a history in which every operation succeeded, the latest versions, the freezing events and
the first events of the snapshot STMs depend only on the invocations (`latestS`, `FreezesS`).
Also: an overwritten version is never the latest one (`old_ne_latest`).
-/

namespace Podc.MultiVersionSTM

open scoped Classical

variable {Tx O P : Type}

/-! ### Old versions are not latest -/

lemma cidx_lt_of_commitBefore {h : Hist Tx O} {A B : Tx} (hc : CommitBefore h A B)
    (hB : Committed h B) : cidx h A < cidx h B := by
  obtain ⟨h₁, h₂, rfl, hA, hnB⟩ := hc
  obtain ⟨k, r, hk⟩ := committed_iff_getElem?.1 hA
  have hk' : (h₁ ++ h₂)[k]? = some ⟨.commit A, some r⟩ := by
    rw [List.getElem?_append_left (lt_length_of_getElem? hk)]; exact hk
  have h1 : cidx (h₁ ++ h₂) A < h₁.length := lt_of_le_of_lt (cidx_le_of hk') (lt_length_of_getElem? hk)
  have h2 : h₁.length ≤ cidx (h₁ ++ h₂) B := by
    by_contra! hlt
    obtain ⟨r', hr'⟩ := cidx_spec hB
    rw [List.getElem?_append_left hlt] at hr'
    exact hnB (committed_iff_getElem?.2 ⟨_, r', hr'⟩)
  omega

variable [TxSys Tx P]

/-- An overwritten version is not the latest version. -/
lemma old_ne_latest {h : Hist Tx O} (hw : WF h) {v : Version Tx O} (hold : Old h v) :
    v.2 ≠ latest h v.1 := by
  obtain ⟨-, w, -, W', -, hcw, hbef⟩ := hold
  have htake : h.take h.length = h := List.take_length
  rcases hL : latest h v.1 with _ | L
  · have := hw.le_cidx_of_latest_none (s := h.length) (by rw [htake]; exact hL) hcw
    exact absurd (cidx_lt hcw.1) (by omega)
  · intro hv
    have h1 := hbef L hv
    have h2 := (hw.of_latest_some (s := h.length) (by rw [htake]; exact hL)).2.2 W' hcw
      (cidx_lt hcw.1)
    have h3 := cidx_lt_of_commitBefore h1 hcw.1
    omega

/-! ### Latest versions from the schedule -/

/-- `latestR` on a reversed list of invocations. -/
noncomputable def latestR (o : O) : List (Inv Tx O) → Option Tx
  | [] => none
  | i :: r => if ∃ W, i = .commit W ∧ Inv.write W o ∈ r then some i.tx else latestR o r

/-- The latest version of `o` after a schedule whose operations all succeed. -/
noncomputable def latestS (σ : List (Inv Tx O)) (o : O) : Option Tx := latestR o σ.reverse

lemma latestS_snoc (σ : List (Inv Tx O)) (i : Inv Tx O) (o : O) :
    latestS (σ ++ [i]) o = if ∃ W, i = .commit W ∧ Inv.write W o ∈ σ then some i.tx else latestS σ o := by
  simp [latestS, latestR]

lemma latest_eq_latestS {h : Hist Tx O} (hs : AllSucc h) (o : O) :
    latest h o = latestS (h.map Event.inv) o := by
  induction h using List.reverseRecOn with
  | nil => simp [latestS, latestR]
  | append_singleton h e ih =>
    have hs' := allSucc_snoc.1 hs
    rw [latest_snoc, List.map_append, List.map_singleton, latestS_snoc, ih hs'.1]
    congr 1
    apply propext
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 hs'.2
    simp only [CommitWrites, hr, writes_iff_map]
    exact ⟨fun ⟨_, W, h1, h2⟩ => ⟨W, h1, h2⟩, fun ⟨W, h1, h2⟩ => ⟨⟨r, rfl⟩, W, h1, h2⟩⟩

/-! ### Freezing events and first events from the schedule -/

/-- `Freezes` on the schedule level. -/
def FreezesS (σ : List (Inv Tx O)) (T : Tx) (k : ℕ) : Prop :=
  ∃ i, σ[k]? = some i ∧ ∃ o, (∃ W, i = .commit W ∧ Inv.write W o ∈ σ.take k) ∧
    Inv.read T o ∈ σ.take k

lemma freezes_iff {h : Hist Tx O} (hs : AllSucc h) (T : Tx) (k : ℕ) :
    Freezes h T k ↔ FreezesS (h.map Event.inv) T k := by
  have hsk : AllSucc (h.take k) := fun e he => hs e (List.mem_of_mem_take he)
  simp only [Freezes, FreezesS, List.getElem?_map, Option.map_eq_some_iff, ← List.map_take]
  constructor
  · rintro ⟨e, he, o, ⟨_, W, h1, h2⟩, ⟨v, hv⟩⟩
    exact ⟨e.inv, ⟨e, he, rfl⟩, o, ⟨W, h1, writes_iff_map.1 h2⟩, List.mem_map.2 ⟨_, hv, rfl⟩⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, o, ⟨W, h1, h2⟩, h3⟩
    obtain ⟨e', he', he'i⟩ := List.mem_map.1 h3
    obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 (hs e (List.mem_of_getElem? he))
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 (hsk e' he')
    refine ⟨e, he, o, ⟨⟨r, hr⟩, W, h1, writes_iff_map.2 h2⟩, v, ?_⟩
    cases e'; simp_all

lemma firstIdx_eq_map (h : Hist Tx O) (T : Tx) :
    firstIdx h T = (h.map Event.inv).findIdx (fun i => decide (Inv.tx i = T)) := by
  simp [firstIdx, List.findIdx_map, Function.comp_def]

lemma snap_not_began (lazy : Bool) {h : Hist Tx O} {T : Tx} (hb : ¬ Began h T) :
    snap lazy h T = h.length := by
  cases lazy
  · simp [snap, firstIdx_eq_length hb]
  · have : frz h T = none := by
      rw [frz_eq_none_iff]
      rintro k - ⟨e, -, o, -, v, hv⟩
      exact hb (Began.of_take (k := k) ⟨_, hv, rfl⟩)
    simp [snap, this]

end Podc.MultiVersionSTM
