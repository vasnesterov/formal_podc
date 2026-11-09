/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Consequences
import Papers.PODC2019.ReconfigurableCommit.LemmaA3

/-!
# Safety of the corrected protocol: from the invariant to TCS-LL and correctness

From the invariant `Inv` of the protocol of Figure 1 (with the check `e ≥ new_epoch` at line 56)
and its consequences (`Consequences.lean`) we derive:

* the TCS-LL witness `wit` of a protocol state and the classification of earlier accepted
  entries in a vote context (`Inv.vote_ctx`, from Proposition A.2);
* Lemma A.1 (`Inv.tcsll`): every history of the protocol satisfies TCS-LL (without constraint
  (12));
* Theorem 4.1 (`Inv.correct`): via Lemma A.3, every history of the protocol is correct;
* well-formedness of the histories (`Inv.wellFormed`).
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

section Witness

variable (Pa : Params T Pl S P) (st : State T Pl S P)

/-- The transactions certified in `h`, as a finset. -/
def certSet (h : History T Pl) : Finset T :=
  (h.filterMap fun
    | Event.certify t _ => some t
    | _ => none).toFinset

omit [DecidableEq Pl] in
theorem mem_certSet {h : History T Pl} {t : T} : t ∈ certSet h ↔ ∃ l, Event.certify t l ∈ h := by
  unfold certSet
  simp only [List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hs⟩
    rcases e with ⟨t', l⟩ | ⟨t', d⟩
    · simp only [Option.some.injEq] at hs
      subst hs
      exact ⟨l, he⟩
    · simp at hs
  · rintro ⟨l, h⟩
    exact ⟨_, h, rfl⟩

open Classical in
/-- An accepted entry of `t` at shard `s` (epoch, slot, entry), if any (chosen). -/
noncomputable def accOf (s : S) (t : T) : Option (ℕ × ℕ × (Entry T Pl × ℕ)) :=
  if h : ∃ x : ℕ × ℕ × (Entry T Pl × ℕ), AccL st s x.1 x.2.1 x.2.2 ∧ x.2.2.1.1 = t then
    some h.choose
  else none

/-- The vote `dₛ[t]`: the vote of the accepted entry. -/
noncomputable def dsW (s : S) (t : T) : Option Dec := (accOf st s t).map fun x => x.2.2.1.2.2

/-- The position `posₛ[t]`: the slot of the accepted entry. -/
noncomputable def posW (s : S) (t : T) : ℕ := ((accOf st s t).map fun x => x.2.1).getD 0

/-- The payload `ploadₛ[t]`: the payload of the accepted entry. -/
noncomputable def plW (s : S) (t : T) : Pl :=
  ((accOf st s t).map fun x => x.2.2.1.2.1).getD Pa.σ.eps

/-- The slots `J₂` recorded for the vote at slot `k` of the log of `o`. -/
def J₂At (s : S) (o k : ℕ) : Finset ℕ :=
  match st.vinfo s o k with
  | some (_, J₂, _) => J₂
  | none => ∅

open Classical in
/-- The set `Pₛ[t]`: if the vote of `t` is `commit`, the transactions in the slots of `L₂` (as
far as they are accepted with vote `commit` before `t`); if it is `abort`, all transactions
accepted with vote `commit` before `t`. -/
noncomputable def PsW (s : S) (t : T) : Finset T :=
  match accOf st s t with
  | none => ∅
  | some (_, k, ((_, _, d), o)) => (certSet st.hist).filter fun t' =>
      dsW st s t' = some .commit ∧ posW st s t' < k ∧
        (d = .abort ∨ ∃ j ∈ J₂At st s o k, (st.elog s o j).map (·.1.1) = some t')

open Classical in
/-- The set `Tₛ[t]`, as forced by constraint (10). -/
noncomputable def TsW (s : S) (t : T) : Finset T :=
  ((certSet st.hist).filter fun t' =>
    (dsW st s t').isSome ∧ posW st s t' < posW st s t ∧ Committed st.hist t') \ PsW st s t

/-- The TCS-LL witness of a protocol state. -/
noncomputable def wit : LLWitness T Pl S where
  ds := dsW st
  pos := posW st
  pload := plW Pa st
  Ts := TsW st
  Ps := PsW st

end Witness

namespace Inv

variable {Pa : Params T Pl S P} {st : State T Pl S P}


omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem accOf_spec {s : S} {t : T} {x : ℕ × ℕ × (Entry T Pl × ℕ)} (h : accOf st s t = some x) :
    AccL st s x.1 x.2.1 x.2.2 ∧ x.2.2.1.1 = t := by
  unfold accOf at h
  split_ifs at h with hx
  cases h
  exact hx.choose_spec

omit [DecidableEq T] in
theorem accOf_eq (hI : Inv Pa st) {s : S} {t : T} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : AccL st s e k v) (ht : v.1.1 = t) : ∃ e', accOf st s t = some (e', k, v) := by
  have hx : ∃ x : ℕ × ℕ × (Entry T Pl × ℕ), AccL st s x.1 x.2.1 x.2.2 ∧ x.2.2.1.1 = t :=
    ⟨(e, k, v), h, ht⟩
  refine ⟨hx.choose.1, ?_⟩
  have hspec := hx.choose_spec
  unfold accOf
  simp only [hx, ↓reduceDIte]
  generalize hx.choose = x at hspec ⊢
  obtain ⟨e', k', v'⟩ := x
  obtain ⟨h1, h2⟩ := hspec
  have hk : k' = k := hI.accL_unique_txn h1 h (h2.trans ht.symm)
  subst hk
  have hv : v' = v := hI.accL_unique_slot h1 h
  subst hv
  rfl

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem exists_of_isSome {s : S} {t : T} (h : (dsW st s t).isSome) :
    ∃ e k v, accOf st s t = some (e, k, v) ∧ AccL st s e k v ∧ v.1.1 = t := by
  unfold dsW at h
  cases hx : accOf st s t with
  | none => simp [hx] at h
  | some x => exact ⟨x.1, x.2.1, x.2.2, rfl, accOf_spec hx⟩

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem dsW_of {s : S} {t : T} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : accOf st s t = some (e, k, v)) : dsW st s t = some v.1.2.2 := by
  simp [dsW, h]

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem posW_of {s : S} {t : T} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : accOf st s t = some (e, k, v)) : posW st s t = k := by
  simp [posW, h]

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem plW_of {s : S} {t : T} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : accOf st s t = some (e, k, v)) : plW Pa st s t = v.1.2.1 := by
  simp [plW, h]

omit [DecidableEq Pl] [DecidableEq S] [Fintype S] in
theorem mem_PsW {s : S} {t t' t₀ : T} {e k o : ℕ} {l : Pl} {d : Dec}
    (h : accOf st s t = some (e, k, ((t₀, l, d), o))) :
    t' ∈ PsW st s t ↔ t' ∈ certSet st.hist ∧ dsW st s t' = some .commit ∧ posW st s t' < k ∧
      (d = .abort ∨ ∃ j ∈ J₂At st s o k, (st.elog s o j).map (·.1.1) = some t') := by
  simp [PsW, h]

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P] [Fintype S] in
theorem exists_idx_of_decIn {t : T} {d : Dec} {n : ℕ} (h : DecIn st t d n) :
    ∃ i < n, st.hist[i]? = some (Event.decide t d) := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_take] at hi
  split_ifs at hi with hin
  exact ⟨i, hin, hi⟩

omit [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P] [Fintype S] in
theorem mem_of_decIn {t : T} {d : Dec} {n : ℕ} (h : DecIn st t d n) :
    Event.decide t d ∈ st.hist :=
  List.mem_of_mem_take h

omit [DecidableEq T] in
theorem shard_of_accL (hI : Inv Pa st) {s : S} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : AccL st s e k v) : s ∈ Pa.σ.shards v.1.1 :=
  (hI.elog_txn s e k v.1.1 v.1.2.1 v.1.2.2 v.2 h.1).1

omit [DecidableEq T] in
/-- A committed transaction has vote `commit` in each of its accepted entries. -/
theorem vote_of_committed (hI : Inv Pa st) {s : S} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : AccL st s e k v) (hc : Committed st.hist v.1.1) : v.1.2.2 = .commit := by
  obtain ⟨es, ks, vs, hv, hd⟩ := hI.hist_decide _ _ hc
  have hs := hI.shard_of_accL h
  obtain ⟨h1, ht1⟩ := hv s hs
  have hk := hI.accL_unique_txn h1 h ht1
  rw [hk] at h1
  rw [← hI.accL_unique_slot h1 h]
  exact meetOver_eq_commit.1 hd.symm s hs

omit [DecidableEq T] in
/-- The vote context of a `commit` vote, and the classification of the earlier accepted
entries of the same shard (Proposition A.2). -/
theorem vote_ctx (hI : Inv Pa st) {s : S} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : AccL st s e k v) (hd : v.1.2.2 = .commit) :
    ∃ J₁ J₂ hl, st.vinfo s v.2 k = some (J₁, J₂, hl) ∧
      v.1.2.2 = (Pa.fs s (J₁.image (plAt Pa st s v.2)) v.1.2.1).meet
        (Pa.gs s (J₂.image (plAt Pa st s v.2)) v.1.2.1) ∧
      ∀ e' k' w, AccL st s e' k' w → k' < k → st.elog s v.2 k' = some w ∧
        ((k' ∈ J₁ ∧ DecIn st w.1.1 .commit hl) ∨ (k' ∈ J₂ ∧ w.1.2.2 = .commit) ∨
          w.1.2.2 = .abort ∨ DecIn st w.1.1 .abort hl) := by
  obtain ⟨-, ho, -⟩ := hI.elog_origin s e k v.1 v.2 h.1
  cases hvi : st.vinfo s v.2 k with
  | none =>
    have := hI.vinfo_none s v.2 k v.1.1 v.1.2.1 v.1.2.2 ho hvi
    rw [hd] at this
    cases this
  | some x =>
    obtain ⟨J₁, J₂, hl⟩ := x
    obtain ⟨-, -, hdv, h1, h2, h5⟩ :=
      hI.vinfo_ok s v.2 k v.1.1 v.1.2.1 v.1.2.2 J₁ J₂ hl ho hvi
    refine ⟨J₁, J₂, hl, rfl, hdv, fun e' k' w h' hk => ?_⟩
    have hw := hI.accL_prefix h h' hk
    refine ⟨hw, ?_⟩
    rcases h5 k' hk w hw with hj | hj | hj | hj
    · exact Or.inl ⟨hj, h1 k' hj w hw⟩
    · exact Or.inr (Or.inl ⟨hj, h2 k' hj w hw⟩)
    · exact Or.inr (Or.inr (Or.inl hj))
    · exact Or.inr (Or.inr (Or.inr hj))

theorem cert_of_accL (hI : Inv Pa st) {s : S} {e k : ℕ} {v : Entry T Pl × ℕ}
    (h : AccL st s e k v) : v.1.1 ∈ certSet st.hist := by
  obtain ⟨-, l₀, hc, -⟩ := hI.elog_txn s e k v.1.1 v.1.2.1 v.1.2.2 v.2 h.1
  exact mem_certSet.2 ⟨l₀, hc⟩

/-- Constraint (9) of Figure 6 for the witness `wit`. -/
theorem c9 (hI : Inv Pa st) (hfs : ∀ s, Distributive (Pa.fs s))
    (hgs : ∀ s, Distributive (Pa.gs s)) (s : S) (t : T) (d : Dec) (hd : dsW st s t = some d) :
    Dec.le d ((Pa.fs s ((TsW st s t).image (plW Pa st s)) (plW Pa st s t)).meet
      (Pa.gs s ((PsW st s t).image (plW Pa st s)) (plW Pa st s t))) := by
  obtain ⟨e, k, ⟨⟨t₀, l, dv⟩, o⟩, hacc, h, ht⟩ :=
    exists_of_isSome (by simp [hd] : (dsW st s t).isSome)
  simp only at ht
  subst ht
  rw [dsW_of hacc] at hd
  cases hd
  cases dv with
  | abort => exact Dec.abort_le _
  | commit =>
  obtain ⟨J₁, J₂, hl, hvi, hvote, hcls⟩ := hI.vote_ctx h rfl
  simp only at hvi hvote hcls
  rw [eq_comm, Dec.meet_eq_commit] at hvote
  rw [Dec.le_commit_iff, Dec.meet_eq_commit, plW_of hacc]
  have hTs : (TsW st s t₀).image (plW Pa st s) ⊆ J₁.image (plAt Pa st s o) := by
    intro x hx
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hx
    simp only [TsW, Finset.mem_sdiff, Finset.mem_filter] at ht'
    obtain ⟨⟨hcert, hsome, hpos, hcom⟩, hnP⟩ := ht'
    obtain ⟨e', k', w, hacc', h', rfl⟩ := exists_of_isSome hsome
    rw [posW_of hacc', posW_of hacc] at hpos
    obtain ⟨hw, hc⟩ := hcls e' k' w h' hpos
    rw [plW_of hacc']
    rcases hc with ⟨hj, -⟩ | ⟨hj, hwc⟩ | hwa | hda
    · exact Finset.mem_image.2 ⟨k', hj, by simp [plAt, hw]⟩
    · refine absurd ((mem_PsW hacc).2 ⟨hcert, by rw [dsW_of hacc', hwc], ?_, Or.inr ⟨k', ?_, ?_⟩⟩)
        hnP
      · rw [posW_of hacc']; exact hpos
      · simpa [J₂At, hvi] using hj
      · simp [hw]
    · have := hI.vote_of_committed h' hcom
      rw [hwa] at this
      cases this
    · have := hI.hist_decide_unique _ _ _ hcom (mem_of_decIn hda)
      cases this
  have hPs : (PsW st s t₀).image (plW Pa st s) ⊆ J₂.image (plAt Pa st s o) := by
    intro x hx
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨-, hds, hpos, hor⟩ := (mem_PsW hacc).1 ht'
    rcases hor with hab | ⟨j, hj, hjt⟩
    · cases hab
    obtain ⟨e', k', w, hacc', h', rfl⟩ :=
      exists_of_isSome (st := st) (s := s) (t := t') (by simp [hds])
    rw [posW_of hacc'] at hpos
    have hw := (hcls e' k' w h' hpos).1
    simp only [J₂At, hvi] at hj
    obtain ⟨y, hy, hyt⟩ := Option.map_eq_some_iff.1 hjt
    have := hI.elog_dist s o j k' y w hy hw hyt
    subst this
    rw [plW_of hacc']
    exact Finset.mem_image.2 ⟨j, hj, by simp [plAt, hw]⟩
  exact ⟨(hfs s).mono hTs hvote.1, (hgs s).mono hPs hvote.2⟩

/-- Every edge `a → b` of `≺rt ∪ ≺dec` goes from a transaction decided at some index `i` to one
all of whose decisions are after `i`. -/
theorem edge (hI : Inv Pa st) {a b : T}
    (hab : RT st.hist a b ∨ (wit Pa st).DecRel st.hist a b) :
    ∃ (i : ℕ) (d : Dec), st.hist[i]? = some (Event.decide a d) ∧
      ∀ j d', st.hist[j]? = some (Event.decide b d') → i < j := by
  rcases hab with ⟨i, j, hij, ⟨d, hi⟩, ⟨l, hj⟩⟩ | ⟨s, hsome, hor⟩
  · refine ⟨i, d, by rw [List.getElem?_eq_getElem i.2]; exact congrArg some hi, fun j' d' hj' => ?_⟩
    obtain ⟨j'', hlt, l', hc⟩ := hI.hist_decide_after j' b d' hj'
    have := hI.hist_certify_idx j'' j b l' l hc
      (by rw [List.getElem?_eq_getElem j.2]; exact congrArg some hj)
    rw [Fin.lt_def] at hij
    omega
  · change (dsW st s b).isSome at hsome
    obtain ⟨e, k, ⟨⟨t₀, l, dv⟩, o⟩, hacc, h, ht⟩ := exists_of_isSome hsome
    simp only at ht
    subst ht
    have key : ∃ e' k' w, accOf st s a = some (e', k', w) ∧ AccL st s e' k' w ∧ w.1.1 = a ∧
        k' < k ∧ w.1.2.2 = .commit ∧ a ∉ PsW st s t₀ := by
      rcases hor with hT | ⟨hpos, hds, -, hnP⟩
      · change a ∈ TsW st s t₀ at hT
        simp only [TsW, Finset.mem_sdiff, Finset.mem_filter] at hT
        obtain ⟨⟨-, hs', hpos, hcom⟩, hnP⟩ := hT
        obtain ⟨e', k', w, hacc', h', rfl⟩ := exists_of_isSome hs'
        rw [posW_of hacc', posW_of hacc] at hpos
        exact ⟨e', k', w, hacc', h', rfl, hpos, hI.vote_of_committed h' hcom, hnP⟩
      · change dsW st s a = some .commit at hds
        change posW st s a < posW st s t₀ at hpos
        obtain ⟨e', k', w, hacc', h', rfl⟩ :=
          exists_of_isSome (st := st) (s := s) (t := a) (by simp [hds])
        rw [posW_of hacc', posW_of hacc] at hpos
        rw [dsW_of hacc'] at hds
        exact ⟨e', k', w, hacc', h', rfl, hpos, Option.some.inj hds, hnP⟩
    obtain ⟨e', k', w, hacc', h', rfl, hpos, hwc, hnP⟩ := key
    have hcert := hI.cert_of_accL h'
    have hdsa : dsW st s w.1.1 = some .commit := by rw [dsW_of hacc', hwc]
    have hposa : posW st s w.1.1 < k := by rw [posW_of hacc']; exact hpos
    cases dv with
    | abort => exact absurd ((mem_PsW hacc).2 ⟨hcert, hdsa, hposa, Or.inl rfl⟩) hnP
    | commit =>
    obtain ⟨J₁, J₂, hl, hvi, -, hcls⟩ := hI.vote_ctx h rfl
    simp only at hvi hcls
    obtain ⟨hw, hc⟩ := hcls e' k' w h' hpos
    have hlt : ∃ i < hl, ∃ dd, st.hist[i]? = some (Event.decide w.1.1 dd) := by
      rcases hc with ⟨-, hd⟩ | ⟨hj, -⟩ | hwa | hd
      · obtain ⟨i, hi, he⟩ := exists_idx_of_decIn hd
        exact ⟨i, hi, _, he⟩
      · refine absurd ((mem_PsW hacc).2 ⟨hcert, hdsa, hposa, Or.inr ⟨k', ?_, by simp [hw]⟩⟩) hnP
        simpa [J₂At, hvi] using hj
      · rw [hwa] at hwc
        cases hwc
      · obtain ⟨i, hi, he⟩ := exists_idx_of_decIn hd
        exact ⟨i, hi, _, he⟩
    obtain ⟨i, hi, dd, he⟩ := hlt
    refine ⟨i, dd, he, fun j d' hj => ?_⟩
    obtain ⟨e'', k'', v'', h'', hb, hord⟩ := hI.hist_order j t₀ d' hj s (hI.shard_of_accL h)
    have hk := hI.accL_unique_txn h'' h hb
    subst hk
    have hv := hI.accL_unique_slot h'' h
    subst hv
    have := hord J₁ J₂ hl hvi
    omega

theorem trans_edge (hI : Inv Pa st) {a b : T}
    (h : Relation.TransGen (fun a b => RT st.hist a b ∨ (wit Pa st).DecRel st.hist a b) a b) :
    ∃ (i : ℕ) (d : Dec), st.hist[i]? = some (Event.decide a d) ∧
      ∀ j d', st.hist[j]? = some (Event.decide b d') → i < j := by
  induction h with
  | single hab => exact hI.edge hab
  | tail _ hbc ih =>
    obtain ⟨i, d, hi, hlt⟩ := ih
    obtain ⟨i', d', hi', hlt'⟩ := hI.edge hbc
    exact ⟨i, d, hi, fun j d'' hj => (hlt i' d' hi').trans (hlt' j d'' hj)⟩

/-- Lemma A.1 of [Bravo–Gotsman 2019] (without constraint (12)): the history of every state
satisfying the invariant satisfies TCS-LL. The shard-local certification functions are assumed
distributive (as in §2, "similarly to (1)"); this is used for constraint (9). -/
theorem tcsll (hI : Inv Pa st) (hfs : ∀ s, Distributive (Pa.fs s))
    (hgs : ∀ s, Distributive (Pa.gs s)) : TCSLL Pa.σ Pa.fs Pa.gs st.hist := by
  refine ⟨wit Pa st, ?_, ?_, ?_, ?_, ?_, fun s t d hd => hI.c9 hfs hgs s t d hd, ?_, ?_, ?_⟩
  · -- domain
    intro s t hs
    obtain ⟨e, k, v, -, h, rfl⟩ := exists_of_isSome hs
    obtain ⟨hsh, l₀, hc, -⟩ := hI.elog_txn s e k v.1.1 v.1.2.1 v.1.2.2 v.2 h.1
    exact ⟨hsh, l₀, hc⟩
  · -- (6), definedness
    intro t d hd s hs
    obtain ⟨es, ks, vs, hv, -⟩ := hI.hist_decide t d hd
    obtain ⟨e', hx⟩ := hI.accOf_eq (hv s hs).1 (hv s hs).2
    change (dsW st s t).isSome
    simp [dsW_of hx]
  · -- (6)
    intro t d hd
    obtain ⟨es, ks, vs, hv, rfl⟩ := hI.hist_decide t d hd
    rw [meetOver_eq_commit]
    refine forall₂_congr fun s hs => ?_
    obtain ⟨e', hx⟩ := hI.accOf_eq (hv s hs).1 (hv s hs).2
    change _ ↔ dsW st s t = _
    simp [dsW_of hx]
  · -- (7)
    intro s t₁ t₂ hne h₁ h₂ hpos
    obtain ⟨e₁, k₁, v₁, hx₁, ha₁, rfl⟩ := exists_of_isSome h₁
    obtain ⟨e₂, k₂, v₂, hx₂, ha₂, rfl⟩ := exists_of_isSome h₂
    change posW st s _ = posW st s _ at hpos
    rw [posW_of hx₁, posW_of hx₂] at hpos
    subst hpos
    exact hne (by rw [hI.accL_unique_slot ha₁ ha₂])
  · -- (8)
    intro t l s hc
    have key : ∀ d, dsW st s t = some d →
        (plW Pa st s t = Pa.σ.proj l s ∨ (plW Pa st s t = Pa.σ.eps ∧ d = .abort)) := by
      intro d hd
      obtain ⟨e, k, v, hx, h, rfl⟩ :=
        exists_of_isSome (st := st) (s := s) (t := t) (by simp [hd])
      rw [dsW_of hx] at hd
      cases hd
      obtain ⟨-, l₀, hc₀, hl⟩ := hI.elog_txn s e k v.1.1 v.1.2.1 v.1.2.2 v.2 h.1
      rw [hI.hist_certify_unique _ _ _ hc₀ hc] at hl
      rw [plW_of hx]
      exact hl
    refine ⟨fun hd => ?_, fun hd => ?_⟩
    · rcases key _ hd with h | ⟨-, h⟩
      · exact h
      · cases h
    · rcases key _ hd with h | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
  · -- (10)
    intro s t _ t'
    change t' ∈ TsW st s t ↔ _
    simp only [TsW, Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨⟨-, h⟩, hn⟩
      exact ⟨h, hn⟩
    · rintro ⟨h, hn⟩
      obtain ⟨e, k, v, -, ha, rfl⟩ := exists_of_isSome h.1
      exact ⟨⟨hI.cert_of_accL ha, h⟩, hn⟩
  · -- (11)
    intro s t hs t' ht'
    obtain ⟨e, k, ⟨⟨t₀, l, dv⟩, o⟩, hacc, -, -⟩ := exists_of_isSome hs
    obtain ⟨-, hds, hpos, -⟩ := (mem_PsW hacc).1 ht'
    exact ⟨hds, by change _ < posW st s t; rw [posW_of hacc]; exact hpos⟩
  · -- (13)
    intro t h
    obtain ⟨i, d, hi, hlt⟩ := hI.trans_edge h
    exact lt_irrefl _ (hlt i d hi)

/-- Theorem 4.1 of [Bravo–Gotsman 2019], from the invariant: if the shard-local certification
functions match `f` (and `ε` is neutral, see `lemma_A_3`), the history of every state satisfying
the invariant is correct w.r.t. `f`. -/
theorem correct (hI : Inv Pa st) {f : Finset Pl → Pl → Dec} (hm : Matching Pa.σ f Pa.fs Pa.gs)
    (heps : EpsNeutral Pa.σ Pa.fs) : Correct f st.hist :=
  lemma_A_3 hm heps hI.hist_certify (hI.tcsll hm.distrib_fs hm.distrib_gs)

omit [DecidableEq T] in
/-- The histories of states satisfying the invariant are well-formed (§2). -/
theorem wellFormed (hI : Inv Pa st) : WellFormed st.hist where
  certify_unique := hI.hist_certify_unique
  decide_unique := hI.hist_decide_unique
  decide_after_certify j t d hj := by
    obtain ⟨i, hij, l, hi⟩ := hI.hist_decide_after j t d
      (by rw [List.getElem?_eq_getElem j.2]; exact congrArg some hj)
    have hilen : i < st.hist.length := (List.getElem?_eq_some_iff.1 hi).1
    refine ⟨⟨i, hilen⟩, by rw [Fin.lt_def]; exact hij, l, ?_⟩
    simpa [List.getElem?_eq_getElem hilen] using hi

end Inv

end Podc.ReconfigurableCommit
