import Papers.PODC2020.StoreCollectChurn.SnapshotKey

/-!
# Theorem 8 (safety): Algorithm 7 is a linearizable atomic snapshot

For every execution `E` of Algorithm 7 (any choice rule at Line 77) on top of a store-collect
object whose schedule is regular, the high-level history of `E` has a linearization with respect
to the sequential specification of an atomic snapshot (`theorem8_linearizable`).  This covers
all finite executions, hence (linearizability being a safety property) all prefixes of infinite
ones; pending operations are handled as in CSLib's `IsLinearization`.
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P]

/-- The operation of an instance (`scan` if not invoked). -/
noncomputable def opD (E : List (Ev P V)) (x : OpId P) : SnapOp P V :=
  (opOf (hist E) x).getD .scan

lemma take_mem_iff {α γ : Type} [LinearOrder γ] (key : α → γ) {l : List α}
    (hl : l.Pairwise (fun a b => key a < key b)) {i : ℕ} (hi : i < l.length) {y : α} :
    y ∈ l.take i ↔ y ∈ l ∧ key y < key l[i] := by
  rw [List.pairwise_iff_getElem] at hl
  constructor
  · intro hy
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    simp only [List.length_take] at hj
    rw [List.getElem_take]
    exact ⟨List.getElem_mem _, hl j i (by omega) hi (by omega)⟩
  · rintro ⟨hy, hk⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hy
    rcases lt_trichotomy j i with h | rfl | h
    · rw [List.mem_iff_getElem]
      exact ⟨j, by simp; omega, by rw [List.getElem_take]⟩
    · exact absurd hk (lt_irrefl _)
    · exact absurd (hl i j hi hj h) (not_lt.2 hk.le)

lemma updVal_eq_some {ρ : P} {o : SnapOp P V} {w : V} (h : updVal ρ o = some w) :
    o = .update ρ w := by
  rcases o with _ | ⟨r, v⟩
  · simp [updVal] at h
  · by_cases hr : r = ρ
    · subst hr; simp [updVal] at h; rw [h]
    · simp [updVal, hr] at h

lemma updOf_eq_some {ρ : P} {e : Ev P V} {w : V} (h : updOf ρ e = some w) :
    e = .hinv ρ (.update w) := by
  rcases e with ⟨q, _ | v⟩ | ⟨q, r⟩ | c
  · simp [updOf] at h
  · by_cases hq : q = ρ
    · subst hq; simp [updOf] at h; rw [h]
    · simp [updOf, hq] at h
  · simp [updOf] at h
  · simp [updOf] at h

variable {E : List (Ev P V)}

lemma opD_eq {x : OpId P} {o : SnapOp P V} (h : opOf (hist E) x = some o) : opD E x = o := by
  simp [opD, h]

lemma invAt_of_upd {u : OpId P} {ρ : P} {w : V} (hu : Invoked (hist E) u)
    (h : opD E u = .update ρ w) : u.1 = ρ ∧ ∃ hh, InvAt E u hh ∧
      E[hh]? = some (.hinv u.1 (.update w)) ∧ opOf (hist E) u = some (.update ρ w) := by
  obtain ⟨hh, o, h1, h2⟩ := invoked_iff.1 hu
  have hop := opOf_of_invAt h1 h2
  rw [opD_eq hop] at h
  rcases o with _ | v
  · cases h
  · simp only [toOp, SnapOp.update.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, hh, ⟨_, h1, h2⟩, h1, hop⟩

variable {pk : Pick P V} (hrun : run pk E ≠ none) (hreg : Regular (scSched E))
include hrun hreg

/-- The response of a scan in the linearization is the state built by the preceding updates. -/
lemma scan_resp {l : List (OpId P)} (hl : ∀ x, x ∈ l ↔ x ∈ OSet E)
    (hs : l.Pairwise (fun a b => key E a < key E b)) {i : ℕ} (hi : i < l.length)
    (hx : ScanOK E l[i]) {r : P → Option V} (hr : respOf (hist E) l[i] = some r) :
    (snapSpec P V).runOps (snapSpec P V).init
      (((l.map fun x => (x, opD E x)).take i).map Prod.snd) = r := by
  set x := l[i] with hxdef
  obtain ⟨d, hd, hv⟩ := vec_spec hrun hreg hx
  have hr' : r = rVal d.W₂ := by rw [hd.2.2.2.2.2.2] at hr; exact (Option.some.inj hr).symm
  subst hr'
  funext ρ
  rw [runOps_snap, List.filterMap_map]
  set L := l.map fun x => (x, opD E x)
  have hL : L.Pairwise (fun a b => key E a.1 < key E b.1) := by
    simpa [L, List.pairwise_map] using hs
  have hLi : i < L.length := by simp [L, hi]
  have hLx : L[i].1 = x := by simp [L, hxdef]
  have hmem : ∀ y, y ∈ L.take i ↔ (y.1 ∈ l ∧ y.2 = opD E y.1) ∧ key E y.1 < key E x := by
    intro y
    rw [take_mem_iff (fun z : OpId P × SnapOp P V => key E z.1) hL hLi, hLx]
    simp only [L, List.mem_map]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hk⟩; exact ⟨⟨hz, rfl⟩, hk⟩
    · rintro ⟨⟨hz, h2⟩, hk⟩; exact ⟨⟨y.1, hz, Prod.ext rfl h2.symm⟩, hk⟩
  -- an update of `ρ` placed before `x` is seen by `x`
  have hseen : ∀ y ∈ L.take i, ∀ w, updVal ρ y.2 = some w →
      y.1.1 = ρ ∧ kU E y.1 ≤ vec E x ρ ∧ ∃ hh, InvAt E y.1 hh ∧
        E[hh]? = some (.hinv y.1.1 (.update w)) ∧ opOf (hist E) y.1 = some (.update ρ w) := by
    intro y hy w hw
    obtain ⟨⟨hy1, hy2⟩, hk⟩ := (hmem y).1 hy
    have hupd := updVal_eq_some hw
    rw [hy2] at hupd
    obtain ⟨hρ, hh, hi', hhe, hop⟩ := invAt_of_upd ((hl _).1 hy1).1 hupd
    have hns : opOf (hist E) y.1 ≠ some .scan := by rw [hop]; simp
    have := obs_of_key_lt hrun hreg hns hx hk
    rw [hρ] at this
    exact ⟨hρ, this, hh, hi', hhe, hop⟩
  have hval := rVal_eq_valOf hrun hreg hd.2.1 ρ
  rw [← (hv ρ).2] at hval
  rw [hval]
  rcases hc : vec E x ρ with _ | c
  · -- nothing of `ρ` is seen
    rw [getLast?_filterMap_eq_none]
    · simp [valOf]
    intro y hy
    rcases hw : updVal ρ y.2 with _ | w
    · exact hw
    obtain ⟨-, hk, hh, hi', hhe, -⟩ := hseen y hy w hw
    rw [kU_eq hrun hreg hi' hhe, hc] at hk
    omega
  · -- the `(c+1)`-th update of `ρ`
    obtain ⟨a, haj, hle⟩ := usq_le_updCnt hrun hreg (p := ρ) hd.2.1
    rw [← (hv ρ).2, hc] at hle
    have hlen := fIdx_le_length (updOf ρ) E a
    have hget : (updArgs E ρ)[c]? = some ((updArgs E ρ)[c]'(by unfold updArgs; unfold updCnt at hle; omega)) :=
      List.getElem?_eq_getElem _
    obtain ⟨hh, e, he, hue, hidx⟩ := exists_of_getElem?_filterMap (updOf ρ) hget
    have he' := updOf_eq_some hue
    subst he'
    set w := (updArgs E ρ)[c]'(by unfold updArgs; unfold updCnt at hle; omega)
    set u : OpId P := (ρ, fIdx (invG ρ) E hh)
    have hiu : InvAt E u hh := ⟨_, he, rfl⟩
    have hku : kU E u = c + 1 := by
      rw [kU_eq hrun hreg hiu he]; show updCnt E hh ρ + 1 = c + 1; simp [updCnt, hidx]
    have hopu : opOf (hist E) u = some (.update ρ w) := opOf_of_invAt (x := u) he rfl
    have hW : ∃ y, d.W₂ ρ = some y ∧ y.usqno = c + 1 := by
      rcases hW : d.W₂ ρ with _ | y
      · rw [(hv ρ).2, hW] at hc; simp [usq] at hc
      · rw [(hv ρ).2, hW] at hc; exact ⟨y, rfl, hc⟩
    obtain ⟨y, hWy, hyu⟩ := hW
    obtain ⟨a', -, ha', -⟩ := reg1_some hreg hd.2.1 hWy
    have huO : u ∈ OSet E :=
      ⟨invoked_iff.2 ⟨hh, hiu⟩, Or.inr ⟨⟨w, hopu⟩, a', y, ha', by rw [hku, hyu]⟩⟩
    have hns : opOf (hist E) u ≠ some .scan := by rw [hopu]; simp
    have hku' : key E u < key E x :=
      key_lt_of_obs hrun hreg hns ⟨hx, by rw [hku]; exact hc.ge⟩
    have hemem : (u, opD E u) ∈ L.take i := (hmem _).2 ⟨⟨(hl u).2 huO, rfl⟩, hku'⟩
    have h2 : updCnt E hh ρ = c := by simpa [updCnt] using hidx
    rw [getLast?_filterMap_of_max (fun z : OpId P × SnapOp P V => key E z.1)
      (updVal ρ ∘ Prod.snd) (v := w) (hL.sublist (List.take_sublist i L)) hemem
      (by simp [opD_eq hopu, updVal])]
    · rw [valOf, if_neg (by omega), Nat.add_sub_cancel, hget]
    · intro e' he' hne
      rcases hw' : updVal ρ e'.2 with _ | w'
      · exact absurd hw' hne
      obtain ⟨hρ', hk', hh', hi'', hhe', hop'⟩ := hseen e' he' w' hw'
      have hhe'' : E[hh']? = some (.hinv ρ (.update w')) := hρ' ▸ hhe'
      have hcnt : kU E e'.1 = updCnt E hh' ρ + 1 := by
        rw [kU_eq hrun hreg hi'' hhe', hρ']
      simp only
      rcases lt_trichotomy hh' hh with hlt | rfl | hgt
      · -- an earlier update of `ρ`
        have hns' : opOf (hist E) e'.1 ≠ some .scan := by rw [hop']; simp
        rw [key_upd hns', key_upd hns, Prod.Lex.toLex_le_toLex']
        refine ⟨?_, fun _ => by rw [invAt_invPos hi'', invAt_invPos hiu]; exact hlt.le⟩
        by_cases htop : mU E u = ⊤
        · rw [htop]; exact le_top
        obtain ⟨S0, ⟨hS0, hk0⟩, heq⟩ := mU_spec htop
        rw [heq]
        refine mU_le ⟨hS0, ?_⟩
        rw [hcnt, hρ']
        rw [hku] at hk0
        change c + 1 ≤ vec E S0 ρ at hk0
        have := updCnt_mono (E := E) (p := ρ) (show hh' + 1 ≤ hh by omega)
        rw [updCnt_succ_of_some hhe'' (v := w') (by simp [updOf])] at this
        omega
      · rw [InvAt.inj hi'' hiu]
      · exfalso
        have := updCnt_mono (E := E) (p := ρ) (show hh + 1 ≤ hh' by omega)
        rw [updCnt_succ_of_some he (v := w) (by simp [updOf])] at this
        rw [hcnt] at hk'
        omega

lemma mem_OSet_of_completed {a : OpId P} (ha : Completed (hist E) a) : a ∈ OSet E := by
  refine ⟨completed_invoked hrun hreg ha, ?_⟩
  obtain ⟨h, k', r, hi, hk, hlt, -, -, hn, hor⟩ := retFact_of_completed hrun hreg ha
  obtain ⟨o, -, ho⟩ := hi
  rcases hor with ⟨hsc, -⟩ | ⟨v, hv, -, a', b, y, -, -, hst, -, hy⟩
  · exact Or.inl ⟨ha, opOf_of_invAt hsc ho⟩
  · refine Or.inr ⟨⟨v, opOf_of_invAt hv ho⟩, a', y, hst, ?_⟩
    rw [hy, kU, invAt_invPos ⟨_, hv, ho⟩, updCnt_eq_of_noHIn hlt hn]

/-- The list `l` of operations, sorted by `key`, is a linearization. -/
theorem isLinearization_of_list {l : List (OpId P)} (hl : ∀ x, x ∈ l ↔ x ∈ OSet E)
    (hnd : l.Nodup) (hs : l.Pairwise (fun a b => key E a < key E b)) :
    IsLinearization (hist E) (l.map fun x => (x, opD E x)) := by
  have hfst : (l.map fun x => (x, opD E x)).map Prod.fst = l := by
    rw [List.map_map]; exact List.map_id' l
  refine ⟨by rw [hfst]; exact hnd, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    obtain ⟨k, o, hk, hi⟩ := invoked_iff.1 ((hl x).1 hx).1
    have := opOf_of_invAt hk hi
    simp [opD, this]
  · intro a ha
    rw [hfst]; exact (hl a).2 (mem_OSet_of_completed hrun hreg ha)
  · intro a b hp hb
    rw [hfst] at hb ⊢
    have ha := (hl a).2 (mem_OSet_of_completed hrun hreg hp.completed)
    have hk := key_lt_of_precedes hrun hreg hp ((hl b).1 hb)
    exact sublist_of_pairwise hs ha hb (not_lt.2 hk.le) (fun h => by rw [h] at hk; exact lt_irrefl _ hk)
  · apply seqOK_of_forall
    intro i hi r hr
    simp only [List.length_map] at hi
    simp only [List.getElem_map] at hr ⊢
    have hxO := (hl _).1 (List.getElem_mem hi)
    obtain ⟨k, o, hk, hidx⟩ := invoked_iff.1 hxO.1
    have hop := opOf_of_invAt hk hidx
    by_cases hsc : opOf (hist E) l[i] = some .scan
    · rw [opD_eq hsc]
      exact scan_resp hrun hreg hl hs hi (mem_OSet_scan hxO hsc) hr
    · have hc : Completed (hist E) l[i] := by
        unfold respOf at hr; exact (List.getElem?_eq_some_iff.1 hr).1
      obtain ⟨h, k', r', hi', -, -, -, hresp, -, hor⟩ := retFact_of_completed hrun hreg hc
      rw [hresp] at hr; cases hr
      rcases hor with ⟨hscan, -⟩ | ⟨v, hv, hr', -⟩
      · obtain ⟨o', -, ho'⟩ := hi'
        exact absurd (opOf_of_invAt hscan ho') hsc
      · obtain ⟨o', -, ho'⟩ := hi'
        rw [opD_eq (opOf_of_invAt hv ho'), hr']
        rfl

variable (pk) in
omit hrun hreg in
/-- **Theorem 8 of [AKSW20] (safety)**: Algorithm 7, run on top of any store-collect object whose
schedule satisfies regularity (Section 2), is a linearizable implementation of an atomic
snapshot: the high-level history of every execution has a linearization (with respect to the
sequential specification of an atomic snapshot over the nodes). The choice rule of Line 77 is
arbitrary. -/
theorem theorem8_linearizable (E : List (Ev P V)) (hrun : run pk E ≠ none)
    (hreg : Regular (scSched E)) : ∃ L, IsLinearization (hist E) L := by
  classical
  have hfin : (OSet E).Finite := by
    apply Set.Finite.of_finite_image (f := invPos E)
    · apply (Set.finite_Iio E.length).subset
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := invoked_iff.1 hx.1
      rw [invAt_invPos hk]; exact hk.lt_length
    · intro x hx y hy hxy
      obtain ⟨k, hk⟩ := invoked_iff.1 hx.1
      obtain ⟨k', hk'⟩ := invoked_iff.1 hy.1
      simp only [invAt_invPos hk, invAt_invPos hk'] at hxy
      subst hxy
      exact hk.inj hk'
  let l := hfin.toFinset.toList.mergeSort (fun a b => decide (key E a ≤ key E b))
  have hmem : ∀ x, x ∈ l ↔ x ∈ OSet E := by
    intro x; simp [l]
  have hnd : l.Nodup := (List.mergeSort_perm _ _).nodup_iff.2 (Finset.nodup_toList _)
  have hsort : l.Pairwise (fun a b => decide (key E a ≤ key E b) = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by simp at hab hbc ⊢; exact hab.trans hbc)
      (fun a b => by simpa using le_total (key E a) (key E b)) _
  have hs : l.Pairwise (fun a b => key E a < key E b) := by
    refine (hsort.and hnd).imp_of_mem fun {a b} ha hb ⟨h1, h2⟩ => ?_
    simp only [decide_eq_true_eq] at h1
    exact lt_of_le_of_ne h1 fun h => h2 (key_inj hrun hreg ((hmem a).1 ha) ((hmem b).1 hb) h)
  exact ⟨_, isLinearization_of_list hrun hreg hmem hnd hs⟩

end Podc.StoreCollectChurn.Snap
