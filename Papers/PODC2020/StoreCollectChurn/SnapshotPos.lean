import Papers.PODC2020.StoreCollectChurn.SnapshotSeq

/-!
# Configurations along an execution, and positions of operation instances
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P] {E : List (Ev P V)} (pk : Pick P V)

/-- The configuration after the first `i` events. -/
noncomputable def cfgAt (E : List (Ev P V)) (i : ℕ) : Cfg P V :=
  (run pk (E.take i)).getD fun _ => LState.init

variable {pk}

lemma run_cfgAt (hrun : run pk E ≠ none) {i : ℕ} (hi : i ≤ E.length) :
    run pk (E.take i) = some (cfgAt pk E i) := by
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.1 (run_take_ne_none pk hrun hi)
  simp [cfgAt, hc]

lemma cfgAt_step (hrun : run pk E ≠ none) {i : ℕ} (hi : i < E.length) :
    lstep pk E[i].proc (cfgAt pk E i E[i].proc) E[i] = some (cfgAt pk E (i + 1) E[i].proc) ∧
      ∀ q, q ≠ E[i].proc → cfgAt pk E (i + 1) q = cfgAt pk E i q := by
  have h1 := run_cfgAt hrun (show i + 1 ≤ E.length by omega)
  rw [run_take_succ pk hi, run_cfgAt hrun hi.le] at h1
  simp only [Option.bind_some, gstep, Option.map_eq_some_iff] at h1
  obtain ⟨s', hs, he⟩ := h1
  refine ⟨by rw [← he, Function.update_self]; exact hs, fun q hq => by
    rw [← he, Function.update_of_ne hq]⟩

lemma cfgAt_const (hrun : run pk E ≠ none) {r : P} {a : ℕ} :
    ∀ b, a < b → b ≤ E.length → NoEvIn E r a b → cfgAt pk E b r = cfgAt pk E (a + 1) r
  | 0, h, _, _ => by omega
  | b + 1, h, hb, hn => by
    rcases Nat.lt_or_ge a b with hab | hab
    · rw [(cfgAt_step hrun (by omega)).2 r (fun h' => hn b hab (by omega) _
        (List.getElem?_eq_getElem (by omega)) h'.symm)]
      exact cfgAt_const hrun b hab (by omega) (hn.mono (by omega))
    · obtain rfl : a = b := by omega
      rfl

/-- After a store, the next event of the node is the `ACK`. -/
lemma next_of_store (hrun : run pk E ≠ none) {a b : ℕ} {r : P} {x : SCVal P V}
    (ha : StE E a r x) (hab : NextE E a b) : E[b]? = some (.sc (.ack r)) := by
  have haL : a < E.length := by
    by_contra h; rw [StE, List.getElem?_eq_none (by omega)] at ha; cases ha
  obtain ⟨hlt, e, e', hea, heb, hp, hno⟩ := hab
  have hbL : b < E.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at heb; cases heb
  have hEa : E[a] = .sc (.stInv r x) := by
    rw [StE, List.getElem?_eq_getElem haL] at ha; exact Option.some.inj ha
  rw [StE, hea] at ha; cases ha
  have hEb : E[b] = .sc e' := by rw [List.getElem?_eq_getElem hbL] at heb; exact Option.some.inj heb
  -- the first event of `r` after `a`
  have hex : ∃ c, a < c ∧ c ≤ b ∧ ∃ h : c < E.length, E[c].proc = r :=
    ⟨b, hlt, le_rfl, hbL, by rw [hEb]; simpa [Ev.proc, SCEv.proc] using hp⟩
  classical
  let c := Nat.find hex
  obtain ⟨hc1, hc2, hcL, hcp⟩ := Nat.find_spec hex
  have hmin : NoEvIn E r a c := fun k hk1 hk2 e'' hk hkp => by
    have hkL : k < E.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hk; cases hk
    rw [List.getElem?_eq_getElem hkL] at hk
    exact Nat.find_min hex hk2 ⟨hk1, by omega, hkL, by rw [Option.some.inj hk]; exact hkp⟩
  have hs1 := (cfgAt_step hrun haL).1
  have hs2 := (cfgAt_step hrun hcL).1
  rw [hEa] at hs1
  simp only [Ev.proc, SCEv.proc] at hs1
  rw [hcp, cfgAt_const hrun c hc1 hcL.le hmin] at hs2
  generalize cfgAt pk E (a + 1) r = s' at hs1 hs2
  generalize cfgAt pk E a r = s at hs1
  have hpc : (∃ emb, s'.pc = .scStoreW emb) ∨ s'.pc = .upStoreW := by
    rcases hpc : s.pc <;> simp [lstep, hpc] at hs1 <;>
      (try obtain ⟨-, rfl⟩ := hs1) <;> simp
  have hEc : E[c] = .sc (.ack r) := by
    rcases hE : E[c] with ⟨q, o⟩ | ⟨q, rr⟩ | ⟨⟨q, y⟩ | q | q | ⟨q, W⟩⟩ <;>
      rw [hE] at hs2 hcp <;> simp only [Ev.proc, SCEv.proc] at hcp <;> subst hcp <;>
      rcases hpc with ⟨emb, hpc⟩ | hpc <;> simp [lstep, hpc] at hs2 <;> rfl
  have : c = b := by
    by_contra hne
    exact hno c hc1 (by omega) (.ack r) (by rw [List.getElem?_eq_getElem hcL, hEc]) rfl
  rw [← this, List.getElem?_eq_getElem hcL, hEc]

/-! ## Positions of operation instances -/

/-- The sequential-specification operation of an invocation. -/
def toOp (p : P) : HOp V → SnapOp P V
  | .scan => .scan
  | .update v => .update p v

lemma invG_hinv (p : P) (o : HOp V) : invG p (.hinv p o : Ev P V) = some (toOp p o) := by
  rcases o <;> simp [toOp]

lemma invG_eq_some {p : P} {e : Ev P V} {y : SnapOp P V} (h : invG p e = some y) :
    ∃ o, e = .hinv p o ∧ y = toOp p o := by
  rcases e with ⟨q, _ | v⟩ | ⟨q, r⟩ | c
  · by_cases hq : q = p
    · subst hq; simp at h; exact ⟨.scan, rfl, h.symm⟩
    · simp [invG, Ev.toLabel, Label.invOf, hq] at h
  · by_cases hq : q = p
    · subst hq; simp at h; exact ⟨.update v, rfl, h.symm⟩
    · simp [invG, Ev.toLabel, Label.invOf, hq] at h
  · simp at h
  · simp at h

lemma retG_eq_some {p : P} {e : Ev P V} {y : P → Option V} (h : retG p e = some y) :
    e = .hret p y := by
  rcases e with ⟨q, _ | v⟩ | ⟨q, r⟩ | c
  · simp at h
  · simp at h
  · by_cases hq : q = p
    · subst hq; simp at h; rw [h]
    · simp [retG, Ev.toLabel, Label.retOf, hq] at h
  · simp at h

variable (E) in
/-- The invocation of operation instance `x` is at position `k`. -/
def InvAt (x : OpId P) (k : ℕ) : Prop :=
  ∃ o, E[k]? = some (.hinv x.1 o) ∧ fIdx (invG x.1) E k = x.2

variable (E) in
/-- The response of operation instance `x` is at position `k`. -/
def RetAt (x : OpId P) (k : ℕ) : Prop :=
  ∃ r, E[k]? = some (.hret x.1 r) ∧ fIdx (retG x.1) E k = x.2

lemma InvAt.unique {x : OpId P} {k k' : ℕ} (h : InvAt E x k) (h' : InvAt E x k') : k = k' := by
  obtain ⟨o, h1, h2⟩ := h
  obtain ⟨o', h1', h2'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := fIdx_lt (invG x.1) h1 (invG_hinv _ _) hlt; omega
  · have := fIdx_lt (invG x.1) h1' (invG_hinv _ _) hlt; omega

lemma RetAt.unique {x : OpId P} {k k' : ℕ} (h : RetAt E x k) (h' : RetAt E x k') : k = k' := by
  obtain ⟨o, h1, h2⟩ := h
  obtain ⟨o', h1', h2'⟩ := h'
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := fIdx_lt (retG x.1) h1 (retG_hret _ _) hlt; omega
  · have := fIdx_lt (retG x.1) h1' (retG_hret _ _) hlt; omega

lemma invoked_iff {x : OpId P} : Invoked (hist E) x ↔ ∃ k, InvAt E x k := by
  unfold Invoked
  rw [opsOf_hist]
  constructor
  · intro h
    obtain ⟨k, a, h1, h2, h3⟩ := exists_of_getElem?_filterMap (invG x.1)
      (List.getElem?_eq_getElem h)
    obtain ⟨o, rfl, -⟩ := invG_eq_some h2
    exact ⟨k, o, h1, h3⟩
  · rintro ⟨k, o, h1, h2⟩
    have := getElem?_filterMap_fIdx (invG x.1) h1 (invG_hinv _ _)
    rw [h2] at this
    exact (List.getElem?_eq_some_iff.1 this).1

lemma opOf_of_invAt {x : OpId P} {k : ℕ} {o : HOp V} (hk : E[k]? = some (.hinv x.1 o))
    (hi : fIdx (invG x.1) E k = x.2) : opOf (hist E) x = some (toOp x.1 o) := by
  unfold opOf; rw [opsOf_hist, ← hi]
  exact getElem?_filterMap_fIdx (invG x.1) hk (invG_hinv _ _)

lemma completed_iff {x : OpId P} : Completed (hist E) x ↔ ∃ k, RetAt E x k := by
  unfold Completed
  rw [respsOf_hist]
  constructor
  · intro h
    obtain ⟨k, a, h1, h2, h3⟩ := exists_of_getElem?_filterMap (retG x.1)
      (List.getElem?_eq_getElem h)
    rw [retG_eq_some h2] at h1
    exact ⟨k, _, h1, h3⟩
  · rintro ⟨k, o, h1, h2⟩
    have := getElem?_filterMap_fIdx (retG x.1) h1 (retG_hret _ _)
    rw [h2] at this
    exact (List.getElem?_eq_some_iff.1 this).1

lemma respOf_of_retAt {x : OpId P} {k : ℕ} {r : P → Option V}
    (hk : E[k]? = some (.hret x.1 r)) (hi : fIdx (retG x.1) E k = x.2) :
    respOf (hist E) x = some r := by
  unfold respOf; rw [respsOf_hist, ← hi]
  exact getElem?_filterMap_fIdx (retG x.1) hk (retG_hret _ _)

/-- Real-time precedence in positions. -/
lemma precedes_pos {a b : OpId P} {ka kb : ℕ} (hP : Precedes (hist E) a b) (ha : RetAt E a ka)
    (hb : InvAt E b kb) : ka < kb := by
  obtain ⟨β, γ, hsplit, hc, hni⟩ := hP
  have hβ : β = (E.take β.length).map Ev.toLabel := by
    rw [List.map_take, ← hist, hsplit, List.take_left]
  unfold Completed at hc; unfold Invoked at hni
  rw [hβ] at hc hni
  have e1 : respsOf ((E.take β.length).map Ev.toLabel) a.1 = (E.take β.length).filterMap (retG a.1) :=
    respsOf_hist (E := E.take β.length) a.1
  have e2 : opsOf ((E.take β.length).map Ev.toLabel) b.1 = (E.take β.length).filterMap (invG b.1) :=
    opsOf_hist (E := E.take β.length) b.1
  rw [e1] at hc; rw [e2] at hni
  change a.2 < fIdx (retG a.1) E β.length at hc
  change ¬ b.2 < fIdx (invG b.1) E β.length at hni
  obtain ⟨r, ha1, ha2⟩ := ha
  obtain ⟨o, hb1, hb2⟩ := hb
  have h1 : ka < β.length := by
    by_contra h
    have := fIdx_mono (retG a.1) (l := E) (show β.length ≤ ka by omega)
    omega
  have h2 : β.length ≤ kb := by
    by_contra h
    have := fIdx_lt (invG b.1) hb1 (invG_hinv _ _) (show kb < β.length by omega)
    omega
  omega

lemma fIdx_eq_of_none {α β : Type} (f : α → Option β) {l : List α} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ m, a ≤ m → m < b → ∀ e, l[m]? = some e → f e = none) : fIdx f l a = fIdx f l b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [ih (by omega) (fun m h1 h2 => h m h1 (by omega)), ← Nat.add_assoc]
    rcases hm : l[a + k]? with _ | e
    · have : l.length ≤ a + k := by
        by_contra hc; simp [List.getElem?_eq_getElem (by omega : a + k < l.length)] at hm
      unfold fIdx
      rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
    · rw [fIdx_succ f hm, h (a + k) (by omega) (by omega) e hm]; rfl

/-- A node is idle when it invokes an operation. -/
lemma count_at_hinv (hrun : run pk E ≠ none) {h : ℕ} {p : P} {o : HOp V}
    (hh : E[h]? = some (.hinv p o)) : fIdx (invG p) E h = fIdx (retG p) E h := by
  have hL : h < E.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hh; cases hh
  have hE : E[h] = .hinv p o := by rw [List.getElem?_eq_getElem hL] at hh; exact Option.some.inj hh
  have hs := (cfgAt_step hrun hL).1
  rw [hE] at hs
  simp only [Ev.proc] at hs
  have hc := count_of_run pk h hL.le _ (run_cfgAt hrun hL.le) p
  have hidle : (cfgAt pk E h p).pc.isIdle = true := by
    generalize cfgAt pk E h p = s at hs
    rcases hpc : s.pc <;> rcases o <;> simp [lstep, hpc] at hs ⊢
  rw [hidle] at hc; simpa using hc

/-- The response at `k'` of operation `x` matches the invocation found by `RetFact`. -/
lemma invAt_of_retFact (hrun : run pk E ≠ none) {x : OpId P} {k' h : ℕ} {o : HOp V}
    (hk' : RetAt E x k') (hh : E[h]? = some (.hinv x.1 o)) (hlt : h < k')
    (hn : NoHIn E x.1 h k') : InvAt E x h := by
  refine ⟨o, hh, ?_⟩
  rw [count_at_hinv hrun hh]
  obtain ⟨r, hr1, hr2⟩ := hk'
  rw [← hr2]
  apply fIdx_eq_of_none _ hlt.le
  intro m hm1 hm2 e he
  rcases Nat.eq_or_lt_of_le hm1 with rfl | hm1
  · rw [hh] at he; cases he; simp
  · by_cases hp : e.proc = x.1
    · obtain ⟨c, rfl⟩ := hn m hm1 hm2 e he hp; simp
    · exact retG_eq_none_of_proc_ne hp

end Podc.StoreCollectChurn.Snap
