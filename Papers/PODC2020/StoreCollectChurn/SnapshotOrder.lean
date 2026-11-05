import Papers.PODC2020.StoreCollectChurn.SnapshotFacts

/-!
# Ordering scans and updates (Lemmas 11–13 of the paper)

Every completed scan `S` is certified by a successful double collect inside it (`GoodCD`); its
*vector* `vec S r` is the update sequence number of `r` in the certifying view.

* Lemma 11 (`vec_total`): the vectors of any two scans are comparable.
* Real-time order of scans is respected (`vec_mono_of_precedes`).
* Updates vs. scans (`k_le_vec_of_precedes`, `vec_lt_k_of_precedes`) and Lemma 13
  (`k_le_vec_of_precedes_upd`).
-/

namespace Podc.StoreCollectChurn.Snap

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {P V : Type} [DecidableEq P]

/-- Data of a double collect certifying a scan. -/
structure CD (P V : Type) where
  i₁ : ℕ
  j₁ : ℕ
  q₁ : P
  W₁ : SCView P V
  i₂ : ℕ
  j₂ : ℕ
  q₂ : P
  W₂ : SCView P V

variable (E : List (Ev P V))

open Classical in
/-- Position of the invocation of `x` (`0` if not invoked). -/
noncomputable def invPos (x : OpId P) : ℕ := if h : ∃ k, InvAt E x k then Nat.find h else 0

open Classical in
/-- Position of the response of `x` (`0` if not completed). -/
noncomputable def retPos (x : OpId P) : ℕ := if h : ∃ k, RetAt E x k then Nat.find h else 0

/-- A completed scan. -/
def ScanOK (x : OpId P) : Prop := Completed (hist E) x ∧ opOf (hist E) x = some .scan

/-- `d` certifies the response of the scan `x`. -/
def GoodCD (x : OpId P) (d : CD P V) : Prop :=
  ColE E d.i₁ d.j₁ d.q₁ d.W₁ ∧ ColE E d.i₂ d.j₂ d.q₂ d.W₂ ∧ invPos E x < d.i₁ ∧ d.j₁ < d.i₂ ∧
    d.j₂ < retPos E x ∧ (∀ r, rU d.W₁ r = rU d.W₂ r) ∧ respOf (hist E) x = some (rVal d.W₂)

open Classical in
/-- The vector (update sequence numbers) of a scan. -/
noncomputable def vec (x : OpId P) (r : P) : ℕ :=
  if h : ∃ d, GoodCD E x d then usq (h.choose.W₂ r) else 0

/-- `k U`: `U` is the `k U`-th update of its node. -/
noncomputable def kU (x : OpId P) : ℕ := updCnt E (invPos E x + 1) x.1

variable {E}

lemma invAt_invPos {x : OpId P} {k : ℕ} (h : InvAt E x k) : invPos E x = k := by
  classical
  have hex : ∃ k, InvAt E x k := ⟨k, h⟩
  simp only [invPos, dif_pos hex]
  exact (Nat.find_spec hex).unique h

lemma retAt_retPos {x : OpId P} {k : ℕ} (h : RetAt E x k) : retPos E x = k := by
  classical
  have hex : ∃ k, RetAt E x k := ⟨k, h⟩
  simp only [retPos, dif_pos hex]
  exact (Nat.find_spec hex).unique h

lemma InvAt.lt_length {x : OpId P} {k : ℕ} (h : InvAt E x k) : k < E.length := by
  obtain ⟨o, h1, -⟩ := h
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h1; cases h1

lemma RetAt.lt_length {x : OpId P} {k : ℕ} (h : RetAt E x k) : k < E.length := by
  obtain ⟨o, h1, -⟩ := h
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h1; cases h1

lemma InvAt.inj {x y : OpId P} {k : ℕ} (hx : InvAt E x k) (hy : InvAt E y k) : x = y := by
  obtain ⟨o, h1, h2⟩ := hx
  obtain ⟨o', h1', h2'⟩ := hy
  have e := Option.some.inj (h1.symm.trans h1')
  injection e with e1 e2
  exact Prod.ext e1 (by rw [← h2, ← h2', e1])

lemma RetAt.inj {x y : OpId P} {k : ℕ} (hx : RetAt E x k) (hy : RetAt E y k) : x = y := by
  obtain ⟨o, h1, h2⟩ := hx
  obtain ⟨o', h1', h2'⟩ := hy
  have e := Option.some.inj (h1.symm.trans h1')
  injection e with e1 e2
  exact Prod.ext e1 (by rw [← h2, ← h2', e1])

variable {pk : Pick P V} (hrun : run pk E ≠ none) (hreg : Regular (scSched E))
include hrun hreg

/-- The response of a completed operation, with the facts of `RetFact`. -/
lemma retFact_of_completed {x : OpId P} (hc : Completed (hist E) x) :
    ∃ h k' r, InvAt E x h ∧ RetAt E x k' ∧ h < k' ∧ E[k']? = some (.hret x.1 r) ∧
      respOf (hist E) x = some r ∧ NoHIn E x.1 h k' ∧
      ((E[h]? = some (.hinv x.1 .scan) ∧ Cert E r h k') ∨
       (∃ v, E[h]? = some (.hinv x.1 (.update v)) ∧ r = (fun _ => none) ∧
          ∃ a b y, h < a ∧ b < k' ∧ StE E a x.1 y ∧ NextE E a b ∧ y.usqno = updCnt E k' x.1)) := by
  obtain ⟨k', hk'⟩ := completed_iff.1 hc
  obtain ⟨r, hr1, hr2⟩ := hk'
  obtain ⟨h, hlt, hn, hor⟩ := (past hrun hreg).2 k' (RetAt.lt_length ⟨r, hr1, hr2⟩) x.1 r hr1
  have hh : ∃ o, E[h]? = some (.hinv x.1 o) := by
    rcases hor with ⟨h1, -⟩ | ⟨v, h1, -⟩
    · exact ⟨_, h1⟩
    · exact ⟨_, h1⟩
  obtain ⟨o, ho⟩ := hh
  exact ⟨h, k', r, invAt_of_retFact hrun ⟨r, hr1, hr2⟩ ho hlt hn, ⟨r, hr1, hr2⟩, hlt, hr1,
    respOf_of_retAt hr1 hr2, hn, hor⟩

lemma completed_invoked {x : OpId P} (hc : Completed (hist E) x) : Invoked (hist E) x := by
  obtain ⟨h, -, -, hi, -⟩ := retFact_of_completed hrun hreg hc
  exact invoked_iff.2 ⟨h, hi⟩

/-- A completed scan is certified by a double collect inside it. -/
lemma exists_goodCD {x : OpId P} (hx : ScanOK E x) : ∃ d, GoodCD E x d := by
  obtain ⟨h, k', r, hi, hk, hlt, -, hresp, -, hor⟩ := retFact_of_completed hrun hreg hx.1
  rcases hor with ⟨-, hcert⟩ | ⟨v, hv, -⟩
  · obtain ⟨i₁, j₁, q₁, W₁, i₂, j₂, q₂, W₂, h1, h2, h3, h4, h5, h6, h7⟩ := hcert
    refine ⟨⟨i₁, j₁, q₁, W₁, i₂, j₂, q₂, W₂⟩, h1, h2, ?_, h4, ?_, h6, ?_⟩
    · rw [invAt_invPos hi]; exact h3
    · rw [retAt_retPos hk]; exact h5
    · rw [hresp, h7]
  · obtain ⟨o, ho, ho2⟩ := hi
    rw [hv] at ho; cases ho
    have := hx.2
    rw [opOf_of_invAt hv ho2] at this
    cases this

lemma vec_spec {x : OpId P} (hx : ScanOK E x) :
    ∃ d, GoodCD E x d ∧ ∀ r, vec E x r = usq (d.W₁ r) ∧ vec E x r = usq (d.W₂ r) := by
  classical
  have hex := exists_goodCD hrun hreg hx
  refine ⟨hex.choose, hex.choose_spec, fun r => ?_⟩
  have hv : vec E x r = usq (hex.choose.W₂ r) := by simp only [vec, dif_pos hex]
  obtain ⟨h1, h2, -, -, -, h6, -⟩ := hex.choose_spec
  exact ⟨hv.trans (usq_eq_of_rU hrun hreg h1 h2 h6 r).symm, hv⟩

/-- **Lemma 11**: the vectors of two scans are comparable. -/
lemma vec_total {x y : OpId P} (hx : ScanOK E x) (hy : ScanOK E y) :
    vec E x ≤ vec E y ∨ vec E y ≤ vec E x := by
  obtain ⟨d, ⟨a1, b1, -, h1, -, -, -⟩, hd⟩ := vec_spec hrun hreg hx
  obtain ⟨e, ⟨a2, b2, -, h2, -, -, -⟩, he⟩ := vec_spec hrun hreg hy
  have hA1 := a1.2.2.1; have hA2 := a2.2.2.1
  rcases Nat.lt_or_ge d.j₁ e.i₂ with h | h
  · left; intro r
    rw [(hd r).1, (he r).2]; exact usq_le_of_before hrun hreg a1 b2 h r
  · right; intro r
    rw [(he r).1, (hd r).2]
    exact usq_le_of_before hrun hreg a2 b1 (by omega) r

/-- Real-time order of scans is respected by their vectors. -/
lemma vec_mono_of_precedes {x y : OpId P} (hx : ScanOK E x) (hy : ScanOK E y)
    (hp : Precedes (hist E) x y) : vec E x ≤ vec E y := by
  obtain ⟨d, ⟨-, b1, -, -, h5, -, -⟩, hd⟩ := vec_spec hrun hreg hx
  obtain ⟨e, ⟨a2, -, h3, -, -, -, -⟩, he⟩ := vec_spec hrun hreg hy
  obtain ⟨kx, hkx⟩ := completed_iff.1 hx.1
  obtain ⟨ky, hky⟩ := invoked_iff.1 (completed_invoked hrun hreg hy.1)
  have := precedes_pos hp hkx hky
  rw [retAt_retPos hkx] at h5; rw [invAt_invPos hky] at h3
  intro r
  rw [(hd r).2, (he r).1]
  exact usq_le_of_before hrun hreg b1 a2 (by omega) r

lemma kU_eq {x : OpId P} {h : ℕ} {v : V} (hi : InvAt E x h)
    (hh : E[h]? = some (.hinv x.1 (.update v))) : kU E x = updCnt E h x.1 + 1 := by
  rw [kU, invAt_invPos hi, updCnt_succ_of_some hh (v := v) (by simp [updOf])]

/-- An update `U` completed before a scan `S` starts is seen by `S`. -/
lemma kU_le_vec_of_precedes {u s : OpId P} (hu : Completed (hist E) u)
    (hu' : opOf (hist E) u ≠ some .scan) (hs : ScanOK E s)
    (hp : Precedes (hist E) u s) : kU E u ≤ vec E s u.1 := by
  obtain ⟨h, k', r, hi, hk, hlt, -, -, hn, hor⟩ := retFact_of_completed hrun hreg hu
  rcases hor with ⟨hsc, -⟩ | ⟨v, hv, -, a, b, y, hha, hbk, hst, hab, hy⟩
  · obtain ⟨o, -, ho⟩ := hi
    exact absurd (opOf_of_invAt hsc ho) hu'
  · obtain ⟨d, ⟨a1, -, h3, -, -, -, -⟩, hd⟩ := vec_spec hrun hreg hs
    obtain ⟨ks, hks⟩ := invoked_iff.1 (completed_invoked hrun hreg hs.1)
    have := precedes_pos hp hk hks
    rw [invAt_invPos hks] at h3
    rw [(hd u.1).1]
    have hk1 : kU E u = y.usqno := by
      rw [hy, kU, invAt_invPos hi, updCnt_eq_of_noHIn hlt hn]
    rw [hk1]
    exact usq_ge_of_storeDone hrun hreg hst hab (by omega) a1

/-- A scan completed before an update `U` starts does not see `U`. -/
lemma vec_lt_kU_of_precedes {s u : OpId P} {h : ℕ} {v : V} (hs : ScanOK E s) (hi : InvAt E u h)
    (hh : E[h]? = some (.hinv u.1 (.update v))) (hp : Precedes (hist E) s u) :
    vec E s u.1 < kU E u := by
  obtain ⟨d, ⟨-, b1, -, -, h5, -, -⟩, hd⟩ := vec_spec hrun hreg hs
  obtain ⟨ks, hks⟩ := completed_iff.1 hs.1
  have := precedes_pos hp hks hi
  rw [retAt_retPos hks] at h5
  obtain ⟨a, haj, hle⟩ := usq_le_updCnt hrun hreg (p := u.1) b1
  rw [(hd u.1).2, kU_eq hrun hreg hi hh]
  have := updCnt_mono (E := E) (p := u.1) (show a ≤ h by omega)
  omega

/-- **Lemma 13** (in terms of vectors): if `U_q` precedes `U_p` and a scan sees `U_p`, it sees
`U_q`. -/
lemma kU_le_vec_of_precedes_upd {q p s : OpId P} {hp : ℕ} {v : V} (hq : Completed (hist E) q)
    (hq' : opOf (hist E) q ≠ some .scan) (hpi : InvAt E p hp)
    (hpu : E[hp]? = some (.hinv p.1 (.update v))) (hs : ScanOK E s)
    (hP : Precedes (hist E) q p) (hk : kU E p ≤ vec E s p.1) : kU E q ≤ vec E s q.1 := by
  have hpast := past hrun hreg
  obtain ⟨d, ⟨a1, b1, -, h4, -, -, -⟩, hd⟩ := vec_spec hrun hreg hs
  rw [(hd p.1).1, kU_eq hrun hreg hpi hpu] at hk
  rcases hW : d.W₁ p.1 with _ | y
  · rw [hW] at hk; simp [usq] at hk
  rw [hW] at hk; simp only [usq] at hk
  obtain ⟨a', ha'j, ha', -⟩ := reg1_some hreg a1 hW
  have ha'L : a' < E.length := by
    by_contra h'; rw [StE, List.getElem?_eq_none (by omega)] at ha'; cases ha'
  have hcnt := (hpast.1 a' ha'L p.1 y ha').le_cnt
  have hpa' : hp < a' := by
    by_contra hc
    have := updCnt_mono (E := E) (p := p.1) (show a' ≤ hp by omega)
    omega
  obtain ⟨h, k', r, hi, hk', hlt, -, -, hn, hor⟩ := retFact_of_completed hrun hreg hq
  rcases hor with ⟨hsc, -⟩ | ⟨w, hw, -, a, b, x, hha, hbk, hst, hab, hx⟩
  · obtain ⟨o, -, ho⟩ := hi
    exact absurd (opOf_of_invAt hsc ho) hq'
  have := precedes_pos hP hk' hpi
  rw [(hd q.1).2]
  have hk1 : kU E q = x.usqno := by
    rw [hx, kU, invAt_invPos hi, updCnt_eq_of_noHIn hlt hn]
  rw [hk1]
  have := a1.2.2.1
  exact usq_ge_of_storeDone hrun hreg hst hab (by omega) b1

end Podc.StoreCollectChurn.Snap
