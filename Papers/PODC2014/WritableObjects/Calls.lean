import Papers.PODC2014.WritableObjects.Ptr
import Mathlib.Order.WithBot

/-!
# Calls of a transcript following the template

* the events following an invocation on `A[i]` (`IsCtrl.next_*`, `IsCtrl.low_ret`);
* *anchors*: a `Write` call is identified by its `A[f].SWrite` invocation `a` and its write `w`
  to `Ptr` (`WAnchor α a w`);
* the point `t*` of condition (C) for every `Exec` (`CPt`, `tsOf`);
* the *timestamp key* `keyPos α a` of an invocation on a base object (the paper's `TS(M)` of the
  enclosing call `M`, or `⊤` if `M` is not matured).
-/

set_option linter.unusedSectionVars false

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {P ι : Type} {T : ObjSpec} {W : Writable T} {owner : ι → P}
  {α : List (Ev P ι T)} {σ : P → ℕ → PSt ι T}

lemma Ev.toLow_eq_inv [DecidableEq ι] {ev : Ev P ι T} {i : ι} {p : P} {o : T.Op}
    (h : ev.toLow W i = some (.inv p o)) :
    (∃ v, ev = .swinv p i v ∧ o = W.wr v) ∨ ev = .opinv p i o := by
  cases ev with
  | swinv q j v => simp only [Ev.toLow] at h; split_ifs at h with hj; cases h; subst hj; simp
  | opinv q j o' => simp only [Ev.toLow] at h; split_ifs at h with hj; cases h; subst hj; simp
  | _ => simp [Ev.toLow] at h

lemma Ev.toLow_eq_ret [DecidableEq ι] {ev : Ev P ι T} {i : ι} {p : P} {r : T.Resp}
    (h : ev.toLow W i = some (.ret p r)) : ev = .aret p i r := by
  cases ev with
  | aret q j r' => simp only [Ev.toLow] at h; split_ifs at h with hj; cases h; subst hj; rfl
  | swinv q j v => simp only [Ev.toLow] at h; split_ifs at h <;> simp at h
  | opinv q j o' => simp only [Ev.toLow] at h; split_ifs at h <;> simp at h
  | _ => simp [Ev.toLow] at h

lemma Ev.toHigh_eq_inv {ev : Ev P ι T} {p : P} {o : T.Op} (h : ev.toHigh W = some (.inv p o)) :
    (∃ v, ev = .winv p v ∧ o = W.wr v) ∨ ev = .einv p o := by
  cases ev <;> simp only [Ev.toHigh, reduceCtorEq, Option.some.injEq, Label.inv.injEq] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp

lemma Ev.toHigh_eq_ret {ev : Ev P ι T} {p : P} {r : T.Resp} (h : ev.toHigh W = some (.ret p r)) :
    ev = .hret p r := by
  cases ev <;> simp only [Ev.toHigh, reduceCtorEq, Option.some.injEq, Label.ret.injEq] at h
  obtain ⟨rfl, rfl⟩ := h; rfl

namespace IsCtrl

variable (h : IsCtrl W owner α σ)
include h

lemma next_wSW {p : P} {x k : ℕ} {v : T.State} {f : ι} (hs : σ p (x + 1) = .wSW v f)
    (hk : k < α.length) (hxk : x < k) (hp : α[k].proc = p) :
    ∃ b, x < b ∧ b ≤ k ∧ Quiet α p x b ∧ (∃ r, α[b]? = some (.aret p f r)) ∧
      σ p (b + 1) = .wPtr v f := by
  obtain ⟨b, hxb, hbk, hb, hq, hs'⟩ := h.next hk hxk hp
  rw [hs] at hs'
  generalize hev : α[b] = ev at hs'
  generalize hsb : σ p (b + 1) = s' at hs'
  cases hs' with
  | swret _ _ r => exact ⟨b, hxb, hbk, hq, ⟨r, by simp [List.getElem?_eq_getElem hb, hev]⟩, hsb⟩

lemma next_wPtr {p : P} {x k : ℕ} {v : T.State} {f : ι} (hs : σ p (x + 1) = .wPtr v f)
    (hk : k < α.length) (hxk : x < k) (hp : α[k].proc = p) :
    ∃ b, x < b ∧ b ≤ k ∧ Quiet α p x b ∧ α[b]? = some (.ptr p f) ∧
      σ p (b + 1) = .wEnd v := by
  obtain ⟨b, hxb, hbk, hb, hq, hs'⟩ := h.next hk hxk hp
  rw [hs] at hs'
  generalize hev : α[b] = ev at hs'
  generalize hsb : σ p (b + 1) = s' at hs'
  cases hs' with
  | ptr => exact ⟨b, hxb, hbk, hq, by simp [List.getElem?_eq_getElem hb, hev], hsb⟩

lemma next_eOp {p : P} {x k : ℕ} {i : ι} (hs : σ p (x + 1) = .eOp i)
    (hk : k < α.length) (hxk : x < k) (hp : α[k].proc = p) :
    ∃ b, x < b ∧ b ≤ k ∧ Quiet α p x b ∧ ∃ r, α[b]? = some (.aret p i r) ∧
      σ p (b + 1) = .eEnd r := by
  obtain ⟨b, hxb, hbk, hb, hq, hs'⟩ := h.next hk hxk hp
  rw [hs] at hs'
  generalize hev : α[b] = ev at hs'
  generalize hsb : σ p (b + 1) = s' at hs'
  cases hs' with
  | opret _ r => exact ⟨b, hxb, hbk, hq, r, by simp [List.getElem?_eq_getElem hb, hev], hsb⟩

end IsCtrl

variable [DecidableEq P] [DecidableEq ι]

/-- `α[a]` is an invocation by `p` of an operation on `A[i]`. -/
def LowInvAt (α : List (Ev P ι T)) (i : ι) (p : P) (a : ℕ) : Prop :=
  (∃ v, α[a]? = some (.swinv p i v)) ∨ (∃ o, α[a]? = some (.opinv p i o))

lemma lowInvAt_of_isInv {i : ι} {y : OpId P} {a : ℕ} (hy : IsInv (Ev.toLow W i) α y a) :
    LowInvAt α i y.1 a := by
  obtain ⟨ha, o, h1, -⟩ := hy
  rcases Ev.toLow_eq_inv h1 with ⟨v, h2, -⟩ | h2
  · exact Or.inl ⟨v, by rw [List.getElem?_eq_getElem ha, h2]⟩
  · exact Or.inr ⟨o, by rw [List.getElem?_eq_getElem ha, h2]⟩

namespace IsCtrl

variable (h : IsCtrl W owner α σ)
include h

lemma lowCnt_of_lowInvAt {i : ι} {p : P} {a : ℕ} (ha : LowInvAt α i p a) :
    (σ p (a + 1)).lowAt = some i := by
  rcases ha with ⟨v, ha⟩ | ⟨o, ha⟩
  · rw [(h.swinv_facts ha).2.2.1]; rfl
  · rw [(h.opinv_facts ha).2.1]; rfl

/-- The response of an operation on `A[i]` invoked at `a`: the next event of the process is
the response, and it is the response of the same instance of the history of `A[i]`. -/
lemma low_ret {i : ι} {y : OpId P} {a k : ℕ} (hy : IsInv (Ev.toLow W i) α y a)
    (hk : k < α.length) (hak : a < k) (hp : α[k].proc = y.1) :
    ∃ b, a < b ∧ b ≤ k ∧ Quiet α y.1 a b ∧ (∃ r, α[b]? = some (.aret y.1 i r)) ∧
      IsRet (Ev.toLow W i) α y b := by
  have hlow := lowInvAt_of_isInv hy
  have hσ := h.lowCnt_of_lowInvAt hlow
  have hex : ∃ b, a < b ∧ b ≤ k ∧ Quiet α y.1 a b ∧ ∃ r, α[b]? = some (.aret y.1 i r) := by
    rcases hlow with ⟨v, ha⟩ | ⟨o, ha⟩
    · obtain ⟨b, h1, h2, h3, h4, -⟩ := h.next_wSW (h.swinv_facts ha).2.2.1 hk hak hp
      exact ⟨b, h1, h2, h3, h4⟩
    · obtain ⟨b, h1, h2, h3, r, h4, -⟩ := h.next_eOp (h.opinv_facts ha).2.1 hk hak hp
      exact ⟨b, h1, h2, h3, r, h4⟩
  obtain ⟨b, hab, hbk, hq, r, hb⟩ := hex
  refine ⟨b, hab, hbk, hq, ⟨r, hb⟩, ?_⟩
  obtain ⟨hb', hev⟩ := getElem_of_getElem? hb
  refine ⟨hb', r, by simp [hev, Ev.toLow], ?_⟩
  have hc := h.count_low i y.1 (t := b) (by omega)
  have hconst : σ y.1 b = σ y.1 (a + 1) :=
    h.const (by omega) (by omega) (fun j hj j1 j2 => hq j hj (by omega) j2)
  rw [hconst] at hc
  simp only [PSt.lowCnt, hσ, ite_true] at hc
  have h1 := opsOf_take_eq (Ev.toLow W i) α y.1 (s := a + 1) (t := b) (by omega) (by omega)
    (fun j hj j1 j2 => Ev.toLow_invOf_of_ne (hq j hj (by omega) j2))
  obtain ⟨ha', o, hinv, hcnt⟩ := hy
  rw [opsOf_take_succ_of_inv _ ha' hinv] at h1
  omega

end IsCtrl

/-! ## Anchors of `Write` calls -/

/-- `a` is the invocation of `A[f].SWrite(v)` and `w` the subsequent `Ptr.Write(f)` of the same
`Write` call (with the response of the `SWrite` in between). -/
def WAnchor (α : List (Ev P ι T)) (a w : ℕ) : Prop :=
  ∃ p i v, α[a]? = some (.swinv p i v) ∧ α[w]? = some (.ptr p i) ∧
    ∃ b, a < b ∧ b < w ∧ (∃ r, α[b]? = some (.aret p i r)) ∧ Quiet α p a b ∧ Quiet α p b w

lemma WAnchor.lt {a w : ℕ} (h : WAnchor α a w) : a < w := by
  obtain ⟨p, i, v, -, -, b, h1, h2, -⟩ := h; omega

lemma WAnchor.unique_left {a a' w : ℕ} (h : WAnchor α a w) (h' : WAnchor α a' w) : a = a' := by
  obtain ⟨p, i, v, ha, hw, b, hab, hbw, ⟨r, hb⟩, hq1, hq2⟩ := h
  obtain ⟨p', i', v', ha', hw', b', hab', hbw', ⟨r', hb'⟩, hq1', hq2'⟩ := h'
  rw [hw] at hw'
  simp only [Option.some.injEq, Ev.ptr.injEq] at hw'
  obtain ⟨rfl, rfl⟩ := hw'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨hl, he⟩ := getElem_of_getElem? ha'
    have : a' ≠ b := by rintro rfl; rw [hb] at ha'; simp at ha'
    by_cases hab2 : a' < b
    · exact hq1 a' hl hlt hab2 (by rw [he]; rfl)
    · exact hq2 a' hl (by omega) (by omega) (by rw [he]; rfl)
  · obtain ⟨hl, he⟩ := getElem_of_getElem? ha
    have : a ≠ b' := by rintro rfl; rw [hb'] at ha; simp at ha
    by_cases hab2 : a < b'
    · exact hq1' a hl hlt hab2 (by rw [he]; rfl)
    · exact hq2' a hl (by omega) (by omega) (by rw [he]; rfl)

lemma WAnchor.unique_right {a w w' : ℕ} (h : WAnchor α a w) (h' : WAnchor α a w') : w = w' := by
  obtain ⟨p, i, v, ha, hw, b, hab, hbw, ⟨r, hb⟩, hq1, hq2⟩ := h
  obtain ⟨p', i', v', ha', hw', b', hab', hbw', ⟨r', hb'⟩, hq1', hq2'⟩ := h'
  rw [ha] at ha'
  simp only [Option.some.injEq, Ev.swinv.injEq] at ha'
  obtain ⟨rfl, rfl, rfl⟩ := ha'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · obtain ⟨hl, he⟩ := getElem_of_getElem? hw
    have : w ≠ b' := by rintro rfl; rw [hb'] at hw; simp at hw
    by_cases h2 : w < b'
    · exact hq1' w hl (by omega) h2 (by rw [he]; rfl)
    · exact hq2' w hl (by omega) hlt (by rw [he]; rfl)
  · obtain ⟨hl, he⟩ := getElem_of_getElem? hw'
    have : w' ≠ b := by rintro rfl; rw [hb] at hw'; simp at hw'
    by_cases h2 : w' < b
    · exact hq1 w' hl (by omega) h2 (by rw [he]; rfl)
    · exact hq2 w' hl (by omega) hlt (by rw [he]; rfl)

namespace IsCtrl

variable (h : IsCtrl W owner α σ)
include h

/-- Every write to `Ptr` is the anchor of a `Write` call. -/
lemma exists_anchor_of_ptr {w : ℕ} {p : P} {f : ι} (hw : α[w]? = some (.ptr p f)) :
    ∃ a, WAnchor α a w := by
  obtain ⟨v, -, -, b, hbw, ⟨r, hb⟩, hq2, a, hab, ha, hq1⟩ := h.ptr_facts hw
  exact ⟨a, p, f, v, ha, hw, b, hab, hbw, ⟨r, hb⟩, hq1, hq2⟩

/-- If the owner of a `SWrite` invoked at `a` writes `Ptr` later, then the `Write` call of `a`
has an anchor, which comes no later. -/
lemma exists_anchor_of_later_ptr {a k : ℕ} {p : P} {i j : ι} {v : T.State}
    (ha : α[a]? = some (.swinv p i v)) (hk : α[k]? = some (.ptr p j)) (hak : a < k) :
    ∃ w ≤ k, WAnchor α a w := by
  obtain ⟨hk', hkev⟩ := getElem_of_getElem? hk
  have hkp : α[k].proc = p := by rw [hkev]; rfl
  obtain ⟨b, hab, hbk, hq1, ⟨r, hb⟩, hσb⟩ :=
    h.next_wSW (h.swinv_facts ha).2.2.1 hk' hak hkp
  have hbk' : b < k := by
    rcases Nat.lt_or_eq_of_le hbk with h1 | rfl
    · exact h1
    · rw [hb] at hk; simp at hk
  obtain ⟨w, hbw, hwk, hq2, hw, -⟩ := h.next_wPtr hσb hk' hbk' hkp
  exact ⟨w, hwk, p, i, v, ha, hw, b, hab, hbw, ⟨r, hb⟩, hq1, hq2⟩

/-- Only the owner of `i` writes `i` to `Ptr`. -/
lemma owner_of_ptr {w : ℕ} {p : P} {f : ι} (hw : α[w]? = some (.ptr p f)) : owner f = p := by
  obtain ⟨v, -, -, b, -, -, -, a, -, ha, -⟩ := h.ptr_facts hw
  exact (h.swinv_facts ha).1

end IsCtrl

/-! ## The point `t*` of condition (C) -/

/-- `ts` is a point `t*` of condition (C) for the `Exec` call whose `Oper` is invoked at `t`. -/
def CPt (α : List (Ev P ι T)) (t ts : ℕ) : Prop :=
  ∃ q i o e o', α[t]? = some (.opinv q i o) ∧ α[e]? = some (.einv q o') ∧ Quiet α q e t ∧
    e < ts ∧ ts ≤ t ∧ ptrAt α ts = some i ∧
    ∀ a p v, α[a]? = some (.swinv p i v) →
      (∃ b r, a < b ∧ b < ts ∧ α[b]? = some (.aret p i r)) ∨
      (∃ c r, t < c ∧ c < a ∧ α[c]? = some (.aret q i r))

lemma IsCtrl.exists_cpt (h : IsCtrl W owner α σ) (hC : CondC α) {t : ℕ} {q : P} {i : ι}
    {o : T.Op} (ht : α[t]? = some (.opinv q i o)) : ∃ ts, CPt α t ts := by
  obtain ⟨-, -, -, e, het, he, hq⟩ := h.opinv_facts ht
  obtain ⟨ts, h1, h2, h3, h4⟩ := hC e t q o o i het he ht (fun k hk k1 k2 => hq k hk k1 k2)
  exact ⟨ts, q, i, o, e, o, ht, he, hq, h1, h2, h3, h4⟩

open Classical in
/-- A chosen point `t*` of condition (C) (the paper takes the latest one; any one works). -/
noncomputable def tsOf (α : List (Ev P ι T)) (t : ℕ) : ℕ :=
  if h : ∃ ts, CPt α t ts then h.choose else 0

lemma cpt_tsOf {t : ℕ} (h : ∃ ts, CPt α t ts) : CPt α t (tsOf α t) := by
  classical
  rw [tsOf, dite_cond_eq_true (eq_true h)]
  exact h.choose_spec

lemma tsOf_le (α : List (Ev P ι T)) (t : ℕ) : tsOf α t ≤ t := by
  classical
  unfold tsOf
  split_ifs with h
  · obtain ⟨-, -, -, -, -, -, -, -, -, h2, -⟩ := h.choose_spec
    exact h2
  · exact Nat.zero_le _

/-- Unpacking `CPt` at a known `Oper` invocation. -/
lemma CPt.facts {t ts : ℕ} {q : P} {i : ι} {o : T.Op} (h : CPt α t ts)
    (ht : α[t]? = some (.opinv q i o)) :
    (∃ e o', α[e]? = some (.einv q o') ∧ Quiet α q e t ∧ e < ts) ∧ ts ≤ t ∧
      ptrAt α ts = some i ∧
      ∀ a p v, α[a]? = some (.swinv p i v) →
        (∃ b r, a < b ∧ b < ts ∧ α[b]? = some (.aret p i r)) ∨
        (∃ c r, t < c ∧ c < a ∧ α[c]? = some (.aret q i r)) := by
  obtain ⟨q', i', o', e, o'', ht', he, hq, h1, h2, h3, h4⟩ := h
  rw [ht] at ht'
  simp only [Option.some.injEq, Ev.opinv.injEq] at ht'
  obtain ⟨rfl, rfl, rfl⟩ := ht'
  exact ⟨⟨e, o'', he, hq, h1⟩, h2, h3, h4⟩

/-! ## Timestamp keys -/

open Classical in
/-- The timestamp key of an invocation on a base object at position `a`: for `A[i].Oper` the
timestamp `TS_Ptr(t*)` of the chosen point of condition (C); for `A[f].SWrite` the timestamp of
the subsequent write to `Ptr`, or `⊤` if there is none (the `Write` call is not matured). -/
noncomputable def keyPos (α : List (Ev P ι T)) (a : ℕ) : WithTop ℕ :=
  if ∃ q i o, α[a]? = some (.opinv q i o) then (nptr α (tsOf α a) : WithTop ℕ)
  else if h : ∃ w, WAnchor α a w then (nptr α (h.choose + 1) : WithTop ℕ) else ⊤

lemma keyPos_opinv {t : ℕ} {q : P} {i : ι} {o : T.Op} (ht : α[t]? = some (.opinv q i o)) :
    keyPos α t = nptr α (tsOf α t) := by
  classical
  rw [keyPos, if_pos ⟨q, i, o, ht⟩]

lemma keyPos_anchor {a w : ℕ} (hw : WAnchor α a w) : keyPos α a = nptr α (w + 1) := by
  classical
  have hno : ¬ ∃ q i o, α[a]? = some (.opinv q i o) := by
    rintro ⟨q, i, o, h⟩
    obtain ⟨p, i', v, ha, -⟩ := hw
    rw [ha] at h; simp at h
  rw [keyPos, if_neg hno, dif_pos ⟨w, hw⟩]
  have := (Exists.choose_spec (p := fun w => WAnchor α a w) ⟨w, hw⟩).unique_right hw
  rw [this]

lemma keyPos_top {a : ℕ} {p : P} {i : ι} {v : T.State} (ha : α[a]? = some (.swinv p i v))
    (hno : ¬ ∃ w, WAnchor α a w) : keyPos α a = ⊤ := by
  classical
  have hno' : ¬ ∃ q i o, α[a]? = some (.opinv q i o) := by
    rintro ⟨q, i, o, h⟩; rw [ha] at h; simp at h
  rw [keyPos, if_neg hno', dif_neg hno]

end Podc.WritableObjects
