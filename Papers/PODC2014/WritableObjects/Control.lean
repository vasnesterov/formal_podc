import Papers.PODC2014.WritableObjects.Defs
import Papers.PODC2014.WritableObjects.Proj

/-!
# Consequences of the template's control automaton

Facts about transcripts following the template (Figure 4.4), derived from the per-process control
states `σ p t` of `Template.ctrl`: what precedes and follows each kind of event of a process,
and the counting invariants relating invocations and responses in the high-level history and in
the histories of the base objects `A[i]`.
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

variable {P ι : Type} {T : ObjSpec} (W : Writable T) (owner : ι → P)

/-- `σ` are control states witnessing that every process of `α` follows the template. -/
def IsCtrl (α : List (Ev P ι T)) (σ : P → ℕ → PSt ι T) : Prop :=
  ∀ p, σ p 0 = .idle ∧ ∀ t (ht : t < α.length),
      (α[t].proc = p → PStep W owner p (σ p t) α[t] (σ p (t + 1))) ∧
      (α[t].proc ≠ p → σ p (t + 1) = σ p t)

/-- No event of `p` strictly between positions `x` and `y`. -/
def Quiet (α : List (Ev P ι T)) (p : P) (x y : ℕ) : Prop :=
  ∀ k (hk : k < α.length), x < k → k < y → α[k].proc ≠ p

/-- The base object on which a process in control state `s` has a pending operation. -/
def PSt.lowAt : PSt ι T → Option ι
  | .wSW _ f => some f
  | .eOp i => some i
  | _ => none

variable {W owner} {α : List (Ev P ι T)} {σ : P → ℕ → PSt ι T}

namespace IsCtrl

lemma step (h : IsCtrl W owner α σ) {t : ℕ} (ht : t < α.length) {p : P} (hp : α[t].proc = p) :
    PStep W owner p (σ p t) α[t] (σ p (t + 1)) := ((h p).2 t ht).1 hp

lemma step_other (h : IsCtrl W owner α σ) {t : ℕ} (ht : t < α.length) {p : P}
    (hp : α[t].proc ≠ p) : σ p (t + 1) = σ p t := ((h p).2 t ht).2 hp

/-- Control states do not change without events of the process. -/
lemma const (h : IsCtrl W owner α σ) {p : P} {s t : ℕ} (hst : s ≤ t) (ht : t ≤ α.length)
    (hq : ∀ k (hk : k < α.length), s ≤ k → k < t → α[k].proc ≠ p) : σ p t = σ p s := by
  induction t, hst using Nat.le_induction with
  | base => rfl
  | succ t hst ih =>
    rw [h.step_other (by omega) (hq t (by omega) hst (by omega))]
    exact ih (by omega) (fun k hk h1 h2 => hq k hk h1 (by omega))

/-- The last event of `p` before a point where `p` is not idle. -/
lemma last (h : IsCtrl W owner α σ) {p : P} {t : ℕ} (ht : t ≤ α.length) (hne : σ p t ≠ .idle) :
    ∃ e < t, ∃ he : e < α.length, α[e].proc = p ∧ Quiet α p e t ∧ σ p t = σ p (e + 1) := by
  induction t with
  | zero => exact absurd (h p).1 hne
  | succ t ih =>
    by_cases hp : (α[t]'(by omega)).proc = p
    · exact ⟨t, by omega, by omega, hp, fun k hk h1 h2 => by omega, rfl⟩
    · rw [h.step_other (by omega) hp] at hne ⊢
      obtain ⟨e, he, he', h1, h2, h3⟩ := ih (by omega) hne
      refine ⟨e, by omega, he', h1, fun k hk k1 k2 => ?_, h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 k2 with k2 | rfl
      · exact h2 k hk k1 k2
      · exact hp

/-- The first event of `p` after position `x` (if `p` has some event after `x`). -/
lemma _root_.Podc.WritableObjects.first_after {p : P} {x k : ℕ} (hk : k < α.length) (hxk : x < k)
    (hp : α[k].proc = p) :
    ∃ b, x < b ∧ b ≤ k ∧ ∃ hb : b < α.length, α[b].proc = p ∧ Quiet α p x b := by
  classical
  have hex : ∃ b, x < b ∧ ∃ hb : b < α.length, α[b].proc = p := ⟨k, hxk, hk, hp⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hxk, hk, hp⟩,
    (Nat.find_spec hex).2.1, (Nat.find_spec hex).2.2, fun j hj j1 j2 hj' => ?_⟩
  exact Nat.find_min hex j2 ⟨j1, hj, hj'⟩

end IsCtrl

lemma getElem_of_getElem? {α : List (Ev P ι T)} {t : ℕ} {ev : Ev P ι T} (h : α[t]? = some ev) :
    ∃ ht : t < α.length, α[t] = ev := by
  have ht : t < α.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h
  exact ⟨ht, by rw [List.getElem?_eq_getElem ht] at h; exact Option.some.inj h⟩

lemma PStep.proc_eq {p : P} {s s' : PSt ι T} {ev : Ev P ι T} (h : PStep W owner p s ev s') :
    ev.proc = p := by
  cases h <;> rfl

lemma PStep.target_ne_idle_of_ne_hret {p : P} {s s' : PSt ι T} {ev : Ev P ι T}
    (h : PStep W owner p s ev s') (hev : ∀ r, ev ≠ .hret p r) : s' ≠ .idle := by
  cases h <;> first | exact (hev _ rfl).elim | (intro h; cases h)

/-- Whether a process in control state `s` has a pending operation on `WT`. -/
def PSt.busy : PSt ι T → ℕ
  | .idle => 0
  | _ => 1

/-- Whether a process in control state `s` has a pending operation on `A[i]`. -/
def PSt.lowCnt [DecidableEq ι] (i : ι) (s : PSt ι T) : ℕ :=
  if s.lowAt = some i then 1 else 0

lemma Ev.toHigh_invOf_of_ne [DecidableEq P] {ev : Ev P ι T} {p : P} (h : ev.proc ≠ p) :
    (ev.toHigh W).bind (Label.invOf p) = none := by
  cases ev <;> simp_all [Ev.toHigh, Ev.proc]

lemma Ev.toHigh_retOf_of_ne [DecidableEq P] {ev : Ev P ι T} {p : P} (h : ev.proc ≠ p) :
    (ev.toHigh W).bind (Label.retOf p) = none := by
  cases ev <;> simp_all [Ev.toHigh, Ev.proc]

lemma Ev.toLow_invOf_of_ne [DecidableEq P] [DecidableEq ι] {ev : Ev P ι T} {p : P} {i : ι}
    (h : ev.proc ≠ p) : (ev.toLow W i).bind (Label.invOf p) = none := by
  cases ev <;> simp_all [Ev.toLow, Ev.proc]

lemma Ev.toLow_retOf_of_ne [DecidableEq P] [DecidableEq ι] {ev : Ev P ι T} {p : P} {i : ι}
    (h : ev.proc ≠ p) : (ev.toLow W i).bind (Label.retOf p) = none := by
  cases ev <;> simp_all [Ev.toLow, Ev.proc]

namespace IsCtrl

variable (h : IsCtrl W owner α σ)
include h

/-- The last event of `p` before a non-idle point, as a step of the automaton. -/
lemma prev {p : P} {t : ℕ} (ht : t ≤ α.length) (hne : σ p t ≠ .idle) :
    ∃ e < t, ∃ he : e < α.length, Quiet α p e t ∧ PStep W owner p (σ p e) α[e] (σ p t) := by
  obtain ⟨e, he, he', h1, h2, h3⟩ := h.last ht hne
  exact ⟨e, he, he', h2, h3 ▸ h.step he' h1⟩

/-- The next event of `p` after position `x` (if any), as a step of the automaton. -/
lemma next {p : P} {x k : ℕ} (hk : k < α.length) (hxk : x < k) (hp : α[k].proc = p) :
    ∃ b, x < b ∧ b ≤ k ∧ ∃ hb : b < α.length, Quiet α p x b ∧
      PStep W owner p (σ p (x + 1)) α[b] (σ p (b + 1)) := by
  obtain ⟨b, hxb, hbk, hb, h1, h2⟩ := first_after hk hxk hp
  refine ⟨b, hxb, hbk, hb, h2, ?_⟩
  have := h.const (p := p) (s := x + 1) (t := b) (by omega) (by omega)
    (fun j hj j1 j2 => h2 j hj (by omega) j2)
  rw [← this]
  exact h.step hb h1

/-- Facts at `A[f].SWrite(v)` (invoked at `a` by `p`): `p` owns `f` and the previous event of
`p` is the invocation of `Write(v)`. -/
lemma swinv_facts {a : ℕ} {p : P} {f : ι} {v : T.State} (ha : α[a]? = some (.swinv p f v)) :
    owner f = p ∧ σ p a = .wBeg v ∧ σ p (a + 1) = .wSW v f ∧
      ∃ e < a, α[e]? = some (.winv p v) ∧ Quiet α p e a := by
  obtain ⟨ha', hev⟩ := getElem_of_getElem? ha
  have hs := h.step ha' (p := p) (by rw [hev]; rfl)
  rw [hev] at hs
  generalize hsa : σ p a = sa at hs
  generalize hsa' : σ p (a + 1) = sa' at hs
  cases hs with
  | swinv _ _ hf =>
    refine ⟨hf, rfl, rfl, ?_⟩
    obtain ⟨e, he, he', h2, hs'⟩ := h.prev (t := a) (p := p) (by omega) (by rw [hsa]; simp)
    refine ⟨e, he, ?_, h2⟩
    rw [hsa] at hs'
    generalize hev' : α[e] = ev at hs'
    generalize σ p e = se at hs'
    cases hs'
    simp [List.getElem?_eq_getElem he', hev']

/-- Facts at `A[i].Oper(o)` (invoked at `t` by `q`): the previous event of `q` is the invocation
of `Exec(o)`, and `o` is not a write. -/
lemma opinv_facts {t : ℕ} {q : P} {i : ι} {o : T.Op} (ht : α[t]? = some (.opinv q i o)) :
    σ q t = .eBeg o ∧ σ q (t + 1) = .eOp i ∧ (∀ v, o ≠ W.wr v) ∧
      ∃ e < t, α[e]? = some (.einv q o) ∧ Quiet α q e t := by
  obtain ⟨ht', hev⟩ := getElem_of_getElem? ht
  have hs := h.step ht' (p := q) (by rw [hev]; rfl)
  rw [hev] at hs
  generalize hsa : σ q t = sa at hs
  generalize hsa' : σ q (t + 1) = sa' at hs
  cases hs with
  | opinv =>
    obtain ⟨e, he, he', h2, hs'⟩ := h.prev (t := t) (p := q) (by omega) (by rw [hsa]; simp)
    rw [hsa] at hs'
    generalize hev' : α[e] = ev at hs'
    generalize σ q e = se at hs'
    cases hs' with
    | einv _ ho =>
      exact ⟨rfl, rfl, ho, e, he, by simp [List.getElem?_eq_getElem he', hev'], h2⟩

/-- Facts at `Ptr.Write(f)` (at `w` by `p`): the previous events of `p` are `A[f].SWrite(v)`
(at `a`) and its response (at `b`). -/
lemma ptr_facts {w : ℕ} {p : P} {f : ι} (hw : α[w]? = some (.ptr p f)) :
    ∃ v, σ p w = .wPtr v f ∧ σ p (w + 1) = .wEnd v ∧
      ∃ b < w, (∃ r, α[b]? = some (.aret p f r)) ∧ Quiet α p b w ∧
        ∃ a < b, α[a]? = some (.swinv p f v) ∧ Quiet α p a b := by
  obtain ⟨hw', hev⟩ := getElem_of_getElem? hw
  have hs := h.step hw' (p := p) (by rw [hev]; rfl)
  rw [hev] at hs
  generalize hsa : σ p w = sa at hs
  generalize hsa' : σ p (w + 1) = sa' at hs
  cases hs with
  | ptr v =>
    refine ⟨v, rfl, rfl, ?_⟩
    obtain ⟨b, hb, hb', h2, hs'⟩ := h.prev (t := w) (p := p) (by omega) (by rw [hsa]; simp)
    rw [hsa] at hs'
    generalize hev' : α[b] = ev at hs'
    generalize hsb : σ p b = sb at hs'
    cases hs' with
    | swret _ _ r =>
      refine ⟨b, hb, ⟨r, by simp [List.getElem?_eq_getElem hb', hev']⟩, h2, ?_⟩
      obtain ⟨a, ha, ha', h3, hs''⟩ := h.prev (t := b) (p := p) (by omega) (by rw [hsb]; simp)
      rw [hsb] at hs''
      generalize hev'' : α[a] = ev at hs''
      generalize σ p a = sa at hs''
      cases hs''
      exact ⟨a, ha, by simp [List.getElem?_eq_getElem ha', hev''], h3⟩

/-- Facts at a response of `WT` (at `r` by `p`). -/
lemma hret_facts {r : ℕ} {p : P} {v : T.Resp} (hr : α[r]? = some (.hret p v)) :
    σ p (r + 1) = .idle ∧
    ((∃ v₀, σ p r = .wEnd v₀ ∧ v = W.wresp v₀ ∧
        ∃ w < r, ∃ f, α[w]? = some (.ptr p f) ∧ Quiet α p w r) ∨
      (σ p r = .eEnd v ∧ ∃ c < r, ∃ i, α[c]? = some (.aret p i v) ∧ Quiet α p c r ∧
        σ p c = .eOp i)) := by
  obtain ⟨hr', hev⟩ := getElem_of_getElem? hr
  have hs := h.step hr' (p := p) (by rw [hev]; rfl)
  rw [hev] at hs
  generalize hsa : σ p r = sa at hs
  generalize hsa' : σ p (r + 1) = sa' at hs
  cases hs with
  | wret v₀ =>
    refine ⟨rfl, Or.inl ⟨v₀, rfl, rfl, ?_⟩⟩
    obtain ⟨w, hw, hw', h2, hs'⟩ := h.prev (t := r) (p := p) (by omega) (by rw [hsa]; simp)
    rw [hsa] at hs'
    generalize hev' : α[w] = ev at hs'
    generalize σ p w = sw at hs'
    cases hs' with
    | ptr _ f => exact ⟨w, hw, f, by simp [List.getElem?_eq_getElem hw', hev'], h2⟩
  | eret =>
    refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    obtain ⟨c, hc, hc', h2, hs'⟩ := h.prev (t := r) (p := p) (by omega) (by rw [hsa]; simp)
    rw [hsa] at hs'
    generalize hev' : α[c] = ev at hs'
    generalize hsc : σ p c = sc at hs'
    cases hs' with
    | opret i => exact ⟨c, hc, i, by simp [List.getElem?_eq_getElem hc', hev'], h2, hsc⟩

variable [DecidableEq P]

/-- Counting invariant of the high-level history: a process has one more invocation than
responses iff it is not idle. -/
lemma count_high (p : P) {t : ℕ} (ht : t ≤ α.length) :
    (opsOf ((α.take t).filterMap (Ev.toHigh W)) p).length =
      (respsOf ((α.take t).filterMap (Ev.toHigh W)) p).length + (σ p t).busy := by
  induction t with
  | zero => simp [(h p).1, PSt.busy]
  | succ t ih =>
    have ht' : t < α.length := by omega
    have ih := ih (by omega)
    rw [filterMap_take_succ _ α ht', opsOf_append, respsOf_append, List.length_append,
      List.length_append, opsOf_toList, respsOf_toList]
    by_cases hp : α[t].proc = p
    · have hs := h.step ht' hp
      generalize α[t] = ev at hs ⊢
      generalize σ p t = st at hs ih
      generalize σ p (t + 1) = st' at hs ⊢
      cases hs <;> simp [Ev.toHigh, PSt.busy] at ih ⊢ <;> omega
    · rw [h.step_other ht' hp, Ev.toHigh_invOf_of_ne hp, Ev.toHigh_retOf_of_ne hp]
      simpa using ih

/-- Counting invariant of the history of `A[i]`. -/
lemma count_low [DecidableEq ι] (i : ι) (p : P) {t : ℕ} (ht : t ≤ α.length) :
    (opsOf ((α.take t).filterMap (Ev.toLow W i)) p).length =
      (respsOf ((α.take t).filterMap (Ev.toLow W i)) p).length + (σ p t).lowCnt i := by
  induction t with
  | zero => simp [(h p).1, PSt.lowCnt, PSt.lowAt]
  | succ t ih =>
    have ht' : t < α.length := by omega
    have ih := ih (by omega)
    rw [filterMap_take_succ _ α ht', opsOf_append, respsOf_append, List.length_append,
      List.length_append, opsOf_toList, respsOf_toList]
    by_cases hp : α[t].proc = p
    · have hs := h.step ht' hp
      generalize α[t] = ev at hs ⊢
      generalize σ p t = st at hs ih
      generalize σ p (t + 1) = st' at hs ⊢
      cases hs <;> simp [Ev.toLow, PSt.lowCnt, PSt.lowAt] at ih ⊢ <;>
        first | omega | (split_ifs at ih ⊢ <;> simp_all)
    · rw [h.step_other ht' hp, Ev.toLow_invOf_of_ne hp, Ev.toLow_retOf_of_ne hp]
      simpa using ih

end IsCtrl

end Podc.WritableObjects
