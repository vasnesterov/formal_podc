import Papers.PODC2013.TMObservationalRefinement.Opacity

/-!
# Traces, transactional actions and observational equivalence (Sections 4–5)

* `Act T O M C`: actions (Definition 11): interface actions `iface t k` and primitive commands
  `cmd t c`, `c : C`.
* `history τ`: the projection of a trace onto interface actions.
* `ann st τ`: every action of `τ` annotated with whether it is *transactional* in the sense of
  Section 4 (`trans`/`nontrans`), when the trace is executed after a prefix whose per-thread
  "inside a transaction" status is `st`. `trans_flag_iff` shows the flag coincides with the
  paper's definition.
* `ObsEq τ τ'` (`τ ∼ τ'`, Definition 15).
* `WFTraceLit` (Definition 12 as printed) and `WFTrace` (Definition 12 with the "inside a
  transaction" condition read per thread, and with the repaired Definition 2).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind

/-- Classification of primitive commands: `thr c = t` and `glob c = false` means
`c ∈ LPcomm_t`; `glob c = true` means `c ∈ GPcomm_t`. -/
class CmdClass (T : outParam Type) (C : Type) where
  thr : C → T
  glob : C → Bool

/-- Actions (Definition 11). -/
inductive Act (T O M C : Type) where
  | iface (t : T) (k : IKind O M)
  | cmd (t : T) (c : C)

variable {T O M C : Type}

namespace Act

/-- The thread performing an action. -/
def thread : Act T O M C → T
  | iface t _ => t
  | cmd t _ => t

/-- The interface action, if any. -/
def toI : Act T O M C → Option (IAct T O M)
  | iface t k => some (t, k)
  | cmd _ _ => none

/-- `committed`/`aborted` action (of any thread). -/
def isEndA : Act T O M C → Bool
  | iface _ k => k.isEnd
  | cmd _ _ => false

/-- `txbegin`/`committed`/`aborted` action. -/
def isBoundA : Act T O M C → Bool
  | iface _ k => k.isBound
  | cmd _ _ => false

@[simp] lemma thread_iface (t : T) (k : IKind O M) : (iface t k : Act T O M C).thread = t := rfl
@[simp] lemma thread_cmd (t : T) (c : C) : (cmd t c : Act T O M C).thread = t := rfl
@[simp] lemma toI_iface (t : T) (k : IKind O M) : (iface t k : Act T O M C).toI = some (t, k) := rfl
@[simp] lemma toI_cmd (t : T) (c : C) : (cmd t c : Act T O M C).toI = none := rfl

end Act

open Act

/-- `history τ`: projection of a trace onto interface actions. -/
def history (τ : List (Act T O M C)) : List (IAct T O M) := τ.filterMap Act.toI

/-- `τ|t`. -/
def tproj [DecidableEq T] (t : T) (τ : List (Act T O M C)) : List (Act T O M C) :=
  τ.filter (fun a => a.thread = t)

@[simp] lemma history_nil : history ([] : List (Act T O M C)) = [] := rfl
@[simp] lemma history_append (τ τ' : List (Act T O M C)) :
    history (τ ++ τ') = history τ ++ history τ' := by simp [history]
@[simp] lemma history_cons_iface (t : T) (k : IKind O M) (τ : List (Act T O M C)) :
    history (iface t k :: τ) = (t, k) :: history τ := by simp [history]
@[simp] lemma history_cons_cmd (t : T) (c : C) (τ : List (Act T O M C)) :
    history (cmd t c :: τ) = history τ := by simp [history, List.filterMap_cons, Act.toI]

lemma toI_thread {a : Act T O M C} {x : IAct T O M} (h : a.toI = some x) : x.1 = a.thread := by
  cases a <;> simp [Act.toI] at h; subst h; rfl

section dec
variable [DecidableEq T]

lemma history_filter (p : T → Bool) (τ : List (Act T O M C)) :
    history (τ.filter (fun a => p a.thread)) = (history τ).filter (fun x => p x.1) := by
  induction τ with
  | nil => rfl
  | cons a τ ih =>
    cases a with
    | iface t k => by_cases h : p t <;> simp [List.filter_cons, h, ih]
    | cmd t c => by_cases h : p t <;> simp [List.filter_cons, h, ih]

lemma proj_history' (t : T) (τ : List (Act T O M C)) :
    proj t (history τ) = (history (tproj t τ)).map Prod.snd := by
  simp only [proj, tproj]
  rw [history_filter (fun u => decide (u = t))]

lemma proj_history (t : T) (τ : List (Act T O M C)) :
    proj t (history τ) = proj t (history (tproj t τ)) := by
  simp only [proj, tproj]
  rw [history_filter (fun u => decide (u = t))]
  simp [List.filter_filter]

/-! ### Transactional status -/

/-- Update of the per-thread "inside a transaction" status by one action. -/
def upd (st : T → Bool) : Act T O M C → T → Bool
  | iface t txbegin => Function.update st t true
  | iface t committed => Function.update st t false
  | iface t aborted => Function.update st t false
  | _ => st

/-- The status after a trace. -/
def stAfter (st : T → Bool) (τ : List (Act T O M C)) : T → Bool := τ.foldl upd st

/-- Is the action transactional, given the status `st` before it. -/
def flag (st : T → Bool) (a : Act T O M C) : Bool := a.isBoundA || st a.thread

/-- Annotate every action with its "transactional" flag. -/
def ann (st : T → Bool) : List (Act T O M C) → List (Act T O M C × Bool)
  | [] => []
  | a :: l => (a, flag st a) :: ann (upd st a) l

/-- `nontrans` of a trace, executed after a prefix with status `st`. -/
def nontransFrom (st : T → Bool) (τ : List (Act T O M C)) : List (Act T O M C) :=
  ((ann st τ).filter (fun p => !p.2)).map Prod.fst

/-- `trans` of a trace, executed after a prefix with status `st`. -/
def transFrom (st : T → Bool) (τ : List (Act T O M C)) : List (Act T O M C) :=
  ((ann st τ).filter (fun p => p.2)).map Prod.fst

/-- `nontrans(τ)` (Section 4). -/
def nontrans (τ : List (Act T O M C)) : List (Act T O M C) := nontransFrom (fun _ => false) τ

/-- `trans(τ)` (Section 4). -/
def trans (τ : List (Act T O M C)) : List (Act T O M C) := transFrom (fun _ => false) τ

/-- **Definition 15**: observational equivalence `τ ∼ τ'`. -/
def ObsEq (τ τ' : List (Act T O M C)) : Prop :=
  (∀ t, tproj t τ = tproj t τ') ∧ nontrans τ = nontrans τ'

lemma ObsEq.refl (τ : List (Act T O M C)) : ObsEq τ τ := ⟨fun _ => rfl, rfl⟩
lemma ObsEq.symm {τ τ' : List (Act T O M C)} (h : ObsEq τ τ') : ObsEq τ' τ :=
  ⟨fun t => (h.1 t).symm, h.2.symm⟩
lemma ObsEq.trans {τ τ' τ'' : List (Act T O M C)} (h : ObsEq τ τ') (h' : ObsEq τ' τ'') :
    ObsEq τ τ'' := ⟨fun t => (h.1 t).trans (h'.1 t), h.2.trans h'.2⟩

@[simp] lemma ann_nil (st : T → Bool) : ann st ([] : List (Act T O M C)) = [] := rfl
@[simp] lemma ann_cons (st : T → Bool) (a : Act T O M C) (l : List (Act T O M C)) :
    ann st (a :: l) = (a, flag st a) :: ann (upd st a) l := rfl

lemma ann_append (st : T → Bool) (l l' : List (Act T O M C)) :
    ann st (l ++ l') = ann st l ++ ann (stAfter st l) l' := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih => simp [ih, stAfter]

@[simp] lemma stAfter_nil (st : T → Bool) : stAfter st ([] : List (Act T O M C)) = st := rfl
@[simp] lemma stAfter_cons (st : T → Bool) (a : Act T O M C) (l : List (Act T O M C)) :
    stAfter st (a :: l) = stAfter (upd st a) l := rfl
lemma stAfter_append (st : T → Bool) (l l' : List (Act T O M C)) :
    stAfter st (l ++ l') = stAfter (stAfter st l) l' := by simp [stAfter, List.foldl_append]

@[simp] lemma map_fst_ann (st : T → Bool) (l : List (Act T O M C)) :
    (ann st l).map Prod.fst = l := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih => simp [ih]

lemma upd_apply_of_ne (st : T → Bool) (a : Act T O M C) {t : T} (h : a.thread ≠ t) :
    upd st a t = st t := by
  have h' : t ≠ a.thread := Ne.symm h
  unfold upd
  split <;> simp_all [Function.update_apply]

lemma upd_congr {st st' : T → Bool} (a : Act T O M C) {t : T} (h : st t = st' t) :
    upd st a t = upd st' a t := by
  unfold upd
  split <;> simp_all [Function.update_apply]

lemma flag_congr {st st' : T → Bool} (a : Act T O M C) (h : st a.thread = st' a.thread) :
    flag st a = flag st' a := by simp [flag, h]

lemma ann_congr {st st' : T → Bool} {t : T} (l : List (Act T O M C))
    (hl : ∀ a ∈ l, a.thread = t) (h : st t = st' t) : ann st l = ann st' l := by
  induction l generalizing st st' with
  | nil => rfl
  | cons a l ih =>
    have ha := hl a (by simp)
    simp only [ann_cons]
    rw [flag_congr (st' := st') a (ha ▸ h), ih (fun b hb => hl b (by simp [hb])) (upd_congr a h)]

lemma stAfter_congr {st st' : T → Bool} {t : T} (l : List (Act T O M C))
    (h : st t = st' t) : stAfter st l t = stAfter st' l t := by
  induction l generalizing st st' with
  | nil => exact h
  | cons a l ih => exact ih (upd_congr a h)

lemma stAfter_tproj (st : T → Bool) (t : T) (l : List (Act T O M C)) :
    stAfter st (tproj t l) t = stAfter st l t := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a.thread = t
    · simp [tproj, List.filter_cons, ha] at ih ⊢; exact ih _
    · simp only [tproj, List.filter_cons, ha, decide_false, Bool.false_eq_true, ite_false,
        stAfter_cons] at ih ⊢
      rw [ih]; exact (stAfter_congr l (upd_apply_of_ne st a ha)).symm

/-- Annotations commute with per-thread projection. -/
lemma ann_tproj (st : T → Bool) (t : T) (l : List (Act T O M C)) :
    (ann st l).filter (fun p => p.1.thread = t) = ann st (tproj t l) := by
  induction l generalizing st with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : a.thread = t
    · simp [tproj, List.filter_cons, ha] at ih ⊢; exact ih _
    · simp only [ann_cons, List.filter_cons, ha, decide_false, Bool.false_eq_true, ite_false,
        tproj] at ih ⊢
      rw [ih]
      exact ann_congr _ (fun b hb => by simp at hb; exact hb.2) (upd_apply_of_ne st a ha)

/-- Annotated lists are determined by their actions and their per-thread projections. -/
lemma annList_ext : ∀ (L L' : List (Act T O M C × Bool)), L.map Prod.fst = L'.map Prod.fst →
    (∀ t, L.filter (fun p => p.1.thread = t) = L'.filter (fun p => p.1.thread = t)) → L = L'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | (a, b) :: L, (a', b') :: L', h, hp => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    have hb : b = b' := by
      have := hp a.thread; simp [List.filter_cons] at this; exact this.1
    subst hb
    congr 1
    refine annList_ext L L' h (fun t => ?_)
    have := hp t
    by_cases ht : a.thread = t <;> simp_all [List.filter_cons]

/-- If `Y` has the same per-thread projections as `X`, its annotation is any annotated list
with actions `Y` and the per-thread projections of `ann st X`. -/
lemma ann_eq_of_perThread (st : T → Bool) (X : List (Act T O M C)) (L' : List (Act T O M C × Bool))
    (hp : ∀ t, L'.filter (fun p => p.1.thread = t) = (ann st X).filter (fun p => p.1.thread = t)) :
    ann st (L'.map Prod.fst) = L' := by
  apply annList_ext _ _ (by simp)
  intro t
  rw [ann_tproj, hp, ann_tproj]
  congr 1
  have e := congrArg (List.map Prod.fst) (hp t)
  conv_rhs => rw [← map_fst_ann st X]
  simp only [tproj, List.filter_map]
  exact e

lemma tproj_append (t : T) (l l' : List (Act T O M C)) :
    tproj t (l ++ l') = tproj t l ++ tproj t l' := by simp [tproj]

lemma nontrans_append (pre τ : List (Act T O M C)) :
    nontrans (pre ++ τ) = nontrans pre ++ nontransFrom (stAfter (fun _ => false) pre) τ := by
  simp [nontrans, nontransFrom, ann_append]

/-- `ObsEq` of two extensions of a common prefix. -/
lemma obsEq_append_of (pre X Y : List (Act T O M C)) (hp : ∀ t, tproj t X = tproj t Y)
    (hn : nontransFrom (stAfter (fun _ => false) pre) X =
      nontransFrom (stAfter (fun _ => false) pre) Y) : ObsEq (pre ++ X) (pre ++ Y) :=
  ⟨fun t => by rw [tproj_append, tproj_append, hp], by rw [nontrans_append, nontrans_append, hn]⟩

/-! ### The flag agrees with the paper's definition of transactional actions -/

/-- `OpenIn t L`: `L = L₁ (t, txbegin) L₂` where `L₂` has no `committed`/`aborted` actions. -/
def OpenIn (t : T) (L : List (Act T O M C)) : Prop :=
  ∃ L₁ L₂, L = L₁ ++ iface t txbegin :: L₂ ∧ ∀ a ∈ L₂, a.isEndA = false

lemma openIn_iff (t : T) (L : List (Act T O M C)) (hL : ∀ a ∈ L, a.thread = t) :
    OpenIn t L ↔ stAfter (fun _ => false) L t = true := by
  induction L using List.reverseRecOn with
  | nil => simp [OpenIn]
  | append_singleton L a ih =>
    have ih := ih (fun b hb => hL b (by simp [hb]))
    have ha : a.thread = t := hL a (by simp)
    rw [stAfter_append]
    simp only [stAfter_cons, stAfter_nil]
    constructor
    · rintro ⟨L₁, L₂, h, h2⟩
      rcases List.eq_nil_or_concat L₂ with rfl | ⟨L₂', b, rfl⟩
      · rw [List.append_singleton_inj] at h; obtain ⟨-, rfl⟩ := h; simp [upd]
      · have h' : L ++ [a] = (L₁ ++ iface t txbegin :: L₂') ++ [b] := by simp [h]
        rw [List.append_singleton_inj] at h'
        obtain ⟨rfl, rfl⟩ := h'
        have hst := ih.mp ⟨L₁, L₂', rfl, fun c hc => h2 c (by simp [hc])⟩
        have hb := h2 a (by simp)
        cases a with
        | cmd u c => simpa [upd] using hst
        | iface u k =>
          simp at ha; subst ha
          cases k <;> simp_all [upd, Act.isEndA, isEnd]
    · intro h
      cases a with
      | cmd u c =>
        obtain ⟨L₁, L₂, rfl, h2⟩ := ih.mpr (by simpa [upd] using h)
        exact ⟨L₁, L₂ ++ [cmd u c], by simp, by
          intro b hb; simp at hb; rcases hb with hb | rfl; exacts [h2 b hb, rfl]⟩
      | iface u k =>
        simp at ha; subst ha
        by_cases hk : k = txbegin
        · subst hk; exact ⟨L, [], rfl, by simp⟩
        by_cases he : k.isEnd = true
        · cases k <;> simp_all [isEnd, upd]
        · have h' : stAfter (fun _ => false) L u = true := by cases k <;> simp_all [upd, isEnd]
          obtain ⟨L₁, L₂, rfl, h2⟩ := ih.mpr h'
          refine ⟨L₁, L₂ ++ [iface u k], by simp, ?_⟩
          intro b hb; simp at hb; rcases hb with hb | rfl
          · exact h2 b hb
          · simpa [Act.isEndA] using he

/-- The flag computed by `ann` is the paper's notion of a transactional action: for
`τ = τ₁ φ τ₂`, the action `φ = (t, _)` is transactional iff it is a `txbegin`, `committed` or
`aborted` action, or `τ₁|t = τ₁' (t, txbegin) τ₁''` with no `committed`/`aborted` in `τ₁''`. -/
theorem trans_flag_iff (τ₁ : List (Act T O M C)) (φ : Act T O M C) :
    flag (stAfter (fun _ => false) τ₁) φ = true ↔
      φ.isBoundA = true ∨ OpenIn φ.thread (tproj φ.thread τ₁) := by
  rw [openIn_iff _ _ (fun a ha => by simp [tproj] at ha; exact ha.2), stAfter_tproj]
  simp [flag]

lemma mem_ann_iff (st : T → Bool) (l : List (Act T O M C)) (x : Act T O M C) (f : Bool) :
    (x, f) ∈ ann st l ↔ ∃ l₁ l₂, l = l₁ ++ x :: l₂ ∧ f = flag (stAfter st l₁) x := by
  induction l generalizing st with
  | nil => simp
  | cons a l ih =>
    simp only [ann_cons, List.mem_cons, Prod.mk.injEq, ih]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨l₁, l₂, rfl, rfl⟩)
      · exact ⟨[], l, rfl, rfl⟩
      · exact ⟨a :: l₁, l₂, rfl, rfl⟩
    · rintro ⟨l₁, l₂, h, rfl⟩
      rcases l₁ with _ | ⟨b, l₁⟩
      · simp at h; obtain ⟨rfl, rfl⟩ := h; left; simp
      · simp at h; obtain ⟨rfl, rfl⟩ := h; right; exact ⟨l₁, l₂, rfl, rfl⟩

/-! ### Well-formed traces (Definition 12) -/

variable [CmdClass T C]

/-- **Definition 12, as printed.** The third condition says: if `τ = τ₁ (t, c) τ₂` with
`c ∈ GPcomm_t`, then `τ₁` is not of the form `τ₁' (t, txbegin) τ₁''` with `τ₁''` free of
`committed`/`aborted` actions (of any thread). -/
def WFTraceLit (τ : List (Act T O M C)) : Prop :=
  WellFormedLit (history τ) ∧ (∀ t c, cmd t c ∈ τ → CmdClass.thr c = t) ∧
  ∀ τ₁ t c τ₂, τ = τ₁ ++ cmd t c :: τ₂ → CmdClass.glob c = true → ¬ OpenIn t τ₁

/-- **Definition 12, repaired**: the history is well-formed in the repaired sense of
Definition 2, and the third condition looks at the actions of thread `t` only (`τ₁|t`). -/
def WFTrace (τ : List (Act T O M C)) : Prop :=
  WellFormed (history τ) ∧ (∀ t c, cmd t c ∈ τ → CmdClass.thr c = t) ∧
  ∀ τ₁ t c τ₂, τ = τ₁ ++ cmd t c :: τ₂ → CmdClass.glob c = true → ¬ OpenIn t (tproj t τ₁)

/-- The third condition of `WFTrace`, stated with the flag. -/
lemma WFTrace.glob_nontrans {τ τ₁ τ₂ : List (Act T O M C)} {t : T} {c : C} (h : WFTrace τ)
    (he : τ = τ₁ ++ cmd t c :: τ₂) (hg : CmdClass.glob c = true) :
    stAfter (fun _ => false) τ₁ t = false := by
  have := h.2.2 τ₁ t c τ₂ he hg
  rw [openIn_iff _ _ (fun a ha => by simp [tproj] at ha; exact ha.2), stAfter_tproj] at this
  simpa using this

lemma tproj_eq_append_cons {t : T} {τ L₁ L₂ : List (Act T O M C)} {x : Act T O M C}
    (h : tproj t τ = L₁ ++ x :: L₂) :
    ∃ τ₁ τ₂, τ = τ₁ ++ x :: τ₂ ∧ tproj t τ₁ = L₁ ∧ tproj t τ₂ = L₂ := by
  simp only [tproj] at h
  obtain ⟨τ₁, τ₂', rfl, h1, h2⟩ := List.filter_eq_append_iff.mp h
  obtain ⟨τ₃, τ₂, rfl, h3, h4, h5⟩ := List.filter_eq_cons_iff.mp h2
  refine ⟨τ₁ ++ τ₃, τ₂, by simp, ?_, h5⟩
  simp only [tproj, List.filter_append, h1]
  rw [List.filter_eq_nil_iff.mpr h3]; simp

/-- Well-formedness only depends on the per-thread projections. -/
lemma WFTrace.of_tproj {τ τ' : List (Act T O M C)} (h : WFTrace τ)
    (hp : ∀ t, tproj t τ = tproj t τ') : WFTrace τ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun t => ?_, fun t c hc => ?_, fun τ₁ t c τ₂ he hg => ?_⟩
  · rw [proj_history, ← hp, ← proj_history]; exact h1 t
  · apply h2
    have : cmd t c ∈ tproj t τ' := by simp [tproj, hc]
    rw [← hp] at this; simp [tproj] at this; exact this
  · have e : tproj t τ = tproj t τ₁ ++ cmd t c :: tproj t τ₂ := by
      rw [hp, he, tproj_append]; simp [tproj]
    obtain ⟨σ₁, σ₂, rfl, e1, -⟩ := tproj_eq_append_cons e
    rw [← e1]; exact h3 σ₁ t c σ₂ rfl hg

lemma WFTrace.toLit_history {τ : List (Act T O M C)} (h : WFTrace τ) : WellFormedLit (history τ) :=
  h.1.toLit

/-! ### Status facts from well-formedness -/

open TState

lemma stAfter_eq_inside (t : T) : ∀ (L : List (Act T O M C)) (st : T → Bool) (q q' : TState O M),
    (∀ a ∈ L, a.thread = t) → st t = q.inside →
    run q ((history L).map Prod.snd) = some q' → stAfter st L t = q'.inside
  | [], st, q, q', _, hs, hr => by simp at hr; subst hr; exact hs
  | a :: L, st, q, q', hL, hs, hr => by
    have ha := hL a (by simp)
    cases a with
    | cmd u c =>
      simp only [history_cons_cmd, stAfter_cons] at hr ⊢
      exact stAfter_eq_inside t L _ q q' (fun b hb => hL b (by simp [hb])) (by simpa [upd]) hr
    | iface u k =>
      simp at ha; subst ha
      simp only [history_cons_iface, List.map_cons, run_cons] at hr
      obtain ⟨q₁, hq₁, hr⟩ := Option.bind_eq_some_iff.mp hr
      refine stAfter_eq_inside u L _ q₁ q' (fun b hb => hL b (by simp [hb])) ?_ hr
      rcases step_eq_some.mp hq₁ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
        ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, hk, rfl⟩ <;>
        simp_all [upd, inside]
      rcases hk with rfl | rfl <;> simp [upd, inside]

/-- In a well-formed trace, before an interface action `(t, k)` thread `t` is inside a
transaction iff `k ≠ txbegin`. -/
lemma WFTrace.st_before_iface {τ₁ τ₂ : List (Act T O M C)} {t : T} {k : IKind O M}
    (h : WFTrace (τ₁ ++ iface t k :: τ₂)) :
    stAfter (fun _ => false) τ₁ t = !k.isTxbegin := by
  have hw := (wellFormed_iff_run _).mp h.1 t
  have e : proj t (history (τ₁ ++ iface t k :: τ₂)) =
      (history (tproj t τ₁)).map Prod.snd ++ k :: (history (tproj t τ₂)).map Prod.snd := by
    rw [proj_history', tproj_append]; simp [tproj]
  rw [e, run_append] at hw
  obtain ⟨q, hq⟩ : ∃ q, run idle ((history (tproj t τ₁)).map Prod.snd) = some q := by
    cases hh : run idle ((history (tproj t τ₁)).map Prod.snd) with
    | none => simp [hh] at hw
    | some q => exact ⟨q, rfl⟩
  rw [hq] at hw
  simp only [Option.bind_some, run_cons] at hw
  have hs : (step q k).isSome := by
    cases hh : step q k with
    | none => simp [hh] at hw
    | some _ => rfl
  rw [← stAfter_tproj, stAfter_eq_inside t _ _ idle q (fun a ha => by simp [tproj] at ha; exact ha.2)
    rfl hq]
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.mp hs
  rcases step_eq_some.mp hq' with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨o, f, n, rfl, rfl, rfl⟩ | ⟨o, f, rfl, rfl, rfl⟩ | ⟨rfl, hk | hk, rfl⟩ <;>
    (try subst hk) <;> simp [inside, isTxbegin]

/-- In a well-formed trace, every interface action is transactional. -/
lemma WFTrace.flag_iface {τ₁ τ₂ : List (Act T O M C)} {t : T} {k : IKind O M}
    (h : WFTrace (τ₁ ++ iface t k :: τ₂)) :
    flag (stAfter (fun _ => false) τ₁) (iface t k : Act T O M C) = true := by
  have := h.st_before_iface
  cases k <;> simp_all [flag, Act.isBoundA, isBound, isTxbegin]

/-- In a well-formed trace, global commands are not transactional. -/
lemma WFTrace.flag_glob {τ₁ τ₂ : List (Act T O M C)} {t : T} {c : C}
    (h : WFTrace (τ₁ ++ cmd t c :: τ₂)) (hg : CmdClass.glob c = true) :
    flag (stAfter (fun _ => false) τ₁) (cmd t c : Act T O M C) = false := by
  simp [flag, Act.isBoundA, h.glob_nontrans rfl hg]

end dec

end Podc.TMObservationalRefinement
