import Papers.PODC2013.TMObservationalRefinement.Rearrangement

/-!
# Programming language semantics (Sections 2 and 4) and Lemma 18

* `Lang`: the parameters of the language: primitive commands `C` with their classes
  (`LPcomm_t`/`GPcomm_t`) and semantics, which may only depend on and change the variables the
  class allows (`sem_lifted`, Section 4), Boolean/integer expressions over local variables, and the
  primitive commands the paper assumes to exist: `assume(b)`, `assume(e = n)` and assignments
  (`x := n`, `g := x`, `x := g`).
* `eval` (Section 4, "Trace evaluation"), `prop_23`.
* `lemma_18`: observationally equivalent well-formed traces evaluate to the same set of states
  (for the repaired Definition 12); `lemma_18_false_literal`: false for Definition 12 as printed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Podc.TMObservationalRefinement

open IKind Act

/-- Program variables: global variables `inl g` and local variables `inr (t, x)` of thread `t`. -/
abbrev Var (T LV GV : Type) := GV ⊕ (T × LV)

/-- Program states. -/
abbrev State (T LV GV : Type) := Var T LV GV → ℤ

variable {T LV GV : Type}

/-- The variables a command of class `(t, g)` may access: the locals of `t`, and the globals if
`g = true`. -/
def accessible (t : T) (g : Bool) : Var T LV GV → Prop
  | .inl _ => g = true
  | .inr (u, _) => u = t

/-- `R` is the lifting to full states of a nondeterministic transformer of the variables in `A`
(Section 4, "Semantics of primitive commands"). -/
def LiftedFrom (A : Var T LV GV → Prop) (R : State T LV GV → Set (State T LV GV)) : Prop :=
  ∃ f : ((v : Subtype A) → ℤ) → Set ((v : Subtype A) → ℤ),
    ∀ s s', s' ∈ R s ↔ (∀ v, ¬ A v → s' v = s v) ∧ (fun v => s' v.1) ∈ f (fun v => s v.1)

/-- The local variables of thread `t` in state `s`. -/
def locals (s : State T LV GV) (t : T) : LV → ℤ := fun x => s (.inr (t, x))

open Classical in
/-- The language parameters. -/
class Lang (T LV GV BE IE : outParam Type) (C : Type) extends CmdClass T C where
  /-- `[[c]]`, lifted to full states. -/
  sem : C → State T LV GV → Set (State T LV GV)
  /-- Commands only access the variables allowed by their class. -/
  sem_lifted : ∀ c, LiftedFrom (accessible (thr c) (glob c)) (sem c)
  /-- Boolean expressions over local variables. -/
  bval : BE → (LV → ℤ) → Bool
  /-- Integer expressions over local variables. -/
  ival : IE → (LV → ℤ) → ℤ
  /-- Integer constants. -/
  cst : ℤ → IE
  ival_cst : ∀ n q, ival (cst n) q = n
  /-- `assume(b)` (`true`) and `assume(¬b)` (`false`) of thread `t`. -/
  assume : T → BE → Bool → C
  /-- `assume(e = n)`. -/
  assumeEq : T → IE → ℤ → C
  /-- `x := n`. -/
  assign : T → LV → ℤ → C
  /-- `g := x`. -/
  setG : T → GV → LV → C
  /-- `x := g`. -/
  getG : T → LV → GV → C
  thr_assume : ∀ t b p, thr (assume t b p) = t
  thr_assumeEq : ∀ t e n, thr (assumeEq t e n) = t
  thr_assign : ∀ t x n, thr (assign t x n) = t
  thr_setG : ∀ t g x, thr (setG t g x) = t
  thr_getG : ∀ t x g, thr (getG t x g) = t
  glob_assume : ∀ t b p, glob (assume t b p) = false
  glob_assumeEq : ∀ t e n, glob (assumeEq t e n) = false
  glob_assign : ∀ t x n, glob (assign t x n) = false
  glob_setG : ∀ t g x, glob (setG t g x) = true
  glob_getG : ∀ t x g, glob (getG t x g) = true
  sem_assume : ∀ t b p s, sem (assume t b p) s = {s' | s' = s ∧ bval b (locals s t) = p}
  sem_assumeEq : ∀ t e n s, sem (assumeEq t e n) s = {s' | s' = s ∧ ival e (locals s t) = n}
  sem_assign : ∀ t x n s, sem (assign t x n) s = {Function.update s (.inr (t, x)) n}
  sem_setG : ∀ t g x s, sem (setG t g x) s = {Function.update s (.inl g) (s (.inr (t, x)))}
  sem_getG : ∀ t x g s, sem (getG t x g) s = {Function.update s (.inr (t, x)) (s (.inl g))}
  /-- The values `committed` and `aborted` assigned to the status variable of an atomic block. -/
  vCom : ℤ
  vAb : ℤ
  vCom_ne_vAb : vCom ≠ vAb

attribute [simp] Lang.thr_assume Lang.thr_assumeEq Lang.thr_assign Lang.thr_setG Lang.thr_getG
  Lang.glob_assume Lang.glob_assumeEq Lang.glob_assign Lang.glob_setG Lang.glob_getG
  Lang.ival_cst

variable {O M BE IE C : Type} [Lang T LV GV BE IE C]

open Lang CmdClass

/-! ### Trace evaluation -/

/-- `eval(s, φ)`. -/
def eval1 (s : State T LV GV) : Act T O M C → Set (State T LV GV)
  | .cmd _ c => sem c s
  | .iface _ _ => {s}

/-- One evaluation step on a set of states. -/
def evalStep (S : Set (State T LV GV)) (a : Act T O M C) : Set (State T LV GV) :=
  {s'' | ∃ s ∈ S, s'' ∈ eval1 s a}

/-- Evaluation of a trace from a set of states. -/
def evalSet (S : Set (State T LV GV)) : List (Act T O M C) → Set (State T LV GV)
  | [] => S
  | a :: l => evalSet (evalStep S a) l

/-- `eval(s, τ)`. -/
def eval (s : State T LV GV) (τ : List (Act T O M C)) : Set (State T LV GV) := evalSet {s} τ

lemma evalSet_append (S : Set (State T LV GV)) (l l' : List (Act T O M C)) :
    evalSet S (l ++ l') = evalSet (evalSet S l) l' := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih => exact ih _

/-- The paper's definition of `eval` on traces: `eval(s, ε) = {s}`,
`eval(s, τ φ) = {s'' | ∃ s' ∈ eval(s, τ), s'' ∈ eval(s', φ)}`. -/
lemma eval_nil (s : State T LV GV) : eval s ([] : List (Act T O M C)) = {s} := rfl

lemma eval_concat (s : State T LV GV) (τ : List (Act T O M C)) (φ : Act T O M C) :
    eval s (τ ++ [φ]) = {s'' | ∃ s' ∈ eval s τ, s'' ∈ eval1 s' φ} := by
  simp [eval, evalSet_append, evalSet, evalStep]

/-- Two actions commute (as relations on states). -/
def Commutes (a b : Act T O M C) : Prop :=
  ∀ S : Set (State T LV GV), evalStep (evalStep S a) b = evalStep (evalStep S b) a

lemma lifted_comm {A₁ A₂ : Var T LV GV → Prop} {R₁ R₂ : State T LV GV → Set (State T LV GV)}
    (h₁ : LiftedFrom A₁ R₁) (h₂ : LiftedFrom A₂ R₂) (hd : ∀ v, ¬ (A₁ v ∧ A₂ v)) (s s'' : State T LV GV) :
    (∃ s', s' ∈ R₁ s ∧ s'' ∈ R₂ s') ↔ (∃ s', s' ∈ R₂ s ∧ s'' ∈ R₁ s') := by
  classical
  obtain ⟨f₁, hf₁⟩ := h₁
  obtain ⟨f₂, hf₂⟩ := h₂
  -- symmetric characterization
  have key : ∀ (B₁ B₂ : Var T LV GV → Prop) (R₁ R₂ : State T LV GV → Set (State T LV GV))
      (f₁ : ((v : Subtype B₁) → ℤ) → Set ((v : Subtype B₁) → ℤ))
      (f₂ : ((v : Subtype B₂) → ℤ) → Set ((v : Subtype B₂) → ℤ)),
      (∀ s s', s' ∈ R₁ s ↔ (∀ v, ¬ B₁ v → s' v = s v) ∧ (fun v => s' v.1) ∈ f₁ (fun v => s v.1)) →
      (∀ s s', s' ∈ R₂ s ↔ (∀ v, ¬ B₂ v → s' v = s v) ∧ (fun v => s' v.1) ∈ f₂ (fun v => s v.1)) →
      (∀ v, ¬ (B₁ v ∧ B₂ v)) →
      ((∃ s', s' ∈ R₁ s ∧ s'' ∈ R₂ s') ↔
        (∀ v, ¬ B₁ v → ¬ B₂ v → s'' v = s v) ∧ (fun v => s'' v.1) ∈ f₁ (fun v => s v.1) ∧
          (fun v => s'' v.1) ∈ f₂ (fun v => s v.1)) := by
    intro B₁ B₂ R₁ R₂ f₁ f₂ hf₁ hf₂ hd
    constructor
    · rintro ⟨s', h1, h2⟩
      rw [hf₁] at h1; rw [hf₂] at h2
      refine ⟨fun v n1 n2 => (h2.1 v n2).trans (h1.1 v n1), ?_, ?_⟩
      · have : (fun v : Subtype B₁ => s'' v.1) = fun v => s' v.1 :=
          funext fun v => h2.1 v.1 (fun h => hd v.1 ⟨v.2, h⟩)
        rw [this]; exact h1.2
      · have : (fun v : Subtype B₂ => s v.1) = fun v => s' v.1 :=
          funext fun v => (h1.1 v.1 (fun h => hd v.1 ⟨h, v.2⟩)).symm
        rw [this]; exact h2.2
    · rintro ⟨h0, h1, h2⟩
      refine ⟨fun v => if B₁ v then s'' v else s v, ?_, ?_⟩
      · rw [hf₁]
        refine ⟨fun v hv => by simp [hv], ?_⟩
        have : (fun v : Subtype B₁ => (if B₁ v.1 then s'' v.1 else s v.1)) = fun v => s'' v.1 :=
          funext fun v => by rw [if_pos v.2]
        rw [this]; exact h1
      · rw [hf₂]
        refine ⟨fun v hv => ?_, ?_⟩
        · by_cases h : B₁ v
          · simp [h]
          · simp [h, h0 v h hv]
        · have : (fun v : Subtype B₂ => (if B₁ v.1 then s'' v.1 else s v.1)) = fun v => s v.1 :=
            funext fun v => by rw [if_neg (fun h => hd v.1 ⟨h, v.2⟩)]
          rw [this]; exact h2
  rw [key A₁ A₂ R₁ R₂ f₁ f₂ hf₁ hf₂ hd, key A₂ A₁ R₂ R₁ f₂ f₁ hf₂ hf₁ (fun v h => hd v ⟨h.2, h.1⟩)]
  constructor
  · rintro ⟨h0, h1, h2⟩; exact ⟨fun v n2 n1 => h0 v n1 n2, h2, h1⟩
  · rintro ⟨h0, h1, h2⟩; exact ⟨fun v n1 n2 => h0 v n2 n1, h2, h1⟩

/-- The condition of Proposition 23 on two actions of different threads. -/
def Prop23Cond (a b : Act T O M C) : Prop :=
  ∀ c₁ c₂, a = .cmd a.thread c₁ → b = .cmd b.thread c₂ →
    (thr c₁ = a.thread ∧ glob c₁ = false ∧ thr c₂ = b.thread) ∨
      (thr c₁ = a.thread ∧ thr c₂ = b.thread ∧ glob c₂ = false)

lemma commutes_of_prop23 {a b : Act T O M C} (hne : a.thread ≠ b.thread) (h : Prop23Cond a b) :
    Commutes a b := by
  intro S
  ext s''
  simp only [evalStep, Set.mem_setOf_eq]
  cases a with
  | iface t k => simp [eval1]
  | cmd t₁ c₁ =>
    cases b with
    | iface t k => simp [eval1]
    | cmd t₂ c₂ =>
      simp only [eval1]
      have hc := h c₁ c₂ rfl rfl
      simp only [Act.thread_cmd] at hne hc
      have hd : ∀ v : Var T LV GV, ¬ (accessible (thr c₁) (glob c₁) v ∧ accessible (thr c₂) (glob c₂) v) := by
        rintro (g | ⟨u, x⟩) ⟨h1, h2⟩
        · simp only [accessible] at h1 h2; rcases hc with ⟨-, h, -⟩ | ⟨-, -, h⟩ <;> simp_all
        · simp only [accessible] at h1 h2
          rcases hc with ⟨e1, -, e2⟩ | ⟨e1, e2, -⟩ <;> exact hne (e1 ▸ e2 ▸ h1 ▸ h2)
      constructor
      · rintro ⟨s', ⟨s, hs, h1⟩, h2⟩
        obtain ⟨s₀, h1', h2'⟩ := (lifted_comm (sem_lifted c₁) (sem_lifted c₂) hd s s'').mp ⟨s', h1, h2⟩
        exact ⟨s₀, ⟨s, hs, h1'⟩, h2'⟩
      · rintro ⟨s', ⟨s, hs, h1⟩, h2⟩
        obtain ⟨s₀, h1', h2'⟩ := (lifted_comm (sem_lifted c₁) (sem_lifted c₂) hd s s'').mpr ⟨s', h1, h2⟩
        exact ⟨s₀, ⟨s, hs, h1'⟩, h2'⟩

/-- **Proposition 23.** Actions of different threads satisfying the class condition commute. -/
theorem prop_23 (φ₁ φ₂ : Act T O M C) (hne : φ₁.thread ≠ φ₂.thread) (h : Prop23Cond φ₁ φ₂)
    (s : State T LV GV) : eval s [φ₁, φ₂] = eval s [φ₂, φ₁] := by
  simp only [eval, evalSet]; exact commutes_of_prop23 hne h {s}

lemma evalSet_swap {a b : Act T O M C} (h : Commutes a b) (S : Set (State T LV GV))
    (l : List (Act T O M C)) : evalSet S (a :: b :: l) = evalSet S (b :: a :: l) := by
  simp only [evalSet]; rw [h S]

lemma evalSet_move (φ : Act T O M C) : ∀ (X₁ X₂ : List (Act T O M C)) (S : Set (State T LV GV)),
    (∀ x ∈ X₁, Commutes x φ) → evalSet S (X₁ ++ φ :: X₂) = evalSet S (φ :: (X₁ ++ X₂))
  | [], _, _, _ => rfl
  | x :: X₁, X₂, S, h => by
    simp only [List.cons_append]
    rw [evalSet, evalSet_move φ X₁ X₂ _ (fun y hy => h y (by simp [hy])), ← evalSet,
      evalSet_swap (h x (by simp))]

/-! ### Lemma 18 -/

section dec
variable [DecidableEq T]

lemma ann_congr_off {st st' : T → Bool} {t : T} (l : List (Act T O M C))
    (hl : ∀ a ∈ l, a.thread ≠ t) (h : ∀ u, u ≠ t → st u = st' u) : ann st l = ann st' l := by
  induction l generalizing st st' with
  | nil => rfl
  | cons a l ih =>
    have ha := hl a (by simp)
    simp only [ann_cons]
    rw [flag_congr (st' := st') a (h _ ha), ih (fun b hb => hl b (by simp [hb])) ?_]
    intro u hu; exact upd_congr a (h u hu)

lemma stAfter_upd_comm {st : T → Bool} {t : T} (φ : Act T O M C) (hφ : φ.thread = t)
    (l : List (Act T O M C)) (hl : ∀ a ∈ l, a.thread ≠ t) :
    stAfter (upd st φ) l = upd (stAfter st l) φ := by
  funext u
  by_cases hu : u = t
  · subst hu
    rw [stAfter_of_no_iface _ _ l (fun x hx h => absurd h (hl x hx))]
    exact upd_congr φ (stAfter_of_no_iface _ _ l (fun x hx h => absurd h (hl x hx))).symm
  · rw [upd_apply_of_ne _ φ (hφ ▸ Ne.symm hu)]
    exact stAfter_congr l (upd_apply_of_ne _ φ (hφ ▸ Ne.symm hu))

/-- Moving an action `φ` of thread `t` to the left over actions of other threads preserves `∼`,
unless `φ` is non-transactional and passes a non-transactional action. -/
lemma obsEq_move (pre X₁ X₂ : List (Act T O M C)) (φ : Act T O M C)
    (hX₁ : ∀ x ∈ X₁, x.thread ≠ φ.thread)
    (hnt : flag (stAfter (fun _ => false) pre) φ = false →
      ∀ p ∈ ann (stAfter (fun _ => false) pre) X₁, p.2 = true) :
    ObsEq (pre ++ (X₁ ++ φ :: X₂)) (pre ++ (φ :: (X₁ ++ X₂))) := by
  obtain ⟨st, hst⟩ : ∃ st, stAfter (fun _ => false) pre = st := ⟨_, rfl⟩
  rw [hst] at hnt
  refine obsEq_append_of pre _ _ (fun u => ?_) ?_
  · by_cases hu : φ.thread = u
    · have : tproj u X₁ = [] := List.filter_eq_nil_iff.mpr (fun x hx => by
        simp only [decide_eq_true_eq]; rw [← hu]; exact hX₁ x hx)
      rw [tproj_append]
      simp only [tproj] at this ⊢
      simp [List.filter_cons, hu, this]
    · simp [tproj, List.filter_append, List.filter_cons, hu]
  · rw [hst]
    have hst1 : stAfter st X₁ φ.thread = st φ.thread :=
      stAfter_of_no_iface _ _ X₁ (fun x hx h => absurd h (hX₁ x hx))
    have hf : flag (stAfter st X₁) φ = flag st φ := flag_congr φ hst1
    have hann : ann (upd st φ) X₁ = ann st X₁ :=
      ann_congr_off X₁ hX₁ (fun u hu => upd_apply_of_ne st φ (Ne.symm hu))
    simp only [nontransFrom, ann_append, ann_cons, hf, hann, stAfter_upd_comm φ rfl X₁ hX₁]
    by_cases hfl : flag st φ = true
    · simp [hfl, List.filter_append, List.filter_cons]
    · have h0 : (ann st X₁).filter (fun p => !p.2) = [] :=
        List.filter_eq_nil_iff.mpr (fun p hp => by simp [hnt (by simpa using hfl) p hp])
      simp [List.filter_append, List.filter_cons, h0, hfl]

variable [Fintype T]

lemma eq_nil_of_tproj {X : List (Act T O M C)} (h : ∀ t, tproj t X = []) : X = [] := by
  rcases X with _ | ⟨a, X⟩
  · rfl
  · have := h a.thread; simp [tproj, List.filter_cons] at this

/-- `Lemma 18`, generalized to a common prefix. -/
theorem evalSet_eq_of_obsEq : ∀ (Y pre X : List (Act T O M C)) (S : Set (State T LV GV)),
    WFTrace (pre ++ X) → WFTrace (pre ++ Y) → ObsEq (pre ++ X) (pre ++ Y) →
    evalSet S X = evalSet S Y
  | [], pre, X, S, _, _, h => by
    have : X = [] := eq_nil_of_tproj (fun t => by
      have := h.1 t; rw [tproj_append, tproj_append] at this
      have := List.append_cancel_left this
      simpa [tproj] using this)
    subst this; rfl
  | φ :: Y, pre, X, S, hX, hY, h => by
    obtain ⟨st, hst⟩ : ∃ st, stAfter (fun _ => false) pre = st := ⟨_, rfl⟩
    have hp : ∀ u, tproj u X = tproj u (φ :: Y) := fun u => by
      have := h.1 u; rw [tproj_append, tproj_append] at this; exact List.append_cancel_left this
    have hn : nontransFrom st X = nontransFrom st (φ :: Y) := by
      have := h.2; rw [nontrans_append, nontrans_append, hst] at this
      exact List.append_cancel_left this
    have ht : tproj φ.thread X = φ :: tproj φ.thread Y := by
      rw [hp]; simp [tproj, List.filter_cons]
    obtain ⟨X₁, X₂, rfl, hX₁, -, hX₂⟩ := List.filter_eq_cons_iff.mp ht
    simp only [decide_eq_true_eq] at hX₁
    -- if `φ` is non-transactional, `X₁` has only transactional actions
    have hnt : flag st φ = false → ∀ p ∈ ann st X₁, p.2 = true := by
      intro hf
      have hst1 : stAfter st X₁ φ.thread = st φ.thread :=
        stAfter_of_no_iface _ _ X₁ (fun x hx h => absurd h (hX₁ x hx))
      have hf' : flag (stAfter st X₁) φ = false := by rw [flag_congr φ hst1]; exact hf
      have e := hn
      simp only [nontransFrom, ann_append, ann_cons, hf', hf, List.filter_append,
        List.filter_cons, Bool.not_false, ite_true, List.map_append, List.map_cons] at e
      intro p hp
      by_contra hc
      have hmem : p ∈ (ann st X₁).filter (fun p => !p.2) := by
        simp [hp, Bool.eq_false_iff.mpr hc]
      rcases hfx : (ann st X₁).filter (fun p => !p.2) with _ | ⟨q, L⟩
      · simp [hfx] at hmem
      · rw [hfx] at e
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at e
        have hq : q ∈ ann st X₁ := List.mem_of_mem_filter (hfx ▸ List.mem_cons_self ..)
        have : q.1 ∈ X₁ := by rw [← map_fst_ann st X₁]; exact List.mem_map_of_mem hq
        exact hX₁ _ this (by rw [e.1])
    -- every action of `X₁` commutes with `φ`
    have hcomm : ∀ x ∈ X₁, Commutes x φ := by
      intro x hx
      apply commutes_of_prop23 (hX₁ x hx)
      intro c₁ c₂ hx' hφ'
      have hloc := hX.2.1
      have h1 : thr c₁ = x.thread := hloc _ _ (by rw [← hx']; simp [hx])
      have h2 : thr c₂ = φ.thread := hloc _ _ (by rw [← hφ']; simp)
      by_cases hg : glob c₂ = true
      · left
        refine ⟨h1, ?_, h2⟩
        -- `φ` is a non-transactional global command, so `x` is transactional, hence local
        have hwφ : WFTrace ((pre ++ X₁) ++ cmd φ.thread c₂ :: X₂) := by
          rw [← hφ']; simpa using hX
        have hfφ := hwφ.flag_glob hg
        rw [stAfter_append, hst, ← hφ'] at hfφ
        have hst1 : stAfter st X₁ φ.thread = st φ.thread :=
          stAfter_of_no_iface _ _ X₁ (fun x hx h => absurd h (hX₁ x hx))
        rw [flag_congr φ hst1] at hfφ
        obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
        have hxann : (x, flag (stAfter st l₁) x) ∈ ann st (l₁ ++ x :: l₂) :=
          (mem_ann_iff st _ x _).mpr ⟨l₁, l₂, rfl, rfl⟩
        have hxt := hnt hfφ _ hxann
        by_contra hgx
        have hwx : WFTrace ((pre ++ l₁) ++ cmd x.thread c₁ :: (l₂ ++ φ :: X₂)) := by
          rw [← hx']; simpa using hX
        have := hwx.flag_glob (by simpa using hgx)
        rw [stAfter_append, hst, ← hx'] at this
        simp [this] at hxt
      · right; exact ⟨h1, h2, by simpa using hg⟩
    rw [evalSet_move φ X₁ X₂ S hcomm]
    simp only [evalSet]
    have hmove := obsEq_move pre X₁ X₂ φ hX₁ (by rw [hst]; exact hnt)
    refine evalSet_eq_of_obsEq Y (pre ++ [φ]) (X₁ ++ X₂) _ ?_ (by simpa using hY) ?_
    · have := hX.of_tproj hmove.1; simpa using this
    · have := hmove.symm.trans h; simpa using this

/-- **Lemma 18** (repaired Definition 12): observationally equivalent well-formed traces have the
same evaluation from every state. (The paper's hypothesis `eval(s, τH) ≠ ∅` is not needed.) -/
theorem lemma_18 {τH τS : List (Act T O M C)} (hH : WFTrace τH) (hS : WFTrace τS)
    (h : ObsEq τH τS) (s : State T LV GV) : eval s τH = eval s τS :=
  evalSet_eq_of_obsEq τS [] τH {s} (by simpa using hH) (by simpa using hS) (by simpa using h)

omit [Fintype T] in
lemma not_openIn_append {t : T} {P r : List (Act T O M C)}
    (hP : ∃ P' e, P = P' ++ [e] ∧ e.isEndA = true) (hr : iface t txbegin ∉ r) :
    ¬ OpenIn t (P ++ r) := by
  rintro ⟨L₁, L₂, h, h2⟩
  obtain ⟨P', e, rfl, he⟩ := hP
  rcases List.append_eq_append_iff.mp h with ⟨a', -, hr'⟩ | ⟨c', hP', hd⟩
  · exact hr (by rw [hr']; simp)
  · rcases c' with _ | ⟨d, c''⟩
    · exact hr (by simp at hd; rw [← hd]; simp)
    · simp only [List.cons_append, List.cons.injEq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      rcases List.eq_nil_or_concat c'' with rfl | ⟨c₃, e', rfl⟩
      · rw [List.append_singleton_inj] at hP'
        obtain ⟨-, rfl⟩ := hP'; simp [Act.isEndA, isEnd] at he
      · have : P' ++ [e] = (L₁ ++ iface t txbegin :: c₃) ++ [e'] := by simp [hP']
        rw [List.append_singleton_inj] at this
        obtain ⟨-, rfl⟩ := this
        have := h2 e (by simp); simp [this] at he

omit [Fintype T] in
lemma prefix_of_cmd {pre R τ₁ τ₂ : List (Act T O M C)} {t : T} {c : C}
    (hpre : ∀ x ∈ pre, x.toI.isSome) (h : τ₁ ++ cmd t c :: τ₂ = pre ++ R) :
    ∃ r, τ₁ = pre ++ r ∧ r ++ cmd t c :: τ₂ = R := by
  rcases List.append_eq_append_iff.mp h with ⟨a', h1, h2⟩ | ⟨c', h1, h2⟩
  · rcases a' with _ | ⟨d, a'⟩
    · exact ⟨[], by simpa using h1.symm, by simp only [List.nil_append] at h2 ⊢; exact h2⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      have := hpre d (by rw [h1, ← h2.1]; simp)
      simp [← h2.1, Act.toI] at this
  · exact ⟨c', h1, h2.symm⟩

omit [Fintype T] in
lemma evalSet_ifaces (S : Set (State T LV GV)) (l : List (Act T O M C))
    (h : ∀ x ∈ l, x.toI.isSome) : evalSet S l = S := by
  induction l generalizing S with
  | nil => rfl
  | cons a l ih =>
    have ha := h a (by simp)
    simp only [evalSet]
    rw [ih _ (fun x hx => h x (by simp [hx]))]
    cases a with
    | cmd => simp [Act.toI] at ha
    | iface => ext; simp [evalStep, eval1]

/-- **Lemma 18 is false for Definition 12 as printed** (where a global command is forbidden only
if no `committed`/`aborted` action of *any* thread occurs since the thread's `txbegin`): thread `t₁`
starts a transaction, thread `t₂` runs a complete transaction, then `t₁` executes `g := x`
(inside its transaction) and `t₂` executes `g := x` (outside). Swapping the two writes preserves
`∼` (the first is transactional) but not the final value of `g`. -/
theorem lemma_18_false_literal (t₁ t₂ : T) (hne : t₁ ≠ t₂) (g : GV) (x : LV) :
    ¬ ∀ (τH τS : List (Act T O M C)), WFTraceLit τH → WFTraceLit τS → ObsEq τH τS →
      ∀ s : State T LV GV, eval s τH ≠ ∅ → eval s τH = eval s τS := by
  intro hall
  let pre : List (Act T O M C) := [iface t₁ txbegin, iface t₁ ok, iface t₂ txbegin, iface t₂ ok,
    iface t₂ txcommit, iface t₂ committed]
  have hpre : ∀ y ∈ pre, y.toI.isSome := by intro y hy; simp [pre] at hy; rcases hy with h | h | h | h | h | h <;> simp [h]
  let a : Act T O M C := cmd t₁ (setG t₁ g x)
  let b : Act T O M C := cmd t₂ (setG t₂ g x)
  have hhist : ∀ R : List (Act T O M C), R = [a, b] ∨ R = [b, a] → history (pre ++ R) =
      [(t₁, txbegin), (t₁, ok), (t₂, txbegin), (t₂, ok), (t₂, txcommit), (t₂, committed)] := by
    rintro R (rfl | rfl) <;> simp [pre, a, b, history]
  have hWF : WellFormed ([(t₁, txbegin), (t₁, ok), (t₂, txbegin), (t₂, ok), (t₂, txcommit),
      (t₂, committed)] : List (IAct T O M)) := by
    rw [wellFormed_iff_run]
    intro t
    by_cases h1 : t = t₁
    · subst h1; simp [proj, List.filter_cons, Ne.symm hne, TState.step]
    by_cases h2 : t = t₂
    · subst h2; simp [proj, List.filter_cons, hne, TState.step]
    · simp [proj, List.filter_cons, Ne.symm h1, Ne.symm h2]
  have wfl : ∀ R : List (Act T O M C), R = [a, b] ∨ R = [b, a] → WFTraceLit (pre ++ R) := by
    intro R hR
    refine ⟨by rw [hhist R hR]; exact hWF.toLit, ?_, ?_⟩
    · intro t c hc
      rcases hR with rfl | rfl <;> simp [pre, a, b] at hc <;>
        rcases hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
    · intro τ₁ t c τ₂ he _
      obtain ⟨r, rfl, hr⟩ := prefix_of_cmd hpre he.symm
      refine not_openIn_append (P := pre) ⟨[iface t₁ txbegin, iface t₁ ok, iface t₂ txbegin,
        iface t₂ ok, iface t₂ txcommit], iface t₂ committed, rfl, by simp [Act.isEndA, isEnd]⟩ ?_
      intro hm
      have : iface t txbegin ∈ R := by rw [← hr]; simp [hm]
      rcases hR with rfl | rfl <;> simp [a, b] at this
  have hobs : ObsEq (pre ++ [a, b]) (pre ++ [b, a]) := by
    refine obsEq_append_of pre _ _ (fun u => ?_) ?_
    · by_cases h1 : t₁ = u
      · subst h1; simp [tproj, a, b, List.filter_cons, hne, Ne.symm hne]
      · simp [tproj, a, b, List.filter_cons, h1]
    · simp [pre, nontransFrom, stAfter, upd, flag, a, b, Act.isBoundA, Function.update_apply,
        hne, Ne.symm hne]
  let s : State T LV GV := fun v => match v with
    | .inr (u, _) => if u = t₁ then 1 else 2
    | .inl _ => 0
  have e1 : ∀ s'' ∈ eval s (pre ++ [a, b]), s'' (.inl g) = 2 := by
    simp only [eval, evalSet_append, evalSet_ifaces _ pre hpre]
    intro s'' hs
    simp [evalSet, evalStep, eval1, a, b, sem_setG, s, Ne.symm hne] at hs
    rw [hs]; simp [Ne.symm hne]
  have e2 : ∀ s'' ∈ eval s (pre ++ [b, a]), s'' (.inl g) = 1 := by
    simp only [eval, evalSet_append, evalSet_ifaces _ pre hpre]
    intro s'' hs
    simp [evalSet, evalStep, eval1, a, b, sem_setG, s, Ne.symm hne] at hs
    rw [hs]; simp
  have hne1 : (eval s (pre ++ [a, b])).Nonempty := by
    classical
    simp only [eval, evalSet_append, evalSet_ifaces _ pre hpre]
    simp [evalSet, evalStep, eval1, a, b, sem_setG, Set.Nonempty]
  have := hall _ _ (wfl _ (Or.inl rfl)) (wfl _ (Or.inr rfl)) hobs s hne1.ne_empty
  obtain ⟨s'', hs''⟩ := hne1
  have h1 := e1 s'' hs''
  rw [this] at hs''
  have h2 := e2 s'' hs''
  omega

end dec

end Podc.TMObservationalRefinement
