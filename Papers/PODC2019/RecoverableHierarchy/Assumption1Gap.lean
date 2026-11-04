import Papers.PODC2019.RecoverableHierarchy.Theorem3

/-!
# The literal Assumption 1 does not support the proof of Theorem 3

The proof of Theorem 3 restricts attention to executions obeying **Assumption 1**: "a process
`pᵢ` takes a crash step iff (1) `pᵢ`'s previous step was its *first access* in this execution to
some TAS object, and (2) `pᵢ` is the lowest-numbered process". With *readable* TAS objects, a
read is an access. Case C of the proof claims that if `p₁` has accessed the TAS object `T` then
`T` holds `1`, which is false when that access was a read.

We show that the restricted-model argument cannot be repaired without changing the assumption:
the simple algorithm `A₀` below (one rTAS object `T` and two registers `P[0]`, `P[1]`) is
**correct on all executions of the literal restricted model** (`literal_assumption1_rcorrect`),
although it is not a recoverable consensus algorithm with at most one failure
(`A₀_not_solvesP`, from Theorem 3 with the repaired assumption, `theorem3`).

Algorithm `A₀`, process `i` with input `v`:
1. `P[i] := v`;
2. read `T` (a dummy read: under the literal Assumption 1 this is `p₀`'s first access to `T`,
   so `p₀` crashes right after it, and never again);
3. `tas T`: if it returns `0`, output `v`;
4. otherwise output `P[1 - i]`.

In the literal restricted model the crashing process `a = 0` crashes exactly once, right after
its first read of `T`, *before* its first `tas`; hence the `tas` winner never crashes afterwards
and the standard TAS consensus argument applies.
-/

namespace Podc.RecoverableHierarchy.Assumption1Gap

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option allowUnsafeReducibility true in
attribute [local reducible] Sum.elim

/-- The objects: registers `P[0]`, `P[1]` (`Sum.inl i`, initially `none`) and one readable
test-and-set object `T` (`Sum.inr ()`). -/
abbrev Obj : Fin 2 ⊕ Unit → ObjSpec :=
  withRW (ιS := Unit) (fun _ : Fin 2 => register (Option Bool) none) rtasObj

/-- Program counter of `A₀` (`done v`: output `v`). -/
inductive Stg where
  | s1 | s2 | s3 | s4
  | done (v : Bool)
  deriving DecidableEq

/-- Local state: the process id, its input, and the program counter. -/
structure Loc where
  id : Fin 2
  inp : Bool
  stg : Stg

/-- The other process. -/
def oth (i : Fin 2) : Fin 2 := if i = 0 then 1 else 0

/-- The next action of `A₀`. -/
def act (l : Loc) : Act Obj Loc :=
  match l.stg with
  | .s1 => .access (.inl l.id) (RWOp.write (some l.inp)) fun _ => { l with stg := .s2 }
  | .s2 => .access (.inr ()) RTASOp.read fun _ => { l with stg := .s3 }
  | .s3 => .access (.inr ()) RTASOp.tas fun (r : Bool) =>
      { l with stg := if r then .s4 else .done l.inp }
  | .s4 => .access (.inl (oth l.id)) (RWOp.read) fun (r : Option Bool) =>
      { l with stg := .done (r.getD l.inp) }
  | .done v => .out v

/-- The algorithm `A₀`. -/
abbrev A₀ : Alg 2 Obj where
  L := Loc
  init i v := ⟨i, v, .s1⟩
  act := act
  mem₀ := fun
    | .inl _ => (none : Option Bool)
    | .inr () => false

/-- The literal Assumption 1: process `0` crashes right after its first **access** (of any
kind, reads included) to the test-and-set object. -/
def trigLit : (i : Fin 2 ⊕ Unit) → (Obj i).Op → Bool
  | .inl _, _ => false
  | .inr _, _ => true

/-- The restricted model of the literal Assumption 1 for `A₀`: `a = 0` crashes, `b = 1` never
crashes; the only triggering object is `T`. -/
def restrLit : Restr A₀ where
  a := 0
  b := 1
  hab := by decide
  trig := trigLit
  F := {Sum.inr ()}
  hF := by
    rintro (j | j) o h
    · simp [trigLit] at h
    · simp

/-! ## One step of `A₀` -/

/-- The memory type, as a plain function type. -/
abbrev Mem := (i : Fin 2 ⊕ Unit) → (Obj i).State

@[simp] lemma upd_inl_inr (m : Mem) (i : Fin 2) (v : Option Bool) (u : Unit) :
    Function.update m (.inl i) v (.inr u) = m (.inr u) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_inr_inl (m : Mem) (v : Bool) (j : Fin 2) :
    Function.update m (.inr ()) v (.inl j) = m (.inl j) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_inr_inr (m : Mem) (v : Bool) :
    Function.update m (.inr ()) v (.inr ()) = v :=
  Function.update_self _ _ _

lemma upd_inl_inl (m : Mem) (i j : Fin 2) (v : Option Bool) :
    (Function.update m (.inl i) v (.inl j) : Option Bool) = if j = i then v else m (.inl j) := by
  by_cases h : j = i
  · subst h; simp
  · simp only [h, ↓reduceIte]; exact Function.update_of_ne (by simpa using h) _ _

variable {C : Cfg A₀} {p : Fin 2}

lemma act_eq (l : Loc) : A₀.act l = act l := rfl

lemma step_s1 (h : (C.loc p).stg = .s1) : C.stepP p =
    { C with loc := Function.update C.loc p { C.loc p with stg := .s2 },
             mem := Function.update C.mem (.inl (C.loc p).id) (some (C.loc p).inp) } := by
  have ha : A₀.act (C.loc p) = .access (.inl (C.loc p).id) (RWOp.write (some (C.loc p).inp))
      (fun _ => { C.loc p with stg := .s2 }) := by rw [act_eq, act, h]
  rw [stepP_of_access C ha]

lemma step_s2 (h : (C.loc p).stg = .s2) : C.stepP p =
    { C with loc := Function.update C.loc p { C.loc p with stg := .s3 } } := by
  have ha : A₀.act (C.loc p) = .access (.inr ()) RTASOp.read
      (fun _ => { C.loc p with stg := .s3 }) := by rw [act_eq, act, h]
  rw [stepP_of_access C ha]
  congr 1
  exact Function.update_eq_self _ _

lemma step_s3 (h : (C.loc p).stg = .s3) : C.stepP p =
    { C with loc := Function.update C.loc p
                { C.loc p with stg := if C.mem (.inr ()) = true then .s4 else .done (C.loc p).inp },
             mem := Function.update C.mem (.inr ()) true } := by
  have ha : A₀.act (C.loc p) = .access (.inr ()) RTASOp.tas
      (fun (r : Bool) => { C.loc p with stg := if r then .s4 else .done (C.loc p).inp }) := by
    rw [act_eq, act, h]
  rw [stepP_of_access C ha]

lemma step_s4 (h : (C.loc p).stg = .s4) : C.stepP p =
    { C with loc := Function.update C.loc p
                { C.loc p with stg := .done ((C.mem (.inl (oth (C.loc p).id)) : Option Bool).getD
                  (C.loc p).inp) } } := by
  have ha : A₀.act (C.loc p) = .access (.inl (oth (C.loc p).id)) RWOp.read
      (fun (r : Option Bool) => { C.loc p with stg := .done (r.getD (C.loc p).inp) }) := by
    rw [act_eq, act, h]
  rw [stepP_of_access C ha]
  congr 1
  exact Function.update_eq_self _ _

lemma step_done {v : Bool} (h : (C.loc p).stg = .done v) : C.stepP p = C :=
  stepP_of_out C (show A₀.act (C.loc p) = .out v by rw [act_eq, act, h])

lemma out_iff {v : Bool} : C.Out p v ↔ (C.loc p).stg = .done v := by
  unfold Cfg.Out
  rw [act_eq, act]
  split <;> simp_all


/-! ## The invariant -/

/-- Stages before the `tas` step completes. -/
def Stg.early : Stg → Bool
  | .s1 | .s2 | .s3 => true
  | _ => false

/-- `d` is the decision: `T` is set, some process `j` with input `d` has output `d`, and every
output is `d`. -/
def Win (x : Fin 2 → Bool) (C : Cfg A₀) (d : Bool) : Prop :=
  C.mem (.inr ()) = true ∧ (∃ j, (C.loc j).stg = .done d ∧ x j = d) ∧
    ∀ q w, (C.loc q).stg = .done w → w = d

/-- The invariant on configurations. -/
structure CInv (x : Fin 2 → Bool) (C : Cfg A₀) : Prop where
  inp : C.inp = x
  id : ∀ q, (C.loc q).id = q
  vin : ∀ q, (C.loc q).inp = x q
  Pst : ∀ q, (C.loc q).stg ≠ .s1 → C.mem (.inl q) = some (x q)
  Tf : C.mem (.inr ()) = false → ∀ q, (C.loc q).stg.early = true
  Tt : C.mem (.inr ()) = true → ∃ d, Win x C d

lemma oth_ne {j q : Fin 2} (h : j ≠ q) : oth q = j := by
  fin_cases j <;> fin_cases q <;> simp_all [oth]

/-- `Win` survives a step of a process that has not output, as long as `T` stays set and the
process does not output a different value. -/
lemma Win.upd {x : Fin 2 → Bool} {C C' : Cfg A₀} {d : Bool} (hW : Win x C d)
    (hT : C'.mem (.inr ()) = true) {l : Loc} (hloc : C'.loc = Function.update C.loc p l)
    (hp : ∀ w, (C.loc p).stg ≠ .done w) (hl : ∀ w, l.stg = .done w → w = d) : Win x C' d := by
  obtain ⟨-, ⟨j, hj, hxj⟩, hw⟩ := hW
  refine ⟨hT, ⟨j, ?_, hxj⟩, fun q w hq => ?_⟩
  · rw [hloc, Function.update_of_ne (by rintro rfl; exact hp _ hj)]; exact hj
  · rw [hloc] at hq
    by_cases hqp : q = p
    · subst hqp; rw [Function.update_self] at hq; exact hl w hq
    · rw [Function.update_of_ne hqp] at hq; exact hw q w hq

lemma cinv_step {x : Fin 2 → Bool} (h : CInv x C) (p : Fin 2) :
    CInv x (C.stepP p) ∧ ∀ d, Win x C d → Win x (C.stepP p) d := by
  obtain ⟨hinp, hid, hvin, hP, hTf, hTt⟩ := h
  rcases hs : (C.loc p).stg with _ | _ | _ | _ | v
  · -- write `P[p]`
    rw [step_s1 hs, hid p, hvin p]
    have hW : ∀ d, Win x C d → Win x { C with
        loc := Function.update C.loc p { C.loc p with stg := .s2 },
        mem := Function.update C.mem (.inl p) (some (x p)) } d := by
      exact fun d hW => hW.upd hW.1 rfl (by simp [hs]) (by simp)
    refine ⟨⟨hinp, fun q => ?_, fun q => ?_, fun q hq => ?_, fun hT q => ?_,
      fun hT => (hTt hT).imp hW⟩, hW⟩ <;>
      simp only [Function.update_apply, upd_inl_inl, upd_inl_inr] at * <;>
      split_ifs at * <;> subst_vars <;> simp_all [-Fin.forall_fin_two, -Fin.exists_fin_two, Stg.early]
  · -- read `T`
    rw [step_s2 hs]
    have hW : ∀ d, Win x C d → Win x { C with
        loc := Function.update C.loc p { C.loc p with stg := .s3 } } d := by
      exact fun d hW => hW.upd hW.1 rfl (by simp [hs]) (by simp)
    refine ⟨⟨hinp, fun q => ?_, fun q => ?_, fun q hq => ?_, fun hT q => ?_,
      fun hT => (hTt hT).imp hW⟩, hW⟩ <;>
      simp only [Function.update_apply] at * <;>
      split_ifs at * <;> subst_vars <;> simp_all [-Fin.forall_fin_two, -Fin.exists_fin_two, Stg.early]
  · -- `tas T`
    rw [step_s3 hs, hvin p]
    have hPp := hP p (by simp [hs])
    cases hT : C.mem (.inr ())
    · -- `p` wins
      have hW : Win x { C with
          loc := Function.update C.loc p { C.loc p with stg := .done (x p) },
          mem := Function.update C.mem (.inr ()) true } (x p) := by
        refine ⟨by simp, ⟨p, by simp, rfl⟩, fun q w hq => ?_⟩
        by_cases hqp : q = p
        · subst hqp; simp at hq; exact hq.symm
        · simp only [Function.update_of_ne hqp] at hq
          have := hTf hT q; rw [hq] at this; cases this
      refine ⟨⟨hinp, fun q => ?_, fun q => ?_, fun q hq => ?_, fun hT' => by simp at hT',
        fun _ => ⟨_, hW⟩⟩, fun d hd => by rw [hd.1] at hT; cases hT⟩ <;>
        simp only [Function.update_apply, upd_inr_inl, Bool.false_eq_true, ↓reduceIte] at * <;>
        split_ifs at * <;> subst_vars <;> simp_all [-Fin.forall_fin_two, -Fin.exists_fin_two]
    · -- `p` loses
      have hW : ∀ d, Win x C d → Win x { C with
          loc := Function.update C.loc p { C.loc p with stg := .s4 },
          mem := Function.update C.mem (.inr ()) true } d :=
        fun d hW => hW.upd (by simp) rfl (by simp [hs]) (by simp)
      refine ⟨⟨hinp, fun q => ?_, fun q => ?_, fun q hq => ?_, fun hT' => by simp at hT',
        fun _ => (hTt hT).imp hW⟩, hW⟩ <;>
        simp only [Function.update_apply, upd_inr_inl, ↓reduceIte] at * <;>
        split_ifs at * <;> subst_vars <;> simp_all [-Fin.forall_fin_two, -Fin.exists_fin_two]
  · -- read `P[oth p]`
    rw [step_s4 hs, hid p, hvin p]
    have hW : ∀ d, Win x C d → Win x { C with
        loc := Function.update C.loc p { C.loc p with
          stg := .done ((C.mem (.inl (oth p)) : Option Bool).getD (x p)) } } d := by
      intro d hW
      obtain ⟨-, ⟨j, hj, hxj⟩, -⟩ := id hW
      have hjp : j ≠ p := by rintro rfl; rw [hs] at hj; cases hj
      have hPj := hP j (by rw [hj]; simp)
      refine hW.upd hW.1 rfl (by simp [hs]) fun w hw => ?_
      rw [oth_ne hjp, hPj] at hw
      simp only [Option.getD_some, Stg.done.injEq] at hw
      rw [← hw, hxj]
    refine ⟨⟨hinp, fun q => ?_, fun q => ?_, fun q hq => ?_, fun hT q => ?_,
      fun hT => (hTt hT).imp hW⟩, hW⟩
    · by_cases hqp : q = p
      · subst hqp; simp [hid]
      · simp [Function.update_of_ne hqp, hid]
    · by_cases hqp : q = p
      · subst hqp; simp [hvin]
      · simp [Function.update_of_ne hqp, hvin]
    · by_cases hqp : q = p
      · subst hqp; exact hP q (by simp [hs])
      · exact hP q (by simpa [Function.update_of_ne hqp] using hq)
    · have := hTf hT p; rw [hs] at this; cases this
  · rw [step_done hs]; exact ⟨⟨hinp, hid, hvin, hP, hTf, hTt⟩, fun _ h => h⟩


lemma cinv_crash {x : Fin 2 → Bool} (h : CInv x C) (hs : (C.loc p).stg = .s3) :
    CInv x (C.next (.crash p)) ∧ ∀ d, Win x C d → Win x (C.next (.crash p)) d := by
  obtain ⟨hinp, hid, hvin, hP, hTf, hTt⟩ := h
  have hc : C.next (.crash p) = { C with loc := Function.update C.loc p ⟨p, x p, .s1⟩ } := by
    simp [Cfg.next, hinp]
  rw [hc]
  have hW : ∀ d, Win x C d → Win x { C with loc := Function.update C.loc p ⟨p, x p, .s1⟩ } d :=
    fun d hW => hW.upd hW.1 rfl (by simp [hs]) (by simp)
  refine ⟨⟨hinp, fun q => ?_, fun q => ?_, fun q hq => ?_, fun hT q => ?_,
    fun hT => (hTt hT).imp hW⟩, hW⟩ <;>
    simp only [Function.update_apply] at * <;>
    split_ifs at * <;> subst_vars <;> simp_all [-Fin.forall_fin_two, -Fin.exists_fin_two, Stg.early]

/-! ## The invariant of the restricted executions -/

/-- The invariant of restricted states: `CInv`, process `0` has not passed its read of `T`
before `T` is triggered, and a pending crash of `0` happens right after that read. -/
structure RInv (x : Fin 2 → Bool) (s : RS A₀) : Prop where
  c : CInv x s.c
  trg : Sum.inr () ∉ s.trg → (s.c.loc 0).stg = .s1 ∨ (s.c.loc 0).stg = .s2
  pend : s.pend = true → (s.c.loc 0).stg = .s3

lemma newTrig_s1 {s : RS A₀} (hs : (s.c.loc 0).stg = .s1) : restrLit.newTrig s = none := by
  unfold Restr.newTrig
  rw [show restrLit.a = 0 from rfl, act_eq, act, hs]
  simp [restrLit, trigLit]

lemma newTrig_s2 {s : RS A₀} (hs : (s.c.loc 0).stg = .s2) (ht : Sum.inr () ∉ s.trg) :
    restrLit.newTrig s = some (.inr ()) := by
  unfold Restr.newTrig
  rw [show restrLit.a = 0 from rfl, act_eq, act, hs]
  simp [restrLit, trigLit, ht]

lemma rinv_mv {x : Fin 2 → Bool} {s : RS A₀} (h : RInv x s) (m : Bool) :
    RInv x (restrLit.mv s m) ∧ ∀ d, Win x s.c d → Win x (restrLit.mv s m).c d := by
  cases m
  · by_cases hp : s.pend
    · rw [restrLit.mv_false_pend s hp]
      have hs := h.pend hp
      obtain ⟨hc, hW⟩ := cinv_crash h.c hs
      refine ⟨⟨hc, fun _ => Or.inl ?_, fun h' => by simp at h'⟩, hW⟩
      simp [Cfg.next, h.c.inp, show restrLit.a = 0 from rfl]
    · simp only [Bool.not_eq_true] at hp
      rw [restrLit.mv_false_npend s hp]
      obtain ⟨hc, hW⟩ := cinv_step h.c 0
      rcases hn : restrLit.newTrig s with _ | i
      · refine ⟨⟨hc, fun ht => ?_, fun h' => by simp [hp] at h'⟩, hW⟩
        rcases h.trg ht with hs | hs
        · show ((s.c.stepP 0).loc 0).stg = .s1 ∨ ((s.c.stepP 0).loc 0).stg = .s2
          rw [step_s1 hs]; simp
        · rw [newTrig_s2 hs ht] at hn; cases hn
      · obtain ⟨hi, hiF⟩ := restrLit.newTrig_spec hn
        have hi' : i = .inr () := by simpa [restrLit] using hiF
        subst hi'
        have hs : (s.c.loc 0).stg = .s2 := by
          rcases h.trg hi with hs | hs
          · rw [newTrig_s1 hs] at hn; cases hn
          · exact hs
        refine ⟨⟨hc, fun ht => by simp at ht, fun _ => ?_⟩, hW⟩
        show ((s.c.stepP 0).loc 0).stg = _
        rw [step_s2 hs]; simp
  · rw [restrLit.mv_true]
    obtain ⟨hc, hW⟩ := cinv_step h.c 1
    have hl : (s.c.stepP 1).loc 0 = s.c.loc 0 := stepP_loc_other _ (by decide)
    exact ⟨⟨hc, fun ht => by simpa [restrLit, hl] using h.trg ht,
      fun hp => by simpa [restrLit, hl] using h.pend hp⟩, hW⟩

lemma rinv_rrun {x : Fin 2 → Bool} (σ : List Bool) : ∀ {s : RS A₀}, RInv x s →
    RInv x (restrLit.rrun s σ) ∧ ∀ d, Win x s.c d → Win x (restrLit.rrun s σ).c d := by
  induction σ with
  | nil => exact fun h => ⟨h, fun _ h => h⟩
  | cons m σ ih =>
    intro s h
    obtain ⟨h1, hW1⟩ := rinv_mv h m
    obtain ⟨h2, hW2⟩ := ih h1
    exact ⟨h2, fun d hd => hW2 d (hW1 d hd)⟩

lemma rinv_init (x : Fin 2 → Bool) : RInv x (RS.init A₀ x) where
  c :=
    { inp := rfl
      id := fun _ => rfl
      vin := fun _ => rfl
      Pst := fun _ h => absurd rfl h
      Tf := fun _ _ => rfl
      Tt := fun h => by simp [RS.init, initCfg] at h }
  trg := fun _ => Or.inl rfl
  pend := fun h => by simp [RS.init] at h

lemma rinv_S (x : Fin 2 → Bool) (σ : List Bool) : RInv x (restrLit.S x σ) :=
  (rinv_rrun σ (rinv_init x)).1

/-- An output is the decision. -/
lemma win_of_out {x : Fin 2 → Bool} {s : RS A₀} (h : RInv x s) {p : Fin 2} {v : Bool}
    (hv : s.c.Out p v) : Win x s.c v := by
  rw [out_iff] at hv
  cases hT : s.c.mem (.inr ())
  · have := h.c.Tf hT p; rw [hv] at this; cases this
  · obtain ⟨d, hd⟩ := h.c.Tt hT
    rwa [hd.2.2 p v hv]

lemma out_S {x : Fin 2 → Bool} {σ : List Bool} {p : Fin 2} {v : Bool}
    (h : Outputs (initCfg A₀ x) (restrLit.E x σ) p v) :
    ∃ k ≤ σ.length, (restrLit.S x (σ.take k)).c.Out p v := by
  obtain ⟨k, hk, hv⟩ := h
  refine ⟨k, by simpa using hk, ?_⟩
  rw [Restr.S_c]; simpa only [Restr.E, Restr.evs_take] using hv

lemma agree_aux {x : Fin 2 → Bool} {σ : List Bool} {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) {p q : Fin 2}
    {v w : Bool} (hv : (restrLit.S x (σ.take k₁)).c.Out p v)
    (hw : (restrLit.S x (σ.take k₂)).c.Out q w) : v = w := by
  have hsplit : σ.take k₂ = σ.take k₁ ++ (σ.take k₂).drop k₁ := by
    conv_lhs => rw [← List.take_append_drop k₁ (σ.take k₂)]
    rw [List.take_take, min_eq_left hk]
  have hW := (rinv_rrun ((σ.take k₂).drop k₁) (rinv_S x (σ.take k₁))).2 v
    (win_of_out (rinv_S x _) hv)
  rw [← Restr.rrun_append, ← hsplit] at hW
  rw [out_iff] at hw
  exact (hW.2.2 q w hw).symm

/-- Rank of a local state: the number of remaining accesses. -/
def rank (l : Loc) : ℕ :=
  match l.stg with
  | .s1 => 4
  | .s2 => 3
  | .s3 => 2
  | .s4 => 1
  | .done _ => 0

lemma rank_lt (l : A₀.L) (i : Fin 2 ⊕ Unit) (o : (Obj i).Op) (κ : (Obj i).Resp → A₀.L)
    (r : (Obj i).Resp) (h : A₀.act l = .access i o κ) : rank (κ r) < rank l := by
  rcases l with ⟨id, v, st⟩
  cases st <;> simp only [act] at h <;> cases h <;> simp [rank]
  split_ifs <;> simp

/-- **The literal Assumption 1 does not support the proof of Theorem 3.** The algorithm `A₀`
(one readable test-and-set object, two registers) is a correct recoverable consensus algorithm —
agreement, validity and recoverable wait-freedom — on all executions of the restricted failure
model of the paper's literal Assumption 1 (process `p₁` crashes iff its previous step was its
first *access*, reads included, to a TAS object). So the valency argument of Theorem 3 in this
restricted model must fail (it does, in Case C). -/
theorem literal_assumption1_rcorrect : restrLit.RCorrect where
  agree x σ p q _ v w hv hw := by
    obtain ⟨k₁, -, h₁⟩ := out_S hv
    obtain ⟨k₂, -, h₂⟩ := out_S hw
    rcases le_total k₁ k₂ with hk | hk
    · exact agree_aux hk h₁ h₂
    · exact (agree_aux hk h₂ h₁).symm
  valid x σ v hv := by
    obtain ⟨p, hp⟩ := Dec.exists_outputs hv
    obtain ⟨k, -, h⟩ := out_S hp
    obtain ⟨-, ⟨j, -, hj⟩, -⟩ := win_of_out (rinv_S x _) h
    exact ⟨j, hj⟩
  prog x sch m N hinf hN := by
    have hsteps : ∀ M, ∃ t ≥ M, restrLit.eInf x sch t = .step (restrLit.who m) := by
      intro M
      obtain ⟨t, ht, hm⟩ := hinf (max M N)
      refine ⟨t, le_of_max_le_left ht, ?_⟩
      have hN' := hN t (le_of_max_le_right ht)
      unfold Restr.eInf at hN' ⊢
      rw [hm] at hN' ⊢
      cases m
      · by_cases hp : (restrLit.S x (Restr.bpre sch t)).pend
        · exact absurd (restrLit.ev_false_pend _ hp) hN'
        · simp only [Bool.not_eq_true] at hp
          exact restrLit.ev_false_npend _ hp
      · rfl
    obtain ⟨t, ht, v, hv⟩ := prog_of_rank rank rank_lt (initCfg A₀ x) (restrLit.eInf x sch)
      (restrLit.who m) N hsteps hN
    refine ⟨t, ht, v, ?_⟩
    rwa [Restr.S_c, ← Restr.pre_eInf]

/-- `A₀` is **not** a recoverable consensus algorithm with at most one failure: by Theorem 3
(with the repaired Assumption 1), no algorithm with one readable test-and-set object and
registers is. Together with `literal_assumption1_rcorrect`, the literal restricted model is
strictly weaker than the model of Theorem 3. -/
theorem A₀_not_solvesP : ¬ SolvesP A₀ (AtMost 1) :=
  theorem3 (fun _ => register_rwLike _ _) 1 (by simp) A₀

end Podc.RecoverableHierarchy.Assumption1Gap
