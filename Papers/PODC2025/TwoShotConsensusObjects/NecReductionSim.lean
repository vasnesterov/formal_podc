import Papers.PODC2025.TwoShotConsensusObjects.Model

/-!
# The simulation behind Proposition 2 (removing one copy of `O`)

Given an algorithm `A`, a configuration `F` of `A`, a copy `k` and a decision rule `dec`, the
algorithm `NecRed.A' A F k dec` uses the copies of `O` other than `k`, the read/write objects of
`A` and two fresh binary registers. Process `p` with input `b`

1. writes `b` to its fresh register;
2. simulates `A` from the local state `F.loc p` (objects other than `k` are shared with the
   simulated execution);
3. when the simulated local state is poised to apply `c` to copy `k`, it outputs the input of
   `p₀` if `dec p c` and the input of `p₁` otherwise (reading the fresh register of the other
   process if needed).
-/

namespace TwoShotCons

namespace NecRed

set_option linter.unusedSectionVars false

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}

/-- The read/write objects of the new algorithm: those of `A` and two fresh binary registers. -/
abbrev R' (R : ιR → ObjSpec) : ιR ⊕ Fin 2 → ObjSpec := Sum.elim R (fun _ => register Bool false)

/-- The objects of the new algorithm. -/
abbrev T' (R : ιR → ObjSpec) (O : ObjSpec) (k : ιS) :=
  withRW (ιS := {k' // k' ≠ k}) (R' R) O

/-- Local states of the new algorithm. -/
inductive St (L : Type) where
  /-- Before writing the input `b` (process `p`). -/
  | start (p : Fin 2) (b : Bool)
  /-- Simulating `A` in local state `l` (process `p`, input `b`). -/
  | sim (p : Fin 2) (b : Bool) (l : L)
  /-- Decided `v`. -/
  | done (v : Bool)

/-- Is the local state a `start` state? -/
def St.isStart {L : Type} : St L → Bool
  | .start _ _ => true
  | _ => false

variable (A : Alg 2 (withRW (ιS := ιS) R O)) (F : Cfg A) (k : ιS) (dec : Fin 2 → O.Op → Bool)

/-- The process whose input is decided when process `p` is poised on `k` with operation `c`. -/
def qOf (p : Fin 2) (c : O.Op) : Fin 2 := if dec p c then 0 else 1

/-- Action of process `p` (input `b`) whose simulated state is poised on `k` with `c`. -/
def decAct (p : Fin 2) (b : Bool) (c : O.Op) : Act (T' R O k) (St A.L) :=
  if qOf dec p c = p then .out b
  else .access (.inl (.inr (qOf dec p c))) RWOp.read (fun r => .done r)

/-- Action of process `p` (input `b`) simulating the action `a` of `A`. -/
def simAct (p : Fin 2) (b : Bool) : Act (withRW (ιS := ιS) R O) A.L → Act (T' R O k) (St A.L)
  | .access (.inl j) o κ => .access (.inl (.inl j)) o (fun r => .sim p b (κ r))
  | .access (.inr k') o κ =>
    if h : k' = k then decAct A k dec p b o
    else .access (.inr ⟨k', h⟩) o (fun r => .sim p b (κ r))
  | .out _ => .out b

/-- Actions of the new algorithm. -/
def act' : St A.L → Act (T' R O k) (St A.L)
  | .start p b => .access (.inl (.inr p)) (RWOp.write b) (fun _ => .sim p b (F.loc p))
  | .sim p b l => simAct A k dec p b (A.act l)
  | .done v => .out v

/-- Initial memory of the new algorithm. -/
def mem₀' : (i : (ιR ⊕ Fin 2) ⊕ {k' // k' ≠ k}) → (T' R O k i).State
  | .inl (.inl j) => F.mem (.inl j)
  | .inl (.inr _) => false
  | .inr k' => F.mem (.inr k'.1)

/-- **The new algorithm** (construction in the proof of Proposition 2). -/
@[reducible] def A' : Alg 2 (T' R O k) where
  L := St A.L
  init := .start
  act := act' A F k dec
  mem₀ := mem₀' A F k

/-- Does the local state perform a simulation step (an access to an object other than `k`)? -/
def isSim : St A.L → Bool
  | .sim _ _ l =>
    match A.act l with
    | .access (.inl _) _ _ => true
    | .access (.inr k') _ _ => decide (k' ≠ k)
    | .out _ => false
  | _ => false

/-- The simulated events of an event of the new algorithm. -/
def projEv (C' : Cfg (A' A F k dec)) : Ev 2 → List (Ev 2)
  | .step q => if isSim A k (C'.loc q) then [.step q] else []
  | .crash _ => []

/-- The simulated execution of an execution of the new algorithm. -/
def proj : Cfg (A' A F k dec) → List (Ev 2) → List (Ev 2)
  | _, [] => []
  | C', e :: α => projEv A F k dec C' e ++ proj (C'.next e) α

variable {A F k dec}

/-- Correspondence between local states. -/
def LocRel (x : Fin 2 → Bool) (p : Fin 2) : St A.L → A.L → Prop
  | .start p' b, l => p' = p ∧ b = x p ∧ l = F.loc p
  | .sim p' b l', l => p' = p ∧ b = x p ∧ l' = l
  | .done v, l => ∃ c κ, A.act l = .access (.inr k) c κ ∧ v = x (qOf dec p c)

/-- Correspondence between configurations. -/
structure Rel (x : Fin 2 → Bool) (C' : Cfg (A' A F k dec)) (D : Cfg A) : Prop where
  memR : ∀ j, C'.mem (.inl (.inl j)) = D.mem (.inl j)
  memS : ∀ k' : {k' // k' ≠ k}, C'.mem (.inr k') = D.mem (.inr k'.1)
  loc : ∀ p, LocRel (F := F) (k := k) (dec := dec) x p (C'.loc p) (D.loc p)
  reg : ∀ p, (C'.loc p).isStart = false → C'.mem (.inl (.inr p)) = x p

/-- The simulation invariant. -/
structure Inv (x : Fin 2 → Bool) (C' : Cfg (A' A F k dec)) (γ : List (Ev 2)) : Prop where
  cf : CrashFree γ
  noK : ∀ q, accCount F γ q (.inr k) = 0
  rel : Rel x C' (run F γ)
  fresh : ∀ q, (C'.loc q).isStart = true → Ev.step q ∉ γ


/-! ## Generic lemmas -/

section Generic

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {n : ℕ} {B : Alg n T}

lemma accCount_single (C : Cfg B) (p q : Fin n) (i : ι) :
    accCount C [.step p] q i = if q = p ∧ objOf C p = some i then 1 else 0 := by
  rw [accCount_cons, accCount_nil, Nat.add_zero]
  by_cases h : q = p
  · subst h; simp
  · have : (Ev.step p : Ev n) ≠ .step q := by simpa [eq_comm] using h
    simp [this, h]

lemma out_run {C : Cfg B} {p : Fin n} {v : Bool} (h : C.Out p v) {α : List (Ev n)}
    (hα : CrashFree α) : (run C α).Out p v := by
  induction α generalizing C with
  | nil => exact h
  | cons e α ih =>
    rw [run_cons]
    apply ih _ (fun q hq => hα q (by simp [hq]))
    rcases e with q | q
    · by_cases hq : q = p
      · subst hq; simp only [Cfg.next, stepP_of_out C h]; exact h
      · unfold Cfg.Out; rw [next_loc_other C _ (by simpa [eq_comm] using hq)]; exact h
    · exact absurd (by simp) (hα q)

lemma out_of_dec {C : Cfg B} {α : List (Ev n)} {v : Bool} (h : Dec C α v) (hα : CrashFree α) :
    ∃ p, (run C α).Out p v := by
  obtain ⟨m, -, p, hp⟩ := h
  refine ⟨p, ?_⟩
  rw [← List.take_append_drop m α, run_append]
  exact out_run hp (fun q hq => hα q (List.mem_of_mem_drop hq))

lemma stepP_mem_self (C : Cfg B) {p : Fin n} {i : ι} {o : (T i).Op} {κ : (T i).Resp → B.L}
    (h : B.act (C.loc p) = .access i o κ) : (C.stepP p).mem i = ((T i).δ (C.mem i) o).1 := by
  rw [stepP_of_access C h]; exact Function.update_self _ _ _

lemma stepP_mem_ne (C : Cfg B) {p : Fin n} {i : ι} {o : (T i).Op} {κ : (T i).Resp → B.L}
    (h : B.act (C.loc p) = .access i o κ) {j : ι} (hj : j ≠ i) : (C.stepP p).mem j = C.mem j := by
  rw [stepP_of_access C h]; exact Function.update_of_ne hj _ _

lemma stepP_loc_self (C : Cfg B) {p : Fin n} {i : ι} {o : (T i).Op} {κ : (T i).Resp → B.L}
    (h : B.act (C.loc p) = .access i o κ) : (C.stepP p).loc p = κ ((T i).δ (C.mem i) o).2 := by
  rw [stepP_of_access C h]; exact Function.update_self _ _ _

end Generic

/-! ## Basic facts about the new algorithm -/

variable (A F k dec) in
@[simp] lemma A'_act : (A' A F k dec).act = act' A F k dec := rfl

variable (A F k dec) in
@[simp] lemma A'_init : (A' A F k dec).init = St.start := rfl

/-- Continuations of the new algorithm never return to a `start` state. -/
lemma act'_cont_not_start {l : St A.L} {i} {o} {κ} (h : act' A F k dec l = .access i o κ) (r) :
    (κ r).isStart = false := by
  rcases l with ⟨p, b⟩ | ⟨p, b, l⟩ | v
  · simp only [act'] at h
    cases h; rfl
  · simp only [act'] at h
    rcases ha : A.act l with ⟨i', o', κ'⟩ | v
    · rw [ha] at h
      rcases i' with j | k'
      · simp only [simAct] at h
        cases h; rfl
      · by_cases hk : k' = k
        · subst hk
          simp only [simAct, dite_true, decAct] at h
          split_ifs at h
          cases h; rfl
        · simp only [simAct, hk, dite_false] at h
          cases h; rfl
    · rw [ha] at h; simp [simAct] at h
  · simp [act'] at h

variable (A F k dec) in
/-- The hypotheses (H1)–(H3) of Proposition 2, relative to the configuration `F`. -/
structure Hyp : Prop where
  H1 : ∀ γ, CrashFree γ → (∀ p, accCount F γ p (.inr k) = 0) → ∀ p v, ¬ (run F γ).Out p v
  H2 : ∀ γ, CrashFree γ → (∀ p, accCount F γ p (.inr k) = 0) →
      ∀ (c c' : O.Op) (κ κ' : O.Resp → A.L),
      A.act ((run F γ).loc 0) = .access (.inr k) c κ →
      A.act ((run F γ).loc 1) = .access (.inr k) c' κ' → dec 0 c = dec 1 c'
  H3 : ∀ p t, accCount F (solo p t) p (.inr k) = 0 → ∀ (c : O.Op) (κ : O.Resp → A.L),
      A.act ((run F (solo p t)).loc p) = .access (.inr k) c κ → qOf dec p c = p

lemma inv_init (x : Fin 2 → Bool) : Inv (F := F) (k := k) (dec := dec) x
    (initCfg (A' A F k dec) x) [] where
  cf := by simp [CrashFree]
  noK := by simp
  rel :=
    { memR := fun _ => rfl
      memS := fun _ => rfl
      loc := fun _ => ⟨rfl, rfl, rfl⟩
      reg := fun _ h => by simp [initCfg, St.isStart] at h }
  fresh := by simp

/-- The conclusion of the step lemma. -/
def StepOK (x : Fin 2 → Bool) (C' : Cfg (A' A F k dec)) (γ : List (Ev 2)) (p : Fin 2) : Prop :=
  Inv x (C'.next (.step p)) (γ ++ projEv A F k dec C' (.step p)) ∧
    ∀ q (k' : {k' // k' ≠ k}), accCount C' [.step p] q (.inr k') =
      accCount (run F γ) (projEv A F k dec C' (.step p)) q (.inr k'.1)

lemma step_noop {x : Fin 2 → Bool} {C' : Cfg (A' A F k dec)} {γ : List (Ev 2)} {p : Fin 2}
    (hI : Inv x C' γ) {v : Bool} (hout : act' A F k dec (C'.loc p) = .out v)
    (hs : isSim A k (C'.loc p) = false) : StepOK x C' γ p := by
  have hpr : projEv A F k dec C' (.step p) = [] := by simp [projEv, hs]
  have hn : C'.next (.step p) = C' := stepP_of_out C' (v := v) hout
  have hobj : objOf C' p = none := by simp [objOf, hout]
  refine ⟨?_, fun q k' => ?_⟩
  · rw [hpr, hn, List.append_nil]; exact hI
  · rw [hpr, accCount_single, hobj]; simp

lemma step_start {x : Fin 2 → Bool} {C' : Cfg (A' A F k dec)} {γ : List (Ev 2)} {p : Fin 2}
    (hI : Inv x C' γ) (hl : C'.loc p = .start p (x p)) : StepOK x C' γ p := by
  have hD : (run F γ).loc p = F.loc p := by
    have := hI.rel.loc p; rw [hl] at this; exact this.2.2
  have hpr : projEv A F k dec C' (.step p) = [] := by simp [projEv, hl, isSim]
  have hact : act' A F k dec (C'.loc p) =
      .access (.inl (.inr p)) (RWOp.write (x p)) (fun _ => .sim p (x p) (F.loc p)) := by
    rw [hl]; rfl
  have hn : C'.next (.step p) =
      { C' with loc := Function.update C'.loc p (.sim p (x p) (F.loc p))
                mem := Function.update C'.mem (.inl (.inr p)) (x p) } :=
    stepP_of_access C' hact
  have hobj : objOf C' p = some (.inl (.inr p)) := by unfold objOf; rw [A'_act, hact]
  refine ⟨?_, fun q k' => ?_⟩
  · rw [hpr, hn, List.append_nil]
    refine ⟨hI.cf, hI.noK, ⟨fun j => ?_, fun k' => ?_, fun q => ?_, fun q hq => ?_⟩, fun q hq => ?_⟩
    · exact (Function.update_of_ne (a' := .inl (.inr p)) (v := x p) (f := C'.mem) (by simp)).trans (hI.rel.memR j)
    · exact (Function.update_of_ne (a' := .inl (.inr p)) (v := x p) (f := C'.mem) (by simp)).trans (hI.rel.memS k')
    · by_cases hqp : q = p
      · subst hqp; simp [hD, LocRel]
      · simpa [hqp] using hI.rel.loc q
    · by_cases hqp : q = p
      · subst hqp; exact Function.update_self _ _ _
      · have hq' : (C'.loc q).isStart = false := by simpa [hqp] using hq
        exact (Function.update_of_ne (by simpa using hqp) _ _).trans (hI.rel.reg q hq')
    · by_cases hqp : q = p
      · subst hqp; simp [St.isStart] at hq
      · exact hI.fresh q (by simpa [hqp] using hq)
  · rw [hpr, accCount_single, hobj]; simp

lemma step_simR {x : Fin 2 → Bool} {C' : Cfg (A' A F k dec)} {γ : List (Ev 2)} {p : Fin 2}
    (hI : Inv x C' γ) {l : A.L} (hl : C'.loc p = .sim p (x p) l) (hlD : (run F γ).loc p = l)
    {j : ιR} {o : (R j).Op} {κ : (R j).Resp → A.L} (ha : A.act l = .access (.inl j) o κ) :
    StepOK x C' γ p := by
  set D := run F γ with hDdef
  have hpr : projEv A F k dec C' (.step p) = [.step p] := by simp [projEv, hl, isSim, ha]
  have hact : (A' A F k dec).act (C'.loc p) =
      .access (.inl (.inl j)) o (fun r => .sim p (x p) (κ r)) := by
    rw [hl]; show simAct A k dec p (x p) (A.act l) = _; rw [ha]; rfl
  have haD : A.act (D.loc p) = .access (.inl j) o κ := by rw [hlD]; exact ha
  have hobj : objOf C' p = some (.inl (.inl j)) := by unfold objOf; rw [hact]
  have hobjD : objOf D p = some (.inl j) := by unfold objOf; rw [haD]
  have hδ : (R j).δ (C'.mem (.inl (.inl j))) o = (R j).δ (D.mem (.inl j)) o := by
    rw [hI.rel.memR j]
  have hrun : run F (γ ++ [.step p]) = D.stepP p := by rw [run_append]; rfl
  have hnext : C'.next (.step p) = C'.stepP p := rfl
  refine ⟨?_, fun q k' => ?_⟩
  · rw [hpr, hnext]
    have hrel : Rel x (C'.stepP p) (D.stepP p) := by
      refine ⟨fun j' => ?_, fun k' => ?_, fun q => ?_, fun q hq => ?_⟩
      · by_cases hj : j' = j
        · subst hj
          exact (stepP_mem_self _ hact).trans
            ((congrArg Prod.fst hδ).trans (stepP_mem_self _ haD).symm)
        · exact (stepP_mem_ne _ hact (by simpa using hj)).trans
            ((hI.rel.memR j').trans (stepP_mem_ne _ haD (by simpa using hj)).symm)
      · exact (stepP_mem_ne _ hact (by simp)).trans
          ((hI.rel.memS k').trans (stepP_mem_ne _ haD (by simp)).symm)
      · by_cases hqp : q = p
        · subst hqp
          rw [stepP_loc_self _ hact, stepP_loc_self _ haD]
          exact ⟨rfl, rfl, congrArg (fun z => κ z.2) hδ⟩
        · rw [stepP_loc_other _ hqp, stepP_loc_other _ hqp]; exact hI.rel.loc q
      · have hq' : (C'.loc q).isStart = false := by
          by_cases hqp : q = p
          · rw [hqp, hl]; rfl
          · rwa [stepP_loc_other _ hqp] at hq
        exact (stepP_mem_ne _ hact (by simp)).trans (hI.rel.reg q hq')
    have hfresh : ∀ q, ((C'.stepP p).loc q).isStart = true → Ev.step q ∉ γ ++ [.step p] := by
      intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [stepP_loc_self _ hact] at hq; simp [St.isStart] at hq
      · rw [stepP_loc_other _ hqp] at hq
        simp [hqp, hI.fresh q hq]
    refine ⟨hI.cf.append (by simp [CrashFree]), fun q => ?_, by rw [hrun]; exact hrel, hfresh⟩
    rw [accCount_append, hI.noK q, accCount_single, ← hDdef, hobjD]; simp
  · rw [hpr, accCount_single, accCount_single, hobj, ← hDdef, hobjD]; simp

lemma step_simS {x : Fin 2 → Bool} {C' : Cfg (A' A F k dec)} {γ : List (Ev 2)} {p : Fin 2}
    (hI : Inv x C' γ) {l : A.L} (hl : C'.loc p = .sim p (x p) l) (hlD : (run F γ).loc p = l)
    {k0 : ιS} (h0 : k0 ≠ k) {o : O.Op} {κ : O.Resp → A.L}
    (ha : A.act l = .access (.inr k0) o κ) : StepOK x C' γ p := by
  set D := run F γ with hDdef
  set k1 : {k' // k' ≠ k} := ⟨k0, h0⟩ with hk1
  have hpr : projEv A F k dec C' (.step p) = [.step p] := by simp [projEv, hl, isSim, ha, h0]
  have hact : (A' A F k dec).act (C'.loc p) =
      .access (.inr k1) o (fun r => .sim p (x p) (κ r)) := by
    rw [hl]; show simAct A k dec p (x p) (A.act l) = _; rw [ha]; simp [simAct, h0]; rfl
  have haD : A.act (D.loc p) = .access (.inr k0) o κ := by rw [hlD]; exact ha
  have hobj : objOf C' p = some (.inr k1) := by unfold objOf; rw [hact]
  have hobjD : objOf D p = some (.inr k0) := by unfold objOf; rw [haD]
  have hδ : O.δ (C'.mem (.inr k1)) o = O.δ (D.mem (.inr k0)) o := by
    rw [hI.rel.memS k1]
  have hrun : run F (γ ++ [.step p]) = D.stepP p := by rw [run_append]; rfl
  have hnext : C'.next (.step p) = C'.stepP p := rfl
  refine ⟨?_, fun q k' => ?_⟩
  · rw [hpr, hnext]
    have hrel : Rel x (C'.stepP p) (D.stepP p) := by
      refine ⟨fun j' => ?_, fun k' => ?_, fun q => ?_, fun q hq => ?_⟩
      · exact (stepP_mem_ne _ hact (by simp)).trans
          ((hI.rel.memR j').trans (stepP_mem_ne _ haD (by simp)).symm)
      · by_cases hk : k' = k1
        · subst hk
          exact (stepP_mem_self _ hact).trans
            ((congrArg Prod.fst hδ).trans (stepP_mem_self _ haD).symm)
        · have hk' : k'.1 ≠ k0 := fun h => hk (Subtype.ext h)
          exact (stepP_mem_ne _ hact (by simpa using hk)).trans
            ((hI.rel.memS k').trans (stepP_mem_ne _ haD (by simpa using hk')).symm)
      · by_cases hqp : q = p
        · subst hqp
          rw [stepP_loc_self _ hact, stepP_loc_self _ haD]
          exact ⟨rfl, rfl, congrArg (fun z => κ z.2) hδ⟩
        · rw [stepP_loc_other _ hqp, stepP_loc_other _ hqp]; exact hI.rel.loc q
      · have hq' : (C'.loc q).isStart = false := by
          by_cases hqp : q = p
          · rw [hqp, hl]; rfl
          · rwa [stepP_loc_other _ hqp] at hq
        exact (stepP_mem_ne _ hact (by simp)).trans (hI.rel.reg q hq')
    have hfresh : ∀ q, ((C'.stepP p).loc q).isStart = true → Ev.step q ∉ γ ++ [.step p] := by
      intro q hq
      by_cases hqp : q = p
      · subst hqp; rw [stepP_loc_self _ hact] at hq; simp [St.isStart] at hq
      · rw [stepP_loc_other _ hqp] at hq
        simp [hqp, hI.fresh q hq]
    refine ⟨hI.cf.append (by simp [CrashFree]), fun q => ?_, by rw [hrun]; exact hrel, hfresh⟩
    rw [accCount_append, hI.noK q, accCount_single, ← hDdef, hobjD]; simp [h0]
  · rw [hpr, accCount_single, accCount_single, hobj, ← hDdef, hobjD]
    simp [hk1, Subtype.ext_iff]

lemma eq_solo_of_not_mem {γ : List (Ev 2)} (hγ : CrashFree γ) {p q : Fin 2} (hqp : q ≠ p)
    (hq : Ev.step q ∉ γ) : γ = solo p γ.length := by
  refine List.eq_replicate_iff.mpr ⟨rfl, fun e he => ?_⟩
  rcases e with r | r
  · have hrq : r ≠ q := by rintro rfl; exact hq he
    congr 1
    fin_cases r <;> fin_cases p <;> fin_cases q <;> simp_all
  · exact absurd he (hγ r)

lemma step_simK (hyp : Hyp A F k dec) {x : Fin 2 → Bool} {C' : Cfg (A' A F k dec)}
    {γ : List (Ev 2)} {p : Fin 2}
    (hI : Inv x C' γ) {l : A.L} (hl : C'.loc p = .sim p (x p) l) (hlD : (run F γ).loc p = l)
    {o : O.Op} {κ : O.Resp → A.L} (ha : A.act l = .access (.inr k) o κ) :
    StepOK x C' γ p := by
  set D := run F γ with hDdef
  have hs : isSim A k (C'.loc p) = false := by simp [hl, isSim, ha]
  have hact0 : (A' A F k dec).act (C'.loc p) = decAct A k dec p (x p) o := by
    rw [hl]; show simAct A k dec p (x p) (A.act l) = _; rw [ha]; simp [simAct]
  by_cases hq : qOf dec p o = p
  · refine step_noop hI (v := x p) ?_ hs
    rw [← A'_act, hact0]; simp [decAct, hq]
  set q := qOf dec p o with hqdef
  have haD : A.act (D.loc p) = .access (.inr k) o κ := by rw [hlD]; exact ha
  have hact : (A' A F k dec).act (C'.loc p) =
      .access (.inl (.inr q)) RWOp.read (fun r => .done r) := by
    rw [hact0]; simp [decAct, ← hqdef, hq]; rfl
  have hpr : projEv A F k dec C' (.step p) = [] := by simp [projEv, hs]
  have hobj : objOf C' p = some (.inl (.inr q)) := by unfold objOf; rw [hact]
  have hnext : C'.next (.step p) = C'.stepP p := rfl
  have hmem : ∀ i, (C'.stepP p).mem i = C'.mem i := by
    intro i
    by_cases hi : i = .inl (.inr q)
    · subst hi; exact stepP_mem_self _ hact
    · exact stepP_mem_ne _ hact hi
  -- the register of `q` holds the input of `q`
  have hreg : C'.mem (.inl (.inr q)) = x q := by
    apply hI.rel.reg q
    by_contra hst
    simp only [Bool.not_eq_false] at hst
    have hsolo := eq_solo_of_not_mem hI.cf hq (hI.fresh q hst)
    have h3 := hyp.H3 p γ.length
    rw [← hsolo] at h3
    exact hq (h3 (hI.noK p) o κ haD)
  refine ⟨?_, fun q' k' => ?_⟩
  · rw [hpr, hnext, List.append_nil]
    refine ⟨hI.cf, hI.noK, ⟨fun j' => ?_, fun k' => ?_, fun q' => ?_, fun q' hq' => ?_⟩, ?_⟩
    · exact (hmem _).trans (hI.rel.memR j')
    · exact (hmem _).trans (hI.rel.memS k')
    · by_cases hqp : q' = p
      · subst hqp
        rw [stepP_loc_self _ hact]
        exact ⟨o, κ, haD, hreg⟩
      · rw [stepP_loc_other _ hqp]; exact hI.rel.loc q'
    · have hq'' : (C'.loc q').isStart = false := by
        by_cases hqp : q' = p
        · rw [hqp, hl]; rfl
        · rwa [stepP_loc_other _ hqp] at hq'
      exact (hmem _).trans (hI.rel.reg q' hq'')
    · intro q' hq'
      by_cases hqp : q' = p
      · subst hqp; rw [stepP_loc_self _ hact] at hq'; simp [St.isStart] at hq'
      · rw [stepP_loc_other _ hqp] at hq'
        exact hI.fresh q' hq'
  · rw [hpr, accCount_single, hobj]; simp

/-- **The simulation step.** -/
lemma step (hyp : Hyp A F k dec) {x : Fin 2 → Bool} {C' : Cfg (A' A F k dec)}
    {γ : List (Ev 2)} (hI : Inv x C' γ) (p : Fin 2) : StepOK x C' γ p := by
  have hloc := hI.rel.loc p
  rcases hl : C'.loc p with ⟨p', b⟩ | ⟨p', b, l⟩ | v
  · rw [hl] at hloc
    obtain ⟨rfl, rfl, -⟩ := hloc
    exact step_start hI hl
  · rw [hl] at hloc
    obtain ⟨rfl, rfl, hlD⟩ := hloc
    rcases ha : A.act l with ⟨i, o, κ⟩ | v
    · rcases i with j | k0
      · exact step_simR hI hl hlD.symm ha
      · by_cases h0 : k0 = k
        · subst h0; exact step_simK hyp hI hl hlD.symm ha
        · exact step_simS hI hl hlD.symm h0 ha
    · refine step_noop hI (v := x p') ?_ ?_
      · rw [hl]; show simAct A k dec _ _ (A.act l) = _; rw [ha]; rfl
      · simp [hl, isSim, ha]
  · refine step_noop hI (v := v) ?_ ?_
    · rw [hl]; rfl
    · simp [hl, isSim]

/-- **The simulation invariant along executions.** -/
lemma inv_run (hyp : Hyp A F k dec) {x : Fin 2 → Bool} :
    ∀ (α : List (Ev 2)) (C' : Cfg (A' A F k dec)) (γ : List (Ev 2)), Inv x C' γ → CrashFree α →
      Inv x (run C' α) (γ ++ proj A F k dec C' α) ∧
      ∀ q (k' : {k' // k' ≠ k}), accCount C' α q (.inr k') =
        accCount (run F γ) (proj A F k dec C' α) q (.inr k'.1) := by
  intro α
  induction α with
  | nil => intro C' γ hI _; simpa [proj] using hI
  | cons e α ih =>
    intro C' γ hI hα
    rcases e with p | p
    · obtain ⟨hI', hacc⟩ := step hyp hI p
      obtain ⟨hI'', hacc'⟩ := ih _ _ hI' (fun q hq => hα q (by simp [hq]))
      refine ⟨?_, fun q k' => ?_⟩
      · rw [run_cons]; simpa [proj, List.append_assoc] using hI''
      · have e1 : accCount C' (.step p :: α) q (.inr k') =
            accCount C' [.step p] q (.inr k') + accCount (C'.next (.step p)) α q (.inr k') :=
          accCount_append C' [.step p] α q _
        rw [e1, hacc, hacc', run_append]
        show _ = accCount (run F γ) (projEv A F k dec C' (.step p) ++ proj A F k dec _ α) q _
        rw [accCount_append]
    · exact absurd (by simp) (hα p)

lemma inv_reach (hyp : Hyp A F k dec) (x : Fin 2 → Bool) {α : List (Ev 2)} (hα : CrashFree α) :
    Inv x (run (initCfg (A' A F k dec) x) α) (proj A F k dec (initCfg _ x) α) ∧
      ∀ q (k' : {k' // k' ≠ k}), accCount (initCfg (A' A F k dec) x) α q (.inr k') =
        accCount F (proj A F k dec (initCfg _ x) α) q (.inr k'.1) := by
  simpa using inv_run hyp α _ [] (inv_init x) hα

/-- **What a process outputs.** -/
lemma out_char (hyp : Hyp A F k dec) {x : Fin 2 → Bool} {C' : Cfg (A' A F k dec)}
    {γ : List (Ev 2)} (hI : Inv x C' γ) {p : Fin 2} {v : Bool} (h : C'.Out p v) :
    ∃ (c : O.Op) (κ : O.Resp → A.L),
      A.act ((run F γ).loc p) = .access (.inr k) c κ ∧ v = x (qOf dec p c) := by
  have hloc := hI.rel.loc p
  unfold Cfg.Out at h
  rcases hl : C'.loc p with ⟨p', b⟩ | ⟨p', b, l⟩ | v'
  · rw [hl] at h; simp [act'] at h
  · rw [hl] at hloc h
    obtain ⟨rfl, rfl, hlD⟩ := hloc
    change simAct A k dec _ _ (A.act l) = _ at h
    rcases ha : A.act l with ⟨i, o, κ⟩ | w
    · rw [ha] at h
      rcases i with j | k0
      · simp [simAct] at h
      · by_cases h0 : k0 = k
        · subst h0
          simp only [simAct, dite_true, decAct] at h
          split_ifs at h with hq
          · refine ⟨o, κ, by rw [← hlD]; exact ha, ?_⟩
            cases h; rw [hq]
        · simp [simAct, h0] at h
    · exact absurd (by unfold Cfg.Out; rw [← hlD]; exact ha) (hyp.H1 γ hI.cf hI.noK p' w)
  · rw [hl] at hloc h
    simp only [act'] at h
    cases h
    exact hloc

/-! ## Correctness of the new algorithm -/

theorem twoShot' (hyp : Hyp A F k dec)
    (h2F : ∀ γ, CrashFree γ → ∀ q (k'' : ιS), accCount F γ q (.inr k'') ≤ 2) :
    TwoShot (A' A F k dec) := by
  intro x α hα q k'
  rw [(inv_reach hyp x hα).2 q k']
  exact h2F _ (inv_reach hyp x hα).1.cf q k'.1

theorem allowed' (hyp : Hyp A F k dec) (m : Fin 2 → Set O.Op)
    (hmF : ∀ γ, CrashFree γ → ∀ q (k'' : ιS) (o : O.Op) (κ : O.Resp → A.L),
      A.act ((run F γ).loc q) = .access (.inr k'') o κ → o ∈ m q) :
    Allowed m (A' A F k dec) := by
  intro x α hα q k' o κ hact
  have hI := (inv_reach hyp x hα).1
  have hloc := hI.rel.loc q
  rcases hl : (run (initCfg (A' A F k dec) x) α).loc q with ⟨p', b⟩ | ⟨p', b, l⟩ | v
  · rw [hl] at hact; cases hact
  · rw [hl] at hloc hact
    obtain ⟨rfl, rfl, hlD⟩ := hloc
    change simAct A k dec _ _ (A.act l) = _ at hact
    rcases ha : A.act l with ⟨i, o', κ'⟩ | w
    · rw [ha] at hact
      rcases i with j | k0
      · cases hact
      · by_cases h0 : k0 = k
        · subst h0
          simp only [simAct, dite_true, decAct] at hact
          split_ifs at hact
          cases hact
        · simp only [simAct, h0, dite_false] at hact
          cases hact
          exact hmF _ hI.cf _ k0 _ κ' (by rw [← hlD]; exact ha)
    · rw [ha] at hact; cases hact
  · rw [hl] at hact; cases hact

theorem agree' (hyp : Hyp A F k dec) (x : Fin 2 → Bool) {α : List (Ev 2)} (hα : CrashFree α)
    {p q : Fin 2} {v w : Bool} (hv : (run (initCfg (A' A F k dec) x) α).Out p v)
    (hw : (run (initCfg (A' A F k dec) x) α).Out q w) : v = w := by
  have hI := (inv_reach hyp x hα).1
  obtain ⟨c, κ, hc, rfl⟩ := out_char hyp hI hv
  obtain ⟨c', κ', hc', rfl⟩ := out_char hyp hI hw
  by_cases hpq : p = q
  · subst hpq
    rw [hc] at hc'
    injection hc' with h1 h2 h3
    cases h2; rfl
  · have h2 := hyp.H2 _ hI.cf hI.noK
    have hp : p = 0 ∨ p = 1 := by fin_cases p <;> simp
    have hq : q = 0 ∨ q = 1 := by fin_cases q <;> simp
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd rfl hpq
    · simp only [qOf, h2 c c' κ κ' hc hc']
    · simp only [qOf, h2 c' c κ' κ hc' hc]
    · exact absurd rfl hpq

/-! ## Wait-freedom -/

lemma proj_append (C' : Cfg (A' A F k dec)) (α β : List (Ev 2)) :
    proj A F k dec C' (α ++ β) = proj A F k dec C' α ++ proj A F k dec (run C' α) β := by
  induction α generalizing C' with
  | nil => rfl
  | cons e α ih => simp [proj, ih, List.append_assoc]

lemma proj_single (C' : Cfg (A' A F k dec)) (e : Ev 2) :
    proj A F k dec C' [e] = projEv A F k dec C' e := by simp [proj]

lemma stepP_self_not_start (C' : Cfg (A' A F k dec)) (p : Fin 2) :
    ((C'.stepP p).loc p).isStart = false := by
  rcases h : act' A F k dec (C'.loc p) with ⟨i, o, κ⟩ | v
  · rw [stepP_loc_self (B := A' A F k dec) C' h]; exact act'_cont_not_start h _
  · rw [stepP_of_out C' (show C'.Out p v from h)]
    rcases hl : C'.loc p with ⟨p', b⟩ | ⟨p', b, l⟩ | v'
    · rw [hl] at h; simp [act'] at h
    · rfl
    · rfl

/-- A started process that is not about to take a simulation step outputs now or after its
next step. -/
lemma not_sim_out (C' : Cfg (A' A F k dec)) (p : Fin 2) (h1 : (C'.loc p).isStart = false)
    (h2 : isSim A k (C'.loc p) = false) :
    (∃ v, C'.Out p v) ∨ ∃ v, (C'.stepP p).Out p v := by
  unfold Cfg.Out
  rcases hl : C'.loc p with ⟨p', b⟩ | ⟨p', b, l⟩ | v
  · rw [hl] at h1; simp [St.isStart] at h1
  · rw [hl] at h2
    rcases ha : A.act l with ⟨i, o, κ⟩ | w
    · rcases i with j | k0
      · simp [isSim, ha] at h2
      · by_cases h0 : k0 = k
        · subst k0
          have hact0 : act' A F k dec (C'.loc p) = decAct A k dec p' b o := by
            rw [hl]; show simAct A k dec p' b (A.act l) = _; rw [ha]; simp [simAct]
          by_cases hq : qOf dec p' o = p'
          · left; refine ⟨b, ?_⟩; rw [← hl, A'_act, hact0]; simp [decAct, hq]
          · right
            have hact : (A' A F k dec).act (C'.loc p) =
                .access (.inl (.inr (qOf dec p' o))) RWOp.read (fun r => .done r) := by
              rw [A'_act, hact0]; simp [decAct, hq]
            exact ⟨_, by rw [stepP_loc_self _ hact]; rfl⟩
        · simp [isSim, ha, h0] at h2
    · left; refine ⟨b, ?_⟩
      show simAct A k dec p' b (A.act l) = _; rw [ha]; rfl
  · left; exact ⟨v, rfl⟩

lemma projEv_eq (C' : Cfg (A' A F k dec)) (q : Fin 2) :
    projEv A F k dec C' (.step q) = if isSim A k (C'.loc q) then [.step q] else [] := rfl

/-- **Wait-freedom of the new algorithm**: a process of the new algorithm that takes infinitely
many steps but never outputs would, after its first step, take infinitely many simulation steps;
the simulated steps form an infinite crash-free execution of `A` from `F` without access to `k`
in which that process takes infinitely many steps, so by wait-freedom of `A` it outputs —
contradicting (H1). -/
theorem prog' (hA : WFConsensus A) (hF : Reach A CrashFree F) (hyp : Hyp A F k dec)
    (x : Fin 2 → Bool) (e : ℕ → Ev 2) (p : Fin 2) (N : ℕ) (hcf : ∀ t, CrashFree (pre e t))
    (hinf : ∀ M, ∃ t ≥ M, e t = .step p) :
    ∃ t ≥ N, ∃ v, (run (initCfg (A' A F k dec) x) (pre e t)).Out p v := by
  classical
  have hcf' := (pre_crashFree_iff e).1 hcf
  set C0 := initCfg (A' A F k dec) x with hC0
  have hsucc : ∀ t, run C0 (pre e (t + 1)) = (run C0 (pre e t)).next (e t) := by
    intro t; rw [pre_succ, run_concat]
  by_contra hno
  push Not at hno
  obtain ⟨t0, ht0, he0⟩ := hinf N
  -- `p` is not in a `start` state after time `t0`
  have hns : ∀ d, ((run C0 (pre e (t0 + 1 + d))).loc p).isStart = false := by
    intro d
    induction d with
    | zero => rw [Nat.add_zero, hsucc, he0]; exact stepP_self_not_start _ p
    | succ d ih =>
      rw [← Nat.add_assoc, hsucc]
      rcases he : e (t0 + 1 + d) with q | q
      · show (((run C0 (pre e (t0 + 1 + d))).stepP q).loc p).isStart = false
        by_cases hqp : q = p
        · subst hqp; exact stepP_self_not_start _ _
        · rw [stepP_loc_other _ (Ne.symm hqp)]; exact ih
      · exact absurd he (hcf' _ q)
  -- every step of `p` after time `t0` is a simulation step
  have hsimp : ∀ t, t0 < t → e t = .step p → isSim A k ((run C0 (pre e t)).loc p) = true := by
    intro t ht he
    by_contra hs
    simp only [Bool.not_eq_true] at hs
    obtain ⟨d, rfl⟩ : ∃ d, t = t0 + 1 + d := ⟨t - (t0 + 1), by omega⟩
    rcases not_sim_out _ p (hns d) hs with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact hno _ (by omega) v hv
    · exact hno (t0 + 1 + d + 1) (by omega) v (by rw [hsucc, he]; exact hv)
  -- the times of simulation steps
  let S : ℕ → Prop := fun t => ∃ q, e t = .step q ∧ isSim A k ((run C0 (pre e t)).loc q) = true
  have hprojS : ∀ t, proj A F k dec C0 (pre e (t + 1)) =
      proj A F k dec C0 (pre e t) ++ (if S t then [e t] else []) := by
    intro t
    rw [pre_succ, proj_append, proj_single]
    congr 1
    obtain ⟨q, hq⟩ : ∃ q, e t = .step q := by
      rcases h : e t with q | q
      · exact ⟨q, rfl⟩
      · exact absurd h (hcf' t q)
    by_cases hS : S t
    · obtain ⟨q', hq', hs⟩ := hS
      rw [ite_eq_left ⟨q', hq', hs⟩, hq', projEv_eq, ite_eq_left hs]
    · rw [ite_eq_right hS, hq, projEv_eq, ite_eq_right (fun hs => hS ⟨q, hq, hs⟩)]
  have hSinf : ∀ M, ∃ t, M ≤ t ∧ S t ∧ e t = .step p := by
    intro M
    obtain ⟨t, ht, he⟩ := hinf (max M (t0 + 1))
    exact ⟨t, by omega, ⟨p, he, hsimp t (by omega) he⟩, he⟩
  have hS : ∀ t, ∃ t', t ≤ t' ∧ S t' := fun t =>
    let ⟨t', h1, h2, _⟩ := hSinf t; ⟨t', h1, h2⟩
  let nxt : ℕ → ℕ := fun t => Nat.find (hS t)
  have nxt_spec : ∀ t, t ≤ nxt t ∧ S (nxt t) := fun t => Nat.find_spec (hS t)
  have nxt_le : ∀ t t', t ≤ t' → S t' → nxt t ≤ t' := fun t t' h1 h2 =>
    Nat.find_min' (hS t) ⟨h1, h2⟩
  have nxt_min : ∀ t t', t ≤ t' → t' < nxt t → ¬ S t' := fun t t' h1 h2 hs =>
    (Nat.find_min (hS t) h2) ⟨h1, hs⟩
  let idx : ℕ → ℕ := fun j => Nat.rec (nxt 0) (fun _ i => nxt (i + 1)) j
  have idx0 : idx 0 = nxt 0 := rfl
  have idxS : ∀ j, idx (j + 1) = nxt (idx j + 1) := fun j => rfl
  have idx_mono : StrictMono idx := strictMono_nat_of_lt_succ (fun j => by
    rw [idxS]; have := (nxt_spec (idx j + 1)).1; omega)
  have hSidx : ∀ j, S (idx j) := by
    intro j
    cases j with
    | zero => exact (nxt_spec 0).2
    | succ i => exact (nxt_spec _).2
  -- the projection is constant on stretches without simulation steps
  have hconst : ∀ a d, (∀ t', a ≤ t' → t' < a + d → ¬ S t') →
      proj A F k dec C0 (pre e (a + d)) = proj A F k dec C0 (pre e a) := by
    intro a d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro h
      rw [← Nat.add_assoc, hprojS, ite_eq_right (h _ (by omega) (by omega)), List.append_nil]
      exact ih (fun t' h1 h2 => h t' h1 (by omega))
  -- the simulated execution of `A`
  let e' : ℕ → Ev 2 := fun j => e (idx j)
  have hpre : ∀ j, proj A F k dec C0 (pre e (idx j)) = pre e' j := by
    intro j
    induction j with
    | zero =>
      have := hconst 0 (nxt 0) (fun t' h1 h2 => nxt_min 0 t' h1 (by omega))
      rw [Nat.zero_add] at this
      rw [idx0, this]; rfl
    | succ j ih =>
      rw [idxS, pre_succ]
      have h1 := (nxt_spec (idx j + 1)).1
      obtain ⟨d, hd⟩ : ∃ d, nxt (idx j + 1) = idx j + 1 + d := ⟨_, (Nat.add_sub_cancel' h1).symm⟩
      rw [hd, hconst (idx j + 1) d (fun t' h1' h2' => nxt_min _ t' h1' (by omega)), hprojS, ih,
        ite_eq_left (hSidx j)]
  -- `p` takes infinitely many steps in the simulated execution
  have hinf' : ∀ M, ∃ j ≥ M, e' j = .step p := by
    intro M
    obtain ⟨t, ht, hSt, het⟩ := hSinf (idx M)
    have hex : ∃ j, t ≤ idx j := ⟨t, idx_mono.id_le t⟩
    have hdec : DecidablePred (fun j => t ≤ idx j) := Classical.decPred _
    obtain ⟨j, hj1, hjmin⟩ : ∃ j, t ≤ idx j ∧ ∀ i < j, ¬ t ≤ idx i :=
      ⟨@Nat.find _ hdec hex, @Nat.find_spec _ hdec hex, fun _ hi => @Nat.find_min _ hdec hex _ hi⟩
    have hjt : idx j = t := by
      refine le_antisymm ?_ hj1
      cases j with
      | zero => rw [idx0]; exact nxt_le 0 t (Nat.zero_le _) hSt
      | succ i =>
        have := hjmin i (by omega)
        rw [idxS]; exact nxt_le _ t (by omega) hSt
    refine ⟨j, ?_, by simp only [e', hjt, het]⟩
    by_contra hjM
    push Not at hjM
    have := idx_mono hjM
    omega
  have he'cf : ∀ t, CrashFree (pre e' t) := (pre_crashFree_iff e').2 (fun t q => hcf' (idx t) q)
  obtain ⟨t, -, v, hv⟩ := hA.prog_of_reach admOK_crashFree hF e' p 0
    (fun t => ⟨t, le_rfl, InE.of_crashFree (he'cf t) 0⟩) hinf' (fun t _ => hcf' (idx t) p)
  rw [← hpre t] at hv
  have hI := (inv_reach hyp x (hcf (idx t))).1
  exact hyp.H1 _ hI.cf hI.noK p v hv

/-- **The new algorithm solves wait-free consensus.** -/
theorem wfConsensus' (hA : WFConsensus A) (hF : Reach A CrashFree F) (hyp : Hyp A F k dec) :
    WFConsensus (A' A F k dec) where
  agree x γ hγ v w hv hw := by
    obtain ⟨p, hp⟩ := out_of_dec hv hγ
    obtain ⟨q, hq⟩ := out_of_dec hw hγ
    exact agree' hyp x hγ hp hq
  valid x γ hγ v hv := by
    obtain ⟨p, hp⟩ := out_of_dec hv hγ
    obtain ⟨c, κ, -, rfl⟩ := out_char hyp (inv_reach hyp x hγ).1 hp
    exact ⟨_, rfl⟩
  prog x e p N hcf hinf _ := prog' hA hF hyp x e p N hcf hinf

end NecRed

end TwoShotCons
