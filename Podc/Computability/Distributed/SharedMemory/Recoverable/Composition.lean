import Podc.Computability.Distributed.SharedMemory.Recoverable.Safety

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Recoverable/Composition.lean

/-!
# Sequential composition: consensus from team consensus (crash-recovery model)

The classical tournament construction (Ruppert, SICOMP 2000; for recoverable consensus
Delporte-Gallet–Fatourou–Fauconnier–Ruppert, PODC'22, Proposition 30): the processes
`Fin (kA + kB)` are split into the side `A` (`Fin.castAdd kB a`) and the side `B`
(`Fin.natAdd kA b`); every process first runs a consensus algorithm of its side (`RA` or `RB`)
and then a *team consensus* algorithm `TC` for all processes, whose input is the output of the
side algorithm. After a crash a process restarts from the beginning (the side algorithm).

`comp RA RB TC` is the composed algorithm. The three algorithms use objects of the same family
`T`, but disjoint *footprints* `FA`, `FB`, `FT` (the objects each of them may access); they have
the same initial memory.

Main result: `comp_safe` — if `RA`, `RB` are safe (agreement and validity) and `TC` is safe for
inputs that are constant on the two sides, the composition is safe; `comp_ranked` — ranks
compose. The proof projects an execution of the composition onto executions of the three
components (`projCfgA`, `projCfgT`, …): the input of `TC` of a process is the value decided by
its side algorithm (`agreement` of the side algorithm makes it unique).
-/

namespace Cslib.SharedMemory.Recoverable

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec}

/-- Map the continuation of an action. -/
def Act.map {L L' : Type} (f : L → L') : Act T L → Act T L'
  | .access i o κ => .access i o (f ∘ κ)
  | .out v => .out v

@[simp] lemma Act.map_access {L L' : Type} (f : L → L') (i : ι) (o : (T i).Op)
    (κ : (T i).Resp → L) : (Act.access i o κ).map f = .access i o (f ∘ κ) := rfl

@[simp] lemma Act.map_out {L L' : Type} (f : L → L') (v : Bool) :
    (Act.out v : Act T L).map f = .out v := rfl

/-- `Function.update_self` for an arbitrary decidability instance (the instances of `Cfg.stepP`
and of the current context need not be syntactically equal). -/
@[simp] lemma update_self_inst {α β : Type*} (inst : DecidableEq α) (f : α → β) (a : α) (v : β) :
    @Function.update α (fun _ => β) inst f a v a = v := by
  simp [Function.update]

/-- `Function.update_of_ne` for an arbitrary decidability instance. -/
lemma update_of_ne_inst {α β : Type*} (inst : DecidableEq α) (f : α → β) {a b : α} (h : b ≠ a)
    (v : β) : @Function.update α (fun _ => β) inst f a v b = f b := by
  simp [Function.update, h]

lemma Cfg.ext' {n : ℕ} {A : Alg n T} {C D : Cfg A} (h1 : C.inp = D.inp) (h2 : C.loc = D.loc)
    (h3 : C.mem = D.mem) : C = D := by
  cases C; cases D; simp_all

section Comp

variable {kA kB : ℕ} (RA : Alg kA T) (RB : Alg kB T) (TC : Alg (kA + kB) T)

/-- The action of a side algorithm. -/
def compSub : RA.L ⊕ RB.L → Act T (RA.L ⊕ RB.L)
  | .inl s => (RA.act s).map Sum.inl
  | .inr s => (RB.act s).map Sum.inr

/-- The initial state of the side algorithm of `p`. -/
def compSubInit (p : Fin (kA + kB)) (x : Bool) : RA.L ⊕ RB.L :=
  Fin.addCases (motive := fun _ => RA.L ⊕ RB.L) (fun a => .inl (RA.init a x))
    (fun b => .inr (RB.init b x)) p

/-- Local states of the composition: the process, its state in the side algorithm, and its state
in the team consensus algorithm (`none`: not started). -/
abbrev CompL := Fin (kA + kB) × (RA.L ⊕ RB.L) × Option TC.L

/-- The action of the composition. A process whose side algorithm is in an output state with
value `v` runs `TC` from its initial state with input `v`. -/
def compAct : CompL RA RB TC → Act T (CompL RA RB TC)
  | (p, s, some t) => (TC.act t).map (fun t' => (p, s, some t'))
  | (p, s, none) =>
    match compSub RA RB s with
    | .access i o κ => .access i o (fun r => (p, κ r, none))
    | .out v => (TC.act (TC.init p v)).map (fun t' => (p, s, some t'))

/-- The composition of side algorithms `RA`, `RB` and a team consensus algorithm `TC`. -/
def comp : Alg (kA + kB) T where
  L := CompL RA RB TC
  init p x := (p, compSubInit RA RB p x, none)
  act := compAct RA RB TC
  mem₀ := TC.mem₀

variable {RA RB TC}

@[simp] lemma compSubInit_left (a : Fin kA) (x : Bool) :
    compSubInit RA RB (Fin.castAdd kB a) x = .inl (RA.init a x) := by
  simp [compSubInit]

@[simp] lemma compSubInit_right (b : Fin kB) (x : Bool) :
    compSubInit RA RB (Fin.natAdd kA b) x = .inr (RB.init b x) := by
  simp [compSubInit]

/-! ### Well-formed configurations -/

/-- Well-formed configurations of the composition. -/
structure CompGood (C : Cfg (comp RA RB TC)) : Prop where
  id : ∀ p, (C.loc p).1 = p
  left : ∀ a, ∃ s, (C.loc (Fin.castAdd kB a)).2.1 = .inl s
  right : ∀ b, ∃ s, (C.loc (Fin.natAdd kA b)).2.1 = .inr s
  ph2 : ∀ p t, (C.loc p).2.2 = some t → ∃ v, compSub RA RB (C.loc p).2.1 = .out v

lemma compGood_init (x : Fin (kA + kB) → Bool) : CompGood (initCfg (comp RA RB TC) x) where
  id p := rfl
  left a := ⟨RA.init a (x (Fin.castAdd kB a)), by simp [initCfg, comp]⟩
  right b := ⟨RB.init b (x (Fin.natAdd kA b)), by simp [initCfg, comp]⟩
  ph2 p t h := by simp [initCfg, comp] at h

/-- The local state of a process after its step, in terms of its action. -/
lemma comp_loc_stepP (C : Cfg (comp RA RB TC)) (p q : Fin (kA + kB)) :
    (C.stepP p).loc q = C.loc q ∨ (q = p ∧ ∃ i o κ, compAct RA RB TC (C.loc p) = .access i o κ ∧
      (C.stepP p).loc q = κ ((T i).δ (C.mem i) o).2) := by
  by_cases hq : q = p
  · subst hq
    rcases h : compAct RA RB TC (C.loc q) with ⟨i, o, κ⟩ | v
    · right
      refine ⟨rfl, i, o, κ, rfl, ?_⟩
      rw [stepP_of_access C (show (comp RA RB TC).act (C.loc q) = _ from h)]
      exact Function.update_self _ _ _
    · left
      rw [stepP_of_out C (show C.Out q v from h)]
  · left; exact stepP_loc_other C hq

/-! ### The actions of the composition -/

/-- The state of `p` in `TC` that drives its step: its `TC` state, or the initial `TC` state with
the output of its side algorithm. -/
lemma compAct_access {p : Fin (kA + kB)} {s : RA.L ⊕ RB.L} {ot : Option TC.L} {i : ι}
    {o : (T i).Op} {κ : (T i).Resp → CompL RA RB TC}
    (h : compAct RA RB TC (p, s, ot) = .access i o κ) :
    (ot = none ∧ ∃ s₀ κ₀, s = .inl s₀ ∧ RA.act s₀ = .access i o κ₀ ∧
        κ = fun r => (p, .inl (κ₀ r), none)) ∨
    (ot = none ∧ ∃ s₀ κ₀, s = .inr s₀ ∧ RB.act s₀ = .access i o κ₀ ∧
        κ = fun r => (p, .inr (κ₀ r), none)) ∨
    (∃ t₀ κ₀, TC.act t₀ = .access i o κ₀ ∧ κ = (fun r => (p, s, some (κ₀ r))) ∧
      (ot = some t₀ ∨ (ot = none ∧ ∃ v, compSub RA RB s = .out v ∧ t₀ = TC.init p v))) := by
  cases ot with
  | some t =>
    right; right
    simp only [compAct] at h
    rcases ht : TC.act t with ⟨i', o', κ'⟩ | w
    · rw [ht] at h
      simp only [Act.map_access, Act.access.injEq] at h
      obtain ⟨rfl, ho, hκ⟩ := h
      subst ho
      refine ⟨t, κ', ht, ?_, Or.inl rfl⟩
      rw [← (eq_of_heq hκ)]; rfl
    · rw [ht] at h; simp at h
  | none =>
    simp only [compAct] at h
    rcases hs : compSub RA RB s with ⟨i', o', κ'⟩ | v
    · rw [hs] at h
      simp only [Act.access.injEq] at h
      obtain ⟨rfl, ho, hκ⟩ := h
      subst ho
      have hκ := eq_of_heq hκ
      subst hκ
      cases s with
      | inl s₀ =>
        left
        refine ⟨rfl, s₀, ?_⟩
        simp only [compSub] at hs
        rcases ha : RA.act s₀ with ⟨i'', o'', κ''⟩ | w
        · rw [ha] at hs
          simp only [Act.map_access, Act.access.injEq] at hs
          obtain ⟨rfl, ho, hκ⟩ := hs
          subst ho
          refine ⟨κ'', rfl, rfl, ?_⟩
          rw [← eq_of_heq hκ]; rfl
        · rw [ha] at hs; simp at hs
      | inr s₀ =>
        right; left
        refine ⟨rfl, s₀, ?_⟩
        simp only [compSub] at hs
        rcases ha : RB.act s₀ with ⟨i'', o'', κ''⟩ | w
        · rw [ha] at hs
          simp only [Act.map_access, Act.access.injEq] at hs
          obtain ⟨rfl, ho, hκ⟩ := hs
          subst ho
          refine ⟨κ'', rfl, rfl, ?_⟩
          rw [← eq_of_heq hκ]; rfl
        · rw [ha] at hs; simp at hs
    · rw [hs] at h
      dsimp only at h
      right; right
      rcases ht : TC.act (TC.init p v) with ⟨i', o', κ'⟩ | w
      · rw [ht] at h
        simp only [Act.map_access, Act.access.injEq] at h
        obtain ⟨rfl, ho, hκ⟩ := h
        subst ho
        refine ⟨TC.init p v, κ', ht, ?_, Or.inr ⟨rfl, v, rfl, rfl⟩⟩
        rw [← (eq_of_heq hκ)]; rfl
      · rw [ht] at h; simp at h

/-- Output states of the composition are output states of `TC`. -/
lemma compAct_out {p : Fin (kA + kB)} {s : RA.L ⊕ RB.L} {ot : Option TC.L} {w : Bool}
    (h : compAct RA RB TC (p, s, ot) = .out w) :
    ∃ t₀, TC.act t₀ = .out w ∧
      (ot = some t₀ ∨ (ot = none ∧ ∃ v, compSub RA RB s = .out v ∧ t₀ = TC.init p v)) := by
  cases ot with
  | some t =>
    simp only [compAct] at h
    rcases ht : TC.act t with ⟨i', o', κ'⟩ | w'
    · rw [ht] at h; simp at h
    · rw [ht] at h; simp only [Act.map_out, Act.out.injEq] at h; subst h
      exact ⟨t, ht, Or.inl rfl⟩
  | none =>
    simp only [compAct] at h
    rcases hs : compSub RA RB s with ⟨i', o', κ'⟩ | v
    · rw [hs] at h; simp at h
    · rw [hs] at h
      dsimp only at h
      rcases ht : TC.act (TC.init p v) with ⟨i', o', κ'⟩ | w'
      · rw [ht] at h; simp at h
      · rw [ht] at h; simp only [Act.map_out, Act.out.injEq] at h; subst h
        exact ⟨_, ht, Or.inr ⟨rfl, v, rfl, rfl⟩⟩

lemma compSub_inl_out {s₀ : RA.L} {v : Bool} :
    compSub RA RB (.inl s₀) = .out v ↔ RA.act s₀ = .out v := by
  simp only [compSub]
  rcases RA.act s₀ with ⟨i, o, κ⟩ | w <;> simp

lemma compSub_inr_out {s₀ : RB.L} {v : Bool} :
    compSub RA RB (.inr s₀) = .out v ↔ RB.act s₀ = .out v := by
  simp only [compSub]
  rcases RB.act s₀ with ⟨i, o, κ⟩ | w <;> simp

/-- Well-formedness is preserved by all events. -/
lemma CompGood.next {C : Cfg (comp RA RB TC)} (hG : CompGood C) (e : Ev (kA + kB)) :
    CompGood (C.next e) := by
  have key : ∀ q, (C.next e).loc q = C.loc q ∨
      ((C.next e).loc q = (q, compSubInit RA RB q (C.inp q), none)) ∨
      (∃ i o κ, compAct RA RB TC (C.loc q) = .access i o κ ∧
        (C.next e).loc q = κ ((T i).δ (C.mem i) o).2) := by
    intro q
    rcases e with p | p
    · rcases comp_loc_stepP C p q with h | ⟨rfl, i, o, κ, h1, h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨i, o, κ, h1, h2⟩)
    · by_cases hq : q = p
      · subst hq; right; left
        simp [Cfg.next, comp]
      · left; exact next_loc_other C _ hq
  refine ⟨fun q => ?_, fun a => ?_, fun b => ?_, fun q t ht => ?_⟩
  · rcases key q with h | h | ⟨i, o, κ, h1, h2⟩
    · rw [h]; exact hG.id q
    · rw [h]
    · have hq := hG.id q
      rcases hq' : C.loc q with ⟨p, s, ot⟩
      rw [hq'] at h1 hq; simp at hq; subst hq
      rw [h2]
      rcases compAct_access h1 with ⟨-, _, _, -, -, rfl⟩ | ⟨-, _, _, -, -, rfl⟩ |
        ⟨_, _, -, rfl, -⟩ <;> rfl
  · rcases key (Fin.castAdd kB a) with h | h | ⟨i, o, κ, h1, h2⟩
    · rw [h]; exact hG.left a
    · rw [h]; simp
    · obtain ⟨s₀, hs₀⟩ := hG.left a
      rcases hq' : C.loc (Fin.castAdd kB a) with ⟨p, s, ot⟩
      rw [hq'] at h1 hs₀; simp only at hs₀; subst hs₀
      rw [h2]
      rcases compAct_access h1 with ⟨-, _, _, -, -, rfl⟩ | ⟨-, _, _, h, -, -⟩ |
        ⟨_, _, -, rfl, -⟩
      · exact ⟨_, rfl⟩
      · simp at h
      · exact ⟨_, rfl⟩
  · rcases key (Fin.natAdd kA b) with h | h | ⟨i, o, κ, h1, h2⟩
    · rw [h]; exact hG.right b
    · rw [h]; simp
    · obtain ⟨s₀, hs₀⟩ := hG.right b
      rcases hq' : C.loc (Fin.natAdd kA b) with ⟨p, s, ot⟩
      rw [hq'] at h1 hs₀; simp only at hs₀; subst hs₀
      rw [h2]
      rcases compAct_access h1 with ⟨-, _, _, h, -, -⟩ | ⟨-, _, _, -, -, rfl⟩ |
        ⟨_, _, -, rfl, -⟩
      · simp at h
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
  · rcases key q with h | h | ⟨i, o, κ, h1, h2⟩
    · rw [h] at ht ⊢; exact hG.ph2 q t ht
    · rw [h] at ht; simp at ht
    · rcases hq' : C.loc q with ⟨p, s, ot⟩
      rw [hq'] at h1
      rw [h2] at ht ⊢
      rcases compAct_access h1 with ⟨-, _, _, -, -, rfl⟩ | ⟨-, _, _, -, -, rfl⟩ |
        ⟨t₀, κ₀, -, rfl, hot⟩
      · simp at ht
      · simp at ht
      · rcases hot with rfl | ⟨-, v, hv, -⟩
        · have := hG.ph2 q t₀ (by rw [hq'])
          rw [hq'] at this; exact this
        · exact ⟨v, hv⟩

lemma CompGood.run {C : Cfg (comp RA RB TC)} (hG : CompGood C) (γ : List (Ev (kA + kB))) :
    CompGood (run C γ) := by
  induction γ generalizing C with
  | nil => exact hG
  | cons e γ ih => exact ih (hG.next e)

/-! ### Footprints and restricted memories -/

lemma restrict_update_of (F : ι → Prop) [DecidablePred F] (m m₀ : (i : ι) → (T i).State) (i : ι)
    (v : (T i).State) (hi : F i) :
    (fun j => if F j then Function.update m i v j else m₀ j) =
      Function.update (fun j => if F j then m j else m₀ j) i v := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [Function.update_of_ne hj]

lemma restrict_update_not (F : ι → Prop) [DecidablePred F] (m m₀ : (i : ι) → (T i).State)
    (i : ι) (v : (T i).State) (hi : ¬ F i) :
    (fun j => if F j then Function.update m i v j else m₀ j) =
      (fun j => if F j then m j else m₀ j) := by
  funext j
  by_cases hj : F j
  · have : j ≠ i := fun h => hi (h ▸ hj)
    rw [ite_eq_left hj, ite_eq_left hj]; exact Function.update_of_ne this _ _
  · simp [hj]

/-- The three algorithms access disjoint sets of objects `FA`, `FB`, `FT`. -/
structure Footprints (RA : Alg kA T) (RB : Alg kB T) (TC : Alg (kA + kB) T)
    (FA FB FT : ι → Prop) : Prop where
  hA : ∀ l i o κ, RA.act l = .access i o κ → FA i
  hB : ∀ l i o κ, RB.act l = .access i o κ → FB i
  hT : ∀ l i o κ, TC.act l = .access i o κ → FT i
  AB : ∀ i, FA i → ¬ FB i
  AT : ∀ i, FA i → ¬ FT i
  BT : ∀ i, FB i → ¬ FT i

/-! ### Projection onto the side algorithm `RA` -/

section ProjA

variable (FA : ι → Prop) [DecidablePred FA]

/-- The configuration of `RA` seen in a configuration of the composition. -/
def projCfgA (C : Cfg (comp RA RB TC)) : Cfg RA where
  inp a := C.inp (Fin.castAdd kB a)
  loc a := Sum.elim (fun s => s) (fun _ => RA.init a (C.inp (Fin.castAdd kB a)))
    (C.loc (Fin.castAdd kB a)).2.1
  mem i := if FA i then C.mem i else RA.mem₀ i

/-- The events of `RA` in an event of the composition. -/
def projEvA : Ev (kA + kB) → List (Ev kA)
  | .step p => Fin.addCases (motive := fun _ => List (Ev kA)) (fun a => [.step a]) (fun _ => []) p
  | .crash p => Fin.addCases (motive := fun _ => List (Ev kA)) (fun a => [.crash a]) (fun _ => [])
      p

/-- The execution of `RA` inside an execution of the composition. -/
def projA (γ : List (Ev (kA + kB))) : List (Ev kA) := γ.flatMap projEvA

lemma projA_append (γ δ : List (Ev (kA + kB))) : projA (γ ++ δ) = projA γ ++ projA δ := by
  simp [projA]

lemma projA_cons (e : Ev (kA + kB)) (γ : List (Ev (kA + kB))) :
    projA (e :: γ) = projEvA e ++ projA γ := by
  simp [projA]

lemma crashFree_projA {γ : List (Ev (kA + kB))} (h : CrashFree γ) : CrashFree (projA γ) := by
  intro a ha
  simp only [projA, List.mem_flatMap] at ha
  obtain ⟨e, he, hae⟩ := ha
  rcases e with p | p
  · induction p using Fin.addCases <;> simp [projEvA] at hae
  · induction p using Fin.addCases with
    | left a' => exact h _ he
    | right b => simp [projEvA] at hae

variable {FA}

lemma projCfgA_loc (C : Cfg (comp RA RB TC)) (a : Fin kA) :
    (projCfgA FA C).loc a = Sum.elim (fun s => s) (fun _ => RA.init a (C.inp (Fin.castAdd kB a)))
      (C.loc (Fin.castAdd kB a)).2.1 := rfl

lemma projCfgA_mem (C : Cfg (comp RA RB TC)) :
    (projCfgA FA C).mem = fun i => if FA i then C.mem i else RA.mem₀ i := rfl

/-- One event of the composition acts on the `RA`-projection as its `RA`-events. -/
lemma projCfgA_next {FB FT : ι → Prop} (hF : Footprints RA RB TC FA FB FT)
    {C : Cfg (comp RA RB TC)} (hG : CompGood C) (e : Ev (kA + kB)) :
    projCfgA FA (C.next e) = run (projCfgA FA C) (projEvA e) := by
  rcases e with p | p
  · -- a step
    induction p using Fin.addCases with
    | left a =>
      simp only [projEvA, Fin.addCases_left, run_cons, run_nil, Cfg.next]
      obtain ⟨s₀, hs₀⟩ := hG.left a
      have hid := hG.id (Fin.castAdd kB a)
      rcases hl : C.loc (Fin.castAdd kB a) with ⟨p, s, ot⟩
      rw [hl] at hs₀ hid; simp only at hs₀ hid; subst hs₀ hid
      have hpl : (projCfgA FA C).loc a = s₀ := by simp [projCfgA, hl]
      rcases hact : compAct RA RB TC (Fin.castAdd kB a, Sum.inl s₀, ot) with ⟨i, o, κ⟩ | w
      · have hact' : (comp RA RB TC).act (C.loc (Fin.castAdd kB a)) = .access i o κ := by
          rw [hl]; exact hact
        rcases compAct_access hact with ⟨-, s₁, κ₀, hs₁, hA, rfl⟩ | ⟨-, s₁, κ₀, hs₁, -, -⟩ |
          ⟨t₀, κ₀, hT, rfl, hot⟩
        · -- a step of `RA`
          cases hs₁
          have hFi := hF.hA _ _ _ _ hA
          have hA' : RA.act ((projCfgA FA C).loc a) = .access i o κ₀ := by rw [hpl]; exact hA
          refine Cfg.ext' (by funext a'; simp [projCfgA]) ?_ ?_
          · funext a'
            by_cases ha' : a' = a
            · subst ha'
              rw [projCfgA_loc, stepP_loc_self C hact', stepP_loc_self _ hA', projCfgA_mem]
              simp [hFi]
            · have : Fin.castAdd kB a' ≠ Fin.castAdd kB a := fun h => ha' (Fin.castAdd_inj.1 h)
              rw [projCfgA_loc, stepP_loc_other C this, stepP_loc_other _ ha', projCfgA_loc,
                stepP_inp]
          · rw [projCfgA_mem, stepP_mem_of_access C hact', stepP_mem_of_access _ hA',
              projCfgA_mem, restrict_update_of FA C.mem RA.mem₀ i _ hFi]
            simp [hFi]
        · cases hs₁
        · -- a step of `TC`: `RA` is in an output state
          have hFi := hF.hT _ _ _ _ hT
          have hout : ∃ v, RA.act s₀ = .out v := by
            rcases hot with rfl | ⟨-, v, hv, -⟩
            · obtain ⟨v, hv⟩ := hG.ph2 _ t₀ (by rw [hl])
              rw [hl] at hv; exact ⟨v, compSub_inl_out.1 hv⟩
            · exact ⟨v, compSub_inl_out.1 hv⟩
          obtain ⟨v, hv⟩ := hout
          rw [stepP_of_out _ (show (projCfgA FA C).Out a v by
            simp only [Cfg.Out]; rw [hpl]; exact hv)]
          refine Cfg.ext' (by funext a'; simp [projCfgA]) ?_ ?_
          · funext a'
            by_cases ha' : a' = a
            · subst ha'
              rw [projCfgA_loc, stepP_loc_self C hact', hpl]; rfl
            · have : Fin.castAdd kB a' ≠ Fin.castAdd kB a := fun h => ha' (Fin.castAdd_inj.1 h)
              rw [projCfgA_loc, stepP_loc_other C this, projCfgA_loc, stepP_inp]
          · rw [projCfgA_mem, stepP_mem_of_access C hact', projCfgA_mem,
              restrict_update_not FA C.mem RA.mem₀ i _ (fun h => hF.AT i h hFi)]
      · have hout : C.Out (Fin.castAdd kB a) w := by
          simp only [Cfg.Out]; rw [hl]; exact hact
        rw [stepP_of_out C hout]
        obtain ⟨t₀, -, hot⟩ := compAct_out hact
        have : ∃ v, RA.act s₀ = .out v := by
          rcases hot with rfl | ⟨-, v, hv, -⟩
          · obtain ⟨v, hv⟩ := hG.ph2 _ t₀ (by rw [hl])
            rw [hl] at hv; exact ⟨v, compSub_inl_out.1 hv⟩
          · exact ⟨v, compSub_inl_out.1 hv⟩
        obtain ⟨v, hv⟩ := this
        rw [stepP_of_out _ (show (projCfgA FA C).Out a v by
          simp only [Cfg.Out]; rw [hpl]; exact hv)]
    | right b =>
      simp only [projEvA, Fin.addCases_right, run_nil, Cfg.next]
      obtain ⟨s₀, hs₀⟩ := hG.right b
      rcases hl : C.loc (Fin.natAdd kA b) with ⟨p, s, ot⟩
      rw [hl] at hs₀; simp only at hs₀; subst hs₀
      rcases hact : compAct RA RB TC (p, Sum.inr s₀, ot) with ⟨i, o, κ⟩ | w
      · have hact' : (comp RA RB TC).act (C.loc (Fin.natAdd kA b)) = .access i o κ := by
          rw [hl]; exact hact
        have hnot : ¬ FA i := by
          rcases compAct_access hact with ⟨-, s₁, κ₀, hs₁, -, -⟩ | ⟨-, s₁, κ₀, -, hB, -⟩ |
            ⟨t₀, κ₀, hT, -, -⟩
          · cases hs₁
          · exact fun h => hF.AB i h (hF.hB _ _ _ _ hB)
          · exact fun h => hF.AT i h (hF.hT _ _ _ _ hT)
        refine Cfg.ext' (by funext a'; simp [projCfgA]) ?_ ?_
        · funext a'
          have : Fin.castAdd kB a' ≠ Fin.natAdd kA b := by
            intro h; have := congrArg Fin.val h; simp at this; omega
          rw [projCfgA_loc, stepP_loc_other C this, projCfgA_loc, stepP_inp]
        · rw [projCfgA_mem, stepP_mem_of_access C hact', projCfgA_mem,
            restrict_update_not FA C.mem RA.mem₀ i _ hnot]
      · rw [stepP_of_out C (show C.Out (Fin.natAdd kA b) w by
          simp only [Cfg.Out]; rw [hl]; exact hact)]
  · -- a crash
    induction p using Fin.addCases with
    | left a =>
      simp only [projEvA, Fin.addCases_left, run_cons, run_nil]
      refine Cfg.ext' (by funext a'; simp [projCfgA]) ?_ rfl
      funext a'
      by_cases ha' : a' = a
      · subst ha'
        rw [projCfgA_loc, crash_loc_self, crash_loc_self]
        simp [comp, projCfgA]
      · have : Fin.castAdd kB a' ≠ Fin.castAdd kB a := fun h => ha' (Fin.castAdd_inj.1 h)
        rw [projCfgA_loc, next_loc_other C _ (by simpa using this),
          next_loc_other _ _ (by simpa using ha'), projCfgA_loc, next_inp]
    | right b =>
      simp only [projEvA, Fin.addCases_right, run_nil]
      refine Cfg.ext' (by funext a'; simp [projCfgA]) ?_ rfl
      funext a'
      have : Fin.castAdd kB a' ≠ Fin.natAdd kA b := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      rw [projCfgA_loc, next_loc_other C _ (by simpa using this), projCfgA_loc, next_inp]

lemma projCfgA_run {FB FT : ι → Prop} (hF : Footprints RA RB TC FA FB FT)
    {C : Cfg (comp RA RB TC)} (hG : CompGood C) (γ : List (Ev (kA + kB))) :
    projCfgA FA (run C γ) = run (projCfgA FA C) (projA γ) := by
  induction γ generalizing C with
  | nil => rfl
  | cons e γ ih =>
    rw [run_cons, ih (hG.next e), projA_cons, run_append, projCfgA_next hF hG e]

lemma projCfgA_init (hmem : RA.mem₀ = TC.mem₀) (x : Fin (kA + kB) → Bool) :
    projCfgA FA (initCfg (comp RA RB TC) x) = initCfg RA (fun a => x (Fin.castAdd kB a)) := by
  refine Cfg.ext' rfl ?_ ?_
  · funext a; simp [projCfgA, initCfg, comp]
  · funext i; by_cases hi : FA i <;> simp [projCfgA, initCfg, comp, hmem]

end ProjA

/-! ### Projection onto the side algorithm `RB` -/

section ProjB

variable (FB : ι → Prop) [DecidablePred FB]

/-- The configuration of `RB` seen in a configuration of the composition. -/
def projCfgB (C : Cfg (comp RA RB TC)) : Cfg RB where
  inp b := C.inp (Fin.natAdd kA b)
  loc b := Sum.elim (fun _ => RB.init b (C.inp (Fin.natAdd kA b))) (fun s => s)
    (C.loc (Fin.natAdd kA b)).2.1
  mem i := if FB i then C.mem i else RB.mem₀ i

/-- The events of `RB` in an event of the composition. -/
def projEvB : Ev (kA + kB) → List (Ev kB)
  | .step p => Fin.addCases (motive := fun _ => List (Ev kB)) (fun _ => []) (fun b => [.step b]) p
  | .crash p => Fin.addCases (motive := fun _ => List (Ev kB)) (fun _ => []) (fun b => [.crash b])
      p

/-- The execution of `RB` inside an execution of the composition. -/
def projB (γ : List (Ev (kA + kB))) : List (Ev kB) := γ.flatMap projEvB

lemma projB_append (γ δ : List (Ev (kA + kB))) : projB (γ ++ δ) = projB γ ++ projB δ := by
  simp [projB]

lemma projB_cons (e : Ev (kA + kB)) (γ : List (Ev (kA + kB))) :
    projB (e :: γ) = projEvB e ++ projB γ := by
  simp [projB]

lemma crashFree_projB {γ : List (Ev (kA + kB))} (h : CrashFree γ) : CrashFree (projB γ) := by
  intro b hb
  simp only [projB, List.mem_flatMap] at hb
  obtain ⟨e, he, hbe⟩ := hb
  rcases e with p | p
  · induction p using Fin.addCases <;> simp [projEvB] at hbe
  · induction p using Fin.addCases with
    | left a => simp [projEvB] at hbe
    | right b' => exact h _ he

variable {FB}

lemma projCfgB_loc (C : Cfg (comp RA RB TC)) (b : Fin kB) :
    (projCfgB FB C).loc b = Sum.elim (fun _ => RB.init b (C.inp (Fin.natAdd kA b))) (fun s => s)
      (C.loc (Fin.natAdd kA b)).2.1 := rfl

lemma projCfgB_mem (C : Cfg (comp RA RB TC)) :
    (projCfgB FB C).mem = fun i => if FB i then C.mem i else RB.mem₀ i := rfl

lemma castAdd_ne_natAdd (a : Fin kA) (b : Fin kB) : Fin.castAdd kB a ≠ Fin.natAdd kA b := by
  intro h; have := congrArg Fin.val h; simp at this; omega

/-- One event of the composition acts on the `RB`-projection as its `RB`-events. -/
lemma projCfgB_next {FA FT : ι → Prop} (hF : Footprints RA RB TC FA FB FT)
    {C : Cfg (comp RA RB TC)} (hG : CompGood C) (e : Ev (kA + kB)) :
    projCfgB FB (C.next e) = run (projCfgB FB C) (projEvB e) := by
  rcases e with p | p
  · -- a step
    induction p using Fin.addCases with
    | right b =>
      simp only [projEvB, Fin.addCases_right, run_cons, run_nil, Cfg.next]
      obtain ⟨s₀, hs₀⟩ := hG.right b
      have hid := hG.id (Fin.natAdd kA b)
      rcases hl : C.loc (Fin.natAdd kA b) with ⟨p, s, ot⟩
      rw [hl] at hs₀ hid; simp only at hs₀ hid; subst hs₀ hid
      have hpl : (projCfgB FB C).loc b = s₀ := by simp [projCfgB, hl]
      rcases hact : compAct RA RB TC (Fin.natAdd kA b, Sum.inr s₀, ot) with ⟨i, o, κ⟩ | w
      · have hact' : (comp RA RB TC).act (C.loc (Fin.natAdd kA b)) = .access i o κ := by
          rw [hl]; exact hact
        rcases compAct_access hact with ⟨-, s₁, κ₀, hs₁, -, -⟩ | ⟨-, s₁, κ₀, hs₁, hB, rfl⟩ |
          ⟨t₀, κ₀, hT, rfl, hot⟩
        · cases hs₁
        · -- a step of `RB`
          cases hs₁
          have hFi := hF.hB _ _ _ _ hB
          have hB' : RB.act ((projCfgB FB C).loc b) = .access i o κ₀ := by rw [hpl]; exact hB
          refine Cfg.ext' (by funext b'; simp [projCfgB]) ?_ ?_
          · funext b'
            by_cases hb' : b' = b
            · subst hb'
              rw [projCfgB_loc, stepP_loc_self C hact', stepP_loc_self _ hB', projCfgB_mem]
              simp [hFi]
            · have : Fin.natAdd kA b' ≠ Fin.natAdd kA b := fun h => hb' ((Fin.natAdd_inj kA).1 h)
              rw [projCfgB_loc, stepP_loc_other C this, stepP_loc_other _ hb', projCfgB_loc,
                stepP_inp]
          · rw [projCfgB_mem, stepP_mem_of_access C hact', stepP_mem_of_access _ hB',
              projCfgB_mem, restrict_update_of FB C.mem RB.mem₀ i _ hFi]
            simp [hFi]
        · -- a step of `TC`: `RB` is in an output state
          have hFi := hF.hT _ _ _ _ hT
          have hout : ∃ v, RB.act s₀ = .out v := by
            rcases hot with rfl | ⟨-, v, hv, -⟩
            · obtain ⟨v, hv⟩ := hG.ph2 _ t₀ (by rw [hl])
              rw [hl] at hv; exact ⟨v, compSub_inr_out.1 hv⟩
            · exact ⟨v, compSub_inr_out.1 hv⟩
          obtain ⟨v, hv⟩ := hout
          rw [stepP_of_out _ (show (projCfgB FB C).Out b v by
            simp only [Cfg.Out]; rw [hpl]; exact hv)]
          refine Cfg.ext' (by funext b'; simp [projCfgB]) ?_ ?_
          · funext b'
            by_cases hb' : b' = b
            · subst hb'
              rw [projCfgB_loc, stepP_loc_self C hact', hpl]; rfl
            · have : Fin.natAdd kA b' ≠ Fin.natAdd kA b := fun h => hb' ((Fin.natAdd_inj kA).1 h)
              rw [projCfgB_loc, stepP_loc_other C this, projCfgB_loc, stepP_inp]
          · rw [projCfgB_mem, stepP_mem_of_access C hact', projCfgB_mem,
              restrict_update_not FB C.mem RB.mem₀ i _ (fun h => hF.BT i h hFi)]
      · have hout : C.Out (Fin.natAdd kA b) w := by
          simp only [Cfg.Out]; rw [hl]; exact hact
        rw [stepP_of_out C hout]
        obtain ⟨t₀, -, hot⟩ := compAct_out hact
        have : ∃ v, RB.act s₀ = .out v := by
          rcases hot with rfl | ⟨-, v, hv, -⟩
          · obtain ⟨v, hv⟩ := hG.ph2 _ t₀ (by rw [hl])
            rw [hl] at hv; exact ⟨v, compSub_inr_out.1 hv⟩
          · exact ⟨v, compSub_inr_out.1 hv⟩
        obtain ⟨v, hv⟩ := this
        rw [stepP_of_out _ (show (projCfgB FB C).Out b v by
          simp only [Cfg.Out]; rw [hpl]; exact hv)]
    | left a =>
      simp only [projEvB, Fin.addCases_left, run_nil, Cfg.next]
      obtain ⟨s₀, hs₀⟩ := hG.left a
      rcases hl : C.loc (Fin.castAdd kB a) with ⟨p, s, ot⟩
      rw [hl] at hs₀; simp only at hs₀; subst hs₀
      rcases hact : compAct RA RB TC (p, Sum.inl s₀, ot) with ⟨i, o, κ⟩ | w
      · have hact' : (comp RA RB TC).act (C.loc (Fin.castAdd kB a)) = .access i o κ := by
          rw [hl]; exact hact
        have hnot : ¬ FB i := by
          rcases compAct_access hact with ⟨-, s₁, κ₀, -, hA, -⟩ | ⟨-, s₁, κ₀, hs₁, -, -⟩ |
            ⟨t₀, κ₀, hT, -, -⟩
          · exact fun h => hF.AB i (hF.hA _ _ _ _ hA) h
          · cases hs₁
          · exact fun h => hF.BT i h (hF.hT _ _ _ _ hT)
        refine Cfg.ext' (by funext b'; simp [projCfgB]) ?_ ?_
        · funext b'
          rw [projCfgB_loc, stepP_loc_other C (castAdd_ne_natAdd a b').symm, projCfgB_loc,
            stepP_inp]
        · rw [projCfgB_mem, stepP_mem_of_access C hact', projCfgB_mem,
            restrict_update_not FB C.mem RB.mem₀ i _ hnot]
      · rw [stepP_of_out C (show C.Out (Fin.castAdd kB a) w by
          simp only [Cfg.Out]; rw [hl]; exact hact)]
  · -- a crash
    induction p using Fin.addCases with
    | right b =>
      simp only [projEvB, Fin.addCases_right, run_cons, run_nil]
      refine Cfg.ext' (by funext b'; simp [projCfgB]) ?_ rfl
      funext b'
      by_cases hb' : b' = b
      · subst hb'
        rw [projCfgB_loc, crash_loc_self, crash_loc_self]
        simp [comp, projCfgB]
      · have : Fin.natAdd kA b' ≠ Fin.natAdd kA b := fun h => hb' ((Fin.natAdd_inj kA).1 h)
        rw [projCfgB_loc, next_loc_other C _ (by simpa using this),
          next_loc_other _ _ (by simpa using hb'), projCfgB_loc, next_inp]
    | left a =>
      simp only [projEvB, Fin.addCases_left, run_nil]
      refine Cfg.ext' (by funext b'; simp [projCfgB]) ?_ rfl
      funext b'
      rw [projCfgB_loc, next_loc_other C _ (by simpa using (castAdd_ne_natAdd a b').symm),
        projCfgB_loc, next_inp]

lemma projCfgB_run {FA FT : ι → Prop} (hF : Footprints RA RB TC FA FB FT)
    {C : Cfg (comp RA RB TC)} (hG : CompGood C) (γ : List (Ev (kA + kB))) :
    projCfgB FB (run C γ) = run (projCfgB FB C) (projB γ) := by
  induction γ generalizing C with
  | nil => rfl
  | cons e γ ih =>
    rw [run_cons, ih (hG.next e), projB_cons, run_append, projCfgB_next hF hG e]

lemma projCfgB_init (hmem : RB.mem₀ = TC.mem₀) (x : Fin (kA + kB) → Bool) :
    projCfgB FB (initCfg (comp RA RB TC) x) = initCfg RB (fun b => x (Fin.natAdd kA b)) := by
  refine Cfg.ext' rfl ?_ ?_
  · funext b; simp [projCfgB, initCfg, comp]
  · funext i; by_cases hi : FB i <;> simp [projCfgB, initCfg, comp, hmem]

end ProjB

/-! ### Projection onto the team consensus algorithm `TC` -/

section ProjT

variable (FT : ι → Prop) [DecidablePred FT] (xT : Fin (kA + kB) → Bool)

/-- The configuration of `TC` (with inputs `xT`) seen in a configuration of the composition: a
process that has not started `TC` is in its initial `TC` state. -/
def projCfgT (C : Cfg (comp RA RB TC)) : Cfg TC where
  inp := xT
  loc p := (C.loc p).2.2.getD (TC.init p (xT p))
  mem i := if FT i then C.mem i else TC.mem₀ i

/-- The inputs `xT` are those with which the processes start `TC`. -/
def GoodD (C : Cfg (comp RA RB TC)) : Prop :=
  ∀ p v, (C.loc p).2.2 = none → compSub RA RB (C.loc p).2.1 = .out v → v = xT p

open Classical in
/-- The events of `TC` in an event of the composition (steps inside the side algorithms are
dropped). -/
noncomputable def projEvT (C : Cfg (comp RA RB TC)) : Ev (kA + kB) → List (Ev (kA + kB))
  | .crash p => [.crash p]
  | .step p => if (C.loc p).2.2 = none ∧ ∃ i o κ, compSub RA RB (C.loc p).2.1 = .access i o κ
      then [] else [.step p]

/-- The execution of `TC` inside an execution of the composition. -/
noncomputable def projT : Cfg (comp RA RB TC) → List (Ev (kA + kB)) → List (Ev (kA + kB))
  | _, [] => []
  | C, e :: γ => projEvT C e ++ projT (C.next e) γ

lemma projT_append (C : Cfg (comp RA RB TC)) (γ δ : List (Ev (kA + kB))) :
    projT C (γ ++ δ) = projT C γ ++ projT (run C γ) δ := by
  induction γ generalizing C with
  | nil => rfl
  | cons e γ ih => simp [projT, ih]

lemma crashFree_projT {C : Cfg (comp RA RB TC)} {γ : List (Ev (kA + kB))} (h : CrashFree γ) :
    CrashFree (projT C γ) := by
  induction γ generalizing C with
  | nil => intro p hp; simp [projT] at hp
  | cons e γ ih =>
    intro p hp
    simp only [projT, List.mem_append] at hp
    rcases hp with hp | hp
    · rcases e with q | q
      · simp only [projEvT] at hp
        split_ifs at hp <;> simp at hp
      · simp only [projEvT, List.mem_singleton] at hp
        exact h q (by simp)
    · exact ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) p hp

variable {FT xT}

lemma projCfgT_loc (C : Cfg (comp RA RB TC)) (p : Fin (kA + kB)) :
    (projCfgT FT xT C).loc p = (C.loc p).2.2.getD (TC.init p (xT p)) := rfl

lemma projCfgT_mem (C : Cfg (comp RA RB TC)) :
    (projCfgT FT xT C).mem = fun i => if FT i then C.mem i else TC.mem₀ i := rfl

/-- The `TC` state driving a step of the composition. -/
lemma projCfgT_loc_of {C : Cfg (comp RA RB TC)} (hD : GoodD xT C) {p : Fin (kA + kB)}
    {t₀ : TC.L} (h : (C.loc p).2.2 = some t₀ ∨ ((C.loc p).2.2 = none ∧
      ∃ v, compSub RA RB (C.loc p).2.1 = .out v ∧ t₀ = TC.init p v)) :
    (projCfgT FT xT C).loc p = t₀ := by
  rw [projCfgT_loc]
  rcases h with h | ⟨h, v, hv, rfl⟩
  · rw [h]; rfl
  · rw [h, hD p v h hv]; rfl

/-- Outputs of the composition are outputs of `TC`. -/
lemma projCfgT_out {C : Cfg (comp RA RB TC)} (hG : CompGood C) (hD : GoodD xT C)
    {p : Fin (kA + kB)} {w : Bool} (h : C.Out p w) : (projCfgT FT xT C).Out p w := by
  have hid := hG.id p
  rcases hl : C.loc p with ⟨p', s, ot⟩
  rw [hl] at hid; simp only at hid; subst p'
  have h' : compAct RA RB TC (p, s, ot) = .out w := by
    have : (comp RA RB TC).act (C.loc p) = .out w := h
    rwa [hl] at this
  obtain ⟨t₀, ht, hot⟩ := compAct_out h'
  simp only [Cfg.Out]
  rw [projCfgT_loc_of hD (t₀ := t₀) (by rw [hl]; exact hot)]
  exact ht

/-- One event of the composition acts on the `TC`-projection as its `TC`-events. -/
lemma projCfgT_next {FA FB : ι → Prop} (hF : Footprints RA RB TC FA FB FT)
    {C : Cfg (comp RA RB TC)} (hG : CompGood C) (hD : GoodD xT C) (e : Ev (kA + kB)) :
    projCfgT FT xT (C.next e) = run (projCfgT FT xT C) (projEvT C e) := by
  rcases e with p | p
  · have hid := hG.id p
    rcases hl : C.loc p with ⟨p', s, ot⟩
    rw [hl] at hid; simp only at hid; subst p'
    simp only [Cfg.next]
    rcases hact : compAct RA RB TC (p, s, ot) with ⟨i, o, κ⟩ | w
    · have hact' : (comp RA RB TC).act (C.loc p) = .access i o κ := by rw [hl]; exact hact
      rcases compAct_access hact with ⟨hot, s₀, κ₀, rfl, hA, rfl⟩ |
        ⟨hot, s₀, κ₀, rfl, hB, rfl⟩ | ⟨t₀, κ₀, hT, rfl, hot⟩
      · -- a step of `RA`: invisible to `TC`
        subst hot
        have hev : projEvT C (.step p) = [] := by
          simp only [projEvT]
          rw [ite_eq_left ⟨by rw [hl], i, o, Sum.inl ∘ κ₀, by rw [hl]; simp [compSub, hA]⟩]
        rw [hev, run_nil]
        have hFi := hF.hA _ _ _ _ hA
        refine Cfg.ext' (by simp [projCfgT]) ?_ ?_
        · funext q
          by_cases hq : q = p
          · subst hq; rw [projCfgT_loc, stepP_loc_self C hact', projCfgT_loc, hl]
          · rw [projCfgT_loc, stepP_loc_other C hq, projCfgT_loc]
        · rw [projCfgT_mem, stepP_mem_of_access C hact', projCfgT_mem,
            restrict_update_not FT C.mem TC.mem₀ i _ (hF.AT i hFi)]
      · -- a step of `RB`
        subst hot
        have hev : projEvT C (.step p) = [] := by
          simp only [projEvT]
          rw [ite_eq_left ⟨by rw [hl], i, o, Sum.inr ∘ κ₀, by rw [hl]; simp [compSub, hB]⟩]
        rw [hev, run_nil]
        have hFi := hF.hB _ _ _ _ hB
        refine Cfg.ext' (by simp [projCfgT]) ?_ ?_
        · funext q
          by_cases hq : q = p
          · subst hq; rw [projCfgT_loc, stepP_loc_self C hact', projCfgT_loc, hl]
          · rw [projCfgT_loc, stepP_loc_other C hq, projCfgT_loc]
        · rw [projCfgT_mem, stepP_mem_of_access C hact', projCfgT_mem,
            restrict_update_not FT C.mem TC.mem₀ i _ (hF.BT i hFi)]
      · -- a step of `TC`
        have hFi := hF.hT _ _ _ _ hT
        have hev : projEvT C (.step p) = [.step p] := by
          simp only [projEvT]
          rw [ite_eq_right]
          rintro ⟨h1, i', o', κ', h'⟩
          rw [hl] at h1 h'
          simp only at h1 h'
          rcases hot with h | ⟨-, v, hv, -⟩
          · rw [h] at h1; cases h1
          · rw [hv] at h'; cases h'
        rw [hev, run_cons, run_nil, Cfg.next]
        have hpl : (projCfgT FT xT C).loc p = t₀ := projCfgT_loc_of hD (by rw [hl]; exact hot)
        have hT' : TC.act ((projCfgT FT xT C).loc p) = .access i o κ₀ := by rw [hpl]; exact hT
        refine Cfg.ext' (by simp [projCfgT]) ?_ ?_
        · funext q
          by_cases hq : q = p
          · subst hq
            rw [projCfgT_loc, stepP_loc_self C hact', stepP_loc_self _ hT', projCfgT_mem]
            simp [hFi]
          · rw [projCfgT_loc, stepP_loc_other C hq, stepP_loc_other _ hq, projCfgT_loc]
        · rw [projCfgT_mem, stepP_mem_of_access C hact', stepP_mem_of_access _ hT',
            projCfgT_mem, restrict_update_of FT C.mem TC.mem₀ i _ hFi]
          simp [hFi]
    · have hout : C.Out p w := by simp only [Cfg.Out]; rw [hl]; exact hact
      rw [stepP_of_out C hout]
      obtain ⟨t₀, ht, hot⟩ := compAct_out hact
      have hpl : (projCfgT FT xT C).loc p = t₀ := projCfgT_loc_of hD (by rw [hl]; exact hot)
      simp only [projEvT]
      split_ifs
      · rfl
      · rw [run_cons, run_nil, Cfg.next, stepP_of_out _ (show (projCfgT FT xT C).Out p w by
          simp only [Cfg.Out]; rw [hpl]; exact ht)]
  · simp only [projEvT, run_cons, run_nil]
    refine Cfg.ext' (by simp [projCfgT]) ?_ rfl
    funext q
    by_cases hq : q = p
    · subst hq; simp [projCfgT, Cfg.next, comp]
    · rw [projCfgT_loc, next_loc_other C _ (by simpa using hq),
        next_loc_other _ _ (by simpa using hq), projCfgT_loc]

lemma projCfgT_run {FA FB : ι → Prop} (hF : Footprints RA RB TC FA FB FT) :
    ∀ (γ : List (Ev (kA + kB))) {C : Cfg (comp RA RB TC)}, CompGood C →
      (∀ m, GoodD xT (run C (γ.take m))) →
      projCfgT FT xT (run C γ) = run (projCfgT FT xT C) (projT C γ) := by
  intro γ
  induction γ with
  | nil => intro C _ _; rfl
  | cons e γ ih =>
    intro C hG hD
    rw [run_cons, ih (hG.next e) (fun m => by simpa using hD (m + 1)), projT, run_append,
      projCfgT_next hF hG (by simpa using hD 0) e]

lemma projCfgT_init (x : Fin (kA + kB) → Bool) :
    projCfgT FT xT (initCfg (comp RA RB TC) x) = initCfg TC xT := by
  refine Cfg.ext' rfl ?_ ?_
  · funext p; simp [projCfgT, initCfg, comp]
  · funext i; by_cases hi : FT i <;> simp [projCfgT, initCfg, comp]

end ProjT

/-! ### Safety and ranks of the composition -/

/-- Inputs constant on the two sides. -/
def SideUniform (x : Fin (kA + kB) → Bool) : Prop :=
  (∀ a a', x (Fin.castAdd kB a) = x (Fin.castAdd kB a')) ∧
    (∀ b b', x (Fin.natAdd kA b) = x (Fin.natAdd kA b'))

/-- **Composition (Proposition 30 of DFFR'22, Ruppert'00).** If the side algorithms solve
consensus (safety) and `TC` solves team consensus (safety for side-uniform inputs), with disjoint
footprints and a common initial memory, the composition is safe. -/
theorem comp_safe (b : Bool) {FA FB FT : ι → Prop} [DecidablePred FA] [DecidablePred FB]
    [DecidablePred FT] (hF : Footprints RA RB TC FA FB FT) (hmA : RA.mem₀ = TC.mem₀)
    (hmB : RB.mem₀ = TC.mem₀) (hkA : 0 < kA) (hkB : 0 < kB)
    (hA : Safe RA (fun _ => True) (AdmB b)) (hB : Safe RB (fun _ => True) (AdmB b))
    (hT : Safe TC SideUniform (AdmB b)) : Safe (comp RA RB TC) (fun _ => True) (AdmB b) := by
  classical
  -- the analysis of one execution
  suffices key : ∀ x γ, AdmB b γ → ∃ xT : Fin (kA + kB) → Bool, SideUniform xT ∧
      (∀ q, ∃ p, x p = xT q) ∧ AdmB b (projT (initCfg (comp RA RB TC) x) γ) ∧
      ∀ v, Dec (initCfg (comp RA RB TC) x) γ v →
        Dec (initCfg TC xT) (projT (initCfg (comp RA RB TC) x) γ) v by
    refine ⟨fun x _ γ hγ v w hv hw => ?_, fun x _ γ hγ v hv => ?_⟩
    · obtain ⟨xT, hu, -, hadm, hdec⟩ := key x γ hγ
      exact hT.agree xT hu _ hadm v w (hdec v hv) (hdec w hw)
    · obtain ⟨xT, hu, hval, hadm, hdec⟩ := key x γ hγ
      obtain ⟨q, hq⟩ := hT.valid xT hu _ hadm v (hdec v hv)
      obtain ⟨p, hp⟩ := hval q
      exact ⟨p, hp.trans hq⟩
  intro x γ hγ
  set C₀ := initCfg (comp RA RB TC) x
  have hG₀ : CompGood C₀ := compGood_init x
  set xA : Fin kA → Bool := fun a => x (Fin.castAdd kB a)
  set xB : Fin kB → Bool := fun b => x (Fin.natAdd kA b)
  have hγA : AdmB b (projA γ) := hγ.imp id crashFree_projA
  have hγB : AdmB b (projB γ) := hγ.imp id crashFree_projB
  -- the decisions of the side algorithms
  let dA : Bool := if h : ∃ v, Dec (initCfg RA xA) (projA γ) v then h.choose else
    x (Fin.castAdd kB ⟨0, hkA⟩)
  let dB : Bool := if h : ∃ v, Dec (initCfg RB xB) (projB γ) v then h.choose else
    x (Fin.natAdd kA ⟨0, hkB⟩)
  have hdA : ∀ v, Dec (initCfg RA xA) (projA γ) v → v = dA := by
    intro v hv
    have h : ∃ v, Dec (initCfg RA xA) (projA γ) v := ⟨v, hv⟩
    simp only [dA, dite_eq_left h]
    exact hA.agree xA trivial _ hγA v _ hv h.choose_spec
  have hdB : ∀ v, Dec (initCfg RB xB) (projB γ) v → v = dB := by
    intro v hv
    have h : ∃ v, Dec (initCfg RB xB) (projB γ) v := ⟨v, hv⟩
    simp only [dB, dite_eq_left h]
    exact hB.agree xB trivial _ hγB v _ hv h.choose_spec
  let xT : Fin (kA + kB) → Bool := Fin.addCases (motive := fun _ => Bool) (fun _ => dA)
    (fun _ => dB)
  -- the starting values of `TC`
  have hD : ∀ m, GoodD xT (run C₀ (γ.take m)) := by
    intro m p v hnone hout
    have hG := hG₀.run (γ.take m)
    have hsplit : γ = γ.take m ++ γ.drop m := (List.take_append_drop m γ).symm
    induction p using Fin.addCases with
    | left a =>
      obtain ⟨s₀, hs₀⟩ := hG.left a
      rw [hs₀, compSub_inl_out] at hout
      have h1 : (projCfgA FA (run C₀ (γ.take m))).Out a v := by
        simp only [Cfg.Out, projCfgA_loc, hs₀, Sum.elim_inl]; exact hout
      rw [projCfgA_run hF hG₀, projCfgA_init hmA] at h1
      have h2 : Dec (initCfg RA xA) (projA γ) v := by
        rw [hsplit, projA_append]; exact (Dec.of_out h1).append_right _
      simpa [xT] using hdA v h2
    | right b' =>
      obtain ⟨s₀, hs₀⟩ := hG.right b'
      rw [hs₀, compSub_inr_out] at hout
      have h1 : (projCfgB FB (run C₀ (γ.take m))).Out b' v := by
        simp only [Cfg.Out, projCfgB_loc, hs₀, Sum.elim_inr]; exact hout
      rw [projCfgB_run hF hG₀, projCfgB_init hmB] at h1
      have h2 : Dec (initCfg RB xB) (projB γ) v := by
        rw [hsplit, projB_append]; exact (Dec.of_out h1).append_right _
      simpa [xT] using hdB v h2
  refine ⟨xT, ⟨fun a a' => by simp [xT], fun b b' => by simp [xT]⟩, fun q => ?_,
    hγ.imp id crashFree_projT, fun v hv => ?_⟩
  · -- validity of the starting values
    induction q using Fin.addCases with
    | left a =>
      simp only [xT, Fin.addCases_left, dA]
      split_ifs with h
      · obtain ⟨a', ha'⟩ := hA.valid xA trivial _ hγA _ h.choose_spec
        exact ⟨_, ha'⟩
      · exact ⟨_, rfl⟩
    | right b' =>
      simp only [xT, Fin.addCases_right, dB]
      split_ifs with h
      · obtain ⟨b'', hb''⟩ := hB.valid xB trivial _ hγB _ h.choose_spec
        exact ⟨_, hb''⟩
      · exact ⟨_, rfl⟩
  · -- decisions of the composition are decisions of `TC`
    obtain ⟨m, hm, p, hp⟩ := hv
    have hout := projCfgT_out (FT := FT) (hG₀.run _) (hD m) hp
    rw [projCfgT_run hF (γ.take m) hG₀ (fun m' => by rw [List.take_take]; exact hD _),
      projCfgT_init] at hout
    rw [← List.take_append_drop m γ, projT_append]
    exact (Dec.of_out hout).append_right _

/-- Ranks compose. -/
theorem comp_ranked (hA : Ranked RA) (hB : Ranked RB) (hT : Ranked TC) :
    Ranked (comp RA RB TC) := by
  classical
  obtain ⟨rA, hrA⟩ := hA
  obtain ⟨rB, hrB⟩ := hB
  obtain ⟨rT, hrT⟩ := hT
  set M := (Finset.univ : Finset (Fin (kA + kB) × Bool)).sup fun pv => rT (TC.init pv.1 pv.2)
  have hM : ∀ p v, rT (TC.init p v) ≤ M := fun p v =>
    Finset.le_sup (f := fun pv : Fin (kA + kB) × Bool => rT (TC.init pv.1 pv.2))
      (Finset.mem_univ (p, v))
  let rank : CompL RA RB TC → ℕ := fun l => match l.2.2 with
    | some t => rT t
    | none => Sum.elim rA rB l.2.1 + M + 1
  refine ⟨rank, fun l i o κ r h => ?_⟩
  obtain ⟨p, s, ot⟩ := l
  rcases compAct_access h with ⟨rfl, s₀, κ₀, rfl, hA, rfl⟩ | ⟨rfl, s₀, κ₀, rfl, hB, rfl⟩ |
    ⟨t₀, κ₀, hT, rfl, hot⟩
  · simp only [rank, Sum.elim_inl]; have := hrA _ _ _ _ r hA; omega
  · simp only [rank, Sum.elim_inr]; have := hrB _ _ _ _ r hB; omega
  · have := hrT _ _ _ _ r hT
    rcases hot with rfl | ⟨rfl, v, -, rfl⟩
    · simp only [rank]; exact this
    · simp only [rank]; have := hM p v; omega


end Comp

/-! ## The trivial one-process algorithm and the tournament -/

section Tournament

/-- The one-process algorithm that outputs its input (no shared objects are accessed). -/
def trivAlg (M : (i : ι) → (T i).State) : Alg 1 T where
  L := Bool
  init _ x := x
  act v := .out v
  mem₀ := M

lemma trivAlg_run (M : (i : ι) → (T i).State) (x : Fin 1 → Bool) (γ : List (Ev 1)) :
    run (initCfg (trivAlg M) x) γ = initCfg (trivAlg M) x := by
  induction γ using List.reverseRecOn with
  | nil => rfl
  | append_singleton γ e ih =>
    rw [run_concat, ih]
    rcases e with p | p
    · exact stepP_of_out (initCfg (trivAlg M) x) (p := p) (v := x p) rfl
    · refine Cfg.ext' rfl ?_ rfl
      funext q
      have : q = p := Subsingleton.elim _ _
      subst this
      simp [initCfg, trivAlg]

theorem trivAlg_safe (M : (i : ι) → (T i).State) (Good : (Fin 1 → Bool) → Prop)
    (Adm : List (Ev 1) → Prop) : Safe (trivAlg M) Good Adm := by
  have key : ∀ x γ v, Dec (initCfg (trivAlg M) x) γ v → v = x 0 := by
    intro x γ v ⟨m, _, p, hp⟩
    rw [trivAlg_run] at hp
    have : p = 0 := Subsingleton.elim _ _
    subst this
    simpa [Cfg.Out, initCfg, trivAlg] using hp.symm
  exact ⟨fun x _ γ _ v w hv hw => (key x γ v hv).trans (key x γ w hw).symm,
    fun x _ γ _ v hv => ⟨0, (key x γ v hv).symm⟩⟩

theorem trivAlg_ranked (M : (i : ι) → (T i).State) : Ranked (trivAlg M) :=
  ⟨fun _ => 0, fun l i o κ r h => by simp [trivAlg] at h⟩

/-- **Tournament (DFFR'22, Proposition 30; Ruppert'00).** Objects are allotted to the nodes of a
binary tree (paths `π : List Bool`): `FP π` are the objects of the subtree of `π`, `FN π ⊆ FP π`
those of the node itself, disjoint from the two subtrees. If for every `k' ≤ k` (`k' ≥ 2`) there
is a split `k' = kA + kB` (`kA, kB ≥ 1`) and, at every node, a safe and ranked team consensus
algorithm for that split using the objects of the node, then there is a safe and ranked consensus
algorithm for `k` processes using the objects of any subtree. -/
theorem tournament (b : Bool) (M : (i : ι) → (T i).State) (FP FN : List Bool → ι → Prop)
    (hN : ∀ π i, FN π i → FP π i) (hsub : ∀ π c i, FP (π ++ [c]) i → FP π i)
    (hdis : ∀ π i, FP (π ++ [false]) i → ¬ FP (π ++ [true]) i)
    (hdisN : ∀ π c i, FP (π ++ [c]) i → ¬ FN π i) :
    ∀ k, 1 ≤ k → (∀ k', 2 ≤ k' → k' ≤ k → ∃ kA kB, 1 ≤ kA ∧ 1 ≤ kB ∧ kA + kB = k' ∧
      ∀ π, ∃ TC : Alg (kA + kB) T, TC.mem₀ = M ∧
        (∀ l i o κ, TC.act l = .access i o κ → FN π i) ∧ Safe TC SideUniform (AdmB b) ∧
        Ranked TC) →
    ∀ π, ∃ A : Alg k T, A.mem₀ = M ∧ (∀ l i o κ, A.act l = .access i o κ → FP π i) ∧
      Safe A (fun _ => True) (AdmB b) ∧ Ranked A := by
  classical
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hsplit π
    by_cases hk1 : k = 1
    · subst hk1
      exact ⟨trivAlg M, rfl, fun l i o κ h => by simp [trivAlg] at h, trivAlg_safe M _ _,
        trivAlg_ranked M⟩
    obtain ⟨kA, kB, hkA, hkB, rfl, hTC⟩ := hsplit k (by omega) le_rfl
    obtain ⟨RA, hmA, hfA, hsA, hrA⟩ := ih kA (by omega) hkA
      (fun k' h1 h2 => hsplit k' h1 (by omega)) (π ++ [false])
    obtain ⟨RB, hmB, hfB, hsB, hrB⟩ := ih kB (by omega) hkB
      (fun k' h1 h2 => hsplit k' h1 (by omega)) (π ++ [true])
    obtain ⟨TC, hmT, hfT, hsT, hrT⟩ := hTC π
    have hF : Footprints RA RB TC (FP (π ++ [false])) (FP (π ++ [true])) (FN π) :=
      ⟨hfA, hfB, hfT, hdis π, fun i h => hdisN π false i h, fun i h => hdisN π true i h⟩
    refine ⟨comp RA RB TC, hmT, fun l i o κ h => ?_,
      comp_safe b hF (hmA.trans hmT.symm) (hmB.trans hmT.symm) hkA hkB hsA hsB hsT,
      comp_ranked hrA hrB hrT⟩
    obtain ⟨p, s, ot⟩ := l
    rcases compAct_access h with ⟨-, s₀, κ₀, -, h', -⟩ | ⟨-, s₀, κ₀, -, h', -⟩ |
      ⟨t₀, κ₀, h', -, -⟩
    · exact hsub π false i (hfA _ _ _ _ h')
    · exact hsub π true i (hfB _ _ _ _ h')
    · exact hN π i (hfT _ _ _ _ h')

end Tournament

end Cslib.SharedMemory.Recoverable
