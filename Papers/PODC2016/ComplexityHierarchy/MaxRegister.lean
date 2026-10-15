import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Valency

/-!
# One max-register is not enough (Theorem 4.1 of EGSZ'16)

A *max-register* (Aspnes–Attiya–Censor) over a linearly ordered set `X` supports `read-max()`
(returns the value) and `write-max(x)` (sets the value to `max value x`, returns nothing).

`theorem_4_1`: obstruction-free binary consensus for `n ≥ 2` processes cannot be solved with a
single max-register.

Proof (the paper's interleaving argument). Let `p` have input `0` and `q` input `1` (all other
processes input `1`, they never move). From the initial configuration, `p` alone decides `0` and
`q` alone decides `1`. We interleave the two solo runs so that each process sees exactly what it
sees in its own solo run: the real memory is always `max mp mq`, where `mp`, `mq` are the values
of the register in the two solo runs. Scheduling rule: a process whose next step is a read (or its
decision) moves whenever it is safe, i.e. when its own solo value dominates the other one;
otherwise both unfinished processes are poised to `write-max`, and the one with the smaller
argument moves. The invariant (`Inv`):

* (A) a process that is not poised to write has `m_other ≤ m_self`;
* (B) a process poised to `write-max(x)` has `m_other ≤ max m_self x`.

When both have finished, both `0` and `1` have been decided: contradiction.

The paper describes the schedule in segments ("let `p` take steps until it is next poised to
perform `write-max`"); our step-by-step rule is equivalent.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

/-- Operations of a max-register. -/
inductive MaxOp (X : Type) where
  /-- `read-max()`. -/
  | read
  /-- `write-max(x)`. -/
  | write (x : X)

/-- A max-register over the linear order `X`; `write-max` returns nothing (`none`). -/
abbrev maxReg (X : Type) [LinearOrder X] [Inhabited X] : ObjSpec where
  State := X
  Op := MaxOp X
  Resp := Option X
  init := default
  δ s o := match o with
    | .read => (s, some s)
    | .write x => (max s x, none)

variable {X : Type} [LinearOrder X] [Inhabited X] {P L : Type} [DecidableEq P]
  {I : Impl BinCons (fun _ : Unit => maxReg X) P L}

/-- The argument of the next `write-max`, if the next action is one. -/
def wval (a : Action BinCons (fun _ : Unit => maxReg X) L) : Option X :=
  match a with
  | .access _ (.write x) _ => some x
  | _ => none

/-- The configuration after `p` applies `o` (continuation `k`). -/
def accCfg (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (o : MaxOp X)
    (k : Option X → L) : Config BinCons (fun _ : Unit => maxReg X) P L :=
  ⟨Function.update W.loc p (k ((maxReg X).δ (W.mem ()) o).2), W.pend,
    Function.update W.mem () ((maxReg X).δ (W.mem ()) o).1⟩

/-- The configuration after `p` returns, continuing in local state `l`. -/
def retCfg (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (l : L) :
    Config BinCons (fun _ : Unit => maxReg X) P L :=
  ⟨Function.update W.loc p l, Function.update W.pend p none, W.mem⟩

@[simp] lemma accCfg_pend (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (o : MaxOp X)
    (k : Option X → L) : (accCfg W p o k).pend = W.pend := rfl

@[simp] lemma accCfg_loc (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (o : MaxOp X)
    (k : Option X → L) :
    (accCfg W p o k).loc = Function.update W.loc p (k ((maxReg X).δ (W.mem ()) o).2) := rfl

@[simp] lemma accCfg_mem (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (o : MaxOp X)
    (k : Option X → L) : (accCfg W p o k).mem () = ((maxReg X).δ (W.mem ()) o).1 := by
  simp [accCfg]

@[simp] lemma retCfg_pend (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (l : L) :
    (retCfg W p l).pend = Function.update W.pend p none := rfl

@[simp] lemma retCfg_loc (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (l : L) :
    (retCfg W p l).loc = Function.update W.loc p l := rfl

@[simp] lemma retCfg_mem (W : Config BinCons (fun _ : Unit => maxReg X) P L) (p : P) (l : L) :
    (retCfg W p l).mem = W.mem := rfl

lemma step_access {W : Config BinCons (fun _ : Unit => maxReg X) P L} {p : P}
    (hp : W.pend p ≠ none) {o : MaxOp X} {k : Option X → L}
    (h : I.act p (W.loc p) = .access () o k) :
    I.step W (.tau p) = some (accCfg W p o k) ∧ I.soloStep p W = accCfg W p o k := by
  have h1 : I.step W (.tau p) = some (accCfg W p o k) := by
    simp [step, hp, h]; rfl
  refine ⟨h1, ?_⟩
  have hn : I.nextLabel W p = .tau p := by unfold nextLabel; rw [h]
  simp only [soloStep, hp, if_false, hn, h1, Option.getD_some]

lemma step_retp {W : Config BinCons (fun _ : Unit => maxReg X) P L} {p : P}
    (hp : W.pend p ≠ none) {r : Bool} {l : L} (h : I.act p (W.loc p) = .ret r l) :
    I.step W (.ret p r) = some (retCfg W p l) ∧ I.soloStep p W = retCfg W p l ∧
      I.nextLabel W p = .ret p r := by
  have h1 : I.step W (.ret p r) = some (retCfg W p l) := by
    simp [step, hp, h]; rfl
  have hn : I.nextLabel W p = .ret p r := by unfold nextLabel; rw [h]
  refine ⟨h1, ?_, hn⟩
  simp only [soloStep, hp, if_false, hn, h1, Option.getD_some]

/-- The invariant of the interleaving (see the module docstring). `vp`, `vq` are the solo
decisions of `p`, `q`; `a`, `b` the numbers of solo steps taken. -/
structure InvW (C₀ : Config BinCons (fun _ : Unit => maxReg X) P L) (p q : P) (vp vq : Bool)
    (Wp Wq : Config BinCons (fun _ : Unit => maxReg X) P L) (Z : Config BinCons (fun _ : Unit => maxReg X) P L)
    (ρ : List (Label P BinCons)) : Prop where
  locp : Z.loc p = Wp.loc p
  pendp : Z.pend p = Wp.pend p
  locq : Z.loc q = Wq.loc q
  pendq : Z.pend q = Wq.pend q
  mem : Z.mem () = max (Wp.mem ()) (Wq.mem ())
  run : I.runFrom C₀ ρ = some Z
  steps : Steps {p, q} ρ
  decp : Wp.pend p = none → Decides ρ vp
  decq : Wq.pend q = none → Decides ρ vq
  Ap : Wp.pend p ≠ none →
    wval (I.act p (Wp.loc p)) = none →
      Wq.mem () ≤ Wp.mem ()
  Aq : Wq.pend q ≠ none →
    wval (I.act q (Wq.loc q)) = none →
      Wp.mem () ≤ Wq.mem ()
  Bp : ∀ x, Wp.pend p ≠ none →
    wval (I.act p (Wp.loc p)) = some x →
      Wq.mem () ≤ max (Wp.mem ()) x
  Bq : ∀ y, Wq.pend q ≠ none →
    wval (I.act q (Wq.loc q)) = some y →
      Wp.mem () ≤ max (Wq.mem ()) y

/-- The invariant after `a` solo steps of `p` and `b` solo steps of `q`. -/
abbrev Inv (C₀ : Config BinCons (fun _ : Unit => maxReg X) P L) (p q : P) (vp vq : Bool)
    (a b : ℕ) (Z : Config BinCons (fun _ : Unit => maxReg X) P L)
    (ρ : List (Label P BinCons)) : Prop :=
  InvW (I := I) C₀ p q vp vq ((I.soloStep p)^[a] C₀) ((I.soloStep q)^[b] C₀) Z ρ

lemma Inv.swap {C₀ : Config BinCons (fun _ : Unit => maxReg X) P L} {p q : P} {vp vq : Bool}
    {a b : ℕ} {Z} {ρ} (h : Inv (I := I) C₀ p q vp vq a b Z ρ) :
    Inv (I := I) C₀ q p vq vp b a Z ρ :=
  ⟨h.locq, h.pendq, h.locp, h.pendp, by rw [h.mem, max_comm], h.run,
    h.steps.mono (Set.pair_comm p q).subset, h.decq, h.decp, h.Aq, h.Ap, h.Bq, h.Bp⟩

/-- One step of `p` preserves the invariant, if it is a read/decision, or a write whose argument
is at most `q`'s pending write (or `q` has finished). -/
lemma Inv.stepP {C₀ : Config BinCons (fun _ : Unit => maxReg X) P L} {p q : P} (hpq : p ≠ q)
    {vp vq : Bool} {a b : ℕ} {Z} {ρ} (h : Inv (I := I) C₀ p q vp vq a b Z ρ)
    (hvp : ∀ w, I.CanDecide {p} C₀ w → w = vp)
    (hp : ((I.soloStep p)^[a] C₀).pend p ≠ none)
    (hcond : wval (I.act p (((I.soloStep p)^[a] C₀).loc p)) = none ∨
      ∃ x, wval (I.act p (((I.soloStep p)^[a] C₀).loc p)) = some x ∧
        (((I.soloStep q)^[b] C₀).pend q = none ∨
          ∃ y, wval (I.act q (((I.soloStep q)^[b] C₀).loc q)) = some y ∧ x ≤ y)) :
    ∃ Z' ρ', Inv (I := I) C₀ p q vp vq (a + 1) b Z' ρ' := by
  classical
  unfold Inv at h ⊢
  set W := (I.soloStep p)^[a] C₀ with hW
  set Y := (I.soloStep q)^[b] C₀ with hY
  have hsucc : (I.soloStep p)^[a + 1] C₀ = I.soloStep p W := Function.iterate_succ_apply' _ _ _
  have hZp : Z.pend p ≠ none := by rw [h.pendp]; exact hp
  have hqp : q ≠ p := Ne.symm hpq
  have hρ : ∀ ℓ', ℓ'.proc = p → ℓ'.IsStep → Steps {p, q} (ρ ++ [ℓ']) := fun ℓ' h1 h2 =>
    h.steps.append (fun l hl => by simp at hl; subst hl; exact ⟨by simp [h1], h2⟩)
  rcases hact : I.act p (W.loc p) with ⟨i, o, k⟩ | ⟨r, l⟩
  · cases i
    have hactZ : I.act p (Z.loc p) = .access () o k := by rw [h.locp]; exact hact
    obtain ⟨hsW, hsoloW⟩ := step_access hp hact
    obtain ⟨hsZ, -⟩ := step_access hZp hactZ
    refine ⟨accCfg Z p o k, ρ ++ [.tau p], ?_⟩
    rw [hsucc, hsoloW]
    cases o with
    | read =>
      have hle : Y.mem () ≤ W.mem () := h.Ap hp (by simp [hact, wval])
      have hZm : Z.mem () = W.mem () := by rw [h.mem]; exact max_eq_left hle
      refine ⟨by simp [hZm], by simp [h.pendp], by simp [Function.update_of_ne hqp, h.locq],
        by simp [h.pendq], by simp [h.mem], by rw [I.runFrom_append_of_eq h.run,
        runFrom_singleton, hsZ], hρ _ rfl trivial, fun e => by simp at e; exact absurd e hp,
        fun e => (h.decq e).mono (List.subset_append_left _ _), fun _ _ => by simpa using hle,
        fun e e' => by simpa using h.Aq e e', fun x _ _ => by simp; exact Or.inl hle,
        fun y e e' => by simpa using h.Bq y e e'⟩
    | write x =>
      have hle : Y.mem () ≤ max (W.mem ()) x := h.Bp x hp (by simp [hact, wval])
      have hcond' : Y.pend q = none ∨ ∃ y, wval (I.act q (Y.loc q)) = some y ∧ x ≤ y := by
        rcases hcond with hc | ⟨x', hx', hc⟩
        · simp [hact, wval] at hc
        · simp [hact, wval] at hx'; subst hx'; exact hc
      refine ⟨by simp, by simp [h.pendp], by simp [Function.update_of_ne hqp, h.locq],
        by simp [h.pendq], by simp [h.mem, max_assoc, max_comm x], by
        rw [I.runFrom_append_of_eq h.run, runFrom_singleton, hsZ], hρ _ rfl trivial,
        fun e => by simp at e; exact absurd e hp,
        fun e => (h.decq e).mono (List.subset_append_left _ _), fun _ _ => by simpa using hle,
        fun e e' => ?_, fun x' _ _ => by rw [accCfg_mem]; exact le_max_of_le_left hle,
        fun y e e' => ?_⟩
      · rcases hcond' with hc | ⟨y, hy, -⟩
        · exact absurd hc e
        · simp [hy] at e'
      · simp only at e e' ⊢
        rcases hcond' with hc | ⟨y', hy', hxy⟩
        · exact absurd hc e
        · rw [e'] at hy'; cases hy'
          have := h.Bq y e e'
          rw [accCfg_mem]
          exact max_le this (le_max_of_le_right hxy)
  · have hactZ : I.act p (Z.loc p) = .ret r l := by rw [h.locp]; exact hact
    obtain ⟨hsW, hsoloW, hnl⟩ := step_retp hp hact
    obtain ⟨hsZ, -, -⟩ := step_retp hZp hactZ
    -- the decision is `vp`
    have hr : r = vp := by
      apply hvp
      refine ⟨I.soloLabels p C₀ (a + 1), _, soloLabels_steps p C₀ (a + 1),
        I.runFrom_soloLabels p C₀ (a + 1), p, ?_⟩
      rw [soloLabels_succ_eq_append, ← hW, if_neg hp, hnl]; simp
    refine ⟨retCfg Z p l, ρ ++ [.ret p r], ?_⟩
    rw [hsucc, hsoloW]
    refine ⟨by simp [h.locp], by simp, by simp [Function.update_of_ne hqp, h.locq],
      by simp [Function.update_of_ne hqp, h.pendq], by simp [h.mem], by
      rw [I.runFrom_append_of_eq h.run, runFrom_singleton, hsZ], hρ _ rfl trivial,
      fun _ => ⟨p, by rw [← hr]; simp⟩, fun e => (h.decq e).mono (List.subset_append_left _ _),
      fun e => by simp at e, fun e e' => by simpa using h.Aq e e', fun x e => by simp at e,
      fun y e e' => by simpa using h.Bq y e e'⟩

lemma iterate_soloStep_pend_none {p : P} {C : Config BinCons (fun _ : Unit => maxReg X) P L} {T : ℕ}
    (hT : ((I.soloStep p)^[T] C).pend p = none) : ∀ a, T ≤ a → ((I.soloStep p)^[a] C).pend p = none := by
  intro a ha
  induction a, ha using Nat.le_induction with
  | base => exact hT
  | succ a _ ih => rw [Function.iterate_succ_apply', soloStep, if_pos ih]; exact ih

/-- **Theorem 4.1** of Ellen–Gelashvili–Shavit–Zhu: it is not possible to solve obstruction-free
binary consensus for `n ≥ 2` processes using a single max-register. -/
theorem theorem_4_1 [Fintype P] (I : Impl BinCons (fun _ : Unit => maxReg X) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hn : 2 ≤ Fintype.card P) : False := by
  classical
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card hn
  let f : P → Bool := fun r => decide (r ≠ p)
  obtain ⟨C₀, h0, hC₀, -, hpend, -⟩ := I.exists_initial hall f
  have hvp : ∀ w, I.CanDecide {p} C₀ w → w = false := fun w hw =>
    (canDecide_initial hS hall f h0 hw).trans (by simp [f])
  have hvq : ∀ w, I.CanDecide {q} C₀ w → w = true := fun w hw =>
    (canDecide_initial hS hall f h0 hw).trans (by simp [f, Ne.symm hpq])
  have hfin : ∀ r, ∃ T, ((I.soloStep r)^[T] C₀).pend r = none := fun r => by
    obtain ⟨α, hα, h1, -⟩ := hC₀
    exact hof α C₀ r hα h1 (by simp [hpend])
  obtain ⟨Tp, hTp⟩ := hfin p
  obtain ⟨Tq, hTq⟩ := hfin q
  have key : ∀ μ a b Z ρ, (Tp - a) + (Tq - b) = μ →
      Inv (I := I) C₀ p q false true a b Z ρ → False := by
    intro μ
    induction μ using Nat.strong_induction_on with
    | _ μ ih =>
    intro a b Z ρ hμ h
    have stepq : ((I.soloStep q)^[b] C₀).pend q ≠ none →
        (wval (I.act q (((I.soloStep q)^[b] C₀).loc q)) = none ∨
          ∃ y, wval (I.act q (((I.soloStep q)^[b] C₀).loc q)) = some y ∧
            (((I.soloStep p)^[a] C₀).pend p = none ∨
              ∃ x, wval (I.act p (((I.soloStep p)^[a] C₀).loc p)) = some x ∧ y ≤ x)) → False := by
      intro hq hc
      have hb : b < Tq := by
        by_contra hb; exact hq (iterate_soloStep_pend_none hTq b (by omega))
      obtain ⟨Z', ρ', h'⟩ := h.swap.stepP (Ne.symm hpq) hvq hq hc
      exact ih _ (by omega) a (b + 1) Z' ρ' rfl h'.swap
    have stepp : ((I.soloStep p)^[a] C₀).pend p ≠ none →
        (wval (I.act p (((I.soloStep p)^[a] C₀).loc p)) = none ∨
          ∃ x, wval (I.act p (((I.soloStep p)^[a] C₀).loc p)) = some x ∧
            (((I.soloStep q)^[b] C₀).pend q = none ∨
              ∃ y, wval (I.act q (((I.soloStep q)^[b] C₀).loc q)) = some y ∧ x ≤ y)) → False := by
      intro hp hc
      have ha : a < Tp := by
        by_contra ha; exact hp (iterate_soloStep_pend_none hTp a (by omega))
      obtain ⟨Z', ρ', h'⟩ := h.stepP hpq hvp hp hc
      exact ih _ (by omega) (a + 1) b Z' ρ' rfl h'
    by_cases hpf : ((I.soloStep p)^[a] C₀).pend p = none
    · by_cases hqf : ((I.soloStep q)^[b] C₀).pend q = none
      · have := hC₀.decides_eq hS h.steps h.run (h.decp hpf) (h.decq hqf)
        simp at this
      · cases hwq : wval (I.act q (((I.soloStep q)^[b] C₀).loc q)) with
        | none => exact stepq hqf (Or.inl hwq)
        | some y => exact stepq hqf (Or.inr ⟨y, hwq, Or.inl hpf⟩)
    · cases hwp : wval (I.act p (((I.soloStep p)^[a] C₀).loc p)) with
      | none => exact stepp hpf (Or.inl hwp)
      | some x =>
        by_cases hqf : ((I.soloStep q)^[b] C₀).pend q = none
        · exact stepp hpf (Or.inr ⟨x, hwp, Or.inl hqf⟩)
        · cases hwq : wval (I.act q (((I.soloStep q)^[b] C₀).loc q)) with
          | none => exact stepq hqf (Or.inl hwq)
          | some y =>
            rcases le_total x y with hxy | hxy
            · exact stepp hpf (Or.inr ⟨x, hwp, Or.inr ⟨y, hwq, hxy⟩⟩)
            · exact stepq hqf (Or.inr ⟨y, hwq, Or.inr ⟨x, hwp, hxy⟩⟩)
  refine key _ 0 0 C₀ [] rfl ⟨rfl, rfl, rfl, rfl, by simp, rfl, Steps.nil _,
    fun e => by simp [hpend] at e, fun e => by simp [hpend] at e, fun _ _ => le_rfl,
    fun _ _ => le_rfl, fun x _ _ => le_max_left _ _, fun y _ _ => le_max_left _ _⟩

end Cslib.SharedMemory.ComplexityHierarchy
