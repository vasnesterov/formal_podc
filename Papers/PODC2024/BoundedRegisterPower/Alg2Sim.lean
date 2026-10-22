import Papers.PODC2024.BoundedRegisterPower.Alg2

/-!
# Algorithm 2: simulation of the ε-agreement black box and basic invariants

Every finite execution of `alg2 E PS` projects to an execution of `E`: the processes that have
not yet started `E` (states `wIn`, `rIn`) are in their initial `E`-state for the input they will
use (`x'`), the processes running `E` (`sub`) are in the corresponding `E`-state, and processes
that left `E` (`post`, `done`) have `E`-output `d`. The registers `some i` of `alg2` are the
registers of `E`. Since the `E`-input of a process is only fixed when it starts `E` (after reading
`I_other`), the statement is for every input vector `x'` of `E` consistent with the started
processes (`SimInputs`).
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

set_option linter.unusedSectionVars false

variable {In O : Type} {KE : Type} [DecidableEq KE] {VE : KE → Type}
  {Δ : (Bool → In) → (Bool → O) → Prop} {L : ℕ}

/-- The value read at line 3, for processes that already read it. -/
def xoOf {S : Type} : St2 S In → Option (Option In)
  | .sub _ xo _ | .post _ xo _ _ | .done _ xo _ _ => some xo
  | _ => none

/-- The task input recorded in the local state. -/
def xOf {S : Type} : St2 S In → In
  | .wIn x | .rIn x | .sub x _ _ | .post x _ _ _ | .done x _ _ _ => x

/-- The `E`-input vector `x'` is consistent with the processes that started `E`. -/
def SimInputs {S : Type} (loc : Bool → St2 S In) (x' : Bool → Bool) : Prop :=
  ∀ p xo, xoOf (loc p) = some xo → x' p = myIn xo

variable (E : Alg Bool KE VE Bool ℕ) (PS : PathSystem Δ L)

/-- Phase-dependent part of the simulation relation for process `p` in state `s`. -/
def PhaseOK (x' : Bool → Bool) (B : ℕ) (D : Config E) (τ σ : List Bool) (p : Bool) :
    St2 E.S In → Prop
  | .wIn _ => D.loc p = E.init p (x' p) ∧ D.out p = none ∧ σ.count p = 0
  | .rIn _ => D.loc p = E.init p (x' p) ∧ D.out p = none ∧ σ.count p = 1
  | .sub _ _ s => D.loc p = s ∧ D.out p = none ∧ σ.count p = τ.count p + 2
  | .post _ _ d _ => D.out p = some d ∧ σ.count p = τ.count p + 2 ∧ τ.count p ≤ B
  | .done _ _ d _ => D.out p = some d

/-- The simulation relation between a configuration `C` of Algorithm 2 reached by `σ` and the
configuration `D` of `E` reached by `τ` from the inputs `x'`. -/
structure SimRel (x' : Bool → Bool) (B : ℕ) (C : Config (alg2 E PS)) (D : Config E)
    (τ σ : List Bool) : Prop where
  mem : ∀ p i, C.mem p (some i) = D.mem p i
  started : ∀ p, p ∈ τ → xoOf (C.loc p) ≠ none
  phase : ∀ p, PhaseOK E x' B D τ σ p (C.loc p)

/-- The output of a process in state `s`. -/
def out2Of (p : Bool) : St2 E.S In → Option O
  | .done x xo d xo2 => some (out2 PS p x xo d xo2)
  | _ => none

/-- Invariants of Algorithm 2 that do not mention `E`'s configuration. -/
structure Inv2 (X : Bool → In) (C : Config (alg2 E PS)) : Prop where
  regI : ∀ p, C.mem p none = match C.loc p with | .wIn _ => none | _ => some (X p)
  xOf_eq : ∀ p, xOf (C.loc p) = X p
  xo : ∀ p xo, xoOf (C.loc p) = some xo → xo = none ∨ xo = some (X (!p))
  notBoth : ∀ p, xoOf (C.loc p) = some none → xoOf (C.loc (!p)) ≠ some none
  xo2 : ∀ p x xo d xo2, (C.loc p = .post x xo d xo2 ∨ C.loc p = .done x xo d xo2) →
    0 < d → d < L → xo2 = some (X (!p))
  out : ∀ p, C.out p = out2Of E PS p (C.loc p)

/-- Black-box properties of the ε-agreement algorithm `E` used by Algorithm 2. -/
structure EBox (E : Alg Bool KE VE Bool ℕ) (L B : ℕ) : Prop where
  /-- `E` solves `1/L`-agreement (safety). -/
  safe : ∀ x τ, epsAgreement L x (E.run (E.initCfg x) τ).out
  /-- Lemma 5.6: the extreme decisions `0` and `L` are only taken by processes with input
  `0` and `1` respectively. -/
  zero : ∀ x τ p, (E.run (E.initCfg x) τ).out p = some 0 → x p = false
  one : ∀ x τ p, (E.run (E.initCfg x) τ).out p = some L → x p = true
  /-- A decision strictly between `0` and `L` requires distinct inputs and a step of the other
  process. -/
  mid : ∀ x τ p m, (E.run (E.initCfg x) τ).out p = some m → 0 < m → m < L →
    x p ≠ x (!p) ∧ (!p) ∈ τ
  /-- Step complexity: after `B` steps a process has decided. -/
  bound : ∀ x τ p, B ≤ τ.count p → ((E.run (E.initCfg x) τ).out p).isSome

variable {E PS}

/-! ### One step of Algorithm 2 -/

section Step

variable {B : ℕ} {X : Bool → In} {σ : List Bool} {C : Config (alg2 E PS)}

lemma count_concat_self (σ : List Bool) (p : Bool) : (σ ++ [p]).count p = σ.count p + 1 := by
  simp

lemma count_concat_ne (σ : List Bool) {p q : Bool} (h : q ≠ p) :
    (σ ++ [p]).count q = σ.count q := by
  simp [List.count_cons]; exact fun e => h e.symm

lemma ne_not (p : Bool) : (!p) ≠ p := by cases p <;> decide

lemma eq_not_of_ne {p q : Bool} (h : q ≠ p) : q = !p := by
  cases p <;> cases q <;> simp_all

/-- Inputs consistent after a step are consistent before it, provided the step of `p` keeps the
value `xo` of a started process. -/
lemma simInputs_of_step {C' : Config (alg2 E PS)} {p : Bool} (x' : Bool → Bool)
    (hne : ∀ q, q ≠ p → C'.loc q = C.loc q)
    (hp : ∀ xo, xoOf (C.loc p) = some xo → xoOf (C'.loc p) = some xo)
    (h : SimInputs C'.loc x') : SimInputs C.loc x' := by
  intro q xo hq
  by_cases hqp : q = p
  · subst hqp; exact h q xo (hp xo hq)
  · exact h q xo (by rw [hne q hqp]; exact hq)

lemma phaseOK_frame {x' : Bool → Bool} {D D' : Config E} {τ τ' σ σ' : List Bool} {q : Bool}
    (s : St2 E.S In) (hl : D'.loc q = D.loc q) (ho : D'.out q = D.out q)
    (hτ : τ'.count q = τ.count q) (hσ : σ'.count q = σ.count q)
    (h : PhaseOK E x' B D τ σ q s) : PhaseOK E x' B D' τ' σ' q s := by
  cases s <;> simp only [PhaseOK, hl, ho, hτ, hσ] at h ⊢ <;> exact h

/-- Frame lemma for the simulation relation: only process `p` moved. -/
lemma SimRel.frame {x' : Bool → Bool} {D D' : Config E} {τ τ' : List Bool}
    {C' : Config (alg2 E PS)} {p : Bool} (h : SimRel E PS x' B C D τ σ)
    (hCl : ∀ q, q ≠ p → C'.loc q = C.loc q) (hCm : ∀ q, q ≠ p → C'.mem q = C.mem q)
    (hDl : ∀ q, q ≠ p → D'.loc q = D.loc q) (hDm : ∀ q, q ≠ p → D'.mem q = D.mem q)
    (hDo : ∀ q, q ≠ p → D'.out q = D.out q) (hτc : ∀ q, q ≠ p → τ'.count q = τ.count q)
    (hτm : ∀ q, q ≠ p → q ∈ τ' → q ∈ τ)
    (hmem : ∀ i, C'.mem p (some i) = D'.mem p i) (hst : p ∈ τ' → xoOf (C'.loc p) ≠ none)
    (hph : PhaseOK E x' B D' τ' (σ ++ [p]) p (C'.loc p)) :
    SimRel E PS x' B C' D' τ' (σ ++ [p]) := by
  refine ⟨fun q i => ?_, fun q hq => ?_, fun q => ?_⟩
  · by_cases hqp : q = p
    · subst hqp; exact hmem i
    · rw [hCm q hqp, hDm q hqp]; exact h.mem q i
  · by_cases hqp : q = p
    · subst hqp; exact hst hq
    · rw [hCl q hqp]; exact h.started q (hτm q hqp hq)
  · by_cases hqp : q = p
    · subst hqp; exact hph
    · rw [hCl q hqp]
      exact phaseOK_frame _ (hDl q hqp) (hDo q hqp) (hτc q hqp) (count_concat_ne σ hqp)
        (h.phase q)

/-- Frame lemma for the invariant: only process `p` moved. -/
lemma Inv2.frame {C' : Config (alg2 E PS)} {p : Bool} (h : Inv2 E PS X C)
    (hCl : ∀ q, q ≠ p → C'.loc q = C.loc q) (hCm : ∀ q, q ≠ p → C'.mem q = C.mem q)
    (hCo : ∀ q, q ≠ p → C'.out q = C.out q)
    (hreg : C'.mem p none = match C'.loc p with | .wIn _ => none | _ => some (X p))
    (hx : xOf (C'.loc p) = X p)
    (hxo : ∀ xo, xoOf (C'.loc p) = some xo → xo = none ∨ xo = some (X (!p)))
    (hnb : ¬ (xoOf (C'.loc p) = some none ∧ xoOf (C.loc (!p)) = some none))
    (hxo2 : ∀ x xo d xo2, (C'.loc p = .post x xo d xo2 ∨ C'.loc p = .done x xo d xo2) →
      0 < d → d < L → xo2 = some (X (!p)))
    (hout : C'.out p = out2Of E PS p (C'.loc p)) : Inv2 E PS X C' := by
  have hn : C'.loc (!p) = C.loc (!p) := hCl _ (ne_not p)
  refine ⟨fun q => ?_, fun q => ?_, fun q xo hq => ?_, fun q hq => ?_,
    fun q x xo d xo2 hq => ?_, fun q => ?_⟩
  · by_cases hqp : q = p
    · subst hqp; exact hreg
    · rw [hCm q hqp, hCl q hqp]; exact h.regI q
  · by_cases hqp : q = p
    · subst hqp; exact hx
    · rw [hCl q hqp]; exact h.xOf_eq q
  · by_cases hqp : q = p
    · subst hqp; exact hxo xo hq
    · rw [hCl q hqp] at hq; exact h.xo q xo hq
  · by_cases hqp : q = p
    · subst hqp; rw [hn]; exact fun h' => hnb ⟨hq, h'⟩
    · have hq' := eq_not_of_ne hqp
      subst hq'
      rw [Bool.not_not]
      rw [hn] at hq
      exact fun h' => hnb ⟨h', hq⟩
  · by_cases hqp : q = p
    · subst hqp; exact hxo2 x xo d xo2 hq
    · rw [hCl q hqp] at hq; exact h.xo2 q x xo d xo2 hq
  · by_cases hqp : q = p
    · subst hqp; exact hout
    · rw [hCo q hqp, hCl q hqp]; exact h.out q

/-- The canonical consistent `E`-input vector. -/
def canonX (loc : Bool → St2 E.S In) (q : Bool) : Bool :=
  match xoOf (loc q) with
  | some xo => myIn xo
  | none => false

lemma simInputs_canonX (loc : Bool → St2 E.S In) : SimInputs loc (canonX loc) := by
  intro q xo h; simp [canonX, h]

/-- One step of Algorithm 2 preserves the invariant and the simulation. -/
theorem step_ok (hE : EBox E L B) (hI : Inv2 E PS X C)
    (hS : ∀ x', SimInputs C.loc x' → ∃ τ, SimRel E PS x' B C (E.run (E.initCfg x') τ) τ σ)
    (p : Bool) :
    Inv2 E PS X ((alg2 E PS).step p C) ∧
    ∀ x', SimInputs ((alg2 E PS).step p C).loc x' →
      ∃ τ, SimRel E PS x' B ((alg2 E PS).step p C) (E.run (E.initCfg x') τ) τ (σ ++ [p]) := by
  set C' := (alg2 E PS).step p C with hC'
  have hCl : ∀ q, q ≠ p → C'.loc q = C.loc q := fun q h => Alg.step_loc_ne C h
  have hCm : ∀ q, q ≠ p → C'.mem q = C.mem q := fun q h => Alg.step_mem_ne C h
  have hCo : ∀ q, q ≠ p → C'.out q = C.out q := fun q h => Alg.step_out_ne C h
  have hn := ne_not p
  have hregp := hI.regI p
  have hxp := hI.xOf_eq p
  have houtp := hI.out p
  rcases hs : C.loc p with ⟨x⟩ | ⟨x⟩ | ⟨x, xo, s⟩ | ⟨x, xo, d, xo2⟩ | ⟨x, xo, d, xo2⟩
  · -- line 2: write the task input
    have hnext : (alg2 E PS).next p (C.loc p) = .write none (some x) (.rIn x) := by rw [hs]
    have hstep := Alg.step_of_write hnext
    rw [hs] at hregp hxp houtp
    have hl : C'.loc p = .rIn x := by rw [hC', hstep]; simp
    have hm : C'.mem p = Function.update (C.mem p) none (some x) := by rw [hC', hstep]; simp
    have ho : C'.out p = C.out p := by rw [hC', hstep]
    refine ⟨hI.frame hCl hCm hCo ?_ ?_ ?_ ?_ ?_ ?_, fun x' hx' => ?_⟩
    · rw [hm, hl]; simp [← hxp, xOf]
    · rw [hl]; exact hxp
    · rw [hl]; simp [xoOf]
    · rw [hl]; simp [xoOf]
    · rw [hl]; simp
    · rw [ho, hl, houtp]; rfl
    · obtain ⟨τ, h⟩ := hS x' (simInputs_of_step x' hCl (by rw [hs]; simp [xoOf]) hx')
      have hpτ : p ∉ τ := fun hp => h.started p hp (by rw [hs]; rfl)
      have hph := h.phase p
      rw [hs] at hph
      refine ⟨τ, h.frame hCl hCm (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ hq => hq) (fun i => ?_) (fun hp => absurd hp hpτ) ?_⟩
      · rw [hm, Function.update_of_ne (by simp)]; exact h.mem p i
      · rw [hl]; exact ⟨hph.1, hph.2.1, by rw [count_concat_self, hph.2.2]⟩
  · -- line 3: read `I_other`
    set v := C.mem (!p) none with hv
    have hnext : (alg2 E PS).next p (C.loc p) =
        .read (!p) none (fun v => .sub x v (E.init p (myIn v))) := by rw [hs]
    have hstep := Alg.step_of_read hnext
    rw [hs] at hregp hxp houtp
    have hl : C'.loc p = .sub x v (E.init p (myIn v)) := by rw [hC', hstep]; simp [hv]
    have hm : C'.mem p = C.mem p := by rw [hC', hstep]
    have ho : C'.out p = C.out p := by rw [hC', hstep]
    have hvI := hI.regI (!p)
    refine ⟨hI.frame hCl hCm hCo ?_ ?_ ?_ ?_ ?_ ?_, fun x' hx' => ?_⟩
    · rw [hm, hl, hregp]
    · rw [hl]; exact hxp
    · intro xo hxo
      rw [hl] at hxo
      simp only [xoOf, Option.some.injEq] at hxo
      subst hxo
      rw [hv, hvI]
      split <;> simp
    · rw [hl]
      rintro ⟨h1, h2⟩
      simp only [xoOf, Option.some.injEq] at h1
      rw [hv, hvI] at h1
      revert h2 h1
      cases C.loc (!p) <;> simp [xoOf]
    · rw [hl]; simp
    · rw [ho, hl, houtp]; rfl
    · obtain ⟨τ, h⟩ := hS x' (simInputs_of_step x' hCl (by rw [hs]; simp [xoOf]) hx')
      have hpτ : p ∉ τ := fun hp => h.started p hp (by rw [hs]; rfl)
      have hph := h.phase p
      rw [hs] at hph
      have hxp' : x' p = myIn v := hx' p v (by rw [hl]; rfl)
      refine ⟨τ, h.frame hCl hCm (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ hq => hq) (fun i => ?_) (fun hp => absurd hp hpτ) ?_⟩
      · rw [hm]; exact h.mem p i
      · rw [hl]
        refine ⟨by rw [hph.1, hxp'], hph.2.1, ?_⟩
        rw [count_concat_self, hph.2.2, List.count_eq_zero_of_not_mem hpτ]
  · -- running `E`
    rw [hs] at hregp hxp houtp
    -- the projected `E` step
    have hEstep : ∀ x' τ, SimRel E PS x' B C (E.run (E.initCfg x') τ) τ σ →
        (E.run (E.initCfg x') τ).loc p = s := by
      intro x' τ h; have := h.phase p; rw [hs] at this; exact this.1
    rcases hEn : E.next p s with ⟨i, v, s'⟩ | ⟨q, i, k⟩ | ⟨d, s'⟩
    · have hnext : (alg2 E PS).next p (C.loc p) = .write (some i) v (.sub x xo s') := by
        rw [hs]; simp [alg2, hEn]
      have hstep := Alg.step_of_write hnext
      have hl : C'.loc p = .sub x xo s' := by rw [hC', hstep]; simp
      have hm : C'.mem p = Function.update (C.mem p) (some i) v := by rw [hC', hstep]; simp
      have ho : C'.out p = C.out p := by rw [hC', hstep]
      refine ⟨hI.frame hCl hCm hCo ?_ ?_ ?_ ?_ ?_ ?_, fun x' hx' => ?_⟩
      · rw [hm, hl, Function.update_of_ne (by simp), hregp]
      · rw [hl]; exact hxp
      · rw [hl]; exact fun xo' h' => hI.xo p xo' (by rw [hs]; exact h')
      · rw [hl]; exact fun ⟨h1, h2⟩ => hI.notBoth p (by rw [hs]; exact h1) h2
      · rw [hl]; simp
      · rw [ho, hl, houtp]; rfl
      · obtain ⟨τ, h⟩ := hS x' (simInputs_of_step x' hCl
          (by rw [hs, hl]; intro _ h'; simpa [xoOf] using h') hx')
        set D := E.run (E.initCfg x') τ
        have hD : E.next p (D.loc p) = .write i v s' := by rw [hEstep x' τ h, hEn]
        have hph := h.phase p
        rw [hs] at hph
        refine ⟨τ ++ [p], ?_⟩
        rw [Alg.run_concat]
        refine h.frame hCl hCm (fun q hq => Alg.step_loc_ne D hq)
          (fun q hq => Alg.step_mem_ne D hq) (fun q hq => Alg.step_out_ne D hq)
          (fun q hq => count_concat_ne τ hq) (fun q hq hm' => ?_) (fun j => ?_) ?_ ?_
        · simp only [List.mem_append, List.mem_singleton] at hm'
          exact hm'.resolve_right hq
        · rw [hm, Alg.step_of_write hD]
          by_cases hj : j = i
          · subst hj; simp
          · simp [Function.update_of_ne (Option.some_injective _ |>.ne hj),
              Function.update_of_ne hj, h.mem p j]
        · rw [hl]; simp [xoOf]
        · rw [hl, Alg.step_of_write hD]
          refine ⟨by simp, by simp [hph.2.1], ?_⟩
          rw [count_concat_self, count_concat_self, hph.2.2]
    · have hnext : (alg2 E PS).next p (C.loc p) =
          .read q (some i) (fun v => .sub x xo (k v)) := by
        rw [hs]; simp [alg2, hEn]
      have hstep := Alg.step_of_read hnext
      have hl : C'.loc p = .sub x xo (k (C.mem q (some i))) := by rw [hC', hstep]; simp
      have hm : C'.mem p = C.mem p := by rw [hC', hstep]
      have ho : C'.out p = C.out p := by rw [hC', hstep]
      refine ⟨hI.frame hCl hCm hCo ?_ ?_ ?_ ?_ ?_ ?_, fun x' hx' => ?_⟩
      · rw [hm, hl, hregp]
      · rw [hl]; exact hxp
      · rw [hl]; exact fun xo' h' => hI.xo p xo' (by rw [hs]; exact h')
      · rw [hl]; exact fun ⟨h1, h2⟩ => hI.notBoth p (by rw [hs]; exact h1) h2
      · rw [hl]; simp
      · rw [ho, hl, houtp]; rfl
      · obtain ⟨τ, h⟩ := hS x' (simInputs_of_step x' hCl
          (by rw [hs, hl]; intro _ h'; simpa [xoOf] using h') hx')
        set D := E.run (E.initCfg x') τ
        have hD : E.next p (D.loc p) = .read q i k := by rw [hEstep x' τ h, hEn]
        have hph := h.phase p
        rw [hs] at hph
        refine ⟨τ ++ [p], ?_⟩
        rw [Alg.run_concat]
        refine h.frame hCl hCm (fun q hq => Alg.step_loc_ne D hq)
          (fun q hq => Alg.step_mem_ne D hq) (fun q hq => Alg.step_out_ne D hq)
          (fun q hq => count_concat_ne τ hq) (fun q hq hm' => ?_) (fun j => ?_) ?_ ?_
        · simp only [List.mem_append, List.mem_singleton] at hm'
          exact hm'.resolve_right hq
        · rw [hm, Alg.step_of_read hD]; exact h.mem p j
        · rw [hl]; simp [xoOf]
        · rw [hl, Alg.step_of_read hD]
          refine ⟨by simp [h.mem q i], by simp [hph.2.1], ?_⟩
          rw [count_concat_self, count_concat_self, hph.2.2]
    · -- `E` decides `d`; line 11: read `I_other`
      set v := C.mem (!p) none with hv
      have hnext : (alg2 E PS).next p (C.loc p) =
          .read (!p) none (fun v => .post x xo d v) := by
        rw [hs]; simp [alg2, hEn]
      have hstep := Alg.step_of_read hnext
      have hl : C'.loc p = .post x xo d v := by rw [hC', hstep]; simp [hv]
      have hm : C'.mem p = C.mem p := by rw [hC', hstep]
      have ho : C'.out p = C.out p := by rw [hC', hstep]
      -- the `E`-configuration after the decision step
      have hsim : ∀ x', SimInputs C.loc x' → ∃ τ, SimRel E PS x' B C (E.run (E.initCfg x') τ) τ σ ∧
          (E.run (E.initCfg x') (τ ++ [p])).out p = some d ∧
          E.run (E.initCfg x') (τ ++ [p]) = E.step p (E.run (E.initCfg x') τ) ∧
          E.next p ((E.run (E.initCfg x') τ).loc p) = .decide d s' := by
        intro x' hx'
        obtain ⟨τ, h⟩ := hS x' hx'
        have hD : E.next p ((E.run (E.initCfg x') τ).loc p) = .decide d s' := by
          rw [hEstep x' τ h, hEn]
        have hph := h.phase p
        rw [hs] at hph
        refine ⟨τ, h, ?_, Alg.run_concat _ _ _, hD⟩
        rw [Alg.run_concat, Alg.step_of_decide hD]; simp [hph.2.1]
      refine ⟨hI.frame hCl hCm hCo ?_ ?_ ?_ ?_ ?_ ?_, fun x' hx' => ?_⟩
      · rw [hm, hl, hregp]
      · rw [hl]; exact hxp
      · rw [hl]; exact fun xo' h' => hI.xo p xo' (by rw [hs]; exact h')
      · rw [hl]; exact fun ⟨h1, h2⟩ => hI.notBoth p (by rw [hs]; exact h1) h2
      · rw [hl]
        rintro x' xo' d' xo2' (h' | h') hd0 hdL
        · simp only [St2.post.injEq] at h'
          obtain ⟨-, -, hd, hx2⟩ := h'
          rw [← hx2]; rw [← hd] at hd0 hdL
          obtain ⟨τ, h, hout, -, -⟩ := hsim _ (simInputs_canonX C.loc)
          have hmid := (hE.mid _ _ p d hout hd0 hdL).2
          simp only [List.mem_append, List.mem_singleton] at hmid
          have hst := h.started _ (hmid.resolve_right hn)
          rw [hv, hI.regI (!p)]
          revert hst
          cases C.loc (!p) <;> simp [xoOf]
        · simp at h'
      · rw [ho, hl, houtp]; rfl
      · obtain ⟨τ, h, hout, hrun, hD⟩ := hsim x' (simInputs_of_step x' hCl
          (by rw [hs, hl]; intro _ h'; simpa [xoOf] using h') hx')
        set D := E.run (E.initCfg x') τ
        have hph := h.phase p
        rw [hs] at hph
        refine ⟨τ ++ [p], ?_⟩
        rw [hrun]
        refine h.frame hCl hCm (fun q hq => Alg.step_loc_ne D hq)
          (fun q hq => Alg.step_mem_ne D hq) (fun q hq => Alg.step_out_ne D hq)
          (fun q hq => count_concat_ne τ hq) (fun q hq hm' => ?_) (fun j => ?_) ?_ ?_
        · simp only [List.mem_append, List.mem_singleton] at hm'
          exact hm'.resolve_right hq
        · rw [hm, Alg.step_of_decide hD]; exact h.mem p j
        · rw [hl]; simp [xoOf]
        · rw [hl]
          refine ⟨by rw [← hrun]; exact hout, ?_, ?_⟩
          · rw [count_concat_self, count_concat_self, hph.2.2]
          · rw [count_concat_self]
            by_contra hB
            have := hE.bound x' τ p (by omega)
            rw [hph.2.1] at this
            exact absurd this (by simp)
  · -- lines 8/18/21: decide
    rw [hs] at hregp hxp houtp
    have hnext : (alg2 E PS).next p (C.loc p) =
        .decide (out2 PS p x xo d xo2) (.done x xo d xo2) := by rw [hs]
    have hstep := Alg.step_of_decide hnext
    have hl : C'.loc p = .done x xo d xo2 := by rw [hC', hstep]; simp
    have hm : C'.mem p = C.mem p := by rw [hC', hstep]
    have ho : C'.out p = some (out2 PS p x xo d xo2) := by
      rw [hC', hstep]; simp [houtp, out2Of]
    refine ⟨hI.frame hCl hCm hCo ?_ ?_ ?_ ?_ ?_ ?_, fun x' hx' => ?_⟩
    · rw [hm, hl, hregp]
    · rw [hl]; exact hxp
    · rw [hl]; exact fun xo' h' => hI.xo p xo' (by rw [hs]; exact h')
    · rw [hl]; exact fun ⟨h1, h2⟩ => hI.notBoth p (by rw [hs]; exact h1) h2
    · rw [hl]
      rintro x' xo' d' xo2' (h' | h') hd0 hdL
      · simp at h'
      · simp only [St2.done.injEq] at h'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h'
        exact hI.xo2 p _ _ _ _ (by rw [hs]; left; rfl) hd0 hdL
    · rw [ho, hl]; rfl
    · obtain ⟨τ, h⟩ := hS x' (simInputs_of_step x' hCl
          (by rw [hs, hl]; intro _ h'; simpa [xoOf] using h') hx')
      have hph := h.phase p
      rw [hs] at hph
      refine ⟨τ, h.frame hCl hCm (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ hq => hq) (fun i => ?_) (fun _ => by rw [hl]; simp [xoOf]) ?_⟩
      · rw [hm]; exact h.mem p i
      · rw [hl]; exact hph.1
  · -- after deciding: no-op reads
    rw [hs] at hregp hxp houtp
    have hnext : (alg2 E PS).next p (C.loc p) =
        .read p none (fun _ => .done x xo d xo2) := by rw [hs]
    have hstep := Alg.step_of_read hnext
    have hl : C'.loc p = .done x xo d xo2 := by rw [hC', hstep]; simp
    have hm : C'.mem p = C.mem p := by rw [hC', hstep]
    have ho : C'.out p = C.out p := by rw [hC', hstep]
    refine ⟨hI.frame hCl hCm hCo ?_ ?_ ?_ ?_ ?_ ?_, fun x' hx' => ?_⟩
    · rw [hm, hl, hregp]
    · rw [hl]; exact hxp
    · rw [hl]; exact fun xo' h' => hI.xo p xo' (by rw [hs]; exact h')
    · rw [hl]; exact fun ⟨h1, h2⟩ => hI.notBoth p (by rw [hs]; exact h1) h2
    · rw [hl]
      rintro x' xo' d' xo2' (h' | h') hd0 hdL
      · simp at h'
      · exact hI.xo2 p x' xo' d' xo2' (by rw [hs]; right; exact h') hd0 hdL
    · rw [ho, hl, houtp]
    · obtain ⟨τ, h⟩ := hS x' (simInputs_of_step x' hCl
          (by rw [hs, hl]; intro _ h'; simpa [xoOf] using h') hx')
      have hph := h.phase p
      rw [hs] at hph
      refine ⟨τ, h.frame hCl hCm (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ hq => hq) (fun i => ?_) (fun _ => by rw [hl]; simp [xoOf]) ?_⟩
      · rw [hm]; exact h.mem p i
      · rw [hl]; exact hph

/-- The invariant and the simulation hold in every finite execution of Algorithm 2. -/
theorem reach_ok (hE : EBox E L B) (X : Bool → In) (σ : List Bool) :
    Inv2 E PS X ((alg2 E PS).run ((alg2 E PS).initCfg X) σ) ∧
    ∀ x', SimInputs ((alg2 E PS).run ((alg2 E PS).initCfg X) σ).loc x' →
      ∃ τ, SimRel E PS x' B ((alg2 E PS).run ((alg2 E PS).initCfg X) σ)
        (E.run (E.initCfg x') τ) τ σ := by
  induction σ using List.reverseRecOn with
  | nil =>
    refine ⟨⟨fun p => rfl, fun p => rfl, fun p xo h => ?_, fun p h => ?_, fun p x xo d xo2 h => ?_,
      fun p => rfl⟩, fun x' _ => ⟨[], ⟨fun p i => rfl, fun p h => by simp at h, fun p => ?_⟩⟩⟩
    · simp [Alg.initCfg, xoOf] at h
    · simp [Alg.initCfg, xoOf] at h
    · simp [Alg.initCfg] at h
    · exact ⟨rfl, rfl, rfl⟩
  | append_singleton σ p ih =>
    rw [Alg.run_concat]
    exact step_ok hE ih.1 ih.2 p

end Step

end Podc.BoundedRegisterPower
