import Papers.PODC2020.InfiniteArrivalHierarchy.Objects

/-!
# Algorithm 3 of Perrin–Mostéfaoui–Bonin (PODC 2020): multi-valued from binary consensus in `M₃`

Shared infinite arrays `proposed[j]` (registers over `Option V`, initially `none`), `isSet[j]`
(registers over `Bool`, initially `false`) and `cons[j]` (binary consensus objects). Code of
`p_i` with input `val_i`:
```
proposed[i] ← val_i; isSet[i] ← true;
for j = 0, 1, 2, …: b ← isSet[j]; if cons[j].propose(b) then return proposed[j]
```
Each step of the model is exactly one shared access (`Loc` is the program counter).

The paper gives no proof (Proposition 3). Our proof: agreement/validity from an invariant
(`GInv`): a decided value is `val_j` for the least `j` with `cons[j] = true`, and
`cons[j] = true → isSet[j] = true`. Wait-freedom: `cons[j]` is decided `false` only by a
process `q` that read `isSet[j] = false` after setting its own flag (ghost `FlagBefore`), so the
process whose flag was set first never sees its `cons` decided `false`
(`consR_ne_false_of_first`); a process that never decides passes all rounds, contradiction.

## Main statements
* `alg3_solvesCons`: Proposition 3 (core): Algorithm 3 solves consensus in `M₃`.
* `alg3_poised_lt`: with `n` processes, only objects of index `< n` are ever accessed.
* `alg3_solvesCons_bounded`: Algorithm 3 solves consensus in `Mⁿ₁`.
-/

namespace Podc.InfiniteArrivalHierarchy.Alg3

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

/-- The shared objects of Algorithm 3. -/
inductive Obj
  | prop (j : ℕ)
  | flag (j : ℕ)
  | cons (j : ℕ)
  deriving DecidableEq

/-- The object family. -/
abbrev T (V : Type) : Obj → ObjSpec
  | .prop _ => register (Option V) none
  | .flag _ => register Bool false
  | .cons _ => consObj Bool

/-- Local states. -/
inductive Loc (V : Type)
  /-- About to write `proposed[i] ← v` (own index `i`, own input `v`). -/
  | wProp (i : ℕ) (v : V)
  /-- About to write `isSet[i] ← true`. -/
  | wFlag (i : ℕ) (v : V)
  /-- Round `j`: about to read `isSet[j]`. -/
  | rFlag (v : V) (j : ℕ)
  /-- Round `j`: about to propose `b` to `cons[j]`. -/
  | prop (v : V) (j : ℕ) (b : Bool)
  /-- `cons[j]` decided `true`: about to read `proposed[j]`. -/
  | rVal (v : V) (j : ℕ)
  /-- Decided `w`. -/
  | done (w : V)

/-- Next action (one shared access per step; local computation folded into continuations). -/
def act {V : Type} : Loc V → Act (T V) (Loc V) V
  | .wProp i v => .access (Obj.prop i) (RWOp.write (some v)) (fun _ => .wFlag i v)
  | .wFlag i v => .access (Obj.flag i) (RWOp.write true) (fun _ => .rFlag v 0)
  | .rFlag v j => .access (Obj.flag j) RWOp.read (fun b => .prop v j b)
  | .prop v j b => .access (Obj.cons j) b (fun d => if d then .rVal v j else .rFlag v (j + 1))
  | .rVal v j => .access (Obj.prop j) RWOp.read (fun w => .done (w.getD v))
  | .done w => .out w

/-- Algorithm 3 (process `i` with input `v` starts in `wProp i v`). -/
def alg3 (V : Type) : Alg (T V) ℕ V V where
  L := Loc V
  init i v := .wProp i v
  act := act
  mem₀
    | .prop _ => (none : Option V)
    | .flag _ => false
    | .cons _ => (none : Option Bool)

variable {V : Type}

/-- Configurations of Algorithm 3. -/
abbrev Cf (V : Type) := Cfg (alg3 V)

/-- Contents of `proposed[j]`. -/
def propR (C : Cf V) (j : ℕ) : Option V := C.mem (.prop j)
/-- Contents of `isSet[j]`. -/
def flagR (C : Cf V) (j : ℕ) : Bool := C.mem (.flag j)
/-- State of `cons[j]` (`none`: undecided). -/
def consR (C : Cf V) (j : ℕ) : Option Bool := C.mem (.cons j)

section Step

variable {C : Cf V} {p : ℕ}

lemma step_wProp {i : ℕ} {v : V} (h : C.loc p = .wProp i v) :
    (C.step p).loc p = .wFlag i v ∧ (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
    (∀ j, propR (C.step p) j = if j = i then some v else propR C j) ∧
    (∀ j, flagR (C.step p) j = flagR C j) ∧ (∀ j, consR (C.step p) j = consR C j) := by
  rw [Cfg.step_of_access (show (alg3 V).act (C.loc p) = _ by rw [h]; rfl)]
  refine ⟨Function.update_self .., fun q hq => Function.update_of_ne hq .., fun j => ?_, fun j => ?_, fun j => ?_⟩
  · by_cases hj : j = i
    · subst hj; simp [propR]
    · simp [propR, hj]
  · simp [flagR]
  · simp [consR]

lemma step_wFlag {i : ℕ} {v : V} (h : C.loc p = .wFlag i v) :
    (C.step p).loc p = .rFlag v 0 ∧ (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
    (∀ j, propR (C.step p) j = propR C j) ∧
    (∀ j, flagR (C.step p) j = if j = i then true else flagR C j) ∧
    (∀ j, consR (C.step p) j = consR C j) := by
  rw [Cfg.step_of_access (show (alg3 V).act (C.loc p) = _ by rw [h]; rfl)]
  refine ⟨Function.update_self .., fun q hq => Function.update_of_ne hq .., fun j => ?_, fun j => ?_, fun j => ?_⟩
  · simp [propR]
  · by_cases hj : j = i
    · subst hj; simp [flagR]
    · simp [flagR, hj]
  · simp [consR]

lemma step_rFlag {v : V} {j : ℕ} (h : C.loc p = .rFlag v j) :
    (C.step p).loc p = .prop v j (flagR C j) ∧ (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
    (C.step p).mem = C.mem := by
  rw [Cfg.step_of_access (show (alg3 V).act (C.loc p) = _ by rw [h]; rfl)]
  refine ⟨Function.update_self .., fun q hq => Function.update_of_ne hq .., ?_⟩
  simp

lemma step_prop {v : V} {j : ℕ} {b : Bool} (h : C.loc p = .prop v j b) :
    (C.step p).loc p = (if (consR C j).getD b then .rVal v j else .rFlag v (j + 1)) ∧
    (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
    (∀ j, propR (C.step p) j = propR C j) ∧
    (∀ j, flagR (C.step p) j = flagR C j) ∧
    (∀ j', consR (C.step p) j' = if j' = j then some ((consR C j).getD b) else consR C j') := by
  rw [Cfg.step_of_access (show (alg3 V).act (C.loc p) = _ by rw [h]; rfl)]
  refine ⟨Function.update_self .., fun q hq => Function.update_of_ne hq .., fun j => ?_, fun j => ?_, fun j' => ?_⟩
  · simp [propR]
  · simp [flagR]
  · by_cases hj : j' = j
    · subst hj; simp [consR]
    · simp [consR, hj]

lemma step_rVal {v : V} {j : ℕ} (h : C.loc p = .rVal v j) :
    (C.step p).loc p = .done ((propR C j).getD v) ∧ (∀ q, q ≠ p → (C.step p).loc q = C.loc q) ∧
    (C.step p).mem = C.mem := by
  rw [Cfg.step_of_access (show (alg3 V).act (C.loc p) = _ by rw [h]; rfl)]
  refine ⟨Function.update_self .., fun q hq => Function.update_of_ne hq .., ?_⟩
  simp

lemma step_done {w : V} (h : C.loc p = .done w) : C.step p = C :=
  Cfg.step_of_out (show (alg3 V).act (C.loc p) = .out w by rw [h]; rfl)

end Step

/-! ### Invariants -/

/-- Ghost history: at some point of the execution `σ` (after a prefix of `σ`), the flag of `q`
was already set while the flag of `j` was not. -/
def FlagBefore (x : ℕ → V) (σ : List ℕ) (q j : ℕ) : Prop :=
  ∃ k ≤ σ.length, flagR ((alg3 V).exec x (σ.take k)) q = true ∧
    flagR ((alg3 V).exec x (σ.take k)) j = false

lemma FlagBefore.append {x : ℕ → V} {σ : List ℕ} {q j : ℕ} (h : FlagBefore x σ q j)
    (τ : List ℕ) : FlagBefore x (σ ++ τ) q j := by
  obtain ⟨k, hk, h1, h2⟩ := h
  refine ⟨k, by simp; omega, ?_⟩
  rw [List.take_append_of_le_length hk]
  exact ⟨h1, h2⟩

/-- Local invariant of process `p` in local state `l`. -/
def LInv (x : ℕ → V) (σ : List ℕ) (C : Cf V) (p : ℕ) : Loc V → Prop
  | .wProp i v => i = p ∧ v = x p
  | .wFlag i v => i = p ∧ v = x p ∧ propR C p = some (x p)
  | .rFlag _ j => flagR C p = true ∧ ∀ j' < j, consR C j' = some false
  | .prop _ j b => flagR C p = true ∧ (∀ j' < j, consR C j' = some false) ∧
      (b = true → flagR C j = true) ∧ (b = false → FlagBefore x σ p j)
  | .rVal _ j => flagR C p = true ∧ (∀ j' < j, consR C j' = some false) ∧
      consR C j = some true
  | .done w => ∃ j, (∀ j' < j, consR C j' = some false) ∧ consR C j = some true ∧ w = x j

/-- The shared memory only grows from `C` to `D`. -/
structure MemLe (C D : Cf V) : Prop where
  prop : ∀ j w, propR C j = some w → propR D j = some w
  flag : ∀ j, flagR C j = true → flagR D j = true
  cons : ∀ j b, consR C j = some b → consR D j = some b

lemma LInv.mono {x : ℕ → V} {σ σ' : List ℕ} {C D : Cf V} {p : ℕ} {l : Loc V} (hm : MemLe C D)
    (hfb : ∀ q j, FlagBefore x σ q j → FlagBefore x σ' q j) (h : LInv x σ C p l) :
    LInv x σ' D p l := by
  cases l with
  | wProp i v => exact h
  | wFlag i v => exact ⟨h.1, h.2.1, hm.prop _ _ h.2.2⟩
  | rFlag v j => exact ⟨hm.flag _ h.1, fun j' hj' => hm.cons _ _ (h.2 j' hj')⟩
  | prop v j b =>
    exact ⟨hm.flag _ h.1, fun j' hj' => hm.cons _ _ (h.2.1 j' hj'),
      fun hb => hm.flag _ (h.2.2.1 hb), fun hb => hfb _ _ (h.2.2.2 hb)⟩
  | rVal v j => exact ⟨hm.flag _ h.1, fun j' hj' => hm.cons _ _ (h.2.1 j' hj'), hm.cons _ _ h.2.2⟩
  | done w =>
    obtain ⟨j, h1, h2, h3⟩ := h
    exact ⟨j, fun j' hj' => hm.cons _ _ (h1 j' hj'), hm.cons _ _ h2, h3⟩

/-- The invariant of Algorithm 3 (for the configuration `C` reached by `σ` from inputs `x`). -/
structure GInv (x : ℕ → V) (σ : List ℕ) (C : Cf V) : Prop where
  prop_eq : ∀ j w, propR C j = some w → w = x j
  flag_prop : ∀ j, flagR C j = true → propR C j = some (x j)
  flag_mem : ∀ j, flagR C j = true → j ∈ σ
  cons_true : ∀ j, consR C j = some true → flagR C j = true
  cons_false : ∀ j, consR C j = some false → ∃ q, FlagBefore x σ q j
  loc : ∀ p, LInv x σ C p (C.loc p)

lemma ginv_nil (x : ℕ → V) : GInv x [] ((alg3 V).exec x []) where
  prop_eq j w h := by simp [propR, Alg.initCfg, alg3] at h
  flag_prop j h := by simp [flagR, Alg.initCfg, alg3] at h
  flag_mem j h := by simp [flagR, Alg.initCfg, alg3] at h
  cons_true j h := by simp [consR, Alg.initCfg, alg3] at h
  cons_false j h := by simp [consR, Alg.initCfg, alg3] at h
  loc p := by simp [Alg.initCfg, alg3, LInv]

lemma MemLe.of_mem_eq {C D : Cf V} (h : D.mem = C.mem) : MemLe C D :=
  ⟨fun j w hw => by simpa [propR, h] using hw, fun j hj => by simpa [flagR, h] using hj,
    fun j b hb => by simpa [consR, h] using hb⟩

lemma GInv.of_mem_eq {x : ℕ → V} {σ : List ℕ} {C D : Cf V} {p : ℕ} (h : GInv x σ C)
    (hmem : D.mem = C.mem) (hl : ∀ q, q ≠ p → D.loc q = C.loc q)
    (hp : LInv x (σ ++ [p]) D p (D.loc p)) : GInv x (σ ++ [p]) D where
  prop_eq j w hw := h.prop_eq j w (by simpa [propR, hmem] using hw)
  flag_prop j hj := by
    simpa [propR, hmem] using h.flag_prop j (by simpa [flagR, hmem] using hj)
  flag_mem j hj := List.mem_append_left _ (h.flag_mem j (by simpa [flagR, hmem] using hj))
  cons_true j hj := by
    simpa [flagR, hmem] using h.cons_true j (by simpa [consR, hmem] using hj)
  cons_false j hj := by
    obtain ⟨q, hq⟩ := h.cons_false j (by simpa [consR, hmem] using hj)
    exact ⟨q, hq.append [p]⟩
  loc q := by
    by_cases hq : q = p
    · subst hq; exact hp
    · rw [hl q hq]; exact (h.loc q).mono (MemLe.of_mem_eq hmem) (fun _ _ h => h.append [p])

lemma ginv_step {x : ℕ → V} {σ : List ℕ} {C : Cf V} (h : GInv x σ C)
    (hC : (alg3 V).exec x σ = C) (p : ℕ) : GInv x (σ ++ [p]) (C.step p) := by
  have hfb : ∀ q j, FlagBefore x σ q j → FlagBefore x (σ ++ [p]) q j :=
    fun q j hq => hq.append [p]
  have hother : ∀ D : Cf V, MemLe C D → (∀ q, q ≠ p → D.loc q = C.loc q) →
      ∀ q, q ≠ p → LInv x (σ ++ [p]) D q (D.loc q) := by
    intro D hm hl q hq
    rw [hl q hq]; exact (h.loc q).mono hm hfb
  have hlp := h.loc p
  cases hl : C.loc p with
  | wProp i v =>
    rw [hl] at hlp
    obtain ⟨hi, hv⟩ := hlp
    subst i v
    obtain ⟨h1, h2, hP, hF, hC'⟩ := step_wProp hl
    have hm : MemLe C (C.step p) := by
      refine ⟨fun j w hw => ?_, fun j hj => by rwa [hF], fun j b hb => by rwa [hC']⟩
      rw [hP]; split_ifs with hji
      · subst hji; rw [h.prop_eq _ _ hw]
      · exact hw
    refine ⟨fun j w hw => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
      fun q => ?_⟩
    · rw [hP] at hw; split_ifs at hw with hji
      · subst hji; simpa using hw.symm
      · exact h.prop_eq _ _ hw
    · rw [hF] at hj; exact hm.prop _ _ (h.flag_prop _ hj)
    · rw [hF] at hj; exact List.mem_append_left _ (h.flag_mem _ hj)
    · rw [hC'] at hj; rw [hF]; exact h.cons_true _ hj
    · rw [hC'] at hj; obtain ⟨q, hq⟩ := h.cons_false _ hj; exact ⟨q, hfb _ _ hq⟩
    · by_cases hq : q = p
      · subst hq; rw [h1]; exact ⟨rfl, rfl, by rw [hP]; simp⟩
      · exact hother _ hm h2 q hq
  | wFlag i v =>
    rw [hl] at hlp
    obtain ⟨hi, hv, hpp⟩ := hlp
    subst i v
    obtain ⟨h1, h2, hP, hF, hC'⟩ := step_wFlag hl
    have hm : MemLe C (C.step p) := by
      refine ⟨fun j w hw => by rwa [hP], fun j hj => ?_, fun j b hb => by rwa [hC']⟩
      rw [hF]; split_ifs <;> simp [hj]
    refine ⟨fun j w hw => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_,
      fun q => ?_⟩
    · rw [hP] at hw; exact h.prop_eq _ _ hw
    · rw [hF] at hj; rw [hP]; split_ifs at hj with hjp
      · subst hjp; exact hpp
      · exact h.flag_prop _ hj
    · rw [hF] at hj; split_ifs at hj with hjp
      · subst hjp; simp
      · exact List.mem_append_left _ (h.flag_mem _ hj)
    · rw [hC'] at hj; exact hm.flag _ (h.cons_true _ hj)
    · rw [hC'] at hj; obtain ⟨q, hq⟩ := h.cons_false _ hj; exact ⟨q, hfb _ _ hq⟩
    · by_cases hq : q = p
      · subst hq; rw [h1]; exact ⟨by rw [hF]; simp, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
      · exact hother _ hm h2 q hq
  | rFlag v j =>
    rw [hl] at hlp
    obtain ⟨h1, h2, hmem⟩ := step_rFlag hl
    refine h.of_mem_eq hmem h2 ?_
    rw [h1]
    refine ⟨by simpa [flagR, hmem] using hlp.1, fun j' hj' => by
      simpa [consR, hmem] using hlp.2 j' hj', fun hb => by simpa [flagR, hmem] using hb,
      fun hb => ⟨σ.length, by simp, ?_⟩⟩
    rw [List.take_append_of_le_length le_rfl, List.take_of_length_le le_rfl, hC]
    exact ⟨hlp.1, hb⟩
  | prop v j b =>
    rw [hl] at hlp
    obtain ⟨hfp, hlt, hbt, hbf⟩ := hlp
    obtain ⟨h1, h2, hP, hF, hC'⟩ := step_prop hl
    have hm : MemLe C (C.step p) := by
      refine ⟨fun j w hw => by rwa [hP], fun j hj => by rwa [hF], fun j' c hc => ?_⟩
      rw [hC']; split_ifs with hj
      · subst hj; rw [hc]; rfl
      · exact hc
    refine ⟨fun j w hw => ?_, fun j hj => ?_, fun j hj => ?_, fun j' hj => ?_, fun j' hj => ?_,
      fun q => ?_⟩
    · rw [hP] at hw; exact h.prop_eq _ _ hw
    · rw [hF] at hj; rw [hP]; exact h.flag_prop _ hj
    · rw [hF] at hj; exact List.mem_append_left _ (h.flag_mem _ hj)
    · rw [hF]; rw [hC'] at hj; split_ifs at hj with hjj
      · subst hjj
        cases hcj : consR C j' with
        | none => rw [hcj] at hj; simp at hj; exact hbt hj
        | some c => rw [hcj] at hj; simp at hj; subst hj; exact h.cons_true _ hcj
      · exact h.cons_true _ hj
    · rw [hC'] at hj; split_ifs at hj with hjj
      · subst hjj
        cases hcj : consR C j' with
        | none => rw [hcj] at hj; simp at hj; exact ⟨p, hfb _ _ (hbf hj)⟩
        | some c =>
          rw [hcj] at hj; simp at hj; subst hj
          obtain ⟨q, hq⟩ := h.cons_false _ hcj; exact ⟨q, hfb _ _ hq⟩
      · obtain ⟨q, hq⟩ := h.cons_false _ hj; exact ⟨q, hfb _ _ hq⟩
    · by_cases hq : q = p
      · subst hq
        have hlt' : ∀ j' < j, consR (C.step q) j' = some false := fun j' hj' => by
          rw [hC', ite_eq_right (by omega)]; exact hlt j' hj'
        by_cases hd : (consR C j).getD b = true
        · have h1' : (C.step q).loc q = Loc.rVal v j := by rw [h1]; simp [hd]; rfl
          rw [h1']
          exact ⟨by rw [hF]; exact hfp, hlt', by simp [hC', hd]⟩
        · have h1' : (C.step q).loc q = Loc.rFlag v (j + 1) := by rw [h1]; simp [hd]; rfl
          rw [h1']
          refine ⟨by rw [hF]; exact hfp, fun j' hj' => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj' with hj' | rfl
          · exact hlt' j' hj'
          · rw [hC']; simpa using hd
      · exact hother _ hm h2 q hq
  | rVal v j =>
    rw [hl] at hlp
    obtain ⟨hfp, hlt, hcj⟩ := hlp
    obtain ⟨h1, h2, hmem⟩ := step_rVal hl
    refine h.of_mem_eq hmem h2 ?_
    rw [h1]
    refine ⟨j, fun j' hj' => by simpa [consR, hmem] using hlt j' hj',
      by simpa [consR, hmem] using hcj, ?_⟩
    rw [h.flag_prop _ (h.cons_true _ hcj)]; rfl
  | done w =>
    rw [step_done hl]
    refine h.of_mem_eq rfl (fun _ _ => rfl) ?_
    rw [hl] at hlp ⊢
    exact hlp.mono (MemLe.of_mem_eq rfl) hfb

lemma ginv (x : ℕ → V) (σ : List ℕ) : GInv x σ ((alg3 V).exec x σ) := by
  induction σ using List.reverseRecOn with
  | nil => exact ginv_nil x
  | append_singleton σ p ih => rw [Alg.exec_concat]; exact ginv_step ih rfl p

lemma out_iff {C : Cf V} {p : ℕ} {w : V} : C.Out p w ↔ C.loc p = .done w := by
  unfold Cfg.Out
  cases C.loc p <;> simp [alg3, act]

/-! ### Flags only go up -/

lemma flagR_step {C : Cf V} {q : ℕ} (hq : flagR C q = true) (p : ℕ) :
    flagR (C.step p) q = true := by
  cases hl : C.loc p with
  | wProp i v => rw [(step_wProp hl).2.2.2.1]; exact hq
  | wFlag i v => rw [(step_wFlag hl).2.2.2.1]; split_ifs <;> simp [hq]
  | rFlag v j => simpa [flagR, (step_rFlag hl).2.2] using hq
  | prop v j b => rw [(step_prop hl).2.2.2.1]; exact hq
  | rVal v j => simpa [flagR, (step_rVal hl).2.2] using hq
  | done w => rw [step_done hl]; exact hq

lemma flagR_run {C : Cf V} {q : ℕ} (hq : flagR C q = true) (τ : List ℕ) :
    flagR ((alg3 V).run C τ) q = true := by
  induction τ generalizing C with
  | nil => exact hq
  | cons p τ ih => exact ih (flagR_step hq p)

lemma flagR_exec_append {x : ℕ → V} {σ : List ℕ} {q : ℕ}
    (hq : flagR ((alg3 V).exec x σ) q = true) (τ : List ℕ) :
    flagR ((alg3 V).exec x (σ ++ τ)) q = true := by
  rw [Alg.exec_append]; exact flagR_run hq τ

/-- The core of the wait-freedom argument: the consensus object `cons[q]` of the process `q`
whose flag was set first is never decided `false`. -/
lemma consR_ne_false_of_first {x : ℕ → V} {σ : List ℕ} {q : ℕ}
    (hq : flagR ((alg3 V).exec x σ) q = true)
    (hmin : ∀ k < σ.length, ∀ q', flagR ((alg3 V).exec x (σ.take k)) q' = false)
    (τ : List ℕ) : consR ((alg3 V).exec x (σ ++ τ)) q ≠ some false := by
  intro hc
  obtain ⟨q', k, hk, h1, h2⟩ := (ginv x (σ ++ τ)).cons_false q hc
  by_cases hkσ : k < σ.length
  · rw [List.take_append_of_le_length hkσ.le] at h1
    rw [hmin k hkσ q'] at h1; exact absurd h1 (by simp)
  · rw [List.take_append, List.take_of_length_le (by omega)] at h2
    rw [flagR_exec_append hq] at h2; exact absurd h2 (by simp)

/-- In every reachable configuration in which some flag is set, some process `q` with its flag
set has `cons[q]` not decided `false`. -/
lemma exists_flag_consR_ne_false {x : ℕ → V} {σ : List ℕ}
    (h : ∃ q, flagR ((alg3 V).exec x σ) q = true) :
    ∃ q, flagR ((alg3 V).exec x σ) q = true ∧ consR ((alg3 V).exec x σ) q ≠ some false := by
  classical
  have hex : ∃ k, ∃ q, flagR ((alg3 V).exec x (σ.take k)) q = true :=
    ⟨σ.length, by simpa using h⟩
  obtain ⟨q, hq⟩ := Nat.find_spec hex
  set k := Nat.find hex
  have hmin : ∀ k' < (σ.take k).length, ∀ q',
      flagR ((alg3 V).exec x ((σ.take k).take k')) q' = false := by
    intro k' hk' q'
    have hk'' : k' < k := lt_of_lt_of_le hk' (by simp)
    rw [List.take_take, min_eq_left hk''.le]
    have := Nat.find_min hex hk''
    push Not at this
    simpa using this q'
  have hσ : σ = σ.take k ++ σ.drop k := (List.take_append_drop k σ).symm
  refine ⟨q, ?_, ?_⟩
  · rw [hσ]; exact flagR_exec_append hq _
  · rw [hσ]; exact consR_ne_false_of_first hq hmin _

/-! ### Agreement and validity -/

lemma eq_of_first_true {C : Cf V} {j₁ j₂ : ℕ}
    (h₁ : ∀ j' < j₁, consR C j' = some false) (h₁' : consR C j₁ = some true)
    (h₂ : ∀ j' < j₂, consR C j' = some false) (h₂' : consR C j₂ = some true) : j₁ = j₂ := by
  rcases lt_trichotomy j₁ j₂ with h | h | h
  · rw [h₂ _ h] at h₁'; simp at h₁'
  · exact h
  · rw [h₁ _ h] at h₂'; simp at h₂'

lemma out_spec {x : ℕ → V} {σ : List ℕ} {p : ℕ} {w : V} (h : ((alg3 V).exec x σ).Out p w) :
    ∃ j, (∀ j' < j, consR ((alg3 V).exec x σ) j' = some false) ∧
      consR ((alg3 V).exec x σ) j = some true ∧ w = x j := by
  have := (ginv x σ).loc p
  rw [out_iff.1 h] at this
  exact this

/-- Proposition 3 (core), agreement. -/
theorem alg3_agreement : Agreement (alg3 V) anySched := by
  intro x σ _ p _ q _ v w hv hw
  obtain ⟨j₁, h₁, h₁', rfl⟩ := out_spec hv
  obtain ⟨j₂, h₂, h₂', rfl⟩ := out_spec hw
  rw [eq_of_first_true h₁ h₁' h₂ h₂']

/-- Proposition 3 (core), validity: a decided value is the input of a process that took a step
(indeed, of a process that completed its announcement `proposed[j] ← val_j; isSet[j] ← true`). -/
theorem alg3_validity : Validity (alg3 V) anySched := by
  intro x σ _ p _ w hw
  obtain ⟨j, -, hj, rfl⟩ := out_spec hw
  have G := ginv x σ
  exact ⟨j, G.flag_mem _ (G.cons_true _ hj), rfl⟩

/-! ### Progress -/

/-- Progress measure of a local state (the program counter, with rounds). -/
def rank : Loc V → ℕ
  | .wProp _ _ => 0
  | .wFlag _ _ => 1
  | .rFlag _ j => 2 * j + 2
  | .prop _ j _ => 2 * j + 3
  | .rVal _ j => 2 * j + 4
  | .done _ => 0

lemma rank_step {C : Cf V} {p : ℕ} (h : ∀ w, C.loc p ≠ .done w) :
    (∃ w, (C.step p).loc p = .done w) ∨ rank (C.loc p) + 1 ≤ rank ((C.step p).loc p) := by
  cases hl : C.loc p with
  | wProp i v => right; rw [(step_wProp hl).1]; simp [rank]
  | wFlag i v => right; rw [(step_wFlag hl).1]; simp [rank]
  | rFlag v j => right; rw [(step_rFlag hl).1]; simp [rank]
  | prop v j b =>
    right
    have h1 := (step_prop hl).1
    by_cases hd : (consR C j).getD b = true
    · have h1' : (C.step p).loc p = Loc.rVal v j := by rw [h1]; simp [hd]; rfl
      rw [h1']; simp [rank]
    · have h1' : (C.step p).loc p = Loc.rFlag v (j + 1) := by rw [h1]; simp [hd]; rfl
      rw [h1']; simp [rank]; omega
  | rVal v j => left; exact ⟨_, (step_rVal hl).1⟩
  | done w => exact absurd hl (h w)

lemma count_le_rank (x : ℕ → V) (s : ℕ → ℕ) (p : ℕ) (t : ℕ) :
    (∃ w, ((alg3 V).exec x (pre s t)).loc p = .done w) ∨
      (pre s t).count p ≤ rank (((alg3 V).exec x (pre s t)).loc p) := by
  induction t with
  | zero => right; simp
  | succ t ih =>
    rw [pre_succ, Alg.exec_concat]
    set C := (alg3 V).exec x (pre s t)
    by_cases hst : s t = p
    · subst hst
      by_cases hd : ∃ w, C.loc (s t) = .done w
      · obtain ⟨w, hw⟩ := hd
        left; exact ⟨w, by rw [step_done hw]; exact hw⟩
      · push Not at hd
        rcases ih with ⟨w, hw⟩ | ih
        · exact absurd hw (hd w)
        · rcases rank_step hd with h | h
          · left; exact h
          · right; simp only [List.count_append, List.count_singleton_self]; omega
    · rw [Cfg.step_loc_other C (Ne.symm hst)]
      rcases ih with h | h
      · left; exact h
      · right; simpa [List.count_append, List.count_singleton, hst] using h

/-- A process whose progress measure is at least `2J + 4` and that has not decided has seen
`cons[j'] = false` for all `j' < J`, and its flag is set. -/
lemma of_rank_ge {x : ℕ → V} {σ : List ℕ} {p J : ℕ}
    (hr : 2 * J + 4 ≤ rank (((alg3 V).exec x σ).loc p))
    (hd : ∀ w, ((alg3 V).exec x σ).loc p ≠ .done w) :
    flagR ((alg3 V).exec x σ) p = true ∧
      ∀ j' < J, consR ((alg3 V).exec x σ) j' = some false := by
  have := (ginv x σ).loc p
  cases hl : ((alg3 V).exec x σ).loc p with
  | wProp i v => rw [hl] at hr; simp [rank] at hr
  | wFlag i v => rw [hl] at hr; simp [rank] at hr
  | rFlag v j =>
    rw [hl] at hr this; simp [rank] at hr
    exact ⟨this.1, fun j' hj' => this.2 j' (by omega)⟩
  | prop v j b =>
    rw [hl] at hr this; simp [rank] at hr
    exact ⟨this.1, fun j' hj' => this.2.1 j' (by omega)⟩
  | rVal v j =>
    rw [hl] at hr this; simp [rank] at hr
    exact ⟨this.1, fun j' hj' => this.2.1 j' (by omega)⟩
  | done w => exact absurd hl (hd w)

lemma count_unbounded {s : ℕ → ℕ} {p : ℕ} (h : InfOften s p) (R : ℕ) :
    ∃ t, R ≤ (pre s t).count p := by
  induction R with
  | zero => exact ⟨0, by simp⟩
  | succ R ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨t', ht', hs⟩ := h t
    refine ⟨t' + 1, ?_⟩
    rw [pre_succ, List.count_append, hs, List.count_singleton_self]
    have := ((pre_prefix s ht').sublist.count_le p)
    omega

lemma take_pre (s : ℕ → ℕ) {k m : ℕ} (h : k ≤ m) : (pre s m).take k = pre s k := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pre_add, List.take_append_of_le_length (by simp)]
  simp

/-- Proposition 3 (core), wait-freedom in the infinite arrival model. -/
theorem alg3_waitFree : WaitFree (alg3 V) infArrival := by
  classical
  intro x s _ p hp
  by_contra hno
  push Not at hno
  have hnd : ∀ t w, ((alg3 V).exec x (pre s t)).loc p ≠ .done w :=
    fun t w hw => hno t w (out_iff.2 hw)
  have hrank : ∀ R, ∃ t₁, ∀ t ≥ t₁, R ≤ rank (((alg3 V).exec x (pre s t)).loc p) := by
    intro R
    obtain ⟨t₁, ht₁⟩ := count_unbounded hp R
    refine ⟨t₁, fun t ht => ?_⟩
    rcases count_le_rank x s p t with ⟨w, hw⟩ | h
    · exact absurd hw (hnd t w)
    · have := ((pre_prefix s ht).sublist.count_le p); omega
  have hex : ∃ m, ∃ q, flagR ((alg3 V).exec x (pre s m)) q = true := by
    obtain ⟨t₁, ht₁⟩ := hrank (2 * 0 + 4)
    exact ⟨t₁, p, (of_rank_ge (ht₁ t₁ le_rfl) (hnd t₁)).1⟩
  obtain ⟨q, hq⟩ := Nat.find_spec hex
  set m := Nat.find hex
  have hmin : ∀ k < (pre s m).length, ∀ q',
      flagR ((alg3 V).exec x ((pre s m).take k)) q' = false := by
    intro k hk q'
    rw [length_pre] at hk
    rw [take_pre s hk.le]
    have := Nat.find_min hex hk
    push Not at this
    simpa using this q'
  obtain ⟨t₁, ht₁⟩ := hrank (2 * (q + 1) + 4)
  set t := max t₁ m
  have hc := (of_rank_ge (ht₁ t (le_max_left _ _)) (hnd t)).2 q (Nat.lt_succ_self q)
  obtain ⟨τ, hτ⟩ := pre_prefix s (le_max_right t₁ m)
  rw [← hτ] at hc
  exact consR_ne_false_of_first hq hmin τ hc

/-- **Proposition 3 (core)** of Perrin–Mostéfaoui–Bonin: Algorithm 3 solves (multi-valued)
consensus from binary consensus objects and registers (infinite arrays of them) in the infinite
arrival model `M₃`. -/
theorem alg3_solvesCons (V : Type) : SolvesCons (alg3 V) anySched infArrival :=
  ⟨alg3_agreement, alg3_validity, alg3_waitFree⟩

/-! ### Bounded memory for `n` processes -/

/-- The index of an object of the arrays. -/
def Obj.idx : Obj → ℕ
  | .prop j => j
  | .flag j => j
  | .cons j => j

/-- With processes `p₀, …, p_{n-1}` only, every process `p_i` (`i < n`) is only ever poised on
objects of index `< n`: Algorithm 3 then uses only the `3n` objects `proposed[j]`, `isSet[j]`,
`cons[j]` (`j < n`). -/
theorem alg3_poised_lt {n : ℕ} (x : ℕ → V) {σ : List ℕ} (hσ : belowN n σ) {p : ℕ} (hp : p < n)
    {o : Obj} (h : ((alg3 V).exec x σ).Poised p o) : o.idx < n := by
  set C := (alg3 V).exec x σ
  have G := ginv x σ
  have hL := G.loc p
  -- a process in round `j ≥ n` would have seen `cons[j'] = false` for all `j' < n`
  have hround : ∀ j, flagR C p = true → (∀ j' < j, consR C j' = some false) → j < n := by
    intro j hf hj
    by_contra hjn
    obtain ⟨q, hq, hqc⟩ := exists_flag_consR_ne_false ⟨p, hf⟩
    exact hqc (hj q (lt_of_lt_of_le (hσ q (G.flag_mem q hq)) (not_lt.1 hjn)))
  obtain ⟨op, k, hact⟩ := h
  cases hl : C.loc p with
  | wProp i v =>
    rw [hl] at hL hact; cases hact; simp [Obj.idx, hL.1, hp]
  | wFlag i v =>
    rw [hl] at hL hact; cases hact; simp [Obj.idx, hL.1, hp]
  | rFlag v j =>
    rw [hl] at hL hact; cases hact; exact hround j hL.1 hL.2
  | prop v j b =>
    rw [hl] at hL hact; cases hact; exact hround j hL.1 hL.2.1
  | rVal v j =>
    rw [hl] at hL hact; cases hact
    exact hσ j (G.flag_mem j (G.cons_true j hL.2.2))
  | done w => rw [hl] at hact; cases hact

/-- Algorithm 3 solves consensus in the classical model `Mⁿ₁` (processes `p₀, …, p_{n-1}`). -/
theorem alg3_solvesCons_bounded (V : Type) (n : ℕ) :
    SolvesCons (alg3 V) (belowN n) (boundedBy n) :=
  ⟨fun x σ _ => alg3_agreement x σ trivial, fun x σ _ => alg3_validity x σ trivial,
    alg3_waitFree.mono (fun _ _ => trivial)⟩

end Podc.InfiniteArrivalHierarchy.Alg3
