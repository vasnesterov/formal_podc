import Papers.PODC2025.TwoShotConsensusObjects.Model

/-!
# Common infrastructure for the algorithms of Section 5 (classes `C₁` and `C₁.₅`)

* the shared registers `Val[i]` (`Option Bool`) and `Ret[i]` (`Option ρ`, `ρ` = responses of `O`),
  all initially `⊥ = none`;
* `wfConsensus_of_inv`: wait-free consensus from an invariant of reachable configurations
  stating that all output values equal the input of one process, plus a ranking function;
* `il`: the interleaving of `O`-operations described by the list of *roles* of its steps
  (role `0` = process `a` applying `f` then `f'`, role `1` = process `b` applying `g` then `g'`);
* `Snap h P`: some prefix of the role history `h` satisfies `P` (a stable "it happened" fact).


Everything lives in the namespace `TwoShotCons.C1Common`.
-/

namespace TwoShotCons.C1Common

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

/-- Register names: `Val[i]` and `Ret[i]`. -/
inductive Reg
  | val (i : Fin 2)
  | ret (i : Fin 2)
  deriving DecidableEq

/-- The registers: `Val[i]` holds `Option Bool`, `Ret[i]` holds `Option ρ` (`⊥ = none`). -/
abbrev RegT (ρ : Type) : Reg → ObjSpec
  | .val _ => register (Option Bool) none
  | .ret _ => register (Option ρ) none

lemma isRW_RegT (ρ : Type) : ∀ j, IsRW (RegT ρ j)
  | .val _ => isRW_register _ _
  | .ret _ => isRW_register _ _

/-- The objects of the algorithms: the registers and one copy of `O`. -/
abbrev Obj (O : ObjSpec) : Reg ⊕ Unit → ObjSpec := withRW (ιS := Unit) (RegT O.Resp) O

section Upd

variable {O : ObjSpec} (m : (i : Reg ⊕ Unit) → (Obj O i).State)

@[simp] lemma upd_val_val (q r : Fin 2) (v : Option Bool) :
    (Function.update m (.inl (.val q)) v) (.inl (.val r)) =
      if r = q then v else m (.inl (.val r)) := by
  by_cases h : r = q
  · subst h; simp [Function.update]
  · simp [Function.update, h]; rfl

@[simp] lemma upd_ret_ret (q r : Fin 2) (v : Option O.Resp) :
    (Function.update m (.inl (.ret q)) v) (.inl (.ret r)) =
      if r = q then v else m (.inl (.ret r)) := by
  by_cases h : r = q
  · subst h; simp [Function.update]
  · simp [Function.update, h]; rfl

@[simp] lemma upd_val_ret (q r : Fin 2) (v : Option Bool) :
    (Function.update m (.inl (.val q)) v) (.inl (.ret r)) = m (.inl (.ret r)) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_ret_val (q r : Fin 2) (v : Option O.Resp) :
    (Function.update m (.inl (.ret q)) v) (.inl (.val r)) = m (.inl (.val r)) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_val_obj (q : Fin 2) (v : Option Bool) :
    (Function.update m (.inl (.val q)) v) (.inr ()) = m (.inr ()) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_ret_obj (q : Fin 2) (v : Option O.Resp) :
    (Function.update m (.inl (.ret q)) v) (.inr ()) = m (.inr ()) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_obj_val (r : Fin 2) (v : O.State) :
    (Function.update m (.inr ()) v) (.inl (.val r)) = m (.inl (.val r)) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_obj_ret (r : Fin 2) (v : O.State) :
    (Function.update m (.inr ()) v) (.inl (.ret r)) = m (.inl (.ret r)) :=
  Function.update_of_ne (by simp) _ _

@[simp] lemma upd_obj_obj (v : O.State) :
    (Function.update m (.inr ()) v) (.inr ()) = v := by simp [Function.update]

/-- Reading a register does not change the memory. -/
@[simp] lemma upd_read_val (j : Fin 2) :
    Function.update m (.inl (.val j))
      ((Obj O (.inl (.val j))).δ (m (.inl (.val j))) RWOp.read).1 = m :=
  Function.update_eq_self _ _

/-- Reading a register does not change the memory. -/
@[simp] lemma upd_read_ret (j : Fin 2) :
    Function.update m (.inl (.ret j))
      ((Obj O (.inl (.ret j))).δ (m (.inl (.ret j))) RWOp.read).1 = m :=
  Function.update_eq_self _ _

end Upd

section Generic

variable {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {A : Alg 2 T}

/-- Output states are stable along crash-free executions. -/
lemma out_run {C : Cfg A} {p : Fin 2} {v : Bool} (h : C.Out p v) (β : List (Ev 2))
    (hβ : CrashFree β) : (run C β).Out p v := by
  induction β generalizing C with
  | nil => simpa using h
  | cons e β ih =>
    rw [run_cons]
    apply ih _ (fun q hq => hβ q (by simp [hq]))
    rcases e with q | q
    · by_cases hq : q = p
      · subst hq; simp only [Cfg.next]; rw [stepP_of_out C h]; exact h
      · simp only [Cfg.Out, Cfg.next] at h ⊢
        rw [stepP_loc_other C (Ne.symm hq)]; exact h
    · exact absurd (by simp) (hβ q)

/-- **Wait-free consensus from an invariant.** If an invariant of reachable configurations
implies that all output values are the input of a single process, and a rank strictly decreases
at each access, the algorithm solves wait-free consensus. -/
theorem wfConsensus_of_inv (Inv : (Fin 2 → Bool) → Cfg A → Prop)
    (hinit : ∀ x, Inv x (initCfg A x))
    (hstep : ∀ x C p, Inv x C → Inv x (C.stepP p))
    (hout : ∀ x C, Inv x C → ∃ q, ∀ p w, C.Out p w → w = x q)
    (rank : A.L → ℕ)
    (hrank : ∀ l i o (κ : (T i).Resp → A.L) r, A.act l = .access i o κ → rank (κ r) < rank l) :
    WFConsensus A := by
  have reach : ∀ x (α : List (Ev 2)) (C : Cfg A), Inv x C → CrashFree α → Inv x (run C α) := by
    intro x α
    induction α with
    | nil => intro C h _; simpa using h
    | cons e α ih =>
      intro C hC hα
      rw [run_cons]
      apply ih _ _ (fun q hq => hα q (by simp [hq]))
      rcases e with q | q
      · exact hstep x C q hC
      · exact absurd (by simp) (hα q)
  -- every decision in a crash-free execution persists to its end
  have persist : ∀ x γ, CrashFree γ → ∀ v, Dec (initCfg A x) γ v →
      ∃ p, (run (initCfg A x) γ).Out p v := by
    intro x γ hγ v ⟨k, hk, p, hp⟩
    refine ⟨p, ?_⟩
    have := out_run hp (γ.drop k) (fun q hq => hγ q (List.mem_of_mem_drop hq))
    rwa [← run_append, List.take_append_drop] at this
  refine ⟨?_, ?_, ?_⟩
  · intro x γ hγ v w hv hw
    obtain ⟨p, hp⟩ := persist x γ hγ v hv
    obtain ⟨p', hp'⟩ := persist x γ hγ w hw
    obtain ⟨q, hq⟩ := hout x _ (reach x γ _ (hinit x) hγ)
    rw [hq p v hp, hq p' w hp']
  · intro x γ hγ v hv
    obtain ⟨p, hp⟩ := persist x γ hγ v hv
    obtain ⟨q, hq⟩ := hout x _ (reach x γ _ (hinit x) hγ)
    exact ⟨q, (hq p v hp).symm⟩
  · intro x e p N hadm hinf _
    exact prog_of_rank rank hrank x e p N hadm hinf

end Generic

/-! ## Role histories -/

section Roles

variable (O : ObjSpec) (a b : Fin 2) (f f' g g' : O.Op)

/-- The interleaving of `O`-operations described by a list of roles: the `k`-th step of role `0`
is process `a` applying `f` (`k = 0`) or `f'` (`k ≥ 1`), the `k`-th step of role `1` is process
`b` applying `g` or `g'`. `c₀`, `c₁` count the steps of each role already done. -/
def ilAux : ℕ → ℕ → List (Fin 2) → List (Fin 2 × O.Op)
  | _, _, [] => []
  | c₀, c₁, r :: t =>
    if r = 0 then (a, if c₀ = 0 then f else f') :: ilAux (c₀ + 1) c₁ t
    else (b, if c₁ = 0 then g else g') :: ilAux c₀ (c₁ + 1) t

/-- The interleaving described by the role history `h`. -/
def il (h : List (Fin 2)) : List (Fin 2 × O.Op) := ilAux O a b f f' g g' 0 0 h

lemma ilAux_append (c₀ c₁ : ℕ) (h : List (Fin 2)) (r : Fin 2) :
    ilAux O a b f f' g g' c₀ c₁ (h ++ [r]) = ilAux O a b f f' g g' c₀ c₁ h ++
      [if r = 0 then (a, if c₀ + h.count 0 = 0 then f else f')
        else (b, if c₁ + h.count 1 = 0 then g else g')] := by
  induction h generalizing c₀ c₁ with
  | nil => by_cases hr : r = 0 <;> simp [ilAux, hr]
  | cons r' t ih =>
    by_cases h0 : r' = 0
    · subst h0; simp [ilAux, ih]
    · have h1 : r' = 1 := by omega
      subst h1; simp [ilAux, ih]

lemma il_append (h : List (Fin 2)) (r : Fin 2) :
    il O a b f f' g g' (h ++ [r]) = il O a b f f' g g' h ++
      [if r = 0 then (a, if h.count 0 = 0 then f else f')
        else (b, if h.count 1 = 0 then g else g')] := by
  simp [il, ilAux_append]

end Roles

lemma resps_append (O : ObjSpec) (s : O.State) (σ τ : List (Fin 2 × O.Op)) :
    resps O s (σ ++ τ) = resps O s σ ++ resps O (after O s σ) τ := by
  induction σ generalizing s with
  | nil => simp
  | cons x σ ih => obtain ⟨p, c⟩ := x; simp [ih]

lemma after_append (O : ObjSpec) (s : O.State) (σ τ : List (Fin 2 × O.Op)) :
    after O s (σ ++ τ) = after O (after O s σ) τ := by
  induction σ generalizing s with
  | nil => simp
  | cons x σ ih => obtain ⟨p, c⟩ := x; simp [ih]

lemma view_append (O : ObjSpec) (s : O.State) (σ τ : List (Fin 2 × O.Op)) (p : Fin 2) :
    view O s (σ ++ τ) p = view O s σ p ++ view O (after O s σ) τ p := by
  simp [view, resps_append]

lemma view_single_self (O : ObjSpec) (s : O.State) (p : Fin 2) (c : O.Op) :
    view O s [(p, c)] p = [(O.δ s c).2] := by simp [view]

lemma view_single_other (O : ObjSpec) (s : O.State) {p q : Fin 2} (h : q ≠ p) (c : O.Op) :
    view O s [(q, c)] p = [] := by simp [view, h]

/-- Some prefix of the history `h` satisfies `P`. -/
def Snap (h : List (Fin 2)) (P : List (Fin 2) → Prop) : Prop :=
  ∃ k ≤ h.length, P (h.take k)

lemma Snap.now {h : List (Fin 2)} {P : List (Fin 2) → Prop} (hP : P h) : Snap h P :=
  ⟨h.length, le_rfl, by simpa using hP⟩

lemma Snap.append {h : List (Fin 2)} {P : List (Fin 2) → Prop} (hP : Snap h P)
    (t : List (Fin 2)) : Snap (h ++ t) P := by
  obtain ⟨k, hk, hP⟩ := hP
  exact ⟨k, by simp; omega, by rwa [List.take_append_of_le_length hk]⟩

/-- Role histories with at most two steps per role. -/
lemma mem_hist {h : List (Fin 2)} (h0 : h.count 0 ≤ 2) (h1 : h.count 1 ≤ 2) :
    h ∈ ([[], [0], [1], [0, 0], [0, 1], [1, 0], [1, 1],
      [0, 0, 1], [0, 1, 0], [1, 0, 0], [0, 1, 1], [1, 0, 1], [1, 1, 0],
      [0, 0, 1, 1], [0, 1, 0, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 0, 1, 0], [1, 1, 0, 0]] :
        List (List (Fin 2))) := by
  rcases h with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, t⟩⟩⟩⟩⟩
  · decide
  all_goals fin_cases x1
  all_goals try fin_cases x2
  all_goals try fin_cases x3
  all_goals try fin_cases x4
  all_goals try fin_cases x5
  all_goals simp at h0 h1 ⊢

/-- The role histories with at most two steps per role, as a disjunction. -/
lemma hist_cases {h : List (Fin 2)} (h0 : h.count 0 ≤ 2) (h1 : h.count 1 ≤ 2) :
    h = [] ∨ h = [0] ∨ h = [1] ∨ h = [0, 0] ∨ h = [0, 1] ∨ h = [1, 0] ∨ h = [1, 1] ∨
    h = [0, 0, 1] ∨ h = [0, 1, 0] ∨ h = [1, 0, 0] ∨ h = [0, 1, 1] ∨ h = [1, 0, 1] ∨
    h = [1, 1, 0] ∨ h = [0, 0, 1, 1] ∨ h = [0, 1, 0, 1] ∨ h = [0, 1, 1, 0] ∨
    h = [1, 0, 0, 1] ∨ h = [1, 0, 1, 0] ∨ h = [1, 1, 0, 0] := by
  simpa using mem_hist h0 h1

end TwoShotCons.C1Common
