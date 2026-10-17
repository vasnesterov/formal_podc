import Papers.PODC2011.TimestampSpace.SimpleAlgCorrect
import Papers.PODC2011.TimestampSpace.LongLived

/-!
# Non-vacuity of Theorem 1.1: a long-lived timestamp implementation from `n` registers

The folklore "max + 1" algorithm (not from the paper): process `p` owns register `R[p]` (CSLib
register over `ℕ`, initially `0`); `getTS` reads `R[0], …, R[n-1]`, computes their maximum `mx`,
writes `mx + 1` to `R[p]` and returns `mx + 1`; `compare t₁ t₂` returns `t₁ < t₂` without
accessing memory.

It is a wait-free **long-lived** timestamp implementation from `n` read/write registers
(`maxTS_isTS`, `maxTS_waitFree`, `maxTS_rwLike`), so the hypotheses of Theorem 1.1
(`theorem_1_1`) are satisfiable for every `n`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.MaxTS

open Cslib.SharedMemory

/-- Program counter (= local state). -/
inductive PC where
  /-- No pending operation. -/
  | idle
  /-- `compare` computed; about to return `b`. -/
  | cmp (b : Bool)
  /-- `getTS`: about to read `R[i]` (or, if `i = n`, to write `mx + 1`); `mx` = maximum so far. -/
  | rd (i mx : ℕ)
  /-- `getTS`: has written `t`; about to return it. -/
  | fin (t : ℕ)

variable {n : ℕ}

/-- The base objects: `n` registers over `ℕ`, initially `0`. -/
abbrev Regs (n : ℕ) : Fin n → ObjSpec := fun _ => register ℕ 0

/-- One step of a process. -/
def act (p : Fin n) (l : PC) : Action (tsObj ℕ) (Regs n) PC :=
  match l with
  | .idle => .ret (.inr false) .idle
  | .cmp b => .ret (.inr b) .idle
  | .rd i mx =>
    if h : i < n then .access ⟨i, h⟩ .read (fun v => .rd (i + 1) (max mx v))
    else .access p (.write (mx + 1)) (fun _ => .fin (mx + 1))
  | .fin t => .ret (.inl t) .idle

/-- Local state after an invocation. -/
def invoke : TSOp ℕ → PC
  | .getTS => .rd 0 0
  | .compare a b => .cmp (decide (a < b))

/-- The "max + 1" timestamp algorithm for `n` processes from `n` registers. -/
def alg (n : ℕ) : Impl (tsObj ℕ) (Regs n) (Fin n) PC where
  memInit _ := 0
  locInit _ := .idle
  invoke _ _ o := invoke o
  act := act

/-- The base objects are registers, hence read/write-like. -/
theorem maxTS_rwLike : RWLike (Regs n) := rwLike_register (V := fun _ : Fin n => ℕ) (fun _ => 0)

/-- Wait-freedom: at most `n + 1` accesses per `getTS`. -/
theorem maxTS_waitFree : (alg n).WaitFree := by
  refine (alg n).waitFree_of_potential
    (fun _ l => match l with | .rd i _ => n - i + 2 | _ => 0) ?_
  intro p l i o k hact x
  cases l with
  | idle => simp [alg, act] at hact
  | cmp b => simp [alg, act] at hact
  | fin t => simp [alg, act] at hact
  | rd j mx =>
    simp only [alg, act] at hact
    split_ifs at hact with h
    · cases hact; simp; omega
    · cases hact; simp

/-! ### Maxima of register values -/

/-- Maximum of the registers `R[j]`, `j ≥ i` (`0` if there are none). -/
def sm (M : Fin n → ℕ) (i : ℕ) : ℕ := (Finset.univ.filter (fun j : Fin n => i ≤ j.val)).sup M

lemma sm_succ (M : Fin n → ℕ) {i : ℕ} (h : i < n) : sm M i = max (M ⟨i, h⟩) (sm M (i + 1)) := by
  unfold sm
  have : Finset.univ.filter (fun j : Fin n => i ≤ j.val) =
      insert ⟨i, h⟩ (Finset.univ.filter (fun j : Fin n => i + 1 ≤ j.val)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.sup_insert]

lemma sm_ge (M : Fin n → ℕ) {i : ℕ} (h : n ≤ i) : sm M i = 0 := by
  unfold sm
  rw [Finset.filter_false_of_mem (fun j _ => by have := j.isLt; omega)]
  rfl

lemma sm_mono {M M' : Fin n → ℕ} (h : ∀ j, M j ≤ M' j) (i : ℕ) : sm M i ≤ sm M' i :=
  Finset.sup_mono_fun fun j _ => h j

lemma le_sm (M : Fin n → ℕ) {i : ℕ} (j : Fin n) (h : i ≤ j.val) : M j ≤ sm M i :=
  Finset.le_sup (f := M) (by simp [h])

/-! ### The invariant -/

/-- Configurations. -/
abbrev Cfg (n : ℕ) := Config (tsObj ℕ) (Regs n) (Fin n) PC

/-- Executions. -/
abbrev Exec (n : ℕ) := List (Label (Fin n) (tsObj ℕ))

/-- Consistency of the pending operation with the program counter. -/
def PendOK : Option (TSOp ℕ) → PC → Prop
  | none, .idle => True
  | some .getTS, .rd _ _ => True
  | some .getTS, .fin _ => True
  | some (.compare a b), .cmp c => c = decide (a < b)
  | _, _ => False

/-- Lower bound on the value a pending `getTS` will return. -/
def LB (l : PC) (M : Fin n → ℕ) : ℕ :=
  match l with
  | .rd i mx => max mx (sm M i) + 1
  | .fin t => t
  | _ => 0

/-- Responses of completed operations. -/
def RespOK : TSOp ℕ → ℕ ⊕ Bool → Prop
  | .getTS, r => ∃ t, r = .inl t
  | .compare a b, r => r = .inr (decide (a < b))

lemma LB_mono {M M' : Fin n → ℕ} (h : ∀ j, M j ≤ M' j) (l : PC) : LB l M ≤ LB l M' := by
  cases l with
  | rd i mx => simp only [LB]; have := sm_mono h i; omega
  | _ => exact le_rfl

/-- The invariant (every execution: long-lived). -/
structure Inv (α : Exec n) (C : Cfg n) : Prop where
  pend : ∀ p, PendOK (C.pend p) (C.loc p)
  own : ∀ p i mx, C.loc p = .rd i mx → p.val < i → C.mem p ≤ mx
  fin_le : ∀ p t, C.loc p = .fin t → t ≤ C.mem p
  done_le : ∀ g t, opOf α g = some .getTS → respOf α g = some (.inl t) → t ≤ sm C.mem 0
  lb : ∀ q g t, C.pend q = some .getTS → opOf α g = some .getTS →
    respOf α g = some (.inl t) → Precedes α g (q, (respsOf α q).length) → t < LB (C.loc q) C.mem
  order : ∀ g₁ g₂ t₁ t₂, opOf α g₁ = some .getTS → respOf α g₁ = some (.inl t₁) →
    opOf α g₂ = some .getTS → respOf α g₂ = some (.inl t₂) → Precedes α g₁ g₂ → t₁ < t₂
  resp : ∀ g o r, opOf α g = some o → respOf α g = some r → RespOK o r

variable {C C' : Cfg n} {p : Fin n}

lemma step_inv_eq {o : TSOp ℕ} (h : (alg n).step C (.inv p o) = some C') :
    C.pend p = none ∧ C' = ⟨Function.update C.loc p (invoke o),
      Function.update C.pend p (some o), C.mem⟩ := by
  obtain ⟨h0, -, h1, h2, h3⟩ := Impl.step_inv h
  refine ⟨h0, ?_⟩
  obtain ⟨l', p', m'⟩ := C'
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

lemma step_ret_eq {r : ℕ ⊕ Bool} (h : (alg n).step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ ∃ l, act p (C.loc p) = .ret r l ∧
      C' = ⟨Function.update C.loc p l, Function.update C.pend p none, C.mem⟩ := by
  obtain ⟨h0, h1, h2, l, hl, h3⟩ := Impl.step_ret h
  refine ⟨h0, l, hl, ?_⟩
  obtain ⟨l', p', m'⟩ := C'
  simp only at h1 h2 h3; subst h1 h2 h3; rfl

lemma step_tau_eq (h : (alg n).step C (.tau p) = some C') :
    C.pend p ≠ none ∧
    ((∃ i mx, C.loc p = .rd i mx ∧ ∃ hi : i < n,
        C' = ⟨Function.update C.loc p (.rd (i + 1) (max mx (C.mem ⟨i, hi⟩))), C.pend, C.mem⟩) ∨
      (∃ i mx, C.loc p = .rd i mx ∧ n ≤ i ∧
        C' = ⟨Function.update C.loc p (.fin (mx + 1)), C.pend,
          Function.update C.mem p (mx + 1)⟩)) := by
  have h0 := (Impl.step_tau h).1
  refine ⟨h0, ?_⟩
  simp only [Impl.step, h0, ite_false, alg, act] at h
  rcases hl : C.loc p with _ | b | ⟨i, mx⟩ | t
  · rw [hl] at h; simp at h
  · rw [hl] at h; simp at h
  · rw [hl] at h
    simp only at h
    split_ifs at h with hi
    · simp only [Option.some.injEq] at h
      subst h
      left; exact ⟨i, mx, rfl, hi, by simp⟩
    · simp only [Option.some.injEq] at h
      subst h
      right; exact ⟨i, mx, rfl, by omega, by simp⟩
  · rw [hl] at h; simp at h

/-! ### Preservation -/

lemma pendOK_none {l : PC} (h : PendOK none l) : l = .idle := by
  cases l <;> simp_all [PendOK]

lemma inv_init : Inv ([] : Exec n) (alg n).initCfg where
  pend _ := trivial
  own _ _ _ h := by simp [Impl.initCfg, alg] at h
  fin_le _ _ h := by simp [Impl.initCfg, alg] at h
  done_le _ _ h := by simp [opOf] at h
  lb _ _ _ h := by simp [Impl.initCfg] at h
  order _ _ _ _ h := by simp [opOf] at h
  resp _ _ _ h := by simp [opOf] at h

/-- Internal steps preserve the invariant. -/
lemma inv_tau {α : Exec n} (hI : Inv α C) (hs : (alg n).step C (.tau p) = some C') :
    Inv (α ++ [.tau p]) C' := by
  have hne : ∀ q r, (Label.tau p : Label (Fin n) (tsObj ℕ)) ≠ .ret q r := by simp
  have hni : ∀ q o, (Label.tau p : Label (Fin n) (tsObj ℕ)) ≠ .inv q o := by simp
  have hg : ∀ i mx, C.loc p = .rd i mx → C.pend p = some .getTS := by
    intro i mx h
    have := hI.pend p; rw [h] at this
    rcases hp : C.pend p with _ | _ | ⟨a, b⟩ <;> simp_all [PendOK]
  obtain ⟨h0, ⟨i, mx, hpc, hi, rfl⟩ | ⟨i, mx, hpc, hi, rfl⟩⟩ := step_tau_eq hs
  · -- a read
    refine ⟨fun q => ?_, fun q i' mx' h hq => ?_, fun q t h => ?_, fun g t h1 h2 => ?_,
      fun q g t hq h1 h2 h3 => ?_, fun g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5 => ?_, fun g o r h1 h2 => ?_⟩
    · by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self]; rw [hg i mx hpc]; trivial
      · simpa [Function.update_of_ne hqp] using hI.pend q
    · by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, PC.rd.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only
        rcases Nat.lt_or_ge q.val i with h1 | h1
        · exact (hI.own q i mx hpc h1).trans (le_max_left _ _)
        · have : q = ⟨i, hi⟩ := Fin.ext (by simp; omega)
          subst this; exact le_max_right _ _
      · simp only [Function.update_of_ne hqp] at h
        exact hI.own q i' mx' h hq
    · by_cases hqp : q = p
      · subst hqp; simp at h
      · simp only [Function.update_of_ne hqp] at h; exact hI.fin_le q t h
    · rw [opOf_concat_of_ne (x := g) (hni g.1)] at h1
      rw [respOf_concat_of_ne (x := g) (hne g.1)] at h2
      exact hI.done_le g t h1 h2
    · rw [opOf_concat_of_ne (x := g) (hni g.1)] at h1
      rw [respOf_concat_of_ne (x := g) (hne g.1)] at h2
      rw [respsOf_concat_of_ne (hne q)] at h3
      have key := hI.lb q g t hq h1 h2 (Precedes.of_concat_of_not_ret hne h3)
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, LB]
        rw [hpc] at key; simp only [LB] at key
        rw [sm_succ _ hi] at key; omega
      · simpa [Function.update_of_ne hqp] using key
    · rw [opOf_concat_of_ne (x := g₁) (hni g₁.1), opOf_concat_of_ne (x := g₂) (hni g₂.1)] at *
      rw [respOf_concat_of_ne (x := g₁) (hne g₁.1), respOf_concat_of_ne (x := g₂) (hne g₂.1)] at *
      exact hI.order g₁ g₂ t₁ t₂ h1 h2 h3 h4 (Precedes.of_concat_of_not_ret hne h5)
    · rw [opOf_concat_of_ne (x := g) (hni g.1)] at h1
      rw [respOf_concat_of_ne (x := g) (hne g.1)] at h2
      exact hI.resp g o r h1 h2
  · -- the write
    have hown : C.mem p ≤ mx := hI.own p i mx hpc (by have := p.isLt; omega)
    have hmem : ∀ j, C.mem j ≤ Function.update C.mem p (mx + 1) j := by
      intro j; by_cases hj : j = p
      · rw [hj]; simp only [Function.update_self]; exact le_trans hown (Nat.le_succ mx)
      · simp [Function.update_of_ne hj]
    refine ⟨fun q => ?_, fun q i' mx' h hq => ?_, fun q t h => ?_, fun g t h1 h2 => ?_,
      fun q g t hq h1 h2 h3 => ?_, fun g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5 => ?_, fun g o r h1 h2 => ?_⟩
    · by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self]; rw [hg i mx hpc]; trivial
      · simpa [Function.update_of_ne hqp] using hI.pend q
    · by_cases hqp : q = p
      · subst hqp; simp at h
      · simp only [Function.update_of_ne hqp] at h ⊢
        exact hI.own q i' mx' h hq
    · by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, PC.fin.injEq] at h ⊢; omega
      · simp only [Function.update_of_ne hqp] at h ⊢; exact hI.fin_le q t h
    · rw [opOf_concat_of_ne (x := g) (hni g.1)] at h1
      rw [respOf_concat_of_ne (x := g) (hne g.1)] at h2
      exact (hI.done_le g t h1 h2).trans (sm_mono hmem 0)
    · rw [opOf_concat_of_ne (x := g) (hni g.1)] at h1
      rw [respOf_concat_of_ne (x := g) (hne g.1)] at h2
      rw [respsOf_concat_of_ne (hne q)] at h3
      have key := hI.lb q g t hq h1 h2 (Precedes.of_concat_of_not_ret hne h3)
      by_cases hqp : q = p
      · subst hqp
        simp only [Function.update_self, LB]
        rw [hpc] at key; simp only [LB, sm_ge _ hi] at key; omega
      · simp only [Function.update_of_ne hqp]
        exact key.trans_le (LB_mono hmem _)
    · rw [opOf_concat_of_ne (x := g₁) (hni g₁.1), opOf_concat_of_ne (x := g₂) (hni g₂.1)] at *
      rw [respOf_concat_of_ne (x := g₁) (hne g₁.1), respOf_concat_of_ne (x := g₂) (hne g₂.1)] at *
      exact hI.order g₁ g₂ t₁ t₂ h1 h2 h3 h4 (Precedes.of_concat_of_not_ret hne h5)
    · rw [opOf_concat_of_ne (x := g) (hni g.1)] at h1
      rw [respOf_concat_of_ne (x := g) (hne g.1)] at h2
      exact hI.resp g o r h1 h2

/-- Invocations preserve the invariant. -/
lemma inv_inv {α : Exec n} {o : TSOp ℕ} (hI : Inv α C) (hrun : (alg n).run α = some C)
    (hs : (alg n).step C (.inv p o) = some C') : Inv (α ++ [.inv p o]) C' := by
  obtain ⟨h0, rfl⟩ := step_inv_eq hs
  have hidle : C.loc p = .idle := pendOK_none (h0 ▸ hI.pend p)
  have hne : ∀ q r, (Label.inv p o : Label (Fin n) (tsObj ℕ)) ≠ .ret q r := by simp
  have hresp : ∀ g, respOf (α ++ [.inv p o]) g = respOf α g :=
    fun g => respOf_concat_of_ne (x := g) (hne g.1)
  have hop : ∀ g r, respOf α g = some r → opOf (α ++ [.inv p o]) g = opOf α g := by
    intro g r h
    apply opOf_append_of_invoked
    have h1 := Completed.of_respOf_eq_some h
    have h2 := Impl.run_resps_le_ops hrun g.1
    simp only [Invoked, Completed] at *; omega
  refine ⟨fun q => ?_, fun q i mx h hq => ?_, fun q t h => ?_, fun g t h1 h2 => ?_,
    fun q g t hq h1 h2 h3 => ?_, fun g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5 => ?_, fun g o' r h1 h2 => ?_⟩
  · by_cases hq : q = p
    · subst hq; cases o <;> simp [PendOK, invoke]
    · simpa [Function.update_of_ne hq] using hI.pend q
  · by_cases hqp : q = p
    · subst hqp
      cases o with
      | getTS => simp only [Function.update_self, invoke, PC.rd.injEq] at h; omega
      | compare a b => simp [invoke] at h
    · simp only [Function.update_of_ne hqp] at h; exact hI.own q i mx h hq
  · by_cases hqp : q = p
    · subst hqp; cases o <;> simp [invoke] at h
    · simp only [Function.update_of_ne hqp] at h; exact hI.fin_le q t h
  · rw [hresp] at h2; rw [hop g _ h2] at h1
    exact hI.done_le g t h1 h2
  · rw [hresp] at h2; rw [hop g _ h2] at h1
    rw [respsOf_concat_of_ne (hne q)] at h3
    have h3 := Precedes.of_concat_of_not_ret hne h3
    by_cases hqp : q = p
    · subst hqp
      simp only [Function.update_self, Option.some.injEq] at hq
      subst hq
      have := hI.done_le g t h1 h2
      simp only [Function.update_self, LB, invoke]; omega
    · simp only [Function.update_of_ne hqp] at hq ⊢
      exact hI.lb q g t hq h1 h2 h3
  · rw [hresp] at h2 h4; rw [hop _ _ h2] at h1; rw [hop _ _ h4] at h3
    exact hI.order g₁ g₂ t₁ t₂ h1 h2 h3 h4 (Precedes.of_concat_of_not_ret hne h5)
  · rw [hresp] at h2; rw [hop _ _ h2] at h1
    exact hI.resp g o' r h1 h2

/-- Responses preserve the invariant. -/
lemma inv_ret {α : Exec n} {r : ℕ ⊕ Bool} (hI : Inv α C) (hrun : (alg n).run α = some C)
    (hs : (alg n).step C (.ret p r) = some C') : Inv (α ++ [.ret p r]) C' := by
  obtain ⟨h0, l, hact, rfl⟩ := step_ret_eq hs
  obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
  have hop0 := (Impl.run_pend_curOp hrun ho).2.2
  have hni : ∀ q o, (Label.ret p r : Label (Fin n) (tsObj ℕ)) ≠ .inv q o := by simp
  have hopeq : ∀ g, opOf (α ++ [.ret p r]) g = opOf α g :=
    fun g => opOf_concat_of_ne (x := g) (hni g.1)
  have hcase : (∃ b, C.loc p = .cmp b ∧ r = .inr b ∧ l = .idle) ∨
      (∃ t, C.loc p = .fin t ∧ r = .inl t ∧ l = .idle) := by
    revert hact
    rcases hl : C.loc p with _ | b | ⟨i, mx⟩ | t <;> intro hact
    · have := hI.pend p; rw [ho, hl] at this; cases o <;> simp [PendOK] at this
    · simp only [act, Action.ret.injEq] at hact
      exact Or.inl ⟨b, rfl, hact.1.symm, hact.2.symm⟩
    · simp only [act] at hact; split_ifs at hact
    · simp only [act, Action.ret.injEq] at hact
      exact Or.inr ⟨t, rfl, hact.1.symm, hact.2.symm⟩
  have hl : l = .idle := by rcases hcase with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> exact h
  have hnew : ∀ g r', respOf (α ++ [.ret p r]) g = some r' →
      respOf α g = some r' ∨ (g = (p, (respsOf α p).length) ∧ r' = r) := by
    intro g r' h
    rcases respOf_concat_cases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · simp only [Label.ret.injEq] at h1
      obtain ⟨h1, rfl⟩ := h1
      right; refine ⟨Prod.ext h1.symm ?_, rfl⟩
      rw [h2, ← h1]
  have hval : o = .getTS → ∃ t, C.loc p = .fin t ∧ r = .inl t := by
    rintro rfl
    rcases hcase with ⟨b, hb, -⟩ | ⟨t, h1, h2, -⟩
    · have := hI.pend p; rw [ho, hb] at this; simp [PendOK] at this
    · exact ⟨t, h1, h2⟩
  have hcompl : ∀ g r', respOf (α ++ [.ret p r]) g = some r' → Completed α g →
      respOf α g = some r' := by
    intro g r' h hc; rwa [respOf_append_of_completed hc] at h
  refine ⟨fun q => ?_, fun q i mx h hq => ?_, fun q t h => ?_, fun g t h1 h2 => ?_,
    fun q g t hq h1 h2 h3 => ?_, fun g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5 => ?_, fun g o' r' h1 h2 => ?_⟩
  · by_cases hq : q = p
    · subst hq; simp [hl, PendOK]
    · simpa [Function.update_of_ne hq] using hI.pend q
  · by_cases hqp : q = p
    · subst hqp; simp [hl] at h
    · simp only [Function.update_of_ne hqp] at h; exact hI.own q i mx h hq
  · by_cases hqp : q = p
    · subst hqp; simp [hl] at h
    · simp only [Function.update_of_ne hqp] at h; exact hI.fin_le q t h
  · rw [hopeq] at h1
    rcases hnew g _ h2 with h2 | ⟨rfl, hr⟩
    · exact hI.done_le g t h1 h2
    · rw [hop0] at h1
      obtain ⟨t', hpc, hrs⟩ := hval (Option.some.inj h1)
      rw [hrs] at hr; cases hr
      exact (hI.fin_le p t hpc).trans (le_sm _ p (Nat.zero_le _))
  · have hqp : q ≠ p := by rintro rfl; simp at hq
    simp only [Function.update_of_ne hqp] at hq ⊢
    rw [hopeq] at h1
    rw [respsOf_concat_of_ne (q := q) (by simp [Ne.symm hqp])] at h3
    rcases precedes_concat h3 with h3 | ⟨-, h4⟩
    · exact hI.lb q g t hq h1 (hcompl g _ h2 h3.completed) h3
    · exact absurd (Invoked.of_opOf_eq_some ((Impl.run_pend_curOp hrun hq).2.2)).mono h4
  · rw [hopeq] at h1 h3
    rcases precedes_concat h5 with h5 | ⟨-, h6⟩
    · have h2' := hcompl g₁ _ h2 h5.completed
      rcases hnew g₂ _ h4 with h4 | ⟨rfl, hr⟩
      · exact hI.order g₁ g₂ t₁ t₂ h1 h2' h3 h4 h5
      · rw [hop0] at h3
        have hog := Option.some.inj h3
        obtain ⟨t, hpc, hrs⟩ := hval hog
        rw [hrs] at hr; cases hr
        have := hI.lb p g₁ t₁ (by rw [ho, hog]) h1 h2' h5
        simpa only [LB, hpc] using this
    · exact absurd (Invoked.of_opOf_eq_some h3).mono h6
  · rw [hopeq] at h1
    rcases hnew g _ h2 with h2 | ⟨rfl, rfl⟩
    · exact hI.resp g o' r' h1 h2
    · rw [hop0] at h1
      cases Option.some.inj h1
      rcases hcase with ⟨b, hb, rfl, -⟩ | ⟨t, hpc, rfl, -⟩
      · have := hI.pend p; rw [ho, hb] at this
        cases o with
        | getTS => simp [PendOK] at this
        | compare a b' => simp only [PendOK] at this; subst this; rfl
      · have := hI.pend p; rw [ho, hpc] at this
        cases o with
        | getTS => exact ⟨t, rfl⟩
        | compare a b' => simp [PendOK] at this

/-- The invariant holds in every execution. -/
theorem inv_run {α : Exec n} {C : Cfg n} (h : (alg n).run α = some C) : Inv α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [Impl.run_nil, Option.some.injEq] at h; subst h; exact inv_init
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases h1 : (alg n).runFrom (alg n).initCfg α with
    | none => simp [h1] at h
    | some C₁ =>
      simp only [h1, Option.bind_some, Impl.runFrom_singleton] at h
      have hI := ih h1
      cases ℓ with
      | inv p o => exact inv_inv hI h1 h
      | tau p => exact inv_tau hI h
      | ret p r => exact inv_ret hI h1 h

/-- Every execution of the "max + 1" algorithm satisfies the timestamp specification. -/
theorem maxTS_correct : ∀ α, (alg n).Valid α → TSCorrect α := by
  rintro α ⟨C, h⟩
  have hI := inv_run h
  constructor
  · intro g r h1 h2; exact hI.resp g _ r h1 h2
  · intro g₁ g₂ c t₁ t₂ o r h1 h2 h3 h4 h5 _ h7 h8
    have hlt := hI.order g₁ g₂ t₁ t₂ h1 h2 h3 h4 h5
    have hr := hI.resp c o r h7 h8
    refine ⟨?_, ?_⟩
    · rintro rfl; simp only [RespOK] at hr; simp [hr, hlt]
    · rintro rfl; simp only [RespOK] at hr
      simp only [hr, Sum.inr.injEq, decide_eq_false_iff_not, not_lt]; omega

/-- **Non-vacuity of Theorem 1.1.** The "max + 1" algorithm is a wait-free long-lived
timestamp implementation for `n` processes from `n` registers. -/
theorem maxTS_isTS : IsTS (alg n) false where
  allowed _ _ := trivial
  correct α hv _ := maxTS_correct α hv
  progress _ C p hα _ hp := Impl.WaitFree.obstructionFree _ maxTS_waitFree C p ⟨_, hα⟩ hp

/-- Theorem 1.1 applied to the "max + 1" algorithm (a sanity check: `⌊n/2⌋ ≤ 3n`). -/
example : Fintype.card (Fin n) / 2 ≤ 3 * Fintype.card (Fin n) :=
  theorem_1_1 (I := alg n) maxTS_rwLike maxTS_isTS

end Cslib.SharedMemory.Timestamp.MaxTS
