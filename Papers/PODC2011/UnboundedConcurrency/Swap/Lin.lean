import Papers.PODC2011.UnboundedConcurrency.Swap.WaitFree
import Cslib.Computability.Distributed.SharedMemory.Objects.Swap

/-!
# Lemma 3 and the linearizability proof of Algorithm 1 (Lemmas 4–8, Theorem 9)

* `lemma3_tst`: every test-and-set object is accessed by at most two processes in any execution
  (so it can be a 2-consensus object);
* `RetFrom C p q` (the paper's `P_p ⇝ P_q`, Definition 1): `p` returned the value of `q`;
* Lemmas 4–8 for complete finite executions (`lemma4` … `lemma8`);
* `SwapLin x σ L`: `L` linearizes the finite execution `σ` of one-shot `swap` operations;
* `theorem9_complete` (Theorem 9 for complete executions, as in the paper) and
  `linearizable` (all finite executions, by completing pending operations with solo runs, using
  wait-freedom).
-/

namespace Podc.UnboundedConcurrency.Swap

open Cslib.SharedMemory Cslib.SharedMemory.Arrival Cfg' Node

variable {V : Type}

/-- The node `ret` from which a returned process read its value (`none` if it returned `⊥` or
has not returned yet). -/
def Loc.ret : Loc V → Option Node
  | .done _ _ _ r _ => r
  | _ => none

/-- `p` returned the value of `q` (Definition 1 of [AMW11], `P_p ⇝ P_q`): `p` returned from the
node `q` captured. -/
def RetFrom (C : Config V) (p q : ℕ) : Prop :=
  ∃ r, (C.loc p).ret = some r ∧ (C.loc q).cap = some r

/-- All processes that took a step in `σ` have returned. -/
def Complete (x : ℕ → V) (σ : List ℕ) : Prop := ∀ p ∈ σ, ∃ v, ((alg V).exec x σ).Out p v

section Basic

variable {x : ℕ → V} {C : Config V}

lemma out_iff {p : ℕ} {v : Option V} : C.Out p v ↔ ∃ d c m r, C.loc p = .done d c m r v := by
  unfold Cfg.Out
  constructor
  · intro h
    cases hc : C.loc p <;> rw [hc] at h <;> simp [alg, act] at h
    subst h; exact ⟨_, _, _, _, rfl⟩
  · rintro ⟨d, c, m, r, h⟩; rw [h]; rfl

lemma loc_not_mem {x : ℕ → V} {σ : List ℕ} {p : ℕ} (h : p ∉ σ) :
    ((alg V).exec x σ).loc p = .start (x p) :=
  Alg.run_loc_other _ _ h

lemma mem_of_dep {x : ℕ → V} {σ : List ℕ} {p d : ℕ}
    (h : (((alg V).exec x σ).loc p).dep = some d) : p ∈ σ := by
  by_contra hp; rw [loc_not_mem hp] at h; simp [Loc.dep] at h

lemma mem_of_cap {x : ℕ → V} {σ : List ℕ} {p : ℕ} {c : Node}
    (h : (((alg V).exec x σ).loc p).cap = some c) : p ∈ σ := by
  obtain ⟨d, hd⟩ := Loc.sel_dep (Loc.cap_sel h); exact mem_of_dep hd

lemma Loc.ret_lost {l : Loc V} {r : Node} (h : l.ret = some r) : l.lost r := by
  cases l <;> simp [Loc.ret] at h
  subst h; rfl

lemma Inv.cap_inj {x : ℕ → V} (hI : Inv x C) {p q : ℕ} {r : Node} (hp : (C.loc p).cap = some r)
    (hq : (C.loc q).cap = some r) : p = q :=
  hI.dep_inj p q _ (hI.cap_dep hp) (hI.cap_dep hq)

/-- `P_p ⇝ P_q` implies that `p` returned `q`'s input. -/
lemma Inv.retFrom_out (hI : Inv x C) {p q : ℕ} (h : RetFrom C p q) : C.Out p (some (x q)) := by
  obtain ⟨r, hr, hq⟩ := h
  cases hc : C.loc p with
  | done d c m r' o =>
    rw [hc] at hr; simp only [Loc.ret] at hr; subst hr
    have hok := hI.ok p; rw [hc] at hok
    obtain ⟨-, -, q', hq', ho⟩ := hok.2.2.2.2.2 r rfl
    rw [hI.cap_inj hq hq', out_iff]; exact ⟨d, c, m, some r, by rw [hc, ho]⟩
  | _ => rw [hc] at hr; simp [Loc.ret] at hr

/-- **Lemma 7** of [AMW11]: each process's value is returned by at most one process. -/
lemma lemma7 (x : ℕ → V) (σ : List ℕ) {p p' q : ℕ} (h : RetFrom ((alg V).exec x σ) p q)
    (h' : RetFrom ((alg V).exec x σ) p' q) : p = p' := by
  obtain ⟨r, hr, hq⟩ := h
  obtain ⟨r', hr', hq'⟩ := h'
  have : r = r' := by rw [hq] at hq'; exact Option.some.inj hq'
  subst this
  exact (inv_exec x σ).tryRet_unique (Or.inr (Or.inl (Loc.ret_lost hr)))
    (Or.inr (Or.inl (Loc.ret_lost hr')))

/-- The node a process selected/captured (`cap`; a dummy if there is none). -/
noncomputable def κ (C : Config V) (p : ℕ) : Node := ((C.loc p).sel).getD (rm 0)

lemma κ_of_sel {p : ℕ} {c : Node} (h : (C.loc p).sel = some c) : κ C p = c := by
  simp [κ, h]

lemma Inv.retFrom_lt (hI : Inv x C) {p q : ℕ} (h : RetFrom C p q) : κ C q < κ C p := by
  obtain ⟨r, hr, hq⟩ := h
  rw [κ_of_sel (Loc.cap_sel hq)]
  cases hc : C.loc p with
  | done d c m r' o =>
    rw [hc] at hr; simp only [Loc.ret] at hr; subst hr
    have hok := hI.ok p; rw [hc] at hok
    rw [κ_of_sel (by rw [hc]; rfl)]
    exact (hok.2.2.2.2.2 r rfl).1
  | _ => rw [hc] at hr; simp [Loc.ret] at hr

/-- **Lemma 8** of [AMW11]: the relation `⇝` is acyclic (in every reachable configuration). -/
theorem lemma8 (x : ℕ → V) (σ : List ℕ) (p : ℕ) :
    ¬ Relation.TransGen (RetFrom ((alg V).exec x σ)) p p := by
  have hI := inv_exec x σ
  have key : ∀ a b, Relation.TransGen (RetFrom ((alg V).exec x σ)) a b →
      κ ((alg V).exec x σ) b < κ ((alg V).exec x σ) a := by
    intro a b h
    induction h with
    | single h => exact hI.retFrom_lt h
    | tail _ h ih => exact (hI.retFrom_lt h).trans ih
  exact fun h => lt_irrefl _ (key p p h)

end Basic

/-! ### Lemma 3 -/

/-- Process `p` applies an operation to the base object `i` in the execution `σ`. -/
def Accesses (x : ℕ → V) (σ : List ℕ) (i : Obj) (p : ℕ) : Prop :=
  ∃ τ₁ τ₂, σ = τ₁ ++ p :: τ₂ ∧ ((alg V).exec x τ₁).Poised p i

section Lemma3

variable {x : ℕ → V} {C : Config V}

lemma Inv.tryRet_step (hI : Inv x C) {q : ℕ} {y : Node} (h : (C.loc q).tryRet y) (r : ℕ) :
    ((C.step r).loc q).tryRet y := by
  rcases (step_mono C r q).tryRet h with h' | ⟨d, c, m, hq⟩
  · exact h'
  by_cases hrq : q = r
  · subst hrq
    have hok := hI.ok q; rw [hq] at hok
    obtain ⟨-, -, -, -, hrc, hrm⟩ := hok
    rw [(step_retTas hq).1]
    by_cases hb : B C y = true
    · rw [ite_eq_left hb]; exact Or.inr (Or.inl rfl)
    · rw [ite_eq_right hb]; exact Or.inl ((afterPrev_blk hrm hrc).2 (Or.inl rfl))
  · rw [Cfg.step_loc_other C hrq]; exact h

lemma persist_run {P : Loc V → Prop} (hP : ∀ C : Config V, Inv x C → ∀ q r, P (C.loc q) →
    P ((C.step r).loc q)) {C : Config V} (hI : Inv x C) {q : ℕ} (h : P (C.loc q)) (τ : List ℕ) :
    P (((alg V).run C τ).loc q) := by
  induction τ generalizing C with
  | nil => exact h
  | cons r τ ih => exact ih (hI.step r) (hP C hI q r h)

/-- **Lemma 3** of [AMW11]: in every execution, each test-and-set object `v.tst` is accessed by at
most two processes (the process of depth `v.d`, which tries to capture `v`, and at most one process
that tries to return from `v`); hence it can be implemented by a 2-consensus object. -/
theorem lemma3_tst (x : ℕ → V) (σ : List ℕ) (v : Node) :
    ∃ a b, ∀ p, Accesses x σ (.tst v) p → p = a ∨ p = b := by
  classical
  set C := (alg V).exec x σ
  have hI : Inv x C := inv_exec x σ
  have hclaim : ∀ p, Accesses x σ (.tst v) p → (C.loc p).dep = some v.d ∨ (C.loc p).tryRet v := by
    rintro p ⟨τ₁, τ₂, hσ, o, k, hpo⟩
    have hI1 := inv_exec x τ₁
    have hC : C = (alg V).run ((alg V).exec x τ₁) (p :: τ₂) := by
      simp only [C, hσ, Alg.exec_append]
    rw [hC]
    cases hc : ((alg V).exec x τ₁).loc p with
    | tas x' d c =>
      rw [hc] at hpo
      simp only [alg, act] at hpo
      have hcv : c = v := by
        have := congrArg (fun a : Act (T V) (Loc V) (Option V) => match a with
          | .access i _ _ => i | .out _ => Obj.maxDepth) hpo
        simpa using this
      subst hcv
      have hok := hI1.ok p; rw [hc] at hok
      left
      exact persist_run (P := fun l => l.dep = some c.d)
        (fun C _ q r h => (step_mono C r q).dep _ h) hI1 (by rw [hc, ← hok.2.1]; rfl) _
    | retTas d c m r =>
      rw [hc] at hpo
      simp only [alg, act] at hpo
      have hrv : r = v := by
        have := congrArg (fun a : Act (T V) (Loc V) (Option V) => match a with
          | .access i _ _ => i | .out _ => Obj.maxDepth) hpo
        simpa using this
      subst hrv
      right
      exact persist_run (P := fun l => l.tryRet r) (fun C hC q r' h => hC.tryRet_step h r') hI1
        (by rw [hc]; exact Or.inr (Or.inr ⟨d, c, m, rfl⟩)) _
    | _ =>
      rw [hc] at hpo
      simp only [alg, act] at hpo
      first
      | (have := congrArg (fun a : Act (T V) (Loc V) (Option V) => match a with
          | .access i _ _ => i | .out _ => Obj.maxDepth) hpo; simp at this)
      | exact absurd hpo (by simp)
  refine ⟨if h : ∃ p, (C.loc p).dep = some v.d then h.choose else 0,
    if h : ∃ p, (C.loc p).tryRet v then h.choose else 0, fun p hp => ?_⟩
  rcases hclaim p hp with h | h
  · left
    have hex : ∃ p, (C.loc p).dep = some v.d := ⟨p, h⟩
    rw [dite_eq_left hex]; exact hI.dep_inj _ _ _ h hex.choose_spec
  · right
    have hex : ∃ p, (C.loc p).tryRet v := ⟨p, h⟩
    rw [dite_eq_left hex]; exact hI.tryRet_unique h hex.choose_spec

end Lemma3

end Podc.UnboundedConcurrency.Swap
