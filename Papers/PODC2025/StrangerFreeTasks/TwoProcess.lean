import Papers.PODC2025.StrangerFreeTasks.LowerBound
import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# The bound of Theorem 2.1 is tight for `n = 2`

Theorem 2.1 of the paper: every wait-free read/write algorithm for a stranger-free task for `n`
processes uses at least `n` registers. By §3.2, `1`-bounded lattice agreement for two processes
is stranger-free (`boundedLA_strangerFree`). Here we show that the bound is attained for `n = 2`:
the following algorithm solves `1`-bounded lattice agreement for processes `Fin 2` wait-free
with two binary registers `R[0], R[1]` (initially `false`); `p + 1` is the other process.

```
R[p] ← true
if R[p + 1] then output {p, p + 1} else output {p}
```

Correctness: if `p` reads `false` then `p + 1` has not written yet, so when `p + 1` later reads
`R[p]` it sees `true`; hence the two processes never both output singletons, and every two
outputs of size `≤ 1` coincide.

## Main results

* `twoAlg_solves`, `twoAlg_waitFree`;
* `theorem_2_1_tight`: the task is stranger-free and solved wait-free with exactly two registers.
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory Impl

/-- Program counters of the two-process algorithm. -/
inductive TPh where
  /-- Not invoked yet. -/
  | idle
  /-- About to write `R[p] ← true`. -/
  | wr
  /-- About to read `R[p + 1]`. -/
  | rd
  /-- Output `o` decided. -/
  | done (o : Finset (Fin 2))
  deriving DecidableEq

/-- Whether a process in this phase has already written `true` into its register. -/
def TPh.written : TPh → Bool
  | .idle => false
  | .wr => false
  | .rd => true
  | .done _ => true

/-- The two-process, two-register algorithm for `1`-bounded lattice agreement. -/
noncomputable def twoAlg : Impl (laObj (Fin 2)) (RegFamily (Fin 2) Bool false) (Fin 2) TPh where
  memInit _ := false
  locInit _ := .idle
  invoke _ l _ := match l with
    | .idle => .wr
    | l => l
  act p l := match l with
    | .wr => .access p (.write true) (fun _ => .rd)
    | .rd => .access (p + 1) .read (fun b => .done (if b then {p, p + 1} else {p}))
    | .done o => .ret o (.done o)
    | .idle => .ret (∅ : Finset (Fin 2)) .idle

/-- Configurations of the algorithm. -/
abbrev TCfg := Config (laObj (Fin 2)) (RegFamily (Fin 2) Bool false) (Fin 2) TPh

/-! ### `Fin 2` facts -/

lemma fin2_add_one_add_one (p : Fin 2) : p + 1 + 1 = p := by revert p; decide

lemma fin2_cases (p q : Fin 2) : q = p ∨ q = p + 1 := by revert p q; decide

lemma fin2_pair_ne (p : Fin 2) : ({p, p + 1} : Finset (Fin 2)) ≠ {p} := by revert p; decide

lemma forall_fin2 (p : Fin 2) {F : Fin 2 → Prop} : (∀ q, F q) ↔ F p ∧ F (p + 1) := by
  refine ⟨fun h => ⟨h p, h (p + 1)⟩, fun h q => ?_⟩
  rcases fin2_cases p q with rfl | rfl
  exacts [h.1, h.2]

lemma fin2_pair_card (p : Fin 2) : ({p, p + 1} : Finset (Fin 2)).card = 2 := by revert p; decide

/-! ### Step lemmas -/

lemma twoAlg_step_inv {C C' : TCfg} {p : Fin 2} {o : Unit}
    (h : twoAlg.step C (.inv p o) = some C') :
    C'.pend = Function.update C.pend p (some o) ∧
      C'.loc = Function.update C.loc p (if C.loc p = .idle then .wr else C.loc p) ∧
      C'.mem = C.mem := by
  obtain ⟨-, -, h2, h3, h4⟩ := Impl.step_inv h
  refine ⟨h2, ?_, h4⟩
  rw [h3]; congr 1
  cases C.loc p <;> rfl

lemma twoAlg_step_tau {C C' : TCfg} {p : Fin 2} (h : twoAlg.step C (.tau p) = some C') :
    C'.pend = C.pend ∧
      ((C.loc p = .wr ∧ C'.mem = Function.update C.mem p true ∧
          C'.loc = Function.update C.loc p .rd) ∨
       (C.loc p = .rd ∧ C'.mem = C.mem ∧
          C'.loc = Function.update C.loc p
            (.done (if C.mem (p + 1) then {p, p + 1} else {p})))) := by
  obtain ⟨-, h2, i, o, k, h4, h5, h6⟩ := Impl.step_tau h
  refine ⟨h2, ?_⟩
  simp only [twoAlg] at h4
  cases hl : C.loc p <;> simp only [hl] at h4
  all_goals cases h4
  · exact Or.inl ⟨rfl, h5, h6⟩
  · exact Or.inr ⟨rfl, by rw [h5]; exact Function.update_eq_self _ _, h6⟩

lemma twoAlg_step_ret {C C' : TCfg} {p : Fin 2} {r : Finset (Fin 2)}
    (h : twoAlg.step C (.ret p r) = some C') :
    C.pend p ≠ none ∧ C'.pend = Function.update C.pend p none ∧ C'.mem = C.mem ∧
      C'.loc = C.loc ∧ (C.loc p = .done r ∨ C.loc p = .idle) := by
  obtain ⟨h1, h2, h3, l, h4, h5⟩ := Impl.step_ret h
  refine ⟨h1, h2, h3, ?_⟩
  simp only [twoAlg] at h4
  cases hl : C.loc p <;> simp only [hl] at h4
  all_goals cases h4
  · exact ⟨by rw [h5, ← hl]; exact Function.update_eq_self _ _, Or.inr rfl⟩
  · exact ⟨by rw [h5, ← hl]; exact Function.update_eq_self _ _, Or.inl rfl⟩

/-! ### The invariant -/

/-- The safety invariant of the two-process algorithm. -/
structure TInv (α : List (Label (Fin 2) (laObj (Fin 2)))) (C : TCfg) : Prop where
  mem_eq : ∀ q, C.mem q = (C.loc q).written
  out : ∀ q o, C.loc q = .done o → o = {q} ∨ (o = {q, q + 1} ∧ C.loc (q + 1) ≠ .idle)
  invoked : ∀ q, C.loc q ≠ .idle → opsOf α q ≠ []
  pend : ∀ q, C.pend q ≠ none → C.loc q ≠ .idle
  resp : ∀ q, ∀ o ∈ respsOf α q, C.loc q = .done o
  key : ∀ q, C.loc q = .done {q} → C.loc (q + 1) ≠ .done {q + 1}

lemma tInv_init : TInv [] twoAlg.initCfg where
  mem_eq q := rfl
  out q o h := by simp [Impl.initCfg, twoAlg] at h
  invoked q h := absurd rfl h
  pend q h := absurd rfl h
  resp q o ho := by simp at ho
  key q h := by simp [Impl.initCfg, twoAlg] at h

lemma TInv.step {α : List (Label (Fin 2) (laObj (Fin 2)))} {C C' : TCfg}
    {ℓ : Label (Fin 2) (laObj (Fin 2))} (hI : TInv α C) (h : twoAlg.step C ℓ = some C') :
    TInv (α ++ [ℓ]) C' := by
  obtain ⟨m, out, inv, pend, resp, key⟩ := hI
  cases ℓ with
  | inv p o =>
    obtain ⟨hpend, hloc, hmem⟩ := twoAlg_step_inv h
    have e1 : C'.loc p = if C.loc p = .idle then .wr else C.loc p := by rw [hloc]; simp
    have e2 : C'.loc (p + 1) = C.loc (p + 1) := by rw [hloc]; simp
    have f1 : C'.pend p = some o := by rw [hpend]; simp
    have f2 : C'.pend (p + 1) = C.pend (p + 1) := by rw [hpend]; simp
    simp only [forall_fin2 p, fin2_add_one_add_one] at m out inv pend resp key
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [forall_fin2 p, fin2_add_one_add_one] <;>
      simp only [hmem, e1, e2, f1, f2, opsOf_append, respsOf_append]
    all_goals (clear h hpend hloc e1 e2 f1 f2 hmem; generalize C.loc p = a at *
               cases a <;> simp_all [TPh.written] <;> first | exact resp.2 | exact resp)
  | tau p =>
    obtain ⟨hpend, hcase⟩ := twoAlg_step_tau h
    simp only [forall_fin2 p, fin2_add_one_add_one] at m out inv pend resp key
    rcases hcase with ⟨hc, hmem, hloc⟩ | ⟨hc, hmem, hloc⟩
    · have e1 : C'.loc p = .rd := by rw [hloc]; simp
      have e2 : C'.loc (p + 1) = C.loc (p + 1) := by rw [hloc]; simp
      have g1 : C'.mem p = true := by rw [hmem]; simp
      have g2 : C'.mem (p + 1) = C.mem (p + 1) := by rw [hmem]; simp
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [forall_fin2 p, fin2_add_one_add_one] <;>
        simp only [hpend, e1, e2, g1, g2, opsOf_append, respsOf_append]
      all_goals (clear h hpend hloc e1 e2 g1 g2 hmem; generalize C.loc p = a at *; subst hc
                 generalize C.loc (p + 1) = b at *
                 cases b <;> simp_all [TPh.written] <;> exact resp.2)
    · have e1 : C'.loc p = .done (if C.mem (p + 1) then {p, p + 1} else {p}) := by
        rw [hloc]; simp
      have e2 : C'.loc (p + 1) = C.loc (p + 1) := by rw [hloc]; simp
      rw [m.2] at e1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [forall_fin2 p, fin2_add_one_add_one] <;>
        simp only [hpend, e1, e2, hmem, opsOf_append, respsOf_append]
      all_goals (clear h hpend hloc e2 hmem; generalize C.loc p = a at *; subst hc
                 generalize C.loc (p + 1) = b at *
                 cases b <;> simp_all [TPh.written, fin2_pair_ne] <;>
                   exact resp.2)
  | ret p r =>
    obtain ⟨hp, hpend, hmem, hloc, hcase⟩ := twoAlg_step_ret h
    simp only [forall_fin2 p, fin2_add_one_add_one] at m out inv pend resp key
    have hc : C.loc p = .done r := hcase.resolve_right (pend.1 hp)
    have f1 : C'.pend p = none := by rw [hpend]; simp
    have f2 : C'.pend (p + 1) = C.pend (p + 1) := by rw [hpend]; simp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [forall_fin2 p, fin2_add_one_add_one] <;>
      simp only [hloc, hmem, f1, f2, opsOf_append, respsOf_append]
    all_goals (clear h hpend hloc hmem f1 f2; generalize C.loc p = a at *; subst hc
               simp_all <;>
                 first
                 | exact resp.2
                 | exact resp
                 | exact ⟨fun o ho => ho.elim (resp.1 o) (fun h => h ▸ rfl), resp.2⟩)

lemma tInv_of_run {α : List (Label (Fin 2) (laObj (Fin 2)))} {C : TCfg}
    (h : twoAlg.run α = some C) : TInv α C :=
  Impl.run_induction (I := twoAlg) (Q := TInv) tInv_init (fun _ _ _ _ _ hI hs => hI.step hs) h

/-! ### Main results -/

/-- The two-process algorithm solves `1`-bounded lattice agreement. -/
theorem twoAlg_solves : twoAlg.Solves (boundedLA (Fin 2) 1) := by
  rintro α ⟨C, hC⟩ -
  have hI := tInv_of_run hC
  have hdone : ∀ p (o : Finset (Fin 2)), outputs α p = some o → C.loc p = .done o :=
    fun p o h => hI.resp p o (List.mem_of_mem_head? h)
  have hin : ∀ q, C.loc q ≠ .idle → inputs α q ≠ none := by
    intro q hq
    simp only [inputs, ne_eq, List.head?_eq_none_iff]
    exact hI.invoked q hq
  have hsing : ∀ p (o : Finset (Fin 2)), C.loc p = .done o → o.card ≤ 1 → o = {p} := by
    intro p o hp hc
    rcases hI.out p o hp with h | ⟨rfl, -⟩
    · exact h
    · rw [fin2_pair_card] at hc; omega
  intro p o ho
  have hp := hdone p o ho
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases hI.out p o hp with rfl | ⟨rfl, hne⟩
    · rw [Finset.mem_singleton] at hq; subst hq; exact hin _ (by simp [hp])
    · rw [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact hin _ (by simp [hp])
      · exact hin _ hne
  · rcases hI.out p o hp with rfl | ⟨rfl, -⟩ <;> simp
  · intro p' o' ho' hc hc'
    have hp' := hdone p' o' ho'
    obtain rfl := hsing p o hp hc
    obtain rfl := hsing p' o' hp' hc'
    rcases fin2_cases p p' with rfl | rfl
    · exact Or.inl le_rfl
    · exact absurd hp' (hI.key p hp)

/-- The two-process algorithm is wait-free. -/
theorem twoAlg_waitFree : twoAlg.WaitFree := by
  refine twoAlg.waitFree_of_potential
    (fun _ l => match l with | .wr => 2 | .rd => 1 | _ => 0) ?_
  intro p l i o k hact x
  cases l <;> simp only [twoAlg] at hact <;> cases hact <;> simp

/-- **The bound of Theorem 2.1 is attained for `n = 2`**: `1`-bounded lattice agreement for two
processes is stranger-free (§3.2) and is solved wait-free with exactly two registers, by an
algorithm in which every process may participate. -/
theorem theorem_2_1_tight :
    (boundedLA (Fin 2) 1).StrangerFree ∧ twoAlg.Solves (boundedLA (Fin 2) 1) ∧
      twoAlg.WaitFree ∧ (∀ p x, twoAlg.allowed p x) ∧ Fintype.card (Fin 2) = 2 :=
  ⟨boundedLA_strangerFree (by simp) .waitFree, twoAlg_solves, twoAlg_waitFree,
    fun _ _ => trivial, Fintype.card_fin 2⟩

end Cslib.SharedMemory.StrangerFree
