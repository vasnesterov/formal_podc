import Papers.PODC2019.AnonymousMutex.Alg1
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases

/-!
# Algorithm 1 is **not** deadlock-free: a livelock for `n = 4`, `m = 5`

Theorem 2 of the paper claims that Algorithm 1 is deadlock-free for every `n` and every
`m > 1` with `m ∈ M(n)`. This is false: for `n = 4` processes and `m = 5 ∈ M(4)` registers
there is a fair infinite execution in which all four processes are in `lock()` forever, nobody is
in the critical section and no operation ever completes.

Processes `0,1,2,3` (identifiers = themselves); local → physical register maps
`π 0 = [0,4,1,2,3]`, `π 1 = [1,2,3,0,4]`, `π 2 = [2,0,1,3,4]`, `π 3 = [3,0,1,2,4]`.
From the configuration where all four are about to take a snapshot of the empty memory, the
following 28 steps lead back to the same situation (memory written as physical registers
`0..4`, `.` = `⊥`):

```
 p0,p1,p2,p3 snapshot the empty memory; they will write 0,1,2,3 resp.
 p0 writes 0; p0 snapshot, writes 4                         0 . . . 0
 p1 writes 1; p1 snapshot, writes 2; snapshot, writes 3      0 1 1 1 0   (full)
 p0 snapshot: owns 2 < 5/2 → shrink; reads 0 (own)
 p2 writes 2 (stale write, based on its first snapshot)      0 1 2 1 0
 p2 snapshot: owns 1 < 5/3 → shrink; reads 2 (own)
 p3 writes 3 (stale write)                                   0 1 2 3 0
 p1 snapshot: owns 1 < 5/4 → shrink;  p3 snapshot: owns 1 < 5/4 → shrink
 p0 erases 0; p2 erases 2; p0 reads 4, erases 4; p1 reads 1, erases 1; p3 reads 3, erases 3
                                                             . . . . .
```

The paper's proof (Claims 4–5) overlooks *stale* writes (a process writing into a register that
was `⊥` in an old snapshot): Claim 4 only shows that at every time *some* competing process does
not withdraw, which does not imply that one process never withdraws.

The Lean proof below checks the two finite pieces of the execution by kernel evaluation
(`decide +kernel`) and builds the infinite periodic execution with
`Impl.exists_infExec_of_chain`.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg1.Livelock

/-- A permutation of `Fin 5` given by its values and those of its inverse. -/
def mkPerm (f g : Fin 5 → Fin 5) (h1 : ∀ x, g (f x) = x := by decide)
    (h2 : ∀ x, f (g x) = x := by decide) : Equiv.Perm (Fin 5) := ⟨f, g, h1, h2⟩

/-- The anonymity permutations (local name ↦ physical register). -/
def π : Fin 4 → Equiv.Perm (Fin 5) :=
  ![mkPerm ![0, 4, 1, 2, 3] ![0, 2, 3, 4, 1],
    mkPerm ![1, 2, 3, 0, 4] ![3, 0, 1, 2, 4],
    mkPerm ![2, 0, 1, 3, 4] ![1, 2, 0, 3, 4],
    mkPerm ![3, 0, 1, 2, 4] ![1, 2, 3, 0, 4]]

/-- The implementation: four processes with identifiers `0,1,2,3`. -/
abbrev I := (alg1 (Fin 4) 5).impl id π

/-- The processes scheduled in one period. -/
def sched : List (Fin 4) :=
  [0, 1, 2, 3, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 2, 2, 2, 3, 1, 3, 0, 2, 0, 0, 1, 1, 3, 3]

/-- The labels of one period. -/
def cycle : List (Label (Fin 4) mutexObj) := sched.map .tau

/-- All four processes invoke `lock()`. -/
def invs : List (Label (Fin 4) mutexObj) := [.inv 0 .lock, .inv 1 .lock, .inv 2 .lock, .inv 3 .lock]

/-- A configuration as a triple with decidable equality. -/
def toTriple (C : SymAlg.Cfg (P := Fin 4) (alg1 (Fin 4) 5)) :
    (Fin 4 → St (Fin 4) 5) × (Fin 4 → Option MutexOp) × (Fin 5 → Option (Fin 4)) :=
  (C.loc, C.pend, C.mem ())

lemma toTriple_injective : Function.Injective toTriple := by
  intro C D h
  simp only [toTriple, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3⟩ := h
  cases C; cases D
  simp only at h1 h2 h3
  subst h1 h2
  congr
  funext u
  exact h3

/-- The configuration after the four invocations. -/
def Cinv : SymAlg.Cfg (P := Fin 4) (alg1 (Fin 4) 5) :=
  ⟨fun p => ⟨p, .snap, fun _ => none⟩, fun _ => some .lock, fun _ _ => none⟩

/-- The views (last snapshots, in local names) at the end of a period. -/
def views : Fin 4 → Fin 5 → Option (Fin 4) :=
  ![![some 0, some 0, some 1, some 1, some 1],
    ![some 1, some 2, some 3, some 0, some 0],
    ![some 2, some 0, some 1, some 1, some 0],
    ![some 3, some 0, some 1, some 2, some 0]]

/-- The configuration at the start of every period (after the first one): all processes are
about to take a snapshot, the memory is empty. -/
def C₁ : SymAlg.Cfg (P := Fin 4) (alg1 (Fin 4) 5) :=
  ⟨fun p => ⟨p, .snap, views p⟩, fun _ => some .lock, fun _ _ => none⟩

/-- Boolean test "`C = C₁`" (field by field). -/
def isC₁ (C : SymAlg.Cfg (P := Fin 4) (alg1 (Fin 4) 5)) : Bool :=
  decide (∀ p : Fin 4, (C.loc p).me = p) && decide (∀ p : Fin 4, (C.loc p).pc = .snap) &&
    decide (∀ p : Fin 4, (C.loc p).view = views p) && decide (∀ p : Fin 4, C.pend p = some .lock) &&
    decide (∀ y : Fin 5, C.mem () y = none)

lemma eq_of_isC₁ {C : SymAlg.Cfg (P := Fin 4) (alg1 (Fin 4) 5)} (h : isC₁ C = true) : C = C₁ := by
  simp only [isC₁, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  apply toTriple_injective
  simp only [toTriple, Prod.mk.injEq]
  refine ⟨funext fun p => ?_, funext h4, funext h5⟩
  have e1 := h1 p; have e2 := h2 p; have e3 := h3 p
  revert e1 e2 e3
  cases C.loc p
  intro e1 e2 e3
  simp only at e1 e2 e3
  subst e1 e2 e3
  rfl

lemma run_first : I.runFrom Cinv cycle = some C₁ := by
  have h : (I.runFrom Cinv cycle).map isC₁ = some true := by decide +kernel
  cases h' : I.runFrom Cinv cycle with
  | none => rw [h'] at h; cases h
  | some C => rw [h'] at h; simp only [Option.map_some, Option.some.injEq] at h; rw [eq_of_isC₁ h]

lemma run_period : I.runFrom C₁ cycle = some C₁ := by
  have h : (I.runFrom C₁ cycle).map isC₁ = some true := by decide +kernel
  cases h' : I.runFrom C₁ cycle with
  | none => rw [h'] at h; cases h
  | some C => rw [h'] at h; simp only [Option.map_some, Option.some.injEq] at h; rw [eq_of_isC₁ h]

lemma run_invs : I.run invs = some Cinv := by
  simp only [Impl.run, invs, Impl.runFrom_cons, Impl.runFrom_nil]
  rw [SymAlg.impl_step_inv _ _ (by rfl)]
  simp only [Option.bind_some]
  rw [SymAlg.impl_step_inv _ _ (by rfl)]
  simp only [Option.bind_some]
  rw [SymAlg.impl_step_inv _ _ (by rfl)]
  simp only [Option.bind_some]
  rw [SymAlg.impl_step_inv _ _ (by rfl)]
  simp only [Option.bind_some, Option.some.injEq]
  apply toTriple_injective
  simp only [toTriple, Prod.mk.injEq]
  refine ⟨funext fun p => ?_, funext fun p => ?_, funext fun y => rfl⟩ <;> fin_cases p <;> rfl

/-- Process number `i` (for `i < 4`). -/
def eP (i : ℕ) : Fin 4 := ⟨i % 4, Nat.mod_lt _ (by norm_num)⟩

/-- The labels of the infinite execution: four invocations, then the period forever. -/
def lbl : ℕ → Label (Fin 4) mutexObj :=
  invTauLabel 4 eP (fun n => sched.getD ((n - 4) % 28) 0)

/-- The prefixes: invocations followed by `k + 1` periods. -/
def E (k : ℕ) : List (Label (Fin 4) mutexObj) := (List.range (4 + 28 * (k + 1))).map lbl

lemma E_zero : E 0 = invs ++ cycle := by
  simp [E, List.range_succ, lbl, invTauLabel, invs, cycle, sched, eP]

lemma E_succ (k : ℕ) : E (k + 1) = E k ++ cycle := by
  rw [E, show 4 + 28 * (k + 1 + 1) = (4 + 28 * (k + 1)) + 28 by ring, List.range_add,
    List.map_append, List.map_map]
  congr 1
  have : ∀ j < 28, (lbl ∘ fun j => 4 + 28 * (k + 1) + j) j = .tau (sched.getD j 0) := by
    intro j hj
    simp only [Function.comp, lbl, invTauLabel, show ¬ 4 + 28 * (k + 1) + j < 4 by omega,
      ↓reduceIte, show 4 + 28 * (k + 1) + j - 4 = j + 28 * (k + 1) by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  rw [List.map_congr_left (fun j hj => this j (List.mem_range.1 hj))]
  rfl

lemma run_E (k : ℕ) : I.run (E k) = some C₁ := by
  induction k with
  | zero => rw [E_zero, Impl.run_append_of_eq _ run_invs, run_first]
  | succ k ih => rw [E_succ, Impl.run_append_of_eq _ ih, run_period]

lemma eP_val (p : Fin 4) : eP p = p := by ext; simp [eP, Nat.mod_eq_of_lt p.isLt]

lemma lbl_proc (n : ℕ) : ∃ i < 4, (fun n => sched.getD ((n - 4) % 28) 0) n = eP i :=
  ⟨_, Fin.isLt _, (eP_val _).symm⟩

lemma lbl_period (t : ℕ) (p : Fin 4) : lbl (4 + 28 * t + p) = .tau p := by
  have h : sched.getD (((p : ℕ) + 28 * t) % 28) 0 = p := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (show (p : ℕ) < 28 by omega)]
    fin_cases p <;> rfl
  simp only [lbl, invTauLabel, show ¬ 4 + 28 * t + (p : ℕ) < 4 by omega, ↓reduceIte,
    show 4 + 28 * t + (p : ℕ) - 4 = p + 28 * t by omega, h]

/-- **Algorithm 1 is not deadlock-free** for `n = 4` processes and `m = 5` registers (with the
anonymity permutations `π`). -/
theorem not_deadlockFree : ¬ I.DeadlockFree := by
  intro hDF
  obtain ⟨ex, hlbl, -⟩ := I.exists_infExec_of_chain E
    (fun k => by rw [E_succ]; exact List.prefix_append _ _)
    (fun k => by simp only [E, List.length_map, List.length_range]; omega)
    (fun k => ⟨_, run_E k⟩)
  have hl : ∀ n, ex.lbl n = lbl n := fun n => by
    rw [hlbl n n (by simp only [E, List.length_map, List.length_range]; omega)]
    simp [E]
  have hpre : ∀ t, ex.pre t = (List.range t).map lbl := fun t => by
    simp only [Impl.InfExec.pre]
    exact List.map_congr_left (fun n _ => hl n)
  have he : ∀ i j, i < 4 → j < 4 → eP i = eP j → i = j := by
    intro i j hi hj h
    have := congrArg Fin.val h
    simpa [eP, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using this
  have hreg : ∀ N, (∀ i < 4, regionOf ((List.range N).map lbl) (eP i) =
      some (if i < N then .trying else .rem)) ∧
      (∀ p, (∀ i < 4, eP i ≠ p) → regionOf ((List.range N).map lbl) p = some .rem) :=
    regionOf_invTau he lbl_proc
  have hall : ∀ p : Fin 4, ∃ i < 4, eP i = p := fun p => ⟨p, p.isLt, eP_val p⟩
  have hwf : ∀ t, ClientWF (ex.pre t) := by
    intro t p
    rw [hpre]
    obtain ⟨i, hi, rfl⟩ := hall p
    rw [(hreg t).1 i hi]; simp
  have hfair : ex.Fair := by
    intro p t _
    refine ⟨4 + 28 * t + p, by omega, ?_⟩
    rw [hl, lbl_period]
    exact ⟨rfl, trivial⟩
  have hcfg : ex.cfg 4 = Cinv := by
    have h1 := ex.run_pre 4
    rw [hpre, show (List.range 4).map lbl = invs by rfl, run_invs] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨t', -, p, r, hret⟩ := hDF ex hwf hfair 4 ⟨0, by rw [hcfg]; simp [Cinv]⟩
    (fun q hq => by
      unfold InCS at hq
      rw [hpre] at hq
      obtain ⟨i, hi, rfl⟩ := hall q
      rw [(hreg 4).1 i hi] at hq
      split_ifs at hq <;> simp at hq)
  rw [hl] at hret
  simp only [lbl, invTauLabel] at hret
  split_ifs at hret

lemma five_mem_M_four : 5 ∈ M 4 := by
  intro ℓ h1 h2
  interval_cases ℓ <;> decide

end AnonymousMutex.Alg1.Livelock

namespace AnonymousMutex

/-- **Theorem 2 of the paper is false.** Algorithm 1 is claimed deadlock-free for all `n` and all
`m > 1` with `m ∈ M(n)`; for `n = 4`, `m = 5` there are identifiers and anonymity permutations
for which it is not. -/
theorem theorem_2_false :
    ∃ (ids : Fin 4 → Fin 4) (π : Fin 4 → Equiv.Perm (Fin 5)),
      Function.Injective ids ∧ 1 < 5 ∧ 5 ∈ M (Fintype.card (Fin 4)) ∧
      ¬ ((Alg1.alg1 (Fin 4) 5).impl ids π).DeadlockFree :=
  ⟨id, Alg1.Livelock.π, Function.injective_id, by norm_num,
    by simpa using Alg1.Livelock.five_mem_M_four, Alg1.Livelock.not_deadlockFree⟩

end AnonymousMutex
