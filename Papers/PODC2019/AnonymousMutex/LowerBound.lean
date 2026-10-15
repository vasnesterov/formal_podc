import Cslib.Computability.Distributed.SharedMemory.Anonymous
import Mathlib.GroupTheory.Perm.List
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Theorem 5: the space lower bound `m ∈ M(n)` for symmetric deadlock-free mutual exclusion

Aghazadeh, Imbs, Raynal, Taubenfeld, Woelfel, *Optimal Memory-Anonymous Symmetric Deadlock-Free
Mutual Exclusion*, PODC 2019 (arXiv:1810.03723), Section 6.2.

If `1 < ℓ ≤ n` and `g = gcd(ℓ, m) > 1`, pick `g` processes `p₀, …, p_{g-1}`, cut the ring of the
`m` registers into `g` arcs of length `d = m / g`, and let `pᵢ` see the registers rotated by
`i·d` (`π pᵢ = (finRotate m)^(i d)`). In the *lock-step* execution (each round: one step of every
`pᵢ`, in order) the configuration stays symmetric: `pᵢ`'s local state is the renaming of `p₀`'s
by `σⁱ` (`σ` the cyclic permutation of the identifiers of the `pᵢ`) and register `sh y` holds the
`σ`-renaming of the value of register `y` (`sh` = rotation by `d`). In a round all processes
access *different* physical registers, so the sequential round has the same effect as a
simultaneous one. Hence either all `g ≥ 2` processes enter the critical section in the same
round (mutual exclusion fails), or none ever does and the lock-step execution is a fair
execution in which no `lock()` completes (deadlock-freedom fails).

The argument covers arbitrary read-modify-write registers *and* atomic snapshots (all processes
of a round perform the same kind of access), so it also gives the necessary condition of
Taubenfeld (PODC 2017) for read/write registers and for the snapshot-based model of Algorithm 1.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex

/-- `M(n) = {m : ∀ ℓ, 1 < ℓ ≤ n → gcd(ℓ, m) = 1}`. -/
def M (n : ℕ) : Set ℕ := {m | ∀ ℓ, 1 < ℓ → ℓ ≤ n → Nat.Coprime ℓ m}

/-! ### Generic lemmas -/

section Generic

variable {O : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]

/-- Run the labels `lab 0, …, lab (n-1)`, given a step invariant. -/
lemma runFrom_range (I : Impl O B P L) (Q : ℕ → Config O B P L → Prop) (lab : ℕ → Label P O)
    (n : ℕ) (C : Config O B P L) (h0 : Q 0 C)
    (hstep : ∀ j < n, ∀ D, Q j D → ∃ D', I.step D (lab j) = some D' ∧ Q (j + 1) D') :
    ∃ D, I.runFrom C ((List.range n).map lab) = some D ∧ Q n D := by
  induction n with
  | zero => exact ⟨C, rfl, h0⟩
  | succ n ih =>
    obtain ⟨D, hD, hQ⟩ := ih (fun j hj => hstep j (by omega))
    obtain ⟨D', hD', hQ'⟩ := hstep n (by omega) D hQ
    refine ⟨D', ?_, hQ'⟩
    rw [List.range_succ, List.map_append, I.runFrom_append_of_eq hD, List.map_singleton,
      I.runFrom_singleton, hD']

end Generic

section Regions

variable {P : Type} [DecidableEq P]

lemma regionOf_append_map_range (g : ℕ) (e : ℕ → P)
    (he : ∀ i j, i < g → j < g → e i = e j → i = j)
    (α : List (Label P mutexObj)) (lab : ℕ → Label P mutexObj) (hlab : ∀ j, (lab j).proc = e j)
    (j : ℕ) (hj : j ≤ g) :
    (∀ i < g, regionOf (α ++ (List.range j).map lab) (e i) =
      if i < j then (regionOf α (e i)).bind (fun r => r.next (lab i)) else regionOf α (e i)) ∧
    (∀ p, (∀ i < g, e i ≠ p) → regionOf (α ++ (List.range j).map lab) p = regionOf α p) := by
  induction j with
  | zero => simp
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [List.range_succ, List.map_append, List.map_singleton, ← List.append_assoc]
    refine ⟨fun i hi => ?_, fun p hp => ?_⟩
    · rw [regionOf_append_singleton, ih1 i hi, hlab]
      by_cases hij : i = j
      · subst hij; simp
      · have hne : e j ≠ e i := fun h => hij (he i j hi (by omega) h.symm)
        simp only [hne, ite_false]
        by_cases hi' : i < j
        · simp [hi', show i < j + 1 by omega]
        · simp [hi', show ¬ i < j + 1 by omega]
    · rw [regionOf_append_singleton, ih2 p hp, hlab]
      simp [hp j (by omega)]

end Regions

/-! ### The symmetric lock-step execution -/

section LockStep

variable {Id V S : Type} {m : ℕ} [MulAction (Equiv.Perm Id) V] [MulAction (Equiv.Perm Id) S]
  {A : SymAlg mutexObj Id m V S} {P : Type} [DecidableEq P] {ids : P → Id}
  {π : P → Equiv.Perm (Fin m)}
  (g : ℕ) (e : ℕ → P) (σ : Equiv.Perm Id) (sh : Equiv.Perm (Fin m)) (a₀ : Id)

/-- The hypotheses on the rotation set-up. -/
structure Setup (ids : P → Id) (π : P → Equiv.Perm (Fin m)) : Prop where
  σpow : σ ^ g = 1
  shpow : sh ^ g = 1
  shinj : ∀ i j y, i < g → j < g → (sh ^ i) y = (sh ^ j) y → i = j
  einj : ∀ i j, i < g → j < g → e i = e j → i = j
  hπ : ∀ i < g, π (e i) = sh ^ i
  hid : ∀ i < g, ids (e i) = (σ ^ i) a₀

/-- A symmetric configuration with base local state `s` and pending operation `b`. -/
structure SymCfg (C : A.Cfg) (s : S) (b : Option MutexOp) : Prop where
  loc : ∀ i < g, C.loc (e i) = (σ ^ i) • s
  pend : ∀ i < g, C.pend (e i) = b
  other : ∀ p, (∀ i < g, e i ≠ p) → C.pend p = none
  mem : ∀ y, C.mem () (sh y) = σ • C.mem () y

variable {g e σ sh a₀}

lemma SymCfg.mem_pow {C : A.Cfg} {s : S} {b : Option MutexOp}
    (hC : SymCfg g e σ sh C s b) (i : ℕ) (y : Fin m) :
    C.mem () ((sh ^ i) y) = (σ ^ i) • C.mem () y := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, hC.mem, ih, pow_succ', mul_smul]

section Rounds

variable (hS : Setup g e σ sh a₀ ids π) (hA : A.Symmetric)
include hS hA

/-- A round of read-modify-write steps preserves symmetry. -/
lemma round_rmw {C : A.Cfg} {s : S} {o : MutexOp} (hC : SymCfg g e σ sh C s (some o))
    {x : Fin m} {f : V → V} {k : V → S} (hact : A.act s = .rmw x f k) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .tau (e j))) = some D ∧
      SymCfg g e σ sh D (k (C.mem () x)) (some o) := by
  set v := C.mem () x
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e i) = (σ ^ i) • (if i < j then k v else s)) ∧
    (∀ p, D.pend p = C.pend p) ∧
    (∀ i < g, D.mem () ((sh ^ i) x) = (σ ^ i) • (if i < j then f v else v)) ∧
    (∀ y, (∀ i < g, (sh ^ i) x ≠ y) → D.mem () y = C.mem () y)
  obtain ⟨D, hD, hQ1, hQ2, hQ3, hQ4⟩ := runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc i hi], fun _ => rfl,
      fun i hi => by simp [hC.mem_pow, v], fun _ _ => rfl⟩
    (by
      rintro j hj D ⟨h1, h2, h3, h4⟩
      have hpend : D.pend (e j) ≠ none := by rw [h2, hC.pend j hj]; simp
      have hloc : D.loc (e j) = (σ ^ j) • s := by simp [h1 j hj]
      have hact' : A.act (D.loc (e j)) = .rmw x (fun w => (σ ^ j) • f ((σ ^ j)⁻¹ • w))
          (fun w => (σ ^ j) • k ((σ ^ j)⁻¹ • w)) := by
        rw [hloc, hA.act, hact]; rfl
      have hval : D.mem () ((sh ^ j) x) = (σ ^ j) • v := by simp [h3 j hj]
      refine ⟨_, SymAlg.impl_step_tau_rmw ids π hpend hact', ?_⟩
      simp only [hS.hπ j hj, hval, inv_smul_smul]
      refine ⟨fun i hi => ?_, fun p => h2 p, fun i hi => ?_, fun y hy => ?_⟩
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e i ≠ e j := fun h => hij (hS.einj i j hi hj h)
          dsimp only; rw [Function.update_of_ne hne, h1 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : (sh ^ i) x ≠ (sh ^ j) x := fun h => hij (hS.shinj i j x hi hj h)
          simp only [Function.update_self]
          rw [Function.update_of_ne hne, h3 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · simp only [Function.update_self]
        rw [Function.update_of_ne (Ne.symm (hy j hj)), h4 y hy])
  refine ⟨D, hD, fun i hi => by simp [hQ1 i hi, hi], fun i hi => by rw [hQ2, hC.pend i hi],
    fun p hp => by rw [hQ2, hC.other p hp], fun y => ?_⟩
  by_cases hy : ∃ i < g, (sh ^ i) x = y
  · obtain ⟨i, hi, rfl⟩ := hy
    rw [hQ3 i hi, if_pos hi]
    by_cases hi1 : i + 1 < g
    · have := hQ3 (i + 1) hi1
      rw [if_pos hi1, pow_succ', Equiv.Perm.mul_apply] at this
      rw [this, pow_succ', mul_smul]
    · have hig : i + 1 = g := by omega
      have : sh ((sh ^ i) x) = x := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', hig, hS.shpow]; rfl
      rw [this]
      have h0 := hQ3 0 (by omega)
      simp only [pow_zero, Equiv.Perm.one_apply, one_smul, if_pos (by omega : 0 < g)] at h0
      rw [h0, smul_smul, ← pow_succ', hig, hS.σpow, one_smul]
  · push Not at hy
    have hy' : ∀ i < g, (sh ^ i) x ≠ sh y := by
      intro i hi h
      rcases i with _ | i
      · apply hy (g - 1) (by omega)
        have : (sh ^ (g - 1)) (sh y) = (sh ^ g) y := by
          rw [← Equiv.Perm.mul_apply, ← pow_succ, show g - 1 + 1 = g by omega]
        rw [hS.shpow] at this
        simp only [pow_zero, Equiv.Perm.one_apply] at h
        rw [h, this]; rfl
      · apply hy i (by omega)
        rw [pow_succ', Equiv.Perm.mul_apply] at h
        exact sh.injective h
    rw [hQ4 _ hy', hQ4 _ hy, hC.mem]

/-- A round of snapshots preserves symmetry. -/
lemma round_snap {C : A.Cfg} {s : S} {o : MutexOp} (hC : SymCfg g e σ sh C s (some o))
    {k : (Fin m → V) → S} (hact : A.act s = .snap k) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .tau (e j))) = some D ∧
      SymCfg g e σ sh D (k (C.mem ())) (some o) := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e i) = (σ ^ i) • (if i < j then k (C.mem ()) else s)) ∧
    (∀ p, D.pend p = C.pend p) ∧ D.mem () = C.mem ()
  obtain ⟨D, hD, hQ1, hQ2, hQ3⟩ := runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc i hi], fun _ => rfl, rfl⟩
    (by
      rintro j hj D ⟨h1, h2, h3⟩
      have hpend : D.pend (e j) ≠ none := by rw [h2, hC.pend j hj]; simp
      have hloc : D.loc (e j) = (σ ^ j) • s := by simp [h1 j hj]
      have hact' : A.act (D.loc (e j)) = .snap (fun w => (σ ^ j) • k ((σ ^ j)⁻¹ • w)) := by
        rw [hloc, hA.act, hact]; rfl
      have hview : (fun y => D.mem () ((sh ^ j) y)) = (σ ^ j) • C.mem () := by
        funext y; rw [h3, hC.mem_pow]; rfl
      refine ⟨_, SymAlg.impl_step_tau_snap ids π hpend hact', ?_⟩
      simp only [hS.hπ j hj, hview, inv_smul_smul]
      refine ⟨fun i hi => ?_, fun p => h2 p, ?_⟩
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e i ≠ e j := fun h => hij (hS.einj i j hi hj h)
          dsimp only; rw [Function.update_of_ne hne, h1 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · simp [h3])
  exact ⟨D, hD, fun i hi => by simp [hQ1 i hi, hi], fun i hi => by rw [hQ2, hC.pend i hi],
    fun p hp => by rw [hQ2, hC.other p hp], fun y => by rw [hQ3, hC.mem]⟩

/-- In a symmetric configuration where the base process returns, all `g` processes return in the
next round. -/
lemma round_ret {C : A.Cfg} {s : S} {o : MutexOp} (hC : SymCfg g e σ sh C s (some o))
    {s' : S} (hact : A.act s = .ret () s') :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .ret (e j) ())) = some D := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    ∀ i < g, j ≤ i → D.loc (e i) = (σ ^ i) • s ∧ D.pend (e i) = some o
  obtain ⟨D, hD, -⟩ := runFrom_range (A.impl ids π) Q _ g C
    (fun i hi _ => ⟨hC.loc i hi, hC.pend i hi⟩)
    (by
      rintro j hj D h1
      obtain ⟨hloc, hpend⟩ := h1 j hj le_rfl
      have hact' : A.act (D.loc (e j)) = .ret () ((σ ^ j) • s') := by
        rw [hloc, hA.act, hact]; rfl
      refine ⟨_, SymAlg.impl_step_ret ids π (by simp [hpend]) hact', fun i hi hji => ?_⟩
      have hne : e i ≠ e j := fun h => by have := hS.einj i j hi hj h; omega
      dsimp only
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
      exact h1 i hi (by omega))
  exact ⟨D, hD⟩

/-- The invocation round: all `g` processes invoke `lock` from the initial configuration. -/
lemma round_inv :
    ∃ D, (A.impl ids π).runFrom (A.impl ids π).initCfg
      ((List.range g).map (fun j => .inv (e j) .lock)) = some D ∧
      SymCfg g e σ sh D (A.invoke (A.init a₀) .lock) (some .lock) := by
  let C₀ := (A.impl ids π).initCfg
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e i) = (σ ^ i) • (if i < j then A.invoke (A.init a₀) .lock else A.init a₀)) ∧
    (∀ i < g, D.pend (e i) = if i < j then some .lock else none) ∧
    (∀ p, (∀ i < g, e i ≠ p) → D.pend p = none) ∧ D.mem () = fun _ => A.bot
  have hloc0 : ∀ i < g, C₀.loc (e i) = (σ ^ i) • A.init a₀ := by
    intro i hi
    show A.init (ids (e i)) = _
    rw [hS.hid i hi, hA.init]
  obtain ⟨D, hD, hQ1, hQ2, hQ3, hQ4⟩ := runFrom_range (A.impl ids π) Q
    (fun j => Label.inv (e j) MutexOp.lock) g C₀
    ⟨fun i hi => by simp [hloc0 i hi], fun i hi => rfl, fun _ _ => rfl, rfl⟩
    (by
      rintro j hj D ⟨h1, h2, h3, h4⟩
      have hpend : D.pend (e j) = none := by simp [h2 j hj]
      refine ⟨_, SymAlg.impl_step_inv (o := MutexOp.lock) ids π hpend, fun i hi => ?_, fun i hi => ?_,
        fun p hp => ?_, ?_⟩
      · by_cases hij : i = j
        · subst hij; simp [h1 i hi, hA.invoke]
        · have hne : e i ≠ e j := fun h => hij (hS.einj i j hi hj h)
          dsimp only; rw [Function.update_of_ne hne, h1 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e i ≠ e j := fun h => hij (hS.einj i j hi hj h)
          dsimp only; rw [Function.update_of_ne hne, h2 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · dsimp only; rw [Function.update_of_ne (Ne.symm (hp j hj)), h3 p hp]
      · exact h4)
  exact ⟨D, hD, fun i hi => by simp [hQ1 i hi, hi], fun i hi => by simp [hQ2 i hi, hi], hQ3,
    fun y => by simp [hQ4, hA.bot]⟩


end Rounds

/-! ### The lock-step execution violates mutual exclusion or deadlock-freedom -/

/-- The labels of the lock-step execution: first all `pᵢ` invoke `lock`, then rounds of steps. -/
def lsLabel (g : ℕ) (e : ℕ → P) (n : ℕ) : Label P mutexObj :=
  if n < g then .inv (e n) .lock else .tau (e ((n - g) % g))

omit [DecidableEq P] in
lemma lsLabel_proc (hg : 0 < g) (n : ℕ) : ∃ i < g, (lsLabel g e n).proc = e i := by
  unfold lsLabel
  split_ifs with h
  · exact ⟨n, h, rfl⟩
  · exact ⟨_, Nat.mod_lt _ hg, rfl⟩

lemma range_map_lsLabel_zero :
    (List.range g).map (lsLabel g e) = (List.range g).map (fun j => .inv (e j) .lock) :=
  List.map_congr_left (fun j hj => by simp [lsLabel, List.mem_range.1 hj])

lemma range_map_lsLabel_succ (k : ℕ) :
    (List.range (g * (k + 2))).map (lsLabel g e) =
      (List.range (g * (k + 1))).map (lsLabel g e) ++ (List.range g).map (fun j => .tau (e j)) := by
  rw [show g * (k + 2) = g * (k + 1) + g by ring, List.range_add, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left (fun j hj => ?_)
  have hj := List.mem_range.1 hj
  simp only [Function.comp, lsLabel, show ¬ g * (k + 1) + j < g by nlinarith, ↓reduceIte]
  congr 2
  rw [show g * (k + 1) + j - g = j + g * k by rw [mul_add, mul_one]; omega, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hj]

/-- Labels "first `g` invocations of `lock`, then steps of processes given by `f`". -/
def invTauLabel (g : ℕ) (e f : ℕ → P) (n : ℕ) : Label P mutexObj :=
  if n < g then .inv (e n) .lock else .tau (f n)

omit [DecidableEq P] in
lemma invTauLabel_proc {f : ℕ → P} (hf : ∀ n, ∃ i < g, f n = e i) (n : ℕ) :
    ∃ i < g, (invTauLabel g e f n).proc = e i := by
  unfold invTauLabel
  split_ifs with h
  · exact ⟨n, h, rfl⟩
  · exact hf n

lemma regionOf_invTau (he : ∀ i j, i < g → j < g → e i = e j → i = j) {f : ℕ → P}
    (hf : ∀ n, ∃ i < g, f n = e i) (N : ℕ) :
    (∀ i < g, regionOf ((List.range N).map (invTauLabel g e f)) (e i) =
      some (if i < N then .trying else .rem)) ∧
    (∀ p, (∀ i < g, e i ≠ p) → regionOf ((List.range N).map (invTauLabel g e f)) p = some .rem) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine ⟨fun i hi => ?_, fun p hp => ?_⟩
    · rw [regionOf_append_singleton, ih.1 i hi]
      unfold invTauLabel
      by_cases hN : N < g
      · simp only [hN, ite_true, Label.proc]
        by_cases hiN : i = N
        · subst hiN; simp [Region.next]
        · have hne : e N ≠ e i := fun h => hiN (he i N hi hN h.symm)
          simp only [hne, ite_false]
          by_cases hi' : i < N
          · simp [hi', show i < N + 1 by omega]
          · simp [hi', show ¬ i < N + 1 by omega]
      · simp only [hN, ite_false, Label.proc]
        have hi' : i < N := by omega
        split_ifs <;> simp_all [Region.next] <;> omega
    · rw [regionOf_append_singleton, ih.2 p hp]
      obtain ⟨i, hi, hpi⟩ := invTauLabel_proc (e := e) hf N
      simp [hpi, hp i hi]

lemma regionOf_lsLabel (he : ∀ i j, i < g → j < g → e i = e j → i = j) (hg : 0 < g) (N : ℕ) :
    (∀ i < g, regionOf ((List.range N).map (lsLabel g e)) (e i) =
      some (if i < N then .trying else .rem)) ∧
    (∀ p, (∀ i < g, e i ≠ p) → regionOf ((List.range N).map (lsLabel g e)) p = some .rem) :=
  regionOf_invTau he (f := fun n => e ((n - g) % g)) (fun _ => ⟨_, Nat.mod_lt _ hg, rfl⟩) N

/-- **The lock-step execution**: for the rotation set-up with `g ≥ 2` processes, the
implementation is not both mutually exclusive and deadlock-free. -/
theorem not_mutualExclusion_and_deadlockFree (hS : Setup g e σ sh a₀ ids π) (hA : A.Symmetric)
    (hg : 2 ≤ g) :
    ¬ ((A.impl ids π).MutualExclusion ∧ (A.impl ids π).DeadlockFree) := by
  rintro ⟨hME, hDF⟩
  have hg0 : 0 < g := by omega
  set E : ℕ → List (Label P mutexObj) := fun k => (List.range (g * (k + 1))).map (lsLabel g e)
    with hE
  -- the base process never returns
  have key : ∀ k C s, (A.impl ids π).run (E k) = some C → SymCfg g e σ sh C s (some .lock) →
      ∀ r s', A.act s ≠ .ret r s' := by
    intro k C s hrun hC r s' hact
    obtain ⟨D, hD⟩ := round_ret hS hA hC hact
    have hval : (A.impl ids π).Valid
        (E k ++ (List.range g).map (fun j => .ret (e j) ())) :=
      ⟨D, by rw [Impl.run_append_of_eq _ hrun]; exact hD⟩
    have hreg := regionOf_append_map_range g e hS.einj (E k) (fun j => .ret (e j) ())
      (fun j => rfl) g le_rfl
    have hEk := regionOf_lsLabel (e := e) hS.einj hg0 (g * (k + 1))
    have hcs : ∀ i < g, InCS (E k ++ (List.range g).map (fun j => .ret (e j) ())) (e i) := by
      intro i hi
      unfold InCS
      rw [hreg.1 i hi, if_pos hi]
      simp only [hE]
      rw [hEk.1 i hi, if_pos (by nlinarith)]
      rfl
    have hwf : ClientWF (E k ++ (List.range g).map (fun j => .ret (e j) ())) := by
      intro p
      by_cases hp : ∃ i < g, e i = p
      · obtain ⟨i, hi, rfl⟩ := hp
        rw [hcs i hi]; simp
      · push Not at hp
        rw [hreg.2 p hp, hE, hEk.2 p hp]; simp
    have := hS.einj 0 1 hg0 (by omega) (hME _ hval hwf _ _ (hcs 0 hg0) (hcs 1 (by omega)))
    omega
  have all : ∀ k, ∃ C s, (A.impl ids π).run (E k) = some C ∧ SymCfg g e σ sh C s (some .lock) := by
    intro k
    induction k with
    | zero =>
      obtain ⟨D, hD, hsym⟩ := round_inv (a₀ := a₀) hS hA
      exact ⟨D, _, by simp only [hE, zero_add, mul_one, range_map_lsLabel_zero]; exact hD, hsym⟩
    | succ k ih =>
      obtain ⟨C, s, hC, hsym⟩ := ih
      have hEs : E (k + 1) = E k ++ (List.range g).map (fun j => .tau (e j)) :=
        range_map_lsLabel_succ k
      cases hact : A.act s with
      | rmw x f k' =>
        obtain ⟨D, hD, hsym'⟩ := round_rmw hS hA hsym hact
        exact ⟨D, _, by rw [hEs, Impl.run_append_of_eq _ hC]; exact hD, hsym'⟩
      | snap k' =>
        obtain ⟨D, hD, hsym'⟩ := round_snap hS hA hsym hact
        exact ⟨D, _, by rw [hEs, Impl.run_append_of_eq _ hC]; exact hD, hsym'⟩
      | ret r s' => exact absurd hact (key k C s hC hsym r s')
  -- the infinite lock-step execution
  obtain ⟨ex, hlbl, -⟩ := (A.impl ids π).exists_infExec_of_chain E
    (fun k => by rw [show E (k + 1) = E k ++ _ from range_map_lsLabel_succ k];
                 exact List.prefix_append _ _)
    (fun k => by simp only [hE, List.length_map, List.length_range]; nlinarith)
    (fun k => by obtain ⟨C, s, hC, -⟩ := all k; exact ⟨C, hC⟩)
  have hl : ∀ n, ex.lbl n = lsLabel g e n := fun n => by
    rw [hlbl n n (by simp only [hE, List.length_map, List.length_range]; nlinarith)]
    simp [hE]
  have hpre : ∀ t, ex.pre t = (List.range t).map (lsLabel g e) := fun t => by
    simp only [Impl.InfExec.pre]
    exact List.map_congr_left (fun n _ => hl n)
  have hreg := regionOf_lsLabel (e := e) hS.einj hg0
  have hwf : ∀ t, ClientWF (ex.pre t) := by
    intro t p
    rw [hpre]
    by_cases hp : ∃ i < g, e i = p
    · obtain ⟨i, hi, rfl⟩ := hp; rw [(hreg t).1 i hi]; simp
    · push Not at hp; rw [(hreg t).2 p hp]; simp
  have hother : ∀ p, (∀ i < g, e i ≠ p) → ∀ t, (ex.cfg t).pend p = none := by
    intro p hp t
    induction t with
    | zero => rw [ex.cfg_zero]; rfl
    | succ t ih =>
      obtain ⟨i, hi, hpi⟩ := lsLabel_proc (e := e) hg0 t
      rw [(Impl.step_other (ex.step_eq t) (by rw [hl, hpi]; exact hp i hi)).2, ih]
  have hfair : ex.Fair := by
    intro p t hp
    by_cases hpe : ∃ i < g, e i = p
    · obtain ⟨i, hi, rfl⟩ := hpe
      refine ⟨g + g * t + i, by nlinarith, ?_⟩
      rw [hl]
      simp only [lsLabel, show ¬ g + g * t + i < g by omega, ite_false,
        show g + g * t + i - g = i + g * t by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt hi]
      exact ⟨rfl, trivial⟩
    · push Not at hpe; exact absurd (hother p hpe t) hp
  obtain ⟨C₀, s₀, hC₀, hsym₀⟩ := all 0
  have hcfg : ex.cfg g = C₀ := by
    have h1 := ex.run_pre g
    rw [hpre] at h1
    have : E 0 = (List.range g).map (lsLabel g e) := by simp [hE]
    rw [this] at hC₀
    rw [hC₀] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨t', -, p, r, hret⟩ := hDF ex hwf hfair g ⟨e 0, by rw [hcfg, hsym₀.pend 0 hg0]; simp⟩
    (fun q hq => by
      unfold InCS at hq
      rw [hpre] at hq
      by_cases hp : ∃ i < g, e i = q
      · obtain ⟨i, hi, rfl⟩ := hp; rw [(hreg g).1 i hi] at hq; simp [hi] at hq
      · push Not at hp; rw [(hreg g).2 q hp] at hq; simp at hq)
  rw [hl] at hret
  unfold lsLabel at hret
  split_ifs at hret


end LockStep


/-! ### Theorem 5 -/

lemma finRotate_pow_val {m : ℕ} (k : ℕ) (x : Fin m) :
    (((finRotate m) ^ k) x : ℕ) = (x + k) % m := by
  rcases m with _ | m
  · exact x.elim0
  induction k with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
      ← Nat.add_mod, Nat.add_assoc]

variable {Id V S : Type} {m : ℕ} [MulAction (Equiv.Perm Id) V] [MulAction (Equiv.Perm Id) S]
  {A : SymAlg mutexObj Id m V S} {P : Type} [DecidableEq P] [Fintype P]

/-- **Theorem 5** of Aghazadeh et al. (PODC 2019): if a symmetric algorithm using `m` anonymous
registers (arbitrary read-modify-write registers, and even atomic snapshots) solves
deadlock-free mutual exclusion for `n` processes — for every assignment of (distinct)
identifiers and every adversarial choice of the anonymity permutations — then
`m ∈ M(n) = {m : ∀ ℓ, 1 < ℓ ≤ n → gcd(ℓ, m) = 1}`.

(The theorem only needs *one* injective identifier assignment `ids`.) -/
theorem theorem_5 (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids)
    (h : ∀ π : P → Equiv.Perm (Fin m),
      (A.impl ids π).MutualExclusion ∧ (A.impl ids π).DeadlockFree) :
    m ∈ M (Fintype.card P) := by
  classical
  intro ℓ hℓ1 hℓn
  by_contra hcop
  set n := Fintype.card P with hn
  set g := Nat.gcd ℓ m with hgdef
  have hg2 : 2 ≤ g := by
    have h0 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have h1 : g ≠ 1 := hcop
    omega
  have hgn : g ≤ n := (Nat.gcd_le_left m (by omega)).trans hℓn
  have hgm : g ∣ m := Nat.gcd_dvd_right ℓ m
  set d := m / g with hd
  have hdg : d * g = m := Nat.div_mul_cancel hgm
  have hn0 : 0 < n := by omega
  let e : ℕ → P := fun i => (Fintype.equivFin P).symm ⟨i % n, Nat.mod_lt _ hn0⟩
  have einj : ∀ i j, i < g → j < g → e i = e j → i = j := by
    intro i j hi hj hij
    have := congrArg Fin.val ((Fintype.equivFin P).symm.injective hij)
    simp only [Nat.mod_eq_of_lt (show i < n by omega), Nat.mod_eq_of_lt (show j < n by omega)]
      at this
    exact this
  let l : List Id := (List.range g).map (fun i => ids (e i))
  have hlen : l.length = g := by simp [l]
  have hl : l.Nodup := List.Nodup.map_on (fun i hi j hj hij =>
    einj i j (List.mem_range.1 hi) (List.mem_range.1 hj) (hid hij)) List.nodup_range
  let σ : Equiv.Perm Id := l.formPerm
  let sh : Equiv.Perm (Fin m) := (finRotate m) ^ d
  let π : P → Equiv.Perm (Fin m) := fun p => sh ^ ((Fintype.equivFin P p : Fin n) : ℕ)
  have hS : Setup g e σ sh (ids (e 0)) ids π :=
    { σpow := by rw [← hlen]; exact List.formPerm_pow_length_eq_one_of_nodup l hl
      shpow := by
        ext x
        rw [← pow_mul, finRotate_pow_val, hdg, Equiv.Perm.one_apply, Nat.add_mod_right,
          Nat.mod_eq_of_lt x.isLt]
      shinj := by
        intro i j y hi hj hij
        have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) y.isLt
        have hd0 : 0 < d := by
          rcases Nat.eq_zero_or_pos d with h0 | h0
          · rw [h0, zero_mul] at hdg; omega
          · exact h0
        have := congrArg Fin.val hij
        rw [← pow_mul, ← pow_mul, finRotate_pow_val, finRotate_pow_val] at this
        have hmod : Nat.ModEq m (d * i) (d * j) := Nat.ModEq.add_left_cancel' (y : ℕ) this
        have := hmod.eq_of_lt_of_lt (by rw [← hdg]; exact Nat.mul_lt_mul_of_pos_left hi hd0)
          (by rw [← hdg]; exact Nat.mul_lt_mul_of_pos_left hj hd0)
        exact Nat.eq_of_mul_eq_mul_left hd0 this
      einj := einj
      hπ := by
        intro i hi
        simp only [π, e, Equiv.apply_symm_apply, Nat.mod_eq_of_lt (show i < n by omega)]
      hid := by
        intro i hi
        have := List.formPerm_pow_apply_getElem l hl i 0 (by omega)
        simp only [zero_add, hlen, Nat.mod_eq_of_lt hi] at this
        simp only [l, List.getElem_map, List.getElem_range] at this
        exact this.symm }
  exact not_mutualExclusion_and_deadlockFree hS hA hg2 (h π)

end AnonymousMutex
