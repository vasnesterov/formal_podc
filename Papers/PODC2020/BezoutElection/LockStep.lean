import Papers.PODC2020.BezoutElection.Defs
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Symmetric lock-step rounds with several groups of processes

Generalizes the lock-step argument of `Papers/PODC2019/AnonymousMutex/LowerBound.lean` (one group
of `g` processes) to `k` groups of `g` processes each, for any one-shot object (here: the
election object `elecObj R`).

Set-up (`Setup`): processes `e q i` (`q < k` the group, `i < g` the position in the group) cover
all processes; process `e q i` sees the registers rotated by `sh ^ i` (`sh ^ g = 1`, the `g`
rotations `sh ^ i` of a register are pairwise distinct) and has identifier `σ ^ i (a q)` where
`σ ^ g = 1`.

A configuration is *symmetric* (`SymCfg C s b`) if for every group `q` the process `e q i` is in
local state `σ ^ i • s q` with pending operation `b q`, and the memory satisfies
`mem (sh y) = σ • mem y`. One step of each member of a group (in order) preserves symmetry
(`round_rmw`, `round_snap`, `round_ret`, `round_inv`): in such a group round the `g` processes
access `g` *different* registers (`sh ^ i x`), so the sequential round has the same effect as a
simultaneous one. Responses do not involve identifiers, so all members of a group return the
same response.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

/-- Run the labels `lab 0, …, lab (n-1)`, given a step invariant. -/
lemma runFrom_range {O : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type}
    [DecidableEq P] (I : Impl O B P L) (Q : ℕ → Config O B P L → Prop) (lab : ℕ → Label P O)
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

section LockStep

variable {R : Type} [Inhabited R] {Id V S : Type} {m : ℕ} [MulAction (Equiv.Perm Id) V]
  [MulAction (Equiv.Perm Id) S] {A : SymAlg (elecObj R) Id m V S} {P : Type} [DecidableEq P]
  {ids : P → Id} {π : P → Equiv.Perm (Fin m)}
  (k g : ℕ) (e : ℕ → ℕ → P) (σ : Equiv.Perm Id) (sh : Equiv.Perm (Fin m)) (a : ℕ → Id)

/-- The rotation set-up with `k` groups of `g` processes. -/
structure Setup (ids : P → Id) (π : P → Equiv.Perm (Fin m)) : Prop where
  σpow : σ ^ g = 1
  shpow : sh ^ g = 1
  shinj : ∀ i j y, i < g → j < g → (sh ^ i) y = (sh ^ j) y → i = j
  einj : ∀ q i q' j, q < k → i < g → q' < k → j < g → e q i = e q' j → q = q' ∧ i = j
  esurj : ∀ p, ∃ q < k, ∃ i < g, e q i = p
  hπ : ∀ q < k, ∀ i < g, π (e q i) = sh ^ i
  hid : ∀ q < k, ∀ i < g, ids (e q i) = (σ ^ i) (a q)

/-- A symmetric configuration: group `q` has base local state `s q` and pending operation
`b q`. -/
structure SymCfg (C : A.Cfg) (s : ℕ → S) (b : ℕ → Option Unit) : Prop where
  loc : ∀ q < k, ∀ i < g, C.loc (e q i) = (σ ^ i) • s q
  pend : ∀ q < k, ∀ i < g, C.pend (e q i) = b q
  mem : ∀ y, C.mem () (sh y) = σ • C.mem () y

variable {k g e σ sh a}

lemma SymCfg.mem_pow {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option Unit}
    (hC : SymCfg k g e σ sh C s b) (i : ℕ) (y : Fin m) :
    C.mem () ((sh ^ i) y) = (σ ^ i) • C.mem () y := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, hC.mem, ih, pow_succ', mul_smul]

section Rounds

variable (hS : Setup k g e σ sh a ids π) (hA : A.Symmetric)
include hS hA

lemma Setup.ne_of_group_ne {q q' i j : ℕ} (hq : q < k) (hq' : q' < k) (hi : i < g) (hj : j < g)
    (hne : q ≠ q') : e q i ≠ e q' j := fun h => hne (hS.einj q i q' j hq hi hq' hj h).1

/-- Memory after a round of `rmw x f` by the `g` members of a group, from the per-register
description. -/
lemma round_mem_aux {M M' : Fin m → V} (hM : ∀ y, M (sh y) = σ • M y) {x : Fin m} {w : V}
    (hg : 0 < g) (h3 : ∀ i < g, M' ((sh ^ i) x) = (σ ^ i) • w)
    (h4 : ∀ y, (∀ i < g, (sh ^ i) x ≠ y) → M' y = M y) : ∀ y, M' (sh y) = σ • M' y := by
  intro y
  by_cases hy : ∃ i < g, (sh ^ i) x = y
  · obtain ⟨i, hi, rfl⟩ := hy
    rw [h3 i hi]
    by_cases hi1 : i + 1 < g
    · have := h3 (i + 1) hi1
      rw [pow_succ', Equiv.Perm.mul_apply] at this
      rw [this, pow_succ', mul_smul]
    · have hig : i + 1 = g := by omega
      have : sh ((sh ^ i) x) = x := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ', hig, hS.shpow]; rfl
      rw [this]
      have h0 := h3 0 hg
      simp only [pow_zero, Equiv.Perm.one_apply, one_smul] at h0
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
    rw [h4 _ hy', h4 _ hy, hM]

/-- A round of read-modify-write steps of group `q` preserves symmetry. -/
lemma round_rmw {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option Unit} (hC : SymCfg k g e σ sh C s b)
    {q : ℕ} (hq : q < k) (hb : b q = some ()) (hg : 0 < g)
    {x : Fin m} {f : V → V} {κ : V → S} (hact : A.act (s q) = .rmw x f κ) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .tau (e q j))) = some D ∧
      SymCfg k g e σ sh D (Function.update s q (κ (C.mem () x))) b ∧
      (∀ p, D.pend p = C.pend p) := by
  set v := C.mem () x
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) = (σ ^ i) • (if i < j then κ v else s q)) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p) ∧
    (∀ p, D.pend p = C.pend p) ∧
    (∀ i < g, D.mem () ((sh ^ i) x) = (σ ^ i) • (if i < j then f v else v)) ∧
    (∀ y, (∀ i < g, (sh ^ i) x ≠ y) → D.mem () y = C.mem () y)
  obtain ⟨D, hD, hQ1, hQ1', hQ2, hQ3, hQ4⟩ := runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun _ _ => rfl, fun _ => rfl,
      fun i hi => by simp [hC.mem_pow, v], fun _ _ => rfl⟩
    (by
      rintro j hj D ⟨h1, h1', h2, h3, h4⟩
      have hpend : D.pend (e q j) ≠ none := by rw [h2, hC.pend q hq j hj, hb]; simp
      have hloc : D.loc (e q j) = (σ ^ j) • s q := by simp [h1 j hj]
      have hact' : A.act (D.loc (e q j)) = .rmw x (fun w => (σ ^ j) • f ((σ ^ j)⁻¹ • w))
          (fun w => (σ ^ j) • κ ((σ ^ j)⁻¹ • w)) := by
        rw [hloc, hA.act, hact]; rfl
      have hval : D.mem () ((sh ^ j) x) = (σ ^ j) • v := by simp [h3 j hj]
      refine ⟨_, SymAlg.impl_step_tau_rmw ids π hpend hact', ?_⟩
      simp only [hS.hπ q hq j hj, hval, inv_smul_smul]
      refine ⟨fun i hi => ?_, fun p hp => ?_, fun p => h2 p, fun i hi => ?_, fun y hy => ?_⟩
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e q i ≠ e q j := fun h => hij (hS.einj q i q j hq hi hq hj h).2
          dsimp only; rw [Function.update_of_ne hne, h1 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · dsimp only; rw [Function.update_of_ne (Ne.symm (hp j hj)), h1' p hp]
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
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => by rw [hQ2, hC.pend q' hq' i hi],
    round_mem_aux hS hA hC.mem hg (w := f v) (fun i hi => by simp [hQ3 i hi, hi]) hQ4⟩, hQ2⟩
  by_cases hqq : q' = q
  · subst hqq; simp [hQ1 i hi, hi]
  · rw [hQ1' _ (fun j hj => hS.ne_of_group_ne hA hq hq' hj hi (Ne.symm hqq)), hC.loc q' hq' i hi,
      Function.update_of_ne hqq]

/-- A round of snapshots of group `q` preserves symmetry. -/
lemma round_snap {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option Unit} (hC : SymCfg k g e σ sh C s b)
    {q : ℕ} (hq : q < k) (hb : b q = some ())
    {κ : (Fin m → V) → S} (hact : A.act (s q) = .snap κ) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .tau (e q j))) = some D ∧
      SymCfg k g e σ sh D (Function.update s q (κ (C.mem ()))) b ∧
      (∀ p, D.pend p = C.pend p) := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) = (σ ^ i) • (if i < j then κ (C.mem ()) else s q)) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p) ∧
    (∀ p, D.pend p = C.pend p) ∧ D.mem () = C.mem ()
  obtain ⟨D, hD, hQ1, hQ1', hQ2, hQ3⟩ := runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun _ _ => rfl, fun _ => rfl, rfl⟩
    (by
      rintro j hj D ⟨h1, h1', h2, h3⟩
      have hpend : D.pend (e q j) ≠ none := by rw [h2, hC.pend q hq j hj, hb]; simp
      have hloc : D.loc (e q j) = (σ ^ j) • s q := by simp [h1 j hj]
      have hact' : A.act (D.loc (e q j)) = .snap (fun w => (σ ^ j) • κ ((σ ^ j)⁻¹ • w)) := by
        rw [hloc, hA.act, hact]; rfl
      have hview : (fun y => D.mem () ((sh ^ j) y)) = (σ ^ j) • C.mem () := by
        funext y; rw [h3, hC.mem_pow]; rfl
      refine ⟨_, SymAlg.impl_step_tau_snap ids π hpend hact', ?_⟩
      simp only [hS.hπ q hq j hj, hview, inv_smul_smul]
      refine ⟨fun i hi => ?_, fun p hp => ?_, fun p => h2 p, ?_⟩
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e q i ≠ e q j := fun h => hij (hS.einj q i q j hq hi hq hj h).2
          dsimp only; rw [Function.update_of_ne hne, h1 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · dsimp only; rw [Function.update_of_ne (Ne.symm (hp j hj)), h1' p hp]
      · simp [h3])
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => by rw [hQ2, hC.pend q' hq' i hi],
    fun y => by rw [hQ3, hC.mem]⟩, hQ2⟩
  by_cases hqq : q' = q
  · subst hqq; simp [hQ1 i hi, hi]
  · rw [hQ1' _ (fun j hj => hS.ne_of_group_ne hA hq hq' hj hi (Ne.symm hqq)), hC.loc q' hq' i hi,
      Function.update_of_ne hqq]

/-- A round in which the members of group `q` return (all with the same response `r`). -/
lemma round_ret {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option Unit} (hC : SymCfg k g e σ sh C s b)
    {q : ℕ} (hq : q < k) (hb : b q = some ()) {r : R} {s' : S} (hact : A.act (s q) = .ret r s') :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .ret (e q j) r)) = some D ∧
      SymCfg k g e σ sh D (Function.update s q s') (Function.update b q none) ∧
      (∀ p, (∀ i < g, e q i ≠ p) → D.pend p = C.pend p) := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) = (σ ^ i) • (if i < j then s' else s q)) ∧
    (∀ i < g, D.pend (e q i) = if i < j then none else b q) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p ∧ D.pend p = C.pend p) ∧
    D.mem () = C.mem ()
  obtain ⟨D, hD, hQ1, hQ2, hQ3, hQ4⟩ := runFrom_range (A.impl ids π) Q _ g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun i hi => by simp [hC.pend q hq i hi],
      fun _ _ => ⟨rfl, rfl⟩, rfl⟩
    (by
      rintro j hj D ⟨h1, h2, h3, h4⟩
      have hpend : D.pend (e q j) ≠ none := by simp [h2 j hj, hb]
      have hloc : D.loc (e q j) = (σ ^ j) • s q := by simp [h1 j hj]
      have hact' : A.act (D.loc (e q j)) = .ret r ((σ ^ j) • s') := by
        rw [hloc, hA.act, hact]; rfl
      refine ⟨_, SymAlg.impl_step_ret ids π hpend hact', fun i hi => ?_, fun i hi => ?_,
        fun p hp => ?_, by simpa using h4⟩
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e q i ≠ e q j := fun h => hij (hS.einj q i q j hq hi hq hj h).2
          dsimp only; rw [Function.update_of_ne hne, h1 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e q i ≠ e q j := fun h => hij (hS.einj q i q j hq hi hq hj h).2
          dsimp only; rw [Function.update_of_ne hne, h2 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · dsimp only
        rw [Function.update_of_ne (Ne.symm (hp j hj)), Function.update_of_ne (Ne.symm (hp j hj))]
        exact h3 p hp)
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => ?_, fun y => by rw [hQ4, hC.mem]⟩,
    fun p hp => (hQ3 p hp).2⟩
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ1 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hA hq hq' hj hi (Ne.symm hqq))).1,
        hC.loc q' hq' i hi, Function.update_of_ne hqq]
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ2 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hA hq hq' hj hi (Ne.symm hqq))).2,
        hC.pend q' hq' i hi, Function.update_of_ne hqq]

/-- The invocation round of group `q`. -/
lemma round_inv {C : A.Cfg} {s : ℕ → S} {b : ℕ → Option Unit} (hC : SymCfg k g e σ sh C s b)
    {q : ℕ} (hq : q < k) (hb : b q = none) :
    ∃ D, (A.impl ids π).runFrom C ((List.range g).map (fun j => .inv (e q j) ())) = some D ∧
      SymCfg k g e σ sh D (Function.update s q (A.invoke (s q) ()))
        (Function.update b q (some ())) := by
  let Q : ℕ → A.Cfg → Prop := fun j D =>
    (∀ i < g, D.loc (e q i) = (σ ^ i) • (if i < j then A.invoke (s q) () else s q)) ∧
    (∀ i < g, D.pend (e q i) = if i < j then some () else b q) ∧
    (∀ p, (∀ i < g, e q i ≠ p) → D.loc p = C.loc p ∧ D.pend p = C.pend p) ∧
    D.mem () = C.mem ()
  obtain ⟨D, hD, hQ1, hQ2, hQ3, hQ4⟩ := runFrom_range (A.impl ids π) Q
    (fun j => Label.inv (e q j) ()) g C
    ⟨fun i hi => by simp [hC.loc q hq i hi], fun i hi => by simp [hC.pend q hq i hi],
      fun _ _ => ⟨rfl, rfl⟩, rfl⟩
    (by
      rintro j hj D ⟨h1, h2, h3, h4⟩
      have hpend : D.pend (e q j) = none := by simp [h2 j hj, hb]
      refine ⟨_, SymAlg.impl_step_inv (o := ()) ids π hpend, fun i hi => ?_, fun i hi => ?_,
        fun p hp => ?_, by simpa using h4⟩
      · by_cases hij : i = j
        · subst hij; simp [h1 i hi, hA.invoke]
        · have hne : e q i ≠ e q j := fun h => hij (hS.einj q i q j hq hi hq hj h).2
          dsimp only; rw [Function.update_of_ne hne, h1 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · by_cases hij : i = j
        · subst hij; simp
        · have hne : e q i ≠ e q j := fun h => hij (hS.einj q i q j hq hi hq hj h).2
          dsimp only; rw [Function.update_of_ne hne, h2 i hi]
          by_cases hi' : i < j
          · simp [hi', show i < j + 1 by omega]
          · simp [hi', show ¬ i < j + 1 by omega]
      · dsimp only
        rw [Function.update_of_ne (Ne.symm (hp j hj)), Function.update_of_ne (Ne.symm (hp j hj))]
        exact h3 p hp)
  refine ⟨D, hD, ⟨fun q' hq' i hi => ?_, fun q' hq' i hi => ?_, fun y => by rw [hQ4, hC.mem]⟩⟩
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ1 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hA hq hq' hj hi (Ne.symm hqq))).1,
        hC.loc q' hq' i hi, Function.update_of_ne hqq]
  · by_cases hqq : q' = q
    · subst hqq; simp [hQ2 i hi, hi]
    · rw [(hQ3 _ (fun j hj => hS.ne_of_group_ne hA hq hq' hj hi (Ne.symm hqq))).2,
        hC.pend q' hq' i hi, Function.update_of_ne hqq]

/-- The initial configuration is symmetric. -/
lemma symCfg_init :
    SymCfg k g e σ sh (A.impl ids π).initCfg (fun q => A.init (a q)) (fun _ => none) :=
  ⟨fun q hq i hi => by
    show A.init (ids (e q i)) = _
    rw [hS.hid q hq i hi, hA.init],
   fun _ _ _ _ => rfl, fun _ => by simp [Impl.initCfg, SymAlg.impl, hA.bot]⟩

end Rounds

end LockStep

end BezoutElection
