import Papers.PODC2021.ScannableBinaryObjects.Impl1Steps
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Implementation 1 is lock-free (Theorem 2 of Ovens, PODC 2021, progress part)

Suppose that from some time `N` on no operation returns. Then

1. the potential `Psi` (an idle process counts `s + 2`, an update with `j` handshaking
   writes left counts `j + 1`, everything else `0`) never increases after `N` and strictly
   decreases at every invocation and every step of an update; hence from some time `T` on all
   steps are steps of scans and no base object `B i` changes any more;
2. after `T` the potential `Mu` (remaining steps of each scan, computed from its local state, the
   now constant values of `B` and its handshaking bit) strictly decreases at every step —
   a contradiction, since the execution is infinite.

This is the paper's argument (a scan restarts only when it observes a change of some `B i` or
a `1` in its handshaking bit; every update writes each handshaking bit once and modifies one
`B i` once), organised as two potential functions.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

namespace Impl1

open List

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]
  {R : ∀ i, (O i).Readable} {Sc Up : Finset P} {h₀ : Sc → Bool}

/-! ### Generic facts -/

/-- A non-increasing sequence of naturals is eventually constant. -/
lemma eventually_const (f : ℕ → ℕ) (N : ℕ) (hmono : ∀ m ≥ N, f (m + 1) ≤ f m) :
    ∃ T ≥ N, ∀ m ≥ T, f (m + 1) = f m := by
  have anti : ∀ a b, N ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact (hmono b (ha.trans hb)).trans ih
  by_contra hc
  push Not at hc
  have key : ∀ c, ∃ t ≥ N, f t + c ≤ f N := by
    intro c
    induction c with
    | zero => exact ⟨N, le_rfl, le_rfl⟩
    | succ c ih =>
      obtain ⟨t, ht, hc'⟩ := ih
      obtain ⟨m, hm, hne⟩ := hc t ht
      have h1 := hmono m (ht.trans hm)
      have h2 := anti t m ht hm
      exact ⟨m + 1, by omega, by omega⟩
  obtain ⟨t, -, ht⟩ := key (f N + 1)
  omega

lemma sum_le_of_update [Fintype P] {f g : P → ℕ} (q : P) (h : ∀ r, r ≠ q → g r = f r)
    (hq : g q ≤ f q) : ∑ r, g r ≤ ∑ r, f r :=
  Finset.sum_le_sum fun r _ => by
    by_cases hr : r = q
    · subst hr; exact hq
    · exact (h r hr).le

lemma sum_lt_of_update [Fintype P] {f g : P → ℕ} (q : P) (h : ∀ r, r ≠ q → g r = f r)
    (hq : g q < f q) : ∑ r, g r < ∑ r, f r :=
  Finset.sum_lt_sum (fun r _ => by
    by_cases hr : r = q
    · subst hr; exact hq.le
    · exact (h r hr).le) ⟨q, Finset.mem_univ _, hq⟩

/-- The configurations of an infinite execution are reachable. -/
lemma run_range {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι]
    {I : Impl A B P L} (e : I.InfExec) (t : ℕ) :
    I.run ((List.range t).map e.lbl) = some (e.cfg t) := by
  induction t with
  | zero => simp [e.cfg_zero]
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, Impl.run_append_of_eq _ ih,
      Impl.runFrom_singleton]
    exact e.step_eq t

/-! ### Phase 1: updates and invocations stop -/

/-- Potential of updates and idle processes. -/
def psi (Sc : Finset P) : Loc O Sc → ℕ
  | .idle => Sc.card + 2
  | .upd _ _ rest => rest.length + 1
  | _ => 0

/-- Local states of a scan. -/
def IsScanLoc : Loc O Sc → Prop
  | .scan1 _ _ => True
  | .scan2 _ _ _ => True
  | _ => False

lemma psi_step [Fintype P] {α : List (Label P (scannable O))}
    {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)} {L : List (OpId P × ScanOp O)}
    (hI : Inv Sc Up α C L) {ℓ : Label P (scannable O)}
    (h : (impl1 R Sc Up h₀).step C ℓ = some C') (hret : ∀ p r, ℓ ≠ .ret p r) :
    ∑ p, psi Sc (C'.loc p) ≤ ∑ p, psi Sc (C.loc p) ∧
      (∑ p, psi Sc (C'.loc p) = ∑ p, psi Sc (C.loc p) →
        ∃ q, ℓ = .tau q ∧ IsScanLoc (C.loc q)) := by
  have hoth := loc_other h
  cases ℓ with
  | ret p r => exact absurd rfl (hret p r)
  | inv q o =>
    obtain ⟨h0, -, -, hloc, -⟩ := Impl.step_inv h
    have hidle : C.loc q = .idle := by
      have := hI.proc q
      cases hl : C.loc q <;> simp only [PInvL, hl] at this <;> simp_all
    have hlt : psi Sc (C'.loc q) < psi Sc (C.loc q) := by
      rw [hloc, Function.update_self, hidle]
      cases o with
      | scan => simp [impl1, psi]
      | update i o =>
        simp only [impl1, psi, Finset.length_toList, Finset.card_univ, Fintype.card_coe]
        omega
    have := sum_lt_of_update q (fun r hr => congrArg (psi Sc) (hoth r hr)) hlt
    exact ⟨this.le, fun he => by omega⟩
  | tau q =>
    cases hl : C.loc q with
    | idle => rw [step_tau_idle hl] at h; cases h
    | done r => rw [step_tau_done hl] at h; cases h
    | upd i o rest =>
      have hlt : psi Sc (C'.loc q) < psi Sc (C.loc q) := by
        cases rest with
        | nil =>
          obtain ⟨-, -, hloc⟩ := step_upd_nil hl h
          rw [hloc, Function.update_self, hl]; simp [psi]
        | cons j rest =>
          obtain ⟨-, -, hloc⟩ := step_upd_cons hl h
          rw [hloc, Function.update_self, hl]; simp [psi]
      have := sum_lt_of_update q (fun r hr => congrArg (psi Sc) (hoth r hr)) hlt
      exact ⟨this.le, fun he => by omega⟩
    | scan1 m b =>
      have hle : psi Sc (C'.loc q) ≤ psi Sc (C.loc q) := by
        by_cases hm : m < k
        · obtain ⟨-, -, hloc⟩ := step_scan1_lt hm hl h
          rw [hloc, Function.update_self, hl]; simp [psi]
        · obtain ⟨_, _, _, hloc⟩ := step_scan1_ge hm hl h
          rw [hloc, Function.update_self, hl]; simp [psi]
      exact ⟨sum_le_of_update q (fun r hr => congrArg (psi Sc) (hoth r hr)) hle,
        fun _ => ⟨q, rfl, by rw [hl]; trivial⟩⟩
    | scan2 c m b =>
      have hle : psi Sc (C'.loc q) ≤ psi Sc (C.loc q) := by
        by_cases hm : m < k
        · obtain ⟨-, -, hloc⟩ := step_scan2_lt hm hl h
          rw [hloc, Function.update_self, hl]; split <;> simp [psi]
        · obtain ⟨_, _, _, hloc⟩ := step_scan2_ge hm hl h
          rw [hloc, Function.update_self, hl]; split
          · simp [psi]
          · split <;> simp [psi]
      exact ⟨sum_le_of_update q (fun r hr => congrArg (psi Sc) (hoth r hr)) hle,
        fun _ => ⟨q, rfl, by rw [hl]; trivial⟩⟩

/-! ### Phase 2: scans finish -/

open Classical in
/-- Remaining steps of a scan when the values `V` of `B` and the handshaking bit `r` of the
scanner do not change any more: a fresh scan needs `k + 1` steps for its first collect and then
`(u + 1) (k + 1)` steps for `u + 1` collects; a scan whose `b` disagrees with `V` restarts within
at most two more collects. -/
noncomputable def mu (u : ℕ) (V : Fin k → Bool) (r : Bool) : Loc O Sc → ℕ
  | .scan1 m b => (k - m) + 1 + (if ∀ i : Fin k, i.val < m → b i = V i then u * (k + 1) + (k + 1)
      else (k + 1) + (k + 1 + (u * (k + 1) + (k + 1))))
  | .scan2 c m b => if b = V ∧ r = false then (u - c) * (k + 1) + (k - m) + 1
      else if r = true ∨ ∃ i : Fin k, m ≤ i.val ∧ b i ≠ V i then
        (k - m) + 1 + (k + 1 + (u * (k + 1) + (k + 1)))
      else (k - m) + 1 + (k + 1) + (k + 1 + (u * (k + 1) + (k + 1)))
  | _ => 0

lemma mu_scan1_zero (u : ℕ) (V : Fin k → Bool) (r : Bool) (b : Fin k → Bool) :
    mu u V r (.scan1 0 b : Loc O Sc) = k + 1 + (u * (k + 1) + (k + 1)) := by
  simp [mu]

lemma mu_scan1_lt (u : ℕ) (V : Fin k → Bool) (r r' : Bool) {m : ℕ} (b : Fin k → Bool)
    (hm : m < k) :
    mu u V r (.scan1 (m + 1) (Function.update b ⟨m, hm⟩ (V ⟨m, hm⟩)) : Loc O Sc) <
      mu u V r' (.scan1 m b : Loc O Sc) := by
  have hg : (∀ i : Fin k, i.val < m + 1 → Function.update b ⟨m, hm⟩ (V ⟨m, hm⟩) i = V i) ↔
      (∀ i : Fin k, i.val < m → b i = V i) := by
    constructor
    · intro h i hi
      have := h i (by omega)
      rwa [Function.update_of_ne (fun he => by rw [he] at hi; simp at hi)] at this
    · intro h i hi
      by_cases he : i = ⟨m, hm⟩
      · subst he; simp
      · rw [Function.update_of_ne he]
        exact h i (by
          rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
          · exact hi
          · exact absurd (Fin.ext hi) he)
  simp only [mu]
  split_ifs with h1 h2 h2
  · omega
  · exact absurd (hg.1 h1) h2
  · exact absurd (hg.2 h2) h1
  · omega

lemma mu_scan1_ge (u : ℕ) (V : Fin k → Bool) (r : Bool) {m : ℕ} (b : Fin k → Bool)
    (hm : ¬ m < k) :
    mu u V false (.scan2 0 0 b : Loc O Sc) < mu u V r (.scan1 m b : Loc O Sc) := by
  by_cases hg : ∀ i : Fin k, i.val < m → b i = V i
  · have hb : b = V := funext fun i => hg i (by omega)
    subst hb
    simp only [mu, and_self, implies_true, ↓reduceIte, Nat.sub_zero]
    omega
  · have hb : b ≠ V := fun h => hg (fun i _ => by rw [h])
    have hex : ∃ i : Fin k, 0 ≤ i.val ∧ b i ≠ V i := by
      by_contra hc; push Not at hc; exact hb (funext fun i => hc i (Nat.zero_le _))
    simp only [mu, hg, hb, hex, false_and, or_true, ↓reduceIte, Nat.sub_zero]
    omega

lemma mu_scan2_lt (u : ℕ) (V : Fin k → Bool) (r : Bool) {c m : ℕ} (b : Fin k → Bool)
    (hm : m < k) :
    mu u V r (if V ⟨m, hm⟩ = b ⟨m, hm⟩ then .scan2 c (m + 1) b else .scan1 0 b : Loc O Sc) <
      mu u V r (.scan2 c m b : Loc O Sc) := by
  by_cases heq : V ⟨m, hm⟩ = b ⟨m, hm⟩
  · simp only [heq, ↓reduceIte]
    by_cases hgood : b = V ∧ r = false
    · simp only [mu, hgood, and_self, ↓reduceIte]; omega
    · by_cases hbad : r = true ∨ ∃ i : Fin k, m ≤ i.val ∧ b i ≠ V i
      · have hbad' : r = true ∨ ∃ i : Fin k, m + 1 ≤ i.val ∧ b i ≠ V i := by
          rcases hbad with hr | ⟨i, hi, hne⟩
          · exact Or.inl hr
          · refine Or.inr ⟨i, ?_, hne⟩
            rcases Nat.lt_or_eq_of_le hi with hi | hi
            · exact hi
            · exfalso; apply hne
              have : i = ⟨m, hm⟩ := Fin.ext hi.symm
              rw [this, heq]
        simp only [mu, hgood, hbad, hbad', ↓reduceIte]; omega
      · have hbad' : ¬ (r = true ∨ ∃ i : Fin k, m + 1 ≤ i.val ∧ b i ≠ V i) := by
          rintro (hr | ⟨i, hi, hne⟩)
          · exact hbad (Or.inl hr)
          · exact hbad (Or.inr ⟨i, by omega, hne⟩)
        simp only [mu, hgood, hbad, hbad', ↓reduceIte]; omega
  · simp only [heq, ↓reduceIte, mu_scan1_zero]
    have hgood : ¬ (b = V ∧ r = false) := fun h => heq (by rw [h.1])
    have hbad : r = true ∨ ∃ i : Fin k, m ≤ i.val ∧ b i ≠ V i :=
      Or.inr ⟨⟨m, hm⟩, le_refl _, fun h => heq h.symm⟩
    simp only [mu, hgood, hbad, ↓reduceIte]; omega

lemma mu_scan2_ge (u : ℕ) (V : Fin k → Bool) (r : Bool) {c m : ℕ} (b : Fin k → Bool)
    (hm : ¬ m < k) :
    mu u V r (if r = true then .scan1 0 b else if c < u then .scan2 (c + 1) 0 b
      else .done (.view b) : Loc O Sc) < mu u V r (.scan2 c m b : Loc O Sc) := by
  by_cases hr : r = true
  · simp only [hr, ↓reduceIte, mu_scan1_zero]
    simp only [mu, Bool.true_eq_false, and_false, true_or, ↓reduceIte]; omega
  · have hr' : r = false := by simpa using hr
    subst hr'
    have hnb : ¬ ∃ i : Fin k, m ≤ i.val ∧ b i ≠ V i := fun ⟨i, hi, _⟩ => by omega
    by_cases hc : c < u
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      by_cases hb : b = V
      · subst hb
        simp only [mu, and_self, ↓reduceIte]
        have : (u - c) * (k + 1) = (u - (c + 1)) * (k + 1) + (k + 1) := by
          rw [show u - c = (u - (c + 1)) + 1 by omega, Nat.succ_mul]
        omega
      · have hex : ∃ i : Fin k, 0 ≤ i.val ∧ b i ≠ V i := by
          by_contra hcon; push Not at hcon; exact hb (funext fun i => hcon i (Nat.zero_le _))
        simp only [mu, hb, false_and, hex, hnb, or_true, or_false, Bool.false_eq_true,
          ↓reduceIte]
        omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]
      simp only [mu]
      split_ifs <;> omega

/-- Values of the base objects `B`. -/
def bval (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) : Fin k → Bool :=
  fun i => C.mem (.inl i)

/-- The handshaking bit of `p` (`true` for non-scanners). -/
def rbit (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) (p : P) : Bool :=
  if hp : p ∈ Sc then C.mem (.inr ⟨p, hp⟩) else true

/-- Total remaining work of all scans. -/
noncomputable def Mu [Fintype P] (u : ℕ) (C : Config (scannable O) (Obj O Sc) P (Loc O Sc)) :
    ℕ :=
  ∑ p, mu u (bval C) (rbit C p) (C.loc p)

lemma Mu_lt [Fintype P] (u : ℕ) {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)} {q : P}
    (hloc : ∀ r, r ≠ q → C'.loc r = C.loc r) (hV : bval C' = bval C)
    (hr : ∀ p, p ≠ q → rbit C' p = rbit C p)
    (hq : mu u (bval C') (rbit C' q) (C'.loc q) < mu u (bval C) (rbit C q) (C.loc q)) :
    Mu u C' < Mu u C :=
  sum_lt_of_update q (fun r hr' => by rw [hloc r hr', hV, hr r hr']) hq

lemma Mu_step [Fintype P] {C C' : Config (scannable O) (Obj O Sc) P (Loc O Sc)} {q : P} (hl : IsScanLoc (C.loc q))
    (h : (impl1 R Sc Up h₀).step C (.tau q) = some C') :
    Mu Up.card C' < Mu Up.card C := by
  have hoth := loc_other h
  cases hlq : C.loc q with
  | idle => rw [hlq] at hl; exact hl.elim
  | done r => rw [hlq] at hl; exact hl.elim
  | upd i o rest => rw [hlq] at hl; exact hl.elim
  | scan1 m b =>
    by_cases hm : m < k
    · obtain ⟨-, hmem, hloc⟩ := step_scan1_lt hm hlq h
      have hV : bval C' = bval C := by funext i; simp [bval, hmem]
      have hr : ∀ p, rbit C' p = rbit C p := fun p => by simp [rbit, hmem]
      refine Mu_lt _ hoth hV (fun p _ => hr p) ?_
      simp only [Label.proc]; rw [hloc, Function.update_self, hV, hr, hlq]
      exact mu_scan1_lt _ _ _ _ b hm
    · obtain ⟨hqS, -, hmem, hloc⟩ := step_scan1_ge hm hlq h
      have hV : bval C' = bval C := by funext i; simp [bval, hmem]
      have hr : ∀ p, p ≠ q → rbit C' p = rbit C p := fun p hp => by
        by_cases hpS : p ∈ Sc
        · simp only [rbit, hpS, dite_true, hmem]
          rw [Function.update_of_ne (by simpa using hp)]
        · simp [rbit, hpS]
      have hrq : rbit C' q = false := by simp [rbit, hqS, hmem]
      refine Mu_lt _ hoth hV hr ?_
      simp only [Label.proc]; rw [hloc, Function.update_self, hV, hrq, hlq]
      exact mu_scan1_ge _ _ _ b hm
  | scan2 c m b =>
    by_cases hm : m < k
    · obtain ⟨-, hmem, hloc⟩ := step_scan2_lt hm hlq h
      have hV : bval C' = bval C := by funext i; simp [bval, hmem]
      have hr : ∀ p, rbit C' p = rbit C p := fun p => by simp [rbit, hmem]
      refine Mu_lt _ hoth hV (fun p _ => hr p) ?_
      simp only [Label.proc]; rw [hloc, Function.update_self, hV, hr, hlq]
      exact mu_scan2_lt _ (bval C) _ b hm
    · obtain ⟨hqS, -, hmem, hloc⟩ := step_scan2_ge hm hlq h
      have hV : bval C' = bval C := by funext i; simp [bval, hmem]
      have hr : ∀ p, rbit C' p = rbit C p := fun p => by simp [rbit, hmem]
      have hrq : rbit C q = C.mem (.inr ⟨q, hqS⟩) := by simp [rbit, hqS]
      refine Mu_lt _ hoth hV (fun p _ => hr p) ?_
      simp only [Label.proc]; rw [hloc, Function.update_self, hV, hr, hlq, hrq]
      exact mu_scan2_ge _ _ _ b hm

end Impl1

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

open Impl1 in
/-- **Theorem 2 of Ovens (PODC 2021), progress**: Implementation 1 is lock-free (for finitely
many processes, any scanners/updaters, readable components and initial handshaking bits). -/
theorem impl1_lockFree [Fintype P] (R : ∀ i, (O i).Readable) (Sc Up : Finset P)
    (h₀ : Sc → Bool) : (impl1 R Sc Up h₀).LockFree := by
  intro e _ N
  by_contra hcon
  push Not at hcon
  have hInv : ∀ t, ∃ L, Inv Sc Up ((List.range t).map e.lbl) (e.cfg t) L :=
    fun t => inv_of_run (run_range e t)
  have hψ : ∀ m ≥ N, ∑ p, psi Sc ((e.cfg (m + 1)).loc p) ≤ ∑ p, psi Sc ((e.cfg m).loc p) ∧
      (∑ p, psi Sc ((e.cfg (m + 1)).loc p) = ∑ p, psi Sc ((e.cfg m).loc p) →
        ∃ q, e.lbl m = .tau q ∧ IsScanLoc ((e.cfg m).loc q)) := fun m hm => by
    obtain ⟨L, hL⟩ := hInv m
    exact psi_step hL (e.step_eq m) (hcon m hm)
  obtain ⟨T, hTN, hT⟩ := eventually_const (fun t => ∑ p, psi Sc ((e.cfg t).loc p)) N
    (fun m hm => (hψ m hm).1)
  have hM : ∀ m ≥ T, Mu Up.card (e.cfg (m + 1)) < Mu Up.card (e.cfg m) := by
    intro m hm
    obtain ⟨q, hlq, hsc⟩ := (hψ m (by omega)).2 (hT m hm)
    have hs := e.step_eq m
    rw [hlq] at hs
    exact Mu_step hsc hs
  have key : ∀ n, Mu Up.card (e.cfg (T + n)) + n ≤ Mu Up.card (e.cfg T) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hM (T + n) (by omega)
      rw [show T + (n + 1) = T + n + 1 by omega]
      omega
  have := key (Mu Up.card (e.cfg T) + 1)
  omega

end Cslib.SharedMemory.Scannable

namespace Cslib.SharedMemory.Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]
  {I : Impl A B P L}

-- CSLib candidate
/-- Lock-freedom implies obstruction-freedom: a process running solo forever would yield an
infinite execution with infinitely many steps and only finitely many responses. -/
theorem LockFree.obstructionFree (hlf : I.LockFree) : I.ObstructionFree := by
  intro C p ⟨α, hα⟩ hp
  by_contra hcon
  push Not at hcon
  let E : ℕ → List (Label P A) := fun k => α ++ I.soloLabels p C k
  have hE : ∀ k, I.run (E k) = some ((I.soloStep p)^[k] C) := fun k => by
    simp only [E]; rw [run_append_of_eq I hα, runFrom_soloLabels]
  have hElen : ∀ k, (E k).length = α.length + k := fun k => by
    simp only [E, List.length_append, I.soloLabels_length p C k (fun i _ => hcon i)]
  obtain ⟨e, hlbl, hcfg⟩ := I.exists_infExec_of_chain E
    (fun k => (List.prefix_append_right_inj α).2 (I.soloLabels_prefix p C k))
    (fun k => by rw [hElen]; omega) (fun k => ⟨_, hE k⟩)
  have hpend : ∀ m ≥ α.length, (e.cfg m).pend p ≠ none := by
    intro m hm
    have h := hcfg (m - α.length) m (by rw [hElen]; omega)
    rw [List.take_of_length_le (by rw [hElen]; omega), hE] at h
    rw [← Option.some_inj.1 h]; exact hcon _
  have htau : ∀ m ≥ α.length, e.lbl m = .tau p := by
    intro m hm
    apply I.eq_tau_of_step (e.step_eq _) _ (hpend _ hm) (hpend _ (by omega))
    rw [hlbl (m + 1) m (by rw [hElen]; omega)]
    simp only [E]
    rw [List.getElem_append_right (by omega)]
    exact I.soloLabels_proc p C _ _ (List.getElem_mem _)
  obtain ⟨m, hm, q, r, hr⟩ := hlf e (fun N => ⟨N + α.length, by omega, by
    rw [htau _ (by omega)]; trivial⟩) α.length
  rw [htau m hm] at hr
  cases hr

end Cslib.SharedMemory.Impl

namespace Cslib.SharedMemory.Scannable

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

open Impl1 in
/-- Implementation 1 is obstruction-free (finitely many processes). -/
theorem impl1_obstructionFree [Fintype P] (R : ∀ i, (O i).Readable) (Sc Up : Finset P)
    (h₀ : Sc → Bool) : (impl1 R Sc Up h₀).ObstructionFree :=
  (impl1_lockFree R Sc Up h₀).obstructionFree

end Cslib.SharedMemory.Scannable
