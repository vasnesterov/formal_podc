import Cslib.Computability.Distributed.SharedMemory.Anonymous.LockStep
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.Nat.GCD.Basic
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

The symmetric rounds are the one-group case (`k = 1`) of the shared lock-step library
`Cslib.Computability.Distributed.SharedMemory.Anonymous.LockStep` (`SymAlg.LSSetup.single`, `SymAlg.round_rmw`, …).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex

/-- `M(n) = {m : ∀ ℓ, 1 < ℓ ≤ n → gcd(ℓ, m) = 1}`. -/
def M (n : ℕ) : Set ℕ := {m | ∀ ℓ, 1 < ℓ → ℓ ≤ n → Nat.Coprime ℓ m}

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
  {g : ℕ} {e : ℕ → P} {σ : Equiv.Perm Id} {sh : Equiv.Perm (Fin m)} {a₀ : Id}

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
theorem not_mutualExclusion_and_deadlockFree
    (hS : SymAlg.LSSetup 1 g (fun _ => e) σ sh (fun _ => a₀) ids π) (hA : A.Symmetric)
    (hg : 2 ≤ g) :
    ¬ ((A.impl ids π).MutualExclusion ∧ (A.impl ids π).DeadlockFree) := by
  rintro ⟨hME, hDF⟩
  have hg0 : 0 < g := by omega
  have he : ∀ i j, i < g → j < g → e i = e j → i = j :=
    fun i j hi hj h => (hS.einj 0 i 0 j one_pos hi one_pos hj h).2
  set E : ℕ → List (Label P mutexObj) := fun k => (List.range (g * (k + 1))).map (lsLabel g e)
    with hE
  -- the processes never return
  have key : ∀ k C s b, (A.impl ids π).run (E k) = some C →
      SymAlg.SymCfg 1 g (fun _ => e) σ sh C s b → b 0 = some .lock →
      ∀ r s', A.act (s 0) ≠ .ret r s' := by
    intro k C s b hrun hC hb r s' hact
    obtain ⟨D, hD, -⟩ := SymAlg.round_ret hS hA hC one_pos (by simp [hb]) hact
    have hval : (A.impl ids π).Valid
        (E k ++ (List.range g).map (fun j => .ret (e j) ())) :=
      ⟨D, by rw [Impl.run_append_of_eq _ hrun]; exact hD⟩
    have hreg := regionOf_append_map_range g e he (E k) (fun j => .ret (e j) ())
      (fun j => rfl) g le_rfl
    have hEk := regionOf_lsLabel (e := e) he hg0 (g * (k + 1))
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
    have := he 0 1 hg0 (by omega) (hME _ hval hwf _ _ (hcs 0 hg0) (hcs 1 (by omega)))
    omega
  have all : ∀ k, ∃ C s b, (A.impl ids π).run (E k) = some C ∧
      SymAlg.SymCfg 1 g (fun _ => e) σ sh C s b ∧ b 0 = some .lock := by
    intro k
    induction k with
    | zero =>
      obtain ⟨D, hD, hsym, -⟩ :=
        SymAlg.round_inv hS hA (SymAlg.symCfg_init hS hA) one_pos rfl MutexOp.lock
      exact ⟨D, _, _, by simp only [hE, zero_add, mul_one, range_map_lsLabel_zero]; exact hD,
        hsym, by simp⟩
    | succ k ih =>
      obtain ⟨C, s, b, hC, hsym, hb⟩ := ih
      have hEs : E (k + 1) = E k ++ (List.range g).map (fun j => .tau (e j)) :=
        range_map_lsLabel_succ k
      cases hact : A.act (s 0) with
      | rmw x f k' =>
        obtain ⟨D, hD, hsym', -⟩ := SymAlg.round_rmw hS hA hsym one_pos (by simp [hb]) hg0 hact
        exact ⟨D, _, b, by rw [hEs, Impl.run_append_of_eq _ hC]; exact hD, hsym', hb⟩
      | snap k' =>
        obtain ⟨D, hD, hsym', -⟩ := SymAlg.round_snap hS hA hsym one_pos (by simp [hb]) hact
        exact ⟨D, _, b, by rw [hEs, Impl.run_append_of_eq _ hC]; exact hD, hsym', hb⟩
      | ret r s' => exact absurd hact (key k C s b hC hsym hb r s')
  -- the infinite lock-step execution
  obtain ⟨ex, hlbl, -⟩ := (A.impl ids π).exists_infExec_of_chain E
    (fun k => by rw [show E (k + 1) = E k ++ _ from range_map_lsLabel_succ k];
                 exact List.prefix_append _ _)
    (fun k => by simp only [hE, List.length_map, List.length_range]; nlinarith)
    (fun k => by obtain ⟨C, -, -, hC, -⟩ := all k; exact ⟨C, hC⟩)
  have hl : ∀ n, ex.lbl n = lsLabel g e n := fun n => by
    rw [hlbl n n (by simp only [hE, List.length_map, List.length_range]; nlinarith)]
    simp [hE]
  have hpre : ∀ t, ex.pre t = (List.range t).map (lsLabel g e) := fun t => by
    simp only [Impl.InfExec.pre]
    exact List.map_congr_left (fun n _ => hl n)
  have hreg := regionOf_lsLabel (e := e) he hg0
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
  obtain ⟨C₀, s₀, b₀, hC₀, hsym₀, hb₀⟩ := all 0
  have hcfg : ex.cfg g = C₀ := by
    have h1 := ex.run_pre g
    rw [hpre] at h1
    have : E 0 = (List.range g).map (lsLabel g e) := by simp [hE]
    rw [this] at hC₀
    rw [hC₀] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨t', -, p, r, hret⟩ := hDF ex hwf hfair g ⟨e 0, by rw [hcfg, hsym₀.pend 0 one_pos 0 hg0, hb₀]; simp⟩
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
  have hS : SymAlg.LSSetup 1 g (fun _ => e) σ sh (fun _ => ids (e 0)) ids π :=
    SymAlg.LSSetup.single
      (by rw [← hlen]; exact List.formPerm_pow_length_eq_one_of_nodup l hl)
      (finRotate_pow_pow_eq_one hdg)
      (fun i j y hi hj hij => finRotate_pow_pow_apply_inj hdg hi hj hij)
      einj
      (fun i hi => by
        simp only [π, e, Equiv.apply_symm_apply, Nat.mod_eq_of_lt (show i < n by omega)])
      (fun i hi => by
        have := List.formPerm_pow_apply_getElem l hl i 0 (by omega)
        simp only [zero_add, hlen, Nat.mod_eq_of_lt hi] at this
        simp only [l, List.getElem_map, List.getElem_range] at this
        exact this.symm)
  exact not_mutualExclusion_and_deadlockFree hS hA hg2 (h π)

end AnonymousMutex
