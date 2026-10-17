import Papers.PODC2020.BezoutElection.LockStepExec
import Papers.PODC2019.AnonymousMutex.LowerBound
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Theorem 1: the impossibility results

Godard, Imbs, Raynal, Taubenfeld, PODC 2020, Section 2, Theorem 1.

Let `δ = gcd(m, n)`. Split the `n` processes into `k = n/δ` groups of `δ` processes; the `i`-th
member of every group sees the anonymous memory rotated by `i · (m/δ)` and has identifier
`τ^i` applied to the identifier of the first member, where `τ` cycles every group. In the
lock-step execution (`exists_symmetric_outcome`) all members of a group return the same bit, so
the number of elected processes is a multiple of `δ` (`exists_elected_mul`). Hence a terminating
symmetric `d`-election algorithm needs `δ ≤ d` (Theorem 1(1)) and an exact `d`-election algorithm
needs `δ ∣ d` (Theorem 1(2)).

The result holds for arbitrary read-modify-write registers *and* atomic snapshots of the whole
anonymous memory, for any register values and local states, and it uses a single injective
identifier assignment (only the anonymity permutations are adversarial).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

section Construction

variable {P : Type} [Fintype P] [DecidableEq P] {Id : Type} (ids : P → Id) (m : ℕ)

/-- The number of groups `k = n / δ` times the group size `δ = gcd(m, n)` is `n`. -/
lemma groups_mul : Fintype.card P / Nat.gcd m (Fintype.card P) * Nat.gcd m (Fintype.card P) =
    Fintype.card P := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)

/-- Processes as pairs (group, position). -/
noncomputable def grp : P ≃ Fin (Fintype.card P / Nat.gcd m (Fintype.card P)) ×
    Fin (Nat.gcd m (Fintype.card P)) :=
  (Fintype.equivFin P).trans ((finCongr (groups_mul (P := P) m).symm).trans finProdFinEquiv.symm)

variable (hn : 0 < Fintype.card P)
include hn

lemma gcd_pos' : 0 < Nat.gcd m (Fintype.card P) := Nat.gcd_pos_of_pos_right _ hn

lemma ngroups_pos : 0 < Fintype.card P / Nat.gcd m (Fintype.card P) := by
  have h := groups_mul (P := P) m
  rcases Nat.eq_zero_or_pos (Fintype.card P / Nat.gcd m (Fintype.card P)) with h0 | h0
  · rw [h0, zero_mul] at h; omega
  · exact h0

/-- The `i`-th member of group `q`. -/
noncomputable def mem' (q i : ℕ) : P :=
  (grp m).symm (⟨q % _, Nat.mod_lt _ (ngroups_pos m hn)⟩, ⟨i % _, Nat.mod_lt _ (gcd_pos' m hn)⟩)

/-- The cyclic shift inside every group. -/
noncomputable def shift : Equiv.Perm P :=
  (grp m).trans (((Equiv.refl _).prodCongr (finRotate _)).trans (grp m).symm)

lemma shift_mem' (q i : ℕ) : shift m (mem' m hn q i) = mem' m hn q (i + 1) := by
  simp only [shift, mem', Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.prodCongr_apply,
    Equiv.coe_refl, Prod.map_apply, id_eq]
  congr 2
  ext
  have hg := gcd_pos' m hn
  obtain ⟨g', hg'⟩ : ∃ g', Nat.gcd m (Fintype.card P) = g' + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hg).symm⟩
  have := AnonymousMutex.finRotate_pow_val (m := Nat.gcd m (Fintype.card P)) 1
    ⟨i % Nat.gcd m (Fintype.card P), Nat.mod_lt _ hg⟩
  simp only [pow_one] at this
  rw [this, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma shift_pow_mem' (q i : ℕ) : (shift m ^ i) (mem' m hn q 0) = mem' m hn q i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, shift_mem']

lemma mem'_surj (p : P) : ∃ q < Fintype.card P / Nat.gcd m (Fintype.card P),
    ∃ i < Nat.gcd m (Fintype.card P), mem' m hn q i = p := by
  refine ⟨((grp m) p).1, ((grp m) p).1.isLt, ((grp m) p).2, ((grp m) p).2.isLt, ?_⟩
  simp only [mem', Nat.mod_eq_of_lt ((grp m) p).1.isLt, Nat.mod_eq_of_lt ((grp m) p).2.isLt]
  exact (grp m).symm_apply_apply p

lemma mem'_add (q i : ℕ) : mem' m hn q (i + Nat.gcd m (Fintype.card P)) = mem' m hn q i := by
  simp [mem', Nat.add_mod_right]

lemma shift_pow_gcd : (shift m : Equiv.Perm P) ^ Nat.gcd m (Fintype.card P) = 1 := by
  ext p
  obtain ⟨q, -, i, -, rfl⟩ := mem'_surj m hn p
  calc (shift m ^ Nat.gcd m (Fintype.card P)) (mem' m hn q i)
      = (shift m ^ Nat.gcd m (Fintype.card P)) ((shift m ^ i) (mem' m hn q 0)) := by
        rw [shift_pow_mem']
    _ = (shift m ^ (i + Nat.gcd m (Fintype.card P))) (mem' m hn q 0) := by
        rw [add_comm i, pow_add, Equiv.Perm.mul_apply]
    _ = mem' m hn q i := by rw [shift_pow_mem', mem'_add]
    _ = (1 : Equiv.Perm P) (mem' m hn q i) := rfl

/-- The rotation set-up for `n = |P|` processes and `m` registers. -/
theorem exists_setup (hid : Function.Injective ids) : ∃ (e : ℕ → ℕ → P) (σ : Equiv.Perm Id) (sh : Equiv.Perm (Fin m))
    (a : ℕ → Id) (π : P → Equiv.Perm (Fin m)),
    Setup (Fintype.card P / Nat.gcd m (Fintype.card P)) (Nat.gcd m (Fintype.card P)) e σ sh a
      ids π := by
  classical
  have hgm : Nat.gcd m (Fintype.card P) ∣ m := Nat.gcd_dvd_left _ _
  have hdg : m / Nat.gcd m (Fintype.card P) * Nat.gcd m (Fintype.card P) = m :=
    Nat.div_mul_cancel hgm
  let ι : P ↪ Id := ⟨ids, hid⟩
  let σ : Equiv.Perm Id := Equiv.Perm.viaEmbeddingHom ι (shift m)
  have hσ : ∀ i p, (σ ^ i) (ids p) = ids ((shift m ^ i) p) := by
    intro i p
    rw [← map_pow]
    exact Equiv.Perm.viaEmbedding_apply _ ι p
  let sh : Equiv.Perm (Fin m) := (finRotate m) ^ (m / Nat.gcd m (Fintype.card P))
  refine ⟨mem' m hn, σ, sh, fun q => ids (mem' m hn q 0),
    fun p => sh ^ (((grp m) p).2 : ℕ), ?_⟩
  exact
    { σpow := by
        have : σ ^ Nat.gcd m (Fintype.card P) =
            Equiv.Perm.viaEmbeddingHom ι (shift m ^ Nat.gcd m (Fintype.card P)) :=
          (map_pow _ _ _).symm
        rw [this, shift_pow_gcd m hn, map_one]
      shpow := by
        ext x
        rw [← pow_mul, AnonymousMutex.finRotate_pow_val, hdg, Equiv.Perm.one_apply,
          Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]
      shinj := by
        intro i j y hi hj hij
        have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) y.isLt
        have hd0 : 0 < m / Nat.gcd m (Fintype.card P) := by
          rcases Nat.eq_zero_or_pos (m / Nat.gcd m (Fintype.card P)) with h0 | h0
          · rw [h0, zero_mul] at hdg; omega
          · exact h0
        have := congrArg Fin.val hij
        rw [← pow_mul, ← pow_mul, AnonymousMutex.finRotate_pow_val,
          AnonymousMutex.finRotate_pow_val] at this
        have hmod : Nat.ModEq m (m / Nat.gcd m (Fintype.card P) * i)
            (m / Nat.gcd m (Fintype.card P) * j) := Nat.ModEq.add_left_cancel' (y : ℕ) this
        have := hmod.eq_of_lt_of_lt
          (by have := Nat.mul_lt_mul_of_pos_left hi hd0; rwa [hdg] at this)
          (by have := Nat.mul_lt_mul_of_pos_left hj hd0; rwa [hdg] at this)
        exact Nat.eq_of_mul_eq_mul_left hd0 this
      einj := by
        intro q i q' j hq hi hq' hj h
        have := (grp m).symm.injective h
        simp only [Prod.mk.injEq, Fin.mk.injEq] at this
        rw [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt hq', Nat.mod_eq_of_lt hi,
          Nat.mod_eq_of_lt hj] at this
        exact this
      esurj := mem'_surj m hn
      hπ := by
        intro q hq i hi
        simp only [mem', Equiv.apply_symm_apply]
        rw [Nat.mod_eq_of_lt hi]
      hid := by
        intro q hq i hi
        rw [hσ, shift_pow_mem'] }

end Construction

section Theorem1

variable {Id V S : Type} {m : ℕ} [MulAction (Equiv.Perm Id) V] [MulAction (Equiv.Perm Id) S]
  {A : SymAlg (elecObj Bool) Id m V S} {P : Type} [Fintype P] [DecidableEq P]

/-- **The symmetry argument.** If a symmetric algorithm for the election object (bit outputs)
terminates for every choice of the anonymity permutations, there is an execution in which all
processes returned and the number of elected processes is a multiple of `gcd(m, n)`. -/
theorem exists_elected_mul (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids)
    (hT : ∀ π, Terminates (A.impl ids π)) :
    ∃ π α, (A.impl ids π).Valid α ∧ OneShot α ∧ AllReturned α ∧
      ∃ c, (elected α).card = Nat.gcd m (Fintype.card P) * c := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card P) with hn | hn
  · refine ⟨fun _ => 1, [], ⟨_, rfl⟩, fun p => by simp, fun p => ?_, 0, ?_⟩
    · exact absurd (Fintype.card_pos_iff.2 ⟨p⟩) (by omega)
    · rw [mul_zero, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro p; exact absurd (Fintype.card_pos_iff.2 ⟨p⟩) (by omega)
  set k := Fintype.card P / Nat.gcd m (Fintype.card P)
  set g := Nat.gcd m (Fintype.card P)
  obtain ⟨e, σ, sh, a, π, hS⟩ := exists_setup ids m hn hid
  have hg : 0 < g := gcd_pos' m hn
  obtain ⟨α, hval, h1, hret, hsym⟩ := exists_symmetric_outcome hS hA hg (hT π)
  refine ⟨π, α, hval, h1, hret, ((Finset.range k).filter
    (fun q => outputs α (e q 0) = some true)).card, ?_⟩
  have himg : elected α = (((Finset.range k).filter (fun q => outputs α (e q 0) = some true)) ×ˢ
      Finset.range g).image (fun x => e x.1 x.2) := by
    ext p
    simp only [elected, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_product, Finset.mem_range, Prod.exists]
    constructor
    · intro hp
      obtain ⟨q, hq, i, hi, rfl⟩ := hS.esurj p
      exact ⟨q, i, ⟨⟨hq, by rw [← hsym q hq i hi]; exact hp⟩, hi⟩, rfl⟩
    · rintro ⟨q, i, ⟨⟨hq, hq'⟩, hi⟩, rfl⟩
      rw [hsym q hq i hi]; exact hq'
  rw [himg, Finset.card_image_of_injOn, Finset.card_product, Finset.card_range, mul_comm]
  rintro ⟨q, i⟩ hx ⟨q', j⟩ hy hxy
  simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_range,
    Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio] at hx hy
  obtain ⟨h1, h2⟩ := hS.einj q i q' j hx.1.1 hx.2 hy.1.1 hy.2 hxy
  simp [h1, h2]

/-- **Theorem 1 (1)** of Godard–Imbs–Raynal–Taubenfeld (PODC 2020): there is no symmetric
d-election algorithm for `n` processes using `m` anonymous read-modify-write registers when
`gcd(m, n) > d`. Here the algorithm must terminate and elect between `1` and `d` processes for
every choice of the anonymity permutations; registers support arbitrary read-modify-write
operations and atomic snapshots, and the outputs are bits ("am I elected?"). -/
theorem theorem_1_1 (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids) (d : ℕ)
    (h : ∀ π, Terminates (A.impl ids π) ∧ DElection d (A.impl ids π)) :
    Nat.gcd m (Fintype.card P) ≤ d := by
  obtain ⟨π, α, hval, h1, hret, c, hc⟩ := exists_elected_mul hA ids hid (fun π => (h π).1)
  have := (h π).2 α hval h1 hret
  rw [hc] at this
  rcases Nat.eq_zero_or_pos c with h0 | h0
  · simp [h0] at this
  · exact le_trans (Nat.le_mul_of_pos_right _ h0) this.2

/-- **Theorem 1 (2)** of Godard–Imbs–Raynal–Taubenfeld (PODC 2020): there is no symmetric exact
d-election algorithm for `n` processes using `m` anonymous read-modify-write registers if
`gcd(m, n)` does not divide `d` (same model as `theorem_1_1`). -/
theorem theorem_1_2 (hA : A.Symmetric) (ids : P → Id) (hid : Function.Injective ids) (d : ℕ)
    (h : ∀ π, Terminates (A.impl ids π) ∧ ExactElection d (A.impl ids π)) :
    Nat.gcd m (Fintype.card P) ∣ d := by
  obtain ⟨π, α, hval, h1, hret, c, hc⟩ := exists_elected_mul hA ids hid (fun π => (h π).1)
  have := (h π).2 α hval h1 hret
  exact ⟨c, by rw [← this, hc]⟩

end Theorem1

end BezoutElection
