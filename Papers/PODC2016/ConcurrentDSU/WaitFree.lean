import Papers.PODC2016.ConcurrentDSU.Inv
import Papers.PODC2016.ConcurrentDSU.Lin
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# Wait-freedom (Lemma 3.3)

Every operation finishes within a bounded number of its own steps, whatever the other processes
do. The proof uses a potential `Ψ p C = bnd · mpot C.mem + Φ (C.loc p) C.mem` where

* `mpot` (`Forest.lean`) decreases with every change of the memory: every successful `Cas`
  moves one parent pointer to a node with a larger id, so there are only finitely many memory
  changes overall;
* `Φ < bnd` is a potential of the local state of `p` *in a fixed memory*: every step of `p` that
  does not change the memory decreases it.

The local potential `Φ` combines, lexicographically, the "positions" of `u` and `v` (twice the
number of larger ids, plus one for a root, see `qv`), the phase of the loop body and the
progress of the running `Find`. Positions are measured at the *roots* of `u` and `v` while a
`Find` is running, and at `u`, `v` themselves at the checks of lines 7–10: a failing `Cas` /
failing root test (`u` is not a root) then strictly decreases the position, which pays for the
next iteration of the loop.

* `Impl.waitFree_of_cfgPotential` (library, `Cslib/Computability/Distributed/SharedMemory/Potential.lean`): a
  configuration potential that never increases while `p` is pending and decreases with every
  step of `p` gives wait-freedom.
* `waitFree` — Lemma 3.3 for all versions of `Find`.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentDSU

open Cslib.SharedMemory

variable {E : Type} [Fintype E] [DecidableEq E] {P : Type} [DecidableEq P]
variable (K : FindKind) (key : E → ℕ)

/-- Position of a node: twice the number of larger ids, plus one if it is a root. -/
def qv (m : E → E) (x : E) : ℕ := 2 * hgt key x + if m x = x then 1 else 0

/-- The current node of a `Find`. -/
def cnode : FS E → E
  | .tst u => u
  | .adv u => u
  | .rdP u _ => u
  | .rdG u _ _ => u
  | .cas u _ _ _ => u

/-- Position part of the potential of a `Find`. -/
def fpos (m : E → E) : FS E → ℕ
  | .tst u => qv key m u
  | .adv u => 2 * hgt key u
  | .rdP u _ => qv key m u
  | .rdG u v _ => 2 * hgt key u + if v = u then 1 else 0
  | .cas u v _ _ => 2 * hgt key u + if v = u then 1 else 0

/-- Program-counter part of the potential of a `Find`. -/
def fpc : FS E → ℕ
  | .tst _ => 1
  | .adv _ => 0
  | .rdP _ i => 3 * (K.tries - 1 - i) + 2
  | .rdG _ _ i => 3 * (K.tries - 1 - i) + 1
  | .cas _ _ _ i => 3 * (K.tries - 1 - i)

/-- Potential of a running `Find`. -/
def fpot (m : E → E) (fs : FS E) : ℕ := 3 * K.tries * fpos key m fs + fpc K fs

/-- Bound on `fpot`. -/
def fB : ℕ := 3 * K.tries * (2 * Fintype.card E + 2)

/-- Weight of the positions in the local potential. -/
def wB : ℕ := 3 * fB (E := E) K + 3

/-- The local potential of a process (in a fixed memory). -/
def Φ (m : E → E) : Loc E → ℕ
  | .idle => 0
  | .done _ => 0
  | .fu _ fs v => wB (E := E) K * (qv key m (rootOf m (cnode fs)) + qv key m (rootOf m v)) +
      2 * fB (E := E) K + fpot K key m fs + 2
  | .fv _ u fs => wB (E := E) K * (qv key m u + qv key m (rootOf m (cnode fs))) +
      fB (E := E) K + fpot K key m fs + 1
  | .chk u v => wB (E := E) K * (qv key m u + qv key m v)
  | .lnk u v => wB (E := E) K * (qv key m u + qv key m v)

/-- Bound on `Φ`. -/
def bnd : ℕ := wB (E := E) K * (4 * Fintype.card E + 3)

variable {K key}

lemma qv_le (m : E → E) (x : E) : qv key m x ≤ 2 * Fintype.card E + 1 := by
  have := hgt_le_card (key := key) x
  unfold qv; split_ifs <;> omega

lemma qv_rootOf {m : E → E} (hg : Good key m) (x : E) :
    qv key m (rootOf m x) = 2 * hgt key (rootOf m x) + 1 := by
  simp [qv, rootOf_fixed hg x]

lemma qv_rootOf_le {m : E → E} (hg : Good key m) (x : E) : qv key m (rootOf m x) ≤ qv key m x := by
  by_cases hx : m x = x
  · rw [rootOf_of_fixed hx]
  · have h1 := hgt_lt (key_lt_rootOf hg hx)
    rw [qv_rootOf hg]; simp only [qv, hx, ite_false]; omega

lemma qv_rootOf_lt {m : E → E} (hg : Good key m) {x : E} (hx : m x ≠ x) :
    qv key m (rootOf m x) + 1 ≤ qv key m x := by
  have h1 := hgt_lt (key_lt_rootOf hg hx)
  rw [qv_rootOf hg]; simp only [qv, hx, ite_false]; omega

lemma fpot_lt (m : E → E) (fs : FS E) : fpot K key m fs < fB (E := E) K := by
  have hT := K.tries_pos
  have hpos : fpos key m fs ≤ 2 * Fintype.card E + 1 := by
    cases fs with
    | tst u => exact qv_le _ _
    | adv u => simp only [fpos]; have := hgt_le_card (key := key) u; omega
    | rdP u i => exact qv_le _ _
    | rdG u v i => simp only [fpos]; have := hgt_le_card (key := key) u; split_ifs <;> omega
    | cas u v w i => simp only [fpos]; have := hgt_le_card (key := key) u; split_ifs <;> omega
  have hpc : fpc K fs < 3 * K.tries := by
    cases fs <;> simp only [fpc] <;> omega
  unfold fpot fB
  calc 3 * K.tries * fpos key m fs + fpc K fs
      < 3 * K.tries * fpos key m fs + 3 * K.tries := by omega
    _ = 3 * K.tries * (fpos key m fs + 1) := by ring
    _ ≤ 3 * K.tries * (2 * Fintype.card E + 2) := by
        apply Nat.mul_le_mul_left; omega

lemma Φ_lt (m : E → E) (l : Loc E) : Φ K key m l < bnd (E := E) K := by
  have h1 := fpot_lt (K := K) (key := key) m
  have hq := qv_le (key := key) m
  have hW : wB (E := E) K = 3 * fB (E := E) K + 3 := rfl
  unfold bnd
  cases l with
  | idle => simp only [Φ]; rw [hW]; positivity
  | done r => simp only [Φ]; rw [hW]; positivity
  | fu b fs v =>
    simp only [Φ]
    have := h1 fs; have := hq (rootOf m (cnode fs)); have := hq (rootOf m v)
    nlinarith
  | fv b u fs =>
    simp only [Φ]
    have := h1 fs; have := hq u; have := hq (rootOf m (cnode fs))
    nlinarith
  | chk u v =>
    simp only [Φ]; have := hq u; have := hq v
    nlinarith
  | lnk u v =>
    simp only [Φ]; have := hq u; have := hq v
    nlinarith

lemma FInv.same_cnode {m : E → E} {s : E} {fs : FS E} (hf : FInv K key m s fs) :
    same m (cnode fs) s := by
  cases fs with
  | tst u => exact hf
  | adv u => exact hf.1
  | rdP u i => exact hf.2
  | rdG u v i => exact hf.2.1
  | cas u v w i => exact hf.2.1

/-- One step of a `Find` that does not change the memory decreases its potential and stays in
the same tree. -/
lemma find_dec {m : E → E} (hg : Good key m) {s : E} {fs fs' : FS E} (hf : FInv K key m s fs)
    (h : (fRes K fs m).1 = .inl fs') (hm : (fRes K fs m).2 = m) :
    fpot K key m fs' < fpot K key m fs ∧ rootOf m (cnode fs') = rootOf m (cnode fs) := by
  have hT := K.tries_pos
  cases fs with
  | tst u =>
    simp only [fRes, FS.next] at h
    split_ifs at h with hu
    cases h
    refine ⟨?_, rfl⟩
    simp only [fpot, fpos, fpc, qv, hu, ite_false, Nat.add_zero]; omega
  | adv u =>
    simp only [fRes, FS.next, Sum.inl.injEq] at h
    subst h
    have hk := hgt_lt ((hg u).resolve_left hf.2)
    refine ⟨?_, rootOf_apply hg u⟩
    have hq : qv key m (m u) ≤ 2 * hgt key (m u) + 1 := by unfold qv; split_ifs <;> omega
    simp only [fpot, fpos, fpc]
    have : 3 * K.tries * qv key m (m u) + 1 < 3 * K.tries * (2 * hgt key u) := by
      calc 3 * K.tries * qv key m (m u) + 1 < 3 * K.tries * qv key m (m u) + 3 * K.tries := by
            omega
        _ = 3 * K.tries * (qv key m (m u) + 1) := by ring
        _ ≤ 3 * K.tries * (2 * hgt key u) := by apply Nat.mul_le_mul_left; omega
    omega
  | rdP u i =>
    simp only [fRes, FS.next, Sum.inl.injEq] at h
    subst h
    refine ⟨?_, rfl⟩
    have : (2 * hgt key u + if m u = u then 1 else 0) = qv key m u := rfl
    simp only [fpot, fpos, fpc, this]; omega
  | rdG u v i =>
    simp only [fRes, FS.next] at h
    split_ifs at h with hv
    cases h
    refine ⟨?_, rfl⟩
    simp only [fpot, fpos, fpc]; omega
  | cas u v w i =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    simp only [fRes, FS.next] at h
    split_ifs at h with hi <;> cases h
    · refine ⟨?_, rfl⟩
      have hq : qv key m u ≤ 2 * hgt key u + if v = u then 1 else 0 := by
        by_cases hvu : v = u
        · simp only [hvu, ite_true, qv]; split_ifs <;> omega
        · simp only [qv, hvu, ite_false, h7 hvu]; omega
      simp only [fpot, fpos, fpc]
      have : 3 * K.tries * qv key m u ≤ 3 * K.tries * (2 * hgt key u + if v = u then 1 else 0) :=
        Nat.mul_le_mul_left _ hq
      omega
    · refine ⟨?_, h3⟩
      have hqv : qv key m v = 2 * hgt key v := by simp [qv, h8]
      have hpos : 2 * hgt key v + 1 ≤ 2 * hgt key u + if v = u then 1 else 0 := by
        by_cases hvu : v = u
        · subst hvu; simp
        · have := hgt_lt (h6.resolve_left hvu); simp only [hvu, ite_false]; omega
      simp only [fpot, fpos, fpc, hqv]
      have : 3 * K.tries * (2 * hgt key v + 1) ≤
          3 * K.tries * (2 * hgt key u + if v = u then 1 else 0) := Nat.mul_le_mul_left _ hpos
      have : 3 * K.tries * (2 * hgt key v + 1) = 3 * K.tries * (2 * hgt key v) + 3 * K.tries := by
        ring
      omega

/-- The root returned by a `Find` is the root of its current node. -/
lemma find_found {m : E → E} (hg : Good key m) {s : E} {fs : FS E} {r : E}
    (hf : FInv K key m s fs) (h : (fRes K fs m).1 = .inr r) : r = rootOf m (cnode fs) := by
  have hs := (fRes_spec hg hf).2
  rw [h] at hs
  obtain ⟨-, hr, hrs⟩ := hs
  have := same_trans hrs (same_symm hf.same_cnode)
  unfold same at this
  rw [rootOf_of_fixed hr] at this
  exact this

lemma cnode_start (v : E) : cnode (FS.start K v) = v := by cases K <;> rfl

/-- **A step of a process that does not change the memory decreases its local potential.** -/
theorem Φ_dec {m : E → E} (hg : Good key m) {o : DSUOp E} {l l' : Loc E}
    (hl : LocInv K key m (some o) l) (h : tauRes K key l m = some (l', m)) :
    Φ K key m l' < Φ K key m l := by
  have hW : wB (E := E) K = 3 * fB (E := E) K + 3 := rfl
  cases l with
  | idle => exact hl.elim
  | done r => simp [tauRes, act] at h
  | fu b fs v =>
    obtain ⟨hb, hf, hv⟩ := hl
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hm⟩ := h
    cases hc : (fRes K fs m).1 with
    | inl fs' =>
      obtain ⟨h1, h2⟩ := find_dec hg hf hc hm
      simp only [contU, Φ, h2]; omega
    | inr r =>
      have hr := find_found hg hf hc
      have := fpot_lt (K := K) (key := key) m (FS.start K v)
      simp only [contU, Φ, cnode_start]
      rw [hr]
      omega
  | fv b u fs =>
    obtain ⟨hb, hu, hf⟩ := hl
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hm⟩ := h
    cases hc : (fRes K fs m).1 with
    | inl fs' =>
      obtain ⟨h1, h2⟩ := find_dec hg hf hc hm
      simp only [contV, Φ, h2]; omega
    | inr r =>
      have hr := find_found hg hf hc
      simp only [contV]
      split_ifs
      · simp only [Φ]; omega
      · simp only [Φ, hr]; omega
      · simp only [Φ, hr]; omega
  | chk u v =>
    simp only [tauRes, act, ptr_read, Function.update_eq_self, val, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    by_cases hu : m u = u
    · simp only [hu, ite_true, Φ]
      have : 1 ≤ qv key m u := by simp [qv, hu]
      have : 0 < wB (E := E) K := by rw [hW]; omega
      nlinarith
    · simp only [hu, ite_false, Φ, cnode_start]
      have h1 := qv_rootOf_lt hg hu
      have h2 := qv_rootOf_le hg v
      have h3 := fpot_lt (K := K) (key := key) m (FS.start K u)
      have : wB (E := E) K * (qv key m (rootOf m u) + qv key m (rootOf m v)) + wB (E := E) K ≤
          wB (E := E) K * (qv key m u + qv key m v) := by
        rw [← Nat.mul_succ]; apply Nat.mul_le_mul_left; omega
      omega
  | lnk u v =>
    obtain ⟨hb, hu, hv, huv⟩ := hl
    by_cases hlt : key u < key v
    · simp only [tauRes, act, hlt, ite_true, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hm⟩ := h
      by_cases hr : m u = u
      · exfalso
        simp only [hr, ite_true] at hm
        have := congrFun hm u
        simp only [Function.update_self] at this
        rw [hr] at this; exact huv this.symm
      · simp only [hr, ite_false, Sum.inr.injEq, Bool.false_eq_true, Φ, cnode_start]
        have h1 := qv_rootOf_lt hg hr
        have h2 := qv_rootOf_le hg v
        have h3 := fpot_lt (K := K) (key := key) m (FS.start K u)
        have : wB (E := E) K * (qv key m (rootOf m u) + qv key m (rootOf m v)) + wB (E := E) K ≤
            wB (E := E) K * (qv key m u + qv key m v) := by
          rw [← Nat.mul_succ]; apply Nat.mul_le_mul_left; omega
        omega
    · simp only [tauRes, act, hlt, ite_false, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, hm⟩ := h
      by_cases hr : m v = v
      · exfalso
        simp only [hr, ite_true] at hm
        have := congrFun hm v
        simp only [Function.update_self] at this
        rw [hr] at this; exact huv this
      · simp only [hr, ite_false, Sum.inr.injEq, Bool.false_eq_true, Φ, cnode_start]
        have h1 := qv_rootOf_le hg u
        have h2 := qv_rootOf_lt hg hr
        have h3 := fpot_lt (K := K) (key := key) m (FS.start K u)
        have : wB (E := E) K * (qv key m (rootOf m u) + qv key m (rootOf m v)) + wB (E := E) K ≤
            wB (E := E) K * (qv key m u + qv key m v) := by
          rw [← Nat.mul_succ]; apply Nat.mul_le_mul_left; omega
        omega

variable (K key) in
/-- The potential of process `p` in a configuration. -/
def Ψ (p : P) (C : Config (dsu E) (Ptr E) P (Loc E)) : ℕ :=
  bnd (E := E) K * mpot key C.mem + Φ K key C.mem (C.loc p)

/-- **Lemma 3.3 (Wait-freedom).** With any version of `Find` and injective ids, every operation
finishes within finitely many of its own steps. -/
theorem waitFree (hkey : Function.Injective key) : (dsuImpl K key P).WaitFree := by
  refine Impl.waitFree_of_cfgPotential _ (LInv K key) linv_init
    (fun C C' ℓ hI h => (linv_step hkey hI h).1) (Ψ K key) ?_
  intro p C C' ℓ hI hp h
  have hleg := (linv_step hkey hI h).2
  have hΦ := Φ_lt (K := K) (key := key) C'.mem (C'.loc p)
  by_cases hm : C'.mem = C.mem
  · -- the memory did not change
    by_cases hℓ : ℓ = .tau p
    · subst hℓ
      obtain ⟨-, hres, -, -⟩ := step_tau_tauRes h
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
      have hl := hI.loc p
      rw [ho] at hl
      rw [hm] at hres
      have := Φ_dec hI.good hl hres
      simp only [Ψ, hm]
      exact ⟨by omega, fun _ => by omega⟩
    · have hle : Φ K key C.mem (C'.loc p) ≤ Φ K key C.mem (C.loc p) := by
        by_cases hq : ℓ.proc = p
        · cases ℓ with
          | inv q o =>
            simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv h).1 hp
          | ret q r =>
            simp only [Label.proc] at hq; subst hq
            obtain ⟨h0, -, -, l, hact, hl⟩ := Impl.step_ret h
            have hact' : act K key (C.loc q) = .ret r l := hact
            rcases act_ret_cases hact' with h1 | h1
            · rw [h1] at hact'; simp only [act] at hact'; cases hact'
              rw [hl, Function.update_self]; simp [Φ]
            · have := hI.loc q
              obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
              rw [ho, h1] at this; exact this.elim
          | tau q => simp only [Label.proc] at hq; exact absurd (by rw [hq]) hℓ
        · rw [(Impl.step_other h hq).1]
      simp only [Ψ, hm]
      exact ⟨by omega, fun h' => absurd h' hℓ⟩
  · -- the memory changed: `mpot` decreased
    have hlt := mpot_lt hleg hm
    have hΦ' := Φ_lt (K := K) (key := key) C.mem (C.loc p)
    have : bnd (E := E) K * mpot key C'.mem + bnd (E := E) K ≤ bnd (E := E) K * mpot key C.mem := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
    simp only [Ψ]
    exact ⟨by omega, fun _ => by omega⟩

end Podc.ConcurrentDSU
