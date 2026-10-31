import Papers.PODC2017.MemoryAnonymousCoordination.MutexRegion
import Cslib.Foundations.Data.Nat.Descent
import Mathlib.Algebra.Ring.Parity

/-!
# Figure 1: Theorem 3.3 (deadlock-freedom)

Proof by contradiction. Fix a fair client-well-formed infinite execution in which some operation
is pending at time `t₀`, nobody is in the critical section at `t₀`, and no operation returns at or
after `t₀` (`Hyp`). Then:

* nobody is in the critical section, at `retLock`, in the exit section or at `retUnlock` after
  `t₀` (`Hyp.inReg`): every process is in the remainder section, active or passive;
* (`Hyp.weak_finite`) a weak collect ("give up") happens at most twice after `t₀`: after the
  first one the loser is passive, the other process cannot give up while it is passive
  (`DFInv.not_weak_of_pas`), so the loser leaves the wait loop before the next give-up; this starts
  a clean race (`GInv`), and the next give-up decides the race for good (`DInv`);
* (`Hyp.weak_infinite`) without give-ups the memory eventually stabilises with no `0` (the zeros
  only decrease, and a process reading a `0` in line 2 would write it); since `m` is odd, one
  process owns fewer than `⌈m/2⌉` registers and gives up at its next collect, or one process owns
  all registers and enters the critical section.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Mutex

open Cslib.SharedMemory Finset

variable {P : Type} [DecidableEq P] {m : ℕ} {π : P → Equiv.Perm (Fin m)}

lemma ATStep.tstep {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (h : ATStep m π x l M l' M') : TStep m π x l M l' M' := by
  cases h
  · exact TStep.scan0 ‹_› ‹_›
  · exact TStep.scan1 ‹_› ‹_›
  · exact TStep.scanW ‹_›
  · exact TStep.coll ‹_›
  · exact TStep.rst0 ‹_› ‹_›
  · exact TStep.rst1 ‹_› ‹_›
  · exact TStep.rstW ‹_›
  · exact TStep.wait ‹_›
  · exact TStep.exit ‹_›

lemma ATStep.not_ret {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (h : ATStep m π x l M l' M') : l ≠ .retLock ∧ l ≠ .retUnlock ∧ l ≠ .rem ∧ l ≠ .cs := by
  cases h <;> simp

lemma ATStep.exit_eq {x : P} {j : ℕ} {l' : Loc P} {M M' : Fin m → Option P}
    (h : ATStep m π x (.exit j) M l' M') : l' = nextExit m j := by
  generalize hl : (Loc.exit j : Loc P) = l at h
  cases h <;> cases hl; rfl

/-! ### Steps of an infinite execution -/

section Exec

variable (e : (I m π).InfExec)

lemma tstep_at (t : ℕ) :
    TStep m π (e.lbl t).proc ((e.cfg t).loc (e.lbl t).proc) (e.cfg t).mem
      ((e.cfg (t + 1)).loc (e.lbl t).proc) (e.cfg (t + 1)).mem :=
  (step_tstep' (e.step_eq t)).1

lemma loc_succ (t : ℕ) : (e.cfg (t + 1)).loc =
    Function.update (e.cfg t).loc (e.lbl t).proc ((e.cfg (t + 1)).loc (e.lbl t).proc) :=
  (step_tstep' (e.step_eq t)).2

lemma loc_succ_of_ne {t : ℕ} {y : P} (hy : (e.lbl t).proc ≠ y) :
    (e.cfg (t + 1)).loc y = (e.cfg t).loc y :=
  (Impl.step_other (e.step_eq t) hy).1

lemma atstep_of_tau {t : ℕ} {x : P} (h : e.lbl t = .tau x) :
    ATStep m π x ((e.cfg t).loc x) (e.cfg t).mem ((e.cfg (t + 1)).loc x) (e.cfg (t + 1)).mem := by
  have := e.step_eq t
  rw [h] at this
  exact step_tau_atstep this

/-- The process whose local state changes is the stepping one. -/
lemma proc_of_loc_ne {t : ℕ} {x : P} (h : (e.cfg (t + 1)).loc x ≠ (e.cfg t).loc x) :
    (e.lbl t).proc = x := by
  by_contra h'; exact h (loc_succ_of_ne e h')

end Exec

/-- The standing hypotheses of the proof of deadlock-freedom (by contradiction). -/
structure Hyp (e : (I m π).InfExec) (t₀ : ℕ) : Prop where
  two : ∀ a b c : P, a ≠ b → c = a ∨ c = b
  other : ∀ a : P, ∃ b, b ≠ a
  hm : 1 ≤ m
  fair : e.Fair
  wf : ∀ t, ClientWF (e.pre t)
  noret : ∀ t ≥ t₀, ∀ p r, e.lbl t ≠ .ret p r
  nocs : ∀ q, ¬ InCS (e.pre t₀) q

namespace Hyp

variable {e : (I m π).InfExec} {t₀ : ℕ} (H : Hyp e t₀)
include H

lemma dfinv (t : ℕ) : DFInv π (e.cfg t).loc (e.cfg t).mem := dfInv_of_run π H.two (e.run_pre t)

lemma reg (t : ℕ) (p : P) : regionOf (e.pre t) p = some (regOf ((e.cfg t).loc p)) ∧
    ((e.cfg t).pend p = none ↔ ((e.cfg t).loc p = .rem ∨ (e.cfg t).loc p = .cs)) ∧
    Bounded m ((e.cfg t).loc p) :=
  reg_inv H.hm (H.wf t) (e.run_pre t) p

/-- A pending process eventually takes an internal step, from its current local state. -/
lemma next_tau {t : ℕ} (ht : t₀ ≤ t) {x : P} (hp : (e.cfg t).pend x ≠ none) :
    ∃ s ≥ t, e.lbl s = .tau x ∧ (e.cfg s).loc x = (e.cfg t).loc x ∧
      (e.cfg s).pend x = (e.cfg t).pend x := by
  obtain ⟨s, hs, hpr, hst, hl, hpe⟩ := e.first_act H.fair hp
  refine ⟨s, hs, ?_, hl, hpe⟩
  cases hlb : e.lbl s with
  | inv p o => rw [hlb] at hst; exact hst.elim
  | ret p r => exact absurd hlb (H.noret s (by omega) p r)
  | tau p => rw [hlb] at hpr; simp only [Label.proc] at hpr; rw [hpr]

/-- After `t₀`, a pending operation stays pending. -/
lemma pend_succ {t : ℕ} (ht : t₀ ≤ t) {x : P} (hp : (e.cfg t).pend x ≠ none) :
    (e.cfg (t + 1)).pend x ≠ none := by
  intro h
  obtain ⟨r, hr⟩ := Impl.step_pend_none (e.step_eq t) hp h
  exact H.noret t ht x r hr

lemma pend_forever {t : ℕ} (ht : t₀ ≤ t) {x : P} (hp : (e.cfg t).pend x ≠ none) :
    ∀ s ≥ t, (e.cfg s).pend x ≠ none := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact hp
  | succ s hs ih => exact H.pend_succ (by omega) ih

/-- After `t₀`, nobody is in the critical section (client region). -/
lemma region_ne_cs : ∀ t ≥ t₀, ∀ q, regionOf (e.pre t) q ≠ some .cs := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact H.nocs
  | succ t ht ih =>
    intro q
    rw [e.pre_succ, regionOf_append_singleton]
    split_ifs with hq
    · cases hr : regionOf (e.pre t) q with
      | none => simp
      | some r =>
        simp only [Option.bind_some]
        cases hl : e.lbl t with
        | inv p o => cases r <;> cases o <;> simp [Region.next]
        | tau p => intro h; simp only [Region.next, Option.some.injEq] at h; subst h; exact ih q hr
        | ret p r' => exact absurd hl (H.noret t ht p r')
    · exact ih q

lemma loc_ne_cs {t : ℕ} (ht : t₀ ≤ t) (q : P) : (e.cfg t).loc q ≠ .cs := by
  intro h
  have := (H.reg t q).1
  rw [h] at this
  exact H.region_ne_cs t ht q this

lemma pend_of_not_rem {t : ℕ} (ht : t₀ ≤ t) {q : P} (h : (e.cfg t).loc q ≠ .rem) :
    (e.cfg t).pend q ≠ none := fun h' =>
  ((H.reg t q).2.1.1 h').elim h (H.loc_ne_cs ht q)

/-- After `t₀`, a pending process is not at `retLock` or `retUnlock`. -/
lemma not_ret_loc {t : ℕ} (ht : t₀ ≤ t) {q : P} (hp : (e.cfg t).pend q ≠ none) :
    (e.cfg t).loc q ≠ .retLock ∧ (e.cfg t).loc q ≠ .retUnlock := by
  obtain ⟨s, hs, hlb, hls, -⟩ := H.next_tau ht hp
  have := (atstep_of_tau e hlb).not_ret
  rw [hls] at this
  exact ⟨this.1, this.2.1⟩

/-- The exit section is not reached after `t₀`. -/
lemma not_exit : ∀ k, ∀ t ≥ t₀, ∀ q j, (e.cfg t).loc q = .exit j → m - j = k → False := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t ht q j hl hk
    have hb := (H.reg t q).2.2
    rw [hl] at hb; simp only [Bounded] at hb
    obtain ⟨s, hs, hlb, hls, hps⟩ := H.next_tau ht (H.pend_of_not_rem ht (by rw [hl]; simp))
    have hst := atstep_of_tau e hlb
    rw [hls, hl] at hst
    have h' := hst.exit_eq
    rcases nextExit_cases (m := m) (P := P) j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] at h'
    · exact ih (m - (j + 1)) (by omega) (s + 1) (by omega) q (j + 1) h' rfl
    · have hp := H.pend_of_not_rem (show t₀ ≤ s + 1 by omega) (by rw [h']; simp)
      exact (H.not_ret_loc (show t₀ ≤ s + 1 by omega) hp).2 h'

/-- After `t₀` every process is in the region (remainder, active or passive). -/
lemma inReg {t : ℕ} (ht : t₀ ≤ t) (q : P) : InReg ((e.cfg t).loc q) := by
  cases hl : (e.cfg t).loc q with
  | rem => exact Or.inl rfl
  | scan _ | scanW _ | coll _ => exact Or.inr (Or.inl trivial)
  | rst _ | rstW _ | wait _ _ => exact Or.inr (Or.inr trivial)
  | cs => exact (H.loc_ne_cs ht q hl).elim
  | retLock => exact ((H.not_ret_loc ht (H.pend_of_not_rem ht (by simp [hl]))).1 hl).elim
  | retUnlock => exact ((H.not_ret_loc ht (H.pend_of_not_rem ht (by simp [hl]))).2 hl).elim
  | exit j => exact (H.not_exit _ t ht q j hl rfl).elim

end Hyp

/-! ### At most two give-ups -/

variable (e : (I m π).InfExec)

/-- Some process gives up at time `t` (a weak collect: it becomes passive). -/
def Weak (t : ℕ) : Prop := ∃ x, ¬ Pas ((e.cfg t).loc x) ∧ Pas ((e.cfg (t + 1)).loc x)

/-- Some process leaves the wait loop at time `t`. -/
def LeaveW (t : ℕ) : Prop := ∃ x, Pas ((e.cfg t).loc x) ∧ Act ((e.cfg (t + 1)).loc x)

variable {e}

lemma TStep.pas_target {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') (hl : Pas l) : Pas l' ∨ Act l' := by
  cases hs with
  | @rst1 j _ hj _ =>
    left; rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> trivial
  | @rstW j _ hj =>
    left; rcases nextRst_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> trivial
  | @wait j z _ hj =>
    rcases afterWait_cases j z (M (π x ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1]
    · left; trivial
    · right; trivial
    · left; trivial
  | rst0 => left; trivial
  | idle => left; exact hl
  | _ => simp [Pas] at hl

lemma weak_data {t : ℕ} {x : P} (h1 : ¬ Pas ((e.cfg t).loc x)) (h2 : Pas ((e.cfg (t + 1)).loc x)) :
    (e.lbl t).proc = x ∧ ∃ vs, (e.cfg t).loc x = .coll vs ∧ (e.cfg (t + 1)).loc x = .rst 0 ∧
      TStep m π x (.coll vs) (e.cfg t).mem (.rst 0) (e.cfg (t + 1)).mem := by
  have hx : (e.lbl t).proc = x := proc_of_loc_ne e (fun h => h1 (h ▸ h2))
  refine ⟨hx, ?_⟩
  have hs := tstep_at e t
  rw [hx] at hs
  obtain ⟨vs, hv1, hv2⟩ := hs.weak_of_pas h1 h2
  refine ⟨vs, hv1, hv2, ?_⟩
  rw [hv1, hv2] at hs; exact hs

namespace Hyp

variable {t₀ : ℕ} (H : Hyp e t₀)
include H

/-- Nobody gives up while the other process is passive. -/
lemma not_weak_of_pas {t : ℕ} {p : P} (hp : Pas ((e.cfg t).loc p)) : ¬ Weak e t := by
  rintro ⟨x, h1, h2⟩
  obtain ⟨-, vs, hv1, -, hs⟩ := weak_data h1 h2
  have hxp : x ≠ p := fun h => h1 (h ▸ hp)
  obtain ⟨hj, -, hlast, hcnt⟩ := hs.weak_count
  have := (H.dfinv t).not_weak_of_pas hxp hp hv1 hj hlast
  omega

lemma pas_succ {t : ℕ} {p : P} (hp : Pas ((e.cfg t).loc p)) :
    Pas ((e.cfg (t + 1)).loc p) ∨ LeaveW e t := by
  by_cases hx : (e.lbl t).proc = p
  · have hs := tstep_at e t
    rw [hx] at hs
    rcases hs.pas_target hp with h | h
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, h⟩
  · left; rw [loc_succ_of_ne e hx]; exact hp

lemma G_of_leaveW {t : ℕ} (hL : LeaveW e t) : GInv π (e.cfg (t + 1)).loc (e.cfg (t + 1)).mem := by
  obtain ⟨x, h1, h2⟩ := hL
  have hx : (e.lbl t).proc = x := proc_of_loc_ne e (fun h => not_act_and_pas h2 (h ▸ h1))
  have hs := tstep_at e t
  rw [hx] at hs
  have := GInv.of_leaveW H.two H.hm (H.dfinv t) hs h1 h2
  have hls := loc_succ e t
  rw [hx] at hls
  rwa [← hls] at this

lemma G_succ {t : ℕ} (ht : t₀ ≤ t) (hG : GInv π (e.cfg t).loc (e.cfg t).mem) (hnw : ¬ Weak e t) :
    GInv π (e.cfg (t + 1)).loc (e.cfg (t + 1)).mem := by
  have hs := tstep_at e t
  have := GInv.step H.two H.hm hG (H.inReg ht _) hs (fun vs hv hr => hnw ⟨(e.lbl t).proc,
    by rw [hv]; simp [Pas], by rw [hr]; trivial⟩)
  rwa [← loc_succ] at this

lemma D_of_G_weak {t : ℕ} (hG : GInv π (e.cfg t).loc (e.cfg t).mem) (hw : Weak e t) :
    ∃ p q, p ≠ q ∧ DInv π q p (e.cfg (t + 1)).loc (e.cfg (t + 1)).mem := by
  obtain ⟨x, h1, h2⟩ := hw
  obtain ⟨hx, vs, hv1, hv2, hs⟩ := weak_data h1 h2
  obtain ⟨y, hy⟩ := H.other x
  have := hG.weak H.two (Ne.symm hy) hv1 hs
  have hls := loc_succ e t
  rw [hx] at hls
  rw [← hv2, ← hls] at this
  exact ⟨x, y, Ne.symm hy, this⟩

lemma D_succ {t : ℕ} (ht : t₀ ≤ t) {p q : P} (hpq : p ≠ q)
    (hD : DInv π q p (e.cfg t).loc (e.cfg t).mem) :
    DInv π q p (e.cfg (t + 1)).loc (e.cfg (t + 1)).mem := by
  have := hD.step H.two (H.dfinv t) hpq (H.inReg ht _) (tstep_at e t)
  rwa [← loc_succ] at this

lemma D_not_weak {t : ℕ} {p q : P} (hD : DInv π q p (e.cfg t).loc (e.cfg t).mem) :
    ¬ Weak e t :=
  H.not_weak_of_pas hD.1

/-- **At most two give-ups after `t₀`.** -/
theorem weak_finite : ∃ T, ∀ t ≥ T, ¬ Weak e t := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨w₁, hw₁, hW₁⟩ := hcon t₀
  have hex : ∃ w, w₁ < w ∧ Weak e w := by
    obtain ⟨w, hw, hW⟩ := hcon (w₁ + 1); exact ⟨w, by omega, hW⟩
  set w₂ := Nat.find hex with hw₂
  obtain ⟨hw₁₂, hW₂⟩ := Nat.find_spec hex
  have hmin : ∀ w, w₁ < w → w < w₂ → ¬ Weak e w := fun w h1 h2 hW =>
    Nat.find_min hex h2 ⟨h1, hW⟩
  -- the loser of `w₁` leaves the wait loop before `w₂`
  obtain ⟨p, hp1, hp2⟩ := hW₁
  have hleave : ∃ a, w₁ < a ∧ a < w₂ ∧ LeaveW e a := by
    by_contra hno
    push Not at hno
    have hpas : ∀ s, w₁ + 1 ≤ s → s ≤ w₂ → Pas ((e.cfg s).loc p) := by
      intro s hs1 hs2
      induction s, hs1 using Nat.le_induction with
      | base => exact hp2
      | succ s hs ih =>
        rcases H.pas_succ (ih (by omega)) with h | h
        · exact h
        · exact absurd h (hno s (by omega) (by omega))
    exact H.not_weak_of_pas (hpas w₂ (by omega) le_rfl) hW₂
  obtain ⟨a, ha1, ha2, hL⟩ := hleave
  -- clean race from `a + 1` to `w₂`
  have hG : ∀ s, a + 1 ≤ s → s ≤ w₂ → GInv π (e.cfg s).loc (e.cfg s).mem := by
    intro s hs1 hs2
    induction s, hs1 using Nat.le_induction with
    | base => exact H.G_of_leaveW hL
    | succ s hs ih =>
      exact H.G_succ (by omega) (ih (by omega)) (hmin s (by omega) (by omega))
  obtain ⟨p', q', hpq, hD⟩ := H.D_of_G_weak (hG w₂ (by omega) le_rfl) hW₂
  have hDall : ∀ s ≥ w₂ + 1, DInv π q' p' (e.cfg s).loc (e.cfg s).mem := by
    intro s hs
    induction s, hs using Nat.le_induction with
    | base => exact hD
    | succ s hs ih => exact H.D_succ (by omega) hpq ih
  obtain ⟨w₃, hw₃, hW₃⟩ := hcon (w₂ + 1)
  exact H.D_not_weak (hDall w₃ hw₃) hW₃

end Hyp

/-! ### Without give-ups the memory stabilises -/

/-- In lines 5 (read or write). -/
def IsR (l : Loc P) : Prop := ∃ j, l = .rst j ∨ l = .rstW j

lemma TStep.isR_target {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') (h : IsR l') : IsR l ∨ ∃ vs, l = .coll vs ∧ l' = .rst 0 := by
  cases hs with
  | rst0 => left; exact ⟨_, Or.inl rfl⟩
  | rst1 => left; exact ⟨_, Or.inl rfl⟩
  | rstW => left; exact ⟨_, Or.inr rfl⟩
  | idle => left; exact h
  | @coll vs _ hj =>
    right
    obtain ⟨j, hj'⟩ := h
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hj' ⊢ <;>
      rcases hj' with h2 | h2 <;> cases h2
    exact ⟨vs, rfl, rfl⟩
  | @scan1 j _ hj _ =>
    obtain ⟨j', hj'⟩ := h
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hj' <;>
      rcases hj' with h2 | h2 <;> cases h2
  | @scanW j _ hj =>
    obtain ⟨j', hj'⟩ := h
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hj' <;>
      rcases hj' with h2 | h2 <;> cases h2
  | @exit j _ hj =>
    obtain ⟨j', hj'⟩ := h
    rcases nextExit_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hj' <;>
      rcases hj' with h2 | h2 <;> cases h2
  | @wait j z _ hj =>
    obtain ⟨j', hj'⟩ := h
    rcases afterWait_cases j z (M (π x ⟨j, hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at hj' <;>
      rcases hj' with h2 | h2 <;> cases h2
  | _ => obtain ⟨j', hj'⟩ := h; rcases hj' with h2 | h2 <;> cases h2

lemma TStep.zero_back {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') (hR : ¬ IsR l) (hreg : InReg l) {r : Fin m}
    (h : M' r = none) : M r = none := by
  cases hs with
  | @scanW j _ hj =>
    have hr0 : r ≠ π x ⟨j, hj⟩ := fun h' => by rw [h'] at h; simp at h
    rwa [Function.update_of_ne hr0] at h
  | rstW => exact (hR ⟨_, Or.inr rfl⟩).elim
  | exit => simp [InReg, Act, Pas] at hreg
  | _ => exact h

lemma TStep.mem_eq_of {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') (hR : ¬ IsR l) (hreg : InReg l) (hW : ∀ j, l ≠ .scanW j) :
    M' = M := by
  cases hs with
  | scanW => exact (hW _ rfl).elim
  | rstW => exact (hR ⟨_, Or.inr rfl⟩).elim
  | exit => simp [InReg, Act, Pas] at hreg
  | _ => rfl

lemma TStep.scanW_target {x : P} {l : Loc P} {j : ℕ} {M M' : Fin m → Option P}
    (hs : TStep m π x l M (.scanW j) M') :
    l = .scanW j ∨ (l = .scan j ∧ ∃ hj : j < m, M (π x ⟨j, hj⟩) = none ∧ M' = M) := by
  generalize hl' : (Loc.scanW j : Loc P) = l' at hs
  cases hs with
  | scan0 hj h0 => cases hl'; exact Or.inr ⟨rfl, hj, h0, rfl⟩
  | idle => exact Or.inl rfl
  | @scan1 j' _ hj _ =>
    rcases nextScan_cases (m := m) (P := P) j' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hl' <;>
      cases hl'
  | @scanW j' _ hj =>
    rcases nextScan_cases (m := m) (P := P) j' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hl' <;>
      cases hl'
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1] at hl' <;> cases hl'
  | @rst1 j' _ hj _ =>
    rcases nextRst_cases (m := m) (P := P) j' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hl' <;>
      cases hl'
  | @rstW j' _ hj =>
    rcases nextRst_cases (m := m) (P := P) j' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hl' <;>
      cases hl'
  | @exit j' _ hj =>
    rcases nextExit_cases (m := m) (P := P) j' with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] at hl' <;>
      cases hl'
  | @wait j' z _ hj =>
    rcases afterWait_cases j' z (M (π x ⟨j', hj⟩)) with ⟨z', h1⟩ | h1 | h1 <;> rw [h1] at hl' <;>
      cases hl'
  | _ => cases hl'

lemma TStep.act_target {x : P} {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') (hl : Act l) : Act l' ∨ Pas l' ∨ l' = .retLock := by
  cases hs with
  | scan0 => left; trivial
  | @scan1 j _ hj _ =>
    left; rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> trivial
  | @scanW j _ hj =>
    left; rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> trivial
  | @coll vs _ hj =>
    rcases afterColl_cases (m := m) x (vs ++ [M (π x ⟨vs.length, hj⟩)]) with
      ⟨-, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1]
    · left; trivial
    · right; left; trivial
    · right; right; rfl
    · left; trivial
  | idle => left; exact hl
  | _ => simp [Act] at hl

/-- Distance (in internal steps) of an active process to the read of its local position `k`
in line 2. -/
def muZ (m k : ℕ) : Loc P → ℕ
  | .scan j => if j ≤ k then k - j else (m - j) + m + k
  | .coll vs => (m - vs.length) + k
  | _ => 0

/-- Distance of a waiting process to leaving the wait loop, if all registers hold `0`. -/
def muW (m : ℕ) : Loc P → ℕ
  | .wait j z => if z then m - j else 2 * m - j
  | _ => 0

/-- Distance of an active process to the start of a collect, if no register holds `0`. -/
def muC (m : ℕ) : Loc P → ℕ
  | .scan j => m - j
  | .coll vs => (m - vs.length) + m
  | _ => 0

/-- The registers holding `0` at time `t`. -/
def zeros (e : (I m π).InfExec) (t : ℕ) : Finset (Fin m) :=
  univ.filter (fun r => (e.cfg t).mem r = none)

namespace Hyp

variable {t₀ : ℕ} (H : Hyp e t₀)
include H

/-- **Progress by a local measure**: if every internal step of the pending process `x` (after
`t`) either establishes `Q` or decreases `μ`, then `Q` eventually holds. -/
lemma progress {x : P} {t : ℕ} (ht : t₀ ≤ t) (hp : (e.cfg t).pend x ≠ none)
    (Q : Loc P → Prop) (μ : Loc P → ℕ)
    (hstep : ∀ s ≥ t, ¬ Q ((e.cfg s).loc x) → e.lbl s = .tau x →
      Q ((e.cfg (s + 1)).loc x) ∨ μ ((e.cfg (s + 1)).loc x) < μ ((e.cfg s).loc x)) :
    ∃ s ≥ t, Q ((e.cfg s).loc x) := by
  induction hn : μ ((e.cfg t).loc x) using Nat.strong_induction_on generalizing t with
  | _ n ih =>
    by_cases hq : Q ((e.cfg t).loc x)
    · exact ⟨t, le_rfl, hq⟩
    obtain ⟨s, hs, hlb, hls, hps⟩ := H.next_tau ht hp
    rcases hstep s hs (by rw [hls]; exact hq) hlb with h | h
    · exact ⟨s + 1, by omega, h⟩
    · rw [hls, hn] at h
      obtain ⟨s', hs', hq'⟩ := ih _ h (t := s + 1) (by omega)
        (H.pend_succ (by omega) (by rw [hps]; exact hp)) (fun s'' hs'' => hstep s'' (by omega)) rfl
      exact ⟨s', by omega, hq'⟩

section NoWeak

variable [Fintype P] {T : ℕ} (hT : t₀ ≤ T) (hNW : ∀ t ≥ T, ¬ Weak e t)
include hT hNW

lemma noR_succ {t : ℕ} (ht : T ≤ t) {x : P} (h : ¬ IsR ((e.cfg t).loc x)) :
    ¬ IsR ((e.cfg (t + 1)).loc x) := by
  intro h'
  by_cases hx : (e.lbl t).proc = x
  · have hs := tstep_at e t
    rw [hx] at hs
    rcases hs.isR_target h' with h1 | ⟨vs, h1, h2⟩
    · exact h h1
    · exact hNW t ht ⟨x, by rw [h1]; simp [Pas], by rw [h2]; trivial⟩
  · rw [loc_succ_of_ne e hx] at h'; exact h h'

lemma leaveR {t : ℕ} (ht : T ≤ t) {x : P} (h : IsR ((e.cfg t).loc x)) :
    ∃ s ≥ t, ¬ IsR ((e.cfg s).loc x) := by
  have hp : (e.cfg t).pend x ≠ none := H.pend_of_not_rem (by omega) (by
    obtain ⟨j, hj | hj⟩ := h <;> rw [hj] <;> simp)
  refine H.progress (by omega) hp (fun l => ¬ IsR l)
    (fun l => match l with
      | .rst j => 2 * (m - j)
      | .rstW j => 2 * (m - j) - 1
      | _ => 0) ?_
  intro s hs hq hlb
  simp only [not_not] at hq
  have hst := atstep_of_tau e hlb
  have hb := (H.reg s x).2.2
  generalize hl' : (e.cfg (s + 1)).loc x = l' at hst ⊢
  generalize (e.cfg s).mem = M at hst
  generalize (e.cfg (s + 1)).mem = M' at hst
  obtain ⟨j, hj | hj⟩ := hq <;> rw [hj] at hst hb ⊢ <;> simp only [Bounded] at hb
  · generalize hl : (Loc.rst j : Loc P) = l at hst
    cases hst <;> cases hl
    · right; simp only; omega
    · rename_i hj' _
      rcases nextRst_cases (m := m) (P := P) j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
      · right; simp only; omega
      · left; rintro ⟨j', hj'' | hj''⟩ <;> cases hj''
  · generalize hl : (Loc.rstW j : Loc P) = l at hst
    cases hst <;> cases hl
    rcases nextRst_cases (m := m) (P := P) j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
    · right; simp only; omega
    · left; rintro ⟨j', hj'' | hj''⟩ <;> cases hj''

/-- Eventually nobody is in line 5. -/
lemma eventually_noR : ∃ T₁ ≥ T, ∀ t ≥ T₁, ∀ x, ¬ IsR ((e.cfg t).loc x) := by
  refine Nat.eventually_forall_of_imp_succ (P := fun t x => ¬ IsR ((e.cfg t).loc x)) T
    (fun t ht x h => H.noR_succ hT hNW ht h) (fun x => ?_)
  by_cases h : IsR ((e.cfg T).loc x)
  · exact H.leaveR hT hNW le_rfl h
  · exact ⟨T, le_rfl, h⟩

end NoWeak

section Zeros

variable {T₁ : ℕ} (hT₁ : t₀ ≤ T₁) (hR : ∀ t ≥ T₁, ∀ x, ¬ IsR ((e.cfg t).loc x))
include hT₁ hR

lemma zeros_succ {t : ℕ} (ht : T₁ ≤ t) : zeros e (t + 1) ⊆ zeros e t := by
  intro r hr
  simp only [zeros, mem_filter, mem_univ, true_and] at hr ⊢
  exact (tstep_at e t).zero_back (hR t ht _) (H.inReg (by omega) _) hr

/-- The zeros eventually stop changing. -/
lemma zeros_const : ∃ T₂ ≥ T₁, ∀ t ≥ T₂, zeros e t = zeros e T₂ := by
  obtain ⟨T₂, hT₂, hc⟩ := Nat.eventually_const_of_succ_le (f := fun t => #(zeros e t)) (N := T₁)
    fun t ht => card_le_card (H.zeros_succ hT₁ hR ht)
  refine ⟨T₂, hT₂, fun t ht => ?_⟩
  have hsub : zeros e t ⊆ zeros e T₂ := by
    induction t, ht using Nat.le_induction with
    | base => exact Subset.rfl
    | succ t ht ih => exact (H.zeros_succ hT₁ hR (by omega)).trans ih
  exact eq_of_subset_of_card_le hsub (hc t ht).ge

end Zeros

section ScanW

variable [Fintype P] {T₂ : ℕ} (hT₂ : t₀ ≤ T₂) (hZ : ∀ t ≥ T₂, zeros e t = zeros e T₂)
include hT₂ hZ

/-- After the zeros have stabilised, nobody starts a write of line 2. -/
lemma not_enter_scanW {t : ℕ} (ht : T₂ ≤ t) {x : P} (h : ∀ j, (e.cfg t).loc x ≠ .scanW j) :
    ∀ j, (e.cfg (t + 1)).loc x ≠ .scanW j := by
  intro j hj
  have hx : (e.lbl t).proc = x := proc_of_loc_ne e (fun h' => h j (h' ▸ hj))
  have hs := tstep_at e t
  rw [hx, hj] at hs
  rcases hs.scanW_target with h1 | ⟨h1, hj', h0, -⟩
  · exact h j h1
  have hr0 : π x ⟨j, hj'⟩ ∈ zeros e T₂ := by
    rw [← hZ t ht]; simp [zeros, h0]
  have hp := H.pend_of_not_rem (show t₀ ≤ t + 1 by omega) (by rw [hj]; simp)
  obtain ⟨s, hs', hlb, hls, -⟩ := H.next_tau (show t₀ ≤ t + 1 by omega) hp
  have hst := atstep_of_tau e hlb
  rw [hls, hj] at hst
  have hw : (e.cfg (s + 1)).mem (π x ⟨j, hj'⟩) = some x := by
    generalize hl' : (e.cfg (s + 1)).loc x = l' at hst
    generalize hM : (e.cfg s).mem = M at hst
    generalize hM' : (e.cfg (s + 1)).mem = M' at hst
    generalize hl : (Loc.scanW j : Loc P) = l at hst
    cases hst <;> cases hl
    simp
  rw [← hZ (s + 1) (by omega)] at hr0
  simp [zeros, hw] at hr0

lemma leave_scanW {t : ℕ} (ht : T₂ ≤ t) {x : P} :
    ∃ s ≥ t, ∀ j, (e.cfg s).loc x ≠ .scanW j := by
  by_cases h : ∃ j, (e.cfg t).loc x = .scanW j
  · obtain ⟨j₀, hj₀⟩ := h
    have hp := H.pend_of_not_rem (show t₀ ≤ t by omega) (by rw [hj₀]; simp)
    refine H.progress (by omega) hp (fun l => ∀ j, l ≠ .scanW j) (fun _ => 0) ?_
    intro s hs hq hlb
    left
    simp only [not_forall, not_not] at hq
    obtain ⟨j, hj⟩ := hq
    have hst := atstep_of_tau e hlb
    rw [hj] at hst
    generalize hl' : (e.cfg (s + 1)).loc x = l' at hst ⊢
    generalize (e.cfg s).mem = M at hst
    generalize (e.cfg (s + 1)).mem = M' at hst
    generalize hl : (Loc.scanW j : Loc P) = l at hst
    cases hst <;> cases hl
    intro j'
    rcases nextScan_cases (m := m) (P := P) j with ⟨-, h1⟩ | ⟨-, h1⟩ <;> rw [h1] <;> simp
  · push Not at h; exact ⟨t, le_rfl, h⟩

lemma eventually_noScanW : ∃ T₃ ≥ T₂, ∀ t ≥ T₃, ∀ x j, (e.cfg t).loc x ≠ .scanW j :=
  Nat.eventually_forall_of_imp_succ (P := fun t x => ∀ j, (e.cfg t).loc x ≠ .scanW j) T₂
    (fun _ ht _ h => H.not_enter_scanW hT₂ hZ ht h) (fun _ => H.leave_scanW hT₂ hZ le_rfl)

end ScanW

section Final

variable {T₃ : ℕ} (hT₃ : t₀ ≤ T₃) (hNW : ∀ t ≥ T₃, ¬ Weak e t)
  (hR : ∀ t ≥ T₃, ∀ x, ¬ IsR ((e.cfg t).loc x)) (hW : ∀ t ≥ T₃, ∀ x j, (e.cfg t).loc x ≠ .scanW j)
include hT₃ hNW hR hW

lemma mem_const : ∀ t ≥ T₃, (e.cfg t).mem = (e.cfg T₃).mem := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [← ih]
    exact (tstep_at e t).mem_eq_of (hR t ht _) (H.inReg (by omega) _) (hW t ht _)

lemma act_succ {t : ℕ} (ht : T₃ ≤ t) {x : P} (h : Act ((e.cfg t).loc x)) :
    Act ((e.cfg (t + 1)).loc x) := by
  by_cases hx : (e.lbl t).proc = x
  · have hs := tstep_at e t
    rw [hx] at hs
    rcases hs.act_target h with h1 | h1 | h1
    · exact h1
    · exact (hNW t ht ⟨x, fun h' => not_act_and_pas h h', h1⟩).elim
    · have := H.inReg (show t₀ ≤ t + 1 by omega) x
      rw [h1] at this; simp [InReg, Act, Pas] at this
  · rw [loc_succ_of_ne e hx]; exact h

lemma act_forever {t : ℕ} (ht : T₃ ≤ t) {x : P} (h : Act ((e.cfg t).loc x)) :
    ∀ s ≥ t, Act ((e.cfg s).loc x) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => exact h
  | succ s hs ih => exact H.act_succ hT₃ hNW hR hW (by omega) ih

lemma pend_of_act {t : ℕ} (ht : T₃ ≤ t) {x : P} (h : Act ((e.cfg t).loc x)) :
    (e.cfg t).pend x ≠ none :=
  H.pend_of_not_rem (by omega) (fun h' => by rw [h'] at h; exact h)

/-- The outcome of the last read of a collect after `T₃`. -/
lemma coll_outcome {s : ℕ} (hs : T₃ ≤ s) {x : P} {vs : List (Option P)}
    (hl : (e.cfg s).loc x = .coll vs) (hlb : e.lbl s = .tau x) :
    ∃ hj : vs.length < m, (e.cfg (s + 1)).loc x =
      afterColl m x (vs ++ [(e.cfg T₃).mem (π x ⟨vs.length, hj⟩)]) := by
  have hst := atstep_of_tau e hlb
  rw [hl, H.mem_const hT₃ hNW hR hW s hs] at hst
  generalize hl' : (e.cfg (s + 1)).loc x = l' at hst ⊢
  generalize (e.cfg T₃).mem = M at hst ⊢
  generalize (e.cfg (s + 1)).mem = M' at hst
  generalize hlc : (Loc.coll vs : Loc P) = lc at hst
  cases hst <;> cases hlc
  exact ⟨‹_›, rfl⟩

lemma not_rst0 {s : ℕ} (hs : T₃ ≤ s) {x : P} {vs : List (Option P)}
    (hl : (e.cfg s).loc x = .coll vs) (h : (e.cfg (s + 1)).loc x = .rst 0) : False :=
  hNW s hs ⟨x, by rw [hl]; simp [Pas], by rw [h]; trivial⟩

lemma not_retLock {s : ℕ} (hs : t₀ ≤ s) {x : P} (h : (e.cfg s).loc x = .retLock) : False := by
  have := H.inReg hs x; rw [h] at this; simp [InReg, Act, Pas] at this

/-- **Case of a `0` in the final memory**: nobody is active. -/
lemma no_act_of_zero {r : Fin m} (hr : (e.cfg T₃).mem r = none) :
    ∀ t ≥ T₃, ∀ x, ¬ Act ((e.cfg t).loc x) := by
  intro t ht x hA
  have hp := H.pend_of_act hT₃ hNW hR hW ht hA
  refine (H.progress (show t₀ ≤ t by omega) hp
    (fun l => (∃ j, l = .scanW j) ∨ ¬ Act l) (muZ m (posn π x r)) ?_).elim
    fun s ⟨hs, hq⟩ => ?_
  swap
  · rcases hq with ⟨j, hj⟩ | hq
    · exact hW s (by omega) x j hj
    · exact hq (H.act_forever hT₃ hNW hR hW ht hA s hs)
  intro s hs hq hlb
  simp only [not_or, not_exists, not_not] at hq
  obtain ⟨hq1, hq2⟩ := hq
  have hM := H.mem_const hT₃ hNW hR hW s (by omega)
  cases hls : (e.cfg s).loc x with
  | scan j =>
    have hst := atstep_of_tau e hlb
    rw [hls, hM] at hst
    have hk := posn_lt π x r
    generalize hl' : (e.cfg (s + 1)).loc x = l' at hst ⊢
    generalize hMM : (e.cfg T₃).mem = M at hst hr
    generalize (e.cfg (s + 1)).mem = M' at hst
    generalize hlc : (Loc.scan j : Loc P) = lc at hst
    cases hst <;> cases hlc
    · left; left; exact ⟨j, rfl⟩
    · rename_i hj h0
      right
      by_cases hjk : j = posn π x r
      · have hr' : π x ⟨j, hj⟩ = r := (eq_of_posn_eq π hj hjk.symm).symm
        rw [hr'] at h0; exact absurd hr h0
      rcases nextScan_cases (m := m) (P := P) j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;>
        simp only [muZ] <;> split_ifs <;> omega
  | coll vs =>
    obtain ⟨hj, h1⟩ := H.coll_outcome hT₃ hNW hR hW (by omega) hls hlb
    rcases afterColl_cases (m := m) x (vs ++ [(e.cfg T₃).mem (π x ⟨vs.length, hj⟩)]) with
      ⟨h2, h3⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩ | ⟨h2, -, h3⟩ <;> rw [h3] at h1
    · right; rw [h1]; simp only [muZ, List.length_append, List.length_cons, List.length_nil]
      simp at h2; omega
    · exact (H.not_rst0 hT₃ hNW hR hW (by omega) hls h1).elim
    · exact (H.not_retLock hT₃ hNW hR hW (by omega) h1).elim
    · right; rw [h1]; simp only [muZ, Nat.zero_le, ↓reduceIte]; omega
  | scanW j => exact absurd hls (hq1 j)
  | _ => rw [hls] at hq2; simp [Act] at hq2


/-- A non-active process after `T₃` waits or is in the remainder section, so owns nothing. -/
lemma own0_of_not_act {t : ℕ} (ht : T₃ ≤ t) {x : P} (h : ¬ Act ((e.cfg t).loc x)) :
    Own0 ((e.cfg t).loc x) := by
  have hreg := H.inReg (show t₀ ≤ t by omega) x
  have hr := hR t ht x
  cases hl : (e.cfg t).loc x <;> rw [hl] at hreg hr h <;> simp_all [InReg, Act, Pas, Own0, IsR]

lemma act_of_own {x : P} {r : Fin m} (h : (e.cfg T₃).mem r = some x) : Act ((e.cfg T₃).loc x) := by
  by_contra h'
  exact (H.dfinv T₃).own1 x (H.own0_of_not_act hT₃ hNW hR hW le_rfl h') r h

/-- **Case of a `0` in the final memory** (continued): contradiction. -/
lemma false_of_zero {p₀ : P} (hp₀ : (e.cfg T₃).pend p₀ ≠ none) {r : Fin m}
    (hr : (e.cfg T₃).mem r = none) : False := by
  have hna := H.no_act_of_zero hT₃ hNW hR hW hr
  have hz : ∀ r, (e.cfg T₃).mem r = none := by
    intro r'
    cases hr' : (e.cfg T₃).mem r' with
    | none => rfl
    | some c => exact ((H.dfinv T₃).own1 c (H.own0_of_not_act hT₃ hNW hR hW le_rfl
        (hna T₃ le_rfl c)) r' hr').elim
  obtain ⟨s, hs, hq⟩ := H.progress hT₃ hp₀ (fun l => Act l) (muW m) (by
    intro s hs hq hlb
    have hM := H.mem_const hT₃ hNW hR hW s (by omega)
    have hps := H.pend_forever hT₃ hp₀ s hs
    have hst := atstep_of_tau e hlb
    have hb := (H.reg s p₀).2.2
    have hown := H.own0_of_not_act hT₃ hNW hR hW (show T₃ ≤ s by omega) hq
    cases hls : (e.cfg s).loc p₀ with
    | wait j z =>
      rw [hls, hM] at hst
      rw [hls] at hb; simp only [Bounded] at hb
      generalize hl' : (e.cfg (s + 1)).loc p₀ = l' at hst ⊢
      generalize hMM : (e.cfg T₃).mem = M at hst hz
      generalize (e.cfg (s + 1)).mem = M' at hst
      generalize hlc : (Loc.wait j z : Loc P) = lc at hst
      cases hst <;> cases hlc
      rename_i hj
      rw [hz] at *
      cases z <;> simp only [afterWait, muW, Act, Option.isNone_none, Bool.and_true] <;>
        split_ifs <;> simp_all <;> omega
    | rem => exact absurd ((H.reg s p₀).2.1.2 (Or.inl hls)) hps
    | retUnlock => exact ((H.not_ret_loc (by omega) hps).2 hls).elim
    | _ => rw [hls] at hown; simp [Own0] at hown)
  exact hna s hs p₀ hq

/-- An active process eventually starts a fresh collect (no `0` in the final memory). -/
lemma reach_coll (hz : ∀ r, (e.cfg T₃).mem r ≠ none) {t : ℕ} (ht : T₃ ≤ t) {x : P}
    (hA : Act ((e.cfg t).loc x)) : ∃ s ≥ t, (e.cfg s).loc x = .coll [] := by
  have hp := H.pend_of_act hT₃ hNW hR hW ht hA
  refine (H.progress (show t₀ ≤ t by omega) hp (fun l => l = .coll [] ∨ ¬ Act l) (muC m) ?_).elim
    fun s ⟨hs, hq⟩ => ?_
  swap
  · rcases hq with hq | hq
    · exact ⟨s, hs, hq⟩
    · exact (hq (H.act_forever hT₃ hNW hR hW ht hA s hs)).elim
  intro s hs hq hlb
  simp only [not_or, not_not] at hq
  obtain ⟨hq1, hq2⟩ := hq
  have hM := H.mem_const hT₃ hNW hR hW s (by omega)
  cases hls : (e.cfg s).loc x with
  | scan j =>
    have hst := atstep_of_tau e hlb
    rw [hls, hM] at hst
    generalize hl' : (e.cfg (s + 1)).loc x = l' at hst ⊢
    generalize hMM : (e.cfg T₃).mem = M at hst hz
    generalize (e.cfg (s + 1)).mem = M' at hst
    generalize hlc : (Loc.scan j : Loc P) = lc at hst
    cases hst <;> cases hlc
    · exact absurd ‹_› (hz _)
    · rcases nextScan_cases (m := m) (P := P) j with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2]
      · right; simp only [muC]; omega
      · left; left; rfl
  | coll vs =>
    obtain ⟨hj, h1⟩ := H.coll_outcome hT₃ hNW hR hW (by omega) hls hlb
    have hvs : vs ≠ [] := fun h => hq1 (by rw [hls, h])
    rcases afterColl_cases (m := m) x (vs ++ [(e.cfg T₃).mem (π x ⟨vs.length, hj⟩)]) with
      ⟨h2, h3⟩ | ⟨-, -, h3⟩ | ⟨-, -, h3⟩ | ⟨h2, -, h3⟩ <;> rw [h3] at h1
    · right; rw [h1]; simp only [muC, List.length_append, List.length_cons, List.length_nil]
      simp at h2; omega
    · exact (H.not_rst0 hT₃ hNW hR hW (by omega) hls h1).elim
    · exact (H.not_retLock hT₃ hNW hR hW (by omega) h1).elim
    · right; rw [h1]; simp only [muC]; omega
  | scanW j => exact absurd hls (hW s (by omega) x j)
  | _ => rw [hls] at hq2; simp [Act] at hq2

/-- During a fresh collect the own values read are exactly the own registers read. -/
lemma collect_count {s₁ : ℕ} (hs₁ : T₃ ≤ s₁) {x : P} (h₁ : (e.cfg s₁).loc x = .coll []) :
    ∀ k, k < m → ∃ s ≥ s₁, ∃ vs : List (Option P), (e.cfg s).loc x = .coll vs ∧
      vs.length = k ∧
      vs.count (some x) = #(univ.filter (fun r => posn π x r < k ∧ (e.cfg T₃).mem r = some x)) := by
  intro k
  induction k with
  | zero => intro _; exact ⟨s₁, le_rfl, [], h₁, rfl, by simp⟩
  | succ k ih =>
    intro hk
    obtain ⟨s, hs, vs, hl, hlen, hc⟩ := ih (by omega)
    have hp := H.pend_of_act hT₃ hNW hR hW (show T₃ ≤ s by omega) (by rw [hl]; trivial)
    obtain ⟨s', hs', hlb, hls, -⟩ := H.next_tau (show t₀ ≤ s by omega) hp
    rw [hl] at hls
    obtain ⟨hj, h1⟩ := H.coll_outcome hT₃ hNW hR hW (by omega) hls hlb
    refine ⟨s' + 1, by omega, vs ++ [(e.cfg T₃).mem (π x ⟨vs.length, hj⟩)], ?_, by simp [hlen], ?_⟩
    · rw [h1]; unfold afterColl; simp [hlen]; omega
    · rw [count_append_one, hc]
      have := card_read_split (π := π) x vs hj (fun r => (e.cfg T₃).mem r = some x)
      generalize (if (e.cfg T₃).mem (π x ⟨vs.length, hj⟩) = some x then 1 else 0) = c at this ⊢
      rw [hlen] at this
      rw [this]

/-- A complete collect of an active process (no `0` in the final memory) counts its registers. -/
lemma full_collect (hm : 1 ≤ m) (hz : ∀ r, (e.cfg T₃).mem r ≠ none) {x : P}
    (hA : Act ((e.cfg T₃).loc x)) : ∃ s ≥ T₃, ∃ vs : List (Option P), m ≤ vs.length ∧
      vs.count (some x) = #(univ.filter (fun r => (e.cfg T₃).mem r = some x)) ∧
      ¬ Pas ((e.cfg s).loc x) ∧ (e.cfg (s + 1)).loc x = afterColl m x vs := by
  obtain ⟨s₁, hs₁, h₁⟩ := H.reach_coll hT₃ hNW hR hW hz le_rfl hA
  obtain ⟨s, hs, vs, hl, hlen, hc⟩ := H.collect_count hT₃ hNW hR hW hs₁ h₁ (m - 1) (by omega)
  have hp := H.pend_of_act hT₃ hNW hR hW (show T₃ ≤ s by omega) (by rw [hl]; trivial)
  obtain ⟨s', hs', hlb, hls, -⟩ := H.next_tau (show t₀ ≤ s by omega) hp
  rw [hl] at hls
  obtain ⟨hj, h1⟩ := H.coll_outcome hT₃ hNW hR hW (by omega) hls hlb
  refine ⟨s', by omega, _, by simp [hlen]; omega, ?_, by rw [hls]; simp [Pas], h1⟩
  rw [count_append_one, hc]
  have := card_read_split (π := π) x vs hj (fun r => (e.cfg T₃).mem r = some x)
  generalize (if (e.cfg T₃).mem (π x ⟨vs.length, hj⟩) = some x then 1 else 0) = c at this ⊢
  rw [hlen] at this
  rw [← this, show m - 1 + 1 = m by omega]
  congr 1
  ext r
  simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
  intro _; have := posn_lt π x r; omega

/-- **Case of no `0` in the final memory**: since `m` is odd, one process owns fewer than
`⌈m/2⌉` registers (and gives up at its next collect) or one process owns all registers (and
enters the critical section). -/
lemma false_of_full (hodd : Odd m) (hz : ∀ r, (e.cfg T₃).mem r ≠ none) {a b : P} (hab : a ≠ b) :
    False := by
  have hm : 1 ≤ m := by obtain ⟨k, hk⟩ := hodd; omega
  set o : P → ℕ := fun c => #(univ.filter (fun r => (e.cfg T₃).mem r = some c)) with ho
  have hcov : m ≤ o a + o b := card_le_of_cover (fun c => H.two a b c hab) hz
  have hdisj : o a + o b ≤ m := by
    have : Disjoint (univ.filter (fun r => (e.cfg T₃).mem r = some a))
        (univ.filter (fun r => (e.cfg T₃).mem r = some b)) := by
      rw [disjoint_filter]; intro r _ h1 h2; rw [h1] at h2; exact hab (Option.some.inj h2)
    have := card_union_of_disjoint this
    have h2 := card_le_univ (univ.filter (fun r => (e.cfg T₃).mem r = some a) ∪
      univ.filter (fun r => (e.cfg T₃).mem r = some b))
    simp only [Fintype.card_fin] at h2
    simp only [ho]; omega
  have hthr : 2 * thr m = m + 1 := by
    obtain ⟨k, hk⟩ := hodd; unfold thr; omega
  -- the complete collect of a process that owns a register
  have key : ∀ x, 0 < o x → (o x < thr m → False) ∧ (o x = m → False) := by
    intro x hx
    obtain ⟨r, hr⟩ := card_pos.1 hx
    simp only [mem_filter, mem_univ, true_and] at hr
    obtain ⟨s, hs, vs, hlen, hc, hnp, h1⟩ :=
      H.full_collect hT₃ hNW hR hW hm hz (H.act_of_own hT₃ hNW hR hW hr)
    have hc' : vs.count (some x) = o x := hc
    unfold afterColl at h1
    rw [ite_eq_right (by omega)] at h1
    refine ⟨fun hlt => ?_, fun heq => ?_⟩
    · rw [ite_eq_left (by omega)] at h1
      exact hNW s hs ⟨x, hnp, by rw [h1]; trivial⟩
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)] at h1
      exact H.not_retLock hT₃ hNW hR hW (by omega) h1
  rcases le_or_gt (thr m) (o a) with h | h
  · by_cases hm' : o a = m
    · exact (key a (by omega)).2 hm'
    · exact (key b (by omega)).1 (by omega)
  · by_cases hm' : o b = m
    · exact (key b (by omega)).2 hm'
    · exact (key a (by omega)).1 h

end Final

/-- **Without give-ups there is no deadlock**: give-ups happen infinitely often. -/
theorem weak_infinite [Fintype P] (hodd : Odd m) {p₀ : P} (hp₀ : (e.cfg t₀).pend p₀ ≠ none) :
    ∀ T, ∃ t ≥ T, Weak e t := by
  by_contra hcon
  push Not at hcon
  obtain ⟨T, hT⟩ := hcon
  have hNW : ∀ t ≥ max T t₀, ¬ Weak e t := fun t ht => hT t (by omega)
  obtain ⟨T₁, hT₁, hR⟩ := H.eventually_noR (le_max_right T t₀) hNW
  obtain ⟨T₂, hT₂, hZ⟩ := H.zeros_const (show t₀ ≤ T₁ by omega) hR
  obtain ⟨T₃, hT₃, hW⟩ := H.eventually_noScanW (show t₀ ≤ T₂ by omega) hZ
  have hR3 : ∀ t ≥ T₃, ∀ x, ¬ IsR ((e.cfg t).loc x) := fun t ht => hR t (by omega)
  have hNW3 : ∀ t ≥ T₃, ¬ Weak e t := fun t ht => hNW t (by omega)
  have hp := H.pend_forever le_rfl hp₀ T₃ (by omega)
  by_cases hz : ∃ r, (e.cfg T₃).mem r = none
  · obtain ⟨r, hr⟩ := hz
    exact H.false_of_zero (show t₀ ≤ T₃ by omega) hNW3 hR3 hW hp hr
  · push Not at hz
    obtain ⟨y, hy⟩ := H.other p₀
    exact H.false_of_full (show t₀ ≤ T₃ by omega) hNW3 hR3 hW hodd hz hy

end Hyp

/-- **Theorem 3.3** of Taubenfeld (PODC 2017): the algorithm of Figure 1 is deadlock-free, for two
processes, every odd number `m` of registers and every adversarial numbering `π` of the registers
(memory anonymity). (The paper assumes `m ≥ 3` odd.) -/
theorem theorem_3_3 [Fintype P] (hP : Fintype.card P = 2) (hodd : Odd m)
    (π : P → Equiv.Perm (Fin m)) : ((alg m).unnamed π).DeadlockFree := by
  intro e hwf hfair t₀ ⟨p₀, hp₀⟩ hnocs
  by_contra hno
  push Not at hno
  have H : Hyp e t₀ :=
    { two := two_procs hP.le
      other := fun a => Fintype.exists_ne_of_one_lt_card (by omega) a
      hm := by obtain ⟨k, hk⟩ := hodd; omega
      fair := hfair
      wf := hwf
      noret := hno
      nocs := hnocs }
  obtain ⟨T, hT⟩ := H.weak_finite
  obtain ⟨t, ht, hw⟩ := H.weak_infinite hodd hp₀ T
  exact hT t ht hw

end Podc.MemoryAnonymousCoordination.Mutex
