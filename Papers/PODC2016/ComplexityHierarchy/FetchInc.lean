import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Valency
import Cslib.Foundations.Data.Nat.Descent

/-!
# One read/write/fetch-and-increment location is not enough (Theorem 5.1 of EGSZ'16)

A single memory location supporting `read()`, `write(x)` and `fetch-and-increment()` (values in
`ℤ`, arbitrary initial value) cannot be used to solve obstruction-free binary consensus for
`n ≥ 2` processes (`theorem_5_1`).

Proof (as in the paper): let `p ≠ q`. Run `p` alone, with input `x`, until it is about to write
(or has decided); during this write-free prefix the location only grows by one per
`fetch-and-increment`. Choose `x` such that the value `M x` reached with input `x` is at most the
value `M (!x)` reached with input `!x`. Starting from the configuration where *everybody* has
input `!x`, stop `p` when the location holds exactly `M x` (discrete intermediate value theorem);
there `q` must decide `!x` (weak validity), and `q` cannot distinguish this configuration from the
one reached by `p`'s write-free prefix with input `x`. If `p` has already decided `x` there, this
contradicts agreement; otherwise `p` is poised to write, and its write hides `q`'s whole solo run,
after which `p` still decides `x`.

The paper's "without loss of generality, at least as many fetch-and-increments in `β'` as in
`α'`" is made explicit by comparing the final values `M x` (which is the same thing).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.ComplexityHierarchy

open Cslib.SharedMemory Impl

/-- Operations of a location supporting `read`, `write(x)` and `fetch-and-increment`. -/
inductive FOp where
  /-- `read()`. -/
  | read
  /-- `write(x)`. -/
  | write (x : ℤ)
  /-- `fetch-and-increment()`. -/
  | fai

/-- A location supporting `read`, `write` and `fetch-and-increment` (write returns `0`, i.e.
nothing). -/
abbrev faiLoc : ObjSpec where
  State := ℤ
  Op := FOp
  Resp := ℤ
  init := 0
  δ s o := match o with
    | .read => (s, s)
    | .write x => (x, 0)
    | .fai => (s + 1, s)

/-- Discrete intermediate value theorem. -/
lemma exists_eq_of_step (g : ℕ → ℤ) (t : ℤ) :
    ∀ a, (∀ j < a, g (j + 1) = g j ∨ g (j + 1) = g j + 1) → g 0 ≤ t → t ≤ g a →
      ∃ j ≤ a, g j = t := by
  intro a hs h0 ha
  rcases ha.lt_or_eq with ha | ha
  · obtain ⟨j, -, hj, hgj, -⟩ := Int.exists_eq_and_succ_eq_of_le_add_one (Nat.zero_le a)
      (fun s _ hs' => by rcases hs s hs' with e | e <;> omega) h0 ha
    exact ⟨j, hj.le, hgj⟩
  · exact ⟨a, le_rfl, ha.symm⟩

lemma le_of_step (g : ℕ → ℤ) : ∀ a, (∀ j < a, g (j + 1) = g j ∨ g (j + 1) = g j + 1) →
    g 0 ≤ g a := by
  intro a
  induction a with
  | zero => intro _; exact le_rfl
  | succ a ih =>
    intro hs
    have := ih (fun j hj => hs j (by omega))
    rcases hs a (by omega) with e | e <;> omega

variable {P L : Type} [DecidableEq P] {I : Impl BinCons (fun _ : Unit => faiLoc) P L}

/-- The action is a `write`. -/
def IsWrite (a : Action BinCons (fun _ : Unit => faiLoc) L) : Prop :=
  ∃ x k, a = .access () (.write x) k

lemma soloStep_mem_fai {p : P} {W : Config BinCons (fun _ : Unit => faiLoc) P L}
    (h : ¬ IsWrite (I.act p (W.loc p))) :
    (I.soloStep p W).mem () = W.mem () ∨ (I.soloStep p W).mem () = W.mem () + 1 := by
  unfold soloStep
  split_ifs with hp
  · exact Or.inl rfl
  obtain ⟨W', hW'⟩ := Option.isSome_iff_exists.1 (I.step_nextLabel_isSome W p hp)
  rw [hW', Option.getD_some]
  have hlab := I.nextLabel_proc W p
  have hst := nextLabel_isStep (I := I) W p
  cases hl : I.nextLabel W p with
  | inv q o => rw [hl] at hst; exact absurd hst (by simp [Label.IsStep])
  | ret q u => rw [hl] at hW'; exact Or.inl (by rw [(step_ret hW').2.2.1])
  | tau q =>
    rw [hl] at hW' hlab
    simp only [Label.proc] at hlab; subst hlab
    obtain ⟨-, -, i, o, k, hk, hm, -⟩ := step_tau hW'
    cases i
    cases o with
    | read => left; rw [hm]; simp
    | write x => exact absurd ⟨x, k, hk⟩ h
    | fai => right; rw [hm]; simp

/-- The step of a process poised to write. -/
lemma step_write {p : P} {W : Config BinCons (fun _ : Unit => faiLoc) P L} {x : ℤ}
    {k : ℤ → L} (hp : W.pend p ≠ none) (hk : I.act p (W.loc p) = .access () (.write x) k) :
    ∃ W', I.step W (.tau p) = some W' ∧ W'.mem () = x ∧ W'.loc p = k 0 ∧ W'.pend = W.pend := by
  refine ⟨{ W with mem := Function.update W.mem () x, loc := Function.update W.loc p (k 0) },
    by simp [step, hp, hk], by simp, by simp, rfl⟩

/-- A pending process that stops being pending during its solo run has decided. -/
lemma exists_ret_soloLabels {p : P} {W : Config BinCons (fun _ : Unit => faiLoc) P L} {K : ℕ}
    (hp : W.pend p ≠ none) (hK : ((I.soloStep p)^[K] W).pend p = none) :
    ∃ w, (Label.ret p w : Label P BinCons) ∈ I.soloLabels p W K := by
  have hc := I.runFrom_counts (I.runFrom_soloLabels p W K) p 1 0 (Or.inr ⟨hp, rfl⟩)
  rw [I.opsOf_soloLabels] at hc
  simp only [hK, List.length_nil, Nat.add_zero, Nat.zero_add, true_and, ne_eq,
    not_true_eq_false, false_and, or_false] at hc
  match h : respsOf (I.soloLabels p W K) p with
  | [] => rw [h] at hc; simp at hc
  | x :: _ => exact ⟨x, mem_respsOf_iff.1 (by rw [h]; simp)⟩

/-- **Theorem 5.1** of Ellen–Gelashvili–Shavit–Zhu: it is not possible to solve obstruction-free
binary consensus for `n ≥ 2` processes using a single memory location that supports only
`read()`, `write(x)` and `fetch-and-increment()`. -/
theorem theorem_5_1 [Fintype P] (I : Impl BinCons (fun _ : Unit => faiLoc) P L)
    (hS : I.Solves (weakConsensus P Bool)) (hof : I.OneShotOF) (hall : ∀ p v, I.allowed p v)
    (hn : 2 ≤ Fintype.card P) : False := by
  classical
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card hn
  let f : Bool → P → Bool := fun y r => if r = p then y else !y
  have hF := fun y => I.exists_initial hall (f y)
  choose F hFrun hFreach hFloc hFpend hFmem using hF
  have hfin : ∀ y, ∃ K, ((I.soloStep p)^[K] (F y)).pend p = none := fun y => by
    obtain ⟨α, hα, h1, -⟩ := hFreach y
    exact hof α (F y) p hα h1 (by simp [hFpend])
  have hA := fun y => I.exists_solo_until p (F y) IsWrite (hfin y)
  choose a ha1 ha2 using hA
  let X : Bool → ℕ → Config BinCons (fun _ : Unit => faiLoc) P L :=
    fun y j => (I.soloStep p)^[j] (F y)
  let M : Bool → ℤ := fun y => (X y (a y)).mem ()
  have hstepM : ∀ y, ∀ j < a y, (X y (j + 1)).mem () = (X y j).mem () ∨
      (X y (j + 1)).mem () = (X y j).mem () + 1 := fun y j hj => by
    simp only [X, Function.iterate_succ_apply']; exact soloStep_mem_fai (ha1 y j hj).2
  obtain ⟨x, hx⟩ : ∃ x, M x ≤ M (!x) := by
    rcases le_total (M false) (M true) with h | h
    · exact ⟨false, h⟩
    · exact ⟨true, h⟩
  -- the unanimous configuration with inputs `!x`
  obtain ⟨Bc, hBrun, hBreach, hBloc, hBpend, hBmem⟩ := I.exists_initial hall (fun _ => !x)
  have hagB : ∀ j, Agree p ((I.soloStep p)^[j] Bc) (X (!x) j) := fun j =>
    iterate_soloStep_agree ⟨by rw [hBmem, hFmem], by rw [hBloc, hFloc]; simp [f],
      by rw [hBpend, hFpend]; simp [f]⟩ j
  have h0 : (X x 0).mem () = I.memInit () := by simp [X, hFmem]
  obtain ⟨j', -, hj'⟩ := exists_eq_of_step (fun j => ((I.soloStep p)^[j] Bc).mem ()) (M x) (a (!x))
    (fun j hj => by simp only [(hagB _).mem]; exact hstepM (!x) j hj)
    (by simp only [Function.iterate_zero, id, hBmem]; rw [← h0]; exact le_of_step (fun j => (X x j).mem ()) (a x) (hstepM x))
    (by simp only [(hagB _).mem]; exact hx)
  set C' := (I.soloStep p)^[j'] Bc with hC'
  set C := X x (a x) with hC
  have hrbC' : I.ReachBy {p} Bc C' := ⟨_, soloLabels_steps p Bc j', I.runFrom_soloLabels p Bc j'⟩
  have hrbC : I.ReachBy {p} (F x) C :=
    ⟨_, soloLabels_steps p (F x) (a x), I.runFrom_soloLabels p (F x) (a x)⟩
  have hC'reach : I.Reach C' := hBreach.reachBy hrbC'
  have hCreach : I.Reach C := (hFreach x).reachBy hrbC
  have hqC' := I.iterate_soloStep_other hpq.symm Bc j'
  have hqC := I.iterate_soloStep_other hpq.symm (F x) (a x)
  -- `q` decides `!x` from `C'`, hence from `C`
  obtain ⟨u, hu⟩ := hC'reach.exists_canDecide_self hof (p := q) (by rw [hqC'.2, hBpend]; simp)
  have hu' : u = !x := canDecide_const hS hBrun hrbC' hu
  have hagq : AgreeOn ({q} : Set P) C' C := by
    refine ⟨funext fun i => ?_, fun r hr => ?_, fun r hr => ?_⟩
    · cases i; rw [hj']
    · rw [Set.mem_singleton_iff] at hr; subst hr
      rw [hqC'.1, hqC.1, hBloc, hFloc]; simp [f, Ne.symm hpq]
    · rw [Set.mem_singleton_iff] at hr; subst hr
      rw [hqC'.2, hqC.2, hBpend, hFpend]; simp [f, Ne.symm hpq]
  have hqx : I.CanDecide {q} C (!x) := hu' ▸ canDecide_of_agreeOn hagq hu
  -- `p` decides `x` in its solo run from `F x`
  have hpx : ∀ Z, I.ReachBy {p} (F x) Z → ∀ w, I.CanDecide {p} Z w → w = x :=
    fun Z hZ w hw => (canDecide_initial hS hall (f x) (hFrun x) (hw.of_reachBy hZ)).trans
      (by simp [f])
  by_cases hret : C.pend p = none
  · obtain ⟨w, hw⟩ := exists_ret_soloLabels (I := I) (by simp [hFpend]) hret
    have hwx : w = x := hpx (F x) (ReachBy.refl _ _) w
      ⟨_, _, soloLabels_steps p (F x) (a x), I.runFrom_soloLabels p (F x) (a x), p, hw⟩
    have := (hFreach x).decides_canDecide_eq hS (soloLabels_steps p (F x) (a x))
      (I.runFrom_soloLabels p (F x) (a x)) ⟨p, hw⟩ hqx
    subst hwx; cases w <;> simp at this
  · obtain ⟨v, k, hk⟩ := (ha2 x).resolve_left hret
    obtain ⟨Cw, hCw, hCwm, hCwl, hCwp⟩ := step_write hret hk
    obtain ⟨γ, Cγ, hγ, hCγ, hdγ⟩ := hqx
    have hpγ := I.runFrom_other hCγ (hγ.proc_ne (by simpa using hpq))
    obtain ⟨Cγw, hCγw, hCγwm, hCγwl, hCγwp⟩ :=
      step_write (by rw [hpγ.2]; exact hret) (by rw [hpγ.1]; exact hk)
    have hCwreach : I.Reach Cw := hCreach.extend (Q := {p}) (β := [.tau p])
      (fun l hl => by simp at hl; subst hl; exact ⟨rfl, trivial⟩) (by rw [runFrom_singleton, hCw])
    obtain ⟨w, hw⟩ := hCwreach.exists_canDecide_self hof (p := p) (by rw [hCwp]; exact hret)
    have hwx : w = x := hpx Cw (hrbC.trans ⟨[.tau p], fun l hl => by
      simp at hl; subst hl; exact ⟨rfl, trivial⟩, by rw [runFrom_singleton, hCw]⟩) w hw
    have hag : AgreeOn ({p} : Set P) Cw Cγw := by
      refine ⟨funext fun i => ?_, fun r hr => ?_, fun r hr => ?_⟩
      · cases i; rw [hCwm, hCγwm]
      · rw [Set.mem_singleton_iff] at hr; subst hr; rw [hCwl, hCγwl]
      · rw [Set.mem_singleton_iff] at hr; subst hr; rw [hCwp, hCγwp, hpγ.2]
    have hw' := canDecide_of_agreeOn hag hw
    have := hCreach.decides_canDecide_eq hS (Q := {q} ∪ {p}) (β := γ ++ [.tau p])
      ((hγ.mono Set.subset_union_left).append (fun l hl => by
        simp at hl; subst hl; exact ⟨Or.inr rfl, trivial⟩))
      (by rw [I.runFrom_append_of_eq hCγ, runFrom_singleton, hCγw])
      (hdγ.mono (List.subset_append_left _ _)) hw'
    subst hwx; cases w <;> simp at this

end Cslib.SharedMemory.ComplexityHierarchy
