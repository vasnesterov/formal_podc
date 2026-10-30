import Papers.PODC2026.ConflictFreedom.Alg1Lin

/-!
# Theorem 4.4: Algorithm 1 is weakly conflict-free — infrastructure

Facts about infinite executions of `Alg1.impl`:

* `inv_at`: the invariants at every time;
* `first_step`: a process that keeps taking steps and is pending takes its next step in its
  current local state;
* `not_writeS`: a correct process whose operation is pending forever is never in phase `writeS`
  or `done` (it would return).
-/

namespace Podc.ConflictFreedom

open Cslib.SharedMemory Cslib.Mazurkiewicz Classical

namespace Alg1

variable {A : ObjSpec} {n : ℕ} [Inhabited A.Resp] [Inhabited A.Op] [NeZero n]

variable (e : (impl (A := A) (n := n)).InfExec)

lemma inv_at (t : ℕ) : Inv1 (e.cfg t) ∧ Inv2 (e.cfg t) ∧ Inv3 (e.pre t) (e.cfg t) :=
  inv_of_run (e.run_pre t)

variable {e}

/-- The next step of a pending process that keeps taking steps is taken in its current local
state. -/
lemma first_step {q : Fin n} {T₀ : ℕ} (hpend : PendingFrom e q T₀) (hinf : TakesInfSteps e q)
    {t : ℕ} (ht : T₀ ≤ t) :
    ∃ m ≥ t, (e.lbl m).proc = q ∧ (e.lbl m).IsStep ∧ (e.cfg m).loc q = (e.cfg t).loc q := by
  have hex : ∃ k, (e.lbl (t + k)).proc = q ∧ (e.lbl (t + k)).IsStep := by
    obtain ⟨m, hm, h1, h2⟩ := hinf t
    exact ⟨m - t, by rw [Nat.add_sub_cancel' hm]; exact ⟨h2, h1⟩⟩
  have hmin := fun j (hj : j < Nat.find hex) => Nat.find_min hex hj
  -- no label of `q` before the first step: `q` cannot invoke while pending
  have hne : ∀ j < Nat.find hex, (e.lbl (t + j)).proc ≠ q := by
    intro j hj hpq
    have hns := hmin j hj
    have : ¬ (e.lbl (t + j)).IsStep := fun hs => hns ⟨hpq, hs⟩
    cases hl : e.lbl (t + j) with
    | inv q' o =>
      rw [hl] at hpq; simp only [Label.proc] at hpq; subst hpq
      have hs := e.step_eq (t + j); rw [hl] at hs
      exact hpend (t + j) (by omega) (Impl.step_inv hs).1
    | tau q' => rw [hl] at this; exact this trivial
    | ret q' r => rw [hl] at this; exact this trivial
  have hc := e.cfg_add_of_proc_ne hne
  exact ⟨t + Nat.find hex, by omega, (Nat.find_spec hex).1, (Nat.find_spec hex).2, hc.1⟩

/-- A step of `q` from phase `done` is its response. -/
lemma step_done {C C' : Cfg A n} {ℓ : Label (Fin n) A} {q : Fin n}
    (h : (impl (A := A) (n := n)).step C ℓ = some C') (hq : ℓ.proc = q) (hs : ℓ.IsStep) (hph : (C.loc q).phase = .done) :
    C'.pend q = none := by
  cases ℓ with
  | inv _ _ => exact hs.elim
  | tau p =>
    simp only [Label.proc] at hq; subst hq
    obtain ⟨-, -, hT⟩ := step_tau_cases h
    cases hT <;> simp_all
  | ret p r =>
    simp only [Label.proc] at hq; subst hq
    rw [(Impl.step_ret h).2.1]; simp

/-- A step of `q` from phase `writeS` leads to phase `done`. -/
lemma step_writeS {C C' : Cfg A n} {ℓ : Label (Fin n) A} {q : Fin n} (hI : Inv1 C)
    (h : (impl (A := A) (n := n)).step C ℓ = some C') (hq : ℓ.proc = q) (hs : ℓ.IsStep)
    (hph : (C.loc q).phase = .writeS) : (C'.loc q).phase = .done := by
  cases ℓ with
  | inv _ _ => exact hs.elim
  | tau p =>
    simp only [Label.proc] at hq; subst hq
    obtain ⟨-, -, hT⟩ := step_tau_cases h
    cases hT <;> simp_all
  | ret p r =>
    simp only [Label.proc] at hq; subst hq
    obtain ⟨hdone, -⟩ := step_ret_cases h (hI.loc p)
    rw [hph] at hdone; cases hdone

/-- A correct process whose operation is pending forever is never about to write `S` or to
return. -/
lemma not_writeS_done {q : Fin n} {T₀ : ℕ} (hpend : PendingFrom e q T₀) (hinf : TakesInfSteps e q)
    {t : ℕ} (ht : T₀ ≤ t) :
    ((e.cfg t).loc q).phase ≠ .writeS ∧ ((e.cfg t).loc q).phase ≠ .done := by
  have hdone : ∀ t', T₀ ≤ t' → ((e.cfg t').loc q).phase ≠ .done := by
    intro t' ht' hph
    obtain ⟨m, hm, hpq, hs, hloc⟩ := first_step hpend hinf ht'
    have := step_done (e.step_eq m) hpq hs (by rw [hloc]; exact hph)
    exact hpend (m + 1) (by omega) this
  refine ⟨fun hph => ?_, hdone t ht⟩
  obtain ⟨m, hm, hpq, hs, hloc⟩ := first_step hpend hinf ht
  have := step_writeS (inv_at e m).1 (e.step_eq m) hpq hs (by rw [hloc]; exact hph)
  exact hdone (m + 1) (by omega) this

lemma LInv.sreg_le {C : Cfg A n} {i : Fin n} (hL : LInv C i) :
    (C.mem (.S i)).1 ≤ (C.loc i).r := by
  rcases h : (C.loc i).phase with _ | ⟨j, best⟩ | g | _ | _
  · exact (hL.sreg_idle h).le
  · exact (hL.sreg_readS j best h).le
  · exact (hL.sreg_gca g h).le
  · exact (hL.sreg_writeS h).le
  · exact (hL.sreg_done h).le

lemma mem_S_self_of_not_writeS {C C' : Cfg A n} {p : Fin n}
    (h : (impl (A := A) (n := n)).step C (.tau p) = some C') (hnw : (C.loc p).phase ≠ .writeS) :
    C'.mem (.S p) = C.mem (.S p) := by
  obtain ⟨-, -, hT⟩ := step_tau_cases h
  cases hT with
  | writeS hph => exact absurd hph hnw
  | _ => simp [Function.update_of_ne]

/-- State of a process of `Q` after `T₀` relative to the round `B + 1`. -/
structure QState (B : ℕ) (C : Cfg A n) (q : Fin n) (c : Cmd A n) : Prop where
  round : ∀ g, (C.loc q).phase = .gca g → (C.loc q).r ≤ B + 1 ∨ (C.loc q).hist (B + 1) ≠ none
  best : ∀ j best, (C.loc q).phase = .readS j best → best.1 ≤ B
  cmd : (C.loc q).cmd = c
  inp : ∀ g, locAt (C.loc q) (B + 1) = some g → ∃ t₀, BaseOK C (B + 1) t₀ ∧ g.inp = t₀.snoc c

/-- Steps inside `GCA_r` preserve `QState`. -/
lemma QState.gca012 {B : ℕ} {C C' : Cfg A n} {q : Fin n} {c : Cmd A n} {ℓ : Label (Fin n) A}
    (hQ : QState B C q c) (hI : Inv1 C) (hI' : Inv1 C')
    (h : (impl (A := A) (n := n)).step C ℓ = some C') {g g' : GCA.Loc n (Tr A n)}
    (hph : (C.loc q).phase = .gca g) (hinp : g'.inp = g.inp)
    (hlp : C'.loc q = { C.loc q with phase := .gca g' })
    (hcurC : ∃ t₀, BaseOK C (C.loc q).r t₀ ∧ g.inp = t₀.snoc (C.loc q).cmd) :
    QState B C' q c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hlp]
  · intro _ _; exact hQ.round g hph
  · intro _ _ h'; cases h'
  · exact hQ.cmd
  · intro g'' hg
    rw [locAt_gca_step (l' := { C.loc q with phase := .gca g' }) hph rfl rfl rfl] at hg
    split_ifs at hg with hr
    · simp only [Option.some.injEq] at hg; subst hg
      obtain ⟨t₀, h1, h2⟩ := hcurC
      exact ⟨t₀, by rw [hr]; exact h1.step hI hI' h, by rw [hinp, h2, hQ.cmd]⟩
    · obtain ⟨t₀, h1, h2⟩ := hQ.inp g'' hg
      exact ⟨t₀, h1.step hI hI' h, h2⟩

/-- One internal step of `q` preserves `QState`. -/
lemma QState.step {B : ℕ} {C C' : Cfg A n} {q : Fin n} {c : Cmd A n} (hI : Inv1 C)
    (hJ : Inv2 C) (hI' : Inv1 C') (hJ' : Inv2 C')
    (h : (impl (A := A) (n := n)).step C (.tau q) = some C') (hQ : QState B C q c)
    (hnw : (C.loc q).phase ≠ .writeS) (hnw' : (C'.loc q).phase ≠ .writeS)
    (hSB : ∀ j, (C.mem (.S j)).1 ≤ B) : QState B C' q c := by
  have hcur : ∀ g, (C'.loc q).phase = .gca g → (C'.loc q).r = B + 1 →
      ∃ t₀, BaseOK C' (B + 1) t₀ ∧ g.inp = t₀.snoc (C'.loc q).cmd := fun g hg hr => by
    rw [← hr]; exact hJ'.cur q g hg
  have hold : ∀ g, (C.loc q).hist (B + 1) = some g →
      ∃ t₀, BaseOK C' (B + 1) t₀ ∧ g.inp = t₀.snoc c := fun g hg => by
    obtain ⟨t₀, h1, h2⟩ := hQ.inp g (hI.locAt_of_hist hg)
    exact ⟨t₀, h1.step hI hI' h, h2⟩
  obtain ⟨-, -, hT⟩ := step_tau_cases h
  cases hT with
  | readS j best hj hph hlt =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [setLoc_loc, Function.update_self]
    · intro _ h; cases h
    · rintro j' b' hb; simp only [Phase.readS.injEq] at hb; rw [← hb.2]
      rcases better_cases best (C.mem (.S ⟨j, hj⟩)) with h' | h' <;> rw [h']
      · exact hQ.best j best hph
      · exact hSB _
    · exact hQ.cmd
    · intro g hg; rw [locAt_of_not_gca (by simp)] at hg; exact hold g hg
  | readLast j best hj hph hlt =>
    have hb : (better best (C.mem (.S ⟨j, hj⟩))).1 ≤ B := by
      rcases better_cases best (C.mem (.S ⟨j, hj⟩)) with h' | h' <;> rw [h']
      · exact hQ.best j best hph
      · exact hSB _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _ _; left; simp [Loc.afterRead, Loc.startRound]; omega
    · intro _ _ h'; simp [Loc.afterRead, Loc.startRound] at h'
    · simpa [Loc.afterRead, Loc.startRound] using hQ.cmd
    · intro g hg
      by_cases hr : ((C.loc q).afterRead (better best (C.mem (.S ⟨j, hj⟩)))).r = B + 1
      · simp only [setLoc_loc, Function.update_self] at hg
        rw [locAt_gca (g := GCA.Loc.init ((better best (C.mem (.S ⟨j, hj⟩))).2.snoc (C.loc q).cmd))
          (by simp [Loc.afterRead, Loc.startRound]), if_pos hr.symm] at hg
        simp only [Option.some.injEq] at hg; subst hg
        obtain ⟨t₀, h1, h2⟩ := hcur
          (GCA.Loc.init ((better best (C.mem (.S ⟨j, hj⟩))).2.snoc (C.loc q).cmd))
          (by simp [Loc.afterRead, Loc.startRound]) (by simpa using hr)
        exact ⟨t₀, h1, by rw [h2]; simp [Loc.afterRead, Loc.startRound, hQ.cmd]⟩
      · simp only [setLoc_loc, Function.update_self] at hg
        rw [locAt_eq_hist_of_ne (Ne.symm hr)] at hg
        exact hold g (by simpa [Loc.afterRead, Loc.startRound] using hg)
  | gca0 g hph hpc =>
    exact hQ.gca012 hI hI' h (g' := { g with pc := 1 }) hph rfl (by simp) (hJ.cur q g hph)
  | gca1 g hph hpc =>
    exact hQ.gca012 hI hI' h (g' := { g with pc := 2, av := C.mem (.A (C.loc q).r) }) hph rfl
      (by simp) (hJ.cur q g hph)
  | gca2 g hph hpc =>
    exact hQ.gca012 hI hI' h (g' := { g with pc := 3 }) hph rfl (by simp) (hJ.cur q g hph)
  | gca3 g hph hpc =>
    set g4 : GCA.Loc n (Tr A n) := { g with pc := 4, bv := C.mem (.B (C.loc q).r) } with hg4
    by_cases hex : g4.output.2 = true ∧ (C.loc q).cmd ∈ g4.output.1.supp
    · exfalso; apply hnw'; simp [Loc.afterGCA, hex]
    · have hl' : (C.loc q).afterGCA g4 = { (C.loc q).startRound (C.loc q).r g4.output.1 with
          hist := Function.update (C.loc q).hist (C.loc q).r (some g4) } := by
        simp only [Loc.afterGCA, hex, if_false]
      have hrn := ((hI.loc q).gca g hph).2.1
      have hlp : (setLoc C q ((C.loc q).afterGCA g4)).loc q =
          { (C.loc q).startRound (C.loc q).r g4.output.1 with
            hist := Function.update (C.loc q).hist (C.loc q).r (some g4) } := by simp [hl']
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hlp]
      · intro _ _
        simp only [Loc.startRound]
        rcases Nat.lt_trichotomy (C.loc q).r (B + 1) with hr | hr | hr
        · left; omega
        · right; rw [hr]; simp
        · right
          rcases hQ.round g hph with h' | h'
          · omega
          · rw [Function.update_of_ne (by omega)]; exact h'
      · intro _ _ h'; simp [Loc.startRound] at h'
      · simpa [Loc.startRound] using hQ.cmd
      · intro g'' hg
        by_cases hr1 : B + 1 = (C.loc q).r + 1
        · rw [locAt_gca (g := GCA.Loc.init (g4.output.1.snoc (C.loc q).cmd))
            (by simp [Loc.startRound]), if_pos (by simpa [Loc.startRound] using hr1)] at hg
          simp only [Option.some.injEq] at hg; subst hg
          have hph' : ((setLoc C q ((C.loc q).afterGCA g4)).loc q).phase =
              .gca (GCA.Loc.init (g4.output.1.snoc (C.loc q).cmd)) := by
            rw [hlp]; simp [Loc.startRound]
          obtain ⟨t₀, h1, h2⟩ := hcur _ hph' (by rw [hlp]; simp [Loc.startRound]; omega)
          exact ⟨t₀, h1, by rw [h2, hlp]; simp [Loc.startRound, hQ.cmd]⟩
        · rw [locAt_eq_hist_of_ne (by simpa [Loc.startRound] using hr1)] at hg
          simp only [Loc.startRound] at hg
          by_cases hr2 : B + 1 = (C.loc q).r
          · rw [hr2, Function.update_self] at hg; simp only [Option.some.injEq] at hg; subst hg
            obtain ⟨t₀, h1, h2⟩ := hJ.cur q g hph
            exact ⟨t₀, by rw [← hr2] at h1; exact h1.step hI hI' h, by
              simpa [hg4, hQ.cmd] using h2⟩
          · rw [Function.update_of_ne hr2] at hg; exact hold g'' hg
  | writeS hph => exact absurd hph hnw

lemma QState.of_loc_eq {B : ℕ} {C C' : Cfg A n} {q : Fin n}
    {c : Cmd A n} {ℓ : Label (Fin n) A} (hQ : QState B C q c) (hI : Inv1 C) (hI' : Inv1 C')
    (h : (impl (A := A) (n := n)).step C ℓ = some C') (hl : C'.loc q = C.loc q) :
    QState B C' q c := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [hl]
  · exact hQ.round
  · exact hQ.best
  · exact hQ.cmd
  · intro g hg; obtain ⟨t₀, h1, h2⟩ := hQ.inp g hg; exact ⟨t₀, h1.step hI hI' h, h2⟩

/-- Progress measure of a process heading for round `B + 1`. -/
def meas (B : ℕ) (l : Loc A n) : ℕ :=
  match l.phase with
  | .readS j _ => 5 * (B + 2) + (n - j)
  | .gca g => 5 * (B + 1 - l.r) + (4 - g.pc)
  | _ => 0

/-- Each internal step of `q` decreases the measure, or completes `GCA_{B+1}`. -/
lemma meas_step {B : ℕ} {C C' : Cfg A n} {q : Fin n} {c : Cmd A n} (hI : Inv1 C)
    (h : (impl (A := A) (n := n)).step C (.tau q) = some C') (hQ : QState B C q c)
    (hng : (C.loc q).hist (B + 1) = none) (hnw : (C.loc q).phase ≠ .writeS)
    (hnw' : (C'.loc q).phase ≠ .writeS) (hSB : ∀ j, (C.mem (.S j)).1 ≤ B) :
    (C'.loc q).hist (B + 1) ≠ none ∨ meas B (C'.loc q) < meas B (C.loc q) := by
  obtain ⟨-, -, hT⟩ := step_tau_cases h
  cases hT with
  | readS j best hj hph hlt =>
    right; simp only [setLoc_loc, Function.update_self, meas, hph]; omega
  | readLast j best hj hph hlt =>
    right
    have hb : (better best (C.mem (.S ⟨j, hj⟩))).1 ≤ B := by
      rcases better_cases best (C.mem (.S ⟨j, hj⟩)) with h' | h' <;> rw [h']
      · exact hQ.best j best hph
      · exact hSB _
    simp only [setLoc_loc, Function.update_self, meas, hph, Loc.afterRead, Loc.startRound,
      GCA.Loc.init]
    omega
  | gca0 g hph hpc =>
    right; simp only [setMemLoc_loc, Function.update_self, meas, hph, hpc]; omega
  | gca1 g hph hpc =>
    right; simp only [setLoc_loc, Function.update_self, meas, hph, hpc]; omega
  | gca2 g hph hpc =>
    right; simp only [setMemLoc_loc, Function.update_self, meas, hph, hpc]; omega
  | gca3 g hph hpc =>
    have hpc4 := ((hI.loc q).gca g hph).2.2
    have hr : (C.loc q).r ≤ B + 1 := by
      rcases hQ.round g hph with h' | h'
      · exact h'
      · exact absurd hng h'
    set g4 : GCA.Loc n (Tr A n) := { g with pc := 4, bv := C.mem (.B (C.loc q).r) } with hg4
    rcases Nat.lt_or_eq_of_le hr with hr | hr
    · by_cases hex : g4.output.2 = true ∧ (C.loc q).cmd ∈ g4.output.1.supp
      · exfalso; apply hnw'; simp [Loc.afterGCA, hex]
      · right
        have hl' : (C.loc q).afterGCA g4 = { (C.loc q).startRound (C.loc q).r g4.output.1 with
            hist := Function.update (C.loc q).hist (C.loc q).r (some g4) } := by
          simp only [Loc.afterGCA, hex, if_false]
        simp only [setLoc_loc, Function.update_self, hl', meas, hph, Loc.startRound,
          GCA.Loc.init]
        omega
    · left
      simp only [setLoc_loc, Function.update_self]
      unfold Loc.afterGCA
      split_ifs <;> simp [Loc.startRound, hr]
  | writeS hph => exact absurd hph hnw

/-- When a process records the result of `GCA_r` in its history, it leaves the loop if the result
is committed and contains its command. -/
lemma writeS_of_hist_set {C C' : Cfg A n} {ℓ : Label (Fin n) A} {j : Fin n} {r : ℕ}
    {g : GCA.Loc n (Tr A n)} (hI : Inv1 C) (h : (impl (A := A) (n := n)).step C ℓ = some C')
    (h0 : (C.loc j).hist r = none) (h1 : (C'.loc j).hist r = some g)
    (hex : g.output.2 = true ∧ (C.loc j).cmd ∈ g.output.1.supp) : (C'.loc j).phase = .writeS := by
  by_cases hp : ℓ.proc = j
  swap
  · rw [(Impl.step_other h hp).1, h0] at h1; cases h1
  cases ℓ with
  | inv p o =>
    simp only [Label.proc] at hp; subst hp
    obtain ⟨-, -, -, hloc, -⟩ := Impl.step_inv h
    rw [hloc] at h1; simp [impl, invoke, h0] at h1
  | ret p r' =>
    simp only [Label.proc] at hp; subst hp
    obtain ⟨-, -, hC'⟩ := step_ret_cases h (hI.loc p)
    rw [hC'] at h1; simp [h0] at h1
  | tau p =>
    simp only [Label.proc] at hp; subst hp
    obtain ⟨-, -, hT⟩ := step_tau_cases h
    cases hT with
    | readS => simp [h0] at h1
    | readLast => simp [Loc.afterRead, Loc.startRound, h0] at h1
    | gca0 => simp [h0] at h1
    | gca1 => simp [h0] at h1
    | gca2 => simp [h0] at h1
    | gca3 g' hph hpc =>
      simp only [setLoc_loc, Function.update_self] at h1 ⊢
      by_cases hr : r = (C.loc p).r
      · subst hr
        unfold Loc.afterGCA at h1 ⊢
        split_ifs at h1 ⊢ with hc
        · rfl
        · simp only [Loc.startRound, Function.update_self, Option.some.injEq] at h1
          subst h1; exact absurd hex hc
      · unfold Loc.afterGCA at h1
        split_ifs at h1 <;> simp [Loc.startRound, Function.update_of_ne hr, h0] at h1
    | writeS => simp [h0] at h1

/-- The ghost history only grows along an infinite execution. -/
lemma hist_mono_time {i : Fin n} {r : ℕ} {g : GCA.Loc n (Tr A n)} {t t' : ℕ} (htt : t ≤ t')
    (h : ((e.cfg t).loc i).hist r = some g) : ((e.cfg t').loc i).hist r = some g := by
  induction t', htt using Nat.le_induction with
  | base => exact h
  | succ t' _ ih => exact hist_mono_step (inv_at e t').1 (e.step_eq t') ih

/-- Hypotheses for the progress arguments: from time `T₀` on, the processes in `Q` are pending
forever and keep taking steps, the other processes take no steps, and all rounds (and the best
rounds read so far) are at most `B`. -/
structure Setup (e : (impl (A := A) (n := n)).InfExec) (Q : Fin n → Prop) (T₀ B : ℕ) : Prop where
  pendQ : ∀ q, Q q → PendingFrom e q T₀
  infQ : ∀ q, Q q → TakesInfSteps e q
  quiet : ∀ i, ¬ Q i → ∀ m ≥ T₀, (e.lbl m).IsStep → (e.lbl m).proc ≠ i
  bound : ∀ i, ((e.cfg T₀).loc i).r ≤ B
  bestB : ∀ i j best, ((e.cfg T₀).loc i).phase = .readS j best → best.1 ≤ B

namespace Setup

variable {Q : Fin n → Prop} {T₀ B : ℕ} (hS : Setup e Q T₀ B)
include hS

/-- After `T₀`, labels of processes outside `Q` are invocations, and labels of processes in `Q`
are internal steps from phases `readS`/`gca`. -/
lemma label_cases {m : ℕ} (hm : T₀ ≤ m) :
    (¬ Q (e.lbl m).proc ∧ ¬ (e.lbl m).IsStep) ∨
    (Q (e.lbl m).proc ∧ e.lbl m = .tau (e.lbl m).proc ∧
      (((e.cfg m).loc (e.lbl m).proc).phase ≠ .writeS ∧
        ((e.cfg m).loc (e.lbl m).proc).phase ≠ .done)) := by
  by_cases hq : Q (e.lbl m).proc
  · right
    have hnw := not_writeS_done (hS.pendQ _ hq) (hS.infQ _ hq) hm
    refine ⟨hq, ?_, hnw⟩
    have hs := e.step_eq m
    cases hl : e.lbl m with
    | inv q o =>
      rw [hl] at hs hq; simp only [Label.proc] at hq
      exact absurd (Impl.step_inv hs).1 (hS.pendQ q hq m hm)
    | tau q => rfl
    | ret q r =>
      rw [hl] at hs hnw; simp only [Label.proc] at hnw
      exact absurd (step_ret_cases hs ((inv_at e m).1.loc q)).1 hnw.2
  · left
    exact ⟨hq, fun hs => hS.quiet _ hq m hm hs rfl⟩

/-- The registers `S[j]` do not change after `T₀`. -/
lemma mem_S {t : ℕ} (ht : T₀ ≤ t) (j : Fin n) : (e.cfg t).mem (.S j) = (e.cfg T₀).mem (.S j) := by
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih =>
    rw [← ih]
    have hs := e.step_eq t
    rcases hS.label_cases ht with ⟨-, hns⟩ | ⟨-, hτ, hnw, -⟩
    · cases hl : e.lbl t with
      | inv q o => rw [hl] at hs; rw [(Impl.step_inv hs).2.2.2.2]
      | tau q => rw [hl] at hns; exact absurd trivial hns
      | ret q r => rw [hl] at hns; exact absurd trivial hns
    · by_cases hj : (e.lbl t).proc = j
      · rw [hτ] at hs
        rw [← hj]
        exact mem_S_self_of_not_writeS hs hnw
      · exact mem_S_other (inv_at e t).1 hs hj

lemma S_le {t : ℕ} (ht : T₀ ≤ t) (j : Fin n) : ((e.cfg t).mem (.S j)).1 ≤ B := by
  rw [hS.mem_S ht j]; exact ((inv_at e T₀).1.loc j).sreg_le.trans (hS.bound j)

lemma locAt_T₀ (i : Fin n) : locAt ((e.cfg T₀).loc i) (B + 1) = none := by
  by_contra hc
  obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hc
  have := (inv_at e T₀).1.le_r_of_locAt hg
  have := hS.bound i; omega

/-- Processes outside `Q` never participate in `GCA_{B+1}`. -/
lemma none_out {i : Fin n} (hi : ¬ Q i) {t : ℕ} (ht : T₀ ≤ t) :
    locAt ((e.cfg t).loc i) (B + 1) = none := by
  induction t, ht using Nat.le_induction with
  | base => exact hS.locAt_T₀ i
  | succ t ht ih =>
    have hs := e.step_eq t
    by_cases hp : (e.lbl t).proc = i
    · rcases hS.label_cases ht with ⟨-, hns⟩ | ⟨hq, -⟩
      · cases hl : e.lbl t with
        | inv q o =>
          rw [hl] at hs hp; simp only [Label.proc] at hp; subst hp
          obtain ⟨hpd, -, -, hloc, -⟩ := Impl.step_inv hs
          have hidle := ((inv_at e t).1.loc q).pend_iff.1 hpd
          rw [hloc]; simp only [Function.update_self]
          rw [locAt_of_not_gca (by simp [impl, invoke])]
          rw [locAt_of_not_gca (by simp [hidle])] at ih
          simpa [impl, invoke] using ih
        | tau q => rw [hl] at hns; exact absurd trivial hns
        | ret q r => rw [hl] at hns; exact absurd trivial hns
      · rw [hp] at hq; exact absurd hq hi
    · rw [(Impl.step_other hs hp).1]; exact ih

/-- The state of the processes of `Q` after `T₀`. -/
lemma qstate {q : Fin n} (hq : Q q) {t : ℕ} (ht : T₀ ≤ t) :
    QState B (e.cfg t) q ((e.cfg T₀).loc q).cmd := by
  induction t, ht using Nat.le_induction with
  | base =>
    refine ⟨fun g _ => Or.inl ((hS.bound q).trans (Nat.le_succ B)), hS.bestB q, rfl, ?_⟩
    intro g hg; rw [hS.locAt_T₀ q] at hg; cases hg
  | succ t ht ih =>
    have hs := e.step_eq t
    obtain ⟨hI, hJ, -⟩ := inv_at e t
    obtain ⟨hI', hJ', -⟩ := inv_at e (t + 1)
    by_cases hp : (e.lbl t).proc = q
    · rcases hS.label_cases ht with ⟨hnq, -⟩ | ⟨-, hτ, hnw, -⟩
      · rw [hp] at hnq; exact absurd hq hnq
      · rw [hτ, hp] at hs
        rw [hp] at hnw
        exact ih.step hI hJ hI' hJ' hs hnw
          (not_writeS_done (hS.pendQ q hq) (hS.infQ q hq) (by omega)).1 (fun j => hS.S_le ht j)
    · exact ih.of_loc_eq hI hI' hs (Impl.step_other hs hp).1

/-- Every process of `Q` eventually completes `GCA_{B+1}`. -/
lemma progress {q : Fin n} (hq : Q q) : ∃ t ≥ T₀, ((e.cfg t).loc q).hist (B + 1) ≠ none := by
  refine e.exists_good q (fun t => ((e.cfg t).loc q).hist (B + 1) ≠ none)
    (fun t => meas B ((e.cfg t).loc q)) T₀ ?_ ?_ ?_
  · intro t ht _
    obtain ⟨m, hm, h1, h2⟩ := hS.infQ q hq t
    exact ⟨m, hm, h2, h1⟩
  · intro t ht hng hpq hst
    rcases hS.label_cases ht with ⟨hnq, hns⟩ | ⟨-, hτ, hnw, -⟩
    · exact absurd hst hns
    · have hs := e.step_eq t
      rw [hτ, hpq] at hs
      rw [hpq] at hnw
      push Not at hng
      exact meas_step (inv_at e t).1 hs (hS.qstate hq ht) hng hnw
        (not_writeS_done (hS.pendQ q hq) (hS.infQ q hq) (by omega)).1 (fun j => hS.S_le ht j)
  · intro t ht _ hns
    right
    have hs := e.step_eq t
    by_cases hpq : (e.lbl t).proc = q
    · exfalso
      cases hl : e.lbl t with
      | inv q' o =>
        rw [hl] at hs hpq; simp only [Label.proc] at hpq; subst hpq
        exact (hS.pendQ q' hq t ht) (Impl.step_inv hs).1
      | tau q' => exact hns ⟨hpq, by rw [hl]; trivial⟩
      | ret q' r => exact hns ⟨hpq, by rw [hl]; trivial⟩
    · rw [(Impl.step_other hs hpq).1]

/-- If, once every process of `Q` has completed `GCA_{B+1}`, the inputs of `GCA_{B+1}` are
compatible, we reach a contradiction: by Commitment some process of `Q` committed a trace
containing its command, so it left the loop and would return. -/
theorem false_of_compat (hne : ∃ q, Q q)
    (hcompat : ∀ t ≥ T₀, (∀ q, Q q → ((e.cfg t).loc q).hist (B + 1) ≠ none) →
      Compat (GCA.inputs (gst (e.cfg t) (B + 1)))) : False := by
  -- a time at which every process of `Q` has completed `GCA_{B+1}`
  choose! tq htq using fun q (hq : Q q) => hS.progress hq
  set T₁ := max T₀ (Finset.univ.sup fun q => if Q q then tq q else 0) with hT₁
  have hT₁0 : T₀ ≤ T₁ := le_max_left _ _
  have hdone : ∀ q, Q q → ∃ g, ((e.cfg T₁).loc q).hist (B + 1) = some g := by
    intro q hq
    obtain ⟨hle, hne'⟩ := htq q hq
    obtain ⟨g, hg⟩ := Option.ne_none_iff_exists'.1 hne'
    refine ⟨g, hist_mono_time ?_ hg⟩
    refine le_trans ?_ (le_max_right _ _)
    have := Finset.le_sup (f := fun q => if Q q then tq q else 0) (Finset.mem_univ q)
    simpa [hq] using this
  obtain ⟨hI, hJ, -⟩ := inv_at e T₁
  have hcom := GCA.commitment_of_reach (hI.reach (B + 1))
    (hcompat T₁ hT₁0 fun q hq => by obtain ⟨g, hg⟩ := hdone q hq; rw [hg]; simp)
    (fun j l hl => by
      rw [gst_loc] at hl
      by_cases hj : Q j
      · obtain ⟨g, hg⟩ := hdone j hj
        rw [hI.locAt_of_hist hg] at hl; cases hl
        exact (hI.loc j).hist_pc _ _ hg
      · rw [hS.none_out hj hT₁0] at hl; cases hl)
    (by
      obtain ⟨q, hq⟩ := hne
      obtain ⟨g, hg⟩ := hdone q hq
      exact ⟨q, by rw [gst_loc, hI.locAt_of_hist hg]; simp⟩)
  obtain ⟨j, l, ⟨hl, -⟩, hinp, hc⟩ := hcom
  rw [gst_loc] at hl
  have hj : Q j := by
    by_contra hj; rw [hS.none_out hj hT₁0] at hl; cases hl
  obtain ⟨g, hg⟩ := hdone j hj
  rw [hI.locAt_of_hist hg] at hl; simp only [Option.some.injEq] at hl; subst hl
  -- the command of `j` is in the committed trace
  obtain ⟨t₀, -, hgi⟩ := (hS.qstate hj hT₁0).inp g (hI.locAt_of_hist hg)
  have hcmd : ((e.cfg T₀).loc j).cmd ∈ g.output.1.supp :=
    NTrace.supp_mono hinp (by rw [hgi, NTrace.supp_snoc]; simp)
  -- the step at which `j` recorded `g`
  have hP : ∃ k, ((e.cfg (T₀ + k)).loc j).hist (B + 1) ≠ none :=
    ⟨T₁ - T₀, by rw [Nat.add_sub_cancel' hT₁0, hg]; simp⟩
  set k := Nat.find hP with hk
  have hk0 : k ≠ 0 := by
    intro h0
    have := Nat.find_spec hP
    rw [← hk, h0, Nat.add_zero] at this
    have := ((inv_at e T₀).1.loc j).hist_le (B + 1) this
    have := hS.bound j; omega
  obtain ⟨k', hk'⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hnone : ((e.cfg (T₀ + k')).loc j).hist (B + 1) = none := by
    by_contra hc'; exact Nat.find_min hP (by omega : k' < k) hc'
  obtain ⟨g', hg'⟩ := Option.ne_none_iff_exists'.1 (show ((e.cfg (T₀ + k' + 1)).loc j).hist (B + 1) ≠ none by
    have := Nat.find_spec hP; rw [← hk, hk'] at this; exact this)
  have hle : T₀ + k' + 1 ≤ T₁ := by
    by_contra hlt
    push Not at hlt
    have := Nat.find_min hP (show T₁ - T₀ < k by omega)
    rw [Nat.add_sub_cancel' hT₁0, hg] at this; simp at this
  have hgg : g' = g := by
    have := hist_mono_time hle hg'; rw [hg] at this; exact (Option.some.inj this).symm
  subst hgg
  have hcmd' : ((e.cfg (T₀ + k')).loc j).cmd = ((e.cfg T₀).loc j).cmd :=
    (hS.qstate hj (by omega)).cmd
  have hw := writeS_of_hist_set (inv_at e (T₀ + k')).1 (e.step_eq (T₀ + k')) hnone hg'
    ⟨hc, by rw [hcmd']; exact hcmd⟩
  exact (not_writeS_done (hS.pendQ j hj) (hS.infQ j hj) (by omega : T₀ ≤ T₀ + k' + 1)).1 hw

end Setup

end Alg1

end Podc.ConflictFreedom
