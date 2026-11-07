import Papers.PODC2012.CloserLookFT.Colorless

/-!
# Lemma 6.1 of Taubenfeld (PODC 2012): liveness of `A'`

Crash faults and resilience notions are those of
`Podc/Computability/Distributed/SharedMemory/Resilience.lean` (a crashed process stops forever
while pending; a *starved* process is pending forever although it keeps taking steps). The
admissible executions are one-shot with required participation.

Proof of `resilient_withOutput` (`A` weakly `t`-resilient ⇒ `A'` `t`-resilient, `t ≤ n - 2`):
let `p` be starved in an admissible infinite execution `e` of `A'`.
1. `starved_step`, `starved_infinitely`: from some time on `p` alternates between reading `⊥`
   from `output` and taking an *access* step of `A` (reading a value would make it adopt and
   return; `A` returning would make it write and return).
2. `outReg_eq_none_of_starved`: `output` is never written (once written it stays non-`⊥`, but
   `p` keeps reading `⊥`). Hence nobody adopts, nobody writes and nobody returns (`no_ret`,
   `not_write`) — in particular no process is a "crash" of `A` caused by adopting.
3. `projE`, `exists_projExec`: the simulated labels of `e` form an infinite execution `eA` of `A`
   (`p`'s infinitely many steps of `A` make it infinite); it is one-shot
   (`oneShotExec_proj`), has the same participants, no returns, and every process crashed in
   `eA` is crashed in `e` (a process that is not crashed in `e` is starved there and takes
   infinitely many steps of `A`).
4. Weak resilience of `A` on `eA` (≤ `t` crashes; with a crash, ≥ `n - t ≥ 2` correct
   processes) yields a correct process of `eA` that returns — impossible.
-/

set_option linter.unusedSectionVars false

namespace Podc.CloserLookFT

open Cslib.SharedMemory Cslib.SharedMemory.Impl

variable {P : Type} [DecidableEq P] {In Out : Type} [Inhabited Out]
  {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type} {A : Impl (taskObj In Out) B P L}

/-- A step of a process `q` that is pending before and after it. -/
lemma qstep {C D : OutCfg In Out B P L} {ℓ : Label P (taskObj In Out)} {q : P}
    (h : (withOutput A).step C ℓ = some D) (hℓ : ℓ.proc = q) (hC : C.pend q ≠ none)
    (hD : D.pend q ≠ none) :
    ℓ = .tau q ∧
    (((C.loc q).2.2 = .check ∧ D.loc q = checkNext (C.loc q) (outReg C)) ∨
     ((C.loc q).2.2 = .exec ∧ (D.loc q).2.2 = .check ∧
        ∃ i o k, A.act q (C.loc q).1 = .access i o k) ∨
     ((C.loc q).2.2 = .exec ∧ ∃ r l', A.act q (C.loc q).1 = .ret r l' ∧
        (D.loc q).2.2 = .fin r)) := by
  rcases wstep_cases h with ⟨p, o, rfl, hp, -, rfl⟩ | ⟨p, rfl, hp, hph, rfl⟩ |
    ⟨p, i, o, k, rfl, hp, hph, hA, rfl⟩ | ⟨p, r, l', rfl, hp, hph, hA, rfl⟩ |
    ⟨p, r, rfl, hp, hph, rfl⟩
  · simp only [Label.proc] at hℓ; subst hℓ; exact absurd hp hC
  · simp only [Label.proc] at hℓ; subst hℓ; exact ⟨rfl, Or.inl ⟨hph, by simp⟩⟩
  · simp only [Label.proc] at hℓ; subst hℓ
    exact ⟨rfl, Or.inr (Or.inl ⟨hph, by simp, i, o, k, hA⟩)⟩
  · simp only [Label.proc] at hℓ; subst hℓ
    exact ⟨rfl, Or.inr (Or.inr ⟨hph, r, l', hA, by simp⟩)⟩
  · simp only [Label.proc] at hℓ; subst hℓ; simp at hD

/-- Labels simulated by a step. -/
lemma projStep_mem {C : OutCfg In Out B P L} {ℓ ℓ' : Label P (taskObj In Out)}
    (h : ℓ' ∈ projStep A C ℓ) :
    ℓ'.proc = ℓ.proc ∧ (∀ q o, ℓ' = .inv q o → ℓ = .inv q o) ∧
      (∀ q r, ℓ' = .ret q r → ∃ l', ℓ = .tau q ∧ (C.loc q).2.2 = .exec ∧
        A.act q (C.loc q).1 = .ret r l') := by
  cases ℓ with
  | inv p o => simp only [projStep, List.mem_singleton] at h; subst h; simp
  | ret p r => simp [projStep] at h
  | tau p =>
    simp only [projStep] at h
    split at h
    · rename_i hph
      split at h
      · simp only [List.mem_singleton] at h; subst h; simp [Label.proc]
      · rename_i r l' hA
        simp only [List.mem_singleton] at h; subst h
        refine ⟨rfl, by simp, ?_⟩
        rintro q r' ⟨⟩
        exact ⟨l', rfl, hph, hA⟩
    · simp at h

section Exec

variable (e : (withOutput A).InfExec)

/-- The structural invariant along an infinite execution. -/
lemma outInv_cfg (j : ℕ) : OutInv (e.cfg j) := outInv_of_run (e.run_pre j)

/-- `output`, once written, stays non-`⊥`. -/
lemma outReg_mono {j j' : ℕ} (h : j ≤ j') (hj : outReg (e.cfg j) ≠ none) :
    outReg (e.cfg j') ≠ none := by
  induction j', h using Nat.le_induction with
  | base => exact hj
  | succ n _ ih => exact outReg_ne_none_step (e.step_eq n) ih

variable {e}

/-- From some time on, a starved process of `A'` is pending in phase `check` or `exec`. -/
lemma starved_phase {q : P} (hs : e.Starved q) : ∃ t0, ∀ j ≥ t0, (e.cfg j).pend q ≠ none ∧
    (((e.cfg j).loc q).2.2 = .check ∨ ((e.cfg j).loc q).2.2 = .exec) := by
  obtain ⟨⟨t0, hb⟩, hnc⟩ := hs
  refine ⟨t0, fun j hj => ⟨hb j hj, ?_⟩⟩
  rcases hph : ((e.cfg j).loc q).2.2 with _ | _ | _ | r | v
  · exact absurd ((outInv_cfg e j q).2.1 hph) (hb j hj)
  · exact Or.inl rfl
  · exact Or.inr rfl
  all_goals
    obtain ⟨j', hj', hproc, hloc, -⟩ := e.exists_first_step hnc (hb j hj)
    obtain ⟨-, h⟩ := qstep (e.step_eq j') hproc (hb j' (by omega)) (hb (j' + 1) (by omega))
    rw [hloc, hph] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h

/-- The steps of a starved process of `A'`: it alternates between reading `⊥` from `output` and
taking a step of `A`. -/
lemma starved_step {q : P} (hs : e.Starved q) : ∃ t0, ∀ j ≥ t0, (e.lbl j).proc = q →
    e.lbl j = .tau q ∧
    ((((e.cfg j).loc q).2.2 = .check ∧ outReg (e.cfg j) = none ∧
        ((e.cfg (j + 1)).loc q).2.2 = .exec) ∨
     (((e.cfg j).loc q).2.2 = .exec ∧ ((e.cfg (j + 1)).loc q).2.2 = .check ∧
        ∃ i o k, A.act q ((e.cfg j).loc q).1 = .access i o k)) := by
  obtain ⟨t0, ht0⟩ := starved_phase hs
  refine ⟨t0, fun j hj hproc => ?_⟩
  obtain ⟨hl, h⟩ := qstep (e.step_eq j) hproc (ht0 j hj).1 (ht0 (j + 1) (by omega)).1
  refine ⟨hl, ?_⟩
  have hnext := (ht0 (j + 1) (by omega)).2
  rcases h with ⟨hph, hD⟩ | ⟨hph, hD, hA⟩ | ⟨hph, r, l', hA, hD⟩
  · left
    refine ⟨hph, ?_, ?_⟩
    · cases hx : outReg (e.cfg j) with
      | none => rfl
      | some v => rw [hD, hx] at hnext; simp [checkNext] at hnext
    · cases hx : outReg (e.cfg j) with
      | none => rw [hD, hx]; rfl
      | some v => rw [hD, hx] at hnext; simp [checkNext] at hnext
  · exact Or.inr ⟨hph, hD, hA⟩
  · rw [hD] at hnext; simp at hnext

/-- A starved process of `A'` takes infinitely many steps of `A` and reads `⊥` from `output`
infinitely often. -/
lemma starved_infinitely {q : P} (hs : e.Starved q) (N : ℕ) :
    (∃ j ≥ N, projStep A (e.cfg j) (e.lbl j) = [.tau q]) ∧ ∃ j ≥ N, outReg (e.cfg j) = none := by
  obtain ⟨t0, ht0⟩ := starved_step hs
  obtain ⟨t1, ht1⟩ := starved_phase hs
  have hnc := hs.2
  set j0 := max N (max t0 t1)
  obtain ⟨j1, hj1, hp1, hl1, -⟩ := e.exists_first_step hnc (ht1 j0 (by omega)).1
  obtain ⟨hl, h1⟩ := ht0 j1 (by omega) hp1
  obtain ⟨j2, hj2, hp2, hl2, -⟩ := e.exists_first_step hnc (ht1 (j1 + 1) (by omega)).1
  obtain ⟨hl', h2⟩ := ht0 j2 (by omega) hp2
  have hproj : ∀ j, e.lbl j = .tau q → ((e.cfg j).loc q).2.2 = .exec →
      (∃ i o k, A.act q ((e.cfg j).loc q).1 = .access i o k) →
      projStep A (e.cfg j) (e.lbl j) = [.tau q] := by
    rintro j hl hph ⟨i, o, k, hA⟩
    rw [hl]; simp only [projStep, hph, hA]
  rcases h1 with ⟨hph1, hr1, hn1⟩ | ⟨hph1, hn1, hA1⟩
  · rw [← hl2] at hn1
    rcases h2 with ⟨hph2, -, -⟩ | ⟨hph2, -, hA2⟩
    · rw [hph2] at hn1; cases hn1
    · exact ⟨⟨j2, by omega, hproj j2 hl' hph2 hA2⟩, ⟨j1, by omega, hr1⟩⟩
  · rw [← hl2] at hn1
    rcases h2 with ⟨hph2, hr2, -⟩ | ⟨hph2, -, -⟩
    · exact ⟨⟨j1, by omega, hproj j1 hl hph1 hA1⟩, ⟨j2, by omega, hr2⟩⟩
    · rw [hph2] at hn1; cases hn1

/-- If some process of `A'` is starved, nobody ever writes `output`. -/
lemma outReg_eq_none_of_starved {q : P} (hs : e.Starved q) (j : ℕ) : outReg (e.cfg j) = none := by
  by_contra h
  obtain ⟨j', hj', h'⟩ := (starved_infinitely hs j).2
  exact outReg_mono e hj' h h'

end Exec

/-! ## The projected execution of `A` -/

section Proj

variable (A) (e : (withOutput A).InfExec)

/-- The labels of `A` simulated by the first `k` steps of `e`. -/
def projE (k : ℕ) : List (Label P (taskObj In Out)) :=
  (List.range k).flatMap fun j => projStep A (e.cfg j) (e.lbl j)

variable {A e}

/-- One more step. -/
lemma projE_succ (k : ℕ) : projE A e (k + 1) = projE A e k ++ projStep A (e.cfg k) (e.lbl k) := by
  simp [projE, List.range_succ, List.flatMap_append]

/-- The simulated executions form a chain. -/
lemma projE_mono {k k' : ℕ} (h : k ≤ k') : projE A e k <+: projE A e k' := by
  induction k', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => rw [projE_succ]; exact ih.trans (List.prefix_append _ _)

/-- Lengths of the simulated executions are monotone. -/
lemma length_projE_mono {k k' : ℕ} (h : k ≤ k') :
    (projE A e k).length ≤ (projE A e k').length :=
  (projE_mono h).length_le

/-- The simulated execution has the same invocations. -/
lemma opsOf_projE (k : ℕ) (q : P) : opsOf (projE A e k) q = opsOf (e.pre k) q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [projE_succ, InfExec.pre_succ, opsOf_append, opsOf_append, ih, opsOf_projStep]
    congr 1

/-- The simulated executions are executions of `A`, ending in the projected configuration. -/
lemma run_projE (hos : e.OneShotExec) (k : ℕ) : A.run (projE A e k) = some (projC (e.cfg k)) := by
  induction k with
  | zero => rw [e.cfg_zero]; rfl
  | succ k ih =>
    rw [projE_succ, Impl.run_append_of_eq A ih]
    refine sim_step (outInv_cfg e k) (e.step_eq k) (outInv_cond (e.run_pre k) ?_)
    rw [← InfExec.pre_succ]; exact hos (k + 1)

/-- If `p` is starved, the simulated execution of `A` is infinite. -/
lemma projE_unbounded {p : P} (hs : e.Starved p) (N : ℕ) : ∃ k, N ≤ (projE A e k).length := by
  induction N with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ N ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨j, hj, hjp⟩ := (starved_infinitely hs k).1
    refine ⟨j + 1, ?_⟩
    rw [projE_succ, List.length_append, hjp]
    have := length_projE_mono (A := A) (e := e) hj
    simp only [List.length_singleton]; omega

/-- The limit of the simulated executions: an infinite execution of `A`. -/
lemma exists_projExec (hos : e.OneShotExec) {p : P} (hs : e.Starved p) :
    ∃ eA : A.InfExec, ∀ k n (hn : n < (projE A e k).length), eA.lbl n = (projE A e k)[n] := by
  classical
  let g : ℕ → ℕ := fun N => Nat.find (projE_unbounded (A := A) hs N)
  have hg : ∀ N, N ≤ (projE A e (g N)).length := fun N => Nat.find_spec (projE_unbounded hs N)
  have hgmono : ∀ N, g N ≤ g (N + 1) := fun N =>
    Nat.find_mono fun k hk => le_trans (Nat.le_succ N) hk
  obtain ⟨eA, hlbl, -⟩ := A.exists_infExec_of_chain (fun N => projE A e (g N))
    (fun N => projE_mono (hgmono N)) hg (fun N => ⟨_, run_projE hos (g N)⟩)
  refine ⟨eA, fun k n hn => ?_⟩
  have hk : k ≤ g ((projE A e k).length + 1) := by
    by_contra hlt
    push Not at hlt
    have h1 := length_projE_mono (A := A) (e := e) hlt.le
    have h2 := hg ((projE A e k).length + 1)
    omega
  have hpre := projE_mono (A := A) (e := e) hk
  rw [hlbl _ n (lt_of_lt_of_le hn hpre.length_le)]
  exact (hpre.getElem hn).symm

end Proj

/-! ## Transfer of participation, crashes and one-shotness -/

section Transfer

variable {e : (withOutput A).InfExec} {eA : A.InfExec}
  (hE : ∀ k n (hn : n < (projE A e k).length), eA.lbl n = (projE A e k)[n])
include hE

/-- The label simulated by step `j` sits at position `|projE j|` of `eA`. -/
lemma lbl_projE {j : ℕ} {ℓ : Label P (taskObj In Out)}
    (h : projStep A (e.cfg j) (e.lbl j) = [ℓ]) : eA.lbl (projE A e j).length = ℓ := by
  rw [hE (j + 1) _ (by simp [projE_succ, h])]
  simp [projE_succ, h]

/-- Every label of `eA` is simulated by some step of `e`. -/
lemma lbl_mem (hunb : ∀ N, ∃ k, N ≤ (projE A e k).length) (n : ℕ) :
    ∃ j, eA.lbl n ∈ projStep A (e.cfg j) (e.lbl j) := by
  obtain ⟨k, hk⟩ := hunb (n + 1)
  rw [hE k n (by omega)]
  have := List.getElem_mem (l := projE A e k) (n := n) (by omega)
  simp only [projE, List.mem_flatMap] at this
  obtain ⟨j, -, hj⟩ := this
  exact ⟨j, hj⟩

/-- The projected execution is one-shot. -/
lemma oneShotExec_proj (hos : e.OneShotExec) (hunb : ∀ N, ∃ k, N ≤ (projE A e k).length) :
    eA.OneShotExec := by
  intro n q
  obtain ⟨k, hk⟩ := hunb n
  rw [eA.pre_eq_take hk (hE k)]
  have h1 : OneShot (projE A e k) := fun q => by rw [opsOf_projE]; exact hos k q
  have h2 : OneShot ((projE A e k).take n ++ (projE A e k).drop n) := by
    rwa [List.take_append_drop]
  exact h2.of_append q

end Transfer

/-- When `output` stays `⊥`, the step of a process writing `output` cannot occur. -/
lemma not_write {e : (withOutput A).InfExec} (hno : ∀ j, outReg (e.cfg j) = none) {j : ℕ}
    {q : P} {r : Out} {l' : L} (hl : e.lbl j = .tau q) (hph : ((e.cfg j).loc q).2.2 = .exec)
    (hA : A.act q ((e.cfg j).loc q).1 = .ret r l') : False := by
  have h := e.step_eq j
  rw [hl] at h
  have hp := (Impl.step_tau h).1
  rw [Impl.step_tau_eq_some hp (act_exec_ret hph hA)] at h
  have := hno (j + 1)
  rw [← Option.some.inj h] at this
  simp [outReg] at this

/-- When `output` stays `⊥`, no process of `A'` ever returns. -/
lemma no_ret {e : (withOutput A).InfExec} (hno : ∀ j, outReg (e.cfg j) = none) (j : ℕ) (q : P)
    (r : Out) : e.lbl j ≠ .ret q r := by
  intro hl
  have h := e.step_eq j
  rw [hl] at h
  rcases wstep_cases h with ⟨p, o, h', -⟩ | ⟨p, h', -⟩ | ⟨p, i, o, k, h', -⟩ |
    ⟨p, r', l', h', -⟩ | ⟨p, r', h', hp, hph, -⟩
  all_goals try cases h'
  obtain ⟨-, h2, h3⟩ := outInv_cfg e j q
  rcases hph with hph | hph | hph
  · exact h3 r (Or.inl hph) (hno j)
  · exact h3 r (Or.inr hph) (hno j)
  · exact hp (h2 hph)

/-! ## Liveness of `A'` -/

/-- **Liveness part of Lemma 6.1.** With required participation (`AllParticipate`), one-shot
executions and `t ≤ n - 2`: if `A` is weakly `t`-resilient then `A'` is `t`-resilient.

Proof: if a process `p` of `A'` were starved (pending forever, taking infinitely many steps),
it would read `⊥` from `output` infinitely often, so nobody ever writes `output`; then nobody
adopts and nobody returns, and `A'` projects to an infinite admissible execution of `A` with no
more crashes, at least as many correct processes, and no process that ever returns. Weak
resilience of `A` contradicts this. -/
theorem resilient_withOutput [Fintype P] {t : ℕ} (ht : t ≤ Fintype.card P - 2)
    (hW : A.WeaklyResilient (fun e => e.OneShotExec ∧ e.AllParticipate) t) :
    (withOutput A).Resilient (fun e => e.OneShotExec ∧ e.AllParticipate) t := by
  rintro e ⟨hos, hall⟩ hcr
  suffices h : ∀ p, ¬ e.Starved p by
    have : {p | e.Starved p} = ∅ := Set.eq_empty_of_forall_notMem h
    simp [this]
  intro p hp
  have hno := outReg_eq_none_of_starved hp
  have hunb := projE_unbounded (A := A) hp
  obtain ⟨eA, hE⟩ := exists_projExec hos hp
  have hpart : ∀ q, eA.Participates q ↔ e.Participates q := by
    intro q
    rw [InfExec.participates_iff_exists_inv, InfExec.participates_iff_exists_inv]
    constructor
    · rintro ⟨n, o, hn⟩
      obtain ⟨j, hj⟩ := lbl_mem hE hunb n
      rw [hn] at hj
      exact ⟨j, o, (projStep_mem hj).2.1 q o rfl⟩
    · rintro ⟨j, o, hj⟩
      exact ⟨_, o, lbl_projE hE (by rw [hj]; rfl)⟩
  have hnoA : ∀ n q r, eA.lbl n ≠ .ret q r := by
    intro n q r hn
    obtain ⟨j, hj⟩ := lbl_mem hE hunb n
    rw [hn] at hj
    obtain ⟨l', hl, hph, hA⟩ := (projStep_mem hj).2.2 q r rfl
    exact not_write hno hl hph hA
  have hcrash : ∀ q, eA.Crashed q → e.Crashed q := by
    intro q hq
    by_contra hnc
    obtain ⟨t₀, ht₀, hst⟩ := hq
    have hpe : e.Participates q := (hpart q).1 ⟨t₀, ht₀⟩
    have hs : e.Starved q :=
      ⟨InfExec.blocked_of_forall_ne_ret hpe (fun j r => no_ret hno j q r), hnc⟩
    obtain ⟨k, hk⟩ := hunb t₀
    obtain ⟨j, hj, hjp⟩ := (starved_infinitely hs k).1
    exact hst _ (le_trans hk (length_projE_mono hj)) (by rw [lbl_projE hE hjp]; rfl)
  have hcorr : ∀ q, e.Correct q → eA.Correct q := fun q hq =>
    ⟨(hpart q).2 hq.1, fun h => hq.2 (hcrash q h)⟩
  have hstarA : eA.Starved p :=
    ⟨InfExec.blocked_of_forall_ne_ret ((hpart p).2 hp.correct.1) (fun n r => hnoA n p r),
      fun h => hp.2 (hcrash p h)⟩
  have hadm : eA.OneShotExec ∧ eA.AllParticipate :=
    ⟨oneShotExec_proj hE hos hunb, fun q => (hpart q).2 (hall q)⟩
  have hcrle : {q | eA.Crashed q}.ncard ≤ {q | e.Crashed q}.ncard :=
    Set.ncard_le_ncard hcrash (Set.toFinite _)
  obtain ⟨h1, h2⟩ := hW eA hadm (hcrle.trans hcr)
  by_cases h0 : {q | eA.Crashed q}.ncard = 0
  · exact h1 h0 p hstarA
  · have hcorrle : {q | e.Correct q}.ncard ≤ {q | eA.Correct q}.ncard :=
      Set.ncard_le_ncard hcorr (Set.toFinite _)
    have hce : {q | e.Correct q} = {q | e.Crashed q}ᶜ := by
      ext q; simp [InfExec.Correct, hall q]
    have hsum := Set.ncard_add_ncard_compl {q | e.Crashed q}
    rw [← hce, Nat.card_eq_fintype_card] at hsum
    obtain ⟨q, hq, hqb⟩ := h2 (by omega)
    exact hqb (InfExec.blocked_of_forall_ne_ret hq.1 (fun n r => hnoA n q r))

end Podc.CloserLookFT
