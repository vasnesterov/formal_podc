import Papers.PODC2011.AtMostOnceEffectiveness.Model

/-!
# Upper bound on effectiveness: `E_A(n, m, f) ≤ n − f`

Theorem 2.1 of Kentros–Kiayias (PODC 2011), which is Corollary 1 of Kentros, Kiayias, Nicolaou,
Shvartsman (2009): every algorithm that solves the at-most-once problem has effectiveness at most
`n − f`.

## Model

We use the model of `Model.lean`: deterministic processes, atomic registers, runs that may stutter,
and crashes as fairness exemptions (`Run.Fair F`: the processes of `F` need not be scheduled).

## Proof

1. *Two pending `do`s* (`AtMostOnce.not_mem_log`, `AtMostOnce.pendingJob_injOn`): in a reachable
   configuration, if process `p` is about to perform job `j ∈ {1, …, n}`, then `j` has not been
   performed yet (else stepping `p` performs `j` twice), and no other process `q` is about to
   perform the same job (else step `p`, then `q`). Hence if all processes of `F` are about to
   perform jobs of `{1, …, n}`, then `Do + |F| ≤ n` (`do_add_card_le`).
2. *Adversary* (`advStep`, `advRun`): round-robin; at time `k` look at `p = k mod m`. If `p` is
   crashed, stutter. If `p` is about to perform a job of `{1, …, n}` and fewer than `f` processes
   have been crashed, crash `p` (stutter, add `p` to the crash set). Otherwise step `p` (stutter if
   `p` has terminated).
3. *Invariants* (`adv_inv`): crashed processes are frozen in front of a `do` of `{1, …, n}`; at most
   `f` processes are crashed; while fewer than `f` are crashed, no job has been performed. Hence
   `Do ≤ n − f` at all times.
4. *Fairness* (`advRun_fair`): with `F∞` = all processes that are ever crashed (`|F∞| ≤ f`), every
   process outside `F∞` is offered a step at the times `m·k + p` and either steps or has terminated.

The hypotheses `0 < m` and `f ≤ n` of the paper are not needed (for `m = 0` the empty run works; for
`f > n` the adversary never reaches `f` crashes and no job is ever performed).
-/

set_option linter.unusedSectionVars false

namespace Podc.AtMostOnceEffectiveness

namespace Alg

variable {m : ℕ} {R V L : Type} [DecidableEq R] {A : Alg m R V L}

/-! ## Pending `do` actions -/

/-- The job of a `perform` step (`0` for the other steps). -/
def _root_.Podc.AtMostOnceEffectiveness.Step.job : Step R V L → ℕ
  | .perform j _ => j
  | _ => 0

/-- Process `p` is about to perform a job of `{1, …, n}` in `C`. -/
def Pending (A : Alg m R V L) (n : ℕ) (C : Config m R V L) (p : Fin m) : Prop :=
  ∃ j l, A.next p (C.loc p) = .perform j l ∧ j ∈ Finset.Icc 1 n

lemma step_perform {C : Config m R V L} {p : Fin m} {j : ℕ} {l : L}
    (h : A.next p (C.loc p) = .perform j l) :
    A.step C p = some { C with loc := Function.update C.loc p l, log := C.log ++ [(p, j)] } := by
  unfold step; rw [h]

/-- In a reachable configuration, a job that some process is about to perform has not been
performed yet. -/
lemma AtMostOnce.not_mem_log {n : ℕ} (hA : A.AtMostOnce n) {C : Config m R V L}
    (hC : A.Reachable C) {p : Fin m} {j : ℕ} {l : L} (h : A.next p (C.loc p) = .perform j l)
    (hj : j ∈ Finset.Icc 1 n) : j ∉ C.log.map Prod.snd := by
  intro hmem
  have h1 := hA _ (Reachable.step hC (step_perform h)) j hj
  have h2 := List.count_pos_iff.mpr hmem
  simp only [List.map_append, List.map_cons, List.map_nil, List.count_append,
    List.count_singleton_self] at h1
  omega

/-- In a reachable configuration, two distinct processes are never about to perform the same job
of `{1, …, n}`. -/
lemma AtMostOnce.pending_ne {n : ℕ} (hA : A.AtMostOnce n) {C : Config m R V L}
    (hC : A.Reachable C) {p q : Fin m} (hpq : p ≠ q) {j : ℕ} {l l' : L}
    (hp : A.next p (C.loc p) = .perform j l) (hq : A.next q (C.loc q) = .perform j l')
    (hj : j ∈ Finset.Icc 1 n) : False := by
  have hs := step_perform hp
  have hq' : A.next q
      (({ C with loc := Function.update C.loc p l, log := C.log ++ [(p, j)] } :
        Config m R V L).loc q) = .perform j l' := by
    simpa [Function.update_of_ne (Ne.symm hpq)] using hq
  exact hA.not_mem_log (Reachable.step hC hs) hq' hj (by simp)

/-- If all processes of `F` are about to perform jobs of `{1, …, n}` in a reachable configuration,
then the jobs performed so far and the processes of `F` together number at most `n`. -/
lemma AtMostOnce.do_add_card_le {n : ℕ} (hA : A.AtMostOnce n) {C : Config m R V L}
    (hC : A.Reachable C) (F : Finset (Fin m)) (hF : ∀ q ∈ F, A.Pending n C q) :
    Do n C + F.card ≤ n := by
  classical
  set g : Fin m → ℕ := fun q => (A.next q (C.loc q)).job
  have hg : ∀ q ∈ F, ∃ l, A.next q (C.loc q) = .perform (g q) l ∧ g q ∈ Finset.Icc 1 n := by
    intro q hq
    obtain ⟨j, l, h, hj⟩ := hF q hq
    have : g q = j := by simp only [g, h, Step.job]
    exact ⟨l, this ▸ h, this ▸ hj⟩
  have hmaps : Set.MapsTo g F (Finset.Icc 1 n \ jobs n C : Finset ℕ) := by
    intro q hq
    obtain ⟨l, h, hj⟩ := hg q hq
    simp only [Finset.coe_sdiff, Set.mem_sdiff, Finset.mem_coe, jobs, Finset.mem_filter, not_and]
    exact ⟨hj, fun _ => hA.not_mem_log hC h hj⟩
  have hinj : Set.InjOn g F := by
    intro q hq q' hq' hqq'
    by_contra hne
    obtain ⟨l, h, hj⟩ := hg q hq
    obtain ⟨l', h', _⟩ := hg q' hq'
    rw [← hqq'] at h'
    exact hA.pending_ne hC hne h h' hj
  have h1 := Finset.card_le_card_of_injOn g hmaps hinj
  have h2 : jobs n C ⊆ Finset.Icc 1 n := Finset.filter_subset _ _
  rw [Finset.card_sdiff_of_subset h2, Nat.card_Icc] at h1
  have h3 := Finset.card_le_card h2
  rw [Nat.card_Icc] at h3
  unfold Do
  omega

/-- A step that is not a `do` of a job of `{1, …, n}` does not change the performed jobs. -/
lemma jobs_step_of_not_pending {n : ℕ} {C C' : Config m R V L} {p : Fin m}
    (h : A.step C p = some C') (hp : ¬ A.Pending n C p) : jobs n C' = jobs n C := by
  unfold step at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  case h_3 j l heq =>
    have hj : j ∉ Finset.Icc 1 n := fun hj => hp ⟨j, l, heq, hj⟩
    unfold jobs
    apply Finset.filter_congr
    intro x hx
    have : x ≠ j := fun h => hj (h ▸ hx)
    simp [this]
  all_goals rfl

/-! ## The adversary -/

section Adversary

variable (A) (n f : ℕ) (hm : 0 < m)

open Classical in
/-- One step of the adversary at time `k` in scheduler state `s = (C, F)` (`F` = crashed
processes): returns the event and the new scheduler state. -/
noncomputable def advStep (k : ℕ) (s : Config m R V L × Finset (Fin m)) :
    Option (Fin m) × Config m R V L × Finset (Fin m) :=
  let p : Fin m := ⟨k % m, Nat.mod_lt _ hm⟩
  if p ∈ s.2 then (none, s)
  else if A.Pending n s.1 p ∧ s.2.card < f then (none, s.1, insert p s.2)
  else match A.step s.1 p with
    | some C' => (some p, C', s.2)
    | none => (none, s)

/-- The scheduler state (configuration, crashed processes) at time `k`. -/
noncomputable def advState : ℕ → Config m R V L × Finset (Fin m)
  | 0 => (A.init, ∅)
  | k + 1 => (advStep A n f hm k (advState k)).2

lemma advState_succ (k : ℕ) :
    advState A n f hm (k + 1) = (advStep A n f hm k (advState A n f hm k)).2 := rfl

/-- The three possible moves of the adversary: stutter (the scheduled process is crashed or has
terminated), crash the scheduled process, or step it. -/
lemma advStep_cases (k : ℕ) (s : Config m R V L × Finset (Fin m)) :
    (advStep A n f hm k s = (none, s) ∧
      ((⟨k % m, Nat.mod_lt _ hm⟩ : Fin m) ∈ s.2 ∨ A.Halted s.1 ⟨k % m, Nat.mod_lt _ hm⟩)) ∨
    (advStep A n f hm k s = (none, s.1, insert ⟨k % m, Nat.mod_lt _ hm⟩ s.2) ∧
      A.Pending n s.1 ⟨k % m, Nat.mod_lt _ hm⟩ ∧ s.2.card < f) ∨
    (∃ C', advStep A n f hm k s = (some ⟨k % m, Nat.mod_lt _ hm⟩, C', s.2) ∧
      A.step s.1 ⟨k % m, Nat.mod_lt _ hm⟩ = some C' ∧ (⟨k % m, Nat.mod_lt _ hm⟩ : Fin m) ∉ s.2 ∧
      ¬ (A.Pending n s.1 ⟨k % m, Nat.mod_lt _ hm⟩ ∧ s.2.card < f)) := by
  unfold advStep
  dsimp only
  split_ifs with h1 h2
  · exact Or.inl ⟨rfl, Or.inl h1⟩
  · exact Or.inr (Or.inl ⟨rfl, h2⟩)
  · split
    next C' hC' => exact Or.inr (Or.inr ⟨C', rfl, hC', h1, h2⟩)
    next hC' =>
      refine Or.inl ⟨rfl, Or.inr ?_⟩
      by_contra hh
      exact step_ne_none_iff.mpr hh hC'

/-- The run produced by the adversary. -/
noncomputable def advRun : A.Run where
  cfg k := (advState A n f hm k).1
  ev k := (advStep A n f hm k (advState A n f hm k)).1
  cfg_zero := rfl
  cfg_succ k := by
    show A.stepO (advState A n f hm k).1 (advStep A n f hm k (advState A n f hm k)).1 =
      some (advStep A n f hm k (advState A n f hm k)).2.1
    rcases advStep_cases A n f hm k (advState A n f hm k) with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨C', h, hs, -⟩
    · rw [h]; rfl
    · rw [h]; rfl
    · rw [h]; exact hs

lemma advCrashed_mono {k k' : ℕ} (hk : k ≤ k') :
    (advState A n f hm k).2 ⊆ (advState A n f hm k').2 := by
  induction k', hk using Nat.le_induction with
  | base => exact subset_rfl
  | succ k' _ ih =>
    refine ih.trans ?_
    rw [advState_succ]
    rcases advStep_cases A n f hm k' (advState A n f hm k') with
      ⟨h, -⟩ | ⟨h, -⟩ | ⟨C', h, -⟩ <;> rw [h]
    · exact Finset.subset_insert _ _

/-- The invariants of the adversary: crashed processes are frozen in front of a `do` of
`{1, …, n}`, at most `f` processes are crashed, and no job is performed while fewer than `f`
processes are crashed. -/
lemma adv_inv (k : ℕ) :
    (∀ q ∈ (advState A n f hm k).2, A.Pending n (advState A n f hm k).1 q) ∧
    (advState A n f hm k).2.card ≤ f ∧
    ((advState A n f hm k).2.card < f → jobs n (advState A n f hm k).1 = ∅) := by
  induction k with
  | zero => simp [advState, jobs, init]
  | succ k ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    rw [advState_succ]
    rcases advStep_cases A n f hm k (advState A n f hm k) with
      ⟨h, -⟩ | ⟨h, hP, hlt⟩ | ⟨C', h, hs, hp, hnot⟩ <;> rw [h]
    · exact ⟨ih1, ih2, ih3⟩
    · refine ⟨?_, ?_, fun _ => ih3 hlt⟩
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        exacts [hP, ih1 q hq]
      · exact (Finset.card_insert_le _ _).trans (by omega)
    · refine ⟨?_, ih2, ?_⟩
      · intro q hq
        obtain ⟨j, l, h1, h2⟩ := ih1 q hq
        refine ⟨j, l, ?_, h2⟩
        rw [step_loc_ne hs (fun h => hp (h ▸ hq))]
        exact h1
      · intro hlt
        rw [jobs_step_of_not_pending hs (fun hP => hnot ⟨hP, hlt⟩)]
        exact ih3 hlt

/-- Against the adversary, at most `n − f` jobs are performed at any time. -/
lemma adv_do_le (hA : A.AtMostOnce n) (k : ℕ) : Do n (advState A n f hm k).1 ≤ n - f := by
  obtain ⟨h1, h2, h3⟩ := adv_inv A n f hm k
  rcases lt_or_eq_of_le h2 with hlt | heq
  · simp [Do, h3 hlt]
  · have := hA.do_add_card_le (C := (advState A n f hm k).1) ((advRun A n f hm).reachable k) _ h1
    omega

open Classical in
/-- The final crash set: all processes that the adversary ever crashes. -/
noncomputable def advFinal : Finset (Fin m) :=
  Finset.univ.filter (fun q => ∃ k, q ∈ (advState A n f hm k).2)

lemma advFinal_card_le : (advFinal A n f hm).card ≤ f := by
  have : ∀ q ∈ advFinal A n f hm, ∃ k, q ∈ (advState A n f hm k).2 := by
    intro q hq; simpa [advFinal] using hq
  choose! t ht using this
  have hsub : advFinal A n f hm ⊆ (advState A n f hm ((advFinal A n f hm).sup t)).2 :=
    fun q hq => advCrashed_mono A n f hm (Finset.le_sup hq) (ht q hq)
  exact (Finset.card_le_card hsub).trans (adv_inv A n f hm _).2.1

/-- The adversary's run is fair with respect to its final crash set. -/
lemma advRun_fair : (advRun A n f hm).Fair (advFinal A n f hm) := by
  intro p hp k
  have hpk : ∀ k, p ∉ (advState A n f hm k).2 := fun k hk =>
    hp (by simp only [advFinal, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨k, hk⟩)
  refine ⟨m * k + p.val, by nlinarith, ?_⟩
  have hp' : (⟨(m * k + p.val) % m, Nat.mod_lt _ hm⟩ : Fin m) = p := by
    ext; simp [Nat.mod_eq_of_lt p.isLt]
  have hc := advStep_cases A n f hm (m * k + p.val) (advState A n f hm (m * k + p.val))
  rw [hp'] at hc
  rcases hc with ⟨h, h'⟩ | ⟨h, -⟩ | ⟨C', h, -⟩
  · rcases h' with h' | h'
    · exact absurd h' (hpk _)
    · exact Or.inr h'
  · refine absurd ?_ (hpk (m * k + p.val + 1))
    rw [advState_succ, h]
    exact Finset.mem_insert_self _ _
  · left
    show (advStep A n f hm _ (advState A n f hm _)).1 = some p
    rw [h]

end Adversary

end Alg

/-! ## Theorem 2.1 -/

/-- Theorem 2.1 of [Kentros–Kiayias] (Corollary 1 of Kentros et al. 2009): for every algorithm
solving the at-most-once problem, `E_A(n, m, f) ≤ n − f`.

The paper's standing assumptions `0 < m` and `f ≤ n` (indeed `f < m`) are not needed. -/
theorem effectiveness_le_sub {m : ℕ} {R V L : Type} [DecidableEq R] (A : Alg m R V L) (n f : ℕ)
    (hA : A.AtMostOnce n) : A.effectiveness n f ≤ n - f := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- no processes: the empty (stuttering) run performs no job
    let r : A.Run :=
      { cfg := fun _ => A.init, ev := fun _ => none, cfg_zero := rfl, cfg_succ := fun _ => rfl }
    have hmem : r.Do n ∈
        {d | ∃ (F : Finset (Fin 0)) (r : A.Run), F.card ≤ f ∧ r.Fair F ∧ r.Do n = d} :=
      ⟨∅, r, by simp, fun p => p.elim0, rfl⟩
    refine (Nat.sInf_le hmem).trans ?_
    rw [r.do_eq_of_stutter n (K := 0) (fun _ _ => rfl)]
    simp [Alg.Do, Alg.jobs, r, Alg.init]
  · have hmem : (Alg.advRun A n f hm).Do n ∈
        {d | ∃ (F : Finset (Fin m)) (r : A.Run), F.card ≤ f ∧ r.Fair F ∧ r.Do n = d} :=
      ⟨Alg.advFinal A n f hm, Alg.advRun A n f hm, Alg.advFinal_card_le A n f hm,
        Alg.advRun_fair A n f hm, rfl⟩
    refine (Nat.sInf_le hmem).trans ?_
    exact (Alg.advRun A n f hm).do_le_of_forall n _ (Alg.adv_do_le A n f hm hA)

end Podc.AtMostOnceEffectiveness
