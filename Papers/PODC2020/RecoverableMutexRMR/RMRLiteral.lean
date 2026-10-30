import Papers.PODC2020.RecoverableMutexRMR.RMR

/-!
# The RMR bound needs crashes to count as passage starts

The paper defines: "A passage of a process begins when it calls `Enter()` and ends when the
process crashes or when it finishes its following `Exit()` call", and claims (Theorems 1, 2)
that "the total number of RMRs incurred in any execution in which `m` passages begin is
`O(m)`". Read literally, steps of `Recover()` after a crash belong to no passage, and the claim
fails: a single process that calls `Enter()` once, reaches the critical section and then crashes
in the critical section again and again re-enters it each time through `Recover()` (line 20),
executing `D.FAI()` (line 15, an RMR in both the CC and the DSM model) each time. Only one
passage begins, but the number of RMRs is unbounded.

With the standard convention that every crash also starts a new passage (as `rmr_bound` does),
the bound holds.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

namespace Literal

/-- One process; 15 steps lead it into the critical section, then it repeats
"crash, line 15, line 16, line 18" forever. -/
def sched (t : ℕ) : Ev Unit :=
  if t < 15 then .step () else if (t - 15) % 4 = 0 then .crash () else .step ()

lemma cs15 : (exec sched 15).pc () = .cs ∧ ((exec sched 15).W ()).2 = true ∧
    (exec sched 15).X () = false := by
  decide

lemma pc_le15 (t : ℕ) (ht : 0 < t) (ht' : t ≤ 15) : (exec sched t).pc () ≠ .rem := by
  interval_cases t <;> decide

lemma crash_cs' {s : Cfg Unit} (h : s.pc () = .cs) :
    (s.crash ()).pc () = .r15 ∧ (s.crash ()).W = s.W ∧ (s.crash ()).X = s.X := by
  simp [Cfg.crash, h]

lemma step_r15' {s : Cfg Unit} (h : s.pc () = .r15) :
    (s.step ()).pc () = .r16 ∧ (s.step ()).W = s.W ∧ (s.step ()).X = s.X := by
  simp [Cfg.step, h]

lemma step_r16' {s : Cfg Unit} (h : s.pc () = .r16) (hX : s.X () = false) :
    (s.step ()).pc () = .r18 ∧ (s.step ()).W = s.W ∧ (s.step ()).X = s.X := by
  simp [Cfg.step, h, hX]

lemma step_r18' {s : Cfg Unit} (h : s.pc () = .r18) (hW : (s.W ()).2 = true) :
    (s.step ()).pc () = .cs ∧ (s.step ()).W = s.W ∧ (s.step ()).X = s.X := by
  simp [Cfg.step, h, hW]

/-- One round of the loop on a configuration in the critical section. -/
lemma round (s : Cfg Unit) (h1 : s.pc () = .cs) (h2 : (s.W ()).2 = true) (h3 : s.X () = false) :
    (s.crash ()).pc () = .r15 ∧ ((s.crash ()).step ()).pc () = .r16 ∧
    (((s.crash ()).step ()).step ()).pc () = .r18 ∧
    ((((s.crash ()).step ()).step ()).step ()).pc () = .cs ∧
    (((((s.crash ()).step ()).step ()).step ()).W ()).2 = true ∧
    ((((s.crash ()).step ()).step ()).step ()).X () = false ∧
    rmrCost (s.crash ()) () = 1 := by
  obtain ⟨c1, c1W, c1X⟩ := crash_cs' h1
  obtain ⟨c2, c2W, c2X⟩ := step_r15' c1
  obtain ⟨c3, c3W, c3X⟩ := step_r16' c2 (by rw [c2X, c1X]; exact h3)
  obtain ⟨c4, c4W, c4X⟩ := step_r18' c3 (by rw [c3W, c2W, c1W]; exact h2)
  refine ⟨c1, c2, c3, c4, by rw [c4W, c3W, c2W, c1W]; exact h2,
    by rw [c4X, c3X, c2X, c1X]; exact h3, by simp [rmrCost, c1]⟩

/-- The loop: at time `15 + 4k` the process is in the critical section. -/
lemma loop (k : ℕ) : (exec sched (15 + 4 * k)).pc () = .cs ∧
    ((exec sched (15 + 4 * k)).W ()).2 = true ∧ (exec sched (15 + 4 * k)).X () = false ∧
    k ≤ totalRMR sched (15 + 4 * k) ∧
    (∀ t, 0 < t → t ≤ 15 + 4 * k → (exec sched t).pc () ≠ .rem) := by
  induction k with
  | zero =>
    exact ⟨cs15.1, cs15.2.1, cs15.2.2, by simp, fun t h1 h2 => pc_le15 t h1 (by omega)⟩
  | succ k ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := ih
    set n := 15 + 4 * k with hn
    have e0 : sched n = .crash () := by simp [sched, hn]
    have e1 : sched (n + 1) = .step () := by simp [sched, hn]; omega
    have e2 : sched (n + 2) = .step () := by simp [sched, hn]; omega
    have e3 : sched (n + 3) = .step () := by simp [sched, hn]; omega
    have E1 : exec sched (n + 1) = (exec sched n).crash () := by rw [exec_succ, e0]; rfl
    have E2 : exec sched (n + 2) = (exec sched (n + 1)).step () := by
      rw [show n + 2 = (n + 1) + 1 from rfl, exec_succ, e1]; rfl
    have E3 : exec sched (n + 3) = (exec sched (n + 2)).step () := by
      rw [show n + 3 = (n + 2) + 1 from rfl, exec_succ, e2]; rfl
    have E4 : exec sched (n + 4) = (exec sched (n + 3)).step () := by
      rw [show n + 4 = (n + 3) + 1 from rfl, exec_succ, e3]; rfl
    obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := round (exec sched n) h1 h2 h3
    rw [← E1] at r1 r2 r3 r4 r5 r6 r7
    rw [← E2] at r2 r3 r4 r5 r6
    rw [← E3] at r3 r4 r5 r6
    rw [← E4] at r4 r5 r6
    have hk : 15 + 4 * (k + 1) = n + 4 := by rw [hn]; ring
    rw [hk]
    refine ⟨r4, r5, r6, ?_, ?_⟩
    · have hc : evCost (exec sched (n + 1)) (sched (n + 1)) = 1 := by
        rw [e1]; simpa [evCost] using r7
      have : totalRMR sched (n + 4) ≥ totalRMR sched n +
          evCost (exec sched (n + 1)) (sched (n + 1)) := by
        unfold totalRMR
        rw [show n + 4 = n + 1 + 1 + 1 + 1 from rfl]
        simp only [Finset.sum_range_succ]
        omega
      omega
    · intro t ht1 ht2
      by_cases h : t ≤ n
      · exact h5 t ht1 h
      · have : t = n + 1 ∨ t = n + 2 ∨ t = n + 3 ∨ t = n + 4 := by omega
        rcases this with rfl | rfl | rfl | rfl
        · rw [r1]; simp
        · rw [r2]; simp
        · rw [r3]; simp
        · rw [r4]; simp

lemma numEnter_le_one (k : ℕ) : numEnter sched (15 + 4 * k) ≤ 1 := by
  unfold numEnter
  have : (Finset.range (15 + 4 * k)).filter
      (fun u => ∃ p, sched u = .step p ∧ (exec sched u).pc p = .rem) ⊆ {0} := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu
    obtain ⟨hu, p, -, hp⟩ := hu
    cases p
    simp only [Finset.mem_singleton]
    by_contra h
    exact (loop k).2.2.2.2 u (by omega) (by omega) hp
  exact (Finset.card_le_card this).trans (by simp)

/-- **The literal reading of Theorems 1–2 fails**: in the execution `sched` exactly one passage
begins (one invocation of `Enter()`, no `Exit()`), yet the number of RMRs is unbounded (in the
DSM model; line 15 is an RMR in the CC model as well). -/
theorem rmr_literal_unbounded :
    (∀ t, numEnter sched t ≤ 1) ∧ ∀ N, ∃ t, N ≤ totalRMR sched t := by
  refine ⟨fun t => ?_, fun N => ⟨15 + 4 * N, (loop N).2.2.2.1⟩⟩
  have hmono : numEnter sched t ≤ numEnter sched (15 + 4 * t) := by
    unfold numEnter
    apply Finset.card_le_card
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_range] at hu ⊢
    exact ⟨by omega, hu.2⟩
  exact hmono.trans (numEnter_le_one t)

end Literal

end Podc.RecoverableMutexRMR
