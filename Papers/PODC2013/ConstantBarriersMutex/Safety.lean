import Papers.PODC2013.ConstantBarriersMutex.Invariant

/-!
# Safety: Lemma 2 (repaired), Corollaries 3 and 4, Lemma 5(a)
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

/-- **Lemma 2(d) under TSO.** At most one process is in the critical section or in its exit
section, where (Definition 1) the exit section ends when the write of statement 43 or 48 is
*performed*. -/
theorem lemma2d {s : Cfg h} (hs : Reachable s) {p q : Proc h} (hp : s.InCSX p) (hq : s.InCSX q) :
    p = q :=
  (inv_reachable hs).uniq p q hp hq

/-- **Corollary 3 (mutual exclusion).** In every reachable configuration of Algorithm 1 under
TSO, at most one process is in the critical section. -/
theorem mutual_exclusion {s : Cfg h} (hs : Reachable s) {p q : Proc h} (hp : s.pc p = .cs)
    (hq : s.pc q = .cs) : p = q :=
  lemma2d hs (Or.inl hp) (Or.inl hq)

/-- **Lemma 2(a).** A process in the critical section owns the lock (in memory). -/
theorem lemma2a {s : Cfg h} (hs : Reachable s) {p : Proc h} (hp : s.pc p = .cs) :
    s.mem.lock = some p := by
  have hL := (inv_reachable hs).loc p
  unfold LI at hL; rw [hp] at hL; exact hL.2.2

/-- **Lemma 2(b), repaired for TSO.** A process in its exit section owns the lock (in memory),
except after its write `lock ← next` of statement 47 has been performed; then the lock owner is
the process it dequeued at statement 45, which is in its entry section. -/
theorem lemma2b {s : Cfg h} (hs : Reachable s) {p : Proc h} (hp : (s.pc p).Exit) :
    s.mem.lock = some p ∨
      ∃ nx, s.pc p = .x48 nx ∧ s.buf p = [] ∧ s.mem.lock = some nx ∧ (s.pc nx).Entry := by
  have hI := inv_reachable hs
  rcases hI.incsx_iff.1 (Or.inr (Or.inl hp)) with hh | ⟨nx, hh⟩
  · exact Or.inl (hI.holds_lock hh)
  · right
    obtain ⟨h1, h2, -, -⟩ := hI.hands_lock hh
    have hnh : ¬ Holds s nx := fun h' => h2 (hI.uniq _ _ (hI.incsx_of_holds h')
      (hI.incsx_of_hands hh))
    rcases hh with ⟨h3, h4⟩ | ⟨h3, -⟩
    · exact ⟨nx, h3, h4, h1, (hI.lock_entry h1 hnh).1⟩
    · rw [h3] at hp; simp [PC.Exit] at hp

/-- **Lemma 2(c), repaired.** If `signal[r]` is set in memory and `r` is in its entry section
after its barrier (statements 23–27), then `r` owns the lock and no other process is in the
critical or exit section. (The paper states this for all `r` with `17 < pc(r) < 49`, which is
false: see `lemma2c_false` and `lemma2c_false_sc`.) -/
theorem lemma2c {s : Cfg h} (hs : Reachable s) {r : Proc h} (hsig : s.mem.signal r = true)
    (hr : (s.pc r).Waiting ∨ s.pc r = .e23) :
    s.mem.lock = some r ∧ ∀ q, q ≠ r → ¬ s.InCSX q := by
  have hI := inv_reachable hs
  have hL := hI.loc r
  have hE : (s.pc r).Entry := by
    rcases hr with hr | hr
    · revert hr; cases s.pc r <;> simp [PC.Waiting, PC.Entry]
    · rw [hr]; simp [PC.Entry]
  have hap : s.mem.apply r = true := by
    unfold LI at hL
    rcases hr with hr | hr
    · revert hr hL; cases s.pc r <;> simp [PC.Waiting]
    · rw [hr] at hL; exact hL.2
  obtain ⟨h1, h2⟩ := hI.sig r hsig hE hap
  refine ⟨h1, fun q hq hX => ?_⟩
  rcases hI.incsx_iff.1 hX with hh | ⟨nx, hh⟩
  · have := hI.holds_lock hh; rw [h1] at this; cases this; exact hq rfl
  · have := (hI.hands_lock hh).1; rw [h1] at this; cases this; exact h2 q hh

/-- **Corollary 4.** The promotion queue is accessed sequentially: a process at a statement
that accesses `promQ` (37, 42, 45) is the only process with pending writes to `promQ`, and it
reads the logical value of the queue (all writes of earlier lock holders are performed). -/
theorem corollary4 {s : Cfg h} (hs : Reachable s) {g : Proc h}
    (hg : (∃ l c rest, s.pc g = .x37 l c rest) ∨ s.pc g = .x42 ∨ s.pc g = .x45) :
    (∀ q, q ≠ g → ∀ w ∈ s.buf q, w.isPromQ = false) ∧ (s.view g).promQ = (lv s).promQ := by
  have hI := inv_reachable hs
  have hh : Holds s g := by
    unfold Holds; rcases hg with ⟨l, c, rest, hg⟩ | hg | hg <;> rw [hg] <;> trivial
  refine ⟨fun q hq w hw => ?_, by rw [hI.lv_of_holds hh]⟩
  have hnq : ¬ Holds s q := fun h' => hq (hI.holds_unique h' hh)
  exact (hI.nonholder_buf hnq w hw).promQ

/-- **Lemma 5(a).** A process that is enqueued to the promotion queue (statement 37) is in its
entry section at that point. -/
theorem lemma5a {s : Cfg h} (hs : Reachable s) {g c : Proc h} {l : ℕ} {rest : List (Proc h)}
    (hg : s.pc g = .x37 l c rest) : (s.pc c).Entry := by
  have := (inv_reachable hs).hc g
  unfold HC at this; rw [hg] at this; exact this.1

/-- Every process in the (logical) promotion queue is in its entry section. -/
theorem promQ_entry {s : Cfg h} (hs : Reachable s) {q : Proc h} (hq : q ∈ (lv s).promQ) :
    (s.pc q).Entry :=
  ((inv_reachable hs).pq q hq).1

end Podc.ConstantBarriersMutex
