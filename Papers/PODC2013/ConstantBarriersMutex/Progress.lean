import Papers.PODC2013.ConstantBarriersMutex.ProgressSteps

/-!
# Progress lemmas for fair executions (token progress, Lemma 5(b), reading in the exit section)

These are the liveness building blocks of the starvation-freedom proof (Lemma 7):

* `Run.handed_enters`: a process that was handed the lock eventually enters the CS (Lemma 6).
* `Run.lemma5b`: a process in the promotion queue eventually enters the CS (Lemma 5(b)).
* `Run.lock_none_of_no_entry`: if no process enters the CS after `T`, then `lock = −1` from
  some time on.
* `Run.enqueued_of_read`: a process `g` that enters the CS reads, in its exit section, the node
  `target (anc g l) j`; if that node holds `p₀` forever and `p₀` stays in its entry section
  with `apply[p₀]` set, then `p₀` is (eventually) in the promotion queue. Under fairness its
  hypotheses are contradictory: `Run.enters_of_read` (same situation, `p₀` in its entry section
  at `t₁` only) shows that `p₀` enters the critical section.

Auxiliary results: `Run.exit_progress` (a process in its critical/exit section returns to the
remainder section; measure `Prog.rkX`, no bounds on the local variables needed),
`Run.noent_lock` (without CS entries, eventually nobody is in its CS/exit section and
`lock = −1`), `Run.Q_enters` (Lemma 5(b) for the promotion order `BW.Q`: the index of a process
in `BW.Q` never increases and drops at every CS entry, so entries stop unless it enters).
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ} {r : Run h}

namespace Run

/-! ### Generic progress tools -/

/-- Progress by a measure for a fairly scheduled process `q`: the domain `Dom` keeps `q` outside
its remainder section, so `q` keeps taking steps. -/
lemma good_of_measure (hf : r.Fair) (q : Proc h) (Good Dom : ℕ → Prop) (μ : ℕ → ℕ) (T₀ : ℕ)
    (h₀ : Dom T₀) (hrem : ∀ t, Dom t → (r.s t).pc q ≠ .rem)
    (hstep : ∀ t ≥ T₀, Dom t → ¬ Good (t + 1) →
      Dom (t + 1) ∧ μ (t + 1) ≤ μ t ∧ (r.ev t = .step q → μ (t + 1) < μ t)) :
    ∃ t ≥ T₀, Good t := by
  by_contra H
  push Not at H
  have hD : ∀ t ≥ T₀, Dom t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact h₀
    | succ t ht ih => exact (hstep t ht ih (H (t + 1) (by omega))).1
  obtain ⟨t, ht, hg⟩ := exists_good_of_measure r.ev q
    (hf.inf_steps (T := T₀) (fun t ht => hrem t (hD t ht))) Good Dom μ T₀ h₀ hstep
  exact H t ht hg

/-- The first entry into the critical section between two times. -/
lemma exists_enters {x : Proc h} {a b : ℕ} (hab : a ≤ b) (ha : (r.s a).pc x ≠ .cs)
    (hb : (r.s b).pc x = .cs) : ∃ t, a ≤ t ∧ t < b ∧ BW.Enters r x t := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd hb ha
  | succ b hab ih =>
    by_cases hc : (r.s b).pc x = .cs
    · obtain ⟨t, h1, h2, h3⟩ := ih hc
      exact ⟨t, h1, by omega, h3⟩
    · exact ⟨b, hab, by omega, hc, hb⟩

lemma enters_ent {x : Proc h} {t : ℕ} (he : BW.Enters r x t) :
    (r.s (t + 1)).ent = (r.s t).ent + 1 := by
  have he' := he
  unfold BW.Enters at he'; rw [r.next_eq] at he' ⊢
  rcases (BW.enters_cases (r.inv t) (r.ev t) he'.1 he'.2).2.2 with ⟨-, -, h3⟩ | ⟨-, -, h3⟩ <;>
    rw [h3]

/-! ### Exit progress -/

lemma rkX_pos_of_incsx {s : Cfg h} {g : Proc h} (hg : s.InCSX g) : 0 < Prog.rkX (s.pc g) := by
  rcases hg with hg | hg | ⟨⟨o, hg⟩, -⟩
  · rw [hg]; simp [Prog.rkX]
  · revert hg; cases s.pc g <;> simp [PC.Exit, Prog.rkX]
  · rw [hg]; simp [Prog.rkX]

/-- **Exit progress.** A process in its critical or exit section (or at statement 50) returns
to its remainder section. -/
theorem exit_progress (hf : r.Fair) {g : Proc h} {T : ℕ} (hpos : 0 < Prog.rkX ((r.s T).pc g)) :
    ∃ t ≥ T, (r.s t).pc g = .rem := by
  apply good_of_measure hf g (fun t => (r.s t).pc g = .rem)
    (fun t => 0 < Prog.rkX ((r.s t).pc g)) (fun t => Prog.μ Prog.rkX (r.s t) g) T hpos
  · intro t ht hrem; rw [hrem] at ht; simp [Prog.rkX] at ht
  · intro t _ hD hG
    rw [r.next_eq] at hG ⊢
    by_cases he : r.ev t = .step g
    · rw [he] at hG ⊢
      obtain ⟨h1, h2⟩ := Prog.stepX (r.inv t) hD hG
      exact ⟨h1, h2.le, fun _ => h2⟩
    · refine ⟨?_, Prog.μ_next_ne _ _ he, fun h => absurd h he⟩
      rw [BW.next_pc_ne _ _ he]; exact hD

/-! ### Lemma 6 -/

/-- **Lemma 6** (generalised): a process to which the lock was handed eventually enters the
critical section. -/
theorem handed_enters (hf : r.Fair) {p : Proc h} {T : ℕ} (hl : (r.s T).mem.lock = some p)
    (hE : ((r.s T).pc p).Entry) : ∃ t ≥ T, (r.s t).pc p = .cs := by
  by_contra H
  push Not at H
  -- `lock = p` and `p` stays in its entry section
  have hP : ∀ t ≥ T, (r.s t).mem.lock = some p ∧ ((r.s t).pc p).Entry := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨hl, hE⟩
    | succ t ht ih =>
      rw [r.next_eq]
      refine ⟨Prog.lock_step (r.inv t) ih.1 ih.2 _, BW.entry_step (r.inv t) _ ih.2 ?_⟩
      rw [← r.next_eq]; exact H _ (by omega)
  obtain ⟨-, ha, hsig⟩ := (r.inv T).lockRole p hl |>.resolve_left (Inv.not_holds_of_entry hE)
  have hA : ∀ t ≥ T, (r.s t).mem.apply p = true := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact ha
    | succ t ht ih =>
      rw [r.next_eq]; exact BW.apply_step (r.inv t) _ (hP t ht).2 ih
  -- phase 1: `signal[p] ← true` is performed
  have h1 : ∃ t ≥ T, (r.s t).mem.signal p = true := by
    rcases hsig with hs | ⟨g, hH⟩
    · exact ⟨T, le_rfl, hs⟩
    apply good_of_measure hf g (fun t => (r.s t).mem.signal p = true)
      (fun t => Hands (r.s t) g p) (fun t => Prog.μ Prog.rkX (r.s t) g) T hH
    · intro t hH' hrem
      rcases hH' with ⟨h', -⟩ | ⟨h', -⟩ <;> rw [hrem] at h' <;> cases h'
    · intro t _ hD hG
      rw [r.next_eq] at hG ⊢
      rcases Prog.hands_step hD (r.ev t) with hs | ⟨hH', hμ⟩
      · exact absurd hs hG
      · refine ⟨hH', ?_, hμ⟩
        by_cases he : r.ev t = .step g
        · exact (hμ he).le
        · exact Prog.μ_next_ne _ _ he
  obtain ⟨t₁, ht₁, hs₁⟩ := h1
  -- phase 2: `p` runs through its entry section
  obtain ⟨t, ht, hcs⟩ := good_of_measure hf p (fun t => (r.s t).pc p = .cs)
    (fun t => T ≤ t ∧ (r.s t).mem.signal p = true) (fun t => Prog.μ Prog.rkE (r.s t) p) t₁
    ⟨ht₁, hs₁⟩
    (fun t hD hrem => by
      have := (hP t hD.1).2; rw [hrem] at this; exact this)
    (fun t _ hD hG => by
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · rw [r.next_eq]
        exact Prog.signal_step (r.inv t) (hP t hD.1).1 (hP t hD.1).2 (hA t hD.1) hD.2 _
      · rw [r.next_eq] at hG ⊢
        by_cases he : r.ev t = .step p
        · rw [he] at hG ⊢
          have := Prog.stepE (r.inv t) (hP t hD.1).2 (hP t hD.1).1 hD.2 hG
          exact ⟨this.le, fun _ => this⟩
        · exact ⟨Prog.μ_next_ne _ _ he, fun h => absurd h he⟩)
  exact H t (by omega) hcs

/-! ### Executions without entries into the critical section -/

lemma incsx_start {s : Cfg h} (hI : Inv s) (e : Ev h) {g : Proc h} (h1 : ¬ s.InCSX g)
    (h2 : (s.next e).InCSX g) : s.pc g ≠ .cs ∧ (s.next e).pc g = .cs := by
  have hcs : s.pc g ≠ .cs := fun h => h1 (Or.inl h)
  refine ⟨hcs, ?_⟩
  by_cases he : e = .step g
  · subst he
    by_cases hE : (s.pc g).Entry
    · by_contra hn
      exact BW.entry_not_incsx (BW.entry_step hI _ hE hn) h2
    · exfalso
      cases hpc : s.pc g <;> simp only [hpc, PC.Entry, not_true_eq_false, not_false_eq_true] at hE
      case rem => simp [Cfg.next, Cfg.stepProc, hpc, Cfg.InCSX, PC.Exit] at h2
      case x50 o =>
        by_cases hb : s.buf g = []
        · simp [Cfg.next, Cfg.stepProc, hpc, Cfg.barrier, hb, Cfg.InCSX, PC.Exit] at h2
        · exact h1 (Or.inr (Or.inr ⟨⟨o, hpc⟩, hb⟩))
      all_goals exact h1 (by simp [Cfg.InCSX, hpc, PC.Exit])
  · exfalso
    unfold Cfg.InCSX at h1 h2
    rw [BW.next_pc_ne _ _ he] at h2
    rcases h2 with h | h | ⟨h, hb⟩
    · exact h1 (Or.inl h)
    · exact h1 (Or.inr (Or.inl h))
    · refine h1 (Or.inr (Or.inr ⟨h, fun hn => hb ?_⟩))
      rw [List.eq_nil_iff_forall_not_mem]
      intro w hw
      have := BW.next_buf_sub s e he hw
      rw [hn] at this; simp at this

/-- Without entries, no process enters its critical or exit section. -/
lemma not_incsx_persist {T : ℕ} (hno : ∀ t ≥ T, ∀ y, ¬ BW.Enters r y t) {g : Proc h} {a : ℕ}
    (ha : T ≤ a) (hg : ¬ (r.s a).InCSX g) : ∀ t ≥ a, ¬ (r.s t).InCSX g := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hg
  | succ t ht ih =>
    intro hc
    rw [r.next_eq] at hc
    have := incsx_start (r.inv t) _ ih hc
    rw [← r.next_eq] at this
    exact hno t (by omega) g this

/-- Without entries, from some time on no process is in its critical or exit section. -/
lemma noent_incsx (hf : r.Fair) {T : ℕ} (hno : ∀ t ≥ T, ∀ y, ¬ BW.Enters r y t) :
    ∃ T₁ ≥ T, ∀ t ≥ T₁, ∀ g, ¬ (r.s t).InCSX g := by
  by_cases hg : ∃ g, (r.s T).InCSX g
  · obtain ⟨g, hg⟩ := hg
    obtain ⟨t₀, ht₀, hrem⟩ := exit_progress hf (rkX_pos_of_incsx hg)
    refine ⟨t₀, ht₀, fun t ht g' => ?_⟩
    by_cases hgg : g' = g
    · subst hgg
      refine not_incsx_persist hno ht₀ ?_ t ht
      simp [Cfg.InCSX, hrem, PC.Exit]
    · exact not_incsx_persist hno le_rfl
        (fun h' => hgg ((r.inv T).uniq _ _ h' hg)) t (by omega)
  · push Not at hg
    exact ⟨T, le_rfl, fun t ht g => not_incsx_persist hno le_rfl (hg g) t ht⟩

/-- Without entries, from some time on no process is in its critical or exit section and the
lock is free. -/
lemma noent_lock (hf : r.Fair) {T : ℕ} (hno : ∀ t ≥ T, ∀ y, ¬ BW.Enters r y t) :
    ∃ T₁ ≥ T, ∀ t ≥ T₁, (∀ g, ¬ (r.s t).InCSX g) ∧ (r.s t).mem.lock = none := by
  obtain ⟨T₁, hT₁, hn⟩ := noent_incsx hf hno
  have h0 : (r.s T₁).mem.lock = none := by
    cases hlk : (r.s T₁).mem.lock with
    | none => rfl
    | some y =>
      exfalso
      rcases (r.inv T₁).lockRole y hlk with hh | ⟨hE, -⟩
      · exact hn T₁ le_rfl y ((r.inv T₁).incsx_of_holds hh)
      · obtain ⟨t, ht, hcs⟩ := handed_enters hf hlk hE
        have hne : (r.s T₁).pc y ≠ .cs := fun h' => by rw [h'] at hE; exact hE
        obtain ⟨t', h1, -, h3⟩ := exists_enters ht hne hcs
        exact hno t' (by omega) y h3
  refine ⟨T₁, hT₁, fun t ht => ⟨hn t ht, ?_⟩⟩
  induction t, ht using Nat.le_induction with
  | base => exact h0
  | succ t ht ih =>
    rcases r.lock_none_succ ih with h' | h'
    · exact h'
    · obtain ⟨y, hy1, hy2⟩ := r.ent_succ_entry h'
      exact absurd ⟨hy1, hy2⟩ (hno t (by omega) y)

lemma Q_nil_of {s : Cfg h} (hI : Inv s) (hn : ∀ g, ¬ s.InCSX g) (hl : s.mem.lock = none) :
    BW.Q s = [] := by
  unfold BW.Q
  rw [BW.hd_of_not]
  · simp [lv, hl, hI.q4 hl]
  · rintro x (⟨g, hg⟩ | ⟨hx, -⟩)
    · exact hn g (BW.htpc_facts hI hg).2.1
    · rw [hl] at hx; cases hx

/-! ### Lemma 5(b) -/

/-- A process in the promotion order (the process the lock is being handed to, followed by the
logical promotion queue) eventually enters the critical section. -/
theorem Q_enters (hf : r.Fair) {x : Proc h} {T : ℕ} (hx : x ∈ BW.Q (r.s T)) :
    ∃ t ≥ T, (r.s t).pc x = .cs := by
  by_contra H
  push Not at H
  have hnx : ∀ t ≥ T, ¬ BW.Enters r x t := fun t ht he => H (t + 1) (by omega) he.2
  have hin : ∀ t ≥ T, x ∈ BW.Q (r.s t) := fun t ht =>
    BW.Q_persist r r.inv ht hx (fun t' h1 _ => hnx t' h1)
  let idx : ℕ → ℕ := fun t => (BW.Q (r.s t)).idxOf x
  have hstep : ∀ t ≥ T, idx (t + 1) ≤ idx t ∧ (∀ y, BW.Enters r y t → idx (t + 1) < idx t) := by
    intro t ht
    have hxt := hin t ht
    have hxt1 := hin (t + 1) (by omega)
    simp only [idx]
    rcases BW.Q_run_step r r.inv t with ⟨y, hy, he | ⟨he, -⟩⟩ | ⟨hn, he | ⟨z, -, he⟩⟩
    · have hyx : y ≠ x := by rintro rfl; exact hnx t ht hy
      rw [he, List.idxOf_cons_ne _ hyx]
      exact ⟨by omega, fun _ _ => by omega⟩
    · rw [he] at hxt; simp at hxt
    · rw [he]; exact ⟨le_rfl, fun y hy => absurd hy (hn y)⟩
    · rw [he, List.idxOf_append_of_mem hxt]; exact ⟨le_rfl, fun y hy => absurd hy (hn y)⟩
  have hmono : ∀ t ≥ T, ∀ t' ≥ t, idx t' ≤ idx t := by
    intro t ht t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact le_rfl
    | succ t' ht' ih => exact (hstep t' (by omega)).1.trans ih
  have hfin : ∀ n, ∀ t ≥ T, idx t ≤ n → ∃ T' ≥ t, ∀ t' ≥ T', ∀ y, ¬ BW.Enters r y t' := by
    intro n
    induction n with
    | zero =>
      intro t ht hi
      refine ⟨t, le_rfl, fun t' ht' y hy => ?_⟩
      have := (hstep t' (by omega)).2 y hy
      have := hmono t ht t' ht'
      omega
    | succ n ih =>
      intro t ht hi
      by_cases hex : ∃ t' ≥ t, ∃ y, BW.Enters r y t'
      · obtain ⟨t', ht', y, hy⟩ := hex
        have h1 := (hstep t' (by omega)).2 y hy
        have h2 := hmono t ht t' ht'
        obtain ⟨T', hT', hno⟩ := ih (t' + 1) (by omega) (by omega)
        exact ⟨T', by omega, hno⟩
      · push Not at hex
        exact ⟨t, le_rfl, hex⟩
  obtain ⟨T', hT', hno⟩ := hfin _ T le_rfl le_rfl
  obtain ⟨T₁, hT₁, hlk⟩ := noent_lock hf hno
  have := hin T₁ (by omega)
  rw [Q_nil_of (r.inv T₁) (hlk T₁ le_rfl).1 (hlk T₁ le_rfl).2] at this
  simp at this

/-- **Lemma 5(b)**: a process in the promotion queue eventually enters the critical section. -/
theorem lemma5b (hf : r.Fair) {p : Proc h} {T : ℕ} (hp : p ∈ (lv (r.s T)).promQ) :
    ∃ t ≥ T, (r.s t).pc p = .cs :=
  Q_enters hf ((BW.mem_Q (r.inv T)).2 (Or.inr hp))

/-- If no process enters the critical section after `T`, then from some time on the lock is
free (`−1`). -/
theorem lock_none_of_no_entry (hf : r.Fair) {T : ℕ}
    (hno : ∀ t ≥ T, (r.s (t + 1)).ent = (r.s t).ent) :
    ∃ T' ≥ T, ∀ t ≥ T', (r.s t).mem.lock = none := by
  have hno' : ∀ t ≥ T, ∀ y, ¬ BW.Enters r y t := fun t ht y hy => by
    have := enters_ent hy; rw [hno t ht] at this; omega
  obtain ⟨T₁, hT₁, h⟩ := noent_lock hf hno'
  exact ⟨T₁, hT₁, fun t ht => (h t ht).2⟩

/-! ### Reading in the exit section (Lemma 7, Claim 2) -/

/-- A process `g` in the critical section at `t₁` reads, in its exit section, node
`target (anc g l) j` (statement 34). If that node holds `p₀ ≠ g` from `t₁` on and `p₀` is in its
entry section with `apply[p₀]` performed at `t₁`, then `p₀` eventually enters the critical
section: `g` promotes it (statements 35–38) unless it is already in the promotion order, and
then Lemma 5(b) applies. -/
theorem enters_of_read (hf : r.Fair) {g p₀ : Proc h} {t₁ l j : ℕ}
    (hcs : (r.s t₁).pc g = .cs) (hl : l < h) (hj : j ≤ 2) (hgp : g ≠ p₀)
    (hnode : ∀ t ≥ t₁, (r.s t).mem.node (target (anc g l) j) = some p₀)
    (hE : ((r.s t₁).pc p₀).Entry) (ha : (r.s t₁).mem.apply p₀ = true) :
    ∃ t ≥ t₁, (r.s t).pc p₀ = .cs := by
  by_contra H
  push Not at H
  have hnx : ∀ t, t₁ ≤ t → t < t + 1 → ¬ BW.Enters r p₀ t :=
    fun t ht _ he => H (t + 1) (by omega) he.2
  obtain ⟨U, hU, hrem⟩ := exit_progress hf (g := g) (T := t₁) (by rw [hcs]; simp [Prog.rkX])
  obtain ⟨τ, hτ1, hτ2, hev, acc, hpc⟩ := BW.read_of_pre r hl hj hU (by rw [hcs]; trivial)
    (by rw [hrem]; simp [BW.PreRead])
  obtain ⟨hE', ha'⟩ := BW.entry_persist r r.inv (b := τ + 1) (by omega) hE ha
    (fun t h1 _ => hnx t h1 (by omega))
  rcases BW.promote_read r r.inv (U := U) hev hpc (hnode τ hτ1) (Ne.symm hgp) hE' ha' (by omega)
      (by simp [Cfg.InCSX, hrem, PC.Exit]) with ⟨t, ht, -, he⟩ | hQ
  · exact hnx t (by omega) (by omega) he
  · obtain ⟨t, ht, hc⟩ := Q_enters hf hQ
    exact H t (by omega) hc

/-- A process `g` in the critical section at `t₁` reads node `target (anc g l) j` in its exit
section (statement 34). If that node holds `p₀ ≠ g` from `t₁` on and `p₀` stays in its entry
section with `apply[p₀]` performed, then `p₀` is (eventually) in the promotion queue.

Under fairness the hypotheses are in fact contradictory: by `enters_of_read`, `p₀` enters the
critical section; the proof derives the conclusion from this contradiction. -/
theorem enqueued_of_read (hf : r.Fair) {g p₀ : Proc h} {t₁ l j : ℕ}
    (hcs : (r.s t₁).pc g = .cs) (hl : l < h) (hj : j ≤ 2) (hgp : g ≠ p₀)
    (hnode : ∀ t ≥ t₁, (r.s t).mem.node (target (anc g l) j) = some p₀)
    (hentry : ∀ t ≥ t₁, ((r.s t).pc p₀).Entry ∧ (r.s t).mem.apply p₀ = true) :
    ∃ t ≥ t₁, p₀ ∈ (lv (r.s t)).promQ := by
  exfalso
  obtain ⟨t, ht, hc⟩ := enters_of_read hf hcs hl hj hgp hnode (hentry t₁ le_rfl).1
    (hentry t₁ le_rfl).2
  have := (hentry t ht).1
  rw [hc] at this; exact this

end Run

end Podc.ConstantBarriersMutex
