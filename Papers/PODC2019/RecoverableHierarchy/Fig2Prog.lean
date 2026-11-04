import Papers.PODC2019.RecoverableHierarchy.Fig2Safe

/-!
# Figure 2: Lemma 15 (recoverable wait-freedom with at most `f` failures)

The paper's claim "at least `k` failures occur before any process begins iteration `k`" becomes
the invariant `PInv c C` (with `c` the number of crashes so far):
* every `R[z] ≤ c + 1`;
* a process at line 16 of iteration `k` either is in a fresh run that has not reached
  line 17 yet (`k ≤ R[z] ≤ c`), or came from a non-returning iteration `k - 1`
  (`R[z] = k` and some `R[w] ≥ k + 1`, found at line 25);
* a process at line 17 of iteration `k` has `k ≤ c`;
* a process that has set `reset` in iteration `k` saw some `R[w] ≥ k + 2`.

With at most `f` crashes no process reaches the end of the `for` loop (`rd16 k` with `k > f`,
footnote 4). All other steps decrease a ranking function (`rank`: the remaining program length),
which gives recoverable wait-freedom (`lemma15`).
-/

namespace Podc.RecoverableHierarchy.Fig2

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

variable {n f : ℕ}

/-! ## The progress invariant -/

/-- The local part of the progress invariant (`c`: number of crashes so far). -/
def PP (C : Cfg (A n f)) (c : ℕ) (z : Fin n) : PC n f → Prop
  | .rd16 k _ => (k ≤ R C z ∧ R C z ≤ c) ∨ (R C z = k ∧ ∃ w, k + 1 ≤ R C w)
  | .wr17 k _ => k.val ≤ c
  | .chk k _ _ r _ => r = true → ∃ w, k.val + 2 ≤ R C w
  | _ => True

/-- The progress invariant after `c` crashes. -/
def PInv (c : ℕ) (C : Cfg (A n f)) : Prop :=
  (∀ z, R C z ≤ c + 1) ∧ ∀ z, PP C c z (C.loc z).pc

lemma PP.mono {C C' : Cfg (A n f)} (h : Mono C C') {c c' : ℕ} (hc : c ≤ c') {z : Fin n}
    (hR : R C' z = R C z) {pc : PC n f} (hp : PP C c z pc) : PP C' c' z pc := by
  cases pc with
  | rd16 k v =>
    rcases hp with ⟨h1, h2⟩ | ⟨h1, w, h2⟩
    · exact Or.inl ⟨hR ▸ h1, by omega⟩
    · exact Or.inr ⟨hR ▸ h1, w, h2.trans (h.R w)⟩
  | wr17 k v => exact le_trans hp hc
  | chk k d v r y => exact fun hr => (hp hr).imp fun w hw => hw.trans (h.R w)
  | _ => trivial

lemma PInv.upd {C C' : Cfg (A n f)} {c : ℕ} (hP : PInv c C) {p : Fin n} {l : Loc n f}
    (hloc : C'.loc = Function.update C.loc p l) (hM : Mono C C')
    (hRo : ∀ z, z ≠ p → R C' z = R C z) (hRp : R C' p ≤ c + 1) (hl : PP C' c p l.pc) :
    PInv c C' := by
  refine ⟨fun z => ?_, fun z => ?_⟩
  · by_cases hz : z = p
    · subst hz; exact hRp
    · rw [hRo z hz]; exact hP.1 z
  · by_cases hz : z = p
    · subst hz; simpa [hloc] using hl
    · simpa [hloc, Function.update_of_ne hz] using (hP.2 z).mono hM le_rfl (hRo z hz)

/-- The witness of a reset. -/
lemma reset_witness {C : Cfg (A n f)} {k : Fin (f + 1)} {r : Bool} {y : Fin n}
    (hr : r = true → ∃ w, k.val + 2 ≤ R C w) (h : (r || decide (k.val + 1 < R C y)) = true) :
    ∃ w, k.val + 2 ≤ R C w := by
  rcases Bool.or_eq_true_iff.1 h with h | h
  · exact hr h
  · exact ⟨y, by simp at h; omega⟩

lemma PInv.step {C : Cfg (A n f)} (hI : Inv C) {c : ℕ} (hP : PInv c C) (p : Fin n) :
    PInv c (C.stepP p) := by
  have hM := hI.mono_step p
  rcases hl : C.loc p with ⟨i, pc⟩
  obtain ⟨rfl, hpc⟩ := hI.locOf hl
  have hpp : PP C c i pc := by have := hP.2 i; rwa [hl] at this
  have hRi := hP.1 i
  cases pc with
  | rd16 k v =>
    rw [stepP_rd16 hl] at hM ⊢
    refine hP.upd rfl hM.1 hM.2 (by simpa using hRi) ?_
    simp only
    split_ifs with hk hRk
    · show k ≤ c
      rcases hpp with ⟨h1, h2⟩ | ⟨h1, w, h2⟩
      · omega
      · have := hP.1 w; omega
    · show (k + 1 ≤ R _ i ∧ R _ i ≤ c) ∨ _
      simp only [R_loc]
      rcases hpp with ⟨h1, h2⟩ | ⟨h1, w, h2⟩
      · left; omega
      · exact absurd h1 hRk
    · show (k ≤ R _ i ∧ R _ i ≤ c) ∨ _
      simp only [R_loc]; exact hpp
  | wr17 k v =>
    rw [stepP_wr17 hl] at hM ⊢
    exact hP.upd rfl hM.1 hM.2 (by simp; exact hpp) trivial
  | scan k j v =>
    by_cases hj : j < k.val
    · rw [stepP_scan_lt hl hj] at hM ⊢
      exact hP.upd rfl hM.1 hM.2 (by simpa using hRi) trivial
    · rw [stepP_scan_ge hl hj] at hM ⊢
      exact hP.upd rfl hM.1 hM.2 (by simpa using hRi) trivial
  | wr22 k d v =>
    rw [stepP_wr22 hl] at hM ⊢
    refine hP.upd rfl hM.1 hM.2 (by simpa using hRi) ?_
    simp only
    split_ifs
    · rcases goChk_cases i k d v false 0 with ⟨_, h⟩ | ⟨_, h, _⟩ | ⟨_, _, h⟩
      · rw [h]; intro h'; cases h'
      · cases h
      · rw [h]; trivial
    · trivial
  | chk k d v r y =>
    rw [stepP_chk hl] at hM ⊢
    refine hP.upd rfl hM.1 hM.2 (by simpa using hRi) ?_
    simp only
    rcases goChk_cases i k d v (r || decide (k.val + 1 < R C y)) (y.val + 1) with
      ⟨_, h⟩ | ⟨_, hr, h⟩ | ⟨_, _, h⟩
    · rw [h]; intro hr; simpa using reset_witness hpp hr
    · rw [h]; right
      obtain ⟨w, hw⟩ := reset_witness hpp hr
      exact ⟨by simpa using hpc.1, w, by simp; omega⟩
    · rw [h]; trivial
  | done d => rw [stepP_done hl]; exact hP

lemma PInv.crash {C : Cfg (A n f)} {c : ℕ} (hP : PInv c C) (p : Fin n) :
    PInv (c + 1) (C.next (.crash p)) := by
  have hP' : PInv (c + 1) C :=
    ⟨fun z => (hP.1 z).trans (Nat.le_succ _), fun z => (hP.2 z).mono (mono_refl_loc C C.loc)
      (Nat.le_succ _) rfl⟩
  show PInv (c + 1) ⟨C.inp, Function.update C.loc p ⟨p, .rd16 0 (C.inp p)⟩, C.mem⟩
  exact hP'.upd rfl (mono_refl_loc _ _) (fun _ _ => rfl) (by simpa using hP'.1 p)
    (Or.inl ⟨Nat.zero_le _, by simpa using hP.1 p⟩)

lemma pinv_run {C : Cfg (A n f)} (hI : Inv C) {c : ℕ} (hP : PInv c C) (α : List (Ev n)) :
    PInv (c + numCrashes α) (run C α) := by
  induction α generalizing C c with
  | nil => simpa using hP
  | cons e α ih =>
    rcases e with q | q
    · simpa using ih (hI.next _) (hP.step hI q)
    · have := ih (hI.next _) (hP.crash q)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

lemma pinv_reach (x : Fin n → Bool) (α : List (Ev n)) :
    PInv (numCrashes α) (run (initCfg (A n f) x) α) := by
  have h0 : PInv 0 (initCfg (A n f) x) :=
    ⟨fun z => by simp [R, initCfg], fun z => Or.inl ⟨Nat.zero_le _, by simp [R, initCfg]⟩⟩
  simpa using pinv_run (inv_init x) h0 α

/-- With at most `f` crashes, no process reaches the end of the `for` loop. -/
lemma PInv.not_stuck {C : Cfg (A n f)} {c : ℕ} (hP : PInv c C) (hc : c ≤ f) (z : Fin n)
    {k : ℕ} {v : Bool} (h : (C.loc z).pc = .rd16 k v) : k ≤ f := by
  have := hP.2 z
  rw [h] at this
  rcases this with ⟨h1, h2⟩ | ⟨h1, w, h2⟩
  · omega
  · have := hP.1 w; omega

/-! ## The ranking function -/

/-- The rank of iteration `k` with in-iteration rank `o` (`o < n + f + 5`). -/
def iterRank (n f k o : ℕ) : ℕ := (f + 1 - k) * (n + f + 5) + o

/-- The remaining program length of a local state (the stuck states `rd16 k`, `k > f`, are
excluded by `PInv.not_stuck`). -/
def rank : Loc n f → ℕ
  | ⟨_, .rd16 k _⟩ => iterRank n f k (n + k + 4)
  | ⟨_, .wr17 k _⟩ => iterRank n f k.val (n + k.val + 3)
  | ⟨_, .scan k j _⟩ => iterRank n f k.val (n + 2 + (k.val - j))
  | ⟨_, .wr22 k _ _⟩ => iterRank n f k.val (n + 1)
  | ⟨_, .chk k _ _ _ y⟩ => iterRank n f k.val (n - y.val)
  | ⟨_, .done _⟩ => 0

lemma iterRank_lt {k o o' : ℕ} (h : o' < o) : iterRank n f k o' < iterRank n f k o := by
  unfold iterRank; omega

lemma iterRank_succ {k o o' : ℕ} (hk : k ≤ f) (h : o' < n + f + 5 + o) :
    iterRank n f (k + 1) o' < iterRank n f k o := by
  unfold iterRank
  rw [show f + 1 - k = (f + 1 - (k + 1)) + 1 by omega, Nat.succ_mul]
  omega

lemma rank_goChk {i : Fin n} {k : Fin (f + 1)} {d v r : Bool} {y : ℕ} {o : ℕ}
    (ho : n - y < o) (hy : y ≤ n) :
    rank ⟨i, goChk i k d v r y⟩ < iterRank n f k.val o := by
  have hk := k.isLt
  rcases goChk_cases i k d v r y with ⟨hs, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;>
    simp only [rank]
  · apply iterRank_lt
    have : y ≤ skip i y := by unfold skip; split_ifs <;> omega
    omega
  · exact iterRank_succ (by omega) (by omega)
  · unfold iterRank; omega

/-- Every access from a non-stuck state decreases the rank. -/
lemma rank_lt (l : Loc n f) (hl : ∀ k v, l.pc = .rd16 k v → k ≤ f) {j : Idx n f}
    {o : (Obj n f j).Op} {κ : (Obj n f j).Resp → Loc n f} (h : act l = .access j o κ)
    (r : (Obj n f j).Resp) : rank (κ r) < rank l := by
  rcases l with ⟨i, pc⟩
  cases pc with
  | rd16 k v =>
    have hk := hl k v rfl
    simp only [act] at h; cases h
    simp only [show k < f + 1 by omega, dite_true]
    split_ifs
    · simp only [rank]; exact iterRank_lt (by omega)
    · simp only [rank]; exact iterRank_succ hk (by omega)
  | wr17 k v =>
    simp only [act] at h; cases h
    simp only [rank]; exact iterRank_lt (by omega)
  | scan k j' v =>
    simp only [act] at h
    split_ifs at h with hj
    · cases h; simp only [rank]; exact iterRank_lt (by omega)
    · cases h; simp only [rank]; exact iterRank_lt (by omega)
  | wr22 k d v =>
    simp only [act] at h; cases h
    simp only [rank]
    split_ifs
    · exact rank_goChk (by omega) (Nat.zero_le _)
    · simp only [iterRank]; omega
  | chk k d v r' y =>
    simp only [act] at h; cases h
    simp only [rank]
    have := y.isLt
    exact rank_goChk (by omega) (by omega)
  | done d => simp [act] at h

/-! ## Progress -/

/-- A variant of CSLib's `prog_of_rank`: it suffices that the steps of `p` taken from time `N`
on decrease the rank. -/
-- CSLib candidate
theorem prog_of_rank_from {ι : Type} [DecidableEq ι] {T : ι → ObjSpec} {A : Alg n T}
    (rank : A.L → ℕ) (C : Cfg A) (e : ℕ → Ev n) (p : Fin n) (N : ℕ)
    (hinf : ∀ M, ∃ t ≥ M, e t = .step p) (hN : ∀ t ≥ N, e t ≠ .crash p)
    (hdec : ∀ t ≥ N, ∀ i o (κ : (T i).Resp → A.L) r,
      A.act ((run C (pre e t)).loc p) = .access i o κ →
        rank (κ r) < rank ((run C (pre e t)).loc p)) :
    ∃ t ≥ N, ∃ v, (run C (pre e t)).Out p v := by
  set Cf : ℕ → Cfg A := fun t => run C (pre e t) with hCf
  have hsucc : ∀ t, Cf (t + 1) = (Cf t).next (e t) := by
    intro t; simp [hCf, pre_succ, run_concat]
  by_contra hno
  push Not at hno
  set r : ℕ → ℕ := fun t => rank ((Cf t).loc p) with hr
  have hstepP : ∀ t ≥ N, rank (((Cf t).stepP p).loc p) < r t := by
    intro t ht
    rcases hact : A.act ((Cf t).loc p) with ⟨i, o, κ⟩ | v
    · rw [stepP_of_access _ hact]
      simpa [hr] using hdec t ht i o κ _ hact
    · exact absurd hact (hno t ht v)
  have hle : ∀ t ≥ N, r (t + 1) ≤ r t := by
    intro t ht
    simp only [hr, hsucc]
    rcases he : e t with q | q
    · by_cases hq : q = p
      · subst hq; exact (hstepP t ht).le
      · rw [next_loc_other _ _ (by simpa using Ne.symm hq)]
    · have hq : q ≠ p := by rintro rfl; exact hN t ht he
      rw [next_loc_other _ _ (by simpa using Ne.symm hq)]
  have hmono : ∀ t ≥ N, ∀ d, r (t + d) ≤ r t := by
    intro t ht d
    induction d with
    | zero => simp
    | succ d ih => exact (hle (t + d) (by omega)).trans ih
  have key : ∀ j, ∃ t ≥ N, r t + j ≤ r N := by
    intro j
    induction j with
    | zero => exact ⟨N, le_rfl, by simp⟩
    | succ j ih =>
      obtain ⟨t, ht, hj⟩ := ih
      obtain ⟨t', ht', he⟩ := hinf t
      refine ⟨t' + 1, by omega, ?_⟩
      have h1 : r (t' + 1) < r t' := by
        simp only [hr, hsucc, he, Cfg.next]; exact hstepP t' (by omega)
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht'
      have h2 := hmono t ht d
      omega
  obtain ⟨t, -, ht⟩ := key (r N + 1)
  omega

/-- **Lemma 15** (recoverable wait-freedom): in every infinite execution with at most `f` crashes
(in all its prefixes), a process that takes infinitely many steps and does not crash after time
`N` outputs at some time `≥ N`. -/
theorem lemma15 (x : Fin n → Bool) (e : ℕ → Ev n) (p : Fin n) (N : ℕ)
    (hadm : ∀ t, AtMost f (pre e t)) (hinf : ∀ M, ∃ t ≥ M, e t = .step p)
    (hN : ∀ t ≥ N, e t ≠ .crash p) :
    ∃ t ≥ N, ∃ v, (run (initCfg (A n f) x) (pre e t)).Out p v := by
  refine prog_of_rank_from (A := A n f) rank _ e p N hinf hN fun t _ i o κ r h => ?_
  exact rank_lt _ (fun k v hk => (pinv_reach x (pre e t)).not_stuck (hadm t) p hk) h r

/-- **Theorem 16** (= Theorem 2): the algorithm of Figure 2 solves recoverable consensus
(agreement, validity, recoverable wait-freedom) in every execution with at most `f` failures, for
all `n` and `f`. Agreement and validity even hold in every execution (`lemma14`, `lemma13`). -/
theorem theorem16 (n f : ℕ) : Solves (A n f) (AtMost f) where
  agree x γ _ v w hv hw := lemma14 x γ v w hv hw
  valid x γ _ v hv := lemma13 x γ v hv
  prog x e p N hadm hinf hN := lemma15 x e p N hadm hinf hN

/-- Theorem 16 in the paper's formulation (`SolvesP`: agreement between distinct processes). -/
theorem theorem16P (n f : ℕ) : SolvesP (A n f) (AtMost f) :=
  Podc.RecoverableHierarchy.Solves.solvesP (theorem16 n f)

end Podc.RecoverableHierarchy.Fig2
