import Papers.PODC2014.DistributedUniversality.NoRepeat
import Papers.PODC2014.DistributedUniversality.Lemma5

/-!
# Progress: rounds, commits, objects that progress forever (Lemma 6, Corollary 1, Theorem 4(a))
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

/-! ### Every step of a process moves it forward -/

/-- Position of a program counter inside a round. -/
def stage (n k : ℕ) : PC → ℕ
  | .init => 0
  | .n1Inv m => 1 + 2 * m
  | .n1Resp m => 2 + 2 * m
  | .scInv => 2 * k + 1
  | .scResp => 2 * k + 2
  | .acInv j => 2 * k + 3 + 2 * j
  | .acResp j => 2 * k + 4 + 2 * j
  | .collect q => 4 * k + 3 + q
  | .loc => 4 * k + 3 + n
  | .upd m => 4 * k + 4 + n + m
  | .write => 5 * k + 4 + n

/-- Progress measure of a process. -/
def rank (l : Loc n k) : ℕ := l.r * (5 * k + n + 5) + stage n k l.pc

theorem rank_step (I : InvA M s) (h : stepFn M s a = some s') :
    rank (s.loc a.proc) < rank (s'.loc a.proc) := by
  have hord : ∀ j x, (s.loc a.proc).ord[j]? = some x →
      ((s.loc a.proc).pc = .acInv j ∨ (s.loc a.proc).pc = .acResp j) → j < k := by
    intro j x hx hpc
    obtain ⟨-, hord, -⟩ := I.ph1_loc a.proc j hpc
    have := (List.getElem?_eq_some_iff.1 hx).1
    rw [hord, length_ordOf] at this; exact this
  have hr0 := I.init_r a.proc
  du_step_cases h <;> simp only [rank, tInit_loc, tN1Inv_loc, tN1Resp_loc, tScInv_loc, tScResp_loc,
    tAcInv_loc, tAcResp_loc, tCollect_loc, tLoc_loc, tUpdIn_loc, tUpdMine_loc, tUpdOther_loc,
    tUpdAdopt_loc, tWrite_loc, Function.update_self, hpc, stage]
  · rw [hr0.1 hpc]; unfold startPC; split_ifs <;> simp [stage] <;> nlinarith
  · omega
  · split_ifs with h1 h2
    · simp [stage]; omega
    · unfold afterN1; split_ifs <;> simp [stage] <;> omega
  · omega
  · simp [stage]
  · omega
  · have := hord j x hx (Or.inr hpc)
    have hl : (s.loc a.proc).ord.length = k := by
      obtain ⟨-, hord', -⟩ := I.ph1_loc a.proc j (Or.inr hpc); rw [hord', length_ordOf]
    split_ifs <;> simp [stage] <;> omega
  · split_ifs <;> simp [stage] <;> omega
  · split_ifs <;> simp [stage] <;> omega
  all_goals first
    | (unfold updPC; split_ifs <;> simp [stage] <;> omega)
    | (generalize ((s.loc a.proc).r) = r
       unfold startPC; split_ifs <;> simp [stage] <;> rw [add_mul, one_mul] <;> omega)

theorem stage_lt (hI : NonVacuity.Inv M s) (i : Fin n) :
    stage n k (s.loc i).pc < 5 * k + n + 5 := by
  have hp := (hI.proc i).pc
  revert hp
  cases (s.loc i).pc <;> intro hp <;> simp only [stage, NonVacuity.PCInv] at hp ⊢ <;> try omega
  · obtain ⟨-, ⟨hm, -⟩, -⟩ := hp; omega
  · obtain ⟨-, -, hord, ⟨x, hx, -⟩, -⟩ := hp
    have := (List.getElem?_eq_some_iff.1 hx).1
    rw [hord, length_ordOf] at this; omega

/-! ### Executions -/

theorem Exec.reachable (e : Exec M n k) (t : ℕ) : Reachable M (e.st t) := by
  induction t with
  | zero => rw [e.start]; exact Relation.ReflTransGen.refl
  | succ t ih => exact ih.tail ⟨e.act t, e.step t⟩

theorem Exec.rank_le_succ (e : Exec M n k) (t : ℕ) (i : Fin n) :
    rank ((e.st t).loc i) ≤ rank ((e.st (t + 1)).loc i) := by
  by_cases hi : i = (e.act t).proc
  · subst hi
    exact le_of_lt (rank_step (InvA.of_reachable (e.reachable t)) (e.step t))
  · rw [loc_ne (e.step t) hi]

theorem Exec.rank_mono (e : Exec M n k) (i : Fin n) {t t' : ℕ} (htt : t ≤ t') :
    rank ((e.st t).loc i) ≤ rank ((e.st t').loc i) := by
  induction htt with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (e.rank_le_succ _ i)

theorem Exec.rank_unbounded (e : Exec M n k) {i : Fin n} (hc : e.Correct i) :
    ∀ N, ∃ t, N ≤ rank ((e.st t).loc i) := by
  intro N
  induction N with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ N ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨t', htt, hp⟩ := hc t
    refine ⟨t' + 1, ?_⟩
    have h1 := e.rank_mono i htt
    have h2 := rank_step (InvA.of_reachable (e.reachable t')) (e.step t')
    rw [hp] at h2
    omega

/-- A correct process executes infinitely many rounds. -/
theorem Exec.round_unbounded (hℓ : 1 ≤ M.ℓ) (hk : 0 < k) (e : Exec M n k) {i : Fin n}
    (hc : e.Correct i) : ∀ R, ∃ t, R ≤ ((e.st t).loc i).r := by
  intro R
  obtain ⟨t, ht⟩ := e.rank_unbounded hc ((R + 1) * (5 * k + n + 5))
  refine ⟨t, ?_⟩
  have hs := stage_lt (NonVacuity.inv_reachable hℓ hk (e.reachable t)) i
  unfold rank at ht
  set B := 5 * k + n + 5
  set r := ((e.st t).loc i).r
  have h1 : (R + 1) * B < (r + 1) * B := by rw [add_mul r, one_mul]; omega
  have := Nat.lt_of_mul_lt_mul_right h1
  omega

/-- Rounds never decrease. -/
theorem Exec.round_mono (e : Exec M n k) (i : Fin n) {t t' : ℕ} (htt : t ≤ t') :
    ((e.st t).loc i).r ≤ ((e.st t').loc i).r := by
  induction htt with
  | refl => exact le_rfl
  | step _ ih =>
    exact ih.trans (r_mono (e.step _) (fun j => ((InvA.of_reachable (e.reachable _)).init_r j).1) i)

/-- In an infinite execution some process takes infinitely many steps. -/
theorem Exec.exists_correct (e : Exec M n k) : ∃ i, e.Correct i := by
  by_contra hno
  unfold Exec.Correct at hno
  push Not at hno
  choose N hN using hno
  have hn : 0 < n := (e.act 0).proc.pos
  let T := Finset.univ.sup N
  have := hN (e.act T).proc T (Finset.le_sup (Finset.mem_univ _))
  exact this rfl

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}

/-! ### Commits -/

/-- Some process got `(commit, v)` from an adopt-commit object of round `r` for object `m`. -/
def CommAt (s : St n k) (r : ℕ) (m : Fin k) (v : Op n) : Prop :=
  ∃ b j, s.acR r b m j = some (true, v)

theorem commAt_of_fin {r : ℕ} {m : Fin k} {j : Fin n} {v : Op n}
    (h : fin M s r m j = some (true, v)) : CommAt s r m v := by
  unfold fin at h
  split_ifs at h
  · exact ⟨false, j, h⟩
  · exact ⟨true, j, h⟩

/-- A commit makes its round uniform (once some process has finished the round). -/
theorem InvA.unif_of_commAt (I : InvA M s) (hM : M.Good) {r m v} (hc : CommAt s r m v)
    (hne : ∃ p tw, s.finR r m p = some tw) : Unif s r m v := by
  obtain ⟨b, j, hj⟩ := hc
  refine ⟨hne, fun p t w hp => ?_⟩
  rcases I.finR_src _ _ _ _ hp with hp' | ⟨hbt, hp'⟩ <;> cases b
  · -- commit in phase false, p in phase true
    have hca := I.acI0_ca _ _ _ _ (I.acR_inv _ _ _ _ _ _ hj).choose_spec.1
    obtain ⟨own, -, ⟨j', hj''⟩, -⟩ := I.acR_inv _ _ _ _ _ _ hp'
    obtain ⟨j3, t3, h3⟩ := I.acI1ca hca (hM hca) _ _ _ _ hj''
    exact I.acR_agree _ _ _ _ _ _ _ _ hj h3
  · exact I.acR_agree _ _ _ _ _ _ _ _ hj hp'
  · exact I.acR_agree _ _ _ _ _ _ _ _ hj hp'
  · -- commit in phase true, p committed in phase false
    simp only at hbt; subst hbt
    have hca := I.acI0_ca _ _ _ _ (I.acR_inv _ _ _ _ _ _ hp').choose_spec.1
    obtain ⟨own, -, ⟨j', hj''⟩, -⟩ := I.acR_inv _ _ _ _ _ _ hj
    obtain ⟨j3, t3, h3⟩ := I.acI1ca hca (hM hca) _ _ _ _ hj''
    exact (I.acR_agree _ _ _ _ _ _ _ _ hp' h3).symm

theorem Exec.commAt_mono (e : Exec M n k) {r m v} {t t' : ℕ} (htt : t ≤ t')
    (h : CommAt (e.st t) r m v) : CommAt (e.st t') r m v := by
  induction htt with
  | refl => exact h
  | step _ ih =>
    obtain ⟨b, j, hj⟩ := ih
    exact ⟨b, j, (InvA.of_reachable (e.reachable _)).acR_mono (e.step _) _ _ _ _ _ hj⟩

/-- The value committed in a round is a proposal of that round. -/
theorem InvA.commAt_prop (I : InvA M s) {r m v} (hc : CommAt s r m v) :
    ∃ j, s.opRec r m j = some v := by
  obtain ⟨b, j, hj⟩ := hc
  obtain ⟨-, -, ⟨j', hj'⟩, -⟩ := I.acR_inv _ _ _ _ _ _ hj
  cases b
  · exact ⟨j', I.acI0 _ _ _ _ hj'⟩
  · exact I.acI1 _ _ _ _ hj'

/-- **Lemma 5** (generalized), on executions: every round has commits on at least `ℓ`
objects. -/
theorem Exec.round_commits (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) (e : Exec M n k) {r : ℕ}
    (hr : 1 ≤ r) : ∃ t, ∃ S : Finset (Fin k), M.ℓ ≤ S.card ∧
      ∀ x ∈ S, ∃ v, CommAt (e.st t) r x v := by
  obtain ⟨i, hi⟩ := e.exists_correct
  obtain ⟨t, ht⟩ := e.round_unbounded hℓ (by omega) hi (r + 1)
  obtain ⟨S, hS, hx⟩ := Lemma5.lemma5_general hℓ hℓk (e.reachable t) hr (p := i) (Or.inl (by omega))
  refine ⟨t, S, hS, fun x hxS => ?_⟩
  obtain ⟨j, v, hv⟩ := hx x hxS
  exact ⟨v, commAt_of_fin hv⟩

end Podc.DistributedUniversality
