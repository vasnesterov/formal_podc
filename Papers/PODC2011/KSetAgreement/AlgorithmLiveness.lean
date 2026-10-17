import Papers.PODC2011.KSetAgreement.AlgorithmSafety

/-!
# Termination of the initially-dead k-set agreement algorithm, and Theorem 8 ("if")

In a run with initially dead processes `dead` (`|dead| ≤ f`, all others correct):
* every correct process wakes up and sends its stage-1 messages (`stage1_sent`);
* every correct process eventually chooses its in-list, because it eventually hears from the
  `≥ n - f - 1 = d` other correct processes (`eventually_inl`);
* every correct process then sends its stage-2 messages (`stage2_sent`), and every correct
  process eventually records them (`eventually_know`);
* in-lists only contain woken, hence correct, processes, so eventually the `know` of every
  correct process is closed, and it decides (`PostGood.closed`).
-/

namespace KSetAgreement.InitDeadAlg

open Cslib Cslib.FLP Relation SourceComp

variable {n : ℕ} {V : Type}

/-! ### Local lemmas -/

@[simp] theorem post_heard (d : ℕ) (p : Fin n) (st : St n V) : (post d p st).heard = st.heard := by
  unfold post; split_ifs <;> rfl

theorem heard_sub_pre (p : Fin n) (e : Option (Msg n V)) (st : St n V) :
    st.heard ⊆ (pre p e st).heard := by
  rcases e with _ | ⟨q, _ | vI⟩
  · exact subset_rfl
  · simp only [pre]; split_ifs
    · exact Finset.subset_insert _ _
    · exact subset_rfl
  · simp only [pre]; split_ifs <;> exact subset_rfl

theorem know_isSome_post (d : ℕ) (p : Fin n) {st : St n V} {u : Fin n}
    (h : (st.know u).isSome) : ((post d p st).know u).isSome := by
  unfold post
  split_ifs
  · simp only [Function.update_apply]
    split_ifs <;> simp [h]
  · exact h

theorem know_isSome_step (d : ℕ) (p : Fin n) (e : Option (Msg n V)) {st : St n V} {u : Fin n}
    (h : (st.know u).isSome) : ((post d p (pre p e st)).know u).isSome := by
  apply know_isSome_post
  rcases e with _ | ⟨q, _ | vI⟩
  · exact h
  · simp only [pre]; split_ifs <;> exact h
  · simp only [pre]; split_ifs
    · simp only [Function.update_apply]; split_ifs <;> simp [h]
    · exact h

theorem run_stable (d : ℕ) (p : Fin n) (Q : St n V → Prop)
    (hQs : ∀ e (st : St n V × Option V), Q st.1 → Q ((alg d).apply p e st).1) :
    ∀ (es : List (Option (Msg n V))) (st : St n V × Option V), Q st.1 →
      Q ((alg d).run p es st).1.1 := by
  intro es
  induction es with
  | nil => exact fun _ h => h
  | cons e es ih => exact fun st h => ih _ (hQs e st h)

theorem run_established (d : ℕ) (p : Fin n) (Q : St n V → Prop) (c : Msg n V)
    (hQs : ∀ e (st : St n V × Option V), Q st.1 → Q ((alg d).apply p e st).1)
    (hQc : ∀ st : St n V × Option V, Q ((alg d).apply p (some c) st).1) :
    ∀ (es : List (Option (Msg n V))) (st : St n V × Option V), some c ∈ es →
      Q ((alg d).run p es st).1.1 := by
  intro es
  induction es with
  | nil => simp
  | cons e es ih =>
    intro st hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact run_stable d p Q hQs es _ (hQc st)
    · exact ih _ hc

theorem apply_stage2 (d : ℕ) (q : Fin n) (e : Option (Msg n V)) (st : St n V × Option V)
    (h0 : st.1.inl = none) (h1 : (((alg d).apply q e st).1.inl).isSome) :
    ∀ p ≠ q, ∃ vI, (p, (q, some vI)) ∈ (alg d).send q e st := by
  intro p hp
  have hr : Ready d (pre q e st.1) := by
    by_contra hr
    simp [KAlgorithm.apply, alg, post, hr, h0] at h1
  refine ⟨((pre q e st.1).input, (pre q e st.1).heard), Multiset.mem_add.2 (Or.inr ?_)⟩
  simp only [stage2, hr, ↓reduceIte]
  exact mem_bcast_of_ne hp

theorem run_stage2 (d : ℕ) (q : Fin n) :
    ∀ (es : List (Option (Msg n V))) (st : St n V × Option V), st.1.inl = none →
      (((alg d).run q es st).1.1.inl).isSome →
      ∀ p ≠ q, ∃ vI, (p, (q, some vI)) ∈ ((alg d).run q es st).2 := by
  intro es
  induction es with
  | nil => intro st h0 h1; simp [KAlgorithm.run, h0] at h1
  | cons e es ih =>
    intro st h0 h1 p hp
    simp only [KAlgorithm.run, Multiset.mem_add]
    by_cases h2 : ((alg d).apply q e st).1.inl = none
    · obtain ⟨vI, h⟩ := ih _ h2 h1 p hp
      exact ⟨vI, Or.inr h⟩
    · obtain ⟨vI, h⟩ := apply_stage2 d q e st h0 (Option.ne_none_iff_isSome.1 h2) p hp
      exact ⟨vI, Or.inl h⟩

variable [DecidableEq V]

/-! ### Global lemmas about single transitions -/

theorem wk_tr {d : ℕ} {x : Fin n → V} {s s' : GS n V} {a : Action (Fin n) (Msg n V)}
    (htr : (algC d x).lts.Tr s a s') {r : Fin n} (h : Wk s r) : Wk s' r := by
  cases a with
  | none =>
    have : s' = s := htr
    subst this; exact h
  | some m =>
    obtain ⟨_, rfl⟩ := htr
    simp only [Wk, recv_proc] at h ⊢
    split_ifs with hr
    · subst hr; exact isRight_nextLoc d x _ _ h
    · exact h

theorem msgs_recv {d : ℕ} {x : Fin n → V} {m : Message (Fin n) (Msg n V)} {s : GS n V}
    {q : Fin n} {c : Msg n V}
    (h : (q, c) ∈ (alg (V := V) d).sendLoc (fun p _ => x p) m.dest m.msg (s.proc m.dest).state) :
    (⟨q, Sum.inr c⟩ : Message (Fin n) (Msg n V)) ∈ ((algC d x).recvMsg m s).msgs := by
  simp only [Algorithm.recvMsg, KAlgorithm.alg, Multiset.mem_add, Multiset.mem_map]
  exact Or.inr ⟨(q, c), h, rfl⟩

/-- When `q` wakes up, it sends stage-1 messages to all others. -/
theorem stage1_sent {d : ℕ} {x : Fin n → V} {s s' : GS n V} {a : Action (Fin n) (Msg n V)}
    (htr : (algC d x).lts.Tr s a s') {q : Fin n} (h0 : ¬ Wk s q) (h1 : Wk s' q) :
    ∀ p ≠ q, (⟨p, Sum.inr (q, none)⟩ : Message (Fin n) (Msg n V)) ∈ s'.msgs := by
  intro p hp
  cases a with
  | none =>
    have : s' = s := htr
    subst this; exact absurd h1 h0
  | some m =>
    obtain ⟨_, rfl⟩ := htr
    simp only [Wk, recv_proc] at h1
    split_ifs at h1 with hq
    · subst hq
      apply msgs_recv
      simp only [Wk] at h0
      revert h0 h1
      rcases m.msg with b | c <;> rcases (s.proc m.dest).state with buf | st <;>
        intro h0 h1 <;> simp [KAlgorithm.nextLoc] at h0 h1
      simp only [KAlgorithm.sendLoc, KAlgorithm.run, Multiset.mem_add]
      left
      exact Multiset.mem_add.2 (Or.inl (mem_bcast_of_ne hp))
    · exact absurd h1 h0

/-- When `q` chooses its in-list, it sends stage-2 messages to all others. -/
theorem stage2_sent {d : ℕ} {x : Fin n → V} {s s' : GS n V} {a : Action (Fin n) (Msg n V)}
    (htr : (algC d x).lts.Tr s a s') {q : Fin n} (h0 : IL s q = none) (h1 : (IL s' q).isSome) :
    ∀ p ≠ q, ∃ vI, (⟨p, Sum.inr (q, some vI)⟩ : Message (Fin n) (Msg n V)) ∈ s'.msgs := by
  intro p hp
  cases a with
  | none =>
    have : s' = s := htr
    subst this; simp [h0] at h1
  | some m =>
    obtain ⟨_, rfl⟩ := htr
    simp only [IL, recv_proc] at h1
    split_ifs at h1 with hq
    · subst hq
      simp only [IL] at h0
      revert h0 h1
      rcases hmsg : m.msg with b | c <;> rcases hst : (s.proc m.dest).state with buf | st <;>
        intro h1 h0
      · simp only [KAlgorithm.nextLoc, ilLoc] at h1
        obtain ⟨vI, hvI⟩ := run_stage2 d m.dest _ _ rfl h1 p hp
        exact ⟨vI, msgs_recv (by rw [hmsg, hst]; exact hvI)⟩
      · simp [KAlgorithm.nextLoc, ilLoc] at h0 h1; simp [h0] at h1
      · simp [KAlgorithm.nextLoc, ilLoc] at h1
      · simp only [KAlgorithm.nextLoc, ilLoc] at h0 h1
        obtain ⟨vI, hvI⟩ := apply_stage2 d m.dest (some c) st h0 h1 p hp
        exact ⟨vI, msgs_recv (by rw [hmsg, hst]; exact hvI)⟩
    · have : ilLoc (s.proc q).state = none := h0
      simp [this] at h1

/-! ### Along an infinite execution -/

section Run

variable {d : ℕ} {x : Fin n → V} {inp : Fin n → Bool} {ss : ωSequence (GS n V)}
  {xs : ωSequence (Action (Fin n) (Msg n V))}

omit [DecidableEq V] in
theorem persist (Φ : GS n V → Prop) (hΦ : ∀ j, Φ (ss j) → Φ (ss (j + 1))) {i j : ℕ}
    (hij : i ≤ j) (hi : Φ (ss i)) : Φ (ss j) := by
  induction j, hij using Nat.le_induction with
  | base => exact hi
  | succ j _ ih => exact hΦ j ih

omit [DecidableEq V] in
theorem first_change (Φ : GS n V → Prop) (h0 : ¬ Φ (ss 0)) {j : ℕ} (hj : Φ (ss j)) :
    ∃ t, ¬ Φ (ss t) ∧ Φ (ss (t + 1)) := by
  induction j with
  | zero => exact absurd hj h0
  | succ j ih =>
    by_cases h : Φ (ss j)
    · exact ih h
    · exact ⟨j, h, hj⟩

variable (hex : (algC d x).lts.OmegaExecution ss xs) (h0 : ss 0 = (algC d x).start inp)
include hex h0

theorem inv_ss (j : ℕ) : Inv x d (ss j) := by
  have := hex.extract_mTr (Nat.zero_le j)
  rw [h0] at this
  exact inv_mTr (inv_start d x inp) this

omit h0 in
theorem wk_persist {r : Fin n} {i j : ℕ} (hij : i ≤ j) (h : Wk (ss i) r) : Wk (ss j) r :=
  persist (fun s => Wk s r) (fun j hj => wk_tr (hex j) hj) hij h

omit [DecidableEq V] hex in
theorem not_wk_zero (r : Fin n) : ¬ Wk (ss 0) r := by
  simp [h0, Wk, Algorithm.start, KAlgorithm.alg]

/-- Initially dead processes never wake up. -/
theorem not_wk_of_neverSteps {r : Fin n} (hr : NeverSteps r xs) (j : ℕ) : ¬ Wk (ss j) r := by
  induction j with
  | zero => exact not_wk_zero h0 r
  | succ j ih =>
    have htr := hex j
    cases hx : xs j with
    | none =>
      rw [hx] at htr
      have : ss (j + 1) = ss j := htr
      rw [this]; exact ih
    | some m =>
      rw [hx] at htr
      obtain ⟨_, he⟩ := htr
      rw [he]
      simp only [Wk, recv_proc]
      rw [ite_eq_right (fun h => hr j m hx h.symm)]
      exact ih

/-- Correct processes wake up. -/
theorem eventually_wk {r : Fin n} (hr : ProcFair r ss xs) : ∃ j, Wk (ss j) r := by
  have hm : (⟨r, Sum.inl (inp r)⟩ : Message (Fin n) (Msg n V)) ∈ (ss 0).msgs := by
    rw [h0]; simp [Algorithm.start]
  obtain ⟨j, -, hj⟩ := hr _ rfl 0 hm
  have htr := hex j
  rw [hj] at htr
  obtain ⟨_, he⟩ := htr
  refine ⟨j + 1, ?_⟩
  rw [he]
  simp only [Wk, recv_proc, ↓reduceIte]
  rcases (ss j).proc r |>.state with buf | st <;> simp [KAlgorithm.nextLoc]

/-- If a message with content `c` is in flight to the correct process `p`, then eventually `p`
is woken and its local state satisfies every stable property `Q` established by `c`. -/
theorem eventually_Q {p : Fin n} (hp : ProcFair p ss xs) {c : Msg n V} {j : ℕ}
    (hm : (⟨p, Sum.inr c⟩ : Message (Fin n) (Msg n V)) ∈ (ss j).msgs) (Q : St n V → Prop)
    (hQs : ∀ e (st : St n V × Option V), Q st.1 → Q ((alg d).apply p e st).1)
    (hQc : ∀ st : St n V × Option V, Q ((alg d).apply p (some c) st).1) :
    ∃ T, ∀ t, T ≤ t → ∃ st, ((ss t).proc p).state = Sum.inr st ∧ Q st.1 := by
  let Φ : GS n V → Prop := fun s => ((s.proc p).state).elim (fun buf => c ∈ buf) (fun st => Q st.1)
  have hΦ : ∀ j, Φ (ss j) → Φ (ss (j + 1)) := by
    intro j hj
    have htr := hex j
    cases hx : xs j with
    | none =>
      rw [hx] at htr
      have : ss (j + 1) = ss j := htr
      rw [this]; exact hj
    | some m =>
      rw [hx] at htr
      obtain ⟨_, he⟩ := htr
      simp only [Φ, he, recv_proc] at hj ⊢
      split_ifs with hpm
      · subst hpm
        revert hj
        rcases m.msg with b | c' <;> rcases (ss j).proc m.dest |>.state with buf | st <;>
          intro hj <;> simp only [KAlgorithm.nextLoc, Sum.elim_inl, Sum.elim_inr] at hj ⊢
        · exact run_established d m.dest Q c hQs hQc _ _
            (List.mem_cons_of_mem _ (List.mem_map_of_mem hj))
        · exact hj
        · exact List.mem_append_left _ hj
        · exact hQs _ _ hj
      · exact hj
  obtain ⟨j1, -, hj1⟩ := hp _ rfl j hm
  have hΦ1 : Φ (ss (j1 + 1)) := by
    have htr := hex j1
    rw [hj1] at htr
    obtain ⟨_, he⟩ := htr
    simp only [Φ, he, recv_proc, ↓reduceIte]
    rcases (ss j1).proc p |>.state with buf | st <;>
      simp only [KAlgorithm.nextLoc, Sum.elim_inl, Sum.elim_inr]
    · simp
    · exact hQc st
  obtain ⟨j2, hj2⟩ := eventually_wk hex h0 hp
  refine ⟨max (j1 + 1) j2, fun t ht => ?_⟩
  have hw := wk_persist hex (le_of_max_le_right ht) hj2
  have hΦt := persist Φ hΦ (le_of_max_le_left ht) hΦ1
  simp only [Wk] at hw
  simp only [Φ] at hΦt
  revert hw hΦt
  rcases (ss t).proc p |>.state with buf | st
  · simp
  · intro _ h; exact ⟨st, rfl, h⟩

/-- Every correct process eventually chooses its in-list. -/
theorem eventually_inl {f : ℕ} (hd : d = n - f - 1) {dead : Finset (Fin n)}
    (hdead : dead.card ≤ f) (hfair : ∀ p ∉ dead, ProcFair p ss xs) {p : Fin n} (hp : p ∉ dead) :
    ∃ T, ∀ t, T ≤ t → ∃ st, ((ss t).proc p).state = Sum.inr st ∧ st.1.inl.isSome := by
  classical
  set A := (Finset.univ \ dead).erase p
  have hQ : ∀ q ∈ A, ∃ T, ∀ t, T ≤ t → ∃ st, ((ss t).proc p).state = Sum.inr st ∧
      (st.1.inl.isSome ∨ q ∈ st.1.heard) := by
    intro q hq
    simp only [A, Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, true_and] at hq
    obtain ⟨jq, hjq⟩ := eventually_wk hex h0 (hfair q hq.2)
    obtain ⟨t, ht0, ht1⟩ := first_change (fun s => Wk s q) (not_wk_zero h0 q) hjq
    have hm := stage1_sent (hex t) ht0 ht1 p (Ne.symm hq.1)
    refine eventually_Q hex h0 (hfair p hp) hm (fun st => st.inl.isSome ∨ q ∈ st.heard) ?_ ?_
    · rintro e ⟨st, dv⟩ (h | h)
      · left
        obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 h
        simp [KAlgorithm.apply, alg, step_inl_of_some d p e hI]
      · by_cases hi : ((alg d).apply p e (st, dv)).1.inl.isSome
        · exact Or.inl hi
        · right
          simp only [KAlgorithm.apply, alg, post_heard]
          exact heard_sub_pre p e st h
    · rintro ⟨st, dv⟩
      by_cases hi : st.inl.isSome
      · left
        obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 hi
        simp [KAlgorithm.apply, alg, step_inl_of_some d p _ hI]
      · right
        simp only [Option.not_isSome_iff_eq_none] at hi
        simp [KAlgorithm.apply, alg, pre, hq.1, hi]
  choose! TQ hTQ using hQ
  obtain ⟨jp, hjp⟩ := eventually_wk hex h0 (hfair p hp)
  refine ⟨max jp (A.sup TQ), fun t ht => ?_⟩
  have hw := wk_persist hex (le_of_max_le_left ht) hjp
  simp only [Wk] at hw
  obtain ⟨st, hst⟩ : ∃ st, ((ss t).proc p).state = Sum.inr st := by
    revert hw
    rcases (ss t).proc p |>.state with buf | st
    · simp
    · exact fun _ => ⟨st, rfl⟩
  refine ⟨st, hst, ?_⟩
  by_contra hnone
  simp only [Option.not_isSome_iff_eq_none] at hnone
  have hsub : A ⊆ st.1.heard := by
    intro q hq
    obtain ⟨st', hst', h⟩ := hTQ q hq t
      ((Finset.le_sup hq).trans (le_of_max_le_right ht))
    rw [hst, Sum.inr.injEq] at hst'
    subst hst'
    simpa [hnone] using h
  have hcard : d ≤ A.card := by
    have h1 : (Finset.univ \ dead).card = n - dead.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
    have h2 : p ∈ Finset.univ \ dead := by simpa using hp
    have h3 := Finset.card_erase_of_mem h2
    simp only [A]
    omega
  have hpost := ((inv_ss hex h0 t).loc p)
  rw [hst] at hpost
  have := hpost.2.heard hnone
  have := Finset.card_le_card hsub
  omega

/-- Every correct process eventually records the stage-2 information of every other correct
process. -/
theorem eventually_know {f : ℕ} (hd : d = n - f - 1) {dead : Finset (Fin n)}
    (hdead : dead.card ≤ f) (hfair : ∀ p ∉ dead, ProcFair p ss xs) {p u : Fin n}
    (hp : p ∉ dead) (hu : u ∉ dead) (hpu : u ≠ p) :
    ∃ T, ∀ t, T ≤ t → ∃ st, ((ss t).proc p).state = Sum.inr st ∧ (st.1.know u).isSome := by
  obtain ⟨Tu, hTu⟩ := eventually_inl hex h0 hd hdead hfair hu
  obtain ⟨st, hst, hinl⟩ := hTu Tu le_rfl
  have hIL : (IL (ss Tu) u).isSome := by simp [IL, hst, ilLoc, hinl]
  have hIL0 : ¬ (IL (ss 0) u).isSome := by
    simp [h0, IL, ilLoc, Algorithm.start, KAlgorithm.alg]
  obtain ⟨t, ht0, ht1⟩ := first_change (fun s => (IL s u).isSome) hIL0 hIL
  obtain ⟨vI, hm⟩ := stage2_sent (hex t) (by simpa using ht0) ht1 p (Ne.symm hpu)
  refine eventually_Q hex h0 (hfair p hp) hm (fun st => (st.know u).isSome) ?_ ?_
  · rintro e ⟨st, dv⟩ h
    exact know_isSome_step d p e h
  · rintro ⟨st, dv⟩
    show ((post d p (pre p (some (u, some vI)) st)).know u).isSome
    apply know_isSome_post
    simp [pre, hpu]

end Run

/-- **Termination** in runs with at most `n - d - 1` initially dead processes. -/
theorem terminates (n f : ℕ) :
    Terminates (alg (n := n) (V := V) (n - f - 1)) (InitDead f) := by
  classical
  intro x inp ss xs ⟨hrun, dead, hdead, hnever, hfair⟩ p
  by_cases hp : p ∈ dead
  · exact Or.inl (neverSteps_procFaulty hrun (hnever p hp))
  right
  obtain ⟨h0, hex⟩ := hrun
  set d := n - f - 1
  have hK := fun u (hu : u ∈ (Finset.univ \ dead).erase p) =>
    eventually_know hex h0 rfl hdead hfair hp
      (by simp at hu; exact hu.2) (by simp at hu; exact hu.1)
  choose! TK hTK using hK
  obtain ⟨T1, hT1⟩ := eventually_inl hex h0 rfl hdead hfair hp
  set T := max T1 (((Finset.univ \ dead).erase p).sup TK)
  obtain ⟨st, hst, hinl⟩ := hT1 T (le_max_left _ _)
  have hinv := inv_ss hex h0 T
  have hloc := hinv.loc p
  rw [hst] at hloc
  have hclosed : Closed st.1.know p := by
    obtain ⟨I, hI⟩ := Option.isSome_iff_exists.1 hinl
    have hkp : (st.1.know p).isSome := by simp [(hloc.1.inl I hI).2.2.2]
    refine ⟨hkp, fun r ⟨v, J⟩ hr u hu => ?_⟩
    have hJ := (hloc.1.know r v J hr).2
    have hwu := (IL_spec hinv hJ).2.2 u hu
    have hud : u ∉ dead := fun hd => not_wk_of_neverSteps hex h0 (hnever u hd) T hwu
    by_cases hup : u = p
    · subst hup; exact hkp
    · have hmem : u ∈ (Finset.univ \ dead).erase p := by simp [hup, hud]
      obtain ⟨st', hst', h⟩ := hTK u hmem T
        ((Finset.le_sup hmem).trans (le_max_right _ _))
      rw [hst, Sum.inr.injEq] at hst'
      subst hst'
      exact h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hloc.2.closed hclosed)
  refine ⟨T, v, ?_⟩
  simp only [dec, hst, KAlgorithm.decOf, hv]

/-- **Theorem 8 of [BRS11], "if" direction.** In an asynchronous message-passing system with `n`
processes, up to `f` of which may be initially dead, `k`-set agreement is solvable if
`k n > (k + 1) f`. The algorithm is the two-stage protocol `alg (n - f - 1)` (with `L = n - f`). -/
theorem initDead_possible (n f k : ℕ) (V : Type) (hk : (k + 1) * f < k * n) :
    ∃ (M S : Type) (_ : DecidableEq M) (A : KAlgorithm (Fin n) M S V),
      SolvesKSA A k (InitDead f) := by
  classical
  exact ⟨Msg n V, St n V, inferInstance, alg (n - f - 1), kSafe n f k hk, terminates n f⟩

end KSetAgreement.InitDeadAlg
