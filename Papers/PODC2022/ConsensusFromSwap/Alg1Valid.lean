import Papers.PODC2022.ConsensusFromSwap.Alg1Defs

/-!
# Algorithm 1: validity (Lemma 7)

Lemma 7 of Ovens, *The Space Complexity of Consensus from Swap* (PODC 2022): every value decided
by Algorithm 1 is the input of some process. We prove the slightly stronger statement that every
decided value is the input of a process that took a step (`lemma7_validity_strong`).

Proof: an invariant of all reachable configurations (`Validity.Inv`): every positive component
`j` of a local lap counter of `p` is `x p` or the input of a process that took a step; every
positive component of a lap counter stored in an object is the input of a process that took a
step; the own-input component of each local lap counter is `≥ 1`; and a decided process has a
positive component at its decided value. (The paper argues via the first step that makes the
`j`-th component positive; the invariant is the same argument, inductively.)
-/

namespace ConsensusFromSwap.Alg1

open ConsensusFromSwap

variable {P : Type} [DecidableEq P] {m N : ℕ} [NeZero m] [NeZero N]

namespace Validity

lemma le_lead (U : Lap m) (j : Fin m) : U j ≤ U (lead U) := by
  unfold lead
  generalize_proofs hne
  exact (Finset.mem_filter.1 (Finset.min'_mem _ hne)).2 j

/-- The local computation after a swap preserves the "positive components are good" property,
keeps the component `a` positive, and decides only values with a positive component. -/
lemma after_inv (s : LState P m N) (r : Val P m) (Q : Fin m → Prop) (a : Fin m)
    (hs : ∀ j, 0 < s.U j → Q j) (hr : ∀ j, 0 < r.1 j → Q j) (ha : 1 ≤ s.U a) :
    (∀ j, 0 < (after s r).U j → Q j) ∧ 1 ≤ (after s r).U a ∧
      ∀ v, (after s r).dec = some v → 0 < (after s r).U v := by
  set U' : Lap m := fun j => max (s.U j) (r.1 j) with hU'
  have hQ : ∀ j, 0 < U' j → Q j := by
    intro j hj
    simp only [hU', lt_max_iff] at hj
    rcases hj with hj | hj
    · exact hs j hj
    · exact hr j hj
  have ha' : 1 ≤ U' a := le_trans ha (le_max_left _ _)
  have hL : 0 < U' (lead U') := lt_of_lt_of_le ha' (le_lead U' a)
  unfold after
  simp only [← hU']
  split_ifs with h1 h2
  · exact ⟨hQ, ha', by simp⟩
  · exact ⟨hQ, ha', by simp⟩
  · unfold lap
    split_ifs with h3
    · refine ⟨hQ, ha', ?_⟩
      intro v hv
      simp only [Option.some.injEq] at hv
      subst hv
      exact hL
    · refine ⟨?_, ?_, by simp⟩
      · intro j hj
        by_cases hjL : j = lead U'
        · subst hjL; exact hQ _ hL
        · simp only [Function.update_of_ne hjL] at hj
          exact hQ j hj
      · simp only
        by_cases haL : a = lead U'
        · subst haL; simp
        · simp only [Function.update_of_ne haL]; exact ha'

/-- The invariant of reachable configurations used for validity (inputs `x`, schedule `α`). -/
structure Inv (x : P → Fin m) (α : List P) (C : Cfg (alg P m N)) : Prop where
  loc_pos : ∀ p j, 0 < (C.loc p : LState P m N).U j → j = x p ∨ ∃ q ∈ α, x q = j
  mem_pos : ∀ i j, 0 < (C.mem i : Val P m).1 j → ∃ q ∈ α, x q = j
  own : ∀ p, 1 ≤ (C.loc p : LState P m N).U (x p)
  dec_pos : ∀ p v, (C.loc p : LState P m N).dec = some v → 0 < (C.loc p : LState P m N).U v

lemma inv_init (x : P → Fin m) : Inv x [] (initCfg (alg P m N) x) where
  loc_pos p j h := by
    left
    by_contra hj
    simp [initCfg, alg, initU, hj] at h
  mem_pos i j h := by simp [initCfg, alg] at h
  own p := by simp [initCfg, alg, initU]
  dec_pos p v h := by simp [initCfg, alg] at h

lemma act_of_dec_some (C : Cfg (alg P m N)) (q : P) (v : Fin m)
    (h : (C.loc q : LState P m N).dec = some v) : C.Out q v := by
  show (match (C.loc q : LState P m N).dec with
    | some v => Act.out v
    | none => _) = _
  rw [h]
  rfl

lemma act_of_dec_none (C : Cfg (alg P m N)) (q : P) (h : (C.loc q : LState P m N).dec = none) :
    (alg P m N).act (C.loc q) = .access (C.loc q : LState P m N).idx
      ((C.loc q : LState P m N).U, some (C.loc q : LState P m N).me)
      (fun r => after (C.loc q) r) := by
  show (match (C.loc q : LState P m N).dec with
    | some v => Act.out v
    | none => _) = _
  rw [h]
  rfl

lemma step_loc_self (C : Cfg (alg P m N)) (q : P) (hd : (C.loc q : LState P m N).dec = none) :
    ((C.step q).loc q : LState P m N) = after (C.loc q) (C.mem (C.loc q : LState P m N).idx) := by
  rw [C.step_of_access (act_of_dec_none C q hd)]
  exact Function.update_self q _ C.loc

lemma step_mem_self (C : Cfg (alg P m N)) (q : P) (hd : (C.loc q : LState P m N).dec = none) :
    ((C.step q).mem (C.loc q : LState P m N).idx : Val P m) =
      ((C.loc q : LState P m N).U, some (C.loc q : LState P m N).me) := by
  rw [C.step_of_access (act_of_dec_none C q hd)]
  exact Function.update_self _ _ C.mem

lemma step_mem_ne (C : Cfg (alg P m N)) (q : P) (i : Fin N)
    (hd : (C.loc q : LState P m N).dec = none) (hi : i ≠ (C.loc q : LState P m N).idx) :
    (C.step q).mem i = C.mem i := by
  rw [C.step_of_access (act_of_dec_none C q hd)]
  exact Function.update_of_ne hi _ C.mem

lemma Inv.step {x : P → Fin m} {α : List P} {C : Cfg (alg P m N)} (h : Inv x α C) (q : P) :
    Inv x (α ++ [q]) (C.step q) := by
  have hmono : ∀ j, (∃ q' ∈ α, x q' = j) → ∃ q' ∈ α ++ [q], x q' = j := by
    rintro j ⟨q', hq', hj⟩
    exact ⟨q', by simp [hq'], hj⟩
  have hq : ∀ j, x q = j → ∃ q' ∈ α ++ [q], x q' = j := fun j hj => ⟨q, by simp, hj⟩
  cases hd : (C.loc q : LState P m N).dec with
  | some v =>
    rw [C.step_of_out (act_of_dec_some C q v hd)]
    exact ⟨fun p j hj => (h.loc_pos p j hj).imp_right (hmono j),
      fun i j hj => hmono j (h.mem_pos i j hj), h.own, h.dec_pos⟩
  | none =>
    have hl := step_loc_self C q hd
    have hm := step_mem_self C q hd
    set s : LState P m N := C.loc q
    obtain ⟨hA, hB, hC⟩ := after_inv s (C.mem s.idx) (fun j => j = x q ∨ ∃ q' ∈ α ++ [q], x q' = j)
      (x q) (fun j hj => (h.loc_pos q j hj).imp_right (hmono j))
      (fun j hj => Or.inr (hmono j (h.mem_pos _ j hj))) (h.own q)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p j hj
      by_cases hpq : p = q
      · subst hpq
        rw [hl] at hj
        exact hA j hj
      · rw [C.step_loc_other hpq] at hj
        exact (h.loc_pos p j hj).imp_right (hmono j)
    · intro i j hj
      by_cases hi : i = s.idx
      · subst hi
        rw [hm] at hj
        rcases h.loc_pos q j hj with hj | hj
        · exact hq j hj.symm
        · exact hmono j hj
      · rw [step_mem_ne C q i hd hi] at hj
        exact hmono j (h.mem_pos i j hj)
    · intro p
      by_cases hpq : p = q
      · subst hpq
        rw [hl]
        exact hB
      · rw [C.step_loc_other hpq]
        exact h.own p
    · intro p v hv
      by_cases hpq : p = q
      · subst hpq
        rw [hl] at hv ⊢
        exact hC v hv
      · rw [C.step_loc_other hpq] at hv ⊢
        exact h.dec_pos p v hv

lemma inv_run (x : P → Fin m) (α : List P) : Inv x α (run (initCfg (alg P m N) x) α) := by
  induction α using List.reverseRecOn with
  | nil => exact inv_init x
  | append_singleton α q ih =>
    rw [run_concat]
    exact ih.step q

lemma dec_of_out {C : Cfg (alg P m N)} {p : P} {v : Fin m} (h : C.Out p v) :
    (C.loc p : LState P m N).dec = some v := by
  cases hd : (C.loc p : LState P m N).dec with
  | none =>
    have h' := h
    rw [Cfg.Out, act_of_dec_none C p hd] at h'
    cases h'
  | some w =>
    have := Cfg.Out.unique h (act_of_dec_some C p w hd)
    rw [this]

end Validity

open Validity

/-- Lemma 7 of [Ovens 2022], strong form: every value decided by Algorithm 1 is the input of a
process that took a step. -/
theorem lemma7_validity_strong (x : P → Fin m) (α : List P) (p : P) (v : Fin m)
    (h : (run (initCfg (alg P m N) x) α).Out p v) : ∃ q ∈ α, x q = v := by
  have hI := inv_run (N := N) x α
  have hd := dec_of_out h
  rcases hI.loc_pos p v (hI.dec_pos p v hd) with hv | hv
  · refine ⟨p, ?_, hv.symm⟩
    by_contra hp
    rw [run_loc_other _ α (fun r hr => by rintro rfl; exact hp hr)] at hd
    simp [initCfg, alg] at hd
  · exact hv

/-- Lemma 7 of [Ovens 2022] (validity): every value decided by Algorithm 1 is the input of some
process. -/
theorem lemma7_validity (x : P → Fin m) (α : List P) (p : P) (v : Fin m)
    (h : (run (initCfg (alg P m N) x) α).Out p v) : ∃ q, x q = v := by
  obtain ⟨q, -, hq⟩ := lemma7_validity_strong x α p v h
  exact ⟨q, hq⟩

/-- Lemma 7 of [Ovens 2022], in the form of the `validity` field of `SolvesSetAgreement`. -/
theorem validity_field :
    ∀ x : P → Fin m, InputsIn Set.univ x → ∀ α p v,
      (run (initCfg (alg P m N) x) α).Out p v → ∃ q, x q = v :=
  fun x _ α p v h => lemma7_validity x α p v h

end ConsensusFromSwap.Alg1
