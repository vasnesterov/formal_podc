import Papers.PODC2025.TwoShotConsensusObjects.AlgC2Alg

/-!
# Class `C₂`, sufficiency: the round protocol (Lemma 3)

Pure facts about `opOf` (the value of `op` after the rounds), in particular **Lemma 3**
(`opOf_adj`): if in each round at least one process sees the other's value, and every value seen
is the other's value at the start of that round, then the two values of `op` stay adjacent.
-/

namespace TwoShotCons

@[simp] lemma opOf_nil (i : Fin 2) : opOf i [] = i.val := rfl

lemma opOf_append (i : Fin 2) (rs : List (Option ℕ)) (o : Option ℕ) :
    opOf i (rs ++ [o]) = stepOp (opOf i rs) o := by
  simp [opOf, List.foldl_append]

lemma opOf_take_succ (i : Fin 2) (rs : List (Option ℕ)) {r : ℕ} {o : Option ℕ}
    (h : rs[r]? = some o) : opOf i (rs.take (r + 1)) = stepOp (opOf i (rs.take r)) o := by
  rw [List.take_add_one, h]
  exact opOf_append i _ o

lemma stepOp_mod (a : ℕ) (o : Option ℕ) : stepOp a o % 2 = a % 2 := by
  cases o <;> (simp [stepOp]; try omega)

/-- Parity: `op` of `pᵢ` is `i` modulo `2`. -/
lemma opOf_mod (i : Fin 2) (rs : List (Option ℕ)) : opOf i rs % 2 = i.val := by
  induction rs using List.reverseRecOn with
  | nil => simp; omega
  | append_singleton rs o ih => rw [opOf_append, stepOp_mod, ih]

lemma own_opOf (i : Fin 2) (rs : List (Option ℕ)) : own (opOf i rs) = i := by
  have := opOf_mod i rs
  unfold own
  fin_cases i <;> simp_all

/-- If `pᵢ` never sees the other process, `op = i · 3 ^ (number of rounds)`. -/
lemma opOf_all_none (i : Fin 2) (rs : List (Option ℕ)) (h : ∀ o ∈ rs, o = none) :
    opOf i rs = i.val * 3 ^ rs.length := by
  induction rs using List.reverseRecOn with
  | nil => simp
  | append_singleton rs o ih =>
    rw [opOf_append, ih (fun o ho => h o (by simp [ho])), h o (by simp)]
    simp [stepOp, pow_succ]; ring

/-- Bound: `op ≤ 3 ^ r` after `r` rounds, preserved by a round whose value read is at most
`3 ^ r`. -/
lemma opOf_bound_append {i : Fin 2} {rs : List (Option ℕ)} {o : Option ℕ}
    (h : ∀ r, opOf i (rs.take r) ≤ 3 ^ r) (ho : ∀ x, o = some x → x ≤ 3 ^ rs.length) :
    ∀ r, opOf i ((rs ++ [o]).take r) ≤ 3 ^ r := by
  intro r
  by_cases hr : r ≤ rs.length
  · rw [List.take_append_of_le_length hr]; exact h r
  · rw [List.take_of_length_le (by simp; omega), opOf_append]
    have h1 := h rs.length
    rw [List.take_length] at h1
    have h2 : 3 ^ (rs.length + 1) ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    cases o with
    | none => simp [stepOp, pow_succ] at h2 ⊢; omega
    | some x => have := ho x rfl; simp [stepOp, pow_succ] at h2 ⊢; omega

lemma opOf_bound_nil (i : Fin 2) : ∀ r, opOf i (([] : List (Option ℕ)).take r) ≤ 3 ^ r := by
  intro r; simp; have := Nat.one_le_pow r 3 (by norm_num); omega

/-- **Lemma 3** (round by round): if every value seen is the other's value at the start of the
round, and in no round both processes miss each other, then after `r` rounds of both processes
their values of `op` are adjacent. -/
lemma opOf_adj {rs0 rs1 : List (Option ℕ)}
    (hs0 : ∀ (r : ℕ) (x : ℕ), rs0[r]? = some (some x) → x = opOf 1 (rs1.take r))
    (hs1 : ∀ (r : ℕ) (x : ℕ), rs1[r]? = some (some x) → x = opOf 0 (rs0.take r))
    (hun : ∀ r : ℕ, rs0[r]? = some none → rs1[r]? ≠ some none) :
    ∀ r, r ≤ rs0.length → r ≤ rs1.length →
      opOf 0 (rs0.take r) + 1 = opOf 1 (rs1.take r) ∨
        opOf 1 (rs1.take r) + 1 = opOf 0 (rs0.take r) := by
  intro r
  induction r with
  | zero => intro _ _; simp
  | succ r ih =>
    intro h0 h1
    obtain ⟨o0, ho0⟩ : ∃ o, rs0[r]? = some o := ⟨rs0[r], by simp⟩
    obtain ⟨o1, ho1⟩ : ∃ o, rs1[r]? = some o := ⟨rs1[r], by simp⟩
    rw [opOf_take_succ 0 rs0 ho0, opOf_take_succ 1 rs1 ho1]
    have ih := ih (by omega) (by omega)
    cases o0 with
    | none =>
      cases o1 with
      | none => exact absurd ho1 (hun r ho0)
      | some x1 => rw [hs1 r x1 ho1]; simp only [stepOp]; omega
    | some x0 =>
      rw [hs0 r x0 ho0]
      cases o1 with
      | none => simp only [stepOp]; omega
      | some x1 => rw [hs1 r x1 ho1]; simp only [stepOp]; omega

end TwoShotCons
