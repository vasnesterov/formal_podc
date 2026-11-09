import Papers.PODC2015.StabilizingByzStorage.Cycle
import Papers.PODC2015.StabilizingByzStorage.Shift

/-!
# Theorem 3 (and Lemma 13) of the paper are false

The register of Fig. 3 is not (practically) stabilizing atomic: there is a fair infinite execution
(`n = 9`, `t = 1`, one Byzantine server, sequence numbers modulo `2^64 + 1`) in which new/old
inversions between two regular reads occur forever (`theorem3_false`).

The execution repeats a cycle of 158 steps (`Cex.cycle`), shifted by `4` (sequence numbers and
values) at every repetition. In each cycle:
* `R1` overlaps the writes `W1..W4`; its first iteration sees four different `last_val`s; `W3`
  refreshes the helping values after `R1`'s `READ(true)`; in the second iteration `WRITE(4)` has
  reached two correct servers, so `(4, 4)` has `2t + 1 = 3` copies (with the Byzantine server) and
  `R1` returns `4`.
* `R2` starts after `R1`; its sanity check (lines N2–N6) sees `2t + 1` helping values `(3, 3)` and,
  since `pwsn = 4 >cd 3`, *lowers* `pwsn` to `3` (Lemma 13 claims this happens only after a wrap-around).
  Its loop sees `(4, 4)` once and `(3, 3)` seven times, so it returns `pv = 3`: an inversion,
  although `W3` (value `3`) completed before `W4` (value `4`) started.
* `W4` completes, a read `R3` runs alone and the system is quiescent again.
-/

namespace Podc.StabilizingByzStorage.Atomic

open Podc.StabilizingByzStorage

section Spec

variable {V : Type}

/-- The read invoked at event `i` returns `v` at event `j`. -/
def ReadOp (lab : ℕ → Label V) (i j : ℕ) (v : V) : Prop :=
  i < j ∧ lab i = .invRead ∧ lab j = .retRead v ∧ ∀ k, i < k → k < j → ∀ v', lab k ≠ .retRead v'

/-- The write of `v` is invoked at event `i` and returns at event `j`. -/
def WriteOp (lab : ℕ → Label V) (i j : ℕ) (v : V) : Prop :=
  i < j ∧ lab i = .invWrite v ∧ lab j = .retWrite ∧ ∀ k, i < k → k < j → lab k ≠ .retWrite

/-- Section 2.2: the read `[i, j]` returns a *regular* value `v`: written by the last write that
completed before the read, or by a write concurrent with it. -/
def RegularRead (lab : ℕ → Label V) (i j : ℕ) (v : V) : Prop :=
  (∃ a b, WriteOp lab a b v ∧ b < i ∧ ∀ k, b < k → k < i → lab k ≠ .retWrite) ∨
  (∃ a, a < j ∧ lab a = .invWrite v ∧ ∀ k, a < k → k ≤ i → lab k ≠ .retWrite)

/-- A new/old inversion: the read `R1 = [i1, j1]` precedes `R2 = [i2, j2]`, `R1` returns the value
`v2` of a write `W2`, `R2` returns the value `v1` of a write `W1` that precedes `W2`; each of these
two values is written only once in the whole execution. -/
def Inversion (lab : ℕ → Label V) (i1 j1 i2 j2 : ℕ) : Prop :=
  ∃ v1 v2 a1 b1 a2, ReadOp lab i1 j1 v2 ∧ ReadOp lab i2 j2 v1 ∧ j1 < i2 ∧
    WriteOp lab a1 b1 v1 ∧ b1 < a2 ∧ lab a2 = .invWrite v2 ∧
    (∀ k, lab k = .invWrite v1 → k = a1) ∧ (∀ k, lab k = .invWrite v2 → k = a2)

/-- The "no new/old inversion after `τ_stab`" half of eventual atomicity (Section 2.2). -/
def EventuallyNoInversion (lab : ℕ → Label V) : Prop :=
  ∃ τ, ∀ i1 j1 i2 j2, τ ≤ i1 → ¬ Inversion lab i1 j1 i2 j2

end Spec

/-- No pending message, both clients idle. -/
def Quiescent {n m : ℕ} {V : Type} (σ : State n m V) : Prop :=
  (∀ s, (σ.srv s).wq = [] ∧ (σ.srv s).rq = []) ∧ σ.w.phase = .idle ∧ σ.r.phase = .idle

namespace Cex

set_option maxRecDepth 10000

lemma sq_add (a b : ℕ) : sq a + Fin.ofNat M b = sq (a + b) := by
  ext; simp [sq, Fin.val_add, Nat.add_mod]

lemma st0_shift (k c : ℕ) : (st0 k).shift c = st0 (k + c) := by
  simp only [st0, State.shift, srv0, Server.map, shD, WPhase.shift, sq_add, Option.map_none,
    List.map_nil, Option.map_some]

/-- State before the `p`-th step of the cycle started in `st0 0`. -/
def stAt (p : ℕ) : State N M ℕ := ((st0 0) :: trace0.map Prod.snd).getD p (st0 0)

/-- Lemma 13's claim that the sanity check (line N6) lowers `pwsn` only after a wrap-around of the
sequence numbers is false: in the cycle, at the sanity check of `R2` (step 104) `pwsn` goes from `4`
down to `3`, with all sequence numbers in `[0, 4]`. -/
theorem sanity_check_lowers_pwsn :
    (stAt 104).r.pwsn = sq 4 ∧ (stAt 105).r.pwsn = sq 3 ∧ (stAt 105).r.pv = 3 := by decide

/-- The infinite execution. -/
def exec (i : ℕ) : State N M ℕ := (stAt (i % 158)).shift (4 * (i / 158))

/-- Its labels. -/
def lab (i : ℕ) : Label ℕ := (expLab (i % 158)).shift (4 * (i / 158))

lemma trace0_length : trace0.length = 158 := by
  simpa using congrArg List.length labs0_eq

lemma step0 (p : ℕ) (hp : p < 158) :
    Step T Byz (stAt p) (expLab p) ((trace0.map Prod.snd).getD p (st0 0)) := by
  have := run_spec T Byz (st0 0) (cycle 0) trace0 runCycle_eq p (by rw [trace0_length]; exact hp)
  rw [labs0_eq] at this
  simpa only [stAt, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hp,
    Option.map_some, Option.getD_some] using this

lemma last_eq : (trace0.map Prod.snd).getD (158 - 1) (st0 0) = st0 4 := by
  have h := finalOK_eq
  unfold finalOK at h
  rw [List.getLast?_eq_getElem?, trace0_length] at h
  have hL : 158 - 1 < trace0.length := by rw [trace0_length]; decide
  rw [List.getElem?_eq_getElem hL] at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hL,
    Option.map_some, Option.getD_some]
  generalize trace0[158 - 1] = x at h ⊢
  obtain ⟨ℓ, srv, w, r⟩ := x
  simp only [Bool.decide_and, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, rfl, rfl⟩ := h
  simp only [st0, State.mk.injEq, and_true]
  funext s; exact h1 s

theorem exec_step (i : ℕ) : Step T Byz (exec i) (lab i) (exec (i + 1)) := by
  have hp : i % 158 < 158 := Nat.mod_lt _ (by decide)
  have h := (step0 (i % 158) hp).shift T Byz (4 * (i / 158))
  by_cases hlast : i % 158 + 1 < 158
  · have h1 : (i + 1) % 158 = i % 158 + 1 := by omega
    have h2 : (i + 1) / 158 = i / 158 := by omega
    unfold exec lab
    rw [h1, h2]
    convert h using 2
    simp [stAt]
  · have hpL : i % 158 = 158 - 1 := by omega
    have h1 : (i + 1) % 158 = 0 := by omega
    have h2 : (i + 1) / 158 = i / 158 + 1 := by omega
    unfold exec lab
    rw [h1, h2]
    rw [hpL, last_eq] at h
    rw [hpL]
    convert h using 1
    simp only [stAt, List.getD_cons_zero, st0_shift]
    congr 1; ring

lemma lab_cycle (c p : ℕ) (hp : p < 158) : lab (c * 158 + p) = (expLab p).shift (4 * c) := by
  have h1 : (c * 158 + p) % 158 = p := by omega
  have h2 : (c * 158 + p) / 158 = c := by omega
  simp [lab, h1, h2]

lemma exec_cycle (c : ℕ) : exec (c * 158) = st0 (4 * c) := by
  have h1 : (c * 158) % 158 = 0 := by omega
  have h2 : (c * 158) / 158 = c := by omega
  simp [exec, h1, h2, stAt, st0_shift]

lemma expLab_invWrite : ∀ p < 158, ∀ w, expLab p = .invWrite w →
    (p = 14 ∧ w = 1) ∨ (p = 38 ∧ w = 2) ∨ (p = 52 ∧ w = 3) ∨ (p = 77 ∧ w = 4) := by
  intro p hp w h
  interval_cases p <;> simp_all [expLab]

lemma expLab_retRead_none : ∀ p < 158, (0 < p ∧ p < 92) ∨ (93 < p ∧ p < 114) →
    ∀ v, expLab p ≠ .retRead v := by
  intro p hp hr v
  interval_cases p <;> simp_all [expLab]

lemma expLab_retWrite_none : ∀ p < 158, (52 < p ∧ p < 74) ∨ (74 < p ∧ p ≤ 93) →
    expLab p ≠ .retWrite := by
  intro p hp hr
  interval_cases p <;> simp_all [expLab]

/-- Writes are identified by their values: the write of `4c + j` (`1 ≤ j ≤ 4`) happens only in
cycle `c`. -/
lemma lab_invWrite (k c j : ℕ) (hj : 1 ≤ j ∧ j ≤ 4) (h : lab k = .invWrite (4 * c + j)) :
    k = c * 158 + [14, 38, 52, 77].getD (j - 1) 0 := by
  obtain ⟨q, p, hp, rfl⟩ : ∃ q p, p < 158 ∧ k = q * 158 + p := ⟨k / 158, k % 158,
    Nat.mod_lt _ (by decide), by omega⟩
  rw [lab_cycle _ _ hp] at h
  cases hp' : expLab p <;> rw [hp'] at h <;> simp [Label.shift] at h
  rename_i w
  have hj4 : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
  rcases hj4 with rfl | rfl | rfl | rfl <;>
  rcases expLab_invWrite _ hp w hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp <;> omega

/-- In cycle `c`, the reads `[cL, cL + 92]` and `[cL + 93, cL + 114]` form a new/old inversion,
and both return regular values. -/
theorem inversion_in_cycle (c : ℕ) :
    Inversion lab (c * 158) (c * 158 + 92) (c * 158 + 93) (c * 158 + 114) ∧
      RegularRead lab (c * 158) (c * 158 + 92) (4 * c + 4) ∧
      RegularRead lab (c * 158 + 93) (c * 158 + 114) (4 * c + 3) := by
  have hl := fun p (hp : p < 158) => lab_cycle c p hp
  have hR1 : ReadOp lab (c * 158) (c * 158 + 92) (4 * c + 4) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simpa [Label.shift, expLab] using hl 0 (by decide)
    · rw [hl 92 (by decide)]; simp [Label.shift, expLab]; omega
    · intro k hk1 hk2 v
      obtain ⟨p, rfl⟩ : ∃ p, k = c * 158 + p := ⟨k - c * 158, by omega⟩
      rw [hl _ (by omega)]
      have := expLab_retRead_none p (by omega) (Or.inl ⟨by omega, by omega⟩)
      cases hp : expLab p <;> simp_all [Label.shift]
  have hR2 : ReadOp lab (c * 158 + 93) (c * 158 + 114) (4 * c + 3) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hl 93 (by decide)]; simp [Label.shift, expLab]
    · rw [hl 114 (by decide)]; simp [Label.shift, expLab]; omega
    · intro k hk1 hk2 v
      obtain ⟨p, rfl⟩ : ∃ p, k = c * 158 + p := ⟨k - c * 158, by omega⟩
      rw [hl _ (by omega)]
      have := expLab_retRead_none p (by omega) (Or.inr ⟨by omega, by omega⟩)
      cases hp : expLab p <;> simp_all [Label.shift]
  have hW3 : WriteOp lab (c * 158 + 52) (c * 158 + 74) (4 * c + 3) := by
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [hl 52 (by decide)]; simp [Label.shift, expLab]; omega
    · rw [hl 74 (by decide)]; simp [Label.shift, expLab]
    · intro k hk1 hk2
      obtain ⟨p, rfl⟩ : ∃ p, k = c * 158 + p := ⟨k - c * 158, by omega⟩
      rw [hl _ (by omega)]
      have := expLab_retWrite_none p (by omega) (Or.inl ⟨by omega, by omega⟩)
      cases hp : expLab p <;> simp_all [Label.shift]
  have hW4 : lab (c * 158 + 77) = .invWrite (4 * c + 4) := by
    rw [hl 77 (by decide)]; simp [Label.shift, expLab]; omega
  refine ⟨⟨4 * c + 3, 4 * c + 4, c * 158 + 52, c * 158 + 74, c * 158 + 77, hR1, hR2, by omega, hW3,
    by omega, hW4, fun k hk => lab_invWrite k c 3 (by omega) hk,
    fun k hk => lab_invWrite k c 4 (by omega) hk⟩, ?_, ?_⟩
  · -- `W4` is concurrent with `R1`
    refine Or.inr ⟨c * 158 + 77, by omega, hW4, fun k hk1 hk2 => by omega⟩
  · -- `W3` is the last write completed before `R2`
    refine Or.inl ⟨c * 158 + 52, c * 158 + 74, hW3, by omega, fun k hk1 hk2 => ?_⟩
    obtain ⟨p, rfl⟩ : ∃ p, k = c * 158 + p := ⟨k - c * 158, by omega⟩
    rw [hl _ (by omega)]
    have := expLab_retWrite_none p (by omega) (Or.inr ⟨by omega, by omega⟩)
    cases hp : expLab p <;> simp_all [Label.shift]

lemma expLab_invRead_ret : ∀ p < 158, expLab p = .invRead →
    ∃ q, p < q ∧ q < 158 ∧ ∃ v, expLab q = .retRead v := by
  intro p hp h
  interval_cases p <;> simp [expLab] at h
  · exact ⟨92, by decide, by decide, 4, rfl⟩
  · exact ⟨114, by decide, by decide, 3, rfl⟩
  · exact ⟨157, by decide, by decide, 4, rfl⟩

lemma expLab_invWrite_ret : ∀ p < 158, ∀ v, expLab p = .invWrite v →
    ∃ q, p < q ∧ q < 158 ∧ expLab q = .retWrite := by
  intro p hp v h
  rcases expLab_invWrite p hp v h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact ⟨35, by decide, by decide, rfl⟩
  · exact ⟨49, by decide, by decide, rfl⟩
  · exact ⟨74, by decide, by decide, rfl⟩
  · exact ⟨134, by decide, by decide, rfl⟩

end Cex

open Cex in
/-- **Theorem 3 of the paper is false.** With `n = 9` servers, `t = 1 < n/8` of them Byzantine,
sequence numbers modulo `2^64 + 1`, the algorithm of Fig. 3 has an infinite execution `exec`
(labels `lab`) starting from a clean configuration, in which every step is a step of the algorithm,
the system is quiescent infinitely often (so every message is delivered and every broadcast
terminates), every operation terminates, each read overlaps at most four writes, and yet for every
`τ` there is a new/old inversion between two reads invoked after `τ` that both return regular
values. So no `τ_stab` exists (Lemma 13 and Theorem 3 fail). -/
theorem theorem3_false :
    8 * T < N ∧ Byz.card ≤ T ∧
    (∀ i, Step T Byz (exec i) (lab i) (exec (i + 1))) ∧
    (∀ i, ∃ j, i ≤ j ∧ Quiescent (exec j)) ∧
    (∀ i, lab i = .invRead → ∃ j, i < j ∧ ∃ v, lab j = .retRead v) ∧
    (∀ i v, lab i = .invWrite v → ∃ j, i < j ∧ lab j = .retWrite) ∧
    (∀ τ, ∃ i1 j1 i2 j2 v1 v2, τ ≤ i1 ∧ Inversion lab i1 j1 i2 j2 ∧
      RegularRead lab i1 j1 v2 ∧ RegularRead lab i2 j2 v1) ∧
    ¬ EventuallyNoInversion lab := by
  have hinv : ∀ τ, ∃ i1 j1 i2 j2 v1 v2, τ ≤ i1 ∧ Inversion lab i1 j1 i2 j2 ∧
      RegularRead lab i1 j1 v2 ∧ RegularRead lab i2 j2 v1 := by
    intro τ
    obtain ⟨h1, h2, h3⟩ := inversion_in_cycle τ
    exact ⟨_, _, _, _, _, _, by nlinarith, h1, h2, h3⟩
  refine ⟨by decide, by decide, exec_step, ?_, ?_, ?_, hinv, ?_⟩
  · intro i
    refine ⟨(i / 158 + 1) * 158, by omega, ?_⟩
    rw [exec_cycle]
    exact ⟨fun _ => ⟨rfl, rfl⟩, rfl, rfl⟩
  · intro i h
    obtain ⟨c, p, hp, rfl⟩ : ∃ c p, p < 158 ∧ i = c * 158 + p := ⟨i / 158, i % 158,
      Nat.mod_lt _ (by decide), by omega⟩
    rw [lab_cycle _ _ hp] at h
    have h' : expLab p = .invRead := by
      cases hq : expLab p <;> rw [hq] at h <;> simp_all [Label.shift]
    obtain ⟨q, hq1, hq2, v, hv⟩ := expLab_invRead_ret _ hp h'
    refine ⟨c * 158 + q, by omega, v + 4 * c, ?_⟩
    rw [lab_cycle _ _ hq2, hv]; rfl
  · intro i v h
    obtain ⟨c, p, hp, rfl⟩ : ∃ c p, p < 158 ∧ i = c * 158 + p := ⟨i / 158, i % 158,
      Nat.mod_lt _ (by decide), by omega⟩
    rw [lab_cycle _ _ hp] at h
    obtain ⟨w, h'⟩ : ∃ w, expLab p = .invWrite w := by
      cases hq : expLab p <;> rw [hq] at h <;> simp_all [Label.shift]
    obtain ⟨q, hq1, hq2, hv⟩ := expLab_invWrite_ret _ hp w h'
    refine ⟨c * 158 + q, by omega, ?_⟩
    rw [lab_cycle _ _ hq2, hv]; rfl
  · rintro ⟨τ, hτ⟩
    obtain ⟨i1, j1, i2, j2, -, -, hle, h, -⟩ := hinv τ
    exact hτ i1 j1 i2 j2 hle h

end Podc.StabilizingByzStorage.Atomic
