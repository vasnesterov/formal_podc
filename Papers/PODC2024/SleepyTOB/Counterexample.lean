import Papers.PODC2024.SleepyTOB.Resilience

/-!
# Algorithm 1 as printed is unsafe; non-vacuity of Theorem 2

D'Amato, Losa, Zanolini, PODC 2024, Section 3.1, Algorithm 1, lines 6–7: "Start `GA_{v,1}` with a
log in the propose message with the largest valid `VRF(v)` *not conflicting with* `L_{v-1}`".
Safety needs the [MMR]-style lock rule (Algorithm 1 is said to recall [MMR]'s protocol): the
proposal must *extend* `L_{v-1}`, and otherwise the process inputs `L_{v-1}` itself (the printed
algorithm has no such fallback).

With the printed rule (`FollowsLiteral`) a Byzantine proposer that wins the VRF lottery can propose
a strict prefix of the decided log (e.g. the genesis log); all honest processes then input it, the
lock is lost, and a conflicting log is decided two views later — in a completely synchronous
execution with one Byzantine process out of four. This refutes Lemma 3, Theorem 1 (safety) and
Theorem 2 for the printed algorithm (`algorithm_1_literal_unsafe`).

The execution (`P = Fin 4`, process 3 Byzantine and silent, all processes always awake, all
messages delivered at once, `η = 2`, `ra = 3`, `π = 1`): every honest process votes
* `[1]` in rounds 1, 2: round 2 is the longest grade-1 output of round 1;
* `[]` in rounds 3, 4: in round 3 (view 2) the processes decide `[1]`, `L_1 = [1]`, and the
  winning proposal is the Byzantine `[]`, which does not conflict with `[1]`;
* `[2]` from round 5 on: in round 5 (view 3) `L_2 = []` and the winning proposal is an honest
  proposal `b || C_2 = [2]` (`C_2 = []` is the longest output of `GA_{2,1}`), which is then
  decided in round 7.

The same family of executions with constant votes satisfies all hypotheses of Theorem 2 together
with a decision (`theorem_2_hypotheses_satisfiable`).
-/

namespace Podc.SleepyTOB

open Finset

noncomputable section
open Classical

variable {P α : Type*} [Fintype P]

/-- Honest processes follow Algorithm 1 *as printed*: the input of `GA_{v,1}` is only required not
to conflict with the longest output `L_{v-1}` of `GA_{v-1,2}`. -/
structure Exec.FollowsLiteral (E : Exec P α) : Prop where
  odd : ∀ r p, 3 ≤ r → Odd r → p ∈ E.H r → (∃ Λ, Outputs (E.tally p (r - 1)) Λ) →
    ∃ L, IsLongest (Outputs (E.tally p (r - 1))) L ∧ ¬ Conflict L (E.vote r p)
  even : ∀ r p, 2 ≤ r → Even r → p ∈ E.H r → (∃ Λ, Grade1 (E.tally p (r - 1)) Λ) →
    IsLongest (Grade1 (E.tally p (r - 1))) (E.vote r p)

/-- The printed rule is weaker than [MMR]'s: every execution following [MMR]'s rule follows the
printed one. -/
theorem Exec.Follows.followsLiteral {E : Exec P α} (h : E.Follows) : E.FollowsLiteral where
  odd r p h1 h2 h3 h4 := by
    obtain ⟨L, hL, hLv⟩ := h.odd r p h1 h2 h3 h4
    exact ⟨L, hL, fun hc => hc (Or.inl hLv)⟩
  even := h.even

/-! ### Uniform executions -/

/-- All processes always awake, a fixed silent Byzantine set `Bz`, every honest process votes
`v r` in round `r`, and every message is delivered immediately. -/
def uniformExec (Bz : Finset P) (v : ℕ → List α) (η ra π : ℕ) : Exec P α where
  η := η
  ra := ra
  π := π
  O _ := univ
  B _ := Bz
  B_subset _ := subset_univ _
  B_mono _ := subset_refl _
  vote r _ := v r
  byz _ := ∅
  byz_sender _ _ h := absurd h (Set.notMem_empty _)
  rcv _ r := {m | ∃ t ≤ r, SentIn (fun _ => univ) (fun _ => Bz) (fun r _ => v r) (fun _ => ∅) t m}
  rcv_mono _ _ _ := fun ⟨t, ht, hs⟩ => ⟨t, by omega, hs⟩
  rcv_sent _ _ _ h := h
  rcv_sync _ _ _ _ t ht _ hm := ⟨t, ht, hm⟩

/-- The tally vote assignment of a uniform round: the honest processes vote `w`. -/
def uniformVotes (Bz : Finset P) (w : List α) : Votes P α :=
  fun q => if q ∈ Bz then none else some w

theorem uniformExec_tally (Bz : Finset P) (v : ℕ → List α) (η ra π : ℕ) (p : P) {r : ℕ}
    (hr : 1 ≤ r) : (uniformExec Bz v η ra π).tally p r = uniformVotes Bz (v r) := by
  funext q
  simp only [uniformVotes]
  split_ifs with hq
  · apply latest_eq_none_of_forall
    rintro s l - ⟨t, -, hs⟩
    rcases hs with ⟨-, hm, -⟩ | hm
    · exact (mem_sdiff.1 hm).2 hq
    · exact hm
  · obtain ⟨s, hs, hW, -, heq⟩ := latest_eq_of_functional (S := (uniformExec Bz v η ra π).rcv p r)
      (W := fun s => r - η ≤ s ∧ s ≤ r) (q := q) v r (fun s hs => hs.2)
      (by
        rintro s l - ⟨t, -, hs⟩
        rcases hs with ⟨-, -, hm⟩ | hm
        · simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm; rfl
        · exact absurd hm (Set.notMem_empty _))
      (s₀ := r) ⟨Nat.sub_le r η, le_rfl⟩
      ⟨r, le_rfl, Or.inl ⟨hr, mem_sdiff.2 ⟨mem_univ q, hq⟩, rfl⟩⟩
    obtain rfl : s = r := le_antisymm hW.2 hs
    exact heq

theorem uniformVotes_voters (Bz : Finset P) (w : List α) :
    voters (uniformVotes Bz w) = univ \ Bz := by
  ext q; simp [voters, uniformVotes]

theorem uniformVotes_votesFor (Bz : Finset P) (w Λ : List α) :
    votesFor (uniformVotes Bz w) Λ = if Λ <+: w then univ \ Bz else ∅ := by
  ext q
  split_ifs with h <;> simp [votesFor, uniformVotes, h]

theorem uniformVotes_grade1 {Bz : Finset P} (hBz : #Bz < Fintype.card P) {w Λ : List α} :
    Grade1 (uniformVotes Bz w) Λ ↔ Λ <+: w := by
  unfold Grade1
  rw [uniformVotes_voters, uniformVotes_votesFor, card_univ_sdiff]
  split_ifs with h <;> simp [h, card_univ_sdiff]
  omega

theorem uniformVotes_outputs {Bz : Finset P} (hBz : #Bz < Fintype.card P) {w Λ : List α} :
    Outputs (uniformVotes Bz w) Λ ↔ Λ <+: w := by
  unfold Outputs
  rw [uniformVotes_voters, uniformVotes_votesFor, card_univ_sdiff]
  split_ifs with h <;> simp [h, card_univ_sdiff]
  omega

theorem uniformVotes_isLongest_grade1 {Bz : Finset P} (hBz : #Bz < Fintype.card P) {w L : List α} :
    IsLongest (Grade1 (uniformVotes Bz w)) L ↔ L = w := by
  simp only [IsLongest, uniformVotes_grade1 hBz]
  constructor
  · rintro ⟨h1, h2⟩
    exact h1.eq_of_length (le_antisymm h1.length_le (h2 w (List.prefix_refl w)))
  · rintro rfl; exact ⟨List.prefix_refl _, fun _ h => h.length_le⟩

theorem uniformVotes_isLongest_outputs {Bz : Finset P} (hBz : #Bz < Fintype.card P) {w L : List α} :
    IsLongest (Outputs (uniformVotes Bz w)) L ↔ L = w := by
  simp only [IsLongest, uniformVotes_outputs hBz]
  constructor
  · rintro ⟨h1, h2⟩
    exact h1.eq_of_length (le_antisymm h1.length_le (h2 w (List.prefix_refl w)))
  · rintro rfl; exact ⟨List.prefix_refl _, fun _ h => h.length_le⟩

theorem uniformExec_H (Bz : Finset P) (v : ℕ → List α) (η ra π r : ℕ) :
    (uniformExec Bz v η ra π).H r = univ \ Bz := rfl

theorem uniformExec_Ow (Bz : Finset P) (v : ℕ → List α) (η ra π a b : ℕ) (h : a ≤ b) :
    (uniformExec Bz v η ra π).Ow a b = univ := by
  apply eq_univ_of_forall
  intro q
  exact mem_biUnion.2 ⟨a, mem_Icc.2 ⟨le_rfl, h⟩, mem_univ q⟩

theorem uniformExec_sleepy {Bz : Finset P} (v : ℕ → List α) (η ra π : ℕ)
    (h : 2 * Fintype.card P < 3 * (Fintype.card P - #Bz)) (r : ℕ) : (uniformExec Bz v η ra π).Sleepy r := by
  show 2 * #((uniformExec Bz v η ra π).Ow (r - η) r) < 3 * #((uniformExec Bz v η ra π).H r)
  rw [uniformExec_Ow _ _ _ _ _ _ _ (Nat.sub_le r η), uniformExec_H, card_univ, card_univ_sdiff]
  exact h

theorem uniformExec_eq4 {Bz : Finset P} (v : ℕ → List α) (η ra π : ℕ)
    (h : 2 * Fintype.card P < 3 * (Fintype.card P - #Bz)) : (uniformExec Bz v η ra π).Eq4 := by
  intro r _ _
  show 2 * #((uniformExec Bz v η ra π).Ow (r - η) r) <
    3 * #((uniformExec Bz v η ra π).H ra \ Bz)
  rw [uniformExec_H, Finset.sdiff_idem, uniformExec_Ow _ _ _ _ _ _ _ (Nat.sub_le r η), card_univ,
    card_univ_sdiff]
  exact h

theorem uniformExec_eq5 (Bz : Finset P) (v : ℕ → List α) (η ra π : ℕ) :
    (uniformExec Bz v η ra π).Eq5 := subset_refl _

/-! ### The counterexample -/

/-- Honest votes of the counterexample: `[1]` in rounds `≤ 2`, `[]` in rounds 3–4, `[2]` later. -/
def cexVote (r : ℕ) : List ℕ := if r ≤ 2 then [1] else if r ≤ 4 then [] else [2]

/-- The counterexample execution: `Fin 4`, process 3 Byzantine (silent), `η = 2`, `ra = 3`,
`π = 1`. -/
def cexExecP (π : ℕ) : Exec (Fin 4) ℕ := uniformExec {3} cexVote 2 3 π

/-- The counterexample with `π = 1`. -/
abbrev cexExec : Exec (Fin 4) ℕ := cexExecP 1

theorem cex_card : #({3} : Finset (Fin 4)) < Fintype.card (Fin 4) := by simp

theorem cex_quorum : 2 * Fintype.card (Fin 4) < 3 * (Fintype.card (Fin 4) - #({3} : Finset (Fin 4))) := by
  simp

theorem cex_mem_H (π r : ℕ) (v : ℕ → List ℕ) : (0 : Fin 4) ∈ (uniformExec {3} v 2 3 π).H r := by
  rw [uniformExec_H]; simp

theorem cex_tally {π : ℕ} (p : Fin 4) {r : ℕ} (hr : 1 ≤ r) :
    (cexExecP π).tally p r = uniformVotes {3} (cexVote r) :=
  uniformExec_tally _ _ _ _ _ p hr

theorem cex_followsLiteral (π : ℕ) : (cexExecP π).FollowsLiteral where
  odd r p h3 hodd _ _ := by
    refine ⟨cexVote (r - 1), ?_, ?_⟩
    · rw [cex_tally p (by omega), uniformVotes_isLongest_outputs cex_card]
    · intro hc; apply hc
      show Compatible (cexVote (r - 1)) (cexVote r)
      obtain ⟨k, rfl⟩ := hodd
      unfold cexVote
      unfold Compatible
      split_ifs <;> first | omega | simp
  even r p h2 heven _ _ := by
    rw [cex_tally p (by omega), uniformVotes_isLongest_grade1 cex_card]
    show cexVote r = cexVote (r - 1)
    obtain ⟨k, rfl⟩ := heven
    unfold cexVote
    split_ifs <;> first | omega | rfl

theorem cex_decides_1 (π : ℕ) : (cexExecP π).Decides 0 3 [1] := by
  refine ⟨le_rfl, ⟨1, rfl⟩, cex_mem_H π 3 cexVote, ?_⟩
  rw [cex_tally 0 (by norm_num), uniformVotes_grade1 cex_card]
  decide

theorem cex_decides_2 (π : ℕ) : (cexExecP π).Decides 0 7 [2] := by
  refine ⟨by norm_num, ⟨3, rfl⟩, cex_mem_H π 7 cexVote, ?_⟩
  rw [cex_tally 0 (by norm_num), uniformVotes_grade1 cex_card]
  decide

/-- **Algorithm 1 as printed is unsafe.** There is an execution in which honest processes follow
the printed Algorithm 1 (input of `GA_{v,1}` "not conflicting with `L_{v-1}`"), every message is
delivered immediately (no asynchrony at all), all hypotheses of Theorem 2 hold (`π < η`,
η-sleepiness in every round, Equations 4 and 5; one Byzantine process out of four), process 0
decides `[1]` in round 3 and `[2]` in round 7, and `[1]`, `[2]` conflict. In particular
* Lemma 3 fails: process 0 decides `[1]` in round 3 but votes `[]` in round 3;
* Theorem 2 fails: `[1] ∈ D_ra` (`ra = 3`) and `[2]` is decided in round `7 > ra + π + 1`;
* Theorem 1 (safety) fails. -/
theorem algorithm_1_literal_unsafe :
    cexExec.FollowsLiteral ∧
    (∀ p r t m, t ≤ r → cexExec.Sent t m → m ∈ cexExec.rcv p r) ∧
    cexExec.π < cexExec.η ∧ (∀ r, cexExec.Sleepy r) ∧ cexExec.Eq4 ∧ cexExec.Eq5 ∧
    cexExec.Decides 0 3 [1] ∧ 3 ≤ cexExec.ra ∧
    cexExec.Decides 0 7 [2] ∧ cexExec.ra + cexExec.π + 1 < 7 ∧ 0 ∈ cexExec.H cexExec.ra ∧
    Conflict [1] [2] ∧
    ¬ [1] <+: cexExec.vote 3 0 := by
  refine ⟨cex_followsLiteral 1, fun _ _ t _ ht hm => ⟨t, ht, hm⟩, by decide,
    uniformExec_sleepy _ _ _ _ cex_quorum, uniformExec_eq4 _ _ _ _ cex_quorum,
    uniformExec_eq5 _ _ _ _ _, cex_decides_1 1, le_rfl, cex_decides_2 1, by decide, cex_mem_H 1 3 cexVote,
    ?_, ?_⟩
  · simp [Conflict, Compatible]
  · show ¬ [1] <+: cexVote 3
    simp [cexVote]

/-- Theorem 2 is false for the printed Algorithm 1: its conclusion fails in `cexExec`. -/
theorem theorem_2_false_for_literal_algorithm :
    ¬ (∀ q s Λ', cexExec.ra + cexExec.π + 1 < s → cexExec.Decides q s Λ' → Compatible [1] Λ') :=
  fun h => algorithm_1_literal_unsafe.2.2.2.2.2.2.2.2.2.2.2.1 (h 0 7 [2] (by decide) (cex_decides_2 1))

/-- Theorem 1 (safety) is false for the printed Algorithm 1, even without any asynchronous round
(`π = 0`) and with η-sleepiness in every round. Compare `Exec.theorem_1_safety`. -/
theorem theorem_1_false_for_literal_algorithm :
    (cexExecP 0).FollowsLiteral ∧ (cexExecP 0).π = 0 ∧ (∀ r, (cexExecP 0).Sleepy r) ∧
    (cexExecP 0).Decides 0 3 [1] ∧ (cexExecP 0).Decides 0 7 [2] ∧ Conflict [1] [2] :=
  ⟨cex_followsLiteral 0, rfl, uniformExec_sleepy _ _ _ _ cex_quorum, cex_decides_1 0,
    cex_decides_2 0, by simp [Conflict, Compatible]⟩

/-! ### Non-vacuity of Theorem 2 -/

/-- Constant votes `[1]`: an execution following the modified Algorithm 1 (with [MMR]'s rule) that
satisfies all hypotheses of Theorem 2 and contains a decision before the asynchronous period. -/
def goodExec : Exec (Fin 4) ℕ := uniformExec {3} (fun _ => [1]) 2 3 1

theorem good_follows : goodExec.Follows where
  odd r p h3 _ _ _ := by
    refine ⟨[1], ?_, List.prefix_refl _⟩
    rw [show goodExec.tally p (r - 1) = uniformVotes {3} [1] from
      uniformExec_tally _ _ _ _ _ p (by omega), uniformVotes_isLongest_outputs cex_card]
  even r p h2 _ _ _ := by
    rw [show goodExec.tally p (r - 1) = uniformVotes {3} [1] from
      uniformExec_tally _ _ _ _ _ p (by omega), uniformVotes_isLongest_grade1 cex_card]
    rfl

/-- All hypotheses of Theorem 2 are simultaneously satisfiable, with a decision in a round
`≤ ra`. -/
theorem theorem_2_hypotheses_satisfiable :
    ∃ E : Exec (Fin 4) ℕ, E.Follows ∧ E.π < E.η ∧
      (∀ r, r ≤ E.ra ∨ E.ra + E.π + 1 < r → E.Sleepy r) ∧ E.Eq4 ∧ E.Eq5 ∧
      ∃ p r Λ, E.Decides p r Λ ∧ r ≤ E.ra := by
  refine ⟨goodExec, good_follows, by decide, fun r _ => uniformExec_sleepy _ _ _ _ cex_quorum r,
    uniformExec_eq4 _ _ _ _ cex_quorum, uniformExec_eq5 _ _ _ _ _, 0, 3, [1], ?_, le_rfl⟩
  refine ⟨le_rfl, ⟨1, rfl⟩, cex_mem_H 1 3 _, ?_⟩
  rw [show goodExec.tally 0 (3 - 1) = uniformVotes {3} [1] from
    uniformExec_tally _ _ _ _ _ 0 (by norm_num), uniformVotes_grade1 cex_card]

end

end Podc.SleepyTOB
