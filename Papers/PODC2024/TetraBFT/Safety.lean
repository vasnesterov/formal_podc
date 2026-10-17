import Papers.PODC2024.TetraBFT.Defs

/-!
# Safety of single-shot TetraBFT (Lemmas 6–8, Theorem 1: agreement)

We prove safety for every *abstract execution*: a set of faulty nodes and, for each correct node,
the set of votes it ever cast, subject to the four guarantees the protocol gives
(`Execution.SafetyHyp`):

* (one value) a correct node casts at most one vote-k per view;
* (quorum) a correct vote-k (k = 2, 3, 4) for `x` in view `r` is preceded by a quorum of vote-(k−1)
  messages for `x` in view `r` — only the *correct* members of that quorum are known to have cast
  those votes, Byzantine members may have sent anything to anybody;
* (Rule 3) a correct vote-1 for `x` in view `r` is preceded by a set `S` of proof messages for view
  `r` such that `x` is safe by Rule 3, where every correct sender reported *honestly* (`IsReport`)
  its votes of views `< r` (Byzantine senders may report anything);
* (decision) a correct node decides `x` in view `v` only if `x` is *committed* in `v`: some quorum's
  correct members all cast vote-4 for `x` in `v`.

No timing, no channels and no view synchronization are involved, so this covers all asynchronous
executions. `Refinement.lean` shows that the message-level protocol (`Protocol.lean`) produces
such executions.
-/

namespace TetraBFT

open Finset Cslib.Quorum

variable {P V : Type*} [Fintype P] [DecidableEq P]

/-- An abstract execution: faulty nodes, votes cast by correct nodes, and decisions
(`decided p x v`: node `p` decides `x` in view `v`). -/
structure Execution (P V : Type*) where
  faulty : Finset P
  voted : P → Vote V → Prop
  decided : P → V → ℕ → Prop

namespace Execution

variable (E : Execution P V) (f : ℕ)

/-- `x` is committed in view `v`: there is a quorum whose correct members cast vote-4 for `x`
in view `v`. -/
def Committed (x : V) (v : ℕ) : Prop :=
  ∃ Q : Finset P, Fintype.card P - f ≤ Q.card ∧ ∀ q ∈ Q, q ∉ E.faulty → E.voted q ⟨4, v, x⟩

/-- The protocol guarantees used by the safety proof. -/
structure SafetyHyp : Prop where
  card_faulty : E.faulty.card ≤ f
  one_val : ∀ p ∉ E.faulty, ∀ k r (x y : V), E.voted p ⟨k, r, x⟩ → E.voted p ⟨k, r, y⟩ → x = y
  quorum_prev : ∀ p ∉ E.faulty, ∀ k r (x : V), 2 ≤ k → k ≤ 4 → E.voted p ⟨k, r, x⟩ →
    ∃ Q : Finset P, Fintype.card P - f ≤ Q.card ∧ ∀ q ∈ Q, q ∉ E.faulty → E.voted q ⟨k - 1, r, x⟩
  rule3 : ∀ p ∉ E.faulty, ∀ r (x : V), E.voted p ⟨1, r, x⟩ →
    ∃ (S : Finset P) (rep : P → Report V),
      (∀ q ∈ S, q ∉ E.faulty → IsReport (E.voted q) r 1 4 (rep q)) ∧
      Rule3 (Fintype.card P) f S rep x r
  decided_committed : ∀ p ∉ E.faulty, ∀ (x : V) v, E.decided p x v → E.Committed f x v

variable {E f}

/-- Some correct node cast the given vote, given a quorum of such votes. -/
theorem exists_correct_of_quorum (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f)
    {Q : Finset P} (hQ : Fintype.card P - f ≤ Q.card) {w : Vote V}
    (h : ∀ q ∈ Q, q ∉ E.faulty → E.voted q w) : ∃ q ∉ E.faulty, E.voted q w := by
  obtain ⟨q, hq, hqF⟩ :=
    exists_mem_notMem_of_card_le_of_lt hE.card_faulty (show f + 1 ≤ Q.card by omega)
  exact ⟨q, hqF, h q hq hqF⟩

/-- A correct vote-k (`2 ≤ k ≤ 4`) is backed by a correct vote-(k−1) for the same value and
view. -/
theorem exists_prev_vote (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {p : P}
    (hp : p ∉ E.faulty) {k r : ℕ} {x : V} (hk2 : 2 ≤ k) (hk4 : k ≤ 4)
    (h : E.voted p ⟨k, r, x⟩) : ∃ q ∉ E.faulty, E.voted q ⟨k - 1, r, x⟩ := by
  obtain ⟨Q, hQ, hQv⟩ := hE.quorum_prev p hp k r x hk2 hk4 h
  exact exists_correct_of_quorum hn hE hQ hQv

/-- Every correct vote is backed by a correct vote-1 for the same value and view. -/
theorem exists_vote1 (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) :
    ∀ k, 1 ≤ k → k ≤ 4 → ∀ {p : P}, p ∉ E.faulty → ∀ {r : ℕ} {x : V},
      E.voted p ⟨k, r, x⟩ → ∃ q ∉ E.faulty, E.voted q ⟨1, r, x⟩ := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hk p hp r x h
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨p, hp, h⟩
    · obtain ⟨q, hq, hqv⟩ := exists_prev_vote hn hE hp (by omega) hk h
      exact ih hk0 (by omega) hq hqv

/-- **Lemma 6.** Two correct vote-k messages (k ∈ {2, 3, 4}) of the same view carry the same
value. -/
theorem lemma6 (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {k r : ℕ} (hk2 : 2 ≤ k)
    (hk4 : k ≤ 4) {p q : P} (hp : p ∉ E.faulty) (hq : q ∉ E.faulty) {x y : V}
    (hx : E.voted p ⟨k, r, x⟩) (hy : E.voted q ⟨k, r, y⟩) : x = y := by
  obtain ⟨Q₁, hQ₁, hv₁⟩ := hE.quorum_prev p hp k r x hk2 hk4 hx
  obtain ⟨Q₂, hQ₂, hv₂⟩ := hE.quorum_prev q hq k r y hk2 hk4 hy
  obtain ⟨c, hc₁, hc₂, hcF⟩ := exists_mem_inter_notMem_of_three_mul_lt hn hE.card_faulty hQ₁ hQ₂
  exact hE.one_val c hcF _ r x y (hv₁ c hc₁ hcF) (hv₂ c hc₂ hcF)

/-- **Lemma 7** (on commitment). At most one value is committed in a view. -/
theorem lemma7 (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {v : ℕ} {x y : V}
    (hx : E.Committed f x v) (hy : E.Committed f y v) : x = y := by
  obtain ⟨Q₁, hQ₁, hv₁⟩ := hx
  obtain ⟨Q₂, hQ₂, hv₂⟩ := hy
  obtain ⟨c, hc₁, hc₂, hcF⟩ := exists_mem_inter_notMem_of_three_mul_lt hn hE.card_faulty hQ₁ hQ₂
  exact hE.one_val c hcF 4 v x y (hv₁ c hc₁ hcF) (hv₂ c hc₂ hcF)

/-- **Lemma 8.** If `x` is committed in view `v` (in particular, if a correct node decides `x` in
view `v`), then no correct node casts a vote-1 for a different value in a later view. -/
theorem lemma8 (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {x : V} {v : ℕ}
    (hc : E.Committed f x v) :
    ∀ v', v < v' → ∀ j ∉ E.faulty, ∀ y : V, E.voted j ⟨1, v', y⟩ → y = x := by
  intro v'
  induction v' using Nat.strong_induction_on with
  | _ v' ih =>
  intro hvv' j hj y hy
  by_contra hyx
  -- the votes in views strictly between `v` and `v'` are all for `x`
  have hmid : ∀ u, v < u → u < v' → ∀ k ∉ E.faulty, ∀ z : V, E.voted k ⟨1, u, z⟩ → z = x :=
    fun u hvu huv' => ih u huv' hvu
  obtain ⟨S, rep, hrep, hrule⟩ := hE.rule3 j hj v' y hy
  rcases hrule with h0 | ⟨Q, hQS, hQ, hcase⟩
  · omega
  obtain ⟨Q4, hQ4, hv4⟩ := hc
  obtain ⟨c, hcQ, hcQ4, hcF⟩ := exists_mem_inter_notMem_of_three_mul_lt hn hE.card_faulty hQ hQ4
  have hcrep := hrep c (hQS hcQ) hcF
  obtain ⟨u', y', htop, hvu'⟩ := hcrep.top_max v x hvv' (hv4 c hcQ4 hcF)
  obtain ⟨hu'v', hcv⟩ := hcrep.top_sound u' y' htop
  rcases hcase with hnone | ⟨w, hwv', hok, hiii⟩
  · rw [hnone c hcQ] at htop; exact absurd htop (by simp)
  -- the view `w` of item 2(b) is above `v`
  have hvw : v < w := by
    rcases hok c hcQ u' y' htop with hlt | ⟨rfl, rfl⟩
    · omega
    · rcases Nat.lt_or_ge v u' with h | h
      · exact h
      · have : u' = v := by omega
        subst this
        exact absurd (hE.one_val c hcF 4 u' x y' (hv4 c hcQ4 hcF) hcv).symm hyx
  -- an honest claim at a view `≥ w` (> v) of a correct node is for `x`
  have hclaim : ∀ z w₁, w ≤ w₁ → Blocking f S rep z w₁ → z = x := by
    intro z w₁ hww₁ ⟨B, hBS, hB, hBc⟩
    obtain ⟨k, hkB, hkF⟩ := exists_mem_notMem_of_card_le_of_lt hE.card_faulty hB
    have hk := hrep k (hBS hkB) hkF
    rcases hk.claims_sound (hBc k hkB) (by omega) with
      ⟨u, hwu, huv', hku⟩ | ⟨u₁, y₁, u₂, y₂, hwu₁, hu₁, hwu₂, hu₂, hy₁₂, -, hk₁, hk₂⟩
    · exact hmid u (by omega) huv' k hkF z hku
    · exact absurd ((hmid u₁ (by omega) hu₁ k hkF y₁ hk₁).trans
        (hmid u₂ (by omega) hu₂ k hkF y₂ hk₂).symm) hy₁₂
  rcases hiii with hA | ⟨-, x₁, x₂, w₁, w₂, hx₁₂, hww₁, hw₁₂, -, hB₁, hB₂⟩
  · exact hyx (hclaim y w le_rfl hA)
  · exact hx₁₂ ((hclaim x₁ w₁ hww₁ hB₁).trans (hclaim x₂ w₂ (by omega) hB₂).symm)

/-- Commitment is unique across views: if `x` is committed in `v` and `y` in `v'`, then
`x = y` (Lemmas 7 and 8). -/
theorem committed_unique (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {x y : V}
    {v v' : ℕ} (hx : E.Committed f x v) (hy : E.Committed f y v') : x = y := by
  have key : ∀ {x y : V} {v v'}, v < v' → E.Committed f x v → E.Committed f y v' → y = x := by
    intro x y v v' hlt hx hy
    obtain ⟨Q, hQ, hQv⟩ := hy
    obtain ⟨q, hq, hqv⟩ := exists_correct_of_quorum hn hE hQ hQv
    obtain ⟨j, hj, hjv⟩ := exists_vote1 hn hE 4 (by omega) le_rfl hq hqv
    exact lemma8 hn hE hx v' hlt j hj y hjv
  rcases lt_trichotomy v v' with h | rfl | h
  · exact (key h hx hy).symm
  · exact lemma7 hn hE hx hy
  · exact key h hy hx

/-- **Theorem 1 (agreement).** No two correct nodes decide different values. -/
theorem agreement (hn : 3 * f < Fintype.card P) (hE : E.SafetyHyp f) {p q : P}
    (hp : p ∉ E.faulty) (hq : q ∉ E.faulty) {x y : V} {v v' : ℕ} (hx : E.decided p x v)
    (hy : E.decided q y v') : x = y :=
  committed_unique hn hE (hE.decided_committed p hp x v hx) (hE.decided_committed q hq y v' hy)

end Execution

end TetraBFT
