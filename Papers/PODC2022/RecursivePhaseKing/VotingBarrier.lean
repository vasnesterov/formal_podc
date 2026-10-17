import Papers.PODC2022.RecursivePhaseKing.Desync
import Papers.PODC2022.RecursivePhaseKing.Subroutines
import Cslib.Foundations.Data.Finset.Quorum

/-!
# Algorithm 7 (electors' broadcast with a voting barrier) and Lemma 4.2 of [LS22]

Lenzen, Sheikholeslami, *A Recursive Early-Stopping Phase King Protocol*, PODC 2022 [LS22],
Section 4.

## Model

* Nodes `P` (`n = |P|`), resilience `t` with `3t < n`, faulty set `F` with `|F| ≤ t` (Byzantine),
  electors `K ⊆ P`, a known bound `T` on the running time of the consensus thread; the loop of
  line 8 has `max {T + 3, 4}` local rounds (`loopLen`).
* Executions are `DRun`s (`Desync.lean`): synchronous lock-step global rounds, node `p` performs
  its local round `ℓ` in global round `σ p + ℓ`; `StartWithin1`: correct nodes start within one
  round of each other. Messages between correct nodes are delivered in the same global round.
* The consensus thread (lines 3–4) runs on separate messages and is abstracted as part of the
  input: `inp i = (b_i, strong_i, cons_i)`, `cons_i = some (τ, c)`: the run terminated after `τ`
  local rounds with output `c`. `ConsCorrect`: if `K` is good (`|K ∩ V_g| > ⌊2|K|/3⌋`), every
  correct elector has `cons = some (τ, c)` with `τ ≤ T` and a common `c`, which is the common input
  of the correct electors if they agree.
* A message carries an optional `elect(c)` and the votes `vote(0)`, `vote(1)` (`Msg`). An elector
  broadcasts `elect(c)` in local round `max τ 1` (lines 5–7). Line 9 is read with `vote(b)` from
  `t + 1` nodes (the paper writes `elect(b)`, a typo): `vote(b)` is broadcast in local round
  `ℓ + 1` (once per `b`) if by the end of round `ℓ` the node has received, during the loop,
  `elect(b)` from `⌈|K|/3⌉` electors or `vote(b)` from `t + 1` nodes (so never in round `0`).
  Lines 11–14: at the end of a round with `vote(b)` from `n - t` nodes the node returns (`b`, or
  its input if strong; `pick` breaks ties); line 15: timeout at the end of round `loopLen T - 1`.
* `alg7 … fix`: `fix = false` is the algorithm of the paper (a node that returns stops sending);
  `fix = true` is a repair: a node that returns still broadcasts, in the next round, the votes it
  qualifies for and has not sent yet, and then stops.

## Results

| [LS22] | Lean |
|---|---|
| Algorithm 7 | `alg7` (`fix = false`), repaired: `alg7` (`fix = true`) |
| Definition 2.5 | `ElectorsBCSpec` (`Subroutines.lean`) |
| Lemma 4.2, validity | `validity` (both versions) |
| Lemma 4.2, electors' agreement | `electorsBC` (repaired); **false** as stated: `cx_not_electorsBC` |
| Lemma 4.2, "within one round" | `within_one` (repaired); **false** as stated: `cx_not_within_one` |
| Lemma 4.2, time `T(k, ⌈k/3⌉-1) + O(1)`, `k = #K` | `terminates` (`max {T+3, 4}` local rounds) |
| Lemma 4.2, early-stopping time `T(k, #(K \ V_g)) + O(1)`, `K` good | `good_ret` (returned by the end of local round `max {D, 1} + 2`) |
| Lemma 4.2, "each node broadcasts at most twice" | `msg_count` (at most 3), `three_bcasts` |
| all bullets (repaired) | `lemma_4_2` |
| voting barrier argument | `barrier`, `first_ret` |
| use in Algorithm 8 (terminated nodes do not participate) | `np_fails`, `ph_fails` |

## Findings

* **Lemma 4.2 is false for Algorithm 7 as stated** (`cx_fails`): `n = 4`, `t = 1`, `K = V`
  (good), consensus correct, all start together. A correct node can return after receiving
  `n - t` votes (some from faulty nodes) without ever having voted itself; the remaining correct
  nodes then miss its vote forever and time out with their own inputs. Both electors' agreement
  and termination within one round fail. The proof's step "all correct nodes broadcast vote(b)"
  overlooks nodes that already returned. Repair: a returning node broadcasts its pending votes
  one more round (`fix = true`); then all bullets hold (`lemma_4_2`, `good_ret`).
* At most three (not two) broadcasts per node: `three_bcasts` (needs `K` not good; minor).
* Inside Algorithm 8, correct nodes that have terminated do not run Algorithm 7; then even the
  repaired barrier fails (`np_fails`; `ph_fails` for the reading of convention (3) where
  terminated nodes are deemed to keep voting, against the unrepaired algorithm).
-/

set_option linter.unusedSectionVars false

namespace RecursivePhaseKing.VotingBarrier

open Finset Cslib.Byzantine.PartialSync

variable {P : Type*} [Fintype P] [DecidableEq P]

/-! ### Algorithm 7 -/

/-- A message of Algorithm 7 outside the consensus thread: an optional `elect(c)` and the votes
`vote(b)` (`vote b = true`). -/
structure Msg where
  /-- `elect c`, if any. -/
  elect : Option Bool
  /-- `vote b = true` iff `vote(b)` is sent. -/
  vote : Bool → Bool

/-- Input of a node: `(b, strong, cons)`; `cons = some (τ, c)`: the consensus thread (only run by
electors) terminated after `τ` local rounds with output `c`; `none`: it did not terminate. -/
abbrev In := Bool × Bool × Option (ℕ × Bool)

/-- Local state of a node running Algorithm 7. -/
structure St (P : Type*) where
  /-- The input value `b_i` (`= op_i` until the node returns). -/
  b : Bool
  /-- The input bit `strong_i`. -/
  strong : Bool
  /-- The result of the consensus thread. -/
  cons : Option (ℕ × Bool)
  /-- `el c`: electors from which `elect(c)` has been received during the loop. -/
  el : Bool → Finset P
  /-- `vt b`: nodes from which `vote(b)` has been received during the loop. -/
  vt : Bool → Finset P
  /-- `sent b`: `vote(b)` has been broadcast. -/
  sent : Bool → Bool
  /-- The returned value. -/
  out : Option Bool
  /-- The node has stopped sending. -/
  fin : Bool

/-- The loop length `max {T + 3, 4}` of line 8 of Algorithm 7. -/
def loopLen (T : ℕ) : ℕ := max (T + 3) 4

/-- `⌈|K|/3⌉`. -/
def thrK (K : Finset P) : ℕ := (K.card + 2) / 3

variable (t : ℕ) (K : Finset P) (T : ℕ) (pick : P → Bool) (fix : Bool)

/-- The precondition of line 9 of Algorithm 7 (with `vote` for the paper's second `elect`):
`elect(b)` from `⌈|K|/3⌉` electors or `vote(b)` from `t + 1` nodes. -/
def qual (s : St P) (b : Bool) : Prop := thrK K ≤ (s.el b).card ∨ t + 1 ≤ (s.vt b).card

instance (s : St P) (b : Bool) : Decidable (qual t K s b) := by unfold qual; infer_instance

/-- Lines 5–7: the `elect` message of local round `ℓ` (in round `max τ 1` after a consensus run
of `τ` rounds). -/
def electMsg (cons : Option (ℕ × Bool)) (ℓ : ℕ) : Option Bool :=
  match cons with
  | some (τ, c) => if ℓ = max τ 1 then some c else none
  | none => none

/-- Lines 9–10: `vote(b)` is broadcast in local round `ℓ` (only once, and never in the first
round, as the precondition refers to messages received during the loop). -/
def voteMsg (ℓ : ℕ) (s : St P) (b : Bool) : Bool :=
  decide (1 ≤ ℓ ∧ qual t K s b ∧ s.sent b = false)

/-- The received message contains `vote(b)`. -/
def isVote (o : Option Msg) (b : Bool) : Bool :=
  match o with
  | some m => m.vote b
  | none => false

/-- The received message contains `elect(b)`. -/
def isElect (o : Option Msg) (b : Bool) : Bool :=
  match o with
  | some m => decide (m.elect = some b)
  | none => false

/-- Line 11: a value for which `n - t` votes have been received (`pk` if both). -/
def win (n : ℕ) (pk : Bool) (vt : Bool → Finset P) : Option Bool :=
  if n - t ≤ (vt true).card then (if n - t ≤ (vt false).card then some pk else some true)
  else if n - t ≤ (vt false).card then some false else none

/-- Electors from which `elect(b)` is received in addition. -/
def newEl (s : St P) (rcv : P → Option Msg) (b : Bool) : Finset P :=
  s.el b ∪ K.filter fun q => isElect (rcv q) b

/-- Nodes from which `vote(b)` is received in addition. -/
def newVt (s : St P) (rcv : P → Option Msg) (b : Bool) : Finset P :=
  s.vt b ∪ univ.filter fun q => isVote (rcv q) b

/-- Lines 11–15: the return value at the end of local round `ℓ`, given the updated votes. -/
def retOut (ℓ : ℕ) (pk : Bool) (s : St P) (vt : Bool → Finset P) : Option Bool :=
  match win t (Fintype.card P) pk vt with
  | some w => some (if s.strong then s.b else w)
  | none => if loopLen T ≤ ℓ + 1 then some s.b else none

/-- Algorithm 7 of [LS22] as a round algorithm (local rounds `0, 1, …`). `fix = false`: as in the
paper (a node that returns stops sending); `fix = true`: the repaired version, in which a node
that has returned still broadcasts, in the next round, the votes it qualifies for and has not
sent yet. `pick p` resolves the arbitrary choice of line 13 when both values have `n - t` votes. -/
def alg7 : RoundAlgorithm P Msg (St P) In Bool where
  init _ x := ⟨x.1, x.2.1, x.2.2, fun _ => ∅, fun _ => ∅, fun _ => false, none, false⟩
  send ℓ p s _ :=
    if s.fin then none
    else if s.out.isSome then (if fix then some ⟨none, voteMsg t K ℓ s⟩ else none)
    else some ⟨if p ∈ K then electMsg s.cons ℓ else none, voteMsg t K ℓ s⟩
  trans ℓ p s rcv :=
    if s.fin then s
    else if s.out.isSome then { s with fin := true }
    else
      { s with
        el := newEl K s rcv
        vt := newVt s rcv
        sent := fun b => s.sent b || voteMsg t K ℓ s b
        out := retOut t T ℓ (pick p) s (newVt s rcv) }
  decide _ s := s.out

/-- The consensus thread is correct (needed only for electors' agreement and the time bound):
if fewer than a third of `K` is faulty, every correct elector terminates within `T` rounds, all
with the same output `c`, and `c` is the common input of the correct electors if there is one. -/
def ConsCorrect (F K : Finset P) (T : ℕ) (inp : P → In) : Prop :=
  2 * K.card / 3 < (K \ F).card → ∃ c : Bool,
    (∀ i ∈ K, i ∉ F → ∃ τ ≤ T, (inp i).2.2 = some (τ, c)) ∧
      ∀ v, (∀ i ∈ K, i ∉ F → (inp i).1 = v) → c = v

/-! ### One-step equations -/

section Steps

variable {t K T pick fix} {ℓ : ℕ} {p q : P} {s : St P} {rcv : P → Option Msg} {b : Bool}

theorem trans_fin (h : s.fin = true) : (alg7 t K T pick fix).trans ℓ p s rcv = s := by
  simp [alg7, h]

theorem trans_ret (h : s.fin = false) (ho : s.out.isSome = true) :
    (alg7 t K T pick fix).trans ℓ p s rcv = { s with fin := true } := by
  simp [alg7, h, ho]

theorem trans_run (h : s.fin = false) (ho : s.out = none) :
    (alg7 t K T pick fix).trans ℓ p s rcv =
      { s with
        el := newEl K s rcv
        vt := newVt s rcv
        sent := fun b => s.sent b || voteMsg t K ℓ s b
        out := retOut t T ℓ (pick p) s (newVt s rcv) } := by
  simp [alg7, h, ho]

theorem trans_b : ((alg7 t K T pick fix).trans ℓ p s rcv).b = s.b := by
  simp only [alg7]; split_ifs <;> rfl

theorem trans_strong : ((alg7 t K T pick fix).trans ℓ p s rcv).strong = s.strong := by
  simp only [alg7]; split_ifs <;> rfl

theorem trans_cons : ((alg7 t K T pick fix).trans ℓ p s rcv).cons = s.cons := by
  simp only [alg7]; split_ifs <;> rfl

theorem send_vote_imp (h : isVote ((alg7 t K T pick fix).send ℓ p s q) b = true) :
    s.fin = false ∧ voteMsg t K ℓ s b = true := by
  simp only [alg7] at h
  split_ifs at h with h1 h2 h3 <;> simp_all [isVote]

theorem send_vote_of (hf : s.fin = false) (ho : s.out = none ∨ fix = true)
    (hv : voteMsg t K ℓ s b = true) : isVote ((alg7 t K T pick fix).send ℓ p s q) b = true := by
  simp only [alg7]
  rcases ho with ho | ho
  · simp [hf, ho, isVote, hv]
  · split_ifs <;> simp_all [isVote]

theorem send_elect_imp (h : isElect ((alg7 t K T pick fix).send ℓ p s q) b = true) :
    s.out = none ∧ p ∈ K ∧ electMsg s.cons ℓ = some b := by
  simp only [alg7] at h
  split_ifs at h with h1 h2 h3 h4 <;> simp_all [isElect]

theorem send_elect_of (hf : s.fin = false) (ho : s.out = none) (hK : p ∈ K)
    (he : electMsg s.cons ℓ = some b) : isElect ((alg7 t K T pick fix).send ℓ p s q) b = true := by
  simp [alg7, hf, ho, hK, he, isElect]

theorem win_some {n : ℕ} {pk : Bool} {vt : Bool → Finset P} {w : Bool}
    (h : win t n pk vt = some w) : n - t ≤ (vt w).card := by
  unfold win at h
  split_ifs at h with h1 h2 h3 <;> (cases h; first | assumption | cases pk <;> assumption)

theorem win_none {n : ℕ} {pk : Bool} {vt : Bool → Finset P} (h : win t n pk vt = none) (w : Bool) :
    (vt w).card < n - t := by
  unfold win at h
  split_ifs at h with h1 h2 h3
  cases w <;> omega

end Steps

/-! ### Executions: basic invariants -/

section Basic

variable {t K T pick fix} {F : Finset P} {inp : P → In} (E : DRun (alg7 t K T pick fix) F inp)
  {ℓ ℓ' : ℕ} {p q : P} {b : Bool} {o : Option Bool}

theorem st0 (p : P) : E.st 0 p =
    ⟨(inp p).1, (inp p).2.1, (inp p).2.2, fun _ => ∅, fun _ => ∅, fun _ => false, none, false⟩ :=
  E.st_zero p

theorem fields (ℓ : ℕ) (p : P) : (E.st ℓ p).b = (inp p).1 ∧ (E.st ℓ p).strong = (inp p).2.1 ∧
    (E.st ℓ p).cons = (inp p).2.2 := by
  induction ℓ with
  | zero => rw [st0]; exact ⟨rfl, rfl, rfl⟩
  | succ ℓ ih => rw [E.st_succ, trans_b, trans_strong, trans_cons]; exact ih

theorem fin_imp (ℓ : ℕ) (p : P) : (E.st ℓ p).fin = true → (E.st ℓ p).out.isSome = true := by
  induction ℓ with
  | zero => simp [st0]
  | succ ℓ ih =>
    rw [E.st_succ]
    cases hf : (E.st ℓ p).fin
    · cases ho : (E.st ℓ p).out with
      | none => rw [trans_run hf ho]; simp [hf]
      | some o => rw [trans_ret hf (by simp [ho])]; simp [ho]
    · rw [trans_fin hf]; exact ih

theorem fin_false_of_none (h : (E.st ℓ p).out = none) : (E.st ℓ p).fin = false := by
  cases hf : (E.st ℓ p).fin
  · rfl
  · have := fin_imp E ℓ p hf; simp [h] at this

theorem fin_succ (ℓ : ℕ) (p : P) : (E.st (ℓ + 1) p).fin = (E.st ℓ p).out.isSome := by
  rw [E.st_succ]
  cases hf : (E.st ℓ p).fin
  · cases ho : (E.st ℓ p).out with
    | none => rw [trans_run hf ho]; simp [hf]
    | some o => rw [trans_ret hf (by simp [ho])]; simp
  · rw [trans_fin hf, hf, fin_imp E ℓ p hf]

theorem out_succ_of_some {o : Bool} (h : (E.st ℓ p).out = some o) :
    (E.st (ℓ + 1) p).out = some o := by
  rw [E.st_succ]
  cases hf : (E.st ℓ p).fin
  · rw [trans_ret hf (by simp [h])]; exact h
  · rw [trans_fin hf]; exact h

theorem out_mono {o : Bool} (h : (E.st ℓ p).out = some o) (hl : ℓ ≤ ℓ') :
    (E.st ℓ' p).out = some o := by
  induction ℓ', hl using Nat.le_induction with
  | base => exact h
  | succ ℓ' _ ih => exact out_succ_of_some E ih

theorem isSome_mono (h : (E.st ℓ p).out.isSome = true) (hl : ℓ ≤ ℓ') :
    (E.st ℓ' p).out.isSome = true := by
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 h
  rw [out_mono E ho hl]; rfl

theorem out_none_of_le (h : (E.st ℓ' p).out = none) (hl : ℓ ≤ ℓ') : (E.st ℓ p).out = none := by
  cases ho : (E.st ℓ p).out with
  | none => rfl
  | some o => rw [out_mono E ho hl] at h; cases h

/-- Every node has returned after `max {T + 3, 4}` local rounds (line 15). -/
theorem out_loopLen (p : P) : (E.st (loopLen T) p).out.isSome = true := by
  have hL : loopLen T = (loopLen T - 1) + 1 := by unfold loopLen; omega
  rw [hL]
  cases ho : (E.st (loopLen T - 1) p).out with
  | some o => rw [out_succ_of_some E ho]; rfl
  | none =>
    rw [E.st_succ, trans_run (fin_false_of_none E ho) ho]
    simp only [retOut]
    split
    · rfl
    · split_ifs with hL
      · rfl
      · exact absurd (by unfold loopLen; omega) hL

/-- The round in which an output was set. -/
theorem exists_ret {o : Bool} (h : (E.st ℓ p).out = some o) :
    ∃ ℓ' < ℓ, (E.st ℓ' p).out = none ∧ (E.st (ℓ' + 1) p).out = some o := by
  induction ℓ with
  | zero => simp [st0] at h
  | succ ℓ ih =>
    cases ho : (E.st ℓ p).out with
    | none => exact ⟨ℓ, by omega, ho, h⟩
    | some o' =>
      have := out_succ_of_some E ho
      rw [h] at this; cases this
      obtain ⟨ℓ', h1, h2⟩ := ih ho
      exact ⟨ℓ', by omega, h2⟩

/-- How a node returns (lines 11–15): with `n - t` votes for `w` (output `w`, or `b_i` if
`strong_i`), or by the timeout (output `b_i`). -/
theorem ret_cases {o : Bool} (ho : (E.st ℓ p).out = none) (h : (E.st (ℓ + 1) p).out = some o) :
    (∃ w, win t (Fintype.card P) (pick p) (E.st (ℓ + 1) p).vt = some w ∧
        o = if (inp p).2.1 then (inp p).1 else w) ∨
      (win t (Fintype.card P) (pick p) (E.st (ℓ + 1) p).vt = none ∧ loopLen T ≤ ℓ + 1 ∧
        o = (inp p).1) := by
  obtain ⟨hb, hs, -⟩ := fields E ℓ p
  rw [E.st_succ, trans_run (fin_false_of_none E ho) ho] at h ⊢
  simp only [retOut] at h ⊢
  split at h
  · rename_i w hw
    left
    refine ⟨w, hw, ?_⟩
    cases h; rw [hb, hs]
  · rename_i hw
    right
    split_ifs at h with hL
    cases h
    exact ⟨hw, hL, hb⟩

/-- A node that has not returned returns as soon as it has `n - t` votes for some value. -/
theorem ret_of_votes {w : Bool} (ho : (E.st ℓ p).out = none)
    (hv : Fintype.card P - t ≤ ((E.st (ℓ + 1) p).vt w).card) :
    (E.st (ℓ + 1) p).out.isSome = true := by
  have hv' := hv
  rw [E.st_succ, trans_run (fin_false_of_none E ho) ho] at hv' ⊢
  simp only [retOut] at hv' ⊢
  split
  · rfl
  · rename_i hw
    have := win_none hw w
    omega

theorem vt_succ_sub (ℓ : ℕ) (p : P) (b : Bool) : (E.st ℓ p).vt b ⊆ (E.st (ℓ + 1) p).vt b := by
  rw [E.st_succ]
  cases hf : (E.st ℓ p).fin
  · cases ho : (E.st ℓ p).out with
    | none => rw [trans_run hf ho]; exact subset_union_left
    | some o => rw [trans_ret hf (by simp [ho])]
  · rw [trans_fin hf]

theorem vt_mono (hl : ℓ ≤ ℓ') : (E.st ℓ p).vt b ⊆ (E.st ℓ' p).vt b := by
  induction ℓ', hl using Nat.le_induction with
  | base => exact Subset.refl _
  | succ ℓ' _ ih => exact ih.trans (vt_succ_sub E ℓ' p b)

theorem el_succ_sub (ℓ : ℕ) (p : P) (b : Bool) : (E.st ℓ p).el b ⊆ (E.st (ℓ + 1) p).el b := by
  rw [E.st_succ]
  cases hf : (E.st ℓ p).fin
  · cases ho : (E.st ℓ p).out with
    | none => rw [trans_run hf ho]; exact subset_union_left
    | some o => rw [trans_ret hf (by simp [ho])]
  · rw [trans_fin hf]

theorem el_mono (hl : ℓ ≤ ℓ') : (E.st ℓ p).el b ⊆ (E.st ℓ' p).el b := by
  induction ℓ', hl using Nat.le_induction with
  | base => exact Subset.refl _
  | succ ℓ' _ ih => exact ih.trans (el_succ_sub E ℓ' p b)

/-- Votes are only recorded when received. -/
theorem mem_vt (h : q ∈ (E.st ℓ p).vt b) : ∃ ℓ' < ℓ, isVote (E.rcv ℓ' p q) b = true := by
  induction ℓ with
  | zero => simp [st0] at h
  | succ ℓ ih =>
    rw [E.st_succ] at h
    cases hf : (E.st ℓ p).fin
    · cases ho : (E.st ℓ p).out with
      | none =>
        rw [trans_run hf ho] at h
        simp only [newVt, mem_union, mem_filter, mem_univ, true_and] at h
        rcases h with h | h
        · obtain ⟨ℓ', h1, h2⟩ := ih h; exact ⟨ℓ', by omega, h2⟩
        · exact ⟨ℓ, by omega, h⟩
      | some o =>
        rw [trans_ret hf (by simp [ho])] at h
        obtain ⟨ℓ', h1, h2⟩ := ih h; exact ⟨ℓ', by omega, h2⟩
    · rw [trans_fin hf] at h
      obtain ⟨ℓ', h1, h2⟩ := ih h; exact ⟨ℓ', by omega, h2⟩

/-- `elect` messages are only recorded from electors, when received. -/
theorem mem_el (h : q ∈ (E.st ℓ p).el b) :
    q ∈ K ∧ ∃ ℓ' < ℓ, isElect (E.rcv ℓ' p q) b = true := by
  induction ℓ with
  | zero => simp [st0] at h
  | succ ℓ ih =>
    rw [E.st_succ] at h
    cases hf : (E.st ℓ p).fin
    · cases ho : (E.st ℓ p).out with
      | none =>
        rw [trans_run hf ho] at h
        simp only [newEl, mem_union, mem_filter] at h
        rcases h with h | h
        · obtain ⟨hK, ℓ', h1, h2⟩ := ih h; exact ⟨hK, ℓ', by omega, h2⟩
        · exact ⟨h.1, ℓ, by omega, h.2⟩
      | some o =>
        rw [trans_ret hf (by simp [ho])] at h
        obtain ⟨hK, ℓ', h1, h2⟩ := ih h; exact ⟨hK, ℓ', by omega, h2⟩
    · rw [trans_fin hf] at h
      obtain ⟨hK, ℓ', h1, h2⟩ := ih h; exact ⟨hK, ℓ', by omega, h2⟩

theorem vt_of_rcv (ho : (E.st ℓ p).out = none) (h : isVote (E.rcv ℓ p q) b = true) :
    q ∈ (E.st (ℓ + 1) p).vt b := by
  rw [E.st_succ, trans_run (fin_false_of_none E ho) ho]
  simp [newVt, h]

theorem el_of_rcv (ho : (E.st ℓ p).out = none) (hK : q ∈ K) (h : isElect (E.rcv ℓ p q) b = true) :
    q ∈ (E.st (ℓ + 1) p).el b := by
  rw [E.st_succ, trans_run (fin_false_of_none E ho) ho]
  simp [newEl, h, hK]

/-- `sent b` records an earlier broadcast of `vote(b)`. -/
theorem sent_spec (h : (E.st ℓ p).sent b = true) :
    ∃ ℓ' < ℓ, (E.st ℓ' p).out = none ∧ voteMsg t K ℓ' (E.st ℓ' p) b = true := by
  induction ℓ with
  | zero => simp [st0] at h
  | succ ℓ ih =>
    rw [E.st_succ] at h
    cases hf : (E.st ℓ p).fin
    · cases ho : (E.st ℓ p).out with
      | none =>
        rw [trans_run hf ho] at h
        simp only [Bool.or_eq_true] at h
        rcases h with h | h
        · obtain ⟨ℓ', h1, h2⟩ := ih h; exact ⟨ℓ', by omega, h2⟩
        · exact ⟨ℓ, by omega, ho, h⟩
      | some o =>
        rw [trans_ret hf (by simp [ho])] at h
        obtain ⟨ℓ', h1, h2⟩ := ih h; exact ⟨ℓ', by omega, h2⟩
    · rw [trans_fin hf] at h
      obtain ⟨ℓ', h1, h2⟩ := ih h; exact ⟨ℓ', by omega, h2⟩

/-- A node that qualifies for `vote(b)` (and still sends) has broadcast `vote(b)` by now. -/
theorem voteSent_of_qual (hf : (E.st ℓ p).fin = false) (h1 : 1 ≤ ℓ) (hq : qual t K (E.st ℓ p) b) :
    ∃ ℓ' ≤ ℓ, (E.st ℓ' p).fin = false ∧ voteMsg t K ℓ' (E.st ℓ' p) b = true := by
  cases hs : (E.st ℓ p).sent b
  · exact ⟨ℓ, le_refl _, hf, by simp [voteMsg, h1, hq, hs]⟩
  · obtain ⟨ℓ', h1', ho, hv⟩ := sent_spec E hs
    exact ⟨ℓ', by omega, fin_false_of_none E ho, hv⟩

theorem sent_or_fin_succ (h : (E.st ℓ p).sent b = true ∨ (E.st ℓ p).fin = true) :
    (E.st (ℓ + 1) p).sent b = true ∨ (E.st (ℓ + 1) p).fin = true := by
  rw [E.st_succ]
  cases hf : (E.st ℓ p).fin
  · cases ho : (E.st ℓ p).out with
    | none =>
      rw [trans_run hf ho]
      simp only [hf, Bool.false_eq_true, or_false] at h
      simp [h]
    | some o => rw [trans_ret hf (by simp [ho])]; simp
  · rw [trans_fin hf]; exact h

/-- After broadcasting `vote(b)`, a node never broadcasts it again. -/
theorem sent_after (hf : (E.st ℓ p).fin = false) (hv : voteMsg t K ℓ (E.st ℓ p) b = true)
    (hl : ℓ < ℓ') : (E.st ℓ' p).sent b = true ∨ (E.st ℓ' p).fin = true := by
  induction ℓ', hl using Nat.le_induction with
  | base =>
    rw [E.st_succ]
    cases ho : (E.st ℓ p).out with
    | none => rw [trans_run hf ho]; simp [hv]
    | some o => rw [trans_ret hf (by simp [ho])]; simp
  | succ ℓ' _ ih => exact sent_or_fin_succ E ih

/-- Validity (lines 12–14): a strong node returns its input. -/
theorem out_strong {o : Bool} (h : (E.st ℓ p).out = some o) (hs : (inp p).2.1 = true) :
    o = (inp p).1 := by
  obtain ⟨ℓ', -, h1, h2⟩ := exists_ret E h
  rcases ret_cases E h1 h2 with ⟨w, -, rfl⟩ | ⟨-, -, rfl⟩
  · simp [hs]
  · rfl

end Basic

/-! ### Messages between correct nodes -/

section Correct

variable {t K T pick fix} {F : Finset P} {inp : P → In} (E : DRun (alg7 t K T pick fix) F inp)
  {ℓ : ℕ} {p q : P} {b : Bool}

theorem rcv_vote_imp (hp : p ∉ F) (hq : q ∉ F) (h : isVote (E.rcv ℓ p q) b = true) :
    E.σ q ≤ E.σ p + ℓ ∧ (E.st (E.σ p + ℓ - E.σ q) q).fin = false ∧
      voteMsg t K (E.σ p + ℓ - E.σ q) (E.st (E.σ p + ℓ - E.σ q) q) b = true := by
  rw [E.honest ℓ p q hp hq] at h
  split_ifs at h with hσ
  · exact ⟨hσ, send_vote_imp h⟩
  · simp [isVote] at h

theorem rcv_elect_imp (hp : p ∉ F) (hq : q ∉ F) (h : isElect (E.rcv ℓ p q) b = true) :
    E.σ q ≤ E.σ p + ℓ ∧ electMsg (inp q).2.2 (E.σ p + ℓ - E.σ q) = some b := by
  rw [E.honest ℓ p q hp hq] at h
  split_ifs at h with hσ
  · obtain ⟨-, -, he⟩ := send_elect_imp h
    rw [(fields E _ q).2.2] at he
    exact ⟨hσ, he⟩
  · simp [isElect] at h

theorem recv_vote (hp : p ∉ F) (hq : q ∉ F) {ℓq : ℕ} (hσ : E.σ p ≤ E.σ q + ℓq)
    (hs : isVote ((alg7 t K T pick fix).send ℓq q (E.st ℓq q) p) b = true)
    (ho : (E.st (E.σ q + ℓq - E.σ p) p).out = none) :
    q ∈ (E.st (E.σ q + ℓq - E.σ p + 1) p).vt b := by
  apply vt_of_rcv E ho
  rw [E.honest _ p q hp hq]
  have h1 : E.σ q ≤ E.σ p + (E.σ q + ℓq - E.σ p) := by omega
  have h2 : E.σ p + (E.σ q + ℓq - E.σ p) - E.σ q = ℓq := by omega
  simp only [h1, ↓reduceIte, h2]; exact hs

theorem recv_elect (hp : p ∉ F) (hq : q ∉ F) (hK : q ∈ K) {ℓq : ℕ} (hσ : E.σ p ≤ E.σ q + ℓq)
    (hs : isElect ((alg7 t K T pick fix).send ℓq q (E.st ℓq q) p) b = true)
    (ho : (E.st (E.σ q + ℓq - E.σ p) p).out = none) :
    q ∈ (E.st (E.σ q + ℓq - E.σ p + 1) p).el b := by
  apply el_of_rcv E ho hK
  rw [E.honest _ p q hp hq]
  have h1 : E.σ q ≤ E.σ p + (E.σ q + ℓq - E.σ p) := by omega
  have h2 : E.σ p + (E.σ q + ℓq - E.σ p) - E.σ q = ℓq := by omega
  simp only [h1, ↓reduceIte, h2]; exact hs

end Correct

/-! ### The first return and the voting barrier -/

section Barrier

variable {t K T pick fix} {F : Finset P} {inp : P → In} (E : DRun (alg7 t K T pick fix) F inp)

/-- Some correct node has returned by the end of global round `g`. -/
def RetBy (g : ℕ) : Prop := ∃ u ∉ F, ∃ ℓ, E.σ u + ℓ = g ∧ (E.st (ℓ + 1) u).out.isSome = true

/-- No correct node has returned before global round `g`. -/
def NoRetBefore (g : ℕ) : Prop := ∀ u ∉ F, E.σ u ≤ g → (E.st (g - E.σ u) u).out = none

theorem noRetBefore_of_not {g : ℕ} (h : ¬ RetBy E g) : NoRetBefore E (g + 1) := by
  intro u hu hσ
  cases hk : g + 1 - E.σ u with
  | zero => simp [st0]
  | succ k =>
    cases ho : (E.st (k + 1) u).out with
    | none => rfl
    | some o => exact absurd ⟨u, hu, k, by omega, by simp [ho]⟩ h

/-- The earliest global round in which a correct node returns. -/
theorem first_ret {g : ℕ} (h : RetBy E g) : ∃ G ≤ g, NoRetBefore E G ∧
    ∃ r ∉ F, E.σ r ≤ G ∧ (E.st (G - E.σ r) r).out = none ∧
      (E.st (G - E.σ r + 1) r).out.isSome = true := by
  classical
  have hex : ∃ g, RetBy E g := ⟨g, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, ?_, ?_⟩
  · intro u hu hσ
    cases hk : Nat.find hex - E.σ u with
    | zero => simp [st0]
    | succ k =>
      cases ho : (E.st (k + 1) u).out with
      | none => rfl
      | some o =>
        exact absurd ⟨u, hu, k, rfl, by simp [ho]⟩ (Nat.find_min hex (by omega))
  · obtain ⟨r, hr, ℓ, hℓ, hs⟩ := Nat.find_spec hex
    refine ⟨r, hr, by omega, ?_, by rw [show Nat.find hex - E.σ r = ℓ by omega]; exact hs⟩
    cases hk : Nat.find hex - E.σ r with
    | zero => simp [st0]
    | succ k =>
      cases ho : (E.st (k + 1) r).out with
      | none => rfl
      | some o =>
        exact absurd ⟨r, hr, k, rfl, by simp [ho]⟩ (Nat.find_min hex (by omega))

/-- **The voting barrier** (repaired Algorithm 7). If no correct node has returned before global
round `G` and the correct node `r` has `n - t` votes for `w` at the end of global round `G`, then
every correct node that has not returned by the end of global round `G` has `n - t` votes for `w`
at the end of global round `G + 1`. -/
theorem barrier (hfix : fix = true) (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hS : E.StartWithin1) {G : ℕ} (hG : NoRetBefore E G) {r : P} (hr : r ∉ F)
    (hσr : E.σ r ≤ G) {w : Bool}
    (hw : Fintype.card P - t ≤ ((E.st (G - E.σ r + 1) r).vt w).card) {q : P} (hq : q ∉ F)
    (hqo : (E.st (G + 1 - E.σ q) q).out = none) :
    Fintype.card P - t ≤ ((E.st (G + 2 - E.σ q) q).vt w).card := by
  set C := ((E.st (G - E.σ r + 1) r).vt w).filter (· ∉ F) with hC
  have hCc : t + 1 ≤ C.card := by
    have := card_sub_card_le_card_filter_notMem ((E.st (G - E.σ r + 1) r).vt w) F
    rw [← hC] at this; omega
  -- every correct voter seen by `r` voted in some local round `≥ 1`, by global round `G`
  have fact1 : ∀ s ∈ C, ∃ ℓs, 1 ≤ ℓs ∧ E.σ s + ℓs ≤ G ∧ (E.st ℓs s).fin = false ∧
      voteMsg t K ℓs (E.st ℓs s) w = true := by
    intro s hs
    rw [hC, mem_filter] at hs
    obtain ⟨ℓ', hℓ', hv⟩ := mem_vt E hs.1
    obtain ⟨hσ, hf, hvm⟩ := rcv_vote_imp E hr hs.2 hv
    have h1 : 1 ≤ E.σ r + ℓ' - E.σ s := by simp [voteMsg] at hvm; exact hvm.1
    exact ⟨_, h1, by omega, hf, hvm⟩
  obtain ⟨s0, hs0⟩ : C.Nonempty := by rw [← card_pos]; omega
  have hs0F : s0 ∉ F := (mem_filter.1 hs0).2
  obtain ⟨ℓ0, h10, h20, -, -⟩ := fact1 s0 hs0
  have hσG : ∀ u ∉ F, E.σ u ≤ G := fun u hu => by have := hS u s0 hu hs0F; omega
  -- every correct node has the votes of `C` by the end of global round `G`
  have fact3 : ∀ u ∉ F, C ⊆ (E.st (G - E.σ u + 1) u).vt w := by
    intro u hu s hs
    obtain ⟨ℓs, h1, h2, hf, hvm⟩ := fact1 s hs
    have hsF : s ∉ F := (mem_filter.1 hs).2
    have hσ : E.σ u ≤ E.σ s + ℓs := by have := hS u s hu hsF; omega
    have hmem := recv_vote E hu hsF hσ (send_vote_of hf (Or.inr hfix) hvm)
      (out_none_of_le E (hG u hu (hσG u hu)) (by omega))
    exact vt_mono E (by omega) hmem
  -- hence every correct node broadcasts `vote(w)` by global round `G + 1`
  have fact4 : ∀ u ∉ F, ∃ ℓu, 1 ≤ ℓu ∧ E.σ u + ℓu ≤ G + 1 ∧ (E.st ℓu u).fin = false ∧
      voteMsg t K ℓu (E.st ℓu u) w = true := by
    intro u hu
    have hq' : qual t K (E.st (G - E.σ u + 1) u) w :=
      Or.inr (le_trans hCc (card_le_card (fact3 u hu)))
    have hf : (E.st (G - E.σ u + 1) u).fin = false := by
      rw [fin_succ, hG u hu (hσG u hu)]; rfl
    obtain ⟨ℓu, hle, hf', hvm⟩ := voteSent_of_qual E hf (by omega) hq'
    have h1 : 1 ≤ ℓu := by simp [voteMsg] at hvm; exact hvm.1
    exact ⟨ℓu, h1, by have := hσG u hu; omega, hf', hvm⟩
  -- and `q` receives all these votes by the end of global round `G + 1`
  have fact5 : ∀ u ∉ F, u ∈ (E.st (G + 2 - E.σ q) q).vt w := by
    intro u hu
    obtain ⟨ℓu, h1, h2, hf, hvm⟩ := fact4 u hu
    have hσ : E.σ q ≤ E.σ u + ℓu := by have := hS q u hq hu; omega
    have hmem := recv_vote E hq hu hσ (send_vote_of hf (Or.inr hfix) hvm)
      (out_none_of_le E hqo (by omega))
    exact vt_mono E (by omega) hmem
  have := card_sub_card_le_of_forall_notMem fact5
  omega

end Barrier


/-! ### Lemma 4.2 for the repaired algorithm -/

section Main

variable {t K T pick fix} {F : Finset P} {inp : P → In} (E : DRun (alg7 t K T pick fix) F inp)

/-- The output of node `p` (set after at most `max {T + 3, 4}` rounds, see `out_loopLen`). -/
def outp (p : P) : Bool := ((E.st (loopLen T) p).out).getD (inp p).1

theorem out_loopLen_eq (p : P) : (E.st (loopLen T) p).out = some (outp E p) := by
  have := out_loopLen E p
  unfold outp
  cases h : (E.st (loopLen T) p).out with
  | none => simp [h] at this
  | some o => rfl

/-- Lemma 4.2 of [LS22], second bullet ("correct nodes terminate within one round of each
other"), for the repaired Algorithm 7: if the correct node `p` has returned by the end of its local
round `ℓ` (global round `σ p + ℓ`), every correct node `q` has returned by the end of global round
`σ p + ℓ + 1` (its local round `σ p + ℓ + 1 - σ q`). -/
theorem within_one (hfix : fix = true) (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hS : E.StartWithin1) {p q : P} (hp : p ∉ F) (hq : q ∉ F) {ℓ : ℕ}
    (h : (E.st (ℓ + 1) p).out.isSome = true) :
    (E.st (E.σ p + ℓ + 2 - E.σ q) q).out.isSome = true := by
  obtain ⟨G, hGle, hG, r, hr, hσr, hr0, hr1⟩ := first_ret E ⟨p, hp, ℓ, rfl, h⟩
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hr1
  have hσq := hS q r hq hr
  rcases ret_cases E hr0 ho with ⟨w, hw, -⟩ | ⟨-, hL, -⟩
  · have hv := barrier E hfix h3 hF hS hG hr hσr (win_some hw) hq
    cases hqo : (E.st (G + 1 - E.σ q) q).out with
    | some o' => exact isSome_mono E (ℓ := G + 1 - E.σ q) (by simp [hqo]) (by omega)
    | none =>
      have h1 := ret_of_votes E (ℓ := G + 1 - E.σ q) hqo
        (by rw [show G + 1 - E.σ q + 1 = G + 2 - E.σ q by omega]; exact hv hqo)
      exact isSome_mono E h1 (by omega)
  · exact isSome_mono E (out_loopLen E q) (by omega)

/-- If fewer than a third of `K` is faulty and all correct electors output `c`, no correct node
ever broadcasts `vote(!c)`. -/
theorem no_bad_vote (hF : F.card ≤ t) (hK : 2 * K.card / 3 < (K \ F).card) {c : Bool}
    (hc : ∀ i ∈ K, i ∉ F → ∃ τ, (inp i).2.2 = some (τ, c)) :
    ∀ q ∉ F, ∀ ℓ, voteMsg t K ℓ (E.st ℓ q) (!c) = false := by
  suffices H : ∀ g, ∀ q ∉ F, ∀ ℓ, E.σ q + ℓ = g → voteMsg t K ℓ (E.st ℓ q) (!c) = false from
    fun q hq ℓ => H _ q hq ℓ rfl
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
  intro q hq ℓ hg
  cases hv : voteMsg t K ℓ (E.st ℓ q) (!c)
  · rfl
  simp only [voteMsg, decide_eq_true_eq] at hv
  obtain ⟨-, hqual, -⟩ := hv
  rcases hqual with hel | hvt
  · -- `elect(!c)` is received only from faulty electors
    have hsub : (E.st ℓ q).el (!c) ⊆ K ∩ F := by
      intro r hr
      obtain ⟨hrK, ℓ', -, he⟩ := mem_el E hr
      refine mem_inter.2 ⟨hrK, ?_⟩
      by_contra hrF
      obtain ⟨-, he'⟩ := rcv_elect_imp E hq hrF he
      obtain ⟨τ, hτ⟩ := hc r hrK hrF
      rw [hτ] at he'
      simp only [electMsg] at he'
      split_ifs at he'
      cases c <;> simp at he'
    have := card_le_card hsub
    have hg := (good_iff F K).1 hK
    unfold thrK at hel
    omega
  · -- `vote(!c)` is received only from faulty nodes (induction on the global round)
    have hsub : (E.st ℓ q).vt (!c) ⊆ F := by
      intro r hr
      obtain ⟨ℓ', hℓ', hv⟩ := mem_vt E hr
      by_contra hrF
      obtain ⟨hσ, -, hvm⟩ := rcv_vote_imp E hq hrF hv
      have := ih (E.σ q + ℓ') (by omega) r hrF (E.σ q + ℓ' - E.σ r) (by omega)
      rw [this] at hvm; cases hvm
    have := card_le_card hsub
    omega

/-- Under the same hypotheses, a value with `n - t` votes is `c`. -/
theorem val_of_votes (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hK : 2 * K.card / 3 < (K \ F).card) {c : Bool}
    (hc : ∀ i ∈ K, i ∉ F → ∃ τ, (inp i).2.2 = some (τ, c)) {p : P} (hp : p ∉ F) {j : ℕ}
    {w : Bool} (hv : Fintype.card P - t ≤ ((E.st j p).vt w).card) : w = c := by
  obtain ⟨r, hr, hrF⟩ := exists_mem_notMem_of_card_lt_card (s := F) (t := (E.st j p).vt w)
    (by omega)
  obtain ⟨ℓ', -, hvote⟩ := mem_vt E hr
  obtain ⟨-, -, hvm⟩ := rcv_vote_imp E hp hrF hvote
  by_contra hne
  have hw : w = !c := by cases w <;> cases c <;> simp_all
  rw [hw, no_bad_vote E hF hK hc r hrF] at hvm
  cases hvm

/-- Lemma 4.2 of [LS22], third bullet, in the early-stopping form `T(|K|, |K \ V_g|) + O(1)`
(repaired Algorithm 7): if fewer than a third of `K` is faulty and every correct elector's
consensus run terminated within `D ≤ T` rounds with output `c`, then every correct node has
returned by the end of its local round `max {D, 1} + 2`, with output `c` (or its input if strong). -/
theorem good_ret (hfix : fix = true) (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hS : E.StartWithin1) (hK : 2 * K.card / 3 < (K \ F).card) {c : Bool} {D : ℕ} (hD : D ≤ T)
    (hc : ∀ i ∈ K, i ∉ F → ∃ τ ≤ D, (inp i).2.2 = some (τ, c)) {p : P} (hp : p ∉ F) :
    (E.st (max D 1 + 3) p).out = some (if (inp p).2.1 then (inp p).1 else c) := by
  have hc' : ∀ i ∈ K, i ∉ F → ∃ τ, (inp i).2.2 = some (τ, c) := fun i hi hiF => by
    obtain ⟨τ, -, h⟩ := hc i hi hiF; exact ⟨τ, h⟩
  obtain ⟨p0, hp0, hmin⟩ := exists_min_image (univ.filter (· ∉ F)) E.σ ⟨p, by simp [hp]⟩
  have hp0F : p0 ∉ F := (mem_filter.1 hp0).2
  have hlow : ∀ u ∉ F, E.σ p0 ≤ E.σ u := fun u hu => hmin u (by simp [hu])
  have hhigh : ∀ u ∉ F, E.σ u ≤ E.σ p0 + 1 := fun u hu => hS u p0 hu hp0F
  set m := max D 1 with hm
  set Gs := E.σ p0 + m + 2 with hGs
  have hLm : m + 2 < loopLen T := by unfold loopLen; omega
  -- by the end of global round `Gs`, every correct node has returned or has `n - t` votes for `c`
  have claim : ∀ q ∉ F, (E.st (Gs - E.σ q) q).out = none →
      Fintype.card P - t ≤ ((E.st (Gs - E.σ q + 1) q).vt c).card := by
    intro q hq hqo
    have hql := hlow q hq
    have hqh := hhigh q hq
    by_cases hR : RetBy E (Gs - 1)
    · obtain ⟨G, hGle, hG, r, hr, hσr, hr0, hr1⟩ := first_ret E hR
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hr1
      have hrl := hlow r hr
      rcases ret_cases E hr0 ho with ⟨w, hw, -⟩ | ⟨-, hL, -⟩
      · have hwc := val_of_votes E h3 hF hK hc' hr (win_some hw)
        subst hwc
        have hv := barrier E hfix h3 hF hS hG hr hσr (win_some hw) hq
          (out_none_of_le E hqo (by omega))
        exact le_trans hv (card_le_card (vt_mono E (by omega)))
      · exfalso; omega
    · have hG := noRetBefore_of_not E hR
      rw [show Gs - 1 + 1 = Gs by omega] at hG
      -- every correct node broadcasts `vote(c)` by global round `Gs`
      have hvote : ∀ u ∉ F, ∃ ℓu, 1 ≤ ℓu ∧ E.σ u + ℓu ≤ Gs ∧ (E.st ℓu u).fin = false ∧
          voteMsg t K ℓu (E.st ℓu u) c = true := by
        intro u hu
        have hul := hlow u hu
        have huh := hhigh u hu
        have hu0 := hG u hu (by omega)
        have hsub : K \ F ⊆ (E.st (Gs - E.σ u) u).el c := by
          intro e he
          rw [mem_sdiff] at he
          obtain ⟨τ, hτD, hτ⟩ := hc e he.1 he.2
          have hel := hlow e he.2
          have heh := hhigh e he.2
          have he0 := hG e he.2 (by omega)
          have hme : max τ 1 ≤ m := by omega
          have heo : (E.st (max τ 1) e).out = none := out_none_of_le E he0 (by omega)
          have hs : isElect ((alg7 t K T pick fix).send (max τ 1) e (E.st (max τ 1) e) u) c =
              true :=
            send_elect_of (fin_false_of_none E heo) heo he.1
              (by rw [(fields E _ e).2.2, hτ]; simp [electMsg])
          have hσ : E.σ u ≤ E.σ e + max τ 1 := by have := hS u e hu he.2; omega
          have hmem := recv_elect E hu he.2 he.1 hσ hs (out_none_of_le E hu0 (by omega))
          exact el_mono E (by omega) hmem
        have hq' : qual t K (E.st (Gs - E.σ u) u) c := by
          left; have := card_le_card hsub; unfold thrK; omega
        obtain ⟨ℓu, hle, hf, hvm⟩ :=
          voteSent_of_qual E (fin_false_of_none E hu0) (by omega) hq'
        have h1 : 1 ≤ ℓu := by simp [voteMsg] at hvm; exact hvm.1
        exact ⟨ℓu, h1, by omega, hf, hvm⟩
      have hall : ∀ u ∉ F, u ∈ (E.st (Gs - E.σ q + 1) q).vt c := by
        intro u hu
        obtain ⟨ℓu, h1, h2, hf, hvm⟩ := hvote u hu
        have hσ : E.σ q ≤ E.σ u + ℓu := by have := hS q u hq hu; omega
        have hmem := recv_vote E hq hu hσ (send_vote_of hf (Or.inr hfix) hvm)
          (out_none_of_le E hqo (by omega))
        exact vt_mono E (by omega) hmem
      have := card_sub_card_le_of_forall_notMem hall
      omega
  have hpl := hlow p hp
  have hph := hhigh p hp
  cases hpo : (E.st (Gs - E.σ p) p).out with
  | none =>
    have hv := claim p hp hpo
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 (ret_of_votes E hpo hv)
    rcases ret_cases E hpo ho with ⟨w, hw, rfl⟩ | ⟨hw, -, -⟩
    · rw [val_of_votes E h3 hF hK hc' hp (win_some hw)] at ho
      exact out_mono E ho (by omega)
    · exact absurd (win_none hw c) (by omega)
  | some o =>
    obtain ⟨ℓ', hℓ', h1, h2⟩ := exists_ret E hpo
    rcases ret_cases E h1 h2 with ⟨w, hw, rfl⟩ | ⟨-, hL, -⟩
    · rw [val_of_votes E h3 hF hK hc' hp (win_some hw)] at hpo
      exact out_mono E hpo (by omega)
    · exfalso; omega

/-- Lemma 4.2 of [LS22], third bullet (worst case): every node returns within
`max {T + 3, 4}` local rounds. -/
theorem terminates (p : P) : (E.st (loopLen T) p).out.isSome = true := out_loopLen E p

/-- Validity part of Lemma 4.2 of [LS22] (both versions of Algorithm 7): strong nodes return their
input. -/
theorem validity (v : Bool) (hv : ∀ i ∉ F, (inp i).1 = v ∧ (inp i).2.1 = true) :
    ∀ i ∉ F, outp E i = v := fun i hi => by
  rw [out_strong E (out_loopLen_eq E i) (hv i hi).2]; exact (hv i hi).1

/-- Lemma 4.2 of [LS22], first bullet: the repaired Algorithm 7 implements electors' broadcast
(Definition 2.5), given a correct consensus thread. -/
theorem electorsBC (hfix : fix = true) (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hS : E.StartWithin1) (hcons : ConsCorrect F K T inp) :
    ElectorsBCSpec F K (fun i => (inp i).1) (fun i => (inp i).2.1) (outp E) := by
  refine ⟨fun v hv i hi => ?_, fun hK hwa i hi j hj => ?_⟩
  · rw [out_strong E (out_loopLen_eq E i) (hv i hi).2]; exact (hv i hi).1
  · obtain ⟨c, hc, hval⟩ := hcons hK
    have key : ∀ i ∉ F, outp E i = if (inp i).2.1 then (inp i).1 else c := by
      intro i hi
      have h1 := good_ret E hfix h3 hF hS hK le_rfl hc hi
      rw [show max T 1 + 3 = loopLen T by unfold loopLen; omega, out_loopLen_eq E i] at h1
      exact Option.some.inj h1
    by_cases hs : ∃ k ∉ F, (inp k).2.1 = true
    · obtain ⟨k, hk, hks⟩ := hs
      have hb : ∀ j ∉ F, (inp j).1 = (inp k).1 := fun j hj => hwa k hk hks j hj
      have hck : c = (inp k).1 := hval _ fun i _ hiF => hb i hiF
      have hall : ∀ i ∉ F, outp E i = (inp k).1 := by
        intro i hi; rw [key i hi]; split_ifs <;> simp [hb i hi, hck]
      rw [hall i hi, hall j hj]
    · have hs' : ∀ k ∉ F, (inp k).2.1 = false := fun k hk => by
        cases h : (inp k).2.1
        · rfl
        · exact absurd ⟨k, hk, h⟩ hs
      rw [key i hi, key j hj, hs' i hi, hs' j hj]; rfl

end Main

/-! ### Message complexity -/

section Messages

variable {t K T pick fix} {F : Finset P} {inp : P → In} (E : DRun (alg7 t K T pick fix) F inp)

/-- The number of broadcasts (`elect`, `vote(0)`, `vote(1)`) contained in a message. -/
def nBcast (o : Option Msg) : ℕ :=
  (if (o.bind Msg.elect).isSome then 1 else 0) + (if isVote o false then 1 else 0) +
    (if isVote o true then 1 else 0)

theorem send_elect_isSome {ℓ : ℕ} {p q : P} {s : St P}
    (h : (((alg7 t K T pick fix).send ℓ p s q).bind Msg.elect).isSome = true) :
    ∃ τ c, s.cons = some (τ, c) ∧ ℓ = max τ 1 := by
  simp only [alg7] at h
  split_ifs at h <;> simp only [Option.bind_none, Option.bind_some, Option.isSome_none,
    Bool.false_eq_true] at h
  revert h
  unfold electMsg
  rcases s.cons with _ | ⟨τ, c⟩
  · simp
  · simp only
    split_ifs with h1
    · exact fun _ => ⟨τ, c, rfl, h1⟩
    · simp

theorem elect_unique (p q q' : P) {ℓ ℓ' : ℕ}
    (h : (((alg7 t K T pick fix).send ℓ p (E.st ℓ p) q).bind Msg.elect).isSome = true)
    (h' : (((alg7 t K T pick fix).send ℓ' p (E.st ℓ' p) q').bind Msg.elect).isSome = true) :
    ℓ = ℓ' := by
  obtain ⟨τ, c, hc, rfl⟩ := send_elect_isSome h
  obtain ⟨τ', c', hc', rfl⟩ := send_elect_isSome h'
  rw [(fields E _ p).2.2] at hc hc'
  rw [hc] at hc'
  cases hc'
  rfl

theorem vote_unique (p q q' : P) (b : Bool) {ℓ ℓ' : ℕ}
    (h : isVote ((alg7 t K T pick fix).send ℓ p (E.st ℓ p) q) b = true)
    (h' : isVote ((alg7 t K T pick fix).send ℓ' p (E.st ℓ' p) q') b = true) : ℓ = ℓ' := by
  have aux : ∀ {a c : ℕ} {q q' : P}, a < c →
      isVote ((alg7 t K T pick fix).send a p (E.st a p) q) b = true →
      isVote ((alg7 t K T pick fix).send c p (E.st c p) q') b = true → False := by
    intro a c q q' hac ha hc
    obtain ⟨hf, hv⟩ := send_vote_imp ha
    obtain ⟨hf', hv'⟩ := send_vote_imp hc
    rcases sent_after E hf hv hac with hs | hs
    · simp [voteMsg, hs] at hv'
    · rw [hs] at hf'; cases hf'
  rcases lt_trichotomy ℓ ℓ' with hl | hl | hl
  · exact (aux hl h h').elim
  · exact hl
  · exact (aux hl h' h).elim

/-- Message complexity in Lemma 4.2 of [LS22] (fourth bullet): apart from the consensus thread,
each node broadcasts at most three times in total (`elect` once, `vote(0)` once, `vote(1)`
once). The paper says "at most twice"; see `three_bcasts` for a node broadcasting three times. -/
theorem msg_count (p q : P) (N : ℕ) :
    ∑ ℓ ∈ range N, nBcast ((alg7 t K T pick fix).send ℓ p (E.st ℓ p) q) ≤ 3 := by
  simp only [nBcast, sum_add_distrib, sum_boole, Nat.cast_id]
  have h1 : ((range N).filter fun ℓ =>
      (((alg7 t K T pick fix).send ℓ p (E.st ℓ p) q).bind Msg.elect).isSome = true).card ≤ 1 :=
    card_le_one.2 fun a ha b hb => elect_unique E p q q (mem_filter.1 ha).2 (mem_filter.1 hb).2
  have h2 : ((range N).filter fun ℓ =>
      isVote ((alg7 t K T pick fix).send ℓ p (E.st ℓ p) q) false = true).card ≤ 1 :=
    card_le_one.2 fun a ha b hb =>
      vote_unique E p q q false (mem_filter.1 ha).2 (mem_filter.1 hb).2
  have h3 : ((range N).filter fun ℓ =>
      isVote ((alg7 t K T pick fix).send ℓ p (E.st ℓ p) q) true = true).card ≤ 1 :=
    card_le_one.2 fun a ha b hb =>
      vote_unique E p q q true (mem_filter.1 ha).2 (mem_filter.1 hb).2
  omega

/-- **Lemma 4.2 of [LS22]** for the repaired Algorithm 7 (`fix = true`), with correct nodes starting
within one round of each other: electors' broadcast (Definition 2.5), termination within
`max {T + 3, 4}` local rounds, termination within one global round of each other, and at most
three broadcasts per node outside the consensus thread. The early-stopping time bound is
`good_ret`. -/
theorem lemma_4_2 (hfix : fix = true) (h3 : 3 * t < Fintype.card P) (hF : F.card ≤ t)
    (hS : E.StartWithin1) (hcons : ConsCorrect F K T inp) :
    ElectorsBCSpec F K (fun i => (inp i).1) (fun i => (inp i).2.1) (outp E) ∧
      (∀ p, (E.st (loopLen T) p).out = some (outp E p)) ∧
      (∀ p q, p ∉ F → q ∉ F → ∀ ℓ, (E.st (ℓ + 1) p).out.isSome = true →
        (E.st (E.σ p + ℓ + 2 - E.σ q) q).out.isSome = true) ∧
      ∀ p q N, ∑ ℓ ∈ range N, nBcast ((alg7 t K T pick fix).send ℓ p (E.st ℓ p) q) ≤ 3 :=
  ⟨electorsBC E hfix h3 hF hS hcons, out_loopLen_eq E,
    fun _ _ hp hq _ h => within_one E hfix h3 hF hS hp hq h, msg_count E⟩

end Messages

/-! ### Concrete executions -/

section Sync

variable {S VI VO M : Type*}

/-- States of the synchronous execution (all nodes start in global round `0`) in which the nodes of
`F` send `adv ℓ p q` to `p` in round `ℓ`. -/
def syncSt (A : RoundAlgorithm P M S VI VO) (F : Finset P) (inp : P → VI)
    (adv : ℕ → P → P → Option M) : ℕ → P → S
  | 0 => fun p => A.init p (inp p)
  | ℓ + 1 => fun p => A.trans ℓ p (syncSt A F inp adv ℓ p)
      (fun q => if q ∈ F then adv ℓ p q else A.send ℓ q (syncSt A F inp adv ℓ q) p)

/-- The synchronous execution as a `DRun` (`σ = 0`); every adversary yields one. -/
def syncRun (A : RoundAlgorithm P M S VI VO) (F : Finset P) (inp : P → VI)
    (adv : ℕ → P → P → Option M) : DRun A F inp where
  σ _ := 0
  st := syncSt A F inp adv
  rcv ℓ p q := if q ∈ F then adv ℓ p q else A.send ℓ q (syncSt A F inp adv ℓ q) p
  st_zero _ := rfl
  st_succ _ _ := rfl
  honest ℓ p q _ hq := by simp [hq]

theorem syncRun_startWithin1 (A : RoundAlgorithm P M S VI VO) (F : Finset P) (inp : P → VI)
    (adv : ℕ → P → P → Option M) : (syncRun A F inp adv).StartWithin1 :=
  fun _ _ _ _ => by simp [syncRun]

end Sync

/-! ### Counterexample: Lemma 4.2 fails for Algorithm 7 as stated -/

section Counterexample

/-- Inputs of the counterexample (`n = 4`, `t = 1`, node `0` faulty, `K = V`, `T = 2`): no node
is strong; the correct electors `1, 2, 3` have inputs `1, 0, 0`, and their consensus run outputs
`1` after `1, 2, 2` rounds. -/
def cxInp : Fin 4 → In
  | 1 => (true, false, some (1, true))
  | 2 => (false, false, some (2, true))
  | 3 => (false, false, some (2, true))
  | _ => (false, false, none)

/-- The faulty node `0` sends `elect(1)` to nodes `1, 2` in round `1` and `vote(1)` to node `3`
in round `2` (0-based local rounds), nothing else. -/
def cxAdv (ℓ : ℕ) (p q : Fin 4) : Option Msg :=
  if q = 0 ∧ ℓ = 1 ∧ (p = 1 ∨ p = 2) then some ⟨some true, fun _ => false⟩
  else if q = 0 ∧ ℓ = 2 ∧ p = 3 then some ⟨none, fun b => b⟩
  else none

/-- The execution of Algorithm 7 (`fix = false`: as in the paper, or `true`: repaired). -/
abbrev cxRun (fix : Bool) :=
  syncRun (alg7 1 (univ : Finset (Fin 4)) 2 (fun _ => true) fix) {0} cxInp cxAdv

/-- The instance satisfies all hypotheses of Lemma 4.2 and of electors' agreement: `3t < n`,
`|F| ≤ t`, `K` is good (`|K ∩ V_g| = 3 > ⌊2|K|/3⌋ = 2`), the consensus thread is correct, and the
inputs satisfy weak agreement (nobody is strong). -/
theorem cx_hyps : 3 * 1 < Fintype.card (Fin 4) ∧ ({0} : Finset (Fin 4)).card ≤ 1 ∧
    2 * (univ : Finset (Fin 4)).card / 3 < (univ \ {0} : Finset (Fin 4)).card ∧
    ConsCorrect {0} univ 2 cxInp ∧
    WeakAgreement {0} (fun i => (cxInp i).1) (fun i => (cxInp i).2.1) := by
  refine ⟨by decide, by decide, by decide, fun _ => ⟨true, ?_, ?_⟩, ?_⟩
  · intro i _ hi
    fin_cases i
    · simp at hi
    · exact ⟨1, by norm_num, rfl⟩
    · exact ⟨2, le_rfl, rfl⟩
    · exact ⟨2, le_rfl, rfl⟩
  · intro v hv
    exact hv 1 (mem_univ _) (by decide)
  · intro i _ hs
    fin_cases i <;> simp [cxInp] at hs

/-- **Counterexample to Lemma 4.2 of [LS22]** (Algorithm 7 exactly as stated). Node `3` returns
`1` at the end of its local round `2` (it has `vote(1)` from `0, 1, 2`) without ever having
voted; nodes `1, 2` have only two votes, have already voted, and wait for the timeout, returning
their inputs `1` and `0` at the end of round `4`. So both electors' agreement and termination
within one round fail, although all hypotheses hold (`cx_hyps`). -/
theorem cx_fails : (outp (cxRun false) 2 = false ∧ outp (cxRun false) 3 = true) ∧
    ((cxRun false).st 3 3).out = some true ∧ ((cxRun false).st 4 2).out = none := by
  decide

/-- Electors' agreement (Definition 2.5) fails for Algorithm 7 as stated. -/
theorem cx_not_electorsBC : ¬ ElectorsBCSpec {0} univ (fun i => (cxInp i).1)
    (fun i => (cxInp i).2.1) (outp (cxRun false)) := by
  intro h
  have := h.2 cx_hyps.2.2.1 cx_hyps.2.2.2.2 2 (by decide) 3 (by decide)
  rw [cx_fails.1.1, cx_fails.1.2] at this
  cases this

/-- "Correct nodes terminate within one round of each other" fails for Algorithm 7 as stated:
node `3` returns in (global = local) round `2`, node `2` has not returned by the end of round
`3`. Compare `within_one`. -/
theorem cx_not_within_one : ¬ ∀ p q : Fin 4, p ∉ ({0} : Finset (Fin 4)) → q ∉ ({0} : Finset (Fin 4)) →
    ∀ ℓ, ((cxRun false).st (ℓ + 1) p).out.isSome = true →
      ((cxRun false).st ((cxRun false).σ p + ℓ + 2 - (cxRun false).σ q) q).out.isSome = true := by
  intro h
  exact absurd (h 3 2 (by decide) (by decide) 2 (by rw [cx_fails.2.1]; rfl)) (by decide)

/-- On the same instance, the repaired algorithm lets node `3` vote `1` after returning; all
correct nodes return `1` at the end of round `3`. -/
theorem cx_repaired : ∀ i : Fin 4, i ≠ 0 → ((cxRun true).st 4 i).out = some true := by
  decide

end Counterexample

/-! ### A node may broadcast three times -/

section ThreeBcasts

/-- Inputs: `n = 4`, `t = 1`, node `0` faulty, `K = {0, 1}` (not good), `T = 2`; the consensus
thread of the correct elector `1` outputs `1` after `2` rounds. -/
def bcInp : Fin 4 → In
  | 1 => (false, false, some (2, true))
  | _ => (false, false, none)

/-- The faulty elector `0` sends `elect(0)` to node `1` in round `0`, nothing else. -/
def bcAdv (ℓ : ℕ) (p q : Fin 4) : Option Msg :=
  if q = 0 ∧ ℓ = 0 ∧ p = 1 then some ⟨some false, fun _ => false⟩ else none

/-- The execution (for both versions of the algorithm). -/
abbrev bcRun (fix : Bool) :=
  syncRun (alg7 1 ({0, 1} : Finset (Fin 4)) 2 (fun _ => true) fix) {0} bcInp bcAdv

/-- The correct node `1` broadcasts `vote(0)` in round `1`, `elect(1)` in round `2` and
`vote(1)` in round `3`: three broadcasts in three different rounds (the paper's proof of
Lemma 4.2 says "at most twice"; `msg_count` gives three). -/
theorem three_bcasts (fix : Bool) :
    (∀ ℓ ∈ [1, 2, 3], nBcast ((alg7 1 ({0, 1} : Finset (Fin 4)) 2 (fun _ => true) fix).send
      ℓ 1 ((bcRun fix).st ℓ 1) 2) = 1) ∧
    ∑ ℓ ∈ range 6, nBcast ((alg7 1 ({0, 1} : Finset (Fin 4)) 2 (fun _ => true) fix).send
      ℓ 1 ((bcRun fix).st ℓ 1) 2) = 3 := by
  cases fix <;> decide

end ThreeBcasts

/-! ### Correct nodes that do not run Algorithm 7 (the use in Algorithm 8) -/

section NonParticipants

/-- `n = 7`, `t = 2`; nodes `0, 1` are faulty, the correct nodes `5, 6` do not participate (they
have terminated in Algorithm 8 and send nothing), `2, 3, 4` run Algorithm 7 with `K = {0, 2, 3}`
and `T = 5`. All inputs are `(1, weak)`; the consensus threads do not terminate (`K` is not good).
-/
def npInp : Fin 7 → In := fun _ => (true, false, none)

/-- Node `0` sends `elect(1)` to everybody in round `0`; nodes `0, 1` send `vote(1)` to node `2`
in round `1`; the non-participants `5, 6` are silent. -/
def npAdv (ℓ : ℕ) (p q : Fin 7) : Option Msg :=
  if q = 0 ∧ ℓ = 0 then some ⟨some true, fun _ => false⟩
  else if q.val ≤ 1 ∧ ℓ = 1 ∧ p = 2 then some ⟨none, fun b => b⟩
  else none

/-- The execution of the repaired algorithm; the silent non-participants are modelled as members
of the `DRun`'s faulty set. -/
abbrev npRun := syncRun (alg7 2 ({0, 2, 3} : Finset (Fin 7)) 5 (fun _ => true) true)
  {0, 1, 5, 6} npInp npAdv

/-- **The voting barrier needs all correct nodes.** With two correct non-participants, node `2`
returns at the end of round `1` (votes from `0, 1, 2, 3, 4`), while nodes `3, 4` (three votes,
already voted) only return at the timeout, at the end of round `7`. -/
theorem np_fails : (∀ ℓ p, npRun.rcv ℓ p 5 = none ∧ npRun.rcv ℓ p 6 = none) ∧
    (npRun.st 2 2).out = some true ∧ (npRun.st 7 3).out = none ∧ (npRun.st 7 4).out = none ∧
    (npRun.st 8 3).out = some true := by
  refine ⟨fun ℓ p => by simp [syncRun, npAdv], by decide⟩

/-- Alternative reading of convention (3): the terminated correct nodes `4, 5, 6` are deemed to
send `vote(1)` in every round; nodes `0, 1` are faulty, `2, 3` run Algorithm 7. -/
def phAdv (ℓ : ℕ) (p q : Fin 7) : Option Msg :=
  if 4 ≤ q.val then some ⟨none, fun b => b⟩
  else if q.val ≤ 1 ∧ ℓ = 0 ∧ p = 2 then some ⟨none, fun b => b⟩
  else none

/-- The execution with phantom voters `4, 5, 6`. -/
abbrev phRun (fix : Bool) := syncRun (alg7 2 ({0, 2, 3} : Finset (Fin 7)) 5 (fun _ => true) fix)
  {0, 1, 4, 5, 6} npInp phAdv

/-- With phantom voters, Algorithm 7 as stated: node `2` returns in its first round (votes from
`0, 1, 4, 5, 6`), node `3` reaches only four votes and returns at the timeout (round `7`). The
repaired algorithm returns at node `3` one round after node `2`. -/
theorem ph_fails : ((phRun false).st 1 2).out = some true ∧ ((phRun false).st 7 3).out = none ∧
    ((phRun true).st 1 2).out = some true ∧ ((phRun true).st 2 3).out = some true := by
  decide

end NonParticipants

end RecursivePhaseKing.VotingBarrier

