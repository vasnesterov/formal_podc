import Papers.PODC2022.RecursivePhaseKing.Desync

/-!
# Algorithm 6 and Theorem 4.1: handling off-by-one round counters

Section 4 of [LS22] gives a compiler (Algorithm 6) that turns a synchronous algorithm `A` into one
that still simulates `A` when the correct nodes start in two consecutive rounds, at the price of a
factor-2 slowdown and one extra bit per message.

## Model

`A` is a CSLib `RoundAlgorithm` (synchronous lock-step rounds, rounds numbered `0, 1, …`; the
paper's simulated round `r ≥ 1` is `A`-round `r - 1`). The compiled algorithm `alg6 A` is again a
`RoundAlgorithm`, run in the desynchronized model `DRun` of `Desync.lean`: node `p` performs its
local round `ℓ` (0-based) in global round `σ p + ℓ`, messages between correct nodes are delivered in
the global round in which they are sent (and lost if the receiver has not started yet), messages
from faulty nodes are arbitrary (Byzantine). `DRun.StartWithin1`: correct start rounds differ by at
most one.

## Paper ↔ Lean

* Local round `ℓ` (0-based) of `alg6 A` is the loop iteration with `r_v = ℓ + 1`. The state
  `St6` holds the simulated state `s` (`s_v`) and the slots `m b w` (`m true w = m_{w,1}`,
  `m false w = m_{w,0}`; the paper's bit `b ∈ {0,1}` is the Boolean `b = 1`).
* `alg6` follows the pseudocode literally, with the paper's arithmetic on `r_v = ℓ + 1`: if `r_v` is
  even, send `((r_v mod 4)/2, m)` with `m` the message of `A` for simulated round `r_v / 2`
  (`A`-round `r_v / 2 - 1`) computed from the state at the beginning of the round; store every
  received `(b, m)` from `w` in `m_{w,b}`; if `r_v` is odd and `≠ 1`, update `s_v` with the
  computation of simulated round `(r_v - 1)/2` (`A`-round `(r_v - 1)/2 - 1`) using the slots
  `m_{w,((r_v - 1) mod 4)/2}`, then clear these slots. `decide` is `A`'s decision on `s_v`.
* Termination (lines 5, 16–17): the paper's loop runs "while `A` has not terminated" and returns
  the output. Here the compiled node runs forever; its output is `A.decide` of the simulated state,
  and what a terminated node sends is whatever `A.send` prescribes for its (terminated) state. This
  is the paper's convention that a terminated node is simulated by its terminated state.
* Normalized forms: `alg6_send_odd`/`alg6_send_even` (the `A`-round-`k` message is sent in local
  round `2k + 1` (0-based) with tag `tag k = decide (k % 2 = 0)`, nothing in even local rounds),
  `alg6_trans_upd` (update for `A`-round `k` in local round `2k + 2`, using slot `tag k`) and
  `alg6_trans_noupd`.
* `Alg6.used_eq`: invariants (ii)/(iii) of the proof of Theorem 4.1; `theorem_4_1`: Theorem 4.1,
  including invariant (i) (`(E'.st (2r+1) v).s = E.s r v`: the state at the end of local round
  `2r+1`, 1-based, is `A`'s state after `r` rounds) and the correspondence of decisions and
  messages.

The execution `E` of `A` is built as in the paper: for correct receivers the received messages are
the slot contents used in the updates (so faulty senders' messages are whatever their tagged
messages left in the slots); faulty receivers (irrelevant for the claim) get the genuine messages of
the correct senders and nothing from faulty ones.
-/

set_option linter.unusedSectionVars false

namespace RecursivePhaseKing

open Cslib.Byzantine.PartialSync

variable {P M S VI VO : Type*}

/-- The tag bit of the messages of `A`-round `k` (0-based), i.e. of simulated round `k + 1`:
the paper's bit `(r_v mod 4)/2` for `r_v = 2k + 2`, which is `1` iff `k` is even. -/
def tag (k : ℕ) : Bool := decide (k % 2 = 0)

theorem tag_eq_tag_iff {j k : ℕ} : tag j = tag k ↔ j % 2 = k % 2 := by
  unfold tag
  rw [decide_eq_decide]
  constructor <;> intro h <;> omega

/-- Local state of Algorithm 6: the simulated state `s_v` and the message slots `m_{w,b}`
(`m true w` is `m_{w,1}`, `m false w` is `m_{w,0}`; `none` is `⊥`). -/
structure St6 (P M S : Type*) where
  /-- The simulated state `s_v` of `A`. -/
  s : S
  /-- The slots: `m b w` is `m_{w,b}`. -/
  m : Bool → P → Option M

/-- Lines 10–11 of Algorithm 6: if `(b, x)` is received from `w`, set `m_{w,b} := x`. -/
def store (m : Bool → P → Option M) (rcv : P → Option (Bool × M)) : Bool → P → Option M :=
  fun b w => match rcv w with
    | some (b', x) => if b' = b then some x else m b w
    | none => m b w

/-- **Algorithm 6** of [LS22] (the compiler), at node `v`, local round `ℓ` (0-based), i.e.
`r_v = ℓ + 1`. Lines 1–4 are `init`; lines 6–9 are `send`; lines 10–15 are `trans` (store the
receptions, then, if `r_v` is odd and `≠ 1`, update `s_v` and clear the used slots). -/
def alg6 (A : RoundAlgorithm P M S VI VO) : RoundAlgorithm P (Bool × M) (St6 P M S) VI VO where
  init v x := ⟨A.init v x, fun _ _ => none⟩
  send ℓ v st w :=
    let rv := ℓ + 1
    if rv % 2 = 0 then
      (A.send (rv / 2 - 1) v st.s w).map fun m => (decide (rv % 4 / 2 = 1), m)
    else none
  trans ℓ v st rcv :=
    let rv := ℓ + 1
    let m' := store st.m rcv
    if rv % 2 = 1 ∧ rv ≠ 1 then
      let c := decide ((rv - 1) % 4 / 2 = 1)
      ⟨A.trans ((rv - 1) / 2 - 1) v st.s (m' c), fun b w => if b = c then none else m' b w⟩
    else ⟨st.s, m'⟩
  decide v st := A.decide v st.s

variable (A : RoundAlgorithm P M S VI VO)

/-- In local round `2k + 1` (0-based; `r_v = 2k + 2`) a node sends its `A`-round-`k` message,
tagged with `tag k`. -/
theorem alg6_send_odd (k : ℕ) (v : P) (st : St6 P M S) (w : P) :
    (alg6 A).send (2 * k + 1) v st w = (A.send k v st.s w).map fun m => (tag k, m) := by
  have h1 : (2 * k + 1 + 1) % 2 = 0 := by omega
  have h2 : (2 * k + 1 + 1) / 2 - 1 = k := by omega
  have h3 : decide ((2 * k + 1 + 1) % 4 / 2 = 1) = tag k := by
    unfold tag; rw [decide_eq_decide]; constructor <;> intro h <;> omega
  simp only [alg6, h1, h2, h3, ↓reduceIte]

/-- In even local rounds (0-based; odd `r_v`) nothing is sent. -/
theorem alg6_send_even (k : ℕ) (v : P) (st : St6 P M S) (w : P) :
    (alg6 A).send (2 * k) v st w = none := by
  have h1 : ¬ (2 * k + 1) % 2 = 0 := by omega
  simp only [alg6, h1, ↓reduceIte]

/-- Local round `2k + 2` (0-based; `r_v = 2k + 3`): store, perform `A`-round `k` with slot
`tag k`, clear slot `tag k`. -/
theorem alg6_trans_upd (k : ℕ) (v : P) (st : St6 P M S) (rcv : P → Option (Bool × M)) :
    (alg6 A).trans (2 * k + 2) v st rcv =
      ⟨A.trans k v st.s (store st.m rcv (tag k)),
        fun b w => if b = tag k then none else store st.m rcv b w⟩ := by
  have h1 : ((2 * k + 2 + 1) % 2 = 1 ∧ 2 * k + 2 + 1 ≠ 1) = True := by simp; omega
  have h2 : (2 * k + 2 + 1 - 1) / 2 - 1 = k := by omega
  have h3 : decide ((2 * k + 2 + 1 - 1) % 4 / 2 = 1) = tag k := by
    unfold tag; rw [decide_eq_decide]; constructor <;> intro h <;> omega
  simp only [alg6, h1, h2, h3, ↓reduceIte]

/-- Local rounds `0` and odd `ℓ` (0-based): only store the receptions. -/
theorem alg6_trans_noupd (ℓ : ℕ) (hℓ : ℓ = 0 ∨ ℓ % 2 = 1) (v : P) (st : St6 P M S)
    (rcv : P → Option (Bool × M)) :
    (alg6 A).trans ℓ v st rcv = ⟨st.s, store st.m rcv⟩ := by
  have h1 : ¬ ((ℓ + 1) % 2 = 1 ∧ ℓ + 1 ≠ 1) := by omega
  simp only [alg6, h1, ↓reduceIte]

/-! ### Executions of the compiled algorithm -/

namespace Alg6

variable {A} {F : Finset P} {inp : P → VI} (E' : DRun (alg6 A) F inp)

/-- The slot content used by `v` for sender `w` in the state update for (0-based) round `k` of
`A`: slot `tag k` after storing the receptions of local round `2k + 2`. -/
def used (k : ℕ) (v w : P) : Option M :=
  store (E'.st (2 * k + 2) v).m (E'.rcv (2 * k + 2) v) (tag k) w

/-! Below `E'` is an execution of `alg6 A` in the desynchronized model. -/

theorem s_zero (v : P) : (E'.st 0 v).s = A.init v (inp v) := by rw [E'.st_zero]; rfl

theorem m_zero (v : P) (b : Bool) (w : P) : (E'.st 0 v).m b w = none := by rw [E'.st_zero]; rfl

/-- Invariant (i) for `r = 0`: at the end of local round 1 (1-based) the simulated state is the
initial state. -/
theorem s_one (v : P) : (E'.st 1 v).s = A.init v (inp v) := by
  rw [E'.st_succ, alg6_trans_noupd A 0 (Or.inl rfl)]; exact s_zero E' v

/-- The simulated state does not change in local round `2k + 1` (0-based). -/
theorem s_even (k : ℕ) (v : P) : (E'.st (2 * k + 2) v).s = (E'.st (2 * k + 1) v).s := by
  rw [E'.st_succ, alg6_trans_noupd A _ (Or.inr (by omega))]

/-- The state update for `A`-round `k`. -/
theorem s_upd (k : ℕ) (v : P) :
    (E'.st (2 * k + 3) v).s = A.trans k v (E'.st (2 * k + 1) v).s (used E' k v) := by
  rw [show 2 * k + 3 = 2 * k + 2 + 1 by omega, E'.st_succ, alg6_trans_upd, s_even]; rfl

/-- Evolution of the slots. -/
theorem m_succ (ℓ : ℕ) (v : P) (b : Bool) (w : P) : (E'.st (ℓ + 1) v).m b w =
    if ℓ % 2 = 0 ∧ ℓ ≠ 0 ∧ b = tag (ℓ / 2 - 1) then none
    else store (E'.st ℓ v).m (E'.rcv ℓ v) b w := by
  rw [E'.st_succ]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' ℓ
  · cases j with
    | zero => rw [alg6_trans_noupd A 0 (Or.inl rfl)]; simp
    | succ k =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, alg6_trans_upd]
      simp
  · rw [alg6_trans_noupd A _ (Or.inr (by omega))]
    simp

variable {v w : P}

/-- A correct `v` receives the tagged round-`k` message of a correct `w` in the global round in
which `w` performs its local round `2k + 1` (0-based). -/
theorem rcv_eq (hv : v ∉ F) (hw : w ∉ F) (ℓ k : ℕ) (h : E'.σ v + ℓ = E'.σ w + (2 * k + 1)) :
    E'.rcv ℓ v w = (A.send k w (E'.st (2 * k + 1) w).s v).map fun m => (tag k, m) := by
  rw [E'.honest ℓ v w hv hw]
  have hc : E'.σ w ≤ E'.σ v + ℓ := by omega
  have he : E'.σ v + ℓ - E'.σ w = 2 * k + 1 := by omega
  simp only [hc, ↓reduceIte, he]
  rw [alg6_send_odd]

/-- Every message received by a correct node from a correct node is a tagged message of `A`. -/
theorem rcv_some (hv : v ∉ F) (hw : w ∉ F) {ℓ : ℕ} {b : Bool} {x : M}
    (h : E'.rcv ℓ v w = some (b, x)) :
    ∃ k, E'.σ v + ℓ = E'.σ w + (2 * k + 1) ∧ b = tag k ∧
      A.send k w (E'.st (2 * k + 1) w).s v = some x := by
  rw [E'.honest ℓ v w hv hw] at h
  split_ifs at h with hc
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' (E'.σ v + ℓ - E'.σ w)
  · rw [hj, alg6_send_even] at h; cases h
  · rw [hj, alg6_send_odd, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, he⟩ := h
    simp only [Prod.mk.injEq] at he
    exact ⟨j, by omega, he.1.symm, he.2 ▸ hm⟩

variable (hE : E'.StartWithin1)
include hE

/-- One step of the slot invariant: storing the receptions of local round `ℓ`. -/
theorem store_slot (hv : v ∉ F) (hw : w ∉ F) (k ℓ ℓ0 : ℕ) (hℓ0 : ℓ0 ≤ ℓ) (hℓ : ℓ ≤ 2 * k + 2)
    (h0 : 2 ≤ k → 2 * k - 2 < ℓ0)
    (hU : (E'.st ℓ v).m (tag k) w =
      if E'.σ w + 2 * k + 1 < E'.σ v + ℓ then A.send k w (E'.st (2 * k + 1) w).s v else none) :
    store (E'.st ℓ v).m (E'.rcv ℓ v) (tag k) w =
      if E'.σ w + 2 * k + 1 ≤ E'.σ v + ℓ then A.send k w (E'.st (2 * k + 1) w).s v else none := by
  have h1 := hE v w hv hw
  have h2 := hE w v hw hv
  simp only [store, hU]
  by_cases heq : E'.σ v + ℓ = E'.σ w + (2 * k + 1)
  · rw [rcv_eq E' hv hw ℓ k heq]
    have hc : E'.σ w + 2 * k + 1 ≤ E'.σ v + ℓ := by omega
    cases hm : A.send k w (E'.st (2 * k + 1) w).s v with
    | none => simp
    | some x => simp [hc]
  · cases hr : E'.rcv ℓ v w with
    | none => simp only; split_ifs <;> first | rfl | omega
    | some bx =>
      obtain ⟨b, x⟩ := bx
      obtain ⟨j, hj, hb, -⟩ := rcv_some E' hv hw hr
      have : b ≠ tag k := by rw [hb, Ne, tag_eq_tag_iff]; omega
      simp only [this, ↓reduceIte]
      split_ifs <;> first | rfl | omega

/-- Slot invariant: between its last clearing (or the start) and the update for `A`-round `k`,
the slot `tag k` of `w` at `v` contains `w`'s round-`k` message iff it has already been received,
and `⊥` otherwise. -/
theorem slot_U (hv : v ∉ F) (hw : w ∉ F) (k ℓ0 : ℕ) (h00 : ℓ0 ≤ 2 * k)
    (h0 : 2 ≤ k → 2 * k - 2 < ℓ0) (hz : (E'.st ℓ0 v).m (tag k) w = none) :
    ∀ ℓ, ℓ0 ≤ ℓ → ℓ ≤ 2 * k + 2 → (E'.st ℓ v).m (tag k) w =
      if E'.σ w + 2 * k + 1 < E'.σ v + ℓ then A.send k w (E'.st (2 * k + 1) w).s v else none := by
  have h1 := hE v w hv hw
  intro ℓ hℓ0
  induction ℓ, hℓ0 using Nat.le_induction with
  | base =>
    intro _
    have : ¬ E'.σ w + 2 * k + 1 < E'.σ v + ℓ0 := by omega
    simp only [hz, this, ↓reduceIte]
  | succ ℓ hℓ ih =>
    intro hℓ'
    have : ¬ (ℓ % 2 = 0 ∧ ℓ ≠ 0 ∧ tag k = tag (ℓ / 2 - 1)) := by rw [tag_eq_tag_iff]; omega
    rw [m_succ]
    simp only [this, ↓reduceIte]
    rw [store_slot E' hE hv hw k ℓ ℓ0 hℓ (by omega) h0 (ih (by omega))]
    split_ifs <;> first | rfl | omega

/-- Invariants (ii) and (iii) in the proof of Theorem 4.1 of [LS22]: when a correct node `v`
performs the state update for round `k` of `A` (local round `2k + 3`, 1-based), the slot it uses
holds, for every correct `w`, exactly the round-`k` message of `w` (or nothing if there is none). -/
theorem used_eq (hv : v ∉ F) (hw : w ∉ F) (k : ℕ) :
    used E' k v w = A.send k w (E'.st (2 * k + 1) w).s v := by
  have h1 := hE v w hv hw
  have h2 := hE w v hw hv
  obtain ⟨ℓ0, h00, h0, hz⟩ : ∃ ℓ0, ℓ0 ≤ 2 * k ∧ (2 ≤ k → 2 * k - 2 < ℓ0) ∧
      (E'.st ℓ0 v).m (tag k) w = none := by
    by_cases hk : 2 ≤ k
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      refine ⟨2 * j + 3, by omega, fun _ => by omega, ?_⟩
      have : (2 * j + 2) % 2 = 0 ∧ 2 * j + 2 ≠ 0 ∧ tag (j + 2) = tag ((2 * j + 2) / 2 - 1) := by
        rw [tag_eq_tag_iff]; omega
      rw [show 2 * j + 3 = 2 * j + 2 + 1 by omega, m_succ]
      exact ite_eq_left_iff.2 fun h => absurd this h
    · exact ⟨0, by omega, fun h => absurd h hk, m_zero E' v _ w⟩
  unfold used
  rw [store_slot E' hE hv hw k (2 * k + 2) ℓ0 (by omega) le_rfl h0
    (slot_U E' hE hv hw k ℓ0 h00 h0 hz _ (by omega) le_rfl)]
  have : E'.σ w + 2 * k + 1 ≤ E'.σ v + (2 * k + 2) := by omega
  simp only [this, ↓reduceIte]

/-! ### The simulated execution of `A` -/

omit hE

open Classical in
/-- Receptions of the constructed execution of `A`: for a correct receiver, the slot contents it
uses in its state updates; for a faulty receiver, the genuine messages of the correct senders. -/
noncomputable def simRcv (k : ℕ) (v w : P) : Option M :=
  if v ∈ F then (if w ∈ F then none else A.send k w (E'.st (2 * k + 1) w).s v)
  else used E' k v w

/-- States of a faulty node in the constructed execution of `A` (driven by `simRcv`). -/
noncomputable def simSF (v : P) : ℕ → S
  | 0 => A.init v (inp v)
  | k + 1 => A.trans k v (simSF v k) (simRcv E' k v)

open Classical in
/-- States of the constructed execution of `A`: for a correct node `v`, the simulated state at
the end of its local round `2k + 1` (1-based). -/
noncomputable def simS (k : ℕ) (v : P) : S :=
  if v ∈ F then simSF E' v k else (E'.st (2 * k + 1) v).s

/-- For correct nodes the constructed states are the simulated states. -/
theorem simS_correct (hv : v ∉ F) (k : ℕ) : simS E' k v = (E'.st (2 * k + 1) v).s := by
  simp [simS, hv]

include hE in
/-- Correct-to-correct messages are delivered in the constructed execution. -/
theorem simRcv_correct (hv : v ∉ F) (hw : w ∉ F) (k : ℕ) :
    simRcv E' k v w = A.send k w (simS E' k w) v := by
  simp only [simRcv, hv, ↓reduceIte, simS_correct E' hw]
  exact used_eq E' hE hv hw k

include hE in
/-- The execution of `A` simulated by an execution `E'` of `alg6 A`. -/
noncomputable def simRun : RoundRun A F inp where
  s := simS E'
  rcv := simRcv E'
  s_zero v := by
    by_cases hv : v ∈ F
    · simp [simS, hv, simSF]
    · rw [simS_correct E' hv]; exact s_one E' v
  s_succ k v := by
    by_cases hv : v ∈ F
    · simp [simS, hv, simSF]
    · rw [simS_correct E' hv, simS_correct E' hv, show 2 * (k + 1) + 1 = 2 * k + 3 by omega,
        s_upd]
      congr 1
      funext w
      simp [simRcv, hv]
  honest k p q m hq h := by
    rw [← h]
    by_cases hp : p ∈ F
    · simp [simRcv, hp, hq, simS_correct E' hq]
    · exact (simRcv_correct E' hE hp hq k).symm

/-- The simulated state of a correct node at the beginning of its local round `ℓ` (0-based) is the
state of `A` after `⌊(ℓ - 1) / 2⌋` rounds (`0` for `ℓ = 0`). -/
theorem st_s_eq_simS (hv : v ∉ F) (ℓ : ℕ) : (E'.st ℓ v).s = simS E' ((ℓ - 1) / 2) v := by
  rw [simS_correct E' hv]
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' ℓ
  · cases j with
    | zero => rw [s_zero, s_one]
    | succ k =>
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, s_even,
        show (2 * k + 2 - 1) / 2 = k by omega]
  · rw [show (2 * j + 1 - 1) / 2 = j by omega]

end Alg6

/-- **Theorem 4.1** of [LS22]. If the correct nodes start the compiled algorithm `alg6 A` within
one round of each other, then it simulates `A`: there is an execution `E` of `A` with the same
faulty set and the same inputs, synchronous (no loss between correct nodes), such that for every
correct node `v`
* (i) the simulated state at the end of local round `2r + 1` (1-based) is the state of `A` after
  `r` rounds — and more generally at the beginning of local round `ℓ` (0-based) it is the state
  after `⌊(ℓ - 1) / 2⌋` rounds;
* consequently the decision (output/termination) of `v` at local round `ℓ` is the decision of `v`
  in `A` after `⌊(ℓ - 1) / 2⌋` rounds ("it terminates after `2r + 1` rounds iff it terminates
  after `r` rounds in `A`");
* `v` sends the same messages as in `E`, with an additional bit as prefix: the round-`r` message
  of `A` in local round `2r + 2` (1-based), and nothing in the other local rounds. -/
theorem theorem_4_1 {F : Finset P} {inp : P → VI} (E' : DRun (alg6 A) F inp)
    (hE : E'.StartWithin1) :
    ∃ E : RoundRun A F inp, E.SyncFrom 0 ∧
      (∀ v ∉ F, ∀ r, (E'.st (2 * r + 1) v).s = E.s r v) ∧
      (∀ v ∉ F, ∀ ℓ, (E'.st ℓ v).s = E.s ((ℓ - 1) / 2) v) ∧
      (∀ v ∉ F, ∀ ℓ, (alg6 A).decide v (E'.st ℓ v) = A.decide v (E.s ((ℓ - 1) / 2) v)) ∧
      (∀ v ∉ F, ∀ r w, (alg6 A).send (2 * r + 1) v (E'.st (2 * r + 1) v) w =
          (A.send r v (E.s r v) w).map fun m => (tag r, m)) ∧
      (∀ v r w, (alg6 A).send (2 * r) v (E'.st (2 * r) v) w = none) := by
  refine ⟨Alg6.simRun E' hE, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _ p q hp hq
    exact Alg6.simRcv_correct E' hE hp hq r
  · intro v hv r
    exact (Alg6.simS_correct E' hv r).symm
  · intro v hv ℓ
    exact Alg6.st_s_eq_simS E' hv ℓ
  · intro v hv ℓ
    exact congrArg (A.decide v) (Alg6.st_s_eq_simS E' hv ℓ)
  · intro v hv r w
    rw [alg6_send_odd]
    exact congrArg (fun s => (A.send r v s w).map fun m => (tag r, m))
      (Alg6.simS_correct E' hv r).symm
  · intro v r w
    exact alg6_send_even A r v _ w

end RecursivePhaseKing
