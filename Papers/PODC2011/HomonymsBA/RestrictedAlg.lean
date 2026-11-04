import Papers.PODC2011.HomonymsBA.Basic

/-!
# Proposition 18: the algorithm (Appendix A.3, Figures 6 and 7)

Partially synchronous Byzantine agreement with numerate processes against restricted Byzantine
processes, `n > 3t`, `ℓ > t`.

**Authenticated broadcast with multiplicity (Figure 6).** Superround `k` consists of the rounds
`2k` and `2k+1`. `Broadcast(i, m, k)` = put `m` into the `init` field of the round-`2k` message
(the broadcaster's identifier `i` is the authenticated identifier of the pair). Every process keeps
`a[h, m, k]` and sends its whole table in the `echo` field of every message (a function: at most
one echo tuple per `(h, m, k)`, which is the paper's validity condition; entry `0` = no tuple).
In round `R`:
* if `R = 2k`, `a[h, m, k] := #received pairs tagged `h` whose `init` contains `m``;
* `a[h, m, k] := max(a[h, m, k], α₁)`, `α₁` = the largest `α ≤ n` such that at least `n - 2t`
  received messages carry an echo `≥ α` for `(h, m, k)`;
* in odd rounds, `Accept(h, α₂, m, k)` with `α₂` the largest `α ≤ n` such that at least `n - t`
  received messages carry an echo `≥ α`; the *witnesses* for `(m, k)` are `∑ h, α₂`
  (`witnesses`), stored in the state field `wit`.

**Consensus (Figure 7).** Phase `ph` = superrounds `4ph … 4ph+3` = rounds `8ph … 8ph+7`; the
leaders of phase `ph` are the processes with identifier `ph mod ℓ`.
* round `8ph`: broadcast `propose v` for every `v ∈ proper` not conflicting with a lock;
* round `8ph+2`: a leader with `n - t` witnesses (from round `8ph+1`) for some `propose v`
  sends `lock v`;
* round `8ph+4`: broadcast `vote v` for a value `v` received in a `lock` message from the leader
  identifier (round `8ph+2`) with `n - t` witnesses for `propose v` (from round `8ph+3`); the
  choice depends only on the set of such values;
* end of round `8ph+5`: if `n - t` witnesses for `vote v` (superround `4ph+2`), lock `(v, ph)`
  (removing other locks on `v`) and send `ack v` in round `8ph+6`;
* round `8ph+6`: decide `v` if `n - t` witnesses for `propose v` (from round `8ph+5`) and `n - t`
  received `ack v` messages;
* end of round `8ph+7`: remove a lock `(v₁, ph₁)` if there are `n - t` witnesses (current round)
  for some `vote v₂` of a phase `ph₂ > ph₁`, `v₂ ≠ v₁`.
* every round: `proper` grows by the values in `t+1` received proper sets, and becomes the set of
  all values if some `2t+1` received messages contain no value `t+1` times.
-/

namespace Podc.HomonymsBA.Restricted

open Finset

/-- Messages of the consensus algorithm that are sent with the authenticated broadcast. -/
inductive CM (V : Type)
  | propose (v : V)
  | vote (v : V)

/-- The message a process sends in a round (bundling all parts of Figures 6 and 7). -/
structure Msg (ℓ : ℕ) (V : Type) where
  /-- Messages broadcast in this round (`Broadcast(i, m, R/2)` for `m ∈ init`; only in even
  rounds). -/
  init : Set (CM V)
  /-- Echo table: `echo h m k` is the sender's `a[h, m, k]` (`0`: no echo tuple). -/
  echo : Fin ℓ → CM V → ℕ → ℕ
  /-- Lock request (sent by leaders in round `8ph+2`). -/
  lock : Option V
  /-- Acknowledgement (used in round `8ph+6`). -/
  ack : Option V
  /-- The sender's proper set. -/
  proper : Set V

/-- Local state. -/
structure St (ℓ : ℕ) (V : Type) where
  id : Fin ℓ
  rnd : ℕ
  a : Fin ℓ → CM V → ℕ → ℕ
  /-- Witness counts computed in the last odd round. -/
  wit : CM V → ℕ → ℕ
  proper : Set V
  locks : Set (V × ℕ)
  /-- Values received in `lock` messages from the leader identifier in round `8ph+2`. -/
  lockRcv : Set V
  /-- Value acknowledged in the current phase (set at the end of round `8ph+5`). -/
  ackVal : Option V
  decided : Option V

/-- A deterministic choice from a set (depends only on the set). -/
noncomputable def pick {V : Type} (X : Set V) : Option V :=
  open Classical in if h : X.Nonempty then some h.some else none

lemma pick_mem {V : Type} {X : Set V} {v : V} (h : pick X = some v) : v ∈ X := by
  unfold pick at h
  split_ifs at h with h'
  · cases h; exact h'.some_mem

lemma pick_isSome {V : Type} {X : Set V} (h : X.Nonempty) : ∃ v, pick X = some v := by
  unfold pick; rw [dite_eq_left h]; exact ⟨_, rfl⟩

lemma pick_eq_none {V : Type} {X : Set V} (h : pick X = none) : X = ∅ := by
  unfold pick at h
  split_ifs at h with h'
  exact Set.not_nonempty_iff_eq_empty.mp h'

section Defs

variable (n t : ℕ) {ℓ : ℕ} (hℓ : 0 < ℓ) {V : Type}

open Classical

/-- Largest `α ≤ n` such that at least `c` received messages carry a value `≥ α` (read by `g`). -/
noncomputable def thr (c : ℕ) (I : Multiset (Fin ℓ × Msg ℓ V)) (g : Msg ℓ V → ℕ) : ℕ :=
  Nat.findGreatest (fun α => c ≤ I.countP (fun x => α ≤ g x.2)) n

/-- Witnesses for `(m, k)` computed from the messages `I` received in an (odd) round: the sum of
the multiplicities `α₂` of the `Accept(h, α₂, m, k)` actions. -/
noncomputable def witnesses (I : Multiset (Fin ℓ × Msg ℓ V)) (m : CM V) (k : ℕ) : ℕ :=
  ∑ h : Fin ℓ, thr n (n - t) I (fun x => x.echo h m k)

/-- Number of received pairs tagged `h` whose `init` contains `m`. -/
noncomputable def initCount (I : Multiset (Fin ℓ × Msg ℓ V)) (h : Fin ℓ) (m : CM V) : ℕ :=
  I.countP (fun x => x.1 = h ∧ m ∈ x.2.init)

/-- The echo table after a round (lines 11–18 of Figure 6). -/
noncomputable def newA (s : St ℓ V) (I : Multiset (Fin ℓ × Msg ℓ V)) (h : Fin ℓ) (m : CM V)
    (k : ℕ) : ℕ :=
  max (s.a h m k) (max (if s.rnd = 2 * k then initCount I h m else 0)
    (thr n (n - 2 * t) I (fun x => x.echo h m k)))

/-- The leader identifier of phase `ph`. -/
def leader (ph : ℕ) : Fin ℓ := ⟨ph % ℓ, Nat.mod_lt _ hℓ⟩

/-- Values that may be proposed (line 6 of Figure 7). -/
def propVals (s : St ℓ V) : Set V := {v | v ∈ s.proper ∧ ∀ x ∈ s.locks, x.1 = v}

/-- Candidates for the lock request of a leader. -/
def lockCand (s : St ℓ V) : Set V := {v | n - t ≤ s.wit (.propose v) (4 * (s.rnd / 8))}

/-- Candidates for the vote. -/
def voteCand (s : St ℓ V) : Set V :=
  {v | v ∈ s.lockRcv ∧ n - t ≤ s.wit (.propose v) (4 * (s.rnd / 8))}

/-- Messages broadcast in the current round. -/
noncomputable def initOut (s : St ℓ V) : Set (CM V) :=
  if s.rnd % 8 = 0 then CM.propose '' propVals s
  else if s.rnd % 8 = 4 then {m | ∃ v, pick (voteCand n t s) = some v ∧ m = .vote v}
  else ∅

/-- The lock request sent in the current round. -/
noncomputable def lockOut (s : St ℓ V) : Option V :=
  if s.rnd % 8 = 2 ∧ s.id = leader hℓ (s.rnd / 8) then pick (lockCand n t s) else none

/-- The message sent by a process in state `s` (the same to every identifier). -/
noncomputable def out (s : St ℓ V) : Msg ℓ V :=
  ⟨initOut n t s, s.a, lockOut n t hℓ s, s.ackVal, s.proper⟩

/-- Values to acknowledge at the end of round `8ph+5`. -/
noncomputable def ackCand (s : St ℓ V) (I : Multiset (Fin ℓ × Msg ℓ V)) : Set V :=
  {v | n - t ≤ witnesses n t I (.vote v) (4 * (s.rnd / 8) + 2)}

/-- Values that may be decided in round `8ph+6`. -/
noncomputable def decCand (s : St ℓ V) (I : Multiset (Fin ℓ × Msg ℓ V)) : Set V :=
  {v | n - t ≤ s.wit (.propose v) (4 * (s.rnd / 8)) ∧ n - t ≤ I.countP (fun x => x.2.ack = some v)}

/-- The proper set after a round. -/
noncomputable def newProper (s : St ℓ V) (I : Multiset (Fin ℓ × Msg ℓ V)) : Set V :=
  s.proper ∪ {v | t + 1 ≤ I.countP (fun x => v ∈ x.2.proper)} ∪
    {_v | ∃ J ≤ I, J.card = 2 * t + 1 ∧ ∀ w, J.countP (fun x => w ∈ x.2.proper) ≤ t}

/-- The locks after a round. -/
noncomputable def newLocks (s : St ℓ V) (I : Multiset (Fin ℓ × Msg ℓ V)) : Set (V × ℕ) :=
  if s.rnd % 8 = 5 then
    match pick (ackCand n t s I) with
    | some v => insert (v, s.rnd / 8) {x | x ∈ s.locks ∧ x.1 ≠ v}
    | none => s.locks
  else if s.rnd % 8 = 7 then
    {x | x ∈ s.locks ∧ ¬ ∃ v₂ ph₂, v₂ ≠ x.1 ∧ x.2 < ph₂ ∧
      n - t ≤ witnesses n t I (.vote v₂) (4 * ph₂ + 2)}
  else s.locks

/-- The transition. -/
noncomputable def step (s : St ℓ V) (I : Multiset (Fin ℓ × Msg ℓ V)) : St ℓ V where
  id := s.id
  rnd := s.rnd + 1
  a := newA n t s I
  wit := if s.rnd % 2 = 1 then witnesses n t I else s.wit
  proper := newProper t s I
  locks := newLocks n t s I
  lockRcv := if s.rnd % 8 = 2 then
      {v | ∃ x ∈ I, x.1 = leader hℓ (s.rnd / 8) ∧ x.2.lock = some v} else s.lockRcv
  ackVal := if s.rnd % 8 = 5 then pick (ackCand n t s I) else s.ackVal
  decided := s.decided.or (if s.rnd % 8 = 6 then pick (decCand n t s I) else none)

/-- **The algorithm of Appendix A.3** (Figures 6 and 7). -/
noncomputable def alg (V : Type) : Algorithm ℓ V (Msg ℓ V) (St ℓ V) where
  init i v := ⟨i, 0, fun _ _ _ => 0, fun _ _ => 0, {v}, ∅, ∅, none, none⟩
  send s _ := some (out n t hℓ s)
  step := step n t hℓ
  decide s := s.decided

end Defs

end Podc.HomonymsBA.Restricted
