/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Protocol

/-!
# The inductive invariant of the corrected protocol

Derived notions (accepted entries, dead epochs, decisions) and the invariant `Inv` of the
protocol of Figure 1 with the check `e ≥ new_epoch` at line 56. The invariant contains the
paper's Invariants 1–12 (Figures 3 and 5) in the following form:

* Invariant 1 (follower arrays are a prefix with holes of the leader's): `loc_elog`, `loc_acked`;
* Invariant 2 (accepted entries persist, with the same prefix): `inv2`, stated for every configured
  epoch `E` with respect to its *candidate* state (the base state if `E` started, otherwise the
  frozen state of its leader), and for all slots that may still be accepted (`AliveK`);
* Invariant 3: `m_probeAck` and `loc_newEpoch`;
* Invariant 5: `cfg_mem` (the probing record of every configuration), from which Invariant 5 is
  derived;
* Invariants 4, 6, 9, 10, 11: `elog_dist`, `m_accept`, `m_prepareAck`, and their consequences;
* Invariant 7: `elog_txn`; Invariant 12: `loc_dec`, `m_decision`;
* Proposition A.2: `vinfo_ok` (the vote context recorded when a vote is computed).
-/

namespace Podc.ReconfigurableCommit

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

section Defs

variable (Pa : Params T Pl S P) (st : State T Pl S P)

/-- The configuration of shard `s` at epoch `e`, if stored at the CS. -/
def cfg (s : S) (e : ℕ) : Option (Config P) := (st.cs s)[e]?

/-- The followers of a configuration. -/
def Config.followers (c : Config P) : Finset P := c.members \ {c.leader}

/-- `q` has sent `ACCEPT_ACK(s, e, k, t, d)`. -/
def Acked (q : P) (s : S) (e k : ℕ) (t : T) (d : Dec) : Prop :=
  ∃ r, Msg.acceptAck s e k t d ∈ st.sent q r

/-- `q` has sent `PROBE_ACK(b, E, s)`. -/
def Replied (q : P) (b : Bool) (E : ℕ) (s : S) : Prop :=
  ∃ r, Msg.probeAck b E s ∈ st.sent q r

/-- Epoch `e` of `s` is dead: one of its followers moved past it without acknowledging anything
at `e`, so nothing can ever be accepted at `e`. -/
def Dead (s : S) (e : ℕ) : Prop :=
  ∃ c, cfg st s e = some c ∧ ∃ q ∈ c.followers, e < (st.loc q).newEpoch ∧
    ∀ k t d, ¬ Acked st q s e k t d

/-- Slot `k` of epoch `e` may still become accepted: every follower has acknowledged it or can
still do so. -/
def AliveK (s : S) (e k : ℕ) : Prop :=
  ∀ c, cfg st s e = some c → ∀ q ∈ c.followers,
    (∃ t d, Acked st q s e k t d) ∨ (st.loc q).newEpoch ≤ e

/-- The entry `v` (with its origin epoch) of slot `k` is accepted at epoch `e` of shard `s`: it is
in the log of `e` and all followers of `e` acknowledged it. -/
def AccL (s : S) (e k : ℕ) (v : Entry T Pl × ℕ) : Prop :=
  st.elog s e k = some v ∧ ∃ c, cfg st s e = some c ∧
    ∀ q ∈ c.followers, Acked st q s e k v.1.1 v.1.2.2

/-- `d` is a possible decision on `t`: on every shard of `t` some entry of `t` is accepted, and `d`
is the meet of their votes (cf. line 26). -/
def Decided (t : T) (d : Dec) : Prop :=
  ∃ (es ks : S → ℕ) (vs : S → Entry T Pl × ℕ),
    (∀ s ∈ Pa.σ.shards t, AccL st s (es s) (ks s) (vs s) ∧ (vs s).1.1 = t) ∧
    d = meetOver (Pa.σ.shards t) (fun s => (vs s).1.2.2)

/-- `q` is fresh for epoch `E` of `s`: not a member of any earlier configuration. -/
def Fresh (q : P) (s : S) (E : ℕ) : Prop :=
  ∀ e < E, ∀ c, cfg st s e = some c → q ∉ c.members

/-- The candidate state of a configured epoch `E` with configuration `c`: the base state if `E`
started, otherwise the state of its leader (entries tagged with their origin). -/
def cand (s : S) (E : ℕ) (c : Config P) : ℕ → Option (Entry T Pl × ℕ) :=
  if st.started s E then st.base s E else fun k =>
    if ((st.loc c.leader).arr.ent k).isSome then st.elog s ((st.loc c.leader).epoch s) k
    else none

/-- The payload of slot `j` of the log of epoch `o` (`ε` if empty). -/
def plAt (s : S) (o j : ℕ) : Pl := ((st.elog s o j).map (·.1.2.1)).getD Pa.σ.eps

/-- Decision `d` on `t` is among the first `n` actions of the history. -/
def DecIn (t : T) (d : Dec) (n : ℕ) : Prop := Event.decide t d ∈ st.hist.take n

end Defs

/-- The invariant. Fields are grouped: configurations, ghost logs, local states, probing,
messages, history. -/
structure Inv (Pa : Params T Pl S P) (st : State T Pl S P) : Prop where
  -- configurations
  cs_zero : ∀ s, cfg st s 0 = some (Pa.init s)
  cfg_wf : ∀ s e c, cfg st s e = some c →
    c.leader ∈ c.members ∧ (∀ q ∈ c.members, Pa.home q = s) ∧ 2 ≤ c.members.card
  cfg_mem : ∀ s E c, 1 ≤ E → cfg st s E = some c → ∃ pe < E,
    (∀ e', pe < e' → e' < E → Dead st s e') ∧ Replied st c.leader true E s ∧
    (∃ y, pe ≤ y ∧ y < E ∧ ∃ cy, cfg st s y = some cy ∧ c.leader ∈ cy.members) ∧
    ∀ q ∈ c.members, Fresh st q s E ∨
      ((∃ b, Replied st q b E s) ∧ ∃ z, pe ≤ z ∧ z < E ∧ ∃ cz, cfg st s z = some cz ∧ q ∈ cz.members)
  frz : ∀ s e, e + 1 < (st.cs s).length → ∃ c, cfg st s e = some c ∧
    ∃ q ∈ c.members, e < (st.loc q).newEpoch
  leader_init : ∀ s e c, cfg st s e = some c → (st.loc c.leader).initialized = true
  init_init : ∀ s q, q ∈ (Pa.init s).members → (st.loc q).initialized = true
  started_cfg : ∀ s e, st.started s e = true → e < (st.cs s).length
  started_leader : ∀ s e c, st.started s e = true → cfg st s e = some c →
    e ≤ (st.loc c.leader).epoch s
  -- ghost logs
  elog_started : ∀ s e k v, st.elog s e k = some v → st.started s e = true
  base_elog : ∀ s e k v, st.base s e k = some v → st.elog s e k = some v
  elog_above : ∀ s e k v, st.elog s e k = some v → st.base s e k = none →
    ∀ j, k ≤ j → st.base s e j = none
  elog_origin : ∀ s e k x o, st.elog s e k = some (x, o) → o ≤ e ∧
    st.elog s o k = some (x, o) ∧ ∀ j < k, ∀ y, st.elog s e j = some y → st.elog s o j = some y
  elog_dist : ∀ s e i j v w, st.elog s e i = some v → st.elog s e j = some w →
    v.1.1 = w.1.1 → i = j
  elog_txn : ∀ s e k t l d o, st.elog s e k = some ((t, l, d), o) → s ∈ Pa.σ.shards t ∧
    ∃ l₀, Event.certify t l₀ ∈ st.hist ∧ (l = Pa.σ.proj l₀ s ∨ (l = Pa.σ.eps ∧ d = .abort))
  vinfo_none : ∀ s o k t l d, st.elog s o k = some ((t, l, d), o) → st.vinfo s o k = none →
    d = .abort
  vinfo_ok : ∀ s o k t l d J₁ J₂ hl, st.elog s o k = some ((t, l, d), o) →
    st.vinfo s o k = some (J₁, J₂, hl) →
    hl ≤ st.hist.length ∧
    (∀ j ∈ J₁ ∪ J₂, j < k ∧ (st.elog s o j).isSome) ∧
    d = (Pa.fs s (J₁.image (plAt Pa st s o)) l).meet (Pa.gs s (J₂.image (plAt Pa st s o)) l) ∧
    (∀ j ∈ J₁, ∀ v, st.elog s o j = some v → DecIn st v.1.1 .commit hl) ∧
    (∀ j ∈ J₂, ∀ v, st.elog s o j = some v → v.1.2.2 = .commit) ∧
    (∀ j < k, ∀ v, st.elog s o j = some v →
      j ∈ J₁ ∨ j ∈ J₂ ∨ v.1.2.2 = .abort ∨ DecIn st v.1.1 .abort hl)
  inv2 : ∀ s E c, cfg st s E = some c →
    (st.started s E = true ∨ (st.loc c.leader).newEpoch = E) →
    ∀ e' < E, ∀ k v, st.elog s e' k = some v → AliveK st s e' k →
      cand st s E c k = some v ∧ ∀ j < k, ∀ y, cand st s E c j = some y → st.elog s e' j = some y
  -- local states
  loc_len : ∀ p k, (st.loc p).arr.phase k ≠ .start → k ≤ (st.loc p).arr.len
  loc_ent : ∀ p k, ((st.loc p).arr.ent k).isSome = true ↔ (st.loc p).arr.phase k ≠ .start
  loc_newEpoch : ∀ p, (st.loc p).status ≠ .reconfiguring →
    (st.loc p).newEpoch ≤ (st.loc p).epoch (Pa.home p)
  loc_view : ∀ p s, cfg st s ((st.loc p).epoch s) =
    some ⟨(st.loc p).members s, (st.loc p).leader s⟩
  loc_started : ∀ p, st.started (Pa.home p) ((st.loc p).epoch (Pa.home p)) = true
  loc_member : ∀ p, (st.loc p).initialized = true → p ∈ (st.loc p).members (Pa.home p)
  loc_member0 : ∀ p, (st.loc p).epoch (Pa.home p) = 0 ∨ p ∈ (st.loc p).members (Pa.home p)
  loc_leaderArr : ∀ p, (st.loc p).leader (Pa.home p) = p → ∀ k,
    (st.loc p).arr.ent k = (st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k).map Prod.fst
  loc_leader : ∀ p, (st.loc p).status = .leader → (st.loc p).leader (Pa.home p) = p ∧
    (st.loc p).initialized = true ∧ (∀ k, (st.loc p).next < k → (st.loc p).arr.phase k = .start) ∧
    ∀ j v, st.base (Pa.home p) ((st.loc p).epoch (Pa.home p)) j = some v → j ≤ (st.loc p).next
  loc_follower : ∀ p, (st.loc p).status = .follower → (st.loc p).leader (Pa.home p) ≠ p ∧
    (st.loc p).initialized = true ∧ p ∈ (st.loc p).members (Pa.home p)
  loc_elog : ∀ p k x, (st.loc p).arr.ent k = some x →
    ∃ o, st.elog (Pa.home p) ((st.loc p).epoch (Pa.home p)) k = some (x, o)
  loc_base : ∀ p, (st.loc p).initialized = true → ∀ k v,
    st.base (Pa.home p) ((st.loc p).epoch (Pa.home p)) k = some v → (st.loc p).arr.ent k = some v.1
  loc_acked : ∀ p k t d, Acked st p (Pa.home p) ((st.loc p).epoch (Pa.home p)) k t d →
    ∃ l, (st.loc p).arr.ent k = some (t, l, d)
  loc_acked_epoch : ∀ p s e k t d, Acked st p s e k t d →
    s = Pa.home p ∧ e ≤ (st.loc p).epoch (Pa.home p) ∧ (st.loc p).initialized = true
  loc_dec : ∀ p k, (st.loc p).arr.phase k = .decided → ∃ dd, (st.loc p).arr.dec k = some dd ∧
    ∃ e v, e ≤ (st.loc p).epoch (Pa.home p) ∧ AccL st (Pa.home p) e k v ∧
      Event.decide v.1.1 dd ∈ st.hist
  loc_acceptAcks : ∀ p q s e k t d, (q, s, e, k, t, d) ∈ (st.loc p).acceptAcks →
    Msg.acceptAck s e k t d ∈ st.sent q p
  loc_probeAcks : ∀ p q b E s, (q, b, E, s) ∈ (st.loc p).probeAcks →
    Msg.probeAck b E s ∈ st.sent q p
  -- probing
  prb : ∀ p, (st.loc p).probing = true →
    1 ≤ (st.loc p).reconEpoch ∧ (st.loc p).probedEpoch < (st.loc p).reconEpoch ∧
    (st.loc p).reconEpoch ≤ (st.cs (st.loc p).reconShard).length ∧
    (∃ c, cfg st (st.loc p).reconShard (st.loc p).probedEpoch = some c ∧
      c.members = (st.loc p).probedMembers) ∧
    (∀ e', (st.loc p).probedEpoch < e' → e' < (st.loc p).reconEpoch →
      Dead st (st.loc p).reconShard e') ∧
    ∀ q, Msg.probe (st.loc p).reconEpoch ∈ st.sent p q → Pa.home q = (st.loc p).reconShard →
      ∃ z, (st.loc p).probedEpoch ≤ z ∧ z < (st.loc p).reconEpoch ∧ ∃ c,
        cfg st (st.loc p).reconShard z = some c ∧ q ∈ c.members
  probe_old : ∀ r q E, Msg.probe E ∈ st.sent r q →
    E < (st.cs (Pa.home q)).length ∨ ((st.loc r).probing = true ∧ (st.loc r).reconEpoch = E ∧
      (st.loc r).reconShard = Pa.home q)
  probe_sent : ∀ r q E, Msg.probe E ∈ st.sent r q → 1 ≤ E ∧
    ∃ z < E, ∃ c, cfg st (Pa.home q) z = some c ∧ q ∈ c.members
  -- messages
  m_probeAck : ∀ q r b E s, Msg.probeAck b E s ∈ st.sent q r → s = Pa.home q ∧
    E ≤ (st.loc q).newEpoch ∧ Msg.probe E ∈ st.sent r q ∧
    (b = true → (st.loc q).initialized = true) ∧
    (b = false → (∀ e < E, ∀ k t d, ¬ Acked st q s e k t d) ∧
      ∀ e < E, ∀ c, cfg st s e = some c → c.leader ≠ q)
  m_frozen : ∀ q b E s, Replied st q b E s → (st.loc q).newEpoch = E → st.started s E = false →
    (st.loc q).status = .reconfiguring
  m_prepare : ∀ c b t lo, Msg.prepare t lo ∈ st.sent c b → Pa.home b ∈ Pa.σ.shards t ∧
    ∃ l₀, Event.certify t l₀ ∈ st.hist ∧ (lo = none ∨ lo = some (Pa.σ.proj l₀ (Pa.home b)))
  m_prepareAck : ∀ c r e s k t l d, Msg.prepareAck e s k t l d ∈ st.sent c r →
    ∃ o, st.elog s e k = some ((t, l, d), o)
  m_accept : ∀ c q e k t l d, Msg.accept e k t l d ∈ st.sent c q →
    ∃ o, st.elog (Pa.home q) e k = some ((t, l, d), o)
  m_acceptAck : ∀ q r s e k t d, Msg.acceptAck s e k t d ∈ st.sent q r → s = Pa.home q ∧
    (∃ l o, st.elog s e k = some ((t, l, d), o)) ∧ ∃ c, cfg st s e = some c ∧ q ∈ c.followers
  m_decision : ∀ c q e k d, Msg.decision e k d ∈ st.sent c q →
    ∃ v, AccL st (Pa.home q) e k v ∧ Event.decide v.1.1 d ∈ st.hist
  m_newConfig : ∀ r q e M, Msg.newConfig e M ∈ st.sent r q → 1 ≤ e ∧
    cfg st (Pa.home q) e = some ⟨M, q⟩ ∧ Replied st q true e (Pa.home q)
  m_newState : ∀ p q e M a, Msg.newState e M a ∈ st.sent p q →
    cfg st (Pa.home q) e = some ⟨M, p⟩ ∧ q ∈ M ∧ q ≠ p ∧ st.started (Pa.home q) e = true ∧
    (∀ k, a.ent k = (st.base (Pa.home q) e k).map Prod.fst) ∧
    (∀ k, a.phase k ≠ .start → k ≤ a.len) ∧
    (∀ k, (a.ent k).isSome = true ↔ a.phase k ≠ .start) ∧
    (∀ k, a.phase k = .decided → ∃ dd, a.dec k = some dd ∧
      ∃ e' v, e' ≤ e ∧ AccL st (Pa.home q) e' k v ∧ Event.decide v.1.1 dd ∈ st.hist)
  -- channels
  net_sub : ∀ a b, (st.net a b).Sublist (st.sent a b)
  nc_unique : ∀ r q e M r' q' M', Msg.newConfig e M ∈ st.sent r q →
    Msg.newConfig e M' ∈ st.sent r' q' → Pa.home q = Pa.home q' → r = r' ∧ q = q' ∧ M = M'
  nc_count : ∀ r q e M M' (i j : ℕ), (st.sent r q)[i]? = some (Msg.newConfig e M) →
    (st.sent r q)[j]? = some (Msg.newConfig e M') → i = j
  nc_flight : ∀ r q e M, Msg.newConfig e M ∈ st.net r q → st.started (Pa.home q) e = false ∧
    ((st.loc q).epoch (Pa.home q) < e ∨ e < (st.loc q).newEpoch)
  ns_unique : ∀ p q e M a p' M' a', Msg.newState e M a ∈ st.sent p q →
    Msg.newState e M' a' ∈ st.sent p' q → p = p' ∧ M = M' ∧ a = a'
  ns_count : ∀ p q e M a M' a' (i j : ℕ), (st.sent p q)[i]? = some (Msg.newState e M a) →
    (st.sent p q)[j]? = some (Msg.newState e M' a') → i = j
  ns_flight : ∀ p q e M a, Msg.newState e M a ∈ st.net p q →
    (st.loc q).epoch (Pa.home q) < e ∨ e < (st.loc q).newEpoch
  -- history
  hist_certify : ∀ t l, Event.certify t l ∈ st.hist → Pa.σ.ValidPayload t l
  hist_certify_unique : ∀ t l l', Event.certify t l ∈ st.hist → Event.certify t l' ∈ st.hist →
    l = l'
  hist_decide : ∀ t d, Event.decide t d ∈ st.hist → Decided Pa st t d
  hist_decide_unique : ∀ t d d', Event.decide t d ∈ st.hist → Event.decide t d' ∈ st.hist →
    d = d'
  hist_decide_idx : ∀ (i j : ℕ) t d d', st.hist[i]? = some (Event.decide t d) →
    st.hist[j]? = some (Event.decide t d') → i = j
  hist_certify_idx : ∀ (i j : ℕ) t l l', st.hist[i]? = some (Event.certify t l) →
    st.hist[j]? = some (Event.certify t l') → i = j
  hist_decide_after : ∀ (i : ℕ) t d, st.hist[i]? = some (Event.decide t d) →
    ∃ j < i, ∃ l, st.hist[j]? = some (Event.certify t l)
  hist_order : ∀ (i : ℕ) t d, st.hist[i]? = some (Event.decide t d) →
    ∀ s ∈ Pa.σ.shards t, ∃ e k v, AccL st s e k v ∧ v.1.1 = t ∧
      ∀ J₁ J₂ hl, st.vinfo s v.2 k = some (J₁, J₂, hl) → hl ≤ i
  vinfo_len : ∀ s o k J₁ J₂ hl, st.vinfo s o k = some (J₁, J₂, hl) → hl ≤ st.hist.length

end Podc.ReconfigurableCommit
