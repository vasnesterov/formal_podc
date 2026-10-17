import Cslib.Computability.Distributed.ContentOblivious.Model
import Mathlib
import Papers.PODC2024.ContentObliviousLE.RingCounting

/-!
# Algorithm 2: quiescently terminating leader election on oriented rings

Frei, Gelles, Ghazy, Nolin, *Content-Oblivious Leader Election on Rings*, PODC 2024 (brief
announcement) / arXiv 2405.03646, Algorithm 2.

Ports of the oriented ring (`Cslib.ContentOblivious.oriented`): `Port1` (`true`) is the clockwise
(CW) port, `Port0` (`false`) the counterclockwise (CCW) one. So CW pulses are *sent* on `true` and
*received* on `false`; CCW pulses are sent on `false` and received on `true`.

The pseudo-code polls `recvCW()`/`recvCCW()` in a loop; we model it event-driven with the
`ready` predicate: a node reads CW pulses unless it waits for its termination pulse
(lines 18–19) or has terminated, and reads CCW pulses only once `ρcw ≥ ID` (line 9) or while
waiting. Each reception executes the remainder of the loop iteration (lines 9–10, 16–17, 20).
-/

namespace Podc.ContentOblivious.Alg2

open Cslib.ContentOblivious Finset

/-- Local state of a node running Algorithm 2. -/
structure S where
  /-- the node's ID -/
  id : ℕ
  /-- `ρcw`: CW pulses received -/
  rcw : ℕ
  /-- `ρccw`: CCW pulses received -/
  rccw : ℕ
  /-- `σccw ≠ 0`: the CCW instance has been started (line 10) -/
  started : Bool
  /-- the output variable `state` (`Leader` / `Non-Leader`) -/
  leader : Bool
  /-- waiting for the return of the termination pulse (lines 18–19) -/
  waiting : Bool
  /-- left the `repeat` loop (line 20): terminated -/
  done : Bool

/-- Reception of a CW pulse (lines 3–8, then 9–10, 16–17, 20). Output: pulses sent on
`Port0` (`false`, CCW) and `Port1` (`true`, CW). -/
def recvCW (s : S) : S × (Bool → ℕ) :=
  let start := !s.started && decide (s.id ≤ s.rcw + 1)
  let trig := decide (s.rcw + 1 = s.id ∧ s.rccw = s.id)
  ({ s with rcw := s.rcw + 1, leader := decide (s.rcw + 1 = s.id),
            started := s.started || start, waiting := s.waiting || trig,
            done := !trig && decide (s.rcw + 1 < s.rccw) },
   fun p => if p then (if s.rcw + 1 = s.id then 0 else 1)
     else (if start then 1 else 0) + (if trig then 1 else 0))

/-- Reception of a CCW pulse: either the awaited termination pulse (line 18, then line 20), or a
pulse of the CCW instance of Algorithm 1 (lines 11–15, then 16–17, 20). -/
def recvCCW (s : S) : S × (Bool → ℕ) :=
  if s.waiting then
    ({ s with rccw := s.rccw + 1, waiting := false, done := decide (s.rcw < s.rccw + 1) },
     fun _ => 0)
  else
    let trig := decide (s.rcw = s.id ∧ s.rccw + 1 = s.id)
    ({ s with rccw := s.rccw + 1, waiting := trig, done := !trig && decide (s.rcw < s.rccw + 1) },
     fun p => if p then 0 else (if s.rccw + 1 = s.id then 0 else 1) + (if trig then 1 else 0))

/-- Algorithm 2 (Quiescently Terminating Leader Election). -/
abbrev alg : Algo where
  State := S
  init i := (⟨i, 0, 0, false, false, false, false⟩, fun p => if p then 1 else 0)
  recv s j := if j then recvCCW s else recvCW s
  ready s j := !s.done && (if j then s.waiting || decide (s.id ≤ s.rcw) else !s.waiting)
  terminated s := s.done
  leader s := s.leader

/-! ## Static counting lemmas (Lemma 22 and the analysis of the termination event) -/

section static

variable {n : ℕ} [NeZero n] (id : ZMod n → ℕ) (M : ℕ)

/-- Per-node counter invariants (Lemma 5 for both instances; Corollary 13 bounds). Arguments:
ID `i`, `ρcw`, `σcw`, `ρccw`, `σccw`. -/
def NodeCnt (i a b c d : ℕ) : Prop :=
  b = a + (if a < i then 1 else 0) ∧
  d = (if i ≤ a then c + (if c < i then 1 else 0) else 0) ∧
  (a < i → c = 0) ∧ a ≤ M ∧ c ≤ M

/-- Counter invariants of a whole ring: per-node invariants and the two edge invariants. -/
structure Counters (rcw scw rccw sccw : ZMod n → ℕ) : Prop where
  node : ∀ v, NodeCnt M (id v) (rcw v) (scw v) (rccw v) (sccw v)
  ecw : ∀ v, rcw (v + 1) ≤ scw v
  eccw : ∀ v, rccw v ≤ sccw (v + 1)

variable {id M} {rcw scw rccw sccw : ZMod n → ℕ}

lemma Counters.profile_cw (h : Counters id M rcw scw rccw sccw) : Ring.Profile rcw scw id :=
  fun v => (h.node v).1

/-- **Lemma 22** (static form): as long as some node has `ρcw < ID` (no CW-quiescence), every node
with `ρcw ≥ ID` has `ρccw < ρcw`. -/
theorem Counters.rccw_lt (h : Counters id M rcw scw rccw sccw) (hid : Function.Injective id)
    (hpos : ∀ v, 0 < id v) (hbad : ∃ u, rcw u < id u) (v : ZMod n) (hv : id v ≤ rcw v) :
    rccw v < rcw v := by
  classical
  obtain ⟨u, hu⟩ := hbad
  have hex : ∃ k, rcw (v + (k : ℕ)) < id (v + (k : ℕ)) :=
    ⟨(u - v).val, by rw [ZMod.natCast_zmod_val, add_sub_cancel]; exact hu⟩
  obtain ⟨k, hkbad, hgood⟩ : ∃ k, rcw (v + (k : ℕ)) < id (v + (k : ℕ)) ∧
      ∀ j < k, id (v + (j : ℕ)) ≤ rcw (v + (j : ℕ)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_lt.1 (Nat.find_min hex hj)⟩
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hkbad; omega
    · exact h0
  have hkn : k < n := by
    by_contra hc
    have := hgood (u - v).val (lt_of_lt_of_le (ZMod.val_lt _) (not_lt.1 hc))
    rw [ZMod.natCast_zmod_val, add_sub_cancel] at this
    omega
  have hsucc : ∀ j : ℕ, v + (j : ZMod n) + 1 = v + ((j + 1 : ℕ) : ZMod n) := by
    intro j; push_cast; ring
  -- CCW chain
  have hccw : ∀ m < k, rccw (v + ((k - 1 - m : ℕ) : ZMod n)) ≤ m := by
    intro m
    induction m with
    | zero =>
      intro _
      have e := h.eccw (v + ((k - 1 - 0 : ℕ) : ZMod n))
      have : v + ((k - 1 - 0 : ℕ) : ZMod n) + 1 = v + (k : ℕ) := by
        rw [hsucc]; congr 3; omega
      rw [this, (h.node _).2.1, if_neg (not_le.2 hkbad)] at e
      omega
    | succ m ih =>
      intro hm
      have e := h.eccw (v + ((k - 1 - (m + 1) : ℕ) : ZMod n))
      have : v + ((k - 1 - (m + 1) : ℕ) : ZMod n) + 1 = v + ((k - 1 - m : ℕ) : ZMod n) := by
        rw [hsucc]; congr 3; omega
      rw [this, (h.node _).2.1, if_pos (hgood _ (by omega))] at e
      have := ih (by omega)
      split_ifs at e <;> omega
  have h1 : rccw v ≤ k - 1 := by
    have := hccw (k - 1) (by omega)
    rwa [show k - 1 - (k - 1) = 0 by omega, Nat.cast_zero, add_zero] at this
  -- CW chain
  have hcw : ∀ j < k, rcw (v + (j : ℕ)) ≤ rcw v := by
    intro j
    induction j with
    | zero => intro _; simp only [Nat.cast_zero, add_zero, le_refl]
    | succ j ih =>
      intro hj
      have e := h.ecw (v + (j : ℕ))
      rw [(h.node _).1, if_neg (not_lt.2 (hgood j (by omega))), hsucc] at e
      have := ih (by omega); omega
  -- pigeonhole on the `k` distinct positive IDs
  obtain ⟨j, hj⟩ := Ring.exists_ge_of_injective (fun j : Fin k => id (v + ((j : ℕ) : ZMod n)))
    (fun a b hab => Fin.ext (CharP.natCast_injOn_Iio (ZMod n) n (Set.mem_Iio.2 (by omega))
      (Set.mem_Iio.2 (by omega)) (add_left_cancel (hid hab))))
    (fun j => hpos _) hk0
  have := hgood j j.2
  have := hcw j j.2
  omega

/-- Consequence of Lemma 22 used for the loop condition (line 20): `ρccw ≤ ρcw` always holds before
the termination event. -/
theorem Counters.rccw_le (h : Counters id M rcw scw rccw sccw) (hid : Function.Injective id)
    (hpos : ∀ v, 0 < id v) {ℓ : ZMod n} (hℓ : id ℓ = M) (v : ZMod n) : rccw v ≤ rcw v := by
  by_cases hv : id v ≤ rcw v
  · by_cases hbad : ∃ u, rcw u < id u
    · exact (h.rccw_lt hid hpos hbad v hv).le
    · push_neg at hbad
      have := (h.profile_cw.eq_max_of_good (fun v => h.ecw v) hbad (fun v => (h.node v).2.2.2.1)
        hℓ v).1
      have := (h.node v).2.2.2.2
      omega
  · rw [(h.node v).2.2.1 (not_le.1 hv)]; omega

/-- **Lemma 24**: the event `ρcw = ID = ρccw` happens only at the node `ℓ` of maximal ID, and only when
every node has received and sent exactly `IDmax` pulses in both directions. -/
theorem Counters.trigger (h : Counters id M rcw scw rccw sccw) (hid : Function.Injective id)
    (hpos : ∀ v, 0 < id v) {ℓ : ZMod n} (hℓ : id ℓ = M) (hM : ∀ v, id v ≤ M) {v : ZMod n}
    (hv1 : rcw v = id v) (hv2 : rccw v = id v) :
    v = ℓ ∧ ∀ u, rcw u = M ∧ scw u = M ∧ rccw u = M ∧ sccw u = M := by
  have hgood : ∀ u, id u ≤ rcw u := by
    by_contra hc
    push_neg at hc
    have := h.rccw_lt hid hpos hc v hv1.ge
    omega
  have hcw := h.profile_cw.eq_max_of_good (fun v => h.ecw v) hgood (fun v => (h.node v).2.2.2.1) hℓ
  have hvl : v = ℓ := hid (by rw [hℓ, ← hv1, (hcw v).1])
  subst hvl
  -- the CCW instance, on the reversed ring
  have hprof : Ring.Profile (fun x => rccw (-x)) (fun x => sccw (-x)) (fun x => id (-x)) := by
    intro x; simp only; rw [(h.node (-x)).2.1, if_pos (hgood _)]
  have hedge : Ring.Edge (fun x => rccw (-x)) (fun x => sccw (-x)) := by
    intro x; have := h.eccw (-(x + 1)); simpa [neg_add_cancel_right] using this
  have hgood' := hprof.good_of_max_good hedge (M := M) (fun x => hM _)
    (fun x hx => by
      have : -x = v := hid (by rw [hx, hℓ])
      simp only [this, hv2, hℓ, le_refl]) (ℓ := -v) (by simpa using hℓ)
  have hccw := hprof.eq_max_of_good hedge hgood' (fun x => (h.node (-x)).2.2.2.2) (ℓ := -v)
    (by simpa using hℓ)
  refine ⟨rfl, fun u => ⟨(hcw u).1, (hcw u).2, ?_, ?_⟩⟩
  · simpa using (hccw (-u)).1
  · simpa using (hccw (-u)).2

lemma NodeCnt.sent_le {M i a b c d : ℕ} (h : NodeCnt M i a b c d) (hi : i ≤ M) : b ≤ M ∧ d ≤ M := by
  obtain ⟨h1, h2, -, h4, h5⟩ := h
  constructor
  · rw [h1]; split_ifs <;> omega
  · rw [h2]; split_ifs <;> omega

end static

/-! ## Per-node transitions -/

/-- State/counter agreement before the termination event. -/
def NodeSt1 (i : ℕ) (s : S) (a c : ℕ) : Prop :=
  s.id = i ∧ s.rcw = a ∧ s.rccw = c ∧ s.started = decide (i ≤ a) ∧ s.leader = decide (a = i) ∧
    s.waiting = false ∧ s.done = false

lemma cw_node {M i a b c d : ℕ} {s : S} (hcnt : NodeCnt M i a b c d) (hst : NodeSt1 i s a c)
    (hpos : 0 < i) (hle : c ≤ a) (hb : a + 1 ≤ M) :
    NodeCnt M i (a + 1) (b + (recvCW s).2 true) c (d + (recvCW s).2 false) ∧
      NodeSt1 i (recvCW s).1 (a + 1) c ∧ ¬(a + 1 = i ∧ c = i) := by
  rcases s with ⟨si, sr, sc, sst, sl, sw, sd⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcnt
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hst
  simp only at e1 e2 e3 e4 e5 e6 e7
  subst e1 e2 e3 e4 e6 e7 h1 h2
  by_cases hia : si ≤ sr
  · have hne : ¬ sr + 1 = si := by omega
    simp [NodeCnt, NodeSt1, recvCW, hia, hne, show si ≤ sr + 1 by omega,
      show ¬ sr < si by omega, show ¬ sr + 1 < si by omega] <;> omega
  · have hc : sc = 0 := h3 (by omega)
    subst hc
    by_cases hia' : sr + 1 = si
    · subst hia'
      simp [NodeCnt, NodeSt1, recvCW] <;> omega
    · simp [NodeCnt, NodeSt1, recvCW, hia, hia', show ¬ si ≤ sr + 1 by omega,
        show sr + 1 < si by omega, show sr < si by omega] <;> omega

lemma ccw_node_cnt {M i a b c d : ℕ} {s : S} (hcnt : NodeCnt M i a b c d) (hst : NodeSt1 i s a c)
    (hia : i ≤ a) (hb : c + 1 ≤ M) (hnt : ¬(a = i ∧ c + 1 = i)) :
    NodeCnt M i a (b + (recvCCW s).2 true) (c + 1) (d + (recvCCW s).2 false) := by
  rcases s with ⟨si, sr, sc, sst, sl, sw, sd⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := hcnt
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hst
  simp only at e1 e2 e3 e4 e5 e6 e7
  subst e1 e2 e3 e4 e6 e7 h1 h2
  have hnt' : ¬(sr = si ∧ sc + 1 = si) := hnt
  by_cases hc : sc + 1 = si
  · have : ¬ sr = si := fun h => hnt ⟨h, hc⟩
    subst hc
    simp [NodeCnt, recvCCW, hia, this, show ¬ sr < sc + 1 by omega]
    exact ⟨h4, by omega⟩
  · by_cases hc' : sc + 1 < si
    · simp [NodeCnt, recvCCW, hia, hc, hc', hnt', show ¬ sr < si by omega,
        show sc < si by omega] <;> omega
    · simp [NodeCnt, recvCCW, hia, hc, hc', hnt', show ¬ sr < si by omega]
      exact ⟨by omega, h4, by omega⟩

lemma ccw_node_st {i a c : ℕ} {s : S} (hst : NodeSt1 i s a c) (hnt : ¬(a = i ∧ c + 1 = i))
    (hle : c + 1 ≤ a) : NodeSt1 i (recvCCW s).1 a (c + 1) := by
  rcases s with ⟨si, sr, sc, sst, sl, sw, sd⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hst
  simp only at e1 e2 e3 e4 e5 e6 e7
  subst e1 e2 e3 e4 e5 e6 e7
  have hnt' : ¬(sr = si ∧ sc + 1 = si) := hnt
  simp [NodeSt1, recvCCW, hnt'] <;> omega

lemma ccw_node_trig {M i a b c d : ℕ} {s : S} (hcnt : NodeCnt M i a b c d) (hst : NodeSt1 i s a c)
    (h1 : a = i) (h2 : c + 1 = i) :
    (recvCCW s).2 true = 0 ∧ (recvCCW s).2 false = 1 ∧ d = c + 1 ∧
      (recvCCW s).1 = { s with rccw := c + 1, waiting := true, done := false } := by
  rcases s with ⟨si, sr, sc, sst, sl, sw, sd⟩
  obtain ⟨-, hd, -⟩ := hcnt
  obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := hst
  simp only at e1 e2 e3 e4 e5 e6 e7
  subst e1 e2 e3 e6 e7 h1 hd
  subst h2; simp [recvCCW]


lemma NodeCnt.of_trig {M i a b c d : ℕ} (h : NodeCnt M i a b c d) (h1 : a = i) (h2 : c + 1 = i)
    (hb : c + 1 ≤ M) : NodeCnt M i a b (c + 1) d := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := h
  refine ⟨e1, ?_, fun h => by omega, e4, hb⟩
  rw [e2]; simp [show i ≤ a by omega, show c < i by omega, show ¬ c + 1 < i by omega]

/-! ## Configuration invariants -/

section dynamic

variable {n : ℕ} [NeZero n] {id : ZMod n → ℕ}

/-- Configurations of Algorithm 2 on the oriented ring of size `n`. -/
abbrev Cfg (n : ℕ) := Config (ZMod n) S

/-- Invariant before the termination event (all four counters of each node, its local state, and
the fact that the event `ρcw = ID = ρccw` has not happened yet). -/
def Inv1 (id : ZMod n → ℕ) (M : ℕ) (c : Cfg n) : Prop :=
  ∀ v, NodeCnt M (id v) (c.recvd (v, false)) (c.sent (v, true)) (c.recvd (v, true)) (c.sent (v, false)) ∧
    NodeSt1 (id v) (c.st v) (c.recvd (v, false)) (c.recvd (v, true)) ∧
    ¬(c.recvd (v, false) = id v ∧ c.recvd (v, true) = id v)

/-- Invariant after the termination event at `ℓ`: CW-quiescence with all counters `= IDmax`, the
termination pulse travelling CCW; nodes it has passed have terminated. -/
def Inv2 (id : ZMod n → ℕ) (ℓ : ZMod n) (c : Cfg n) : Prop :=
  (∀ v, (c.st v).id = id v ∧ (c.st v).rcw = c.recvd (v, false) ∧ (c.st v).rccw = c.recvd (v, true) ∧
      c.recvd (v, false) = id ℓ ∧ c.sent (v, true) = id ℓ ∧ (c.st v).started = true ∧
      (c.st v).leader = decide (id ℓ = id v)) ∧
  (∀ v, v ≠ ℓ → c.sent (v, false) = c.recvd (v, true) ∧ (c.st v).waiting = false ∧
      ((c.recvd (v, true) = id ℓ ∧ (c.st v).done = false) ∨
        (c.recvd (v, true) = id ℓ + 1 ∧ (c.st v).done = true))) ∧
  c.sent (ℓ, false) = id ℓ + 1 ∧
  ((c.recvd (ℓ, true) = id ℓ ∧ (c.st ℓ).waiting = true ∧ (c.st ℓ).done = false) ∨
    (c.recvd (ℓ, true) = id ℓ + 1 ∧ (c.st ℓ).waiting = false ∧ (c.st ℓ).done = true))

lemma edges {c : Cfg n} (h : Reach (oriented n) alg id c) :
    (∀ v, c.recvd (v + 1, false) ≤ c.sent (v, true)) ∧ ∀ v, c.recvd (v, true) ≤ c.sent (v + 1, false) := by
  refine ⟨fun v => ?_, fun v => ?_⟩
  · have := h.recvd_le (v + 1, false); simpa using this
  · have := h.recvd_le (v, true); simpa using this

lemma Inv1.counters {M : ℕ} {c : Cfg n} (h : Inv1 id M c) (hr : Reach (oriented n) alg id c) :
    Counters id M (fun v => c.recvd (v, false)) (fun v => c.sent (v, true))
      (fun v => c.recvd (v, true)) (fun v => c.sent (v, false)) :=
  ⟨fun v => (h v).1, (edges hr).1, (edges hr).2⟩

section deliver

variable (c : Cfg n) (v u : ZMod n) (j k : Bool)

lemma d_recvd_ne (h : u ≠ v) : (deliver alg c v j).recvd (u, k) = c.recvd (u, k) := by
  simp [deliver, h]
lemma d_sent_ne (h : u ≠ v) : (deliver alg c v j).sent (u, k) = c.sent (u, k) := by
  simp [deliver, h]
lemma d_st_ne (h : u ≠ v) : (deliver alg c v j).st u = c.st u := by simp [deliver, h]
lemma d_recvd_self : (deliver alg c v j).recvd (v, k) = c.recvd (v, k) + if k = j then 1 else 0 := by
  simp [deliver]
lemma d_sent_self : (deliver alg c v j).sent (v, k) = c.sent (v, k) + (alg.recv (c.st v) j).2 k := by
  simp [deliver]
lemma d_st_self : (deliver alg c v j).st v = (alg.recv (c.st v) j).1 := by simp [deliver]

end deliver

lemma alg_recv_false (s : S) : alg.recv s false = recvCW s := rfl
lemma alg_recv_true (s : S) : alg.recv s true = recvCCW s := rfl

variable {ℓ : ZMod n}

lemma inv1_init (hpos : ∀ v, 0 < id v) (hℓ : ∀ v, id v ≤ id ℓ) :
    Inv1 id (id ℓ) (initCfg alg id) := by
  intro v
  have := hpos v
  simp only [initCfg, alg]
  refine ⟨⟨?_, ?_, fun _ => rfl, Nat.zero_le _, Nat.zero_le _⟩, ⟨rfl, rfl, rfl, ?_, ?_, rfl, rfl⟩, ?_⟩
  · simp [this]
  all_goals (try simp) <;> omega

/-- One step from `Inv1`: either `Inv1` is preserved or the termination event happens and `Inv2`
holds. -/
lemma step_inv1 (hid : Function.Injective id) (hpos : ∀ v, 0 < id v) (hℓ : ∀ v, id v ≤ id ℓ)
    {c : Cfg n} (hr : Reach (oriented n) alg id c) (h : Inv1 id (id ℓ) c) {v : ZMod n} {j : Bool}
    (hen : Enabled (oriented n) alg c v j) :
    Inv1 id (id ℓ) (deliver alg c v j) ∨ Inv2 id ℓ (deliver alg c v j) := by
  have hr' : Reach (oriented n) alg id (deliver alg c v j) := hr.tail (Step.mk (W := oriented n) (A := alg) c v j hen)
  have hC := h.counters hr
  obtain ⟨hcnt, hst, hnt⟩ := h v
  obtain ⟨-, hready, hlt⟩ := hen
  cases j with
  | false =>
    left
    simp only [oriented_peer_false] at hlt
    have hb : c.recvd (v, false) + 1 ≤ id ℓ := by
      have := ((h (v - 1)).1.sent_le (hℓ _)).1; omega
    have hle := hC.rccw_le hid hpos rfl v
    obtain ⟨n1, n2, n3⟩ := cw_node hcnt hst (hpos v) hle hb
    intro u
    by_cases hu : u = v
    · subst hu
      simp only [d_recvd_self, d_sent_self, d_st_self, alg_recv_false]
      exact ⟨by simpa using n1, by simpa using n2, by simpa using n3⟩
    · simp only [d_recvd_ne _ _ _ _ _ hu, d_sent_ne _ _ _ _ _ hu, d_st_ne _ _ _ _ hu]
      exact h u
  | true =>
    simp only [oriented_peer_true] at hlt
    have hwait : (c.st v).waiting = false := hst.2.2.2.2.2.1
    have hdone : (c.st v).done = false := hst.2.2.2.2.2.2
    have hia : id v ≤ c.recvd (v, false) := by
      simp only [alg, hdone, hwait, hst.1, hst.2.1] at hready; simpa using hready
    have hb : c.recvd (v, true) + 1 ≤ id ℓ := by
      have := ((h (v + 1)).1.sent_le (hℓ _)).2; omega
    by_cases htr : c.recvd (v, false) = id v ∧ c.recvd (v, true) + 1 = id v
    · -- the termination event
      right
      obtain ⟨t1, t2, t3, t4⟩ := ccw_node_trig hcnt hst htr.1 htr.2
      set c' := deliver alg c v true with hc'
      have hcnt' := hcnt.of_trig htr.1 htr.2 hb
      -- counters of `c'` without the termination pulse
      let sccw : ZMod n → ℕ := fun u => if u = v then c.sent (v, false) else c'.sent (u, false)
      have hC' : Counters id (id ℓ) (fun u => c'.recvd (u, false)) (fun u => c'.sent (u, true))
          (fun u => c'.recvd (u, true)) sccw := by
        refine ⟨fun u => ?_, (edges hr').1, fun u => ?_⟩
        · by_cases hu : u = v
          · subst hu
            simp only [sccw, if_true, hc', d_recvd_self, d_sent_self, alg_recv_true, t1]
            simpa using hcnt'
          · simp only [sccw, if_neg hu, hc', d_recvd_ne _ _ _ _ _ hu, d_sent_ne _ _ _ _ _ hu]
            exact (h u).1
        · by_cases hu : u + 1 = v
          · simp only [sccw, if_pos hu]
            by_cases huv : u = v
            · subst huv; simp only [hc', d_recvd_self]; simp [t3]
            · simp only [hc', d_recvd_ne _ _ _ _ _ huv]
              have := (edges hr).2 u; rwa [hu] at this
          · simp only [sccw, if_neg hu]; exact (edges hr').2 u
      have htrig := hC'.trigger hid hpos rfl hℓ (v := v)
        (by simp [hc', d_recvd_self]; exact htr.1)
        (by simp [hc', d_recvd_self]; exact htr.2)
      obtain ⟨hvl, hall⟩ := htrig
      subst v
      refine ⟨fun u => ?_, fun u hu => ?_, ?_, ?_⟩
      · obtain ⟨a1, a2, a3, a4⟩ := hall u
        simp only at a1 a2 a3 a4
        refine ⟨?_, ?_, ?_, a1, a2, ?_, ?_⟩
        · by_cases hu : u = ℓ
          · subst hu; simp [hc', d_st_self, alg_recv_true, t4, hst.1]
          · simp [hc', d_st_ne _ _ _ _ hu, (h u).2.1.1]
        · by_cases hu : u = ℓ
          · subst hu; simp [hc', d_st_self, alg_recv_true, t4, hst.2.1, d_recvd_self]
          · simp [hc', d_st_ne _ _ _ _ hu, (h u).2.1.2.1, d_recvd_ne _ _ _ _ _ hu]
        · by_cases hu : u = ℓ
          · subst hu; simp [hc', d_st_self, alg_recv_true, t4, d_recvd_self]
          · simp [hc', d_st_ne _ _ _ _ hu, (h u).2.1.2.2.1, d_recvd_ne _ _ _ _ _ hu]
        · by_cases hu : u = ℓ
          · subst hu; simp [hc', d_st_self, alg_recv_true, t4, hst.2.2.2.1, hia]
          · have := (h u).2.1.2.2.2.1
            rw [hc', d_st_ne _ _ _ _ hu, this, decide_eq_true_eq]
            rw [hc', d_recvd_ne _ _ _ _ _ hu] at a1; rw [a1]; exact hℓ u
        · by_cases hu : u = ℓ
          · subst hu; simp [hc', d_st_self, alg_recv_true, t4, hst.2.2.2.2.1, htr.1]
          · have := (h u).2.1.2.2.2.2.1
            rw [hc', d_st_ne _ _ _ _ hu, this]
            rw [hc', d_recvd_ne _ _ _ _ _ hu] at a1; rw [a1]
      · obtain ⟨-, -, a3, a4⟩ := hall u
        simp only [sccw, if_neg hu] at a3 a4
        refine ⟨by rw [a3, a4], ?_, Or.inl ⟨a3, ?_⟩⟩
        · simp [hc', d_st_ne _ _ _ _ hu, (h u).2.1.2.2.2.2.2.1]
        · simp [hc', d_st_ne _ _ _ _ hu, (h u).2.1.2.2.2.2.2.2]
      · have := htr.2
        rw [hc', d_sent_self, alg_recv_true, t2, t3]; omega
      · left
        have := htr.2
        simp only [hc', d_recvd_self, d_st_self, alg_recv_true, t4, if_true]
        simp; omega
    · left
      have n1 := ccw_node_cnt hcnt hst hia hb htr
      have hcnt' : ∀ u, NodeCnt (id ℓ) (id u) ((deliver alg c v true).recvd (u, false))
          ((deliver alg c v true).sent (u, true)) ((deliver alg c v true).recvd (u, true))
          ((deliver alg c v true).sent (u, false)) := by
        intro u
        by_cases hu : u = v
        · subst hu; simpa [d_recvd_self, d_sent_self, alg_recv_true] using n1
        · simp only [d_recvd_ne _ _ _ _ _ hu, d_sent_ne _ _ _ _ _ hu]; exact (h u).1
      have hC' : Counters id (id ℓ) _ _ _ _ := ⟨hcnt', (edges hr').1, (edges hr').2⟩
      have hle := hC'.rccw_le hid hpos rfl v
      simp only [d_recvd_self] at hle
      simp only [Bool.false_eq_true, ite_false, ite_true, add_zero] at hle
      have n2 := ccw_node_st hst htr hle
      intro u
      by_cases hu : u = v
      · subst hu
        refine ⟨hcnt' u, ?_, ?_⟩
        · simpa [d_recvd_self, d_st_self, alg_recv_true] using n2
        · simpa [d_recvd_self] using htr
      · simp only [d_recvd_ne _ _ _ _ _ hu, d_sent_ne _ _ _ _ _ hu, d_st_ne _ _ _ _ hu]
        exact h u

lemma recvCCW_relay {s : S} {M : ℕ} (hw : s.waiting = false) (h1 : s.rcw = M) (h2 : s.rccw = M)
    (hi : s.id ≤ M) :
    recvCCW s = ({ s with rccw := M + 1, waiting := false, done := true }, fun p => if p then 0 else 1) := by
  rcases s with ⟨si, sr, sc, sst, sl, sw, sd⟩
  simp only at hw h1 h2 hi
  subst hw h1 h2
  refine Prod.ext ?_ ?_
  · simp [recvCCW]; omega
  · funext p; cases p <;> simp [recvCCW] <;> split_ifs <;> omega

lemma recvCCW_wait {s : S} {M : ℕ} (hw : s.waiting = true) (h1 : s.rcw = M) (h2 : s.rccw = M) :
    recvCCW s = ({ s with rccw := M + 1, waiting := false, done := true }, fun _ => 0) := by
  rcases s with ⟨si, sr, sc, sst, sl, sw, sd⟩
  simp only at hw h1 h2
  subst hw h1 h2
  simp [recvCCW]

/-- `Inv2` is preserved: the termination pulse travels CCW around the ring back to `ℓ`. -/
lemma step_inv2 (hid : Function.Injective id) (hℓ : ∀ v, id v ≤ id ℓ) {c : Cfg n}
    (h : Inv2 id ℓ c) {v : ZMod n} {j : Bool} (hen : Enabled (oriented n) alg c v j) :
    Inv2 id ℓ (deliver alg c v j) := by
  obtain ⟨hA, hB, hC, hD⟩ := h
  obtain ⟨-, hready, hlt⟩ := hen
  cases j with
  | false =>
    simp only [oriented_peer_false] at hlt
    have := (hA v).2.2.2.1; have := (hA (v - 1)).2.2.2.2.1; omega
  | true =>
    have hdone : (c.st v).done = false := by
      simp only [alg] at hready; revert hready; cases (c.st v).done <;> simp
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hA v
    by_cases hv : v = ℓ
    · subst hv
      have hwait : (c.st v).waiting = true ∧ c.recvd (v, true) = id v := by
        rcases hD with ⟨d1, d2, -⟩ | ⟨-, -, d3⟩
        · exact ⟨d2, d1⟩
        · rw [hdone] at d3; cases d3
      have hr := recvCCW_wait hwait.1 (a2.trans a4) (a3.trans hwait.2)
      refine ⟨fun u => ?_, fun u hu => ?_, ?_, ?_⟩
      · by_cases hu : u = v
        · subst hu
          simp only [d_st_self, d_recvd_self, d_sent_self, alg_recv_true, hr]
          simp [a1, a2, a4, a5, a6, a7, hwait.2]
        · simp only [d_st_ne _ _ _ _ hu, d_recvd_ne _ _ _ _ _ hu, d_sent_ne _ _ _ _ _ hu]
          exact hA u
      · simp only [d_st_ne _ _ _ _ hu, d_recvd_ne _ _ _ _ _ hu, d_sent_ne _ _ _ _ _ hu]
        exact hB u hu
      · simp only [d_sent_self, alg_recv_true, hr, hC]; rfl
      · right
        simp only [d_st_self, d_recvd_self, alg_recv_true, hr]
        simp [hwait.2]
    · obtain ⟨b1, b2, b3⟩ := hB v hv
      have hM : c.recvd (v, true) = id ℓ := by
        rcases b3 with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact h1
        · rw [hdone] at h2; cases h2
      have hr := recvCCW_relay b2 (a2.trans a4) (a3.trans hM) (a1 ▸ hℓ v)
      refine ⟨fun u => ?_, fun u hu => ?_, ?_, ?_⟩
      · by_cases hu : u = v
        · subst hu
          simp only [d_st_self, d_recvd_self, d_sent_self, alg_recv_true, hr]
          simp [a1, a2, a4, a5, a6, a7, hM]
        · simp only [d_st_ne _ _ _ _ hu, d_recvd_ne _ _ _ _ _ hu, d_sent_ne _ _ _ _ _ hu]
          exact hA u
      · by_cases huv : u = v
        · subst huv
          simp only [d_st_self, d_recvd_self, d_sent_self, alg_recv_true, hr]
          simp [b1, hM]
        · simp only [d_st_ne _ _ _ _ huv, d_recvd_ne _ _ _ _ _ huv, d_sent_ne _ _ _ _ _ huv]
          exact hB u hu
      · rw [d_sent_ne _ _ _ _ _ (Ne.symm hv)]; exact hC
      · simp only [d_st_ne _ _ _ _ (Ne.symm hv), d_recvd_ne _ _ _ _ _ (Ne.symm hv)]; exact hD

/-- Every reachable configuration satisfies `Inv1` or `Inv2`. -/
theorem reach_inv (hid : Function.Injective id) (hpos : ∀ v, 0 < id v) (hℓ : ∀ v, id v ≤ id ℓ)
    {c : Cfg n} (h : Reach (oriented n) alg id c) : Inv1 id (id ℓ) c ∨ Inv2 id ℓ c := by
  induction h with
  | refl => exact Or.inl (inv1_init hpos hℓ)
  | tail hr hs ih =>
    obtain ⟨v, j, hen⟩ := hs
    rcases ih with h1 | h2
    · exact step_inv1 hid hpos hℓ hr h1 hen
    · exact Or.inr (step_inv2 hid hℓ h2 hen)

end dynamic

end Podc.ContentOblivious.Alg2
