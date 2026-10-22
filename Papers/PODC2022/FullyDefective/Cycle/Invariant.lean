import Papers.PODC2022.FullyDefective.Cycle.Model
import Cslib.Foundations.Data.ZMod.Cyclic

/-!
# Lemma 5 of [CCGS22] (safety part): the invariant of Algorithm 1

An inductive invariant of the ring layer of Algorithm 1 (`Cycle/Model.lean`). It describes the
configurations of an epoch `K = |ds|` (`ds` = ghost list of the payloads of the epochs started so
far, `T = hold` = the node that took the token last) in three stages:

* `DataStage` — `T` sends its `d` data pulses (line 21); every other node is still in epoch `K`,
  in its token phase or forwarding data pulses (`fwd k`, `k ≤ d`); no counterclockwise pulse is in
  transit;
* `EndStage` — `T` has sent its `end` pulse (line 23); the `end` pulse travels counterclockwise,
  the nodes it has passed have completed epoch `K` and are in the token phase of epoch `K + 1`,
  the others are still in `fwd d`;
* `TokStage` — everybody completed epoch `K` (`K = 0` initially) and is in the token phase of
  epoch `K + 1`; at most one pulse (the `token`) is in transit counterclockwise.

The common part says that each node's pulse counters are determined by its local state (the sent
transcript of Lemma 5(3): per epoch one `request` and `d` `data` pulses clockwise), that each log
(decoded payloads) is a prefix of `ds` (global consistency, Lemma 5(3)), and that only `T` holds
the token (Lemma 5(2)).
-/

namespace Podc.FullyDefective.Cycle

variable {n : ℕ}

/-- Number of epochs completed by `u`. -/
abbrev Config.ep (c : Config n) (u : ZMod n) : ℕ := (c.node u).log.length

/-- Clockwise pulses of the first `e` epochs: one `request` and `d_j` `data` pulses each. -/
def base (ds : List ℕ) (e : ℕ) : ℕ := ((ds.take e).map (· + 1)).sum

/-- Clockwise pulses sent in the current epoch, as a function of the program point. -/
def Phase.sOff : Phase → ℕ
  | .idle => 0
  | .waitReq => 1
  | .ready => 1
  | .fwd c => c + 1
  | .send d _ => d + 1
  | .waitEnd d => d + 1

/-- Clockwise pulses received in the current epoch, as a function of the program point. -/
def Phase.rOff : Phase → ℕ
  | .idle => 0
  | .waitReq => 0
  | .ready => 1
  | .fwd c => c + 1
  | .send _ r => r + 1
  | .waitEnd d => d + 1

/-- Program points of the token phase (lines 1–17, before any data pulse). -/
def Phase.IsTok : Phase → Prop
  | .idle | .waitReq | .ready => True
  | _ => False

/-- Program points at which the token holder keeps `isTokenHolder = True`: the data phase, and
lines 1–3 of the next epoch (`b` = "the epoch of the data phase is completed"). -/
def Phase.Holding (b : Prop) : Phase → Prop
  | .send _ _ | .waitEnd _ => True
  | .idle | .waitReq => b
  | _ => False

/-- The part of the invariant common to all stages. -/
structure Common (c : Config n) : Prop where
  log : ∀ u, (c.node u).log = c.ds.take (c.ep u)
  ep_le : ∀ u, c.ep u ≤ c.ds.length
  cwS : ∀ u, c.cwS u = base c.ds (c.ep u) + (c.node u).ph.sOff
  cwR : ∀ u, c.cwR u = base c.ds (c.ep u) + (c.node u).ph.rOff
  cwChan : ∀ u, c.cwR u ≤ c.cwS (u - 1)
  ccwChan : ∀ u, c.ccwR u ≤ c.ccwS (u + 1)
  ccwOne : ∀ u, c.ccwS (u + 1) ≤ c.ccwR u + 1
  ccwUniq : ∀ u v, c.ccwIn u → c.ccwIn v → u = v
  posq : ∀ u, ∀ a ∈ (c.node u).q, 0 < a
  tok : ∀ u, (c.node u).tok = true ↔
    u = c.hold ∧ (c.node u).ph.Holding (c.ep u = c.ds.length)

/-- Data stage of epoch `|pre| + 1`, payload `d`; the holder got `r` data pulses back. -/
structure DataStage (c : Config n) (pre : List ℕ) (d r : ℕ) : Prop where
  ds_eq : c.ds = pre ++ [d]
  ph_hold : (c.node c.hold).ph = .send d r
  r_lt : r < d
  ep_hold : c.ep c.hold = pre.length
  others : ∀ u, u ≠ c.hold → c.ep u = pre.length ∧
    ((c.node u).ph.IsTok ∨ ∃ k, (c.node u).ph = .fwd k ∧ 1 ≤ k ∧ k ≤ d)
  noIn : ∀ u, ¬ c.ccwIn u

/-- End stage of epoch `|pre| + 1`, payload `d`: the `end` pulse travels counterclockwise. -/
structure EndStage (c : Config n) (pre : List ℕ) (d : ℕ) : Prop where
  ds_eq : c.ds = pre ++ [d]
  ph_hold : (c.node c.hold).ph = .waitEnd d
  ep_hold : c.ep c.hold = pre.length
  others : ∀ u, u ≠ c.hold →
    (c.ep u = pre.length ∧ (c.node u).ph = .fwd d) ∨
    (c.ep u = pre.length + 1 ∧ (c.node u).ph.IsTok)
  wave : ∀ u, u ≠ c.hold → c.ep u = pre.length + 1 →
    u + 1 = c.hold ∨ c.ep (u + 1) = pre.length + 1
  target : ∀ v, c.ccwIn v →
    (v + 1 = c.hold ∨ c.ep (v + 1) = pre.length + 1) ∧ (v = c.hold ∨ c.ep v = pre.length)
  someIn : ∃ v, c.ccwIn v

/-- Token stage: every node completed all started epochs and is in its token phase. -/
structure TokStage (c : Config n) : Prop where
  ep_all : ∀ u, c.ep u = c.ds.length
  isTok : ∀ u, (c.node u).ph.IsTok
  held : (c.node c.hold).tok = true → ∀ u, ¬ c.ccwIn u
  released : (c.node c.hold).tok = false → ∃ u, c.ccwIn u

/-- The invariant of Algorithm 1. -/
def Inv (c : Config n) : Prop :=
  Common c ∧ ((∃ pre d r, DataStage c pre d r) ∨ (∃ pre d, EndStage c pre d) ∨ TokStage c)

/-! ### Basic lemmas -/

@[simp] lemma base_nil (e : ℕ) : base [] e = 0 := by simp [base]

lemma base_append_of_le {ds : List ℕ} {e : ℕ} (a : ℕ) (h : e ≤ ds.length) :
    base (ds ++ [a]) e = base ds e := by
  simp [base, List.take_append_of_le_length h]

lemma base_succ {ds : List ℕ} (d : ℕ) : base (ds ++ [d]) (ds.length + 1) = base ds ds.length + d + 1 := by
  simp [base, add_assoc, List.take_of_length_le]

section next

variable (c : Config n) (u v : ZMod n)

@[simp] lemma next_push_node (a : ℕ) : (next c (.push u a)).node v =
    if v = u then { c.node u with q := (c.node u).q ++ [a] } else c.node v := by
  simp [next, Function.update_apply]

@[simp] lemma next_push_cwS (a : ℕ) : (next c (.push u a)).cwS = c.cwS := rfl
@[simp] lemma next_push_cwR (a : ℕ) : (next c (.push u a)).cwR = c.cwR := rfl
@[simp] lemma next_push_ccwS (a : ℕ) : (next c (.push u a)).ccwS = c.ccwS := rfl
@[simp] lemma next_push_ccwR (a : ℕ) : (next c (.push u a)).ccwR = c.ccwR := rfl
@[simp] lemma next_push_ds (a : ℕ) : (next c (.push u a)).ds = c.ds := rfl
@[simp] lemma next_push_hold (a : ℕ) : (next c (.push u a)).hold = c.hold := rfl

@[simp] lemma next_start_node : (next c (.start u)).node v =
    if v = u then { c.node u with ph := .waitReq } else c.node v := by
  simp [next, Function.update_apply]

@[simp] lemma next_start_cwS : (next c (.start u)).cwS v = c.cwS v + if v = u then 1 else 0 := by
  simp [next, Function.update_apply]; split_ifs <;> simp_all

@[simp] lemma next_start_cwR : (next c (.start u)).cwR = c.cwR := rfl
@[simp] lemma next_start_ccwS : (next c (.start u)).ccwS = c.ccwS := rfl
@[simp] lemma next_start_ccwR : (next c (.start u)).ccwR = c.ccwR := rfl
@[simp] lemma next_start_ds : (next c (.start u)).ds = c.ds := rfl
@[simp] lemma next_start_hold : (next c (.start u)).hold = c.hold := rfl

@[simp] lemma next_cw_node : (next c (.cw u)).node v =
    if v = u then (onCW (c.node u)).1 else c.node v := by
  simp [next, Function.update_apply]

@[simp] lemma next_cw_cwS : (next c (.cw u)).cwS v =
    c.cwS v + if v = u then (onCW (c.node u)).2.1 else 0 := by
  simp [next, Function.update_apply]; split_ifs <;> simp_all

@[simp] lemma next_cw_ccwS : (next c (.cw u)).ccwS v =
    c.ccwS v + if v = u then (onCW (c.node u)).2.2 else 0 := by
  simp [next, Function.update_apply]; split_ifs <;> simp_all

@[simp] lemma next_cw_cwR : (next c (.cw u)).cwR v = c.cwR v + if v = u then 1 else 0 := by
  simp [next, Function.update_apply]; split_ifs <;> simp_all

@[simp] lemma next_cw_ccwR : (next c (.cw u)).ccwR = c.ccwR := rfl
@[simp] lemma next_cw_ds : (next c (.cw u)).ds = c.ds := rfl
@[simp] lemma next_cw_hold : (next c (.cw u)).hold = c.hold := rfl

@[simp] lemma next_ccw_node : (next c (.ccw u)).node v =
    if v = u then (onCCW (c.node u)).1 else c.node v := by
  simp [next, Function.update_apply]

@[simp] lemma next_ccw_cwS : (next c (.ccw u)).cwS v =
    c.cwS v + if v = u then (onCCW (c.node u)).2.1 else 0 := by
  simp [next, Function.update_apply]; split_ifs <;> simp_all

@[simp] lemma next_ccw_ccwS : (next c (.ccw u)).ccwS v =
    c.ccwS v + if v = u then (onCCW (c.node u)).2.2 else 0 := by
  simp [next, Function.update_apply]; split_ifs <;> simp_all

@[simp] lemma next_ccw_ccwR : (next c (.ccw u)).ccwR v = c.ccwR v + if v = u then 1 else 0 := by
  simp [next, Function.update_apply]; split_ifs <;> simp_all

@[simp] lemma next_ccw_cwR : (next c (.ccw u)).cwR = c.cwR := rfl

lemma next_ccw_ds : (next c (.ccw u)).ds =
    match capture? (c.node u) with | some a => c.ds ++ [a] | none => c.ds := rfl

lemma next_ccw_hold : (next c (.ccw u)).hold =
    match capture? (c.node u) with | some _ => u | none => c.hold := rfl

end next

/-! ### The initial configuration -/

theorem inv_init (T₀ : ZMod n) {qs : ZMod n → List ℕ} (hqs : ∀ u, ∀ a ∈ qs u, 0 < a) :
    Inv (init T₀ qs) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hqs, ?_⟩, Or.inr (Or.inr ⟨?_, ?_, ?_, ?_⟩)⟩ <;>
    simp [init, Config.ccwIn, Phase.sOff, Phase.rOff, Phase.IsTok, Phase.Holding]

/-! ### Steps that do not touch the pulses -/

theorem inv_push {c : Config n} (h : Inv c) (u : ZMod n) {a : ℕ} (ha : 0 < a) :
    Inv (next c (.push u a)) := by
  obtain ⟨hC, hS⟩ := h
  have hn : ∀ v, ((next c (.push u a)).node v).ph = (c.node v).ph ∧
      ((next c (.push u a)).node v).tok = (c.node v).tok ∧
      ((next c (.push u a)).node v).log = (c.node v).log := by
    intro v; by_cases hv : v = u <;> simp [hv]
  have hep : ∀ v, (next c (.push u a)).ep v = c.ep v := fun v => by
    rw [Config.ep, (hn v).2.2]
  refine ⟨⟨fun v => by rw [(hn v).2.2, hep]; exact hC.log v, fun v => by rw [hep]; exact hC.ep_le v,
    fun v => by simp only [next_push_cwS, next_push_ds, hep, (hn v).1]; exact hC.cwS v,
    fun v => by simp only [next_push_cwR, next_push_ds, hep, (hn v).1]; exact hC.cwR v,
    hC.cwChan, hC.ccwChan, hC.ccwOne, hC.ccwUniq, ?_, ?_⟩, ?_⟩
  · intro v b hb
    by_cases hv : v = u
    · subst hv; simp at hb; rcases hb with hb | rfl
      · exact hC.posq _ _ hb
      · exact ha
    · simp [hv] at hb; exact hC.posq _ _ hb
  · intro v; simp only [(hn v).1, (hn v).2.1, hep, next_push_ds, next_push_hold]; exact hC.tok v
  · have hc : (next c (.push u a)).ccwIn = c.ccwIn := rfl
    rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
    · exact Or.inl ⟨pre, d, r, H.ds_eq, by rw [(hn _).1]; exact H.ph_hold, H.r_lt,
        by rw [next_push_hold, hep]; exact H.ep_hold,
        fun v hv => by rw [(hn v).1, hep]; exact H.others v hv, by rw [hc]; exact H.noIn⟩
    · exact Or.inr (Or.inl ⟨pre, d, H.ds_eq, by rw [(hn _).1]; exact H.ph_hold,
        by rw [next_push_hold, hep]; exact H.ep_hold,
        fun v hv => by rw [(hn v).1, hep]; exact H.others v hv,
        fun v hv => by simp only [hep]; exact H.wave v hv,
        fun v hv => by simp only [hep]; exact H.target v hv, H.someIn⟩)
    · exact Or.inr (Or.inr ⟨fun v => by rw [hep]; exact H.ep_all v,
        fun v => by rw [(hn v).1]; exact H.isTok v,
        fun h' => by rw [hc]; exact H.held (by rw [← (hn _).2.1]; exact h'),
        fun h' => by rw [hc]; exact H.released (by rw [← (hn _).2.1]; exact h')⟩)

theorem inv_start {c : Config n} (h : Inv c) {u : ZMod n} (hu : (c.node u).ph = .idle) :
    Inv (next c (.start u)) := by
  obtain ⟨hC, hS⟩ := h
  set c' := next c (.start u)
  have hph : ∀ v, (c'.node v).ph = if v = u then .waitReq else (c.node v).ph := by
    intro v; by_cases hv : v = u <;> simp [c', hv]
  have htok : ∀ v, (c'.node v).tok = (c.node v).tok := by
    intro v; by_cases hv : v = u <;> simp [c', hv]
  have hlog : ∀ v, (c'.node v).log = (c.node v).log := by
    intro v; by_cases hv : v = u <;> simp [c', hv]
  have hep : ∀ v, c'.ep v = c.ep v := fun v => by rw [Config.ep, hlog]
  have hc : c'.ccwIn = c.ccwIn := rfl
  have hds : c'.ds = c.ds := rfl
  have hhold : c'.hold = c.hold := rfl
  have hIsTok : ∀ v, (c'.node v).ph.IsTok ↔ (c.node v).ph.IsTok := by
    intro v; rw [hph]; split_ifs with hv
    · subst hv; rw [hu]; simp [Phase.IsTok]
    · rfl
  have hne : ∀ x, (c.node x).ph ≠ .idle → x ≠ u := by rintro x hx rfl; exact hx hu
  refine ⟨⟨fun v => by rw [hlog, hep, hds]; exact hC.log v,
    fun v => by rw [hep, hds]; exact hC.ep_le v, ?_, ?_, ?_,
    hC.ccwChan, hC.ccwOne, hC.ccwUniq, fun v => by
      by_cases hv : v = u <;> simp [c', hv] <;> [exact hC.posq u; exact hC.posq v], ?_⟩, ?_⟩
  · intro v; rw [hep, hds, hph]
    simp only [c', next_start_cwS, hC.cwS v]
    split_ifs with hv
    · subst hv; rw [hu]; simp [Phase.sOff]
    · simp
  · intro v; rw [hep, hds, hph]
    simp only [c', next_start_cwR, hC.cwR v]
    split_ifs with hv
    · subst hv; rw [hu]; simp [Phase.rOff]
    · rfl
  · intro v; simp only [c', next_start_cwS, next_start_cwR]
    have := hC.cwChan v; split_ifs <;> omega
  · intro v; rw [htok, hep, hds, hhold, hph, hC.tok v]
    split_ifs with hv
    · subst hv; rw [hu]; rfl
    · rfl
  · rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
    · have hT : c.hold ≠ u := hne _ (by rw [H.ph_hold]; simp)
      refine Or.inl ⟨pre, d, r, H.ds_eq, by simp only [hhold, hph, hT, ↓reduceIte]; exact H.ph_hold, H.r_lt,
        by rw [hhold, hep]; exact H.ep_hold, fun v hv => ?_, by rw [hc]; exact H.noIn⟩
      rw [hep, hIsTok]
      refine ⟨(H.others v hv).1, ?_⟩
      rcases (H.others v hv).2 with h1 | ⟨k, hk, hk'⟩
      · exact Or.inl h1
      · refine Or.inr ⟨k, ?_, hk'⟩
        simp only [hph, hne _ (by rw [hk]; simp), ↓reduceIte]; exact hk
    · have hT : c.hold ≠ u := hne _ (by rw [H.ph_hold]; simp)
      refine Or.inr (Or.inl ⟨pre, d, H.ds_eq, by simp only [hhold, hph, hT, ↓reduceIte]; exact H.ph_hold,
        by rw [hhold, hep]; exact H.ep_hold, fun v hv => ?_,
        fun v hv => by simp only [hep]; exact H.wave v hv,
        fun v hv => by simp only [hep]; exact H.target v hv, H.someIn⟩)
      rw [hep, hIsTok]
      rcases H.others v hv with ⟨h1, h2⟩ | h1
      · refine Or.inl ⟨h1, ?_⟩
        simp only [hph, hne _ (by rw [h2]; simp), ↓reduceIte]; exact h2
      · exact Or.inr h1
    · exact Or.inr (Or.inr ⟨fun v => by rw [hep]; exact H.ep_all v,
        fun v => (hIsTok v).2 (H.isTok v),
        fun h' => by rw [hc]; exact H.held (by rw [← htok]; exact h'),
        fun h' => by rw [hc]; exact H.released (by rw [← htok]; exact h')⟩)

/-! ### Reading a clockwise pulse: the common part -/

@[simp] lemma onCW_log (s : Node) : (onCW s).1.log = s.log := by
  rcases s with ⟨ph, tok, q, log⟩; cases ph <;> simp [onCW] <;> split_ifs <;> rfl

@[simp] lemma onCW_q (s : Node) : (onCW s).1.q = s.q := by
  rcases s with ⟨ph, tok, q, log⟩; cases ph <;> simp [onCW] <;> split_ifs <;> rfl

lemma onCW_sOff {s : Node} (hs : ∀ d r, s.ph = .send d r → r + 1 ≤ d) :
    s.ph.sOff + (onCW s).2.1 = (onCW s).1.ph.sOff := by
  rcases s with ⟨ph, tok, q, log⟩
  cases ph <;> simp [onCW, Phase.sOff] <;> split_ifs <;> simp [Phase.sOff]

lemma onCW_rOff {s : Node} (hr : s.ph.cwReady = true) (hs : ∀ d r, s.ph = .send d r → r + 1 ≤ d) :
    s.ph.rOff + 1 = (onCW s).1.ph.rOff := by
  rcases s with ⟨ph, tok, q, log⟩
  cases ph with
  | send d r =>
    have := hs d r rfl
    simp only [onCW]; split_ifs <;> simp [Phase.rOff] <;> omega
  | waitEnd d => simp [Phase.cwReady] at hr
  | _ => simp [onCW, Phase.rOff]

lemma onCW_ccw_le_one (s : Node) : (onCW s).2.2 ≤ 1 := by
  rcases s with ⟨ph, tok, q, log⟩
  cases ph <;> simp [onCW] <;> split_ifs <;> simp

lemma onCW_tok {s : Node} {P : Prop} (h : s.tok = true ↔ P ∧ s.ph.Holding b) :
    (onCW s).1.tok = true ↔ P ∧ (onCW s).1.ph.Holding b := by
  rcases s with ⟨ph, tok, q, log⟩
  cases ph <;> simp_all [onCW, Phase.Holding] <;> split_ifs <;> simp_all [Phase.Holding]

theorem common_cw {c : Config n} (hC : Common c) {u : ZMod n} (hen : Enabled c (.cw u))
    (hsend : ∀ d r, (c.node u).ph = .send d r → r + 1 ≤ d)
    (hno : (onCW (c.node u)).2.2 ≠ 0 → ∀ w, ¬ c.ccwIn w) : Common (next c (.cw u)) := by
  obtain ⟨hr, hin⟩ := hen
  set c' := next c (.cw u)
  have hlog : ∀ v, (c'.node v).log = (c.node v).log := by
    intro v; by_cases hv : v = u <;> simp [c', hv]
  have hep : ∀ v, c'.ep v = c.ep v := fun v => by rw [Config.ep, hlog]
  have hds : c'.ds = c.ds := rfl
  have hhold : c'.hold = c.hold := rfl
  refine ⟨fun v => by rw [hlog, hep, hds]; exact hC.log v,
    fun v => by rw [hep, hds]; exact hC.ep_le v, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; rw [hep, hds]; simp only [c', next_cw_cwS, next_cw_node, hC.cwS v]
    split_ifs with hv
    · subst hv; rw [add_assoc, onCW_sOff hsend]
    · simp
  · intro v; rw [hep, hds]; simp only [c', next_cw_cwR, next_cw_node, hC.cwR v]
    split_ifs with hv
    · subst hv; rw [add_assoc, onCW_rOff hr hsend]
    · simp
  · intro v; simp only [c', next_cw_cwS, next_cw_cwR]
    have := hC.cwChan v
    by_cases hv : v = u
    · subst hv; simp only [Config.cwIn] at hin; split_ifs <;> omega
    · split_ifs <;> omega
  · intro v; simp only [c', next_cw_ccwS, next_cw_ccwR]; have := hC.ccwChan v; split_ifs <;> omega
  · intro v; simp only [c', next_cw_ccwS, next_cw_ccwR]
    have h1 := hC.ccwOne v
    split_ifs with hv
    · by_cases h0 : (onCW (c.node u)).2.2 = 0
      · omega
      · have h2 := hno h0 v; have h3 := onCW_ccw_le_one (c.node u)
        simp only [Config.ccwIn, not_lt] at h2; rw [hv] at h2 h1 ⊢; omega
    · omega
  · intro v w hv hw
    simp only [Config.ccwIn, c', next_cw_ccwS, next_cw_ccwR] at hv hw
    by_cases h0 : (onCW (c.node u)).2.2 = 0
    · simp only [h0, ite_self, add_zero] at hv hw; exact hC.ccwUniq v w hv hw
    · have hno' := hno h0
      have h1 := onCW_ccw_le_one (c.node u)
      have e : ∀ x, c.ccwR x < c.ccwS (x + 1) + (if x + 1 = u then (onCW (c.node u)).2.2 else 0) →
          x + 1 = u := by
        intro x hx; by_contra hx'
        simp only [hx', ↓reduceIte, add_zero] at hx; exact hno' x (by simpa [Config.ccwIn] using hx)
      have := e v hv; have := e w hw
      calc v = v + 1 - 1 := by ring
        _ = w + 1 - 1 := by rw [‹v + 1 = u›, ‹w + 1 = u›]
        _ = w := by ring
  · intro v a ha; by_cases hv : v = u
    · subst hv; simp [c'] at ha; exact hC.posq _ _ ha
    · simp [c', hv] at ha; exact hC.posq _ _ ha
  · intro v; rw [hep, hds, hhold]; by_cases hv : v = u
    · subst hv; simp only [c', next_cw_node, ↓reduceIte]
      exact onCW_tok (hC.tok v)
    · simp only [c', next_cw_node, hv, ↓reduceIte]; exact hC.tok v

/-! ### Reading a clockwise pulse: the stages -/

section cwStage

variable {c : Config n} {u v w : ZMod n}

lemma cw_node_ne (hv : v ≠ u) : (next c (.cw u)).node v = c.node v := by simp [hv]

lemma cw_ep (v : ZMod n) : (next c (.cw u)).ep v = c.ep v := by
  by_cases hv : v = u <;> simp [Config.ep, hv]

lemma cw_ccwIn_of (h : c.ccwIn w) : (next c (.cw u)).ccwIn w := by
  simp only [Config.ccwIn, next_cw_ccwS, next_cw_ccwR] at h ⊢; omega

lemma cw_ccwIn_iff (h0 : (onCW (c.node u)).2.2 = 0) : (next c (.cw u)).ccwIn w ↔ c.ccwIn w := by
  simp only [Config.ccwIn, next_cw_ccwS, next_cw_ccwR, h0, ite_self, add_zero]

lemma onCW_ccw_eq_zero {s : Node} (h : s.tok = false ∨ ¬ (s.ph = .idle ∨ s.ph = .waitReq))
    (h' : ∀ d r, s.ph = .send d r → r + 1 < d) : (onCW s).2.2 = 0 := by
  rcases s with ⟨ph, tok, q, log⟩
  cases ph with
  | send d r => have := h' d r rfl; simp [onCW, this]
  | idle | waitReq => rcases h with h | h <;> simp_all [onCW]
  | _ => simp [onCW]

lemma base_ds {c : Config n} {pre : List ℕ} {d : ℕ} (h : c.ds = pre ++ [d]) :
    base c.ds (pre.length + 1) = base c.ds pre.length + d + 1 := by
  rw [h, base_succ, base_append_of_le _ le_rfl]

lemma DataStage.cwS_le (hC : Common c) {pre d r} (H : DataStage c pre d r) (v : ZMod n) :
    c.cwS v ≤ base c.ds pre.length + d + 1 := by
  rw [hC.cwS v]
  by_cases hv : v = c.hold
  · subst hv; rw [H.ep_hold, H.ph_hold]; simp [Phase.sOff]; omega
  · obtain ⟨he, hp⟩ := H.others v hv
    rw [he]
    have := H.r_lt
    rcases hp with hp | ⟨k, hk, -, hkd⟩
    · revert hp; cases (c.node v).ph <;> simp [Phase.IsTok, Phase.sOff] <;> omega
    · rw [hk]; simp [Phase.sOff]; omega

lemma DataStage.fwd_of_le (hC : Common c) {pre d r} (H : DataStage c pre d r) (hv : v ≠ c.hold)
    (h : base c.ds pre.length + d + 1 ≤ c.cwS v) : (c.node v).ph = .fwd d := by
  obtain ⟨he, hp⟩ := H.others v hv
  rw [hC.cwS v, he] at h
  have := H.r_lt
  rcases hp with hp | ⟨k, hk, -, hkd⟩
  · revert h hp; cases (c.node v).ph <;> simp [Phase.IsTok, Phase.sOff] <;> omega
  · rw [hk] at h ⊢; simp [Phase.sOff] at h; congr 1; omega

lemma DataStage.all_fwd [NeZero n] (hC : Common c) {pre d r} (H : DataStage c pre d r)
    (hlast : base c.ds pre.length + d + 1 ≤ c.cwS (c.hold - 1)) :
    ∀ v, v ≠ c.hold → (c.node v).ph = .fwd d := by
  have key : ∀ v, v = c.hold ∨ base c.ds pre.length + d + 1 ≤ c.cwS v := by
    refine ZMod.chain_ccw_all _ c.hold (fun v hv h => Or.inr ?_) (Or.inl rfl)
    rcases h with h | h
    · rw [← h, add_sub_cancel_right] at hlast; exact hlast
    · by_cases h1 : v + 1 = c.hold
      · rw [← h1, add_sub_cancel_right] at hlast; exact hlast
      · have hf := H.fwd_of_le hC h1 h
        have h2 := hC.cwChan (v + 1)
        rw [add_sub_cancel_right, hC.cwR, hf, (H.others _ h1).1] at h2
        simp only [Phase.rOff] at h2; omega
  intro v hv
  rcases key v with h | h
  · exact absurd h hv
  · exact H.fwd_of_le hC hv h

lemma EndStage.all_done [NeZero n] {pre d} (H : EndStage c pre d) (hT : c.ccwIn c.hold) :
    ∀ v, v ≠ c.hold → c.ep v = pre.length + 1 := by
  have key : ∀ v, v = c.hold ∨ c.ep v = pre.length + 1 := by
    refine ZMod.chain_cw_all _ c.hold (fun v hv h => ?_) ?_
    · rcases h with h | h
      · exact absurd h hv
      · rcases H.wave v hv h with h' | h'
        · exact Or.inl h'
        · exact Or.inr h'
    · rcases (H.target _ hT).1 with h | h
      · exact Or.inl h
      · exact Or.inr h
  intro v hv
  rcases key v with h | h
  · exact absurd h hv
  · exact h

/-- A node at line 8 reads a clockwise pulse only if its predecessor is in the data phase. -/
lemma ready_cw (hC : Common c) (hu : (c.node u).ph = .ready) (hin : c.cwIn u) :
    base c.ds (c.ep u) + 2 ≤ c.cwS (u - 1) := by
  have := hC.cwR u; rw [hu] at this; simp only [Phase.rOff] at this
  simp only [Config.cwIn] at hin; omega

theorem inv_cw [NeZero n] (h : Inv c) (hen : Enabled c (.cw u)) : Inv (next c (.cw u)) := by
  obtain ⟨hC, hS⟩ := h
  have hen' := hen
  obtain ⟨hr, hin⟩ := hen
  set c' := next c (.cw u)
  have hhold : c'.hold = c.hold := rfl
  have hds : c'.ds = c.ds := rfl
  have hnode : ∀ v, v ≠ u → c'.node v = c.node v := fun v hv => cw_node_ne hv
  have hep' : ∀ v, c'.ep v = c.ep v := fun v => cw_ep v
  have hcIn : ∀ w, c.ccwIn w → c'.ccwIn w := fun w hw => cw_ccwIn_of hw
  have hcIff : (onCW (c.node u)).2.2 = 0 → ∀ w, (c'.ccwIn w ↔ c.ccwIn w) :=
    fun h0 w => cw_ccwIn_iff h0
  rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
  · -- data stage
    have hle := H.cwS_le hC (u - 1)
    have hsend : ∀ d' r', (c.node u).ph = .send d' r' → r' + 1 ≤ d' := by
      intro d' r' hp
      have hu : u = c.hold := by
        by_contra hu
        rcases (H.others u hu).2 with h1 | ⟨k, hk, -⟩
        · rw [hp] at h1; exact h1
        · rw [hp] at hk; cases hk
      subst hu
      rw [H.ph_hold] at hp; cases hp
      have := hC.cwR c.hold; rw [H.ph_hold, H.ep_hold] at this
      simp only [Config.cwIn, Phase.rOff] at hin this; omega
    have hC' := common_cw hC hen' hsend (fun _ => H.noIn)
    refine ⟨hC', ?_⟩
    by_cases hu : u = c.hold
    · subst hu
      have hs := H.ph_hold
      have hrd := hsend d r hs
      by_cases hlt : r + 1 < d
      · have hph : (c'.node c.hold).ph = .send d (r + 1) := by
          simp [c', hs, onCW, hlt]
        have h0 : (onCW (c.node c.hold)).2.2 = 0 := by simp [onCW, hs, hlt]
        refine Or.inl ⟨pre, d, r + 1, H.ds_eq, by rw [hhold]; exact hph, hlt,
          by rw [hhold, hep']; exact H.ep_hold, fun v hv => ?_,
          fun v => by rw [hcIff h0]; exact H.noIn v⟩
        rw [hep', hnode v hv]; exact H.others v hv
      · have hrd' : r + 1 = d := by omega
        have hph : (c'.node c.hold).ph = .waitEnd d := by
          simp [c', hs, onCW, hlt]
        have hlast : base c.ds pre.length + d + 1 ≤ c.cwS (c.hold - 1) := by
          have := hC.cwR c.hold; rw [H.ph_hold, H.ep_hold] at this
          simp only [Config.cwIn, Phase.rOff] at hin this; omega
        have hall := H.all_fwd hC hlast
        have h1 : (onCW (c.node c.hold)).2.2 = 1 := by simp [onCW, hs, hlt]
        have hinT : ∀ w, c'.ccwIn w ↔ w = c.hold - 1 := by
          intro w
          simp only [Config.ccwIn, c', next_cw_ccwS, next_cw_ccwR, h1]
          have h2 := hC.ccwOne w; have h3 := H.noIn w
          simp only [Config.ccwIn, not_lt] at h3
          constructor
          · intro hw; by_contra hw'; split_ifs at hw with hh
            · exact hw' (by rw [← hh]; ring)
            · omega
          · rintro rfl
            have h4 := hC.ccwChan (c.hold - 1)
            simp only [sub_add_cancel, ↓reduceIte] at h4 ⊢; omega
        refine Or.inr (Or.inl ⟨pre, d, H.ds_eq, by rw [hhold]; exact hph,
          by rw [hhold, hep']; exact H.ep_hold, fun v hv => ?_, fun v hv hv' => ?_,
          fun v hv => ?_, ⟨c.hold - 1, (hinT _).2 rfl⟩⟩)
        · rw [hep', hnode v hv]; exact Or.inl ⟨(H.others v hv).1, hall v hv⟩
        · rw [hep', (H.others v hv).1] at hv'; omega
        · rw [hinT] at hv; subst hv
          refine ⟨Or.inl (by rw [hhold]; ring), ?_⟩
          by_cases h' : c.hold - 1 = c.hold
          · exact Or.inl h'
          · exact Or.inr (by rw [hep']; exact (H.others _ h').1)
    · obtain ⟨hep, hp⟩ := H.others u hu
      have htok : (c.node u).tok = false := by
        cases ht : (c.node u).tok
        · rfl
        · exact absurd ((hC.tok u).1 ht).1 hu
      have h0 : (onCW (c.node u)).2.2 = 0 := onCW_ccw_eq_zero (Or.inl htok) (by
        intro d' r' hp'; rcases hp with h1 | ⟨k, hk, -⟩
        · rw [hp'] at h1; exact h1.elim
        · rw [hp'] at hk; cases hk)
      refine Or.inl ⟨pre, d, r, H.ds_eq, by rw [hhold, hnode _ (Ne.symm hu)]; exact H.ph_hold,
        H.r_lt, by rw [hhold, hep']; exact H.ep_hold, fun v hv => ?_,
        fun v => by rw [hcIff h0]; exact H.noIn v⟩
      rw [hep']
      by_cases hvu : v = u
      · subst hvu
        refine ⟨hep, ?_⟩
        simp only [c', next_cw_node, ↓reduceIte]
        have hR := hC.cwR v; have hS' := hC.cwS v
        rcases hp with h1 | ⟨k, hk, hk1, hkd⟩
        · revert h1; rcases hs : c.node v with ⟨ph, tk, q, lg⟩
          cases ph <;> simp [onCW, Phase.IsTok]
          · have := H.r_lt; omega
        · rw [hk] at hR
          rcases hs : c.node v with ⟨ph, tk, q, lg⟩
          rw [hs] at hk; simp only at hk; subst hk
          simp only [onCW]
          refine Or.inr ⟨k + 1, rfl, by omega, ?_⟩
          rw [hep] at hR; simp only [Phase.rOff, Config.cwIn] at hR hin; omega
      · rw [hnode v hvu]; exact H.others v hv
  · -- end stage
    have hTe : (c.node c.hold).ph = .waitEnd d := H.ph_hold
    have hu : u ≠ c.hold := by rintro rfl; rw [hTe] at hr; simp [Phase.cwReady] at hr
    have htok : (c.node u).tok = false := by
      cases ht : (c.node u).tok
      · rfl
      · exact absurd ((hC.tok u).1 ht).1 hu
    have hnotsend : ∀ d' r', (c.node u).ph ≠ .send d' r' := by
      intro d' r' hp; rcases H.others u hu with ⟨-, h2⟩ | ⟨-, h2⟩
      · rw [hp] at h2; cases h2
      · rw [hp] at h2; exact h2
    have h0 : (onCW (c.node u)).2.2 = 0 :=
      onCW_ccw_eq_zero (Or.inl htok) (fun d' r' hp => absurd hp (hnotsend d' r'))
    have hC' := common_cw hC hen' (fun d' r' hp => absurd hp (hnotsend d' r'))
      (fun h => absurd h0 h)
    refine ⟨hC', ?_⟩
    have hbase := base_ds H.ds_eq
    -- the predecessor's clockwise count
    have hpred : c.cwS (u - 1) ≤ base c.ds (pre.length + 1) + (if c.ep (u - 1) = pre.length + 1
        then 1 else 0) := by
      rw [hC.cwS]
      by_cases h1 : u - 1 = c.hold
      · rw [h1, H.ep_hold, hTe]; simp [Phase.sOff]; omega
      · rcases H.others _ h1 with ⟨he, hp⟩ | ⟨he, hp⟩
        · rw [he, hp]; simp [Phase.sOff]; omega
        · rw [he]; simp only [↓reduceIte]
          revert hp; cases (c.node (u - 1)).ph <;> simp [Phase.IsTok, Phase.sOff]
    rcases H.others u hu with ⟨he, hp⟩ | ⟨he, hp⟩
    · -- `u` has not completed the epoch: it cannot read a clockwise pulse
      exfalso
      have hR := hC.cwR u; rw [he, hp] at hR; simp only [Phase.rOff, Config.cwIn] at hR hin
      by_cases h1 : c.ep (u - 1) = pre.length + 1
      · have h2 : u - 1 ≠ c.hold := by
          intro h2; rw [h2, H.ep_hold] at h1; omega
        rcases H.wave _ h2 h1 with h3 | h3
        · exact hu (by rw [← h3]; ring)
        · rw [sub_add_cancel, he] at h3; omega
      · simp only [h1, ↓reduceIte] at hpred; omega
    · have hp' : (c.node u).ph = .idle ∨ (c.node u).ph = .waitReq := by
        revert hp; rcases hs : (c.node u).ph <;> simp [Phase.IsTok]
        have hR := hC.cwR u; rw [he, hs] at hR; simp only [Phase.rOff, Config.cwIn] at hR hin
        split_ifs at hpred <;> omega
      have hph : (c'.node u).ph = .ready := by
        simp only [c', next_cw_node, ↓reduceIte]
        rcases hp' with h1 | h1 <;> simp [onCW, h1]
      refine Or.inr (Or.inl ⟨pre, d, H.ds_eq, by rw [hhold, hnode _ (Ne.symm hu)]; exact hTe,
        by rw [hhold, hep']; exact H.ep_hold, fun v hv => ?_, fun v hv hv' => ?_,
        fun v hv => ?_, ?_⟩)
      · rw [hep']
        by_cases hvu : v = u
        · subst hvu; exact Or.inr ⟨he, by rw [hph]; trivial⟩
        · rw [hnode v hvu]; exact H.others v hv
      · simp only [hep'] at hv' ⊢; exact H.wave v hv hv'
      · rw [hcIff h0] at hv; simp only [hep']; exact H.target v hv
      · obtain ⟨w, hw⟩ := H.someIn; exact ⟨w, hcIn _ hw⟩
  · -- token stage
    have hnotsend : ∀ d' r', (c.node u).ph ≠ .send d' r' := by
      intro d' r' hp; have := H.isTok u; rw [hp] at this; exact this
    have hno : (onCW (c.node u)).2.2 ≠ 0 → ∀ w, ¬ c.ccwIn w := by
      intro h1
      have ht : (c.node u).tok = true := by
        by_contra ht; simp only [Bool.not_eq_true] at ht
        exact h1 (onCW_ccw_eq_zero (Or.inl ht) (fun d' r' hp => absurd hp (hnotsend d' r')))
      have := ((hC.tok u).1 ht).1; subst this; exact H.held ht
    refine ⟨common_cw hC hen' (fun d' r' hp => absurd hp (hnotsend d' r')) hno, ?_⟩
    have hp' : (c.node u).ph = .idle ∨ (c.node u).ph = .waitReq := by
      have := H.isTok u
      revert this; rcases hs : (c.node u).ph <;> simp [Phase.IsTok]
      have := ready_cw hC hs hin
      have h2 := hC.cwS (u - 1); rw [H.ep_all] at h2; rw [H.ep_all] at this
      have h3 := H.isTok (u - 1)
      revert h2 h3; cases (c.node (u - 1)).ph <;> simp [Phase.IsTok, Phase.sOff] <;> omega
    have hph : (c'.node u).ph = .ready := by
      simp only [c', next_cw_node, ↓reduceIte]
      rcases hp' with h1 | h1 <;> simp [onCW, h1]
    refine Or.inr (Or.inr ⟨fun v => by rw [hep']; exact H.ep_all v, fun v => ?_, fun ht => ?_,
      fun ht => ?_⟩)
    · by_cases hvu : v = u
      · subst hvu; rw [hph]; trivial
      · rw [hnode v hvu]; exact H.isTok v
    · rw [hhold] at ht
      have hu : c.hold ≠ u := by
        rintro hu; rw [hu] at ht; simp only [c', next_cw_node, ↓reduceIte] at ht
        rcases hp' with h1 | h1 <;> simp [onCW, h1] at ht
      rw [hnode _ hu] at ht
      have htu : (c.node u).tok = false := by
        cases h' : (c.node u).tok
        · rfl
        · exact absurd ((hC.tok u).1 h').1.symm hu
      intro w; rw [cw_ccwIn_iff (onCW_ccw_eq_zero (Or.inl htu)
        (fun d' r' hp => absurd hp (hnotsend d' r')))]; exact H.held ht w
    · rw [hhold] at ht
      by_cases hu : c.hold = u
      · subst hu
        cases h' : (c.node c.hold).tok
        · obtain ⟨w, hw⟩ := H.released h'; exact ⟨w, hcIn _ hw⟩
        · refine ⟨c.hold - 1, ?_⟩
          simp only [Config.ccwIn, c', next_cw_ccwS, next_cw_ccwR, sub_add_cancel, ↓reduceIte]
          have : (onCW (c.node c.hold)).2.2 = 1 := by rcases hp' with h1 | h1 <;> simp [onCW, h1, h']
          have h4 := hC.ccwChan (c.hold - 1)
          simp only [sub_add_cancel] at h4; omega
      · rw [hnode _ hu] at ht
        obtain ⟨w, hw⟩ := H.released ht; exact ⟨w, hcIn _ hw⟩

end cwStage

/-! ### Reading a counterclockwise pulse -/

section ccwStep

variable {c : Config n} {u v w : ZMod n}

lemma onCCW_ccw_le_one (s : Node) : (onCCW s).2.2 ≤ 1 := by
  rcases s with ⟨ph, tok, q, log⟩
  cases ph <;> simp [onCCW]; split <;> simp

lemma ccw_node_ne (hv : v ≠ u) : (next c (.ccw u)).node v = c.node v := by simp [hv]

/-- After reading the (unique) counterclockwise pulse in transit, the only possible pulse in
transit is the one just sent to `u - 1`. -/
lemma ccw_in_imp (hC : Common c) (hin : c.ccwIn u) (h : (next c (.ccw u)).ccwIn w) : w + 1 = u := by
  by_contra hw
  simp only [Config.ccwIn, next_ccw_ccwS, next_ccw_ccwR, hw, ↓reduceIte, add_zero] at h
  by_cases hwu : w = u
  · subst hwu; simp only [↓reduceIte] at h; have := hC.ccwOne w; omega
  · simp only [hwu, ↓reduceIte, add_zero] at h; exact hwu (hC.ccwUniq w u h hin)

lemma ccw_none (hC : Common c) (hin : c.ccwIn u) (h0 : (onCCW (c.node u)).2.2 = 0) :
    ∀ w, ¬ (next c (.ccw u)).ccwIn w := by
  intro w h
  have hw := ccw_in_imp hC hin h
  have h1 := hC.ccwOne w
  simp only [Config.ccwIn, next_ccw_ccwS, next_ccw_ccwR] at h
  rw [hw] at h h1
  simp only [↓reduceIte, h0, add_zero] at h
  by_cases hwu : w = u
  · subst hwu; simp only [↓reduceIte] at h; omega
  · simp only [hwu, ↓reduceIte, add_zero] at h
    exact hwu (hC.ccwUniq w u (by simp only [Config.ccwIn, hw]; exact h) hin)

lemma ccw_send_in (hC : Common c) (hin : c.ccwIn u) (h1 : (onCCW (c.node u)).2.2 = 1) :
    (next c (.ccw u)).ccwIn (u - 1) := by
  simp only [Config.ccwIn, next_ccw_ccwS, next_ccw_ccwR, sub_add_cancel, ↓reduceIte, h1]
  have := hC.ccwChan (u - 1); rw [sub_add_cancel] at this
  simp only [Config.ccwIn] at hin
  split_ifs with h
  · have hu1 : u + 1 = u := by
      calc u + 1 = (u - 1) + 1 := by rw [h]
        _ = u := by ring
    rw [hu1] at hin; rw [h]; omega
  · omega

/-- The channel clauses of `Common` after reading a counterclockwise pulse. -/
lemma ccw_chan (hC : Common c) (hin : c.ccwIn u) :
    (∀ v, (next c (.ccw u)).cwR v ≤ (next c (.ccw u)).cwS (v - 1)) ∧
    (∀ v, (next c (.ccw u)).ccwR v ≤ (next c (.ccw u)).ccwS (v + 1)) ∧
    (∀ v, (next c (.ccw u)).ccwS (v + 1) ≤ (next c (.ccw u)).ccwR v + 1) ∧
    (∀ v w, (next c (.ccw u)).ccwIn v → (next c (.ccw u)).ccwIn w → v = w) := by
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v w hv hw => ?_⟩
  · simp only [next_ccw_cwS, next_ccw_cwR]; have := hC.cwChan v; omega
  · simp only [next_ccw_ccwS, next_ccw_ccwR]; have := hC.ccwChan v
    simp only [Config.ccwIn] at hin
    by_cases hv : v = u
    · subst hv; simp only [↓reduceIte]; split_ifs <;> omega
    · simp only [hv, ↓reduceIte]; omega
  · simp only [next_ccw_ccwS, next_ccw_ccwR]
    have h1 := hC.ccwOne v; have h2 := onCCW_ccw_le_one (c.node u)
    by_cases hv1 : v + 1 = u
    · simp only [hv1, ↓reduceIte] at h1 ⊢
      by_cases hvu : v = u
      · subst hvu; simp only [↓reduceIte]; omega
      · simp only [hvu, ↓reduceIte, add_zero]
        have := hC.ccwUniq v u
        have h3 : ¬ c.ccwIn v := fun h => hvu (this h hin)
        simp only [Config.ccwIn, hv1, not_lt] at h3; omega
    · simp only [hv1, ↓reduceIte, add_zero]; split_ifs <;> omega
  · have h1 := ccw_in_imp hC hin hv; have h2 := ccw_in_imp hC hin hw
    calc v = v + 1 - 1 := by ring
      _ = w + 1 - 1 := by rw [h1, h2]
      _ = w := by ring

lemma ZMod.eq_of_add_one_eq_self {u : ZMod n} (h : u + 1 = u) (x y : ZMod n) : x = y := by
  have h1 : (1 : ZMod n) = 0 := by
    calc (1 : ZMod n) = u + 1 - u := by ring
      _ = 0 := by rw [h]; ring
  calc x = x * 1 := by ring
    _ = y * 1 := by rw [h1]; ring
    _ = y := by ring

theorem inv_ccw [NeZero n] (h : Inv c) (hen : Enabled c (.ccw u)) : Inv (next c (.ccw u)) := by
  obtain ⟨hC, hS⟩ := h
  obtain ⟨hr, hin⟩ := hen
  obtain ⟨hch1, hch2, hch3, hch4⟩ := ccw_chan hC hin
  set c' := next c (.ccw u)
  have hnode : ∀ v, v ≠ u → c'.node v = c.node v := fun v hv => ccw_node_ne hv
  rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
  · exact absurd hin (H.noIn u)
  · -- end stage: an `end` pulse
    obtain ⟨ht1, ht2⟩ := H.target u hin
    have hbase := base_ds H.ds_eq
    have hlen : c.ds.length = pre.length + 1 := by rw [H.ds_eq]; simp
    have hph : (c.node u).ph = .waitEnd d ∨ (c.node u).ph = .fwd d := by
      by_cases hu : u = c.hold
      · subst hu; exact Or.inl H.ph_hold
      · rcases ht2 with h2 | h2
        · exact absurd h2 hu
        · rcases H.others u hu with ⟨-, h3⟩ | ⟨h3, -⟩
          · exact Or.inr h3
          · omega
    have hcap : capture? (c.node u) = none := by
      unfold capture?; rcases hph with h1 | h1 <;> rw [h1]
    have hds : c'.ds = c.ds := by simp only [c', next_ccw_ds, hcap]
    have hhold : c'.hold = c.hold := by simp only [c', next_ccw_hold, hcap]
    have hepu : c.ep u = pre.length := by
      rcases ht2 with h2 | h2
      · rw [h2]; exact H.ep_hold
      · exact h2
    have hlogu : (c.node u).log ++ [d] = c.ds := by
      rw [hC.log u, hepu, H.ds_eq]; simp
    have hnu : c'.node u = ⟨.idle, (c.node u).tok, (c.node u).q, (c.node u).log ++ [d]⟩ := by
      simp only [c', next_ccw_node, ↓reduceIte]
      rcases hph with h1 | h1 <;> simp [onCCW, h1]
    have hepu' : c'.ep u = pre.length + 1 := by simp [Config.ep, hnu, hepu]
    have hep : ∀ v, v ≠ u → c'.ep v = c.ep v := fun v hv => by simp [Config.ep, hnode v hv]
    have hcwS : c'.cwS u = c.cwS u := by
      simp only [c', next_ccw_cwS, ↓reduceIte]; rcases hph with h1 | h1 <;> simp [onCCW, h1]
    have hcwSu : c.cwS u = base c.ds (pre.length + 1) := by
      rw [hC.cwS, hepu, hbase]; rcases hph with h1 | h1 <;> rw [h1] <;> simp [Phase.sOff] <;> ring
    have hcwRu : c.cwR u = base c.ds (pre.length + 1) := by
      rw [hC.cwR, hepu, hbase]; rcases hph with h1 | h1 <;> rw [h1] <;> simp [Phase.rOff] <;> ring
    have hcomm : Common c' := by
      refine ⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, hch1, hch2, hch3, hch4,
        fun v a ha => ?_, fun v => ?_⟩
      · by_cases hv : v = u
        · subst hv; rw [hds, hepu', hnu, ← hlen, List.take_length]; exact hlogu
        · rw [hnode v hv, hds, hep v hv]; exact hC.log v
      · by_cases hv : v = u
        · subst hv; rw [hds, hepu', hlen]
        · rw [hds, hep v hv]; exact hC.ep_le v
      · by_cases hv : v = u
        · subst hv; rw [hcwS, hds, hepu', hnu, hcwSu]; simp [Phase.sOff]
        · simp only [c', next_ccw_cwS, hv, ↓reduceIte, add_zero]
          rw [hds, hep v hv, hnode v hv]; exact hC.cwS v
      · by_cases hv : v = u
        · subst hv; simp only [c', next_ccw_cwR]; rw [hds, hepu', hnu, hcwRu]; simp [Phase.rOff]
        · simp only [c', next_ccw_cwR]; rw [hds, hep v hv, hnode v hv]; exact hC.cwR v
      · by_cases hv : v = u
        · subst hv; rw [hnu] at ha; exact hC.posq _ _ ha
        · rw [hnode v hv] at ha; exact hC.posq _ _ ha
      · rw [hds, hhold]
        by_cases hv : v = u
        · subst hv; rw [hnu, hepu', hlen]; simp only
          rw [hC.tok v]
          rcases hph with h1 | h1 <;> rw [h1] <;> simp [Phase.Holding]
          intro h2; rw [h2, H.ph_hold] at h1; cases h1
        · rw [hnode v hv, hep v hv]; exact hC.tok v
    refine ⟨hcomm, ?_⟩
    by_cases hu : u = c.hold
    · -- the `end` pulse is back at the holder: token stage
      have hphu : (c.node u).ph = .waitEnd d := by rw [hu]; exact H.ph_hold
      have hall : ∀ v, v ≠ u → c.ep v = pre.length + 1 := by
        rw [hu]; exact H.all_done (by rw [← hu]; exact hin)
      have h0 : (onCCW (c.node u)).2.2 = 0 := by simp [onCCW, hphu]
      refine Or.inr (Or.inr ⟨fun v => ?_, fun v => ?_, fun _ => ccw_none hC hin h0, fun ht => ?_⟩)
      · rw [hds, hlen]; by_cases hv : v = u
        · subst hv; exact hepu'
        · rw [hep v hv]; exact hall v hv
      · by_cases hv : v = u
        · subst hv; rw [hnu]; trivial
        · rw [hnode v hv]
          rcases H.others v (by rw [← hu]; exact hv) with ⟨h1, -⟩ | ⟨-, h1⟩
          · have := hall v hv; omega
          · exact h1
      · exfalso; rw [hhold, ← hu, hnu] at ht; simp only at ht
        have := (hC.tok u).2 ⟨hu, by rw [hphu]; trivial⟩
        rw [this] at ht; cases ht
    · -- a non-holder forwards the `end` pulse
      have h1 : (onCCW (c.node u)).2.2 = 1 := by
        rcases hph with h1 | h1
        · exfalso; rcases H.others u hu with ⟨-, h2⟩ | ⟨-, h2⟩
          · rw [h1] at h2; cases h2
          · rw [h1] at h2; exact h2
        · simp [onCCW, h1]
      refine Or.inr (Or.inl ⟨pre, d, by rw [hds]; exact H.ds_eq, ?_, ?_, fun v hv => ?_, fun v hv hv' => ?_,
        fun w hw => ?_, ⟨u - 1, ccw_send_in hC hin h1⟩⟩)
      · rw [hhold, hnode _ (Ne.symm hu)]; exact H.ph_hold
      · rw [hhold, hep _ (Ne.symm hu)]; exact H.ep_hold
      · rw [hhold] at hv
        by_cases hvu : v = u
        · subst hvu; exact Or.inr ⟨hepu', by rw [hnu]; trivial⟩
        · rw [hep v hvu, hnode v hvu]; exact H.others v hv
      · rw [hhold] at hv ⊢
        have key : ∀ x, c.ep x = pre.length + 1 → c'.ep x = pre.length + 1 := by
          intro x hx; by_cases hxu : x = u
          · subst hxu; exact hepu'
          · rw [hep x hxu]; exact hx
        by_cases hvu : v = u
        · subst hvu
          rcases ht1 with h2 | h2
          · exact Or.inl h2
          · exact Or.inr (key _ h2)
        · rw [hep v hvu] at hv'
          rcases H.wave v hv hv' with h2 | h2
          · exact Or.inl h2
          · by_cases hvu' : v + 1 = u
            · rw [hvu']; exact Or.inr hepu'
            · exact Or.inr (key _ h2)
      · have hw1 := ccw_in_imp hC hin hw
        rw [hhold, hw1]
        refine ⟨Or.inr hepu', ?_⟩
        by_cases hwT : w = c.hold
        · exact Or.inl hwT
        · right
          by_cases hwu : w = u
          · exfalso; subst hwu; exact hu (ZMod.eq_of_add_one_eq_self hw1 _ _)
          · rw [hep w hwu]
            rcases H.others w hwT with ⟨h2, -⟩ | ⟨h2, -⟩
            · exact h2
            · rcases H.wave w hwT h2 with h3 | h3
              · exact absurd (hw1.symm.trans h3) hu
              · rw [hw1, hepu] at h3; omega
  · -- token stage: a `token` pulse
    have hph : (c.node u).ph = .ready := by
      have := H.isTok u; revert hr this
      cases (c.node u).ph <;> simp [Phase.IsTok, Phase.ccwReady]
    have htokH : (c.node c.hold).tok = false := by
      cases h' : (c.node c.hold).tok
      · rfl
      · exact absurd hin (H.held h' u)
    have htokf : ∀ v, (c.node v).tok = false := by
      intro v; cases h' : (c.node v).tok
      · rfl
      · have := ((hC.tok v).1 h').1; subst this; rw [htokH] at h'; cases h'
    cases hq : (c.node u).q with
    | nil =>
      -- forward the token
      have ho : onCCW (c.node u) = (c.node u, 0, 1) := by simp [onCCW, hph, hq]
      have hcap : capture? (c.node u) = none := by unfold capture?; rw [hph, hq]
      have hnd : ∀ v, c'.node v = c.node v := by
        intro v; by_cases hv : v = u
        · subst hv; simp [c', ho]
        · exact hnode v hv
      have hep : ∀ v, c'.ep v = c.ep v := fun v => by simp [Config.ep, hnd]
      have hds : c'.ds = c.ds := by simp only [c', next_ccw_ds, hcap]
      have hhold : c'.hold = c.hold := by simp only [c', next_ccw_hold, hcap]
      have hcwS' : ∀ v, c'.cwS v = c.cwS v := fun v => by simp [c', ho]
      have hcwR' : ∀ v, c'.cwR v = c.cwR v := fun v => rfl
      refine ⟨⟨fun v => by rw [hnd, hep, hds]; exact hC.log v,
        fun v => by rw [hep, hds]; exact hC.ep_le v,
        fun v => by rw [hcwS', hds, hep, hnd]; exact hC.cwS v,
        fun v => by rw [hcwR', hds, hep, hnd]; exact hC.cwR v,
        hch1, hch2, hch3, hch4, fun v => by rw [hnd]; exact hC.posq v,
        fun v => by rw [hnd, hep, hds, hhold]; exact hC.tok v⟩,
        Or.inr (Or.inr ⟨fun v => by rw [hep, hds]; exact H.ep_all v,
          fun v => by rw [hnd]; exact H.isTok v, fun ht => ?_,
          fun _ => ⟨u - 1, ccw_send_in hC hin (by rw [ho])⟩⟩)⟩
      rw [hhold, hnd, htokH] at ht; cases ht
    | cons a q' =>
      -- take the token
      have ho : onCCW (c.node u) = (⟨.send a 0, true, q', (c.node u).log⟩, a, 0) := by
        simp [onCCW, hph, hq]
      have hcap : capture? (c.node u) = some a := by unfold capture?; rw [hph, hq]
      have hnu : c'.node u = ⟨.send a 0, true, q', (c.node u).log⟩ := by simp [c', ho]
      have hep : ∀ v, c'.ep v = c.ep v := fun v => by
        by_cases hv : v = u
        · subst hv; simp [Config.ep, hnu]
        · simp [Config.ep, hnode v hv]
      have hds : c'.ds = c.ds ++ [a] := by simp only [c', next_ccw_ds, hcap]
      have hhold : c'.hold = u := by simp only [c', next_ccw_hold, hcap]
      have ha : 0 < a := hC.posq u a (by rw [hq]; simp)
      have hbase : ∀ v, base c'.ds (c'.ep v) = base c.ds (c.ep v) := fun v => by
        rw [hds, hep, base_append_of_le _ (hC.ep_le v)]
      have h0 : (onCCW (c.node u)).2.2 = 0 := by rw [ho]
      refine ⟨⟨fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_, hch1, hch2, hch3, hch4,
        fun v b hb => ?_, fun v => ?_⟩, Or.inl ⟨c.ds, a, 0, hds, by rw [hhold, hnu], ha,
          by rw [hhold, hep]; exact H.ep_all u, fun v hv => ?_, ccw_none hC hin h0⟩⟩
      · have : (c'.node v).log = (c.node v).log := by
          by_cases hv : v = u
          · subst hv; rw [hnu]
          · rw [hnode v hv]
        rw [this, hep, hds, H.ep_all, List.take_append_of_le_length le_rfl, ← H.ep_all v]
        exact hC.log v
      · rw [hep, hds]; have := hC.ep_le v; simp; omega
      · rw [hbase]; by_cases hv : v = u
        · subst hv; simp only [c', next_ccw_cwS, ↓reduceIte, ho]; rw [hnu, hC.cwS, hph]
          simp [Phase.sOff]; ring
        · simp only [c', next_ccw_cwS, hv, ↓reduceIte, add_zero]; rw [hnode v hv]; exact hC.cwS v
      · rw [hbase]; by_cases hv : v = u
        · subst hv; simp only [c', next_ccw_cwR, ↓reduceIte]; rw [hnu, hC.cwR, hph]
          simp [Phase.rOff]
        · simp only [c', next_ccw_cwR, hv, ↓reduceIte, add_zero]; rw [hnode v hv]; exact hC.cwR v
      · by_cases hv : v = u
        · subst hv; rw [hnu] at hb; exact hC.posq v b (by rw [hq]; exact List.mem_cons_of_mem _ hb)
        · rw [hnode v hv] at hb; exact hC.posq v b hb
      · rw [hhold]; by_cases hv : v = u
        · subst hv; rw [hnu]; simp [Phase.Holding]
        · rw [hnode v hv, htokf v]; simp [hv]
      · rw [hhold] at hv; rw [hep, hnode v hv]; exact ⟨H.ep_all v, Or.inl (H.isTok v)⟩

end ccwStep

end Podc.FullyDefective.Cycle

namespace Podc.FullyDefective.Cycle

variable {n : ℕ} [NeZero n] {c : Config n}

theorem inv_step (h : Inv c) {l : Label n} (hen : Enabled c l) : Inv (next c l) := by
  cases l with
  | push u a => exact inv_push h u hen
  | start u => exact inv_start h hen.1
  | cw u => exact inv_cw h hen
  | ccw u => exact inv_ccw h hen

/-- The invariant holds in every reachable configuration. -/
theorem Reach.inv {T₀ : ZMod n} {qs : ZMod n → List ℕ} (hqs : ∀ u, ∀ a ∈ qs u, 0 < a)
    (h : Reach T₀ qs c) : Inv c := by
  induction h with
  | refl => exact inv_init T₀ hqs
  | tail _ hs ih => obtain ⟨l, hen, rfl⟩ := hs; exact inv_step ih hen

/-- Every node has completed all started epochs but possibly the last one. -/
lemma Inv.ep_ge (h : Inv c) (u : ZMod n) : c.ds.length ≤ c.ep u + 1 := by
  obtain ⟨hC, hS⟩ := h
  rcases hS with ⟨pre, d, r, H⟩ | ⟨pre, d, H⟩ | H
  · rw [H.ds_eq]; simp
    by_cases hu : u = c.hold
    · rw [hu, H.ep_hold]
    · rw [(H.others u hu).1]
  · rw [H.ds_eq]; simp
    by_cases hu : u = c.hold
    · rw [hu, H.ep_hold]
    · rcases H.others u hu with ⟨h1, -⟩ | ⟨h1, -⟩ <;> omega
  · rw [H.ep_all u]; omega

/-- **Lemma 5(2), single token holder.** At most one node has `isTokenHolder = True`. -/
theorem Inv.tok_unique (h : Inv c) {u v : ZMod n} (hu : (c.node u).tok = true)
    (hv : (c.node v).tok = true) : u = v :=
  ((h.1.tok u).1 hu).1.trans ((h.1.tok v).1 hv).1.symm

/-- **Lemma 5(3), global consistency.** Every node has decoded exactly the payloads of the
epochs it completed: its log is a prefix of the global sequence of payloads. -/
theorem Inv.log_prefix (h : Inv c) (u : ZMod n) : (c.node u).log <+: c.ds := by
  rw [h.1.log u]; exact List.take_prefix _ _

end Podc.FullyDefective.Cycle
