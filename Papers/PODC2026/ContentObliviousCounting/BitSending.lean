import Cslib.Computability.Distributed.ContentOblivious.Mirror
import Mathlib
import Cslib.Computability.Distributed.ContentOblivious.VirtualRing
import Cslib.Foundations.Algebra.BigOperators.Translate

/-!
# Algorithms 7–8 (`CCWBitSending` / `CCWBitRelay`) and Theorem 17

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260), §6.1: Algorithm 7 `CCWBitSending(bit)`, Algorithm 8
`CCWBitRelay()`, Lemmas 15–16, Theorem 17; and their mirror images `CWBitSending` /
`CWBitRelay` ("symmetric, omitted" in the paper).

**Model.** Oriented ring `ZMod n` (`n ≥ 1`; `Port1 = true` is the clockwise port), asynchronous
content-oblivious pulses, adversarial scheduler (`Cslib.ContentOblivious.Step`), no failures,
deterministic nodes, exactly one leader, at least one active node. The input of a node is
`(isLeader, isActive, bit)`; active nodes run `CCWBitSending(bit)` (`bit : Option Bool`,
`none` = ⊥), the other nodes (relays) run `CCWBitRelay()`. Both are one procedure `proc`.

**Encoding of the pseudo-code.** States `loop` (Alg. 7, while loop, lines 12–18), `wait`
(Alg. 7 after line 19: the leader waits on port 0 only, line 21; a non-leader runs the repeat loop
of lines 23–30 and reads any port), `relay` (Alg. 8, loop of lines 4–11, any port) and `ret`
(returned, with the result: the decoded bit for an active node, `none` for a relay). Each
reception executes the code up to the next receive.

**Proof method** (all interleavings). For each node `v` let `P v = r₀ - s₀` and `Q v = s₁ - r₁`
(pulses received/sent on `Port0`/`Port1`). The link from `v` to `v + 1` carries
`Q v - P (v + 1) ≥ 0` pulses, and every node relates `Q` to `P` (a non-leader forwards the
"wave" pulses: `Q = max P 0` or `Q = P`; the leader injects one). Everything follows by
propagating inequalities around the ring, plus one inductive invariant: once the leader has
received the synchronization pulse back (`P ℓ ≥ 1`), every bit pulse has been received
(`ccwQuiet`). These are the key facts of the paper's proof of Lemma 15 (acknowledgements +
"sync" pulse), made precise for relays (Lemma 16) without collapsing relay segments.
-/

namespace Podc.ContentOblivious.BitSending

open Cslib.ContentOblivious Finset

/-- Number of pulses encoding a bit: `κ(⊥) = 0`, `κ(0) = 1`, `κ(1) = 2`. -/
def κ : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

/-- Lines 31–36 of Algorithm 7. -/
def decodeBit : ℕ → Option Bool
  | 1 => some false
  | 2 => some true
  | _ => none

@[simp] lemma decodeBit_κ (b : Option Bool) : decodeBit (κ b) = b := by
  rcases b with _ | _ | _ <;> rfl

lemma κ_le (b : Option Bool) : κ b ≤ 2 := by rcases b with _ | _ | _ <;> decide

/-- Local states of Algorithms 7 and 8. -/
inductive St
  /-- Algorithm 7, while loop (lines 12–18), with the variables `cnt` and `in`. -/
  | loop (ldr : Bool) (cnt : ℤ) (inn : ℕ)
  /-- Algorithm 7 after line 19 (line 21 for the leader, lines 23–30 otherwise). -/
  | wait (ldr : Bool) (inn : ℕ)
  /-- Algorithm 8, loop of lines 4–11, with the variable `cnt`. -/
  | relay (ldr : Bool) (cnt : ℤ)
  /-- Returned (with the returned value). -/
  | ret (r : Option Bool)

/-- Start-up: lines 1–11 of Algorithm 7, lines 1–3 of Algorithm 8. -/
def init : Bool × Bool × Option Bool → St × (Bool → ℕ)
  | (ldr, true, bit) => (.loop ldr (κ bit) 0, fun p => if p then (if ldr then 1 else 0) else κ bit)
  | (ldr, false, _) => (.relay ldr 0, fun p => if p && ldr then 1 else 0)

/-- Reception of a pulse on port `q`, and the code executed up to the next receive. -/
def recv : St → Bool → St × (Bool → ℕ)
  | .loop ldr cnt inn, false => -- lines 14–15, then loop test (line 12) and line 19
    if cnt - 1 < 0 then (.wait ldr inn, onePulse true) else (.loop ldr (cnt - 1) inn, fun _ => 0)
  | .loop ldr cnt inn, true => (.loop ldr cnt (inn + 1), onePulse true) -- lines 16–18
  | .wait ldr inn, false => -- line 21 (leader), lines 28–30 (non-leader)
    (.ret (decodeBit inn), if ldr then fun _ => 0 else onePulse true)
  | .wait ldr inn, true => (.wait ldr (inn + 1), onePulse true) -- lines 25–27
  | .relay ldr cnt, q => -- lines 5–11
    let cnt' := if q then cnt + 1 else cnt - 1
    (if cnt' < -1 then .ret none else .relay ldr cnt',
      if ldr && !q && decide (cnt = -1) then fun _ => 0 else onePulse (!q))
  | .ret r, _ => (.ret r, fun _ => 0)

/-- The ports on which a node waits: only port 0 for the leader at line 21; none once returned. -/
def ready : St → Bool → Bool
  | .wait true _, j => !j
  | .ret _, _ => false
  | _, _ => true

/-- The returned value. -/
def result : St → Option (Option Bool)
  | .ret r => some r
  | _ => none

/-- **Algorithms 7 and 8** (`CCWBitSending` for active nodes, `CCWBitRelay` for relays) as one
procedure with input `(isLeader, isActive, bit)`. Relays return `none`. -/
abbrev proc : Proc (Bool × Bool × Option Bool) (Option Bool) where
  State := St
  init := init
  recv := recv
  ready := ready
  terminated s := (result s).isSome
  result := result
  terminated_eq _ := rfl

/-- **`CWBitSending` / `CWBitRelay`**: the mirror images of Algorithms 7 and 8 (ports swapped),
"symmetric, omitted" in the paper. An active node sends its bit clockwise and receives the bit
of the next active node counter-clockwise. -/
abbrev cwProc : Proc (Bool × Bool × Option Bool) (Option Bool) := proc.mirror

/-! ## Local invariant -/

/-- Relation between the input `a`, the state `s` and the ghost counters of a node (`r p`: pulses
received on port `p`, `snt p`: pulses sent on port `p`). -/
def Rel (a : Bool × Bool × Option Bool) (s : St) (r snt : Bool → ℕ) : Prop :=
  match a.2.1, s with
  | true, .loop L cnt inn => L = a.1 ∧ 0 ≤ cnt ∧ cnt ≤ κ a.2.2 ∧
      (r false : ℤ) = κ a.2.2 - cnt ∧ r true = inn ∧ snt false = κ a.2.2 ∧
      snt true = (if a.1 then 1 else 0) + inn
  | true, .wait L inn => L = a.1 ∧ r false = κ a.2.2 + 1 ∧ r true = inn ∧
      snt false = κ a.2.2 ∧ snt true = (if a.1 then 1 else 0) + inn + 1
  | true, .ret res => res = decodeBit (r true) ∧ r false = κ a.2.2 + 2 ∧
      snt false = κ a.2.2 ∧ snt true = r true + 2
  | false, .relay L cnt => L = a.1 ∧ cnt = (r true : ℤ) - r false ∧ -1 ≤ cnt ∧
      snt false = r true ∧ snt true = r false + (if a.1 then 1 else 0)
  | false, .ret res => res = none ∧ r false = r true + 2 ∧ snt false = r true ∧
      snt true = r false
  | _, _ => False

lemma rel_init (a : Bool × Bool × Option Bool) : Rel a (init a).1 (fun _ => 0) (init a).2 := by
  obtain ⟨L, act, bit⟩ := a
  cases act <;> cases L <;> simp [Rel, init]

lemma rel_step (a : Bool × Bool × Option Bool) (s : St) (r snt : Bool → ℕ) (j : Bool)
    (h : Rel a s r snt) (hrd : ready s j = true) :
    Rel a (recv s j).1 (fun p => r p + if p = j then 1 else 0)
      (fun p => snt p + (recv s j).2 p) := by
  obtain ⟨L, act, bit⟩ := a
  cases act <;> cases s <;> simp only [Rel] at h
  · -- relay
    rename_i L' cnt
    obtain ⟨rfl, rfl, hc1, h0, h1⟩ := h
    cases j
    · by_cases hm : (r true : ℤ) - r false = -1
      · have hr : r false = r true + 1 := by omega
        cases L' <;> simp [recv, Rel, onePulse, h0, h1, hr]
      · have hm' : ¬ ((r true : ℤ) - r false - 1 < -1) := by omega
        cases L' <;> simp [recv, Rel, onePulse, hm, hm', h0, h1] <;> omega
    · have hm' : ¬ ((r true : ℤ) - r false + 1 < -1) := by omega
      cases L' <;> simp [recv, Rel, onePulse, hm', h0, h1] <;> omega
  · simp [ready] at hrd
  · -- loop
    rename_i L' cnt inn
    obtain ⟨rfl, hc0, hck, hr0, rfl, h0, h1⟩ := h
    cases j
    · by_cases hm : cnt - 1 < 0
      · have : cnt = 0 := by omega
        subst this
        cases L' <;> simp [recv, Rel, onePulse, h0, h1] <;> omega
      · cases L' <;> simp [recv, Rel, hm, h0, h1] <;> omega
    · cases L' <;> simp [recv, Rel, onePulse, h0, h1] <;> omega
  · -- wait
    rename_i L' inn
    obtain ⟨rfl, hr0, rfl, h0, h1⟩ := h
    cases j <;> cases L' <;> simp [recv, Rel, onePulse, ready, h0, h1, hr0] at hrd ⊢
    all_goals omega
  · simp [ready] at hrd

/-! ### Consequences of the local invariant

`P = r₀ - s₀` and `Q = s₁ - r₁` (as integers). -/

section facts

variable {a : Bool × Bool × Option Bool} {s : St} {r snt : Bool → ℕ}

lemma Rel.P_le (h : Rel a s r snt) : (r false : ℤ) - snt false ≤ 2 := by
  obtain ⟨L, act, bit⟩ := a
  cases act <;> cases s <;> simp only [Rel] at h <;> omega

lemma Rel.Q_le (h : Rel a s r snt) : (snt true : ℤ) - r true ≤ 2 := by
  obtain ⟨L, act, bit⟩ := a
  cases act <;> cases s <;> simp only [Rel] at h <;> (try split_ifs at h) <;> omega

lemma Rel.done_iff (h : Rel a s r snt) :
    (result s).isSome = true ↔ (r false : ℤ) - snt false = 2 := by
  obtain ⟨L, act, bit⟩ := a
  cases act <;> cases s <;> simp only [Rel] at h <;> simp [result] <;> omega

lemma Rel.nl (h : Rel a s r snt) (ha : a.1 = false) :
    (0 ≤ (r false : ℤ) - snt false → (snt true : ℤ) - r true = (r false : ℤ) - snt false) ∧
    ((r false : ℤ) - snt false < 0 → (snt true : ℤ) - r true ≤ 0) ∧
    (r false : ℤ) - snt false ≤ (snt true : ℤ) - r true := by
  obtain ⟨L, act, bit⟩ := a
  simp only at ha; subst ha
  cases act <;> cases s <;> simp only [Rel] at h <;> (try simp at h) <;> omega

lemma Rel.l (h : Rel a s r snt) (ha : a.1 = true) :
    ((r false : ℤ) - snt false = 0 → (snt true : ℤ) - r true = 1) ∧
    ((r false : ℤ) - snt false ≤ 0 → (snt true : ℤ) - r true ≤ 1 ∧
      (r false : ℤ) - snt false + 1 ≤ (snt true : ℤ) - r true) ∧
    ((r false : ℤ) - snt false = 1 → (snt true : ℤ) - r true = 2) ∧
    ((r false : ℤ) - snt false = 2 → (snt true : ℤ) - r true = 2) := by
  obtain ⟨L, act, bit⟩ := a
  simp only at ha; subst ha
  cases act <;> cases s <;> simp only [Rel] at h <;> (try simp at h) <;> omega

lemma Rel.ready0 (_h : Rel a s r snt) (hd : (result s).isSome = false) :
    ready s false = true := by
  rcases s with ⟨L, c, i⟩ | ⟨L, i⟩ | ⟨L, c⟩ | r
  · rfl
  · cases L <;> rfl
  · rfl
  · simp [result] at hd

lemma Rel.ready1 (h : Rel a s r snt) (hd : (result s).isSome = false)
    (hw : ¬ (a.1 = true ∧ a.2.1 = true ∧ (r false : ℤ) - snt false = 1)) : ready s true = true := by
  obtain ⟨L, act, bit⟩ := a
  cases act <;> cases s <;> simp only [Rel] at h <;> simp_all [ready, result]

lemma Rel.not_ready1 (h : Rel a s r snt) (hl : a.1 = true) (ha : a.2.1 = true)
    (hp : (r false : ℤ) - snt false = 1) : ready s true = false := by
  obtain ⟨L, act, bit⟩ := a
  simp only at hl ha; subst hl ha
  cases s <;> simp only [Rel] at h <;> simp_all [ready]
  all_goals omega

lemma Rel.s0_act (h : Rel a s r snt) (ha : a.2.1 = true) : snt false = κ a.2.2 := by
  obtain ⟨L, act, bit⟩ := a
  simp only at ha; subst ha
  cases s <;> simp only [Rel] at h <;> simp_all

lemma Rel.s0_relay (h : Rel a s r snt) (ha : a.2.1 = false) : snt false = r true := by
  obtain ⟨L, act, bit⟩ := a
  simp only at ha; subst ha
  cases s <;> simp only [Rel] at h <;> simp_all

lemma Rel.result_act (h : Rel a s r snt) (ha : a.2.1 = true) {res : Option Bool}
    (hres : result s = some res) : res = decodeBit (r true) := by
  obtain ⟨L, act, bit⟩ := a
  simp only at ha; subst ha
  cases s <;> simp only [Rel] at h <;> simp_all [result]

lemma Rel.result_relay (h : Rel a s r snt) (ha : a.2.1 = false) {res : Option Bool}
    (hres : result s = some res) : res = none := by
  obtain ⟨L, act, bit⟩ := a
  simp only at ha; subst ha
  cases s <;> simp only [Rel] at h <;> simp_all [result]

end facts

lemma recv_false_port0 (s : St) : (recv s false).2 false = 0 := by
  rcases s with ⟨L, c, i⟩ | ⟨L, i⟩ | ⟨L, c⟩ | r
  · simp only [recv]; split_ifs <;> simp [onePulse]
  · cases L <;> simp [recv, onePulse]
  · simp only [recv]; split_ifs <;> simp [onePulse]
  · simp [recv]

/-! ## Propagation of the potentials around the ring

Abstract setting: `P v`, `Q v` are the potentials of node `v`, and `c1 v`, `c2 v` the numbers of
clockwise / counter-clockwise pulses in transit on the link from `v` to `v + 1`. -/

/-- Hypotheses on the potentials (consequences of `Rel` and of the channel inequalities). -/
structure Pot {n : ℕ} (ℓ : ZMod n) (P Q c1 c2 : ZMod n → ℤ) : Prop where
  link : ∀ v, Q v - P (v + 1) = c1 v + c2 v
  c1_nn : ∀ v, 0 ≤ c1 v
  c2_nn : ∀ v, 0 ≤ c2 v
  P_le : ∀ v, P v ≤ 2
  Q_le : ∀ v, Q v ≤ 2
  nl_eq : ∀ v, v ≠ ℓ → 0 ≤ P v → Q v = P v
  nl_neg : ∀ v, v ≠ ℓ → P v < 0 → Q v ≤ 0
  nl_ge : ∀ v, v ≠ ℓ → P v ≤ Q v
  l0 : P ℓ = 0 → Q ℓ = 1
  lneg : P ℓ ≤ 0 → Q ℓ ≤ 1 ∧ P ℓ + 1 ≤ Q ℓ
  l1 : P ℓ = 1 → Q ℓ = 2
  l2 : P ℓ = 2 → Q ℓ = 2

namespace Pot

variable {n : ℕ} [NeZero n] {ℓ : ZMod n} {P Q c1 c2 : ZMod n → ℤ} (h : Pot ℓ P Q c1 c2)
include h

omit [NeZero n] in
lemma P_succ_le (v : ZMod n) : P (v + 1) ≤ Q v := by
  have := h.link v; have := h.c1_nn v; have := h.c2_nn v; omega

omit [NeZero n] in
lemma nl_pos {v : ZMod n} (hv : v ≠ ℓ) (hq : 1 ≤ Q v) : P v = Q v := by
  by_cases hp : 0 ≤ P v
  · exact (h.nl_eq v hv hp).symm
  · have := h.nl_neg v hv (by omega); omega

/-- The pulses in transit: `∑ (c1 + c2) = ∑ (Q - P)`. -/
lemma sum_link : ∑ v, (c1 v + c2 v) = ∑ v, (Q v - P v) := by
  have e : ∑ v, P (v + 1) = ∑ v, P v := Fintype.sum_add_right_eq_self P 1
  calc ∑ v, (c1 v + c2 v) = ∑ v, (Q v - P (v + 1)) := sum_congr rfl fun v _ => (h.link v).symm
    _ = ∑ v, (Q v - P v) := by rw [sum_sub_distrib, sum_sub_distrib, e]

lemma sum_ge : Q ℓ - P ℓ ≤ ∑ v, (Q v - P v) := by
  classical
  rw [← add_sum_erase _ _ (mem_univ ℓ)]
  have : 0 ≤ ∑ v ∈ univ.erase ℓ, (Q v - P v) :=
    sum_nonneg fun v hv => by have := h.nl_ge v (ne_of_mem_erase hv); omega
  omega

/-- A wave value `k ≥ 1` seen anywhere was emitted by the leader. -/
lemma up {k : ℤ} (hk : 1 ≤ k) {w : ZMod n} (hw : k ≤ P w) : k ≤ Q ℓ := by
  have := ZMod.chain_ccw_to (fun u => k ≤ P u) ℓ (fun u hu hS => by
    have := h.P_succ_le u
    try dsimp only at hS ⊢
    rw [h.nl_pos hu (by omega)]; omega) w hw
  have := h.P_succ_le ℓ; try dsimp only at this ⊢
  omega

lemma all_of_leader {k : ℤ} (hk : 1 ≤ k) (hl : k ≤ P ℓ) (v : ZMod n) : k ≤ P v :=
  ZMod.chain_ccw_all (fun u => k ≤ P u) ℓ (fun u hu hS => by
    have := h.P_succ_le u
    try dsimp only at hS ⊢
    rw [h.nl_pos hu (by omega)]; omega) hl v

/-- When the leader receives the synchronization pulse back, no counter-clockwise pulse is in
transit. -/
lemma quiet_of_exit (hl : P ℓ = 0) (h1 : 1 ≤ c1 (ℓ - 1)) (v : ZMod n) : c2 v = 0 := by
  classical
  have hQ : ∀ u, 1 ≤ Q u := ZMod.chain_ccw_all (fun u => 1 ≤ Q u) (ℓ - 1) (fun u hu hS => by
      have hu' : u + 1 ≠ ℓ := fun e => hu (by rw [← e, add_sub_cancel_right])
      have := h.P_succ_le u
      try dsimp only at hS ⊢
      have := h.nl_pos hu' hS; omega)
    (by have hlink := h.link (ℓ - 1); have := h.c2_nn (ℓ - 1)
        rw [sub_add_cancel] at hlink; try dsimp only
        omega)
  have hsum : ∑ u, (c1 u + c2 u) = 1 := by
    rw [h.sum_link, ← add_sum_erase _ _ (mem_univ ℓ), hl, h.l0 hl]
    have : ∑ u ∈ univ.erase ℓ, (Q u - P u) = 0 :=
      sum_eq_zero fun u hu => by rw [h.nl_pos (ne_of_mem_erase hu) (hQ u)]; ring
    omega
  have hnn : ∀ u ∈ (univ : Finset (ZMod n)), 0 ≤ c1 u + c2 u :=
    fun u _ => by have := h.c1_nn u; have := h.c2_nn u; omega
  by_cases hv : v = ℓ - 1
  · subst hv
    have := single_le_sum hnn (mem_univ (ℓ - 1)); have := h.c2_nn (ℓ - 1); omega
  · have := sum_le_sum_of_subset_of_nonneg (subset_univ {v, ℓ - 1}) (fun u _ _ => hnn u (mem_univ u))
    rw [sum_pair hv] at this
    have := h.c1_nn v; have := h.c2_nn v; have := h.c2_nn (ℓ - 1); omega

end Pot

/-! ## Reachable configurations -/

section ring

variable {n : ℕ} [NeZero n] {x : ZMod n → Bool × Bool × Option Bool} {ℓ : ZMod n}

/-- `P v = r₀ - s₀`. -/
def P {S : Type*} (c : Config (ZMod n) S) (v : ZMod n) : ℤ := (c.recvd (v, false) : ℤ) - c.sent (v, false)
/-- `Q v = s₁ - r₁`. -/
def Q {S : Type*} (c : Config (ZMod n) S) (v : ZMod n) : ℤ := (c.sent (v, true) : ℤ) - c.recvd (v, true)
/-- Clockwise pulses in transit from `v` to `v + 1`. -/
def c1 {S : Type*} (c : Config (ZMod n) S) (v : ZMod n) : ℤ := (c.sent (v, true) : ℤ) - c.recvd (v + 1, false)
/-- Counter-clockwise pulses in transit from `v + 1` to `v`. -/
def c2 {S : Type*} (c : Config (ZMod n) S) (v : ZMod n) : ℤ := (c.sent (v + 1, false) : ℤ) - c.recvd (v, true)

omit [NeZero n] in
lemma rel {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c) (v : ZMod n) :
    Rel (x v) (c.st v) (fun p => c.recvd (v, p)) (fun p => c.sent (v, p)) :=
  Prog.Reach.local_inv (P := proc.toProg) Rel rel_init
    (fun a s r snt j h _ hrd => rel_step a s r snt j h hrd) hc v

omit [NeZero n] in
lemma recvd_le {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c) (p : ZMod n × Bool) :
    c.recvd p ≤ c.sent ((oriented n).peer p) :=
  Reach.recvd_le (W := oriented n) (A := proc.toAlgo) hc p

omit [NeZero n] in
/-- The potentials of a reachable configuration satisfy `Pot`. -/
lemma pot (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) : Pot ℓ (P c) (Q c) (c1 c) (c2 c) := by
  have hnl : ∀ v, v ≠ ℓ → (x v).1 = false := fun v hv => by
    simpa using (hℓ v).not.2 hv
  refine ⟨fun v => by simp only [P, Q, c1, c2]; ring, fun v => ?_, fun v => ?_,
    fun v => (rel hc v).P_le, fun v => (rel hc v).Q_le, fun v hv => ((rel hc v).nl (hnl v hv)).1,
    fun v hv => ((rel hc v).nl (hnl v hv)).2.1, fun v hv => ((rel hc v).nl (hnl v hv)).2.2,
    ((rel hc ℓ).l ((hℓ ℓ).2 rfl)).1, ((rel hc ℓ).l ((hℓ ℓ).2 rfl)).2.1,
    ((rel hc ℓ).l ((hℓ ℓ).2 rfl)).2.2.1, ((rel hc ℓ).l ((hℓ ℓ).2 rfl)).2.2.2⟩
  · have := recvd_le hc (v + 1, false); simp only [oriented_peer_false, add_sub_cancel_right] at this
    simp only [c1]; omega
  · have := recvd_le hc (v, true); simp only [oriented_peer_true] at this
    simp only [c2]; omega

omit [NeZero n] in
lemma done_iff {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c) (v : ZMod n) :
    (result (c.st v)).isSome = true ↔ P c v = 2 := (rel hc v).done_iff

omit [NeZero n] in
lemma c2_deliver_false {c : Config (ZMod n) St} (h0 : ∀ v, c2 c v = 0) (w : ZMod n) (v : ZMod n) :
    c2 (deliver proc.toAlgo c w false) v = 0 := by
  have := h0 v
  simp only [c2] at this
  simp only [c2, deliver_sent, deliver_recvd, Prod.mk.injEq, Bool.true_eq_false, and_false,
    ite_false, add_zero]
  have e : (proc.toAlgo.recv (c.st w) false).2 false = 0 := recv_false_port0 _
  split_ifs with h
  · rw [e]; push_cast; omega
  · push_cast; omega

/-- **Invariant**: once the leader has received the synchronization pulse back (`P ℓ ≥ 1`), no
bit pulse (counter-clockwise pulse) is in transit any more. -/
theorem ccw_quiet (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) : 1 ≤ P c ℓ → ∀ v, c2 c v = 0 := by
  refine Prog.Reach.induction (motive := fun c => 1 ≤ P c ℓ → ∀ v, c2 c v = 0) ?_ ?_ hc
  · intro h; simp [P, Prog.initCfg] at h; omega
  · intro c c' hr hs ih h1
    obtain ⟨w, j, hen⟩ := hs
    have hj : j = false ∧ ∀ v, c2 c v = 0 := by
      by_cases hP : 1 ≤ P c ℓ
      · have h0 := ih hP
        refine ⟨?_, h0⟩
        by_contra hj; simp only [Bool.not_eq_false] at hj; subst hj
        have := hen.2.2; have := h0 w
        simp only [Prog.toAlgo, oriented_peer_true, c2] at *; omega
      · -- the leader exits its loop at this step
        simp only [P, deliver_sent, deliver_recvd, Prod.mk.injEq] at h1 hP
        have hw : w = ℓ ∧ j = false := by
          by_contra hc'
          rcases not_and_or.1 hc' with h' | h'
          · simp only [show ℓ ≠ w from fun e => h' e.symm, false_and, ite_false, add_zero] at h1
            omega
          · simp only [Bool.not_eq_false] at h'; subst h'
            simp only [Bool.false_eq_true, and_false, ite_false, add_zero] at h1
            split_ifs at h1 <;> push_cast at h1 <;> omega
        obtain ⟨rfl, rfl⟩ := hw
        refine ⟨rfl, ?_⟩
        have e' : (recv (c.st w) false).2 false = 0 := recv_false_port0 _
        simp only [and_self, ite_true, e', add_zero] at h1
        have hP0 : P c w = 0 := by simp only [P]; push_cast at h1; omega
        refine (pot hℓ hr).quiet_of_exit hP0 ?_
        have := hen.2.2
        simp only [Prog.toAlgo, oriented_peer_false] at this
        simp only [c1, sub_add_cancel]; omega
    obtain ⟨rfl, h0⟩ := hj
    exact c2_deliver_false h0 w

omit [NeZero n] in
/-- In a final configuration, a node that has not returned has nothing in transit towards
`Port0`. -/
lemma c1_final {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c)
    (hf : proc.Final (oriented n) c) {u : ZMod n} (hu : P c u ≠ 2) : c1 c (u - 1) = 0 := by
  have hd : (result (c.st u)).isSome = false := by
    by_contra h; simp only [Bool.not_eq_false] at h; exact hu ((done_iff hc u).1 h)
  have hle := recvd_le hc (u, false)
  have hnot := hf u false
  simp only [Enabled, Prog.toAlgo, hd, (rel hc u).ready0 hd, true_and, not_lt,
    oriented_peer_false] at hnot hle
  simp only [c1, sub_add_cancel]; omega

omit [NeZero n] in
/-- In a final configuration, a node that has not returned and is not the active leader waiting
at line 21 has nothing in transit towards `Port1`. -/
lemma c2_final {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c)
    (hf : proc.Final (oriented n) c) {u : ZMod n} (hu : P c u ≠ 2)
    (hw : ¬ ((x u).1 = true ∧ (x u).2.1 = true ∧ P c u = 1)) : c2 c u = 0 := by
  have hd : (result (c.st u)).isSome = false := by
    by_contra h; simp only [Bool.not_eq_false] at h; exact hu ((done_iff hc u).1 h)
  have hle := recvd_le hc (u, true)
  have hnot := hf u true
  simp only [Enabled, Prog.toAlgo, hd, (rel hc u).ready1 hd hw, true_and, not_lt,
    oriented_peer_true] at hnot hle
  simp only [c2]; omega

/-- In every final configuration every node has returned (`P = 2`). -/
theorem final_done (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) (hf : proc.Final (oriented n) c) (v : ZMod n) :
    P c v = 2 := by
  have H := pot hℓ hc
  have hnn : ∀ u ∈ (univ : Finset (ZMod n)), 0 ≤ c1 c u + c2 c u :=
    fun u _ => by have := H.c1_nn u; have := H.c2_nn u; omega
  have hsum := H.sum_link
  have hge := H.sum_ge
  rcases lt_trichotomy (P c ℓ) 1 with hlt | heq | hgt
  · exfalso
    have hnd : ∀ u, P c u ≠ 2 := fun u hu => by
      have := H.up (k := 2) (by norm_num) hu.ge; have := (H.lneg (by omega)).1; omega
    have hz : ∀ u, c1 c u + c2 c u = 0 := fun u => by
      have h1 := c1_final hc hf (hnd (u + 1)); rw [add_sub_cancel_right] at h1
      have h2 := c2_final hc hf (hnd u) (fun h => by
        rcases eq_or_ne u ℓ with rfl | hu
        · omega
        · exact absurd ((hℓ u).1 h.1) hu)
      omega
    have := (H.lneg (by omega)).2
    simp only [hz, sum_const_zero] at hsum; omega
  · exfalso
    have h2 := ccw_quiet hℓ hc heq.ge
    have hz : ∀ u, c1 c u + c2 c u = 0 := fun u => by
      rw [h2 u, add_zero]
      by_cases hu : P c (u + 1) = 2
      · have := H.link u; have := H.Q_le u; have := H.c1_nn u; rw [hu, h2 u] at *; omega
      · have h1 := c1_final hc hf hu; rwa [add_sub_cancel_right] at h1
    have := H.l1 heq
    simp only [hz, sum_const_zero] at hsum; omega
  · have := H.all_of_leader (k := 2) (by norm_num) (by omega) v
    have := H.P_le v; omega

/-- **Quiescent termination** (Theorem 17): every final configuration is quiescent and every node
has returned. -/
theorem final_spec (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) (hf : proc.Final (oriented n) c) :
    proc.Quiescent (oriented n) c ∧ ∀ v, (proc.result (c.st v)).isSome = true := by
  have H := pot hℓ hc
  have hP := final_done hℓ hc hf
  have hQ : ∀ v, Q c v = 2 := fun v => by
    rcases eq_or_ne v ℓ with rfl | hv
    · exact H.l2 (hP v)
    · rw [H.nl_eq v hv (by rw [hP v]; norm_num), hP v]
  have hsum := H.sum_link
  simp only [hP, hQ, sub_self, sum_const_zero] at hsum
  have hnn : ∀ u ∈ (univ : Finset (ZMod n)), 0 ≤ c1 c u + c2 c u :=
    fun u _ => by have := H.c1_nn u; have := H.c2_nn u; omega
  have hz := (sum_eq_zero_iff_of_nonneg hnn).1 hsum
  refine ⟨?_, fun v => (done_iff hc v).2 (hP v)⟩
  rintro ⟨v, _ | _⟩
  · have := hz (v - 1) (mem_univ _); have := H.c1_nn (v - 1); have := H.c2_nn (v - 1)
    simp only [c1, sub_add_cancel] at *
    simp only [oriented_peer_false]; omega
  · have := hz v (mem_univ _); have := H.c1_nn v; have := H.c2_nn v
    simp only [c2] at *
    simp only [oriented_peer_true]; omega

end ring

/-! ## Theorem 17 -/

section main

variable {n : ℕ} [NeZero n] {x : ZMod n → Bool × Bool × Option Bool} {ℓ : ZMod n}

/-- The active flags. -/
abbrev act (x : ZMod n → Bool × Bool × Option Bool) (v : ZMod n) : Bool := (x v).2.1

omit [NeZero n] in
/-- Along a segment of relays, the counter-clockwise channels can only decrease the number of
pulses. -/
lemma r1_le_chain {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c) (v : ZMod n) (K : ℕ)
    (hrel : ∀ k, 0 < k → k < K → (x (v + k)).2.1 = false) :
    ∀ j, 0 < j → j ≤ K → c.recvd (v, true) ≤ c.sent (v + j, false) := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hjK
    have hlink := recvd_le hc (v + j, true)
    simp only [oriented_peer_true] at hlink
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using hlink
    · have h1 := ih hj (by omega)
      have h2 := (rel hc (v + j)).s0_relay (hrel j hj (by omega))
      rw [Nat.cast_succ, ← add_assoc]; omega

omit [NeZero n] in
lemma r1_eq_chain {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c)
    (hq : proc.Quiescent (oriented n) c) (v : ZMod n) (K : ℕ)
    (hrel : ∀ k, 0 < k → k < K → (x (v + k)).2.1 = false) :
    ∀ j, 0 < j → j ≤ K → c.recvd (v, true) = c.sent (v + j, false) := by
  intro j
  induction j with
  | zero => intro h; omega
  | succ j ih =>
    intro _ hjK
    have hlink := hq (v + j, true)
    simp only [oriented_peer_true] at hlink
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa using hq (v, true)
    · have h1 := ih hj (by omega)
      have h2 := (rel hc (v + j)).s0_relay (hrel j hj (by omega))
      rw [Nat.cast_succ, ← add_assoc]; omega

lemma recvd_true_le (hact : ∃ u, (x u).2.1 = true) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) (v : ZMod n) : c.recvd (v, true) ≤ 2 := by
  obtain ⟨u, hu⟩ := hact
  obtain ⟨k, h0, -, -, h1, h2⟩ := vnext_spec (act := act x) hu v
  have := r1_le_chain hc v k h2 _ h0 le_rfl
  rw [(rel hc _).s0_act h1] at this
  exact this.trans (κ_le _)

/-- **Theorem 17** (message complexity): no execution sends more than `6n` pulses. -/
theorem totalSent_le (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hact : ∃ u, (x u).2.1 = true)
    {c : Config (ZMod n) proc.State} (hc : proc.Reach (oriented n) x c) : totalSent c ≤ 6 * n := by
  have H := pot hℓ hc
  have hv : ∀ v, c.sent (v, false) + c.sent (v, true) ≤ 6 := by
    intro v
    have hr := recvd_true_le hact hc v
    have hQ := H.Q_le v
    simp only [Q] at hQ
    have hs0 : c.sent (v, false) ≤ 2 := by
      cases ha : (x v).2.1
      · rw [(rel hc v).s0_relay ha]; exact hr
      · rw [(rel hc v).s0_act ha]; exact κ_le _
    omega
  calc totalSent c = ∑ v, (c.sent (v, false) + c.sent (v, true)) := sum_ports _
    _ ≤ ∑ _v : ZMod n, 6 := sum_le_sum fun v _ => hv v
    _ = 6 * n := by simp [ZMod.card, mul_comm]

/-- **Theorem 17** (results): every active node `v` returns the bit of the next active node
clockwise (`v + k`, least `k ≥ 1`); relays return `none`. -/
theorem returns (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hact : ∃ u, (x u).2.1 = true) :
    proc.Returns (oriented n) x (fun v => if (x v).2.1 then (x (vnext (act x) v)).2.2 else none) := by
  intro c hc hf v
  obtain ⟨hq, hdone⟩ := final_spec hℓ hc hf
  obtain ⟨res, hres⟩ := Option.isSome_iff_exists.1 (hdone v)
  change result (c.st v) = some res at hres
  change result (c.st v) = _
  rw [hres]
  cases ha : (x v).2.1
  · rw [(rel hc v).result_relay ha hres]; simp [ha]
  · rw [(rel hc v).result_act ha hres]; simp only [ha, ite_true]
    obtain ⟨u, hu⟩ := hact
    obtain ⟨k, h0, -, hk, h1, h2⟩ := vnext_spec (act := act x) hu v
    have := r1_eq_chain hc hq v k h2 _ h0 le_rfl
    rw [(rel hc _).s0_act h1] at this
    rw [this, decodeBit_κ, hk]

/-- **Theorem 17** (composable ending), when the leader is active. -/
theorem composable (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hact : ∃ u, (x u).2.1 = true)
    (hlact : (x ℓ).2.1 = true) : proc.Composable (oriented n) x where
  bounded := ⟨6 * n, fun c hc => totalSent_le hℓ hact hc⟩
  final c hc hf := final_spec hℓ hc hf
  clean c hc v j hv hrd hpeer := by
    have H := pot hℓ hc
    have hnd : P c v ≠ 2 := fun h => by
      have := (done_iff hc v).2 h; simp_all
    have hpv := H.P_le v
    cases j
    · -- the counter-clockwise neighbour `v - 1` has returned
      have hp : P c (v - 1) = 2 := (done_iff hc (v - 1)).1 (by simpa using hpeer)
      have hQ : Q c (v - 1) = 2 := by
        rcases eq_or_ne (v - 1) ℓ with h | h
        · rw [h] at hp ⊢; exact H.l2 hp
        · rw [H.nl_eq _ h (by omega), hp]
      have hl := H.up (k := 2) (by norm_num) hp.ge
      have hl1 : 1 ≤ P c ℓ := by
        by_contra hc'; have := (H.lneg (by omega)).1; omega
      have h2 := ccw_quiet hℓ hc hl1 (v - 1)
      have hlink := H.link (v - 1)
      rw [sub_add_cancel, h2, hQ] at hlink
      simp only [c1, sub_add_cancel] at hlink
      simp only [oriented_peer_false]; omega
    · -- the clockwise neighbour `v + 1` has returned
      exfalso
      have hp : P c (v + 1) = 2 := (done_iff hc (v + 1)).1 (by simpa using hpeer)
      have hQ := H.P_succ_le v
      rcases eq_or_ne v ℓ with rfl | h
      · have : P c v = 1 := by
          by_contra hc'; have := (H.lneg (by omega)).1; omega
        have := (rel hc v).not_ready1 ((hℓ v).2 rfl) hlact this
        simp_all
      · have := H.nl_pos h (by omega); omega

/-- **Lemma 15** (no relays): if every node is active, every node returns the bit of its clockwise
neighbour (and `proc` is composable by `composable`, with at most `6n` pulses by `totalSent_le`). -/
theorem lemma15 (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hall : ∀ v, (x v).2.1 = true) :
    proc.Returns (oriented n) x (fun v => (x (v + 1)).2.2) := by
  have hact : ∃ u, (x u).2.1 = true := ⟨ℓ, hall ℓ⟩
  have hnext : ∀ v, vnext (act x) v = v + 1 := fun v => by
    obtain ⟨k, h0, -, hk, -, h2⟩ := vnext_spec (act := act x) (hall ℓ) v
    have : k = 1 := by
      by_contra h
      have := h2 1 one_pos (by omega)
      simp [act, hall] at this
    rw [hk, this, Nat.cast_one]
  intro c hc hf v
  rw [returns hℓ hact c hc hf v]
  simp [hall, hnext]

end main

/-! ## Theorem 17 is false for a relay leader: an explicit counterexample to composability

With a relay leader, the leader relay forwards the synchronization pulse a second time (this
second lap is the termination wave) and keeps reading **any** port until the termination pulse
comes back (Algorithm 8, line 5). Meanwhile its clockwise neighbour has already returned and may
start the next procedure, whose pulses on `Port0` the leader relay would consume. So the
"composable ending property" claimed in Lemma 16 / Theorem 17 fails (the terminator waits on
port `d = 1` after starting the termination wave), and so does `Composable.clean`.

Counterexample: `n = 2`, node `0` is the leader and a relay, node `1` is active with bit `⊥`. -/

section counterexample

/-- Inputs: node `0` is a relay leader, node `1` is active with bit `⊥`. -/
def xRelay : ZMod 2 → Bool × Bool × Option Bool := fun v =>
  if v = 0 then (true, false, none) else (false, true, none)

/-- The configuration reached after three deliveries: node `1` receives the synchronization
pulse and forwards it, node `0` forwards it again (termination wave), node `1` receives it and
returns. -/
def cRelay : Config (ZMod 2) St :=
  deliver proc.toAlgo (deliver proc.toAlgo (deliver proc.toAlgo (proc.initCfg xRelay) 1 false)
    0 false) 1 false

theorem cRelay_reach : proc.Reach (oriented 2) xRelay cRelay :=
  (((Prog.Reach.init xRelay).tail (Step.mk _ 1 false (by unfold Enabled; decide))).tail
    (Step.mk _ 0 false (by unfold Enabled; decide))).tail
    (Step.mk _ 1 false (by unfold Enabled; decide))

/-- In `cRelay`, the leader relay `0` has not returned and is willing to read `Port1`, its
clockwise neighbour `1` has returned, and no pulse is in transit from `1` to `0`. -/
theorem cRelay_spec :
    proc.result (cRelay.st 0) = none ∧ proc.ready (cRelay.st 0) true = true ∧
      (proc.result (cRelay.st 1)).isSome = true ∧
      cRelay.recvd (0, true) = cRelay.sent ((oriented 2).peer (0, true)) := by
  decide

/-- **Theorem 17 fails for a relay leader**: the combined CCWBitSending/CCWBitRelay execution
is not composable (`Composable.clean` fails), although it terminates quiescently with the right
results (`final_spec`, `returns`, `totalSent_le` hold for any position of the leader). -/
theorem not_composable_relay_leader : ¬ proc.Composable (oriented 2) xRelay := by
  intro h
  obtain ⟨h1, h2, h3, h4⟩ := cRelay_spec
  have := h.clean cRelay cRelay_reach 0 true h1 h2 h3
  omega

/-- The mirror image: `CWBitSending` / `CWBitRelay` with a relay leader is not composable either. -/
theorem cw_not_composable_relay_leader : ¬ cwProc.Composable (oriented 2) (xRelay ∘ Neg.neg) := by
  intro h
  rw [Proc.composable_mirror_iff] at h
  have e : (xRelay ∘ Neg.neg) ∘ Neg.neg = xRelay := by funext v; simp
  rw [e] at h
  exact not_composable_relay_leader h

end counterexample

/-! ## Mirror images: `CWBitSending` / `CWBitRelay` -/

section mirror

variable {n : ℕ} [NeZero n] {x : ZMod n → Bool × Bool × Option Bool} {ℓ : ZMod n}

omit [NeZero n] in
lemma hℓ_neg (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) : ∀ v, (x (-v)).1 = true ↔ v = -ℓ := fun v => by
  rw [hℓ, neg_eq_iff_eq_neg]

omit [NeZero n] in
lemma hact_neg (hact : ∃ u, (x u).2.1 = true) : ∃ u, (x (-u)).2.1 = true := by
  obtain ⟨u, hu⟩ := hact; exact ⟨-u, by simpa using hu⟩

/-- **Theorem 17 for `CWBitSending`** (composable ending), when the leader is active. -/
theorem cw_composable (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hact : ∃ u, (x u).2.1 = true)
    (hlact : (x ℓ).2.1 = true) : cwProc.Composable (oriented n) x :=
  (Proc.composable_mirror_iff proc x).2
    (composable (x := x ∘ Neg.neg) (hℓ_neg hℓ) (hact_neg hact) (by simpa using hlact))

/-- **Theorem 17 for `CWBitSending`** (results): every active node `v` returns the bit of the
next active node counter-clockwise; relays return `none`. -/
theorem cw_returns (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hact : ∃ u, (x u).2.1 = true) :
    cwProc.Returns (oriented n) x (fun v => if (x v).2.1 then (x (vprev (act x) v)).2.2 else none) := by
  rw [Proc.returns_mirror_iff]
  convert returns (x := x ∘ Neg.neg) (hℓ_neg hℓ) (hact_neg hact) using 1
  funext w
  simp only [Function.comp, vprev_eq_neg_vnext_neg, neg_neg]
  rfl

/-- **Theorem 17 for `CWBitSending`** (message complexity): at most `6n` pulses. -/
theorem cw_totalSent_le (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hact : ∃ u, (x u).2.1 = true)
    {c : Config (ZMod n) cwProc.State} (hc : cwProc.Reach (oriented n) x c) :
    totalSent c ≤ 6 * n :=
  (Proc.totalSent_mirror_le_iff proc x _).2
    (fun _ hc' => totalSent_le (hℓ_neg hℓ) (hact_neg hact) hc') c hc

/-- **Theorem 17 for `CWBitSending`** (quiescent termination), for any position of the leader. -/
theorem cw_final_spec (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) {c : Config (ZMod n) cwProc.State}
    (hc : cwProc.Reach (oriented n) x c) (hf : cwProc.Final (oriented n) c) :
    cwProc.Quiescent (oriented n) c ∧ ∀ v, (cwProc.result (c.st v)).isSome = true := by
  have hc' := (Proc.reach_mirror_iff proc x c).1 hc
  have hf' := (Proc.final_mirror_iff proc c).1 hf
  obtain ⟨hq, hr⟩ := final_spec (hℓ_neg hℓ) hc' hf'
  exact ⟨(Proc.quiescent_mirror_iff proc c).2 hq, fun v => by
    simpa [Config.mirror, Proc.mirror, Prog.mirror] using hr (-v)⟩

end mirror

end Podc.ContentOblivious.BitSending
