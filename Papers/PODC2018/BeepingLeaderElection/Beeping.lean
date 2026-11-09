import Papers.PODC2018.BeepingLeaderElection.Balanced
import Papers.PODC2018.BeepingLeaderElection.Theorem2
import Podc.Computability.Distributed.Beeping.Basic

/-!
# Algorithm 1 in the beeping model: communication phases of 1664 rounds (Section 3.1.3), Theorem 3

Dufoulon, Burman, Beauquier. *Beeping a Deterministic Time-Optimal Leader Election.* DISC 2018,
Sections 2.2, 3.1.2, 3.1.3 and Theorem 3.

**Model** (`Cslib.Beeping`, Section 2.2): synchronous rounds with a synchronous start; deterministic
algorithm; in every round a node beeps or listens; a beeping node learns nothing, a listening node
learns one bit: whether at least one neighbour beeped (no collision detection, no sender identity, no
multiplicity). Nodes know their own identifier (stored in the initial state as `α(id)`) and nothing
else (uniform in `n`, `N`, `D`). No failures.

**Implementation of a diffusion phase** (Section 3.1.3). The phase-level message of a node is its pair
`(prefix, suspicious)`. It is encoded (`encode`) as one of `c = 13 · 64 · 2 = 1664` slots:
`(|prefix| mod 13, the last min(|prefix|, 6) bits of prefix as a number < 64, suspicious)`. A
communication phase consists of `c` rounds; in round `r` of the phase a node beeps iff `r` is its own
slot, and otherwise listens and records `r` if it heard a beep. At the end of the phase it decodes every
heard slot w.r.t. its own prefix `x` (`decode`: length `L = decodeNat 6 |x| (k mod 13)` by 6-balanced
decoding, word `x[0, L-6) ‖ (last bits)`) and applies the rules of Algorithm 1 (`ruleStep`,
with the repaired priority `Priority.maxDelete`) to the decoded set.

* `decode_encode` — decoding is correct whenever the sender's prefix `y` and the receiver's prefix `x`
  satisfy the conclusion of Lemma 1; `encode_inj` — so the encoding is injective among such pairs;
* `ruleStep_insert_self` / `ruleStep_erase_self` — the node's own pair never triggers a rule (needed
  because a beeping node cannot hear neighbours that use its own slot);
* `beepRun_phase` (simulation) — at round `1664 · p` the beep-level state of every node carries exactly
  the phase-level state `run G .maxDelete ident p v`; `beepRun_s` for every round `t` (phase `t / 1664`);
* `theorem_3` — **Theorem 3** in rounds: after `1664 · (|α(X)| + 2D)` rounds, every node has
  `prefix = α(X)`, `leaderId = X`, and the maximum-identifier node is the unique candidate and the unique
  leader; `theorem_3_log` — the same after `1664 · (2⌊log₂ X⌋ + 3 + 2D)` rounds, i.e. `O(D + log N)`.
-/

namespace Podc.BeepingLeaderElection

/-! ### Encoding and decoding of `(prefix, suspicious)` pairs -/

/-- The length of a communication phase: `c = 13 · 2⁶ · 2 = 1664` rounds (Section 3.1.3). -/
def commLen : ℕ := 1664

/-- The last `min(|x|, 6)` bits of `x`. -/
def lastBits (x : Word) : Word := x.drop (x.length - 6)

/-- The slot (message) of a pair `(prefix, suspicious)`:
`(|prefix| mod 13) + 13 · (ofBits (last bits) + 64 · suspicious)` ∈ `[0, 1664)`. -/
def encode (m : Word × Bool) : ℕ :=
  m.1.length % 13 + 13 * (ofBits (lastBits m.1) + 64 * m.2.toNat)

/-- The `n` least significant bits of a number, most significant bit first. -/
def bitsOf : ℕ → ℕ → Word
  | 0, _ => []
  | n + 1, k => bitsOf n (k / 2) ++ [k % 2 == 1]

/-- Decoding of slot `k` by a receiver with prefix `x`: the length `L` is decoded as a 6-balanced
value (`M = 13`), the `min(L, 6)` last bits are read from the slot, and the more significant bits are
taken from `x`. -/
def decode (x : Word) (k : ℕ) : Word × Bool :=
  let L := decodeNat 6 x.length (k % 13)
  (x.take (L - 6) ++ bitsOf (min L 6) (k / 13 % 64), decide (k / 832 = 1))

theorem encode_mk (y : Word) (b : Bool) :
    encode (y, b) = y.length % 13 + 13 * (ofBits (lastBits y) + 64 * b.toNat) := rfl

theorem lastBits_length (x : Word) : (lastBits x).length = min x.length 6 := by
  simp [lastBits]; omega

theorem ofBits_lastBits_lt (x : Word) : ofBits (lastBits x) < 64 :=
  (ofBits_lt _).trans_le (by
    rw [lastBits_length, show (64 : ℕ) = 2 ^ 6 by rfl]
    exact Nat.pow_le_pow_right (by norm_num) (min_le_right _ _))

/-- Every slot is `< 1664`. -/
theorem encode_lt (m : Word × Bool) : encode m < commLen := by
  have := ofBits_lastBits_lt m.1
  have : m.2.toNat ≤ 1 := Bool.toNat_le _
  unfold encode commLen; omega

theorem bitsOf_ofBits (w : Word) : bitsOf w.length (ofBits w) = w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.length_append, List.length_singleton, bitsOf, ofBits_append_singleton]
    have h1 : (2 * ofBits l + a.toNat) / 2 = ofBits l := by cases a <;> simp; omega
    have h2 : ((2 * ofBits l + a.toNat) % 2 == 1) = a := by cases a <;> simp
    rw [h1, h2, ih]

theorem take_eq_of_prefix {a y : Word} (h : a <+: y) {n : ℕ} (hn : n ≤ a.length) :
    a.take n = y.take n := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append_of_le_length hn]

theorem take_dropLast {x : Word} {n : ℕ} (hn : n ≤ x.length - 1) : x.dropLast.take n = x.take n :=
  take_eq_of_prefix (List.dropLast_prefix x) (by simpa using hn)

/-- The lengths of neighbouring prefixes are 6-balanced (from Lemma 1). -/
theorem Lemma1Holds.length_le {x y : Word} (h : Lemma1Holds x y) :
    y.length ≤ x.length + 6 ∧ x.length ≤ y.length + 6 := by
  rcases le_total x.length y.length with hl | hl
  · have := (h.1 hl).2.1; omega
  · have := (h.2 hl).2.1; omega

/-- Lemma 1 lets the receiver `x` fill in the bits of `y` before its last 6 bits. -/
theorem Lemma1Holds.take_eq {x y : Word} (h : Lemma1Holds x y) :
    x.take (y.length - 6) = y.take (y.length - 6) := by
  rcases le_total x.length y.length with hl | hl
  · obtain ⟨hd, hlen, hne⟩ := h.1 hl
    by_cases hp : x <+: y
    · exact take_eq_of_prefix hp (by omega)
    · have := hne hp
      rw [← take_dropLast (by omega)]
      exact take_eq_of_prefix hd (by simp; omega)
  · obtain ⟨hd, hlen, -⟩ := h.2 hl
    rw [← take_dropLast (x := y) (by omega)]
    exact (take_eq_of_prefix hd (by simp; omega)).symm

/-- **Section 3.1.3** (decoding correctness): if the prefixes `x` of the receiver and `y` of the
sender satisfy the conclusion of Lemma 1, the receiver decodes the slot of `(y, b)` to `(y, b)`. -/
theorem decode_encode {x y : Word} (h : Lemma1Holds x y) (b : Bool) :
    decode x (encode (y, b)) = (y, b) := by
  have he := ofBits_lastBits_lt y
  have hb : b.toNat ≤ 1 := Bool.toNat_le _
  obtain ⟨h1, h2⟩ := h.length_le
  have hL : decodeNat 6 x.length (encode (y, b) % 13) = y.length := by
    have : encode (y, b) % 13 = y.length % 13 := by rw [encode_mk]; omega
    rw [this]; exact decodeNat_correct 6 (by omega) (by omega)
  have hk : encode (y, b) / 13 % 64 = ofBits (lastBits y) := by rw [encode_mk]; omega
  have hs : encode (y, b) / 832 = b.toNat := by rw [encode_mk]; omega
  simp only [decode, hL, hk, hs, Prod.mk.injEq]
  refine ⟨?_, by cases b <;> simp⟩
  rw [← lastBits_length, bitsOf_ofBits, h.take_eq, lastBits, List.take_append_drop]

/-- The encoding is injective among pairs whose prefixes satisfy Lemma 1 with the receiver's
prefix `x`. -/
theorem encode_inj {x y y' : Word} {b b' : Bool} (h : Lemma1Holds x y) (h' : Lemma1Holds x y')
    (he : encode (y, b) = encode (y', b')) : (y, b) = (y', b') := by
  rw [← decode_encode h b, ← decode_encode h' b', he]

/-- Example: a receiver with prefix `1101` decodes the slot of `(110110, true)`. -/
example : decode [true, true, false, true] (encode ([true, true, false, true, true, false], true)) =
    ([true, true, false, true, true, false], true) := by decide

/-- A word satisfies Lemma 1 with itself. -/
theorem lemma1Holds_self (x : Word) : Lemma1Holds x x :=
  lemma1Holds_of_prefix (List.prefix_refl x) (by omega)

/-! ### The own pair never triggers a rule -/

section own

variable {pr : Priority} {Y : Word} {s : NState} {R : Finset (Word × Bool)}

theorem lcpLen_self (x : Word) : lcpLen x x = x.length := by
  simpa using lcpLen_self_append x []

theorem branchLow_self (x : Word) : branchLow x x = false := by
  simp [branchLow, lcpLen_self]

theorem delAmount_insert_self (pr : Priority) (x : Word) (b : Bool) (R : Finset (Word × Bool)) :
    delAmount pr x (insert (x, b) R) = delAmount pr x R := by
  have h1 : amt1 x (x, b) = 0 := by simp [amt1]
  have h2 : amt2 x x = 0 := by simp [amt2, branchLow_self]
  have hs1 : (insert (x, b) R).sup (amt1 x) = R.sup (amt1 x) := by
    rw [Finset.sup_insert, h1]; exact bot_sup_eq _
  have hs2 : ((insert (x, b) R).sup fun m => amt2 x m.1) = R.sup fun m => amt2 x m.1 := by
    rw [Finset.sup_insert]; exact (congrArg (· ⊔ _) h2).trans (bot_sup_eq _)
  unfold delAmount
  rw [hs1, hs2]

/-- **Section 3.1.3**: adding the node's own pair `(prefix, b)` to the received set does not change
the update of Algorithm 1 (a node with the same prefix triggers no rule). -/
theorem ruleStep_insert_self (b : Bool) :
    ruleStep pr Y s (insert (s.pre, b) R) = ruleStep pr Y s R := by
  have hc : chgBy s.pre s.pre = false := by simp [chgBy, branchLow_self]
  have h4 : ¬ s.pre ++ [true] <+: s.pre := fun h => by simpa using h.length_le
  have h5 : ¬ s.pre ++ [false] <+: s.pre := fun h => by simpa using h.length_le
  simp only [ruleStep, delAmount_insert_self, Finset.exists_mem_insert, hc, h4, h5, false_or,
    Bool.false_eq_true]

/-- Removing the node's own pair from the received set does not change the update. -/
theorem ruleStep_erase_self (b : Bool) :
    ruleStep pr Y s (R.erase (s.pre, b)) = ruleStep pr Y s R := by
  rw [← ruleStep_insert_self (R := R.erase _) b, Finset.insert_erase_eq_insert,
    ruleStep_insert_self]

/-- Removing any set of pairs carrying the node's own prefix does not change the update. -/
theorem ruleStep_filter_self (P : Word × Bool → Prop) [DecidablePred P]
    (hP : ∀ m ∈ R, ¬ P m → m.1 = s.pre) : ruleStep pr Y s (R.filter P) = ruleStep pr Y s R := by
  have key : ∀ D : Finset (Word × Bool), (∀ m ∈ D, m.1 = s.pre) →
      ruleStep pr Y s (R.filter P ∪ D) = ruleStep pr Y s (R.filter P) := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | insert a D _ ih =>
      intro hD
      obtain ⟨a1, a2⟩ := a
      have ha : a1 = s.pre := hD _ (Finset.mem_insert_self _ _)
      subst ha
      rw [Finset.union_insert, ruleStep_insert_self,
        ih fun m hm => hD m (Finset.mem_insert_of_mem hm)]
  conv_rhs => rw [← Finset.filter_union_filter_not_eq P R]
  rw [key]
  intro m hm
  rw [Finset.mem_filter] at hm
  exact hP m hm.1 hm.2

end own

/-! ### The beep-level algorithm -/

/-- Local state of a node in the beeping implementation. -/
structure BState where
  /-- The node's own α-encoded identifier `α(id)` (its input). -/
  Y : Word
  /-- The phase-level state of Algorithm 1 (`prefix`, `suspicious`, `candidate`). -/
  s : NState
  /-- The current round within the communication phase, in `[0, 1664)`. -/
  slot : ℕ
  /-- The slots in which a beep was heard so far in this communication phase. -/
  heard : Finset ℕ
  deriving DecidableEq

/-- The slot of a node with phase-level state `s`. -/
def ownSlot (s : NState) : ℕ := encode (s.pre, s.susp)

/-- End of a round with the updated set `H` of heard slots: move to the next slot, or, at the end of
the communication phase, decode the heard slots and apply the rules of Algorithm 1. -/
def endRound (σ : BState) (H : Finset ℕ) : BState :=
  if σ.slot + 1 < commLen then ⟨σ.Y, σ.s, σ.slot + 1, H⟩
  else ⟨σ.Y, ruleStep .maxDelete σ.Y σ.s (H.image (decode σ.s.pre)), 0, ∅⟩

/-- Algorithm 1 in the beeping model (Section 3.1.3): in each round a node beeps iff the current
round of the communication phase is its own slot. -/
def beepAlgo : Cslib.Beeping.Algorithm BState where
  beeps σ := decide (σ.slot = ownSlot σ.s)
  onBeep σ := endRound σ σ.heard
  onListen σ b := endRound σ (if b then insert σ.slot σ.heard else σ.heard)

theorem onBeep_eq (σ : BState) : beepAlgo.onBeep σ = endRound σ σ.heard := rfl

theorem onListen_eq (σ : BState) (b : Bool) :
    beepAlgo.onListen σ b = endRound σ (if b then insert σ.slot σ.heard else σ.heard) := rfl

/-- Output `leader` of a node (lines 9–10 of Algorithm 1): a candidate whose prefix is its own α-id. -/
def BState.isLeader (σ : BState) : Prop := σ.s.cand = true ∧ σ.s.pre = σ.Y

/-- Output `leaderId = α⁻¹(prefix)`. -/
def BState.leaderId (σ : BState) : Option ℕ := alphaInv σ.s.pre

section Network

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (ident : V → ℕ)

/-- Initial state of node `v`: its input `α(id_v)`, phase-level initial state, slot `0`. -/
def initState (v : V) : BState := ⟨alpha (ident v), NState.init, 0, ∅⟩

/-- The beep-level execution of Algorithm 1: the configuration at the end of round `t`. -/
def beepRun : ℕ → V → BState := Cslib.Beeping.run G beepAlgo (initState ident)

/-- The heard slots of `v` after the first `r` rounds of communication phase `p`: the slots `< r` of
its neighbours, other than its own. -/
def heardAt (p r : ℕ) (v : V) : Finset ℕ :=
  ((Finset.univ.filter (G.Adj v)).image fun u => ownSlot (run G .maxDelete ident p u)).filter
    fun k => k < r ∧ k ≠ ownSlot (run G .maxDelete ident p v)

omit [DecidableEq V] in
/-- One round inside communication phase `p`. -/
theorem beepRun_round {p r : ℕ}
    (h : ∀ v, beepRun G ident (commLen * p + r) v =
      ⟨alpha (ident v), run G .maxDelete ident p v, r, heardAt G ident p r v⟩) (v : V) :
    beepRun G ident (commLen * p + r + 1) v =
      endRound ⟨alpha (ident v), run G .maxDelete ident p v, r, heardAt G ident p r v⟩
        (heardAt G ident p (r + 1) v) := by
  have hb : ∀ u, beepAlgo.beeps (beepRun G ident (commLen * p + r) u) = decide (r = ownSlot (run G .maxDelete ident p u)) :=
    fun u => by rw [h u]; rfl
  unfold beepRun
  by_cases hv : r = ownSlot (run G .maxDelete ident p v)
  · rw [Cslib.Beeping.run_succ_of_beeps _ _ (by rw [← beepRun, hb v]; simpa using hv)]
    rw [← beepRun, h v]
    rw [onBeep_eq]
    dsimp only
    congr 1
    ext k
    simp only [heardAt, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hk1, hk2⟩; exact ⟨hk, by omega, hk2⟩
    · rintro ⟨hk, hk1, hk2⟩; exact ⟨hk, by omega, hk2⟩
  · rw [Cslib.Beeping.run_succ_of_listens _ _ (by rw [← beepRun, hb v]; simpa using hv)]
    have hh : Cslib.Beeping.hears G beepAlgo (beepRun G ident (commLen * p + r)) v =
        decide (∃ u, G.Adj v u ∧ r = ownSlot (run G .maxDelete ident p u)) := by
      rw [Bool.eq_iff_iff, Cslib.Beeping.hears_eq_true]
      simp only [hb, decide_eq_true_eq]
    rw [← beepRun, hh, h v]
    rw [onListen_eq]
    dsimp only
    congr 1
    ext k
    simp only [heardAt, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    split_ifs with hu
    · rw [decide_eq_true_eq] at hu
      rw [Finset.mem_insert, Finset.mem_filter, Finset.mem_image]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro (rfl | ⟨hk, hk1, hk2⟩)
        · obtain ⟨u, hu1, hu2⟩ := hu; exact ⟨⟨u, hu1, hu2.symm⟩, by omega, hv⟩
        · exact ⟨hk, by omega, hk2⟩
      · rintro ⟨hk, hk1, hk2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk1 with hk1 | rfl
        · exact Or.inr ⟨hk, hk1, hk2⟩
        · exact Or.inl rfl
    · rw [decide_eq_true_eq] at hu
      push Not at hu
      rw [Finset.mem_filter, Finset.mem_image]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hk, hk1, hk2⟩; exact ⟨hk, by omega, hk2⟩
      · rintro ⟨⟨u, hu1, rfl⟩, hk1, hk2⟩
        refine ⟨⟨u, hu1, rfl⟩, ?_, hk2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hk1 with hk1 | hk1
        · exact hk1
        · exact absurd hk1.symm (hu u hu1)

omit [DecidableEq V] in
/-- Inside communication phase `p`, the phase-level state is frozen and the heard slots accumulate. -/
theorem beepRun_inPhase {p : ℕ}
    (h0 : ∀ v, beepRun G ident (commLen * p) v = ⟨alpha (ident v), run G .maxDelete ident p v, 0, ∅⟩) :
    ∀ r < commLen, ∀ v, beepRun G ident (commLen * p + r) v =
      ⟨alpha (ident v), run G .maxDelete ident p v, r, heardAt G ident p r v⟩ := by
  intro r
  induction r with
  | zero =>
    intro _ v
    rw [Nat.add_zero, h0 v]
    congr 1
    simp [heardAt]
  | succ r ih =>
    intro hr v
    rw [← Nat.add_assoc, beepRun_round G ident (ih (by omega)) v]
    simp only [endRound, hr, ↓reduceIte]

/-- At the end of a communication phase, the decoded set equals the set of received pairs, up to the
node's own pair. -/
theorem decode_heardAt (p : ℕ) (v : V) :
    (heardAt G ident p commLen v).image (decode (run G .maxDelete ident p v).pre) =
      (received G (run G .maxDelete ident p) v).filter
        fun m => encode m ≠ ownSlot (run G .maxDelete ident p v) := by
  ext m
  simp only [heardAt, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    mem_received]
  constructor
  · rintro ⟨k, ⟨⟨u, hu, rfl⟩, -, hne⟩, rfl⟩
    rw [ownSlot, decode_encode (lemma_1 G ident p hu)]
    exact ⟨⟨u, hu, rfl⟩, hne⟩
  · rintro ⟨⟨u, hu, rfl⟩, hne⟩
    exact ⟨_, ⟨⟨u, hu, rfl⟩, encode_lt _, hne⟩, decode_encode (lemma_1 G ident p hu) _⟩

/-- The update at the end of a communication phase is the phase-level update of Algorithm 1. -/
theorem ruleStep_heardAt (p : ℕ) (v : V) :
    ruleStep .maxDelete (alpha (ident v)) (run G .maxDelete ident p v)
        ((heardAt G ident p commLen v).image (decode (run G .maxDelete ident p v).pre)) =
      run G .maxDelete ident (p + 1) v := by
  rw [decode_heardAt, run_succ]
  apply ruleStep_filter_self
  intro m hm hne
  push Not at hne
  obtain ⟨u, hu, rfl⟩ := (mem_received G).1 hm
  have := encode_inj (lemma_1 G ident p hu) (lemma1Holds_self _) hne
  exact congrArg Prod.fst this

/-- **Section 3.1.3** (simulation): at round `1664 · p` (the start of the `p`-th communication phase),
every node's beep-level state carries exactly the phase-level state of Algorithm 1 after `p` diffusion
phases; slot and heard set are reset. -/
theorem beepRun_phase (p : ℕ) (v : V) :
    beepRun G ident (commLen * p) v = ⟨alpha (ident v), run G .maxDelete ident p v, 0, ∅⟩ := by
  induction p generalizing v with
  | zero => rfl
  | succ p ih =>
    have hin := beepRun_inPhase G ident ih
    have : commLen * (p + 1) = commLen * p + (commLen - 1) + 1 := by unfold commLen; ring
    rw [this, beepRun_round G ident (hin _ (by unfold commLen; omega)) v,
      show commLen - 1 + 1 = commLen by rfl]
    simp only [endRound, show ¬ (commLen - 1 + 1 < commLen) by decide, ↓reduceIte,
      ruleStep_heardAt]

/-- **Section 3.1.3** (simulation, every round): at round `t`, the phase-level part of every node's
state is the state of Algorithm 1 after `⌊t / 1664⌋` diffusion phases. -/
theorem beepRun_s (t : ℕ) (v : V) :
    (beepRun G ident t v).s = run G .maxDelete ident (t / commLen) v := by
  have ht : t = commLen * (t / commLen) + t % commLen := (Nat.div_add_mod t commLen).symm
  rw [ht, beepRun_inPhase G ident (beepRun_phase G ident _) _ (Nat.mod_lt _ (by decide)),
    ← ht]

theorem beepRun_Y (t : ℕ) (v : V) : (beepRun G ident t v).Y = alpha (ident v) := by
  have ht : t = commLen * (t / commLen) + t % commLen := (Nat.div_add_mod t commLen).symm
  rw [ht, beepRun_inPhase G ident (beepRun_phase G ident _) _ (Nat.mod_lt _ (by decide))]

/-- **Theorem 3** of [Dufoulon–Burman–Beauquier, DISC 2018] (with the repaired rule priority,
`Priority.maxDelete`): Algorithm 1 solves uniform eventual leader election in the beeping model.
Let `G` be connected, the identifiers be unique and `l` the node with the maximum identifier `X`.
From round `1664 · (|α(X)| + 2D)` on (`D` the diameter), every node has `prefix = α(X)` and outputs
`leaderId = α⁻¹(prefix) = X`, and `l` is the unique candidate and the unique leader. -/
theorem theorem_3 (hconn : G.Connected) (hinj : Function.Injective ident) {l : V}
    (hmax : ∀ v, ident v ≤ ident l) {t : ℕ}
    (ht : commLen * ((alpha (ident l)).length + 2 * G.diam) ≤ t) :
    (∀ v, (beepRun G ident t v).s.pre = alpha (ident l)) ∧
    (∀ v, (beepRun G ident t v).leaderId = some (ident l)) ∧
    (∀ v, (beepRun G ident t v).s.cand = true ↔ v = l) ∧
    (∀ v, (beepRun G ident t v).isLeader ↔ v = l) := by
  have hp : (alpha (ident l)).length + 2 * G.diam ≤ t / commLen :=
    (Nat.le_div_iff_mul_le (by decide)).2 (by rw [mul_comm]; exact ht)
  obtain ⟨h1, h2, h3, h4⟩ := theorem_3_phases G ident hconn hinj hmax hp
  refine ⟨fun v => by rw [beepRun_s]; exact h1 v, fun v => by
    rw [BState.leaderId, beepRun_s]; exact h2 v, fun v => by rw [beepRun_s]; exact h3 v,
    fun v => ?_⟩
  rw [BState.isLeader, beepRun_s, beepRun_Y]
  exact h4 v

/-- `|α(X)| ≤ 2⌊log₂ X⌋ + 3` for every `X` (with equality for `X > 0`). -/
theorem alpha_length_le_log (X : ℕ) : (alpha X).length ≤ 2 * Nat.log 2 X + 3 := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [alpha, bin]
  · rw [alpha_length_le hX]

/-- **Theorem 3** of [Dufoulon–Burman–Beauquier, DISC 2018], explicit round bound: from round
`1664 · (2⌊log₂ X⌋ + 3 + 2D)` on, every node has `prefix = α(X)` and `leaderId = X`, and the
maximum-identifier node `l` is the unique candidate and the unique leader. Since `X ≤ N`, this is
`O(D + log N)` rounds. -/
theorem theorem_3_log (hconn : G.Connected) (hinj : Function.Injective ident) {l : V}
    (hmax : ∀ v, ident v ≤ ident l) {t : ℕ}
    (ht : 1664 * (2 * Nat.log 2 (ident l) + 3 + 2 * G.diam) ≤ t) :
    (∀ v, (beepRun G ident t v).s.pre = alpha (ident l)) ∧
    (∀ v, (beepRun G ident t v).leaderId = some (ident l)) ∧
    (∀ v, (beepRun G ident t v).s.cand = true ↔ v = l) ∧
    (∀ v, (beepRun G ident t v).isLeader ↔ v = l) :=
  theorem_3 G ident hconn hinj hmax (le_trans (by
    unfold commLen
    have := alpha_length_le_log (ident l)
    omega) ht)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- The bound of `theorem_3_log` in terms of an upper bound `N` on the identifiers:
`1664 · (2⌊log₂ X⌋ + 3 + 2D) ≤ 1664 · (2⌊log₂ N⌋ + 3 + 2D)`, i.e. `O(D + log N)` rounds. -/
theorem theorem_3_round_bound {l : V} {N : ℕ} (hN : ident l ≤ N) :
    1664 * (2 * Nat.log 2 (ident l) + 3 + 2 * G.diam) ≤ 1664 * (2 * Nat.log 2 N + 3 + 2 * G.diam) := by
  have := Nat.log_mono_right (b := 2) hN
  omega

end Network

end Podc.BeepingLeaderElection
