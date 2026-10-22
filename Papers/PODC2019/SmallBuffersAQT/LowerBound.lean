import Mathlib
import Podc.Computability.Distributed.AQT.Basic

/-!
# The lower bound on buffer space (Theorem 5.1 of [MPR19])

[MPR19] A. Miller, B. Patt-Shamir, W. Rosenbaum, *With Great Speed Come Small Buffers:
Space-Bandwidth Tradeoffs for Routing*, PODC 2019 (arXiv 1902.08069).

Theorem 5.1: for every `ρ > 1/(ℓ+1)` there is a `(ρ, 1)`-bounded adversary on a path with
`n ≈ (ℓ+1) m^ℓ` nodes such that *every* forwarding protocol needs buffers of size
`Ω(((ℓ+1)ρ - 1) m / (ℓ+1))`.

## Model

* The network is the directed path `0 → 1 → ⋯`. A `Packet` has an injection round, a source and a
  destination. A finite packet family `P : ι → Packet` is an (offline) injection pattern; its
  count function `counts P` is used to state `(ρ, σ)`-boundedness with `Cslib.AQT.IsBounded`.
* An `Execution P` is an arbitrary (offline, centralized, possibly clairvoyant) forwarding
  protocol: `pos t p` is the node holding `p` in round `t` (after injections, before forwarding);
  in each round a packet either stays or moves one hop towards its destination, and every edge
  carries at most one packet per round. A packet at its destination is delivered and occupies no
  buffer (`Execution.load`).

## The adversary (`lbAdv`)

Rounds are grouped into phases of `m` rounds; the phase of round `t` is `P = t / m`, whose
base-`m` digits are the paper's `t_ℓ … t_1` (`digit m P j = t_j`). The paper's sites are
`v_i = ∑_{j=i}^{ℓ} ((j+1) m^j - (t_j+1) j m^{j-1})` (`site`, with `term_eq`), and
`v_0 = (ℓ+1) m^ℓ` is the last node (the paper writes `n`; with `n = (ℓ+1) m^ℓ` nodes this is off
by one, so the path here has `(ℓ+1) m^ℓ + 1` nodes). In every round `t < (m-1) m^ℓ` with
`⌊ρ (t+1)⌋ ≠ ⌊ρ t⌋` (`jump`), one packet of each type `r = 0, …, ℓ` is injected at `v_{r+1}` with
destination `v_r`; this makes precise the paper's informal "inject `ρm` packets per phase".
The adversary is `(ρ, 1)`-bounded (`lbAdv_isBounded`) since the `ℓ+1` routes of a round are
disjoint.

## Proof

`front ℓ m t = v_1(t/m)` is the paper's `F(t)`. A packet is *fresh* in round `t` if it is at a
node `≤ F(t)`. Claim 3 (`claim3`) and its consequence `site_one_lt` show Lemma 5.3
(`lemma_5_3`): a packet that has reached its destination is to the right of `F` (so fresh packets
are undelivered). Lemma 5.2/5.4 (`becomeStale_pos`, `card_becomeStale_le_one`,
`card_becomeStale_le_sum_load`): a packet that becomes stale at the end of round `t` lies in
`[F(t+1), F(t)]` in round `t`, and if `F` does not move, at most one packet becomes stale; the
paper's length of that interval, `F(t) - F(t+1) = ∑_{j=0}^{k} m^j`, is `lemma_5_4_drop` (not
needed below).

Instead of the dichotomy of Lemma 5.5 we use a global telescoping count
(`Execution.card_injected_le_real`): with `L` the maximal load, at most
`1 + 2 L (F(t) - F(t+1))` packets become stale at the end of round `t`, which sums to
`T + 2 L F(0)`; the fresh packets at the end are at most `(F(T)+1) L`. Comparing with the
`(ℓ+1) ⌊ρ T⌋` injected packets gives `exists_load_ge`, which implies the paper's bound
(`lower_bound`, `theorem_5_1`).
-/

namespace Podc.SmallBuffersAQT.LowerBound

open Finset

/-- A packet on the path: injection round, source node, destination node. -/
structure Packet where
  /-- injection round -/
  time : ℕ
  /-- source node -/
  src : ℕ
  /-- destination node -/
  dst : ℕ
  deriving DecidableEq

/-- The count function of a finite packet family (number of packets injected in round `t` at
node `a` with destination `b`), to state `(ρ, σ)`-boundedness with `Cslib.AQT.IsBounded`. -/
def counts {ι : Type*} [Fintype ι] (P : ι → Packet) : ℕ → ℕ → ℕ → ℕ :=
  fun t a b => #{p | P p = ⟨t, a, b⟩}

/-- An execution of an arbitrary forwarding protocol on the path for the packet family `P`:
`pos t p` is the node holding `p` in round `t` (state after injection, before forwarding); it is
meaningful for `t ≥ (P p).time`. In each round a packet stays or moves one hop towards its
destination, and at most one packet is forwarded over each edge `(v, v+1)`. -/
structure Execution {ι : Type*} [Fintype ι] (P : ι → Packet) where
  /-- position of packet `p` in round `t` -/
  pos : ℕ → ι → ℕ
  pos_time : ∀ p, pos (P p).time p = (P p).src
  step : ∀ p t, (P p).time ≤ t →
    pos (t + 1) p = pos t p ∨ (pos t p < (P p).dst ∧ pos (t + 1) p = pos t p + 1)
  cap : ∀ t v, #{p | (P p).time ≤ t ∧ pos t p = v ∧ pos (t + 1) p = v + 1} ≤ 1

variable {ι : Type*} [Fintype ι] {P : ι → Packet}

namespace Execution

/-- Buffer occupancy of node `v` in round `t` (delivered packets do not count). -/
def load (E : Execution P) (t v : ℕ) : ℕ :=
  #{p | (P p).time ≤ t ∧ E.pos t p = v ∧ v < (P p).dst}

/-- The idle protocol (never forward anything) is an execution: executions exist. -/
def idle (P : ι → Packet) : Execution P where
  pos _ p := (P p).src
  pos_time _ := rfl
  step _ _ _ := Or.inl rfl
  cap t v := by
    rw [Nat.le_one_iff_eq_zero_or_eq_one]; left
    rw [card_eq_zero, filter_eq_empty_iff]
    rintro p - ⟨-, h1, h2⟩
    omega

variable (E : Execution P)

lemma pos_succ_le {p : ι} {t : ℕ} (h : (P p).time ≤ t) : E.pos (t + 1) p ≤ E.pos t p + 1 := by
  rcases E.step p t h with h' | ⟨_, h'⟩ <;> omega

lemma pos_le_src_add (p : ι) : ∀ n, E.pos ((P p).time + n) p ≤ (P p).src + n
  | 0 => by simp [E.pos_time]
  | n + 1 => by
    have h1 := E.pos_succ_le (p := p) (t := (P p).time + n) (by omega)
    have h2 := pos_le_src_add p n
    rw [← add_assoc]
    omega

/-- A packet moves at most one hop per round. -/
lemma pos_le_src_add_of_le {p : ι} {t : ℕ} (h : (P p).time ≤ t) :
    E.pos t p ≤ (P p).src + (t - (P p).time) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  simpa using E.pos_le_src_add p n

lemma pos_le_dst_aux {p : ι} (hsd : (P p).src ≤ (P p).dst) :
    ∀ n, E.pos ((P p).time + n) p ≤ (P p).dst
  | 0 => by simp [E.pos_time, hsd]
  | n + 1 => by
    have h2 := pos_le_dst_aux hsd n
    rw [← add_assoc]
    rcases E.step p ((P p).time + n) (by omega) with h' | ⟨h1, h'⟩ <;> omega

/-- A packet never overshoots its destination. -/
lemma pos_le_dst {p : ι} {t : ℕ} (hsd : (P p).src ≤ (P p).dst) (h : (P p).time ≤ t) :
    E.pos t p ≤ (P p).dst := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  exact E.pos_le_dst_aux hsd n

/-! ### Counting fresh and stale packets, for an arbitrary "front" `F` -/

variable (F : ℕ → ℕ)

/-- Packets fresh in round `t`: injected and at a node `≤ F t`. -/
def fresh (t : ℕ) : Finset ι := {p | (P p).time ≤ t ∧ E.pos t p ≤ F t}

/-- Packets stale in round `t`: injected and at a node `> F t`. -/
def stale (t : ℕ) : Finset ι := {p | (P p).time ≤ t ∧ F t < E.pos t p}

/-- Packets that become stale at the end of round `t`. -/
def becomeStale (t : ℕ) : Finset ι :=
  {p | (P p).time ≤ t ∧ E.pos t p ≤ F t ∧ F (t + 1) < E.pos (t + 1) p}

/-- Undelivered packets of round `t` located in `I` are counted by the loads of the nodes of `I`. -/
lemma card_le_sum_load {t : ℕ} {s : Finset ι} {I : Finset ℕ}
    (h : ∀ p ∈ s, (P p).time ≤ t ∧ E.pos t p ∈ I ∧ E.pos t p < (P p).dst) :
    #s ≤ ∑ v ∈ I, E.load t v := by
  rw [card_eq_sum_card_fiberwise (f := E.pos t) (fun p hp => (h p hp).2.1)]
  refine sum_le_sum fun v _ => ?_
  unfold load
  refine card_le_card fun p hp => ?_
  simp only [mem_filter, mem_univ, true_and] at hp ⊢
  obtain ⟨hps, rfl⟩ := hp
  exact ⟨(h p hps).1, rfl, (h p hps).2.2⟩

/-- Lemma 5.2 of [MPR19] (form used here): a packet that becomes stale at the end of round `t`
is in `[F(t+1), F(t)]` in round `t`. -/
lemma becomeStale_pos {t : ℕ} {p : ι} (hp : p ∈ E.becomeStale F t) :
    F (t + 1) ≤ E.pos t p ∧ E.pos t p ≤ F t := by
  simp only [becomeStale, mem_filter, mem_univ, true_and] at hp
  have := E.pos_succ_le hp.1
  omega

/-- Lemma 5.2 (1) and Lemma 5.4 (α-stale packets) of [MPR19]: if `F` does not decrease in round
`t`, a packet becomes stale only by being forwarded from node `F t`, so at most one packet becomes
stale. -/
lemma card_becomeStale_le_one {t : ℕ} (hF : F t ≤ F (t + 1)) : #(E.becomeStale F t) ≤ 1 := by
  refine (card_le_card ?_).trans (E.cap t (F t))
  intro p hp
  simp only [becomeStale, mem_filter, mem_univ, true_and] at hp ⊢
  have := E.pos_succ_le hp.1
  exact ⟨hp.1, by omega, by omega⟩

/-- Lemma 5.4 (β-stale packets) of [MPR19], corrected: the packets that become stale at the end
of round `t` are counted by the loads of `[F(t+1), F(t)]` **in round `t`** (the paper uses round
`t+1`, where such a packet may already have been delivered). Needs that fresh packets are
undelivered (Lemma 5.3). -/
lemma card_becomeStale_le_sum_load {t : ℕ}
    (hund : ∀ p, (P p).time ≤ t → E.pos t p ≤ F t → E.pos t p < (P p).dst) :
    #(E.becomeStale F t) ≤ ∑ v ∈ Icc (F (t + 1)) (F t), E.load t v := by
  refine E.card_le_sum_load fun p hp => ?_
  have h2 := E.becomeStale_pos F hp
  simp only [becomeStale, mem_filter, mem_univ, true_and] at hp
  exact ⟨hp.1, mem_Icc.2 h2, hund p hp.1 hp.2.1⟩

lemma stale_succ_subset [DecidableEq ι] (hinj : ∀ p, (P p).src ≤ F (P p).time) (t : ℕ) :
    E.stale F (t + 1) ⊆ E.becomeStale F t ∪ E.stale F t := by
  intro p hp
  simp only [stale, becomeStale, mem_union, mem_filter, mem_univ, true_and] at hp ⊢
  rcases Nat.lt_or_ge t (P p).time with h | h
  · have ht : (P p).time = t + 1 := by omega
    have h1 := E.pos_time p
    have h2 := hinj p
    rw [ht] at h1 h2
    omega
  · by_cases hf : E.pos t p ≤ F t
    · exact Or.inl ⟨h, hf, hp.2⟩
    · exact Or.inr ⟨h, by omega⟩

lemma card_stale_le (hinj : ∀ p, (P p).src ≤ F (P p).time) :
    ∀ T, #(E.stale F T) ≤ ∑ t ∈ range T, #(E.becomeStale F t)
  | 0 => by
    simp only [range_zero, sum_empty, Nat.le_zero, card_eq_zero, filter_eq_empty_iff, stale,
      mem_univ, true_implies, not_and, not_lt]
    intro p hp
    have h0 : (P p).time = 0 := by omega
    have h1 := E.pos_time p
    have h2 := hinj p
    rw [h0] at h1 h2
    omega
  | T + 1 => by
    classical
    rw [sum_range_succ]
    have := card_stale_le hinj T
    calc #(E.stale F (T + 1)) ≤ #(E.becomeStale F T ∪ E.stale F T) :=
          card_le_card (E.stale_succ_subset F hinj T)
      _ ≤ #(E.becomeStale F T) + #(E.stale F T) := card_union_le _ _
      _ ≤ _ := by omega

/-- Every injected packet is fresh or became stale in some earlier round. -/
lemma card_injected_le (hinj : ∀ p, (P p).src ≤ F (P p).time) (T : ℕ) :
    #{p | (P p).time ≤ T} ≤ #(E.fresh F T) + ∑ t ∈ range T, #(E.becomeStale F t) := by
  classical
  have h1 : #{p | (P p).time ≤ T} ≤ #(E.fresh F T ∪ E.stale F T) := by
    refine card_le_card fun p hp => ?_
    simp only [fresh, stale, mem_union, mem_filter, mem_univ, true_and] at hp ⊢
    by_cases h : E.pos T p ≤ F T
    · exact Or.inl ⟨hp, h⟩
    · exact Or.inr ⟨hp, by omega⟩
  have := card_union_le (E.fresh F T) (E.stale F T)
  have := E.card_stale_le F hinj T
  omega

/-- The counting core of the lower bound (replacing Lemma 5.5 of [MPR19] by a telescoping
argument). Assume every packet is fresh at injection, `F` is non-increasing up to round `T`,
fresh packets are undelivered (Lemma 5.3), and all loads up to round `T` are at most `L`. Then at
most `T + L (2 F(0) + 1)` packets are injected up to round `T`. -/
theorem card_injected_le_real {T : ℕ} (hinj : ∀ p, (P p).src ≤ F (P p).time)
    (hF : ∀ t < T, F (t + 1) ≤ F t)
    (hund : ∀ t ≤ T, ∀ p, (P p).time ≤ t → E.pos t p ≤ F t → E.pos t p < (P p).dst)
    {L : ℝ} (hL : ∀ t ≤ T, ∀ v, (E.load t v : ℝ) ≤ L) :
    (#{p | (P p).time ≤ T} : ℝ) ≤ T + L * (2 * F 0 + 1) := by
  have hL0 : 0 ≤ L := (Nat.cast_nonneg _).trans (hL 0 (Nat.zero_le _) 0)
  have h1 := E.card_injected_le F hinj T
  have hfresh : (#(E.fresh F T) : ℝ) ≤ (F T + 1) * L := by
    have h : #(E.fresh F T) ≤ ∑ v ∈ range (F T + 1), E.load T v := by
      refine E.card_le_sum_load fun p hp => ?_
      simp only [fresh, mem_filter, mem_univ, true_and] at hp
      exact ⟨hp.1, mem_range.2 (Nat.lt_succ_of_le hp.2), hund T le_rfl p hp.1 hp.2⟩
    calc (#(E.fresh F T) : ℝ) ≤ ∑ v ∈ range (F T + 1), (E.load T v : ℝ) := by exact_mod_cast h
      _ ≤ ∑ v ∈ range (F T + 1), L := sum_le_sum fun v _ => hL T le_rfl v
      _ = _ := by simp
  have hstep : ∀ t ∈ range T,
      (#(E.becomeStale F t) : ℝ) ≤ 1 + 2 * L * ((F t : ℝ) - F (t + 1)) := by
    intro t ht
    rw [mem_range] at ht
    rcases (hF t ht).lt_or_eq with hlt | heq
    · have hs := E.card_becomeStale_le_sum_load F (t := t)
        (fun p h1 h2 => hund t ht.le p h1 h2)
      have h2 : (#(E.becomeStale F t) : ℝ) ≤ ((F t + 1 - F (t + 1) : ℕ) : ℝ) * L := by
        calc (#(E.becomeStale F t) : ℝ) ≤ ∑ v ∈ Icc (F (t + 1)) (F t), (E.load t v : ℝ) := by
              exact_mod_cast hs
          _ ≤ ∑ v ∈ Icc (F (t + 1)) (F t), L := sum_le_sum fun v _ => hL t ht.le v
          _ = _ := by simp [Nat.card_Icc]
      have hc : ((F t + 1 - F (t + 1) : ℕ) : ℝ) ≤ 2 * ((F t : ℝ) - F (t + 1)) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        have : (F (t + 1) : ℝ) + 1 ≤ F t := by exact_mod_cast hlt
        linarith
      nlinarith
    · have := E.card_becomeStale_le_one F (t := t) heq.ge
      rw [heq, sub_self, mul_zero, add_zero]
      exact_mod_cast this
  have htel : ∑ t ∈ range T, ((F t : ℝ) - F (t + 1)) = F 0 - F T :=
    sum_range_sub' (fun t => (F t : ℝ)) T
  have hsum : ∑ t ∈ range T, (1 + 2 * L * ((F t : ℝ) - F (t + 1))) = T + 2 * L * (F 0 - F T) := by
    rw [sum_add_distrib, ← mul_sum, htel]
    simp
  have hFT : (0 : ℝ) ≤ L * F T := mul_nonneg hL0 (Nat.cast_nonneg _)
  calc (#{p | (P p).time ≤ T} : ℝ)
      ≤ #(E.fresh F T) + ∑ t ∈ range T, (#(E.becomeStale F t) : ℝ) := by exact_mod_cast h1
    _ ≤ (F T + 1) * L + ∑ t ∈ range T, (1 + 2 * L * ((F t : ℝ) - F (t + 1))) :=
        add_le_add hfresh (sum_le_sum hstep)
    _ = (F T + 1) * L + (T + 2 * L * (F 0 - F T)) := by rw [hsum]
    _ ≤ T + L * (2 * F 0 + 1) := by nlinarith

end Execution

/-! ### The adversary -/

section Adversary

variable {ℓ m : ℕ}

/-- The paper's digit `t_j` (`j ≥ 1`) of a round in phase `P`: the base-`m` digit `j - 1` of the
phase number `P`. -/
def digit (m P j : ℕ) : ℕ := P / m ^ (j - 1) % m

/-- The `j`-th summand of the sites; equal to the paper's `(j+1) m^j - (t_j + 1) j m^(j-1)`
(`term_eq`), written without truncated subtraction. -/
def term (m P j : ℕ) : ℕ := m ^ j + (m - 1 - digit m P j) * j * m ^ (j - 1)

/-- The sites of phase `P`: `site ℓ m P i = v_i` for `1 ≤ i ≤ ℓ` (paper), `site ℓ m P (ℓ+1) = 0`,
and `site ℓ m P 0 = (ℓ+1) m^ℓ` is the last node of the path (the paper's destination `n`). -/
def site (ℓ m P i : ℕ) : ℕ := if i = 0 then (ℓ + 1) * m ^ ℓ else ∑ j ∈ Ico i (ℓ + 1), term m P j

/-- The paper's `F(t) = v_1(t_ℓ ⋯ t_1)`: the right-most injection site in round `t`. -/
def front (ℓ m t : ℕ) : ℕ := site ℓ m (t / m) 1

/-- Length of the injection period: `(m - 1) m^ℓ` rounds (phases `0, …, (m-1) m^(ℓ-1) - 1`, i.e.
the paper's `t_ℓ ∈ {0, …, m-2}`). -/
def horizon (ℓ m : ℕ) : ℕ := (m - 1) * m ^ ℓ

/-- Round `t` is an injection round iff `⌊ρ (t+1)⌋ ≠ ⌊ρ t⌋`. -/
def jump (ρ : ℝ) (t : ℕ) : Prop := ⌊ρ * ((t : ℝ) + 1)⌋₊ ≠ ⌊ρ * t⌋₊

noncomputable instance (ρ : ℝ) : DecidablePred (jump ρ) :=
  fun _ => inferInstanceAs (Decidable (_ ≠ _))

/-- Packets of the adversary: a type `r ∈ {0, …, ℓ}` and an injection round `t < horizon ℓ m`
with `jump ρ t`. -/
abbrev LBIndex (ℓ m : ℕ) (ρ : ℝ) := {x : Fin (ℓ + 1) × Fin (horizon ℓ m) // jump ρ x.2}

/-- The adversary of Theorem 5.1 of [MPR19]: in every injection round `t`, a packet of each type
`r ∈ {0, …, ℓ}` is injected at `v_{r+1}(t/m)` with destination `v_r(t/m)` (type `r` here is the
paper's type `r + 1`; type `ℓ` is injected at node `0 = v_{ℓ+1}`). -/
def lbAdv (ℓ m : ℕ) (ρ : ℝ) (x : LBIndex ℓ m ρ) : Packet :=
  ⟨x.1.2, site ℓ m ((x.1.2 : ℕ) / m) ((x.1.1 : ℕ) + 1), site ℓ m ((x.1.2 : ℕ) / m) x.1.1⟩

lemma digit_lt (hm : 0 < m) (P j : ℕ) : digit m P j < m := Nat.mod_lt _ hm

lemma term_eq (hm : 0 < m) (P : ℕ) {j : ℕ} (hj : 1 ≤ j) :
    (term m P j : ℤ) = (j + 1) * m ^ j - (digit m P j + 1) * j * m ^ (j - 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hd := digit_lt hm P (1 + j)
  unfold term
  rw [Nat.sub_sub, Nat.add_sub_cancel_left]
  push_cast [Nat.cast_sub (show 1 + digit m P (1 + j) ≤ m by omega)]
  ring

lemma pow_le_term (m P j : ℕ) : m ^ j ≤ term m P j := Nat.le_add_right _ _

lemma term_le (m P j : ℕ) : term m P j ≤ m ^ j + (m - 1) * j * m ^ (j - 1) := by
  unfold term
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.sub_le _ _))) _

/-- `∑_{j=1}^{K} ((j+1) m^j - j m^(j-1)) = (K+1) m^K - 1`. -/
lemma sum_termMax (hm : 0 < m) (K : ℕ) :
    ∑ j ∈ Ico 1 (K + 1), (m ^ j + (m - 1) * j * m ^ (j - 1)) + 1 = (K + 1) * m ^ K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_Ico_succ_top (by omega : 1 ≤ K + 1), add_right_comm, ih]
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring

lemma site_zero (P : ℕ) : site ℓ m P 0 = (ℓ + 1) * m ^ ℓ := by simp [site]

lemma site_of_ne_zero (P : ℕ) {i : ℕ} (hi : i ≠ 0) :
    site ℓ m P i = ∑ j ∈ Ico i (ℓ + 1), term m P j := by simp [site, hi]

lemma site_one_add_one_le (hm : 0 < m) (P : ℕ) : site ℓ m P 1 + 1 ≤ (ℓ + 1) * m ^ ℓ := by
  rw [site_of_ne_zero P one_ne_zero, ← sum_termMax hm ℓ]
  have := sum_le_sum (s := Ico 1 (ℓ + 1)) fun j _ => term_le m P j
  omega

lemma site_succ (P : ℕ) {i : ℕ} (hi : 1 ≤ i) (hiℓ : i ≤ ℓ) :
    site ℓ m P i = term m P i + site ℓ m P (i + 1) := by
  rw [site_of_ne_zero P (by omega), site_of_ne_zero P (by omega),
    sum_eq_sum_Ico_succ_bot (by omega)]

/-- The sites are non-increasing in the index. -/
lemma site_anti (hm : 0 < m) (P : ℕ) {i i' : ℕ} (h : i ≤ i') : site ℓ m P i' ≤ site ℓ m P i := by
  have hpos : ∀ {i i'}, 1 ≤ i → i ≤ i' → site ℓ m P i' ≤ site ℓ m P i := by
    intro i i' hi h
    rw [site_of_ne_zero P (by omega), site_of_ne_zero P (by omega)]
    exact sum_le_sum_of_subset (Ico_subset_Ico_left h)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rcases Nat.eq_zero_or_pos i' with rfl | hi'
    · exact le_rfl
    · have h1 := hpos le_rfl hi'
      have h2 := site_one_add_one_le (ℓ := ℓ) hm P
      rw [site_zero]
      omega
  · exact hpos hi h

/-- Routes are non-empty: `v_{r+1} < v_r`. -/
lemma site_succ_lt (hm : 0 < m) (P : ℕ) {r : ℕ} (hr : r ≤ ℓ) :
    site ℓ m P (r + 1) < site ℓ m P r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · have := site_one_add_one_le (ℓ := ℓ) hm P
    rw [site_zero, Nat.zero_add]
    omega
  · rw [site_succ P hr0 hr]
    have := pow_le_term m P r
    have := pow_pos hm r
    omega

/-- Claim 3 of [MPR19] (in terms of phases): if the phases `P` and `P'` agree in the digits
`t_ℓ, …, t_{k+1}` and `t'_k > t_k`, then `F` in phase `P'` is left of `v_k` of phase `P`. -/
theorem claim3 (hm : 0 < m) {k P P' : ℕ} (hk : 1 ≤ k) (hkℓ : k ≤ ℓ)
    (hq : P' / m ^ k = P / m ^ k) (hd : digit m P k < digit m P' k) :
    site ℓ m P' 1 < site ℓ m P k := by
  have hhi : ∑ j ∈ Ico (k + 1) (ℓ + 1), term m P' j = ∑ j ∈ Ico (k + 1) (ℓ + 1), term m P j := by
    refine sum_congr rfl fun j hj => ?_
    rw [mem_Ico] at hj
    have : P' / m ^ (j - 1) = P / m ^ (j - 1) := by
      have e : m ^ (j - 1) = m ^ k * m ^ (j - 1 - k) := by rw [← pow_add]; congr 1; omega
      rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hq]
    simp only [term, digit, this]
  have hlo : ∑ j ∈ Ico 1 k, term m P' j + 1 ≤ k * m ^ (k - 1) := by
    have h1 := sum_termMax hm (k - 1)
    rw [Nat.sub_add_cancel hk] at h1
    have h2 := sum_le_sum (s := Ico 1 k) fun j _ => term_le m P' j
    omega
  have hmid : term m P' k + k * m ^ (k - 1) ≤ term m P k := by
    have hd' := digit_lt hm P' k
    unfold term
    have h3 : (m - 1 - digit m P' k + 1) * (k * m ^ (k - 1)) ≤
        (m - 1 - digit m P k) * (k * m ^ (k - 1)) := Nat.mul_le_mul_right _ (by omega)
    rw [add_mul, one_mul, ← mul_assoc, ← mul_assoc] at h3
    omega
  rw [site_of_ne_zero P' one_ne_zero, site_of_ne_zero P (by omega),
    ← sum_Ico_consecutive _ hk (by omega : k ≤ ℓ + 1),
    sum_eq_sum_Ico_succ_bot (by omega : k < ℓ + 1),
    sum_eq_sum_Ico_succ_bot (by omega : k < ℓ + 1), hhi]
  omega

/-- Consequence of Claim 3: if phase `P'` is at least `m^(r-1)` phases after `P` (and
`P' < m^ℓ`), then `F` in phase `P'` is strictly left of `v_r` of phase `P`. -/
theorem site_one_lt (hm : 0 < m) {r P P' : ℕ} (hr : 1 ≤ r)
    (hPP' : P + m ^ (r - 1) ≤ P') (hP' : P' < m ^ ℓ) : site ℓ m P' 1 < site ℓ m P r := by
  classical
  have hpos : ∀ i, 0 < m ^ i := fun i => pow_pos hm i
  have hP : P < m ^ ℓ := by have := hpos (r - 1); omega
  have hex : ∃ k, P' / m ^ k = P / m ^ k :=
    ⟨ℓ, by rw [Nat.div_eq_of_lt hP', Nat.div_eq_of_lt hP]⟩
  have hk : P' / m ^ Nat.find hex = P / m ^ Nat.find hex := Nat.find_spec hex
  have hkℓ : Nat.find hex ≤ ℓ :=
    Nat.find_min' hex (by rw [Nat.div_eq_of_lt hP', Nat.div_eq_of_lt hP])
  have hrk : r ≤ Nat.find hex := by
    by_contra hlt
    have e : m ^ (r - 1) = m ^ Nat.find hex * m ^ (r - 1 - Nat.find hex) := by
      rw [← pow_add]; congr 1; omega
    have hq : P' / m ^ (r - 1) = P / m ^ (r - 1) := by
      rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hk]
    have h1 := Nat.lt_div_mul_add (a := P') (hpos (r - 1))
    have h2 := Nat.div_mul_le_self P (m ^ (r - 1))
    rw [hq] at h1
    omega
  set k := Nat.find hex with hkdef
  have hk1 : 1 ≤ k := by omega
  have hne : P' / m ^ (k - 1) ≠ P / m ^ (k - 1) := Nat.find_min hex (by omega)
  have hdiv : ∀ Q, Q / m ^ (k - 1) / m = Q / m ^ k := fun Q => by
    rw [Nat.div_div_eq_div_mul, ← pow_succ, Nat.sub_add_cancel hk1]
  have hle : P / m ^ (k - 1) ≤ P' / m ^ (k - 1) := Nat.div_le_div_right (by omega)
  have hd : digit m P k < digit m P' k := by
    unfold digit
    have a1 := Nat.div_add_mod (P' / m ^ (k - 1)) m
    have a2 := Nat.div_add_mod (P / m ^ (k - 1)) m
    rw [hdiv] at a1 a2
    rw [hk] at a1
    generalize m * (P / m ^ k) = z at a1 a2
    omega
  exact (claim3 hm hk1 hkℓ hk hd).trans_le (site_anti hm P hrk)

lemma mul_sub_one_mod (hm : 0 < m) {x : ℕ} (hx : 1 ≤ x) : (x * m - 1) % m = m - 1 := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hx
  have e : (1 + x) * m - 1 = (m - 1) + m * x := by
    rw [add_mul, one_mul, mul_comm x m]
    omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- Lemma 5.4 of [MPR19], the length of the interval `[F(t+1)+1, F(t)]` (not needed for the
proof of `exists_load_ge`, verified for completeness): if the phase `P = q m^k + (m^k - 1)` has
its lowest `k` digits equal to `m - 1` and its digit `t_{k+1} = q mod m < m - 1` (with
`k + 1 ≤ ℓ`), then at the transition to phase `P + 1` the front `F` drops by
`∑_{j=0}^{k} m^j = 1 + m (m^k - 1)/(m - 1)`. -/
theorem lemma_5_4_drop (hm : 0 < m) {k q : ℕ} (hk : k + 1 ≤ ℓ) (hq : q % m < m - 1) :
    site ℓ m (q * m ^ k + (m ^ k - 1)) 1 =
      site ℓ m ((q + 1) * m ^ k) 1 + ∑ j ∈ range (k + 1), m ^ j := by
  set P := q * m ^ k + (m ^ k - 1) with hPdef
  set P1 := (q + 1) * m ^ k with hP1def
  have hpos : ∀ i, 0 < m ^ i := fun i => pow_pos hm i
  have hPk : P / m ^ k = q := by
    rw [hPdef, add_comm, Nat.add_mul_div_right _ _ (hpos k), Nat.div_eq_of_lt (by
      have := hpos k; omega), zero_add]
  have hP1k : P1 / m ^ k = q + 1 := Nat.mul_div_cancel _ (hpos k)
  have hq1 : (q + 1) / m = q / m := by
    have h1 := Nat.div_add_mod q m
    have : q + 1 = (q % m + 1) + m * (q / m) := by omega
    rw [this, Nat.add_mul_div_left _ _ hm, Nat.div_eq_of_lt (by omega), zero_add]
  have hqa : ∀ a, 1 ≤ a → (q + 1) / m ^ a = q / m ^ a := by
    intro a ha
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le ha
    rw [pow_add, pow_one, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hq1]
  -- digits above `k + 1` agree
  have hhigh : ∀ j ∈ Ico (k + 1 + 1) (ℓ + 1), term m P j = term m P1 j := by
    intro j hj
    rw [mem_Ico] at hj
    have e : m ^ (j - 1) = m ^ k * m ^ (j - 1 - k) := by rw [← pow_add]; congr 1; omega
    have : P / m ^ (j - 1) = P1 / m ^ (j - 1) := by
      rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hPk, hP1k, hqa _ (by omega)]
    simp only [term, digit, this]
  -- digit `k + 1`
  have hdk : digit m P (k + 1) = q % m := by simp [digit, hPk]
  have hdk1 : digit m P1 (k + 1) = q % m + 1 := by
    simp only [digit, Nat.add_sub_cancel, hP1k]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (a := 1) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hmidk : term m P (k + 1) = term m P1 (k + 1) + (k + 1) * m ^ k := by
    unfold term
    rw [hdk, hdk1, Nat.add_sub_cancel]
    have : m - 1 - q % m = (m - 1 - (q % m + 1)) + 1 := by omega
    rw [this, add_mul, add_mul, one_mul]
    ring
  -- low digits
  have hlow : ∀ j ∈ Ico 1 (k + 1), term m P j = m ^ j ∧
      term m P1 j = m ^ j + (m - 1) * j * m ^ (j - 1) := by
    intro j hj
    rw [mem_Ico] at hj
    have e : m ^ k = m ^ (k - j) * m * m ^ (j - 1) := by
      rw [← pow_succ, ← pow_add]; congr 1; omega
    have hd1 : digit m P1 j = 0 := by
      simp only [digit, hP1def, e, ← mul_assoc, Nat.mul_div_cancel _ (hpos (j - 1))]
      exact Nat.mul_mod_left _ _
    have hd : digit m P j = m - 1 := by
      have hPj : P / m ^ (j - 1) = (q + 1) * m ^ (k - j) * m - 1 := by
        have h1 : P + 1 = ((q + 1) * m ^ (k - j) * m) * m ^ (j - 1) := by
          rw [hPdef, mul_assoc, mul_assoc, ← mul_assoc (m ^ (k - j)), ← e]
          have := hpos k
          rw [add_mul, one_mul]
          omega
        have h2 : 0 < (q + 1) * m ^ (k - j) * m := by
          have := hpos (k - j); positivity
        have h3 : P = ((q + 1) * m ^ (k - j) * m - 1) * m ^ (j - 1) + (m ^ (j - 1) - 1) := by
          have := hpos (j - 1)
          rw [Nat.sub_mul, one_mul, ← h1]
          have : m ^ (j - 1) ≤ P + 1 := by
            rw [h1]; exact Nat.le_mul_of_pos_left _ h2
          omega
        rw [h3, add_comm, Nat.add_mul_div_right _ _ (hpos (j - 1)),
          Nat.div_eq_of_lt (by have := hpos (j - 1); omega), zero_add]
      simp only [digit]
      rw [hPj]
      exact mul_sub_one_mod hm (Nat.mul_pos (Nat.succ_pos q) (hpos _))
    refine ⟨?_, ?_⟩
    · simp [term, hd]
    · simp [term, hd1]
  have hsP : ∑ j ∈ Ico 1 (k + 1), term m P j = ∑ j ∈ Ico 1 (k + 1), m ^ j :=
    sum_congr rfl fun j hj => (hlow j hj).1
  have hsP1 : ∑ j ∈ Ico 1 (k + 1), term m P1 j + 1 = (k + 1) * m ^ k := by
    rw [sum_congr rfl fun j hj => (hlow j hj).2]
    exact sum_termMax hm k
  have hgeom : ∑ j ∈ range (k + 1), m ^ j = 1 + ∑ j ∈ Ico 1 (k + 1), m ^ j := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), pow_zero]
  rw [site_of_ne_zero _ one_ne_zero, site_of_ne_zero _ one_ne_zero,
    ← sum_Ico_consecutive _ (by omega : 1 ≤ k + 1) (by omega : k + 1 ≤ ℓ + 1),
    ← sum_Ico_consecutive _ (by omega : 1 ≤ k + 1) (by omega : k + 1 ≤ ℓ + 1),
    sum_eq_sum_Ico_succ_bot (by omega : k + 1 < ℓ + 1),
    sum_eq_sum_Ico_succ_bot (by omega : k + 1 < ℓ + 1), sum_congr rfl (fun j hj => hhigh j hj),
    hgeom, hsP, hmidk]
  linarith

lemma front_add_one_le (hm : 0 < m) (t : ℕ) : front ℓ m t + 1 ≤ (ℓ + 1) * m ^ ℓ :=
  site_one_add_one_le hm _

lemma div_lt_of_le_horizon (hm : 0 < m) {t : ℕ} (ht : t ≤ horizon ℓ m) : t / m < m ^ ℓ := by
  rw [Nat.div_lt_iff_lt_mul hm]
  have := pow_pos hm ℓ
  calc t ≤ (m - 1) * m ^ ℓ := ht
    _ < m * m ^ ℓ := Nat.mul_lt_mul_of_pos_right (by omega) this
    _ = m ^ ℓ * m := mul_comm _ _

/-- `F` is non-increasing (during the injection period). -/
lemma front_succ_le (hm : 0 < m) {t : ℕ} (ht : t + 1 ≤ horizon ℓ m) :
    front ℓ m (t + 1) ≤ front ℓ m t := by
  unfold front
  rcases (Nat.div_le_div_right (Nat.le_succ t) : t / m ≤ (t + 1) / m).eq_or_lt with h | h
  · rw [h]
  · exact (site_one_lt (r := 1) hm le_rfl (by simpa using h)
      (div_lt_of_le_horizon hm ht)).le

variable {ρ : ℝ}

lemma lbAdv_src_le_front (hm : 0 < m) (x : LBIndex ℓ m ρ) :
    (lbAdv ℓ m ρ x).src ≤ front ℓ m (lbAdv ℓ m ρ x).time :=
  site_anti hm _ (Nat.le_add_left 1 _)

lemma lbAdv_src_lt_dst (hm : 0 < m) (x : LBIndex ℓ m ρ) :
    (lbAdv ℓ m ρ x).src < (lbAdv ℓ m ρ x).dst :=
  site_succ_lt hm _ (Nat.lt_succ_iff.1 x.1.1.2)

lemma lbAdv_dst_lt (hm : 0 < m) (x : LBIndex ℓ m ρ) :
    (lbAdv ℓ m ρ x).dst < (ℓ + 1) * m ^ ℓ + 1 := by
  have := site_anti (ℓ := ℓ) hm ((x.1.2 : ℕ) / m) (Nat.zero_le x.1.1)
  rw [site_zero] at this
  simp only [lbAdv]
  omega

/-- Lemma 5.3 of [MPR19]: a packet that has reached its destination in round `t` (within the
injection period) is stale in round `t`, i.e. its destination is right of `F(t)`. -/
theorem lemma_5_3 (hm : 0 < m) (E : Execution (lbAdv ℓ m ρ)) (p : LBIndex ℓ m ρ) {t : ℕ}
    (ht : (lbAdv ℓ m ρ p).time ≤ t) (htT : t ≤ horizon ℓ m)
    (hdel : E.pos t p = (lbAdv ℓ m ρ p).dst) : front ℓ m t < (lbAdv ℓ m ρ p).dst := by
  have hmove := E.pos_le_src_add_of_le ht
  obtain ⟨⟨r, t0⟩, hj⟩ := p
  simp only [lbAdv] at ht hdel hmove ⊢
  rcases Nat.eq_zero_or_pos (r : ℕ) with hr | hr
  · rw [hr, site_zero]
    have := front_add_one_le (ℓ := ℓ) hm t
    omega
  · have hrℓ : (r : ℕ) ≤ ℓ := Nat.lt_succ_iff.1 r.2
    rw [site_succ _ hr hrℓ] at hdel
    have hterm := pow_le_term m ((t0 : ℕ) / m) r
    have h1 : (t0 : ℕ) + m ^ (r : ℕ) ≤ t := by omega
    have h2 : (t0 : ℕ) / m + m ^ ((r : ℕ) - 1) ≤ t / m := by
      have e : m ^ (r : ℕ) = m ^ ((r : ℕ) - 1) * m := by rw [← pow_succ, Nat.sub_add_cancel hr]
      rw [e] at h1
      calc (t0 : ℕ) / m + m ^ ((r : ℕ) - 1) = ((t0 : ℕ) + m ^ ((r : ℕ) - 1) * m) / m :=
            (Nat.add_mul_div_right _ _ hm).symm
        _ ≤ t / m := Nat.div_le_div_right h1
    exact site_one_lt hm hr h2 (div_lt_of_le_horizon hm htT)

/-- Fresh packets are not delivered (consequence of Lemma 5.3). -/
lemma lbAdv_undelivered (hm : 0 < m) (E : Execution (lbAdv ℓ m ρ)) {t : ℕ}
    (htT : t ≤ horizon ℓ m) (p : LBIndex ℓ m ρ) (ht : (lbAdv ℓ m ρ p).time ≤ t)
    (hf : E.pos t p ≤ front ℓ m t) : E.pos t p < (lbAdv ℓ m ρ p).dst := by
  have hle := E.pos_le_dst (lbAdv_src_lt_dst hm p).le ht
  rcases hle.lt_or_eq with h | h
  · exact h
  · have := lemma_5_3 hm E p ht htT h
    omega

/-! ### Counting injections and boundedness -/

lemma sum_jump (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {s t : ℕ} (hst : s ≤ t) :
    ∑ u ∈ Ico s t, (if jump ρ u then 1 else 0) + ⌊ρ * s⌋₊ = ⌊ρ * t⌋₊ := by
  induction t, hst using Nat.le_induction with
  | base => simp
  | succ t hst ih =>
    rw [sum_Ico_succ_top hst, add_right_comm, ih]
    have h1 : ⌊ρ * t⌋₊ ≤ ⌊ρ * ((t : ℝ) + 1)⌋₊ := Nat.floor_le_floor (by nlinarith)
    have h2 : ⌊ρ * ((t : ℝ) + 1)⌋₊ ≤ ⌊ρ * t⌋₊ + 1 := by
      rw [← Nat.floor_add_one (by positivity)]
      exact Nat.floor_le_floor (by nlinarith)
    push_cast
    by_cases h : jump ρ t
    · simp only [h, ↓reduceIte]
      unfold jump at h
      omega
    · simp only [h, ↓reduceIte]
      unfold jump at h
      omega

lemma card_jump_le (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {s t : ℕ} (hst : s ≤ t) :
    ((∑ u ∈ Ico s t, (if jump ρ u then 1 else 0) : ℕ) : ℝ) ≤ ρ * ((t : ℝ) - s) + 1 := by
  have h := sum_jump hρ0 hρ1 hst
  have h1 : (⌊ρ * t⌋₊ : ℝ) ≤ ρ * t := Nat.floor_le (by positivity)
  have h2 : ρ * s < ⌊ρ * s⌋₊ + 1 := Nat.lt_floor_add_one _
  have h3 : ((∑ u ∈ Ico s t, (if jump ρ u then 1 else 0) : ℕ) : ℝ) = ⌊ρ * t⌋₊ - ⌊ρ * s⌋₊ := by
    rw [← h]
    push_cast
    ring
  linarith

/-- The adversary injects `(ℓ + 1) ⌊ρ (m-1) m^ℓ⌋` packets. -/
lemma card_lbIndex (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Fintype.card (LBIndex ℓ m ρ) = (ℓ + 1) * ⌊ρ * horizon ℓ m⌋₊ := by
  rw [Fintype.card_subtype, ← univ_product_univ,
    filter_product_right (fun y : Fin (horizon ℓ m) => jump ρ y), card_product, card_univ,
    Fintype.card_fin, card_filter, Fin.sum_univ_eq_sum_range (fun u => if jump ρ u then 1 else 0),
    range_eq_Ico, ← sum_jump hρ0 hρ1 (Nat.zero_le (horizon ℓ m))]
  simp

lemma sum_counts_eq (P : ι → Packet) (u v n : ℕ) :
    ∑ a ∈ range (v + 1), ∑ b ∈ Ioo v n, counts P u a b =
      #{p | (P p).time = u ∧ (P p).src ≤ v ∧ v < (P p).dst ∧ (P p).dst < n} := by
  rw [card_eq_sum_card_fiberwise (f := fun p => ((P p).src, (P p).dst))
    (t := range (v + 1) ×ˢ Ioo v n), sum_product]
  · refine sum_congr rfl fun a ha => sum_congr rfl fun b hb => ?_
    simp only [mem_range, mem_Ioo] at ha hb
    unfold counts
    congr 1
    ext p
    rcases hP : P p with ⟨t', a', b'⟩
    simp only [mem_filter, mem_univ, true_and, hP, Packet.mk.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨⟨rfl, by omega, hb.1, hb.2⟩, rfl, rfl⟩
    · rintro ⟨⟨rfl, -⟩, rfl, rfl⟩
      exact ⟨rfl, rfl, rfl⟩
  · intro p hp
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hp
    simp only [coe_product, coe_range, coe_Ioo, Set.mem_prod, Set.mem_Iio, Set.mem_Ioo]
    omega

/-- The `ℓ + 1` routes of one round are pairwise disjoint, so at most one packet injected in round
`u` crosses a given buffer, and none if `u` is not an injection round. -/
lemma card_route_le (hm : 0 < m) (u v n : ℕ) :
    #{p : LBIndex ℓ m ρ | (lbAdv ℓ m ρ p).time = u ∧ (lbAdv ℓ m ρ p).src ≤ v ∧
      v < (lbAdv ℓ m ρ p).dst ∧ (lbAdv ℓ m ρ p).dst < n} ≤ if jump ρ u then 1 else 0 := by
  split_ifs with hj
  · rw [card_le_one]
    rintro ⟨⟨r, t0⟩, h0⟩ hp ⟨⟨r', t0'⟩, h0'⟩ hq
    simp only [mem_filter, mem_univ, true_and] at hp hq
    simp only [lbAdv] at hp hq
    have ht : t0 = t0' := Fin.ext (by omega)
    subst ht
    have hr : r = r' := by
      apply Fin.ext
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := site_anti (ℓ := ℓ) hm ((t0 : ℕ) / m) (show (r : ℕ) + 1 ≤ r' from h)
        omega
      · have := site_anti (ℓ := ℓ) hm ((t0 : ℕ) / m) (show (r' : ℕ) + 1 ≤ r from h)
        omega
    subst hr
    rfl
  · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
    rintro ⟨⟨r, t0⟩, h0⟩ - ⟨h1, -⟩
    simp only [lbAdv] at h1
    exact hj (h1 ▸ h0)

/-- The adversary is `(ρ, 1)`-bounded (part of Theorem 5.1 of [MPR19]). -/
theorem lbAdv_isBounded (hm : 0 < m) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Cslib.AQT.IsBounded (counts (lbAdv ℓ m ρ)) ((ℓ + 1) * m ^ ℓ + 1) ρ 1 := by
  intro v _ s t hst
  unfold Cslib.AQT.cross
  have h : ∑ u ∈ Ico s t, ∑ a ∈ range (v + 1), ∑ b ∈ Ioo v ((ℓ + 1) * m ^ ℓ + 1),
      counts (lbAdv ℓ m ρ) u a b ≤ ∑ u ∈ Ico s t, if jump ρ u then 1 else 0 :=
    sum_le_sum fun u _ => (sum_counts_eq _ u v _).trans_le (card_route_le hm u v _)
  calc _ ≤ ((∑ u ∈ Ico s t, (if jump ρ u then 1 else 0) : ℕ) : ℝ) := by exact_mod_cast h
    _ ≤ _ := card_jump_le hρ0.le hρ1 hst

/-! ### The lower bound -/

/-- Theorem 5.1 of [MPR19], sharp form: for every execution some buffer, in some round of the
injection period, has load `L` with `((ℓ+1)ρ - 1)(m-1) m^ℓ - (ℓ+1) ≤ 2 (ℓ+1) m^ℓ L`, i.e.
`L ≥ ((ℓ+1)ρ - 1)(m-1) / (2(ℓ+1)) - 1/(2 m^ℓ)` (the paper's bound in its second case). -/
theorem exists_load_ge (hm : 2 ≤ m) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (E : Execution (lbAdv ℓ m ρ)) :
    ∃ t ≤ horizon ℓ m, ∃ v, (((ℓ + 1) * ρ - 1) * (m - 1) * m ^ ℓ - (ℓ + 1) : ℝ) ≤
      2 * (ℓ + 1) * m ^ ℓ * E.load t v := by
  have hm0 : 0 < m := by omega
  set T := horizon ℓ m with hTdef
  set s : Finset (ℕ × ℕ) := range (T + 1) ×ˢ range ((ℓ + 1) * m ^ ℓ + 1) with hs
  have hne : s.Nonempty := ⟨(0, 0), by simp [hs]⟩
  obtain ⟨⟨t, v⟩, hmem, hmax⟩ := exists_mem_eq_sup s hne (fun x => E.load x.1 x.2)
  set L := s.sup (fun x => E.load x.1 x.2) with hLdef
  have hL : ∀ t' ≤ T, ∀ v', (E.load t' v' : ℝ) ≤ L := by
    intro t' ht' v'
    by_cases hv : v' < (ℓ + 1) * m ^ ℓ + 1
    · exact_mod_cast le_sup (f := fun x : ℕ × ℕ => E.load x.1 x.2) (b := (t', v'))
        (mem_product.2 ⟨mem_range.2 (by omega), mem_range.2 hv⟩)
    · have : E.load t' v' = 0 := by
        unfold Execution.load
        rw [card_eq_zero, filter_eq_empty_iff]
        rintro p - ⟨-, -, h⟩
        have := lbAdv_dst_lt hm0 p
        omega
      rw [this]
      exact_mod_cast Nat.zero_le _
  have key := E.card_injected_le_real (front ℓ m) (T := T) (lbAdv_src_le_front hm0)
    (fun t ht => front_succ_le hm0 (by omega))
    (fun t ht p h1 h2 => lbAdv_undelivered hm0 E ht p h1 h2) hL
  have hall : #{p : LBIndex ℓ m ρ | (lbAdv ℓ m ρ p).time ≤ T} = (ℓ + 1) * ⌊ρ * T⌋₊ := by
    have hle : ∀ p ∈ (univ : Finset (LBIndex ℓ m ρ)), (lbAdv ℓ m ρ p).time ≤ T :=
      fun p _ => p.1.2.2.le
    rw [filter_true_of_mem hle, card_univ, card_lbIndex hρ0.le hρ1]
  rw [hall] at key
  push_cast at key
  have hfl : ρ * T - 1 < ⌊ρ * T⌋₊ := by have := Nat.lt_floor_add_one (ρ * T); linarith
  have hF0 : (front ℓ m 0 : ℝ) + 1 ≤ (ℓ + 1) * m ^ ℓ := by exact_mod_cast front_add_one_le hm0 0
  have hT : (T : ℝ) = (m - 1) * m ^ ℓ := by
    rw [hTdef, horizon, Nat.cast_mul, Nat.cast_sub (by omega)]
    push_cast
    ring
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hLF : (L : ℝ) * (2 * front ℓ m 0 + 1) ≤ L * (2 * ((ℓ + 1) * m ^ ℓ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hL0
  refine ⟨t, ?_, v, ?_⟩
  · simp only [hs, mem_product, mem_range] at hmem
    omega
  · have hLv : (L : ℝ) = E.load t v := by exact_mod_cast hmax
    rw [← hLv]
    have hℓ0 : (0 : ℝ) ≤ ℓ + 1 := by positivity
    have h5 : (ℓ + 1) * (ρ * T - 1) ≤ (ℓ + 1) * (⌊ρ * T⌋₊ : ℝ) :=
      mul_le_mul_of_nonneg_left hfl.le hℓ0
    rw [hT] at h5 key
    linarith

/-- Theorem 5.1 of [MPR19], with explicit constants: for every execution of any forwarding
protocol against `lbAdv ℓ m ρ`, some buffer has load at least
`((ℓ+1)ρ - 1)(m-1) / (4(ℓ+1)) - 1`. -/
theorem lower_bound (hm : 2 ≤ m) (hρ : 1 / ((ℓ : ℝ) + 1) < ρ) (hρ1 : ρ ≤ 1)
    (E : Execution (lbAdv ℓ m ρ)) :
    ∃ t v, ((ℓ + 1) * ρ - 1) * (m - 1) / (4 * (ℓ + 1)) ≤ (E.load t v : ℝ) + 1 := by
  have hℓ0 : (0 : ℝ) < ℓ + 1 := by positivity
  have hρ0 : 0 < ρ := lt_trans (by positivity) hρ
  have hc : 0 < (ℓ + 1) * ρ - 1 := by
    rw [div_lt_iff₀ hℓ0] at hρ
    linarith
  obtain ⟨t, -, v, h⟩ := exists_load_ge hm hρ0 hρ1 E
  refine ⟨t, v, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have hmℓ : (1 : ℝ) ≤ m ^ ℓ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ m))
  have hload : (0 : ℝ) ≤ E.load t v := Nat.cast_nonneg _
  have h2 : ((ℓ + 1) * ρ - 1) * (m - 1) * m ^ ℓ ≤
      (2 * (ℓ + 1) * E.load t v + (ℓ + 1)) * m ^ ℓ := by nlinarith
  have h3 : ((ℓ + 1) * ρ - 1) * (m - 1) ≤ 2 * (ℓ + 1) * E.load t v + (ℓ + 1) :=
    le_of_mul_le_mul_right h2 (by positivity)
  nlinarith

/-- **Theorem 5.1 of [MPR19]** (packaged). For `m ≥ 2` and `1/(ℓ+1) < ρ ≤ 1`, on the
path with `(ℓ+1) m^ℓ + 1` nodes there is a finite `(ρ, 1)`-bounded injection pattern such that
every forwarding protocol has, in some round, a buffer of load at least
`((ℓ+1)ρ - 1)(m-1) / (4(ℓ+1)) - 1`; with `n ≈ (ℓ+1) m^ℓ` this is
`Ω(((ℓ+1)ρ - 1) / (ℓ+1) · (n/(ℓ+1))^(1/ℓ))`. -/
theorem theorem_5_1 (ℓ m : ℕ) (ρ : ℝ) (hm : 2 ≤ m) (hρ : 1 / ((ℓ : ℝ) + 1) < ρ)
    (hρ1 : ρ ≤ 1) :
    ∃ (ι : Type) (_ : Fintype ι) (P : ι → Packet),
      (∀ p, (P p).src < (P p).dst ∧ (P p).dst < (ℓ + 1) * m ^ ℓ + 1) ∧
      Cslib.AQT.IsBounded (counts P) ((ℓ + 1) * m ^ ℓ + 1) ρ 1 ∧
      ∀ E : Execution P, ∃ t v,
        ((ℓ + 1) * ρ - 1) * (m - 1) / (4 * (ℓ + 1)) ≤ (E.load t v : ℝ) + 1 := by
  have hm0 : 0 < m := by omega
  have hρ0 : 0 < ρ := lt_trans (by positivity) hρ
  exact ⟨LBIndex ℓ m ρ, inferInstance, lbAdv ℓ m ρ,
    fun p => ⟨lbAdv_src_lt_dst hm0 p, lbAdv_dst_lt hm0 p⟩,
    lbAdv_isBounded hm0 hρ0 hρ1, fun E => lower_bound hm hρ hρ1 E⟩

end Adversary

end Podc.SmallBuffersAQT.LowerBound
