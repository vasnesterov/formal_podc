import Mathlib

/-!
# Adaptive `k`-shot broadcasting: the lower bound of Section 5

Karmakar, Koutris, Pagourtzis, Sakavalas. *k-shot Broadcasting in Ad Hoc Radio Networks*,
arXiv:1603.08393v1, Section 5 (Definitions 1–2, Theorems 1–3).

**Model.** Directed radio network `G : V → V → Prop` on a finite id set `V`, source `s`,
synchronous rounds `0, 1, 2, …` (the paper's round `t` is our round `t - 1`), no collision
detection: a node that does not transmit hears a message iff exactly one in-neighbour transmits;
a transmitter hears nothing (`sender`). Deterministic adaptive protocols are arbitrary state
machines (`Protocol`): initial state from the id and the source flag, action (transmit a message
or listen) and update depending on the id, the round and the state; nodes may transmit before
they know the source message. This contains the paper's full-information protocols
`π(v, t, H_{t-1}(v))`. Being informed is tracked semantically (`Protocol.informed`): a node
becomes informed when it hears a node that was informed at the start of the round.
`k`-shot (`KShotOnFamily`): in every network of the family every node transmits in at most `k`
rounds. Correctness of the protocol is *not* assumed by the lower bounds.

**Family `G`.** A listing `e : V ≃ Fin n` with `e s = 0`; position `p` is in layer
`⌊(p + 1)/2⌋` (`layerOf`), and the edges go from every node of a layer to every node of the next
one (`familyGraph`). Layer `i` here is the paper's `L_{i+1}`.

**Transmission trees (Definitions 1, 2).** Encoded by the transmission patterns
`p : α → ℕ → Bool` of the ids: the tree node at depth `t` on the branch of `x` is `cell A p t x`
(the ids acting like `x` in rounds `< t`); its left/right children are the listeners/transmitters
of round `t`. `HeightLE A p h`: all depth-`h` nodes are singleton leaves. `KShotTree A p k`: every
root–leaf branch has at most `k` right edges.

**Main results.**
* `card_le_sum_choose_of_kShotTree`, `card_le_pow_of_kShotTree`, `rpow_sub_one_le_of_kShotTree`:
  Theorem 2 (`a ≤ ∑_{i ≤ k} C(h, i) ≤ (h + 1)^k`, i.e. `height ≥ a^{1/k} - 1`).
* `exists_extension_of_not_heightLE`: Theorem 1 as stated (absolute rounds).
* `exists_extension_of_same_window`, `exists_extension_quiet`: the corrected (relative) form of
  Theorems 1 + 2: measured from the round `D₀` before which layer `i + 1` cannot be informed, the
  relay to layer `i + 2` can be delayed by `d` more rounds whenever `∑_{r ≤ k} C(d, r)` is less
  than the number of unused ids.
* `exists_slow_network`, `exists_slow_network_uniform`, `exists_slow_network_rpow`: Theorem 3
  (some network of `G` is not informed after `n^{1 + 1/k} / 32` rounds when `n ≥ 2 · 4^k`).
* `onceProtocol_kShot`, `onceProtocol_heightLE`: non-vacuity of the `k`-shot hypothesis, and an
  illustration of why the paper's summation of absolute tree heights is not justified.
-/

namespace Podc.KShotRadioBroadcast.Adaptive

open Finset

/-! ## Counting patterns with at most `k` ones -/

/-- The sets of at most `k` rounds among `0, …, h-1`. -/
def smallSubsets (h k : ℕ) : Finset (Finset ℕ) :=
  (range (k + 1)).biUnion fun i => powersetCard i (range h)

lemma mem_smallSubsets {h k : ℕ} {S : Finset ℕ} (hS : S ⊆ range h) (hk : #S ≤ k) :
    S ∈ smallSubsets h k := by
  simp only [smallSubsets, mem_biUnion, mem_range, mem_powersetCard]
  exact ⟨#S, by omega, hS, rfl⟩

lemma card_smallSubsets_le (h k : ℕ) :
    #(smallSubsets h k) ≤ ∑ i ∈ range (k + 1), h.choose i := by
  refine (card_biUnion_le).trans (le_of_eq ?_)
  simp [card_powersetCard]

/-- `∑_{i ≤ k} C(h, i) ≤ (h + 1)^k`. -/
lemma sum_choose_le_pow (h k : ℕ) : ∑ i ∈ range (k + 1), h.choose i ≤ (h + 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, pow_succ]
    have h1 : h.choose (k + 1) ≤ h * (h + 1) ^ k := by
      calc h.choose (k + 1) ≤ h ^ (k + 1) := Nat.choose_le_pow _ _
        _ = h * h ^ k := by ring
        _ ≤ h * (h + 1) ^ k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    nlinarith


/-! ## Transmission trees (Definitions 1, 2) and Theorem 2 -/

section Tree

variable {α : Type*} [DecidableEq α]

/-- The node at depth `t` of the transmission tree `T(A, π, (H_j))` that lies on the branch of
`x`: the elements of `A` that act like `x` in the first `t` rounds. Here `p y i = true` means that
`y` transmits in round `i + 1` (the paper's round `t` is our index `t - 1`), so the children of a
depth-`t` node `P` are `{y ∈ P | p y t = false}` (left, `R^P`) and `{y ∈ P | p y t = true}`
(right, `S^P`), exactly as in Definition 1. -/
def cell (A : Finset α) (p : α → ℕ → Bool) (t : ℕ) (x : α) : Finset α :=
  A.filter fun y => ∀ i < t, p y i = p x i

/-- The transmission tree of `A` under the round patterns `p` has height at most `h`: every node
at depth `h` is a singleton leaf. (Definition 1 requires the leaves to be singletons; the tree is
cut at the first singleton node of each branch.) -/
def HeightLE (A : Finset α) (p : α → ℕ → Bool) (h : ℕ) : Prop :=
  ∀ x ∈ A, cell A p h x = {x}

/-- Definition 2: a `k`-shot transmission tree. The branch to the leaf of `x` uses the edge from
depth `i` to depth `i + 1` iff the depth-`i` node is not yet a leaf (has at least two elements);
that edge goes to a right child iff `p x i`. Every branch has at most `k` right children. -/
def KShotTree (A : Finset α) (p : α → ℕ → Bool) (k : ℕ) : Prop :=
  ∀ x ∈ A, ∀ t, #((range t).filter fun i => 1 < #(cell A p i x) ∧ p x i = true) ≤ k

omit [DecidableEq α] in
lemma mem_cell_self {A : Finset α} {p : α → ℕ → Bool} {t : ℕ} {x : α} (hx : x ∈ A) :
    x ∈ cell A p t x := by
  simp [cell, hx]

/-- **Theorem 2 of the paper (exact form).** A `k`-shot transmission tree of height at most `h`
on a set of `a` elements satisfies `a ≤ ∑_{i ≤ k} C(h, i)`. (For `k = 1` this is `a ≤ h + 1`, the
paper's `height ≥ a - 1`.) -/
theorem card_le_sum_choose_of_kShotTree {A : Finset α} {p : α → ℕ → Bool} {h k : ℕ}
    (hh : HeightLE A p h) (hk : KShotTree A p k) :
    #A ≤ ∑ i ∈ range (k + 1), h.choose i := by
  classical
  let q : α → Finset ℕ := fun x => (range h).filter fun i => 1 < #(cell A p i x) ∧ p x i = true
  have hmaps : Set.MapsTo q A (smallSubsets h k) := fun x hx =>
    mem_smallSubsets (filter_subset _ _) (hk x hx h)
  have hinj : Set.InjOn q A := by
    intro x hx y hy hxy
    by_contra hne
    -- `y` is separated from `x` before depth `h`
    have hsep : ∃ i, i < h ∧ p y i ≠ p x i := by
      have : y ∉ cell A p h x := by rw [hh x hx]; simpa [eq_comm] using hne
      simp only [cell, mem_filter, not_and, not_forall] at this
      obtain ⟨i, hi, hne⟩ := this hy
      exact ⟨i, hi, hne⟩
    let i₀ := Nat.find hsep
    have hi₀ : i₀ < h ∧ p y i₀ ≠ p x i₀ := Nat.find_spec hsep
    have hbefore : ∀ i < i₀, p y i = p x i := fun i hi => by
      by_contra hc
      exact Nat.find_min hsep hi ⟨lt_trans hi hi₀.1, hc⟩
    have hcx : 1 < #(cell A p i₀ x) := by
      rw [one_lt_card]
      exact ⟨x, mem_cell_self hx, y,
        by simp only [cell, mem_filter]; exact ⟨hy, hbefore⟩, hne⟩
    have hcy : 1 < #(cell A p i₀ y) := by
      rw [one_lt_card]
      exact ⟨y, mem_cell_self hy, x,
        by simp only [cell, mem_filter]; exact ⟨hx, fun i hi => (hbefore i hi).symm⟩, Ne.symm hne⟩
    have := congrArg (i₀ ∈ ·) hxy
    simp only [q, mem_filter, mem_range, hi₀.1, hcx, hcy, true_and, eq_iff_iff] at this
    cases hpx : p x i₀ <;> cases hpy : p y i₀ <;> simp_all
  exact (card_le_card_of_injOn q hmaps hinj).trans (card_smallSubsets_le h k)

/-- **Theorem 2 of the paper**, power form: `a ≤ (h + 1)^k`, i.e. `height ≥ a^{1/k} - 1`. -/
theorem card_le_pow_of_kShotTree {A : Finset α} {p : α → ℕ → Bool} {h k : ℕ}
    (hh : HeightLE A p h) (hk : KShotTree A p k) : #A ≤ (h + 1) ^ k :=
  (card_le_sum_choose_of_kShotTree hh hk).trans (sum_choose_le_pow h k)

/-- **Theorem 2 of the paper**, real form: `height ≥ a^{1/k} - 1` for `k ≥ 1`. -/
theorem rpow_sub_one_le_of_kShotTree {A : Finset α} {p : α → ℕ → Bool} {h k : ℕ} (hk1 : 1 ≤ k)
    (hh : HeightLE A p h) (hk : KShotTree A p k) :
    (#A : ℝ) ^ ((1 : ℝ) / k) - 1 ≤ h := by
  have h1 : (#A : ℝ) ≤ ((h : ℝ) + 1) ^ k := by exact_mod_cast card_le_pow_of_kShotTree hh hk
  have h2 : (#A : ℝ) ^ ((1 : ℝ) / k) ≤ (((h : ℝ) + 1) ^ k) ^ ((1 : ℝ) / k) :=
    Real.rpow_le_rpow (by positivity) h1 (by positivity)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    mul_one_div_cancel (by exact_mod_cast (show k ≠ 0 by omega)), Real.rpow_one] at h2
  linarith

end Tree

/-! ## Adaptive protocols in directed radio networks -/

/-- `uniqueOf Q`: the unique `u` with `Q u`, if there is exactly one. -/
noncomputable def uniqueOf {V : Type*} (Q : V → Prop) : Option V :=
  open Classical in if h : ∃ u, ∀ w, Q w ↔ w = u then some h.choose else none

lemma uniqueOf_eq_some {V : Type*} {Q : V → Prop} {u : V} :
    uniqueOf Q = some u ↔ ∀ w, Q w ↔ w = u := by
  unfold uniqueOf
  split_ifs with h
  · have hc := h.choose_spec
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact hc
    · intro hu; exact ((hc u).1 ((hu u).2 rfl)).symm ▸ rfl
  · simp only [false_iff]
    exact fun hu => h ⟨u, hu⟩

/-- The sender heard by `v` in a round in which the nodes transmit `tx` (`none` = listen) in the
directed network `G` (`G u v`: edge `u → v`): if `v` transmits it hears nothing; otherwise it hears
its in-neighbour `u` iff `u` is the only transmitting in-neighbour (no collision detection:
silence and collision are indistinguishable). -/
noncomputable def sender {V M : Type*} (G : V → V → Prop) (tx : V → Option M) (v : V) :
    Option V :=
  if (tx v).isSome then none else uniqueOf fun w => G w v ∧ (tx w).isSome

lemma sender_eq_some {V M : Type*} {G : V → V → Prop} {tx : V → Option M} {v u : V} :
    sender G tx v = some u ↔ (tx v).isSome = false ∧ ∀ w, (G w v ∧ (tx w).isSome) ↔ w = u := by
  unfold sender
  split_ifs with h <;> simp [h, uniqueOf_eq_some]

/-- A deterministic adaptive radio protocol, as a general state machine (this subsumes the
paper's full-information protocols `π(v, t, H_{t-1}(v))`, where the state is the view). Node `v`
starts in `init v b` (`b`: whether `v` is the source); in round `t` it transmits `act v t q`
(`none` = listen) in state `q`, and then moves to `δ v t q r` where `r` is what it received.
Nodes may transmit before they know the source message. -/
structure Protocol (V σ M : Type*) where
  /-- Initial state of node `v`; the flag says whether `v` is the source. -/
  init : V → Bool → σ
  /-- Action in round `t`: `some m` = transmit `m`, `none` = listen. -/
  act : V → ℕ → σ → Option M
  /-- State update after round `t` with the received message (if any). -/
  δ : V → ℕ → σ → Option M → σ

namespace Protocol

variable {V σ M : Type*} [DecidableEq V] (P : Protocol V σ M)

/-- The execution of `P` in the network `G` with source `s`: `P.state G s t v` is the state of
`v` after `t` rounds (rounds are numbered `0, 1, …`; the paper's round `t` is our round `t - 1`). -/
noncomputable def state (G : V → V → Prop) (s : V) : ℕ → V → σ
  | 0 => fun v => P.init v (decide (v = s))
  | t + 1 => fun v =>
      P.δ v t (state G s t v)
        ((sender G (fun u => P.act u t (state G s t u)) v).bind
          fun u => P.act u t (state G s t u))

/-- What the nodes transmit in round `t`. -/
noncomputable def tx (G : V → V → Prop) (s : V) (t : ℕ) (v : V) : Option M :=
  P.act v t (P.state G s t v)

lemma state_zero (G : V → V → Prop) (s v : V) : P.state G s 0 v = P.init v (decide (v = s)) :=
  rfl

lemma state_succ (G : V → V → Prop) (s : V) (t : ℕ) (v : V) :
    P.state G s (t + 1) v =
      P.δ v t (P.state G s t v) ((sender G (P.tx G s t) v).bind (P.tx G s t)) := rfl

/-- `P.informed G s t v`: node `v` knows the source message after `t` rounds. The source is
informed at time `0`; a node becomes informed when it hears (in the sense of `sender`) a node that
was already informed at the beginning of the round. (This is the most generous notion: any
message of an informed node is assumed to carry the source message.) -/
def informed (G : V → V → Prop) (s : V) : ℕ → V → Prop
  | 0 => fun v => v = s
  | t + 1 => fun v => informed G s t v ∨ ∃ u, sender G (P.tx G s t) v = some u ∧ informed G s t u

lemma informed_mono {G : V → V → Prop} {s : V} {t t' : ℕ} (htt' : t ≤ t') {v : V}
    (h : P.informed G s t v) : P.informed G s t' v := by
  induction htt' with
  | refl => exact h
  | step _ ih => exact Or.inl ih

/-- Locality: if `U` is closed under in-neighbours and the in-neighbourhoods of the nodes of `U`
are the same in `G` and `G'`, then the nodes of `U` behave identically in both networks. -/
theorem state_informed_congr {G G' : V → V → Prop} {s : V} {U : V → Prop}
    (hU : ∀ v, U v → ∀ w, G w v ∨ G' w v → U w) (hG : ∀ v, U v → ∀ w, G w v ↔ G' w v) :
    ∀ t v, U v → P.state G s t v = P.state G' s t v ∧
      (P.informed G s t v ↔ P.informed G' s t v) := by
  intro t
  induction t with
  | zero => intro v _; exact ⟨rfl, Iff.rfl⟩
  | succ t ih =>
    intro v hv
    have htx : ∀ w, U w → P.tx G s t w = P.tx G' s t w := fun w hw => by
      simp only [tx, (ih w hw).1]
    have hsend : sender G (P.tx G s t) v = sender G' (P.tx G' s t) v := by
      unfold sender
      rw [htx v hv]
      congr 2
      funext w
      apply propext
      constructor
      · rintro ⟨h1, h2⟩
        have hw := hU v hv w (Or.inl h1)
        exact ⟨(hG v hv w).1 h1, htx w hw ▸ h2⟩
      · rintro ⟨h1, h2⟩
        have hw := hU v hv w (Or.inr h1)
        exact ⟨(hG v hv w).2 h1, (htx w hw).symm ▸ h2⟩
    have hsU : ∀ u, sender G (P.tx G s t) v = some u → U u := fun u hu => by
      have := (sender_eq_some.1 hu).2 u
      exact hU v hv u (Or.inl (this.2 rfl).1)
    constructor
    · rw [state_succ, state_succ, (ih v hv).1, ← hsend]
      congr 1
      cases hc : sender G (P.tx G s t) v with
      | none => rfl
      | some u => simp [htx u (hsU u hc)]
    · simp only [informed]
      rw [(ih v hv).2, ← hsend]
      constructor
      · rintro (h | ⟨u, hu, hi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨u, hu, (ih u (hsU u hu)).2.1 hi⟩
      · rintro (h | ⟨u, hu, hi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨u, hu, (ih u (hsU u hu)).2.2 hi⟩

/-! ### Layered networks -/

/-- The layered network of a layer function `lay`: an edge `u → v` iff `lay v = lay u + 1`. -/
def layered (lay : V → ℕ) : V → V → Prop := fun u v => lay v = lay u + 1

/-- Locality in layered networks: the nodes of layers `≤ j` behave the same in two layered
networks that agree on these layers. -/
theorem layered_congr {lay lay' : V → ℕ} {j : ℕ} {s : V}
    (H : ∀ v, lay v ≤ j ∨ lay' v ≤ j → lay v = lay' v) :
    ∀ t v, lay v ≤ j → P.state (layered lay) s t v = P.state (layered lay') s t v ∧
      (P.informed (layered lay) s t v ↔ P.informed (layered lay') s t v) := by
  refine P.state_informed_congr (U := fun v => lay v ≤ j) ?_ ?_
  · intro v hv w hw
    simp only [layered] at hw
    rcases hw with hw | hw
    · omega
    · have := H v (Or.inl hv); have := H w; omega
  · intro v hv w
    simp only [layered]
    have := H v (Or.inl hv)
    constructor
    · intro h; have := H w (Or.inl (by omega)); omega
    · intro h; have := H w (Or.inr (by omega)); omega

/-- The run of node `w` when it hears `inp t` in every round `t` in which it listens. -/
def solo (w : V) (inp : ℕ → Option M) : ℕ → σ
  | 0 => P.init w false
  | t + 1 => P.δ w t (solo w inp t)
      (if (P.act w t (solo w inp t)).isSome then none else inp t)

/-- What a listening node of layer `j` hears in round `t` of the layered network of `lay`: the
message of the unique transmitter of layer `j - 1`, if there is exactly one. -/
noncomputable def layerInput (lay : V → ℕ) (s : V) (j t : ℕ) : Option M :=
  (uniqueOf fun x => j = lay x + 1 ∧ (P.tx (layered lay) s t x).isSome).bind
    (P.tx (layered lay) s t)

/-- The transmission pattern of id `w` if placed in layer `j` (`j ≥ 1`) of the layered network of
`lay`: `P.pat lay s j w t` says whether it transmits in round `t`. -/
noncomputable def pat (lay : V → ℕ) (s : V) (j : ℕ) (w : V) (t : ℕ) : Bool :=
  (P.act w t (P.solo w (P.layerInput lay s j) t)).isSome

theorem state_eq_solo (lay : V → ℕ) {s w : V} (hw : w ≠ s) :
    ∀ t, P.state (layered lay) s t w = P.solo w (P.layerInput lay s (lay w)) t := by
  intro t
  induction t with
  | zero => simp [state_zero, solo, hw]
  | succ t ih =>
    rw [state_succ, ih]
    simp only [solo, sender, layerInput, tx, ih]
    split_ifs <;> rfl

theorem tx_isSome_eq_pat (lay : V → ℕ) {s w : V} (hw : w ≠ s) (t : ℕ) :
    (P.tx (layered lay) s t w).isSome = P.pat lay s (lay w) w t := by
  simp [tx, pat, P.state_eq_solo lay hw]

theorem layerInput_congr {lay lay' : V → ℕ} {j : ℕ} {s : V}
    (H : ∀ v, lay v ≤ j ∨ lay' v ≤ j → lay v = lay' v) :
    P.layerInput lay s (j + 1) = P.layerInput lay' s (j + 1) := by
  funext t
  have htx : ∀ x, lay x ≤ j → P.tx (layered lay) s t x = P.tx (layered lay') s t x := fun x hx => by
    simp only [tx, (P.layered_congr H t x hx).1]
  have hpred : (fun x => j + 1 = lay x + 1 ∧ (P.tx (layered lay) s t x).isSome) =
      (fun x => j + 1 = lay' x + 1 ∧ (P.tx (layered lay') s t x).isSome) := by
    funext x
    apply propext
    constructor
    · rintro ⟨h1, h2⟩
      have := H x (Or.inl (by omega))
      exact ⟨by omega, htx x (by omega) ▸ h2⟩
    · rintro ⟨h1, h2⟩
      have := H x (Or.inr (by omega))
      exact ⟨by omega, (htx x (by omega)).symm ▸ h2⟩
  unfold layerInput
  rw [hpred]
  cases hc : uniqueOf (fun x => j + 1 = lay' x + 1 ∧ (P.tx (layered lay') s t x).isSome) with
  | none => rfl
  | some u =>
    have hu := ((uniqueOf_eq_some.1 hc) u).2 rfl
    have := H u (Or.inr (by omega))
    simp [htx u (by omega)]

theorem pat_congr {lay lay' : V → ℕ} {j : ℕ} {s : V}
    (H : ∀ v, lay v ≤ j ∨ lay' v ≤ j → lay v = lay' v) :
    P.pat lay s (j + 1) = P.pat lay' s (j + 1) := by
  unfold pat
  rw [P.layerInput_congr H]

/-- In rounds `< D`, no informed node of layer `L` transmits alone within its layer. -/
def Quiet (G : V → V → Prop) (s : V) (L : V → Prop) (D : ℕ) : Prop :=
  ∀ t < D, ∀ u, L u → P.informed G s t u → (P.tx G s t u).isSome →
    ∃ u', u' ≠ u ∧ L u' ∧ (P.tx G s t u').isSome

/-- If layer `j` is quiet before round `D`, no node of layer `j + 1` is informed at time `D`. -/
theorem not_informed_of_quiet {lay : V → ℕ} {s : V} (hs : lay s = 0) {j D : ℕ}
    (hq : P.Quiet (layered lay) s (fun u => lay u = j) D) :
    ∀ t ≤ D, ∀ v, lay v = j + 1 → ¬ P.informed (layered lay) s t v := by
  intro t
  induction t with
  | zero => intro _ v hv h; simp only [informed] at h; subst h; omega
  | succ t ih =>
    intro ht v hv h
    rcases h with h | ⟨u, hu, hi⟩
    · exact ih (by omega) v hv h
    · obtain ⟨-, huniq⟩ := sender_eq_some.1 hu
      obtain ⟨hGu, htxu⟩ := (huniq u).2 rfl
      simp only [layered] at hGu
      obtain ⟨u', hne, hu', htx'⟩ := hq t (by omega) u (by omega) hi htxu
      exact hne ((huniq u').1 ⟨by simp only [layered]; omega, htx'⟩)

/-- Quietness of layer `j` only depends on the layers `≤ j`. -/
theorem quiet_congr {lay lay' : V → ℕ} {j : ℕ} {s : V} {D : ℕ}
    (H : ∀ v, lay v ≤ j ∨ lay' v ≤ j → lay v = lay' v)
    (hq : P.Quiet (layered lay) s (fun u => lay u = j) D) :
    P.Quiet (layered lay') s (fun u => lay' u = j) D := by
  have hL : ∀ u, lay' u = j → lay u = j := fun u hu => by have := H u (Or.inr (by omega)); omega
  have hc := P.layered_congr (s := s) H
  intro t ht u hu hi htx
  have hu' := hL u hu
  have e1 := hc t u (by omega)
  obtain ⟨u', hne, hu'', htx'⟩ := hq t ht u hu' (e1.2.2 hi) (by simpa [tx, e1.1] using htx)
  have e2 := hc t u' (by omega)
  refine ⟨u', hne, ?_, by simpa [tx, e2.1] using htx'⟩
  have := H u' (Or.inl (by omega)); omega

/-- **Theorem 1 (corrected, relative form): the key step.** Suppose layer `j` is not informed
up to time `D₀`, and layer `j` consists of two ids `w₁ ≠ w₂` that behave identically in the window
of rounds `D₀, …, D₀ + d - 1`. Then layer `j` is quiet before round `D₀ + d`; in particular
(`not_informed_of_quiet`) layer `j + 1` is not informed at time `D₀ + d`. -/
theorem quiet_of_same_window {lay : V → ℕ} {s : V} {j D₀ d : ℕ} {w₁ w₂ : V} (hne : w₁ ≠ w₂)
    (hw₁ : lay w₁ = j) (hw₂ : lay w₂ = j)
    (hL : ∀ x, lay x = j → x = w₁ ∨ x = w₂)
    (hinf : ∀ t ≤ D₀, ∀ v, lay v = j → ¬ P.informed (layered lay) s t v)
    (hpat : ∀ t, D₀ ≤ t → t < D₀ + d →
      (P.tx (layered lay) s t w₁).isSome = (P.tx (layered lay) s t w₂).isSome) :
    P.Quiet (layered lay) s (fun u => lay u = j) (D₀ + d) := by
  intro t ht u hu hi htx
  have hD : D₀ < t := by
    by_contra hc
    exact hinf t (by omega) u hu hi
  have hp := hpat t (by omega) ht
  rcases hL u hu with rfl | rfl
  · exact ⟨w₂, hne.symm, hw₂, by rw [← hp]; exact htx⟩
  · exact ⟨w₁, hne, hw₁, by rw [hp]; exact htx⟩

end Protocol

/-! ## The family `G` of layered networks -/

section Family

variable {V σ M : Type*} [DecidableEq V] [Fintype V]

/-- Layer of a node in the listing `e` of the nodes (`e v` = position of `v`): position `0` is
layer `0` (the paper's `L₁ = {s}`), positions `2i - 1, 2i` form layer `i` (the paper's `L_{i+1}`).
With `n` nodes the last layer has one or two nodes, and there are `⌊n/2⌋ + 1` layers. -/
def layerOf (e : V ≃ Fin (Fintype.card V)) (v : V) : ℕ := ((e v : ℕ) + 1) / 2

/-- The network of the family `G` given by the listing `e` (with `e s = 0`): all edges from
each layer to the next one, and no other edges. -/
def familyGraph (e : V ≃ Fin (Fintype.card V)) : V → V → Prop := Protocol.layered (layerOf e)

/-- `P` is `k`-shot on the family `G` with source `s`: in every network of the family, every
node transmits in at most `k` rounds. -/
def KShotOnFamily (P : Protocol V σ M) (s : V) (k : ℕ) : Prop :=
  ∀ e : V ≃ Fin (Fintype.card V), (e s : ℕ) = 0 → ∀ v T,
    #((range T).filter fun t => (P.tx (familyGraph e) s t v).isSome) ≤ k

omit [DecidableEq V] [Fintype V] in
/-- Move `w` to position `p ≤ e w` by a swap; positions `< p` are untouched. -/
lemma exists_move {n : ℕ} (e : V ≃ Fin n) (w : V) (p : Fin n) (hp : p ≤ e w) :
    ∃ e' : V ≃ Fin n, e' w = p ∧ ∀ v, (e v < p ∨ e' v < p) → e' v = e v := by
  classical
  refine ⟨e.trans (Equiv.swap (e w) p), by simp, ?_⟩
  intro v hv
  simp only [Equiv.trans_apply, Equiv.swap_apply_def] at hv ⊢
  rw [Fin.lt_def, Fin.lt_def] at hv
  rw [Fin.le_def] at hp
  split_ifs at hv ⊢ with h1 h2 <;> simp only [Fin.ext_iff] at * <;> omega

omit [DecidableEq V] in
lemma layerOf_le_iff (e : V ≃ Fin (Fintype.card V)) (v : V) (i : ℕ) :
    layerOf e v ≤ i ↔ (e v : ℕ) < 2 * i + 1 := by
  unfold layerOf; omega

omit [DecidableEq V] in
/-- Listings that agree on the positions `< 2i + 1` agree on the layers `≤ i`. -/
lemma layer_agree {e e' : V ≃ Fin (Fintype.card V)} {i : ℕ}
    (h : ∀ v, ((e v : ℕ) < 2 * i + 1 ∨ (e' v : ℕ) < 2 * i + 1) → e' v = e v) :
    ∀ v, layerOf e v ≤ i ∨ layerOf e' v ≤ i → layerOf e v = layerOf e' v := by
  intro v hv
  simp only [layerOf_le_iff] at hv
  rw [layerOf, layerOf, h v hv]

omit [DecidableEq V] in
lemma card_tail_ge (e : V ≃ Fin (Fintype.card V)) (p : ℕ) :
    Fintype.card V - p ≤ #(univ.filter fun w => p ≤ (e w : ℕ)) := by
  have h1 : #(univ.filter fun w => ¬ p ≤ (e w : ℕ)) ≤ p := by
    have := card_le_card_of_injOn (fun w => (e w : ℕ)) (t := range p)
      (s := univ.filter fun w => ¬ p ≤ (e w : ℕ))
      (fun w hw => by simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
                      simp only [coe_range, Set.mem_Iio]; omega)
      (fun a _ b _ hab => e.injective (Fin.ext hab))
    simpa using this
  have h2 := card_filter_add_card_filter_not (s := univ) (fun w => p ≤ (e w : ℕ))
  rw [card_univ] at h2
  omega

variable (P : Protocol V σ M)

/-- **Theorem 1, the choice of layer `i + 1`.** Let the listing `e` fix layers `0, …, i`, with
layer `i` quiet before round `D₀` (so layer `i + 1` is not informed at time `D₀`). If two unused
ids `w₁ ≠ w₂` (positions `≥ 2i + 1`) would behave identically as members of layer `i + 1` in the
rounds `D₀, …, D₀ + d - 1`, then putting them in layer `i + 1` (keeping layers `≤ i`) makes
layer `i + 1` quiet before round `D₀ + d`: it cannot relay the message to layer `i + 2` before
round `D₀ + d` (`not_informed_of_quiet`). -/
theorem exists_extension_of_same_window {s : V} {e : V ≃ Fin (Fintype.card V)}
    (he : (e s : ℕ) = 0) {i D₀ d : ℕ}
    (hq : P.Quiet (familyGraph e) s (fun u => layerOf e u = i) D₀)
    (hp2 : 2 * i + 2 < Fintype.card V) {w₁ w₂ : V} (hne : w₁ ≠ w₂)
    (hw₁ : 2 * i + 1 ≤ (e w₁ : ℕ)) (hw₂ : 2 * i + 1 ≤ (e w₂ : ℕ))
    (hsame : ∀ r < d, P.pat (layerOf e) s (i + 1) w₁ (D₀ + r) =
      P.pat (layerOf e) s (i + 1) w₂ (D₀ + r)) :
    ∃ e' : V ≃ Fin (Fintype.card V), (e' s : ℕ) = 0 ∧
      (∀ v, layerOf e v ≤ i ∨ layerOf e' v ≤ i → layerOf e v = layerOf e' v) ∧
      P.Quiet (familyGraph e') s (fun u => layerOf e' u = i + 1) (D₀ + d) := by
  have hp1 : 2 * i + 1 < Fintype.card V := by omega
  -- put `w₁, w₂` at positions `2i + 1, 2i + 2`
  obtain ⟨e₁, he₁w, he₁⟩ := exists_move e w₁ ⟨2 * i + 1, hp1⟩ (by rw [Fin.le_def]; exact hw₁)
  have he₁' : ∀ v, ((e v : ℕ) < 2 * i + 1 ∨ (e₁ v : ℕ) < 2 * i + 1) → e₁ v = e v :=
    fun v hv => he₁ v (by simpa [Fin.lt_def] using hv)
  have he₁w₂ : 2 * i + 2 ≤ (e₁ w₂ : ℕ) := by
    have h1 : e₁ w₂ ≠ e₁ w₁ := fun h => hne (e₁.injective h).symm
    rw [he₁w] at h1
    have h2 : ¬ (e₁ w₂ : ℕ) < 2 * i + 1 := fun h => by
      have := he₁' w₂ (Or.inr h); rw [this] at h; omega
    have h3 : (e₁ w₂ : ℕ) ≠ 2 * i + 1 := fun h => h1 (Fin.ext h)
    omega
  obtain ⟨e₂, he₂w, he₂⟩ := exists_move e₁ w₂ ⟨2 * i + 2, hp2⟩ (by rw [Fin.le_def]; exact he₁w₂)
  have he₂' : ∀ v, ((e₁ v : ℕ) < 2 * i + 2 ∨ (e₂ v : ℕ) < 2 * i + 2) → e₂ v = e₁ v :=
    fun v hv => he₂ v (by simpa [Fin.lt_def] using hv)
  have hagree : ∀ v, ((e v : ℕ) < 2 * i + 1 ∨ (e₂ v : ℕ) < 2 * i + 1) → e₂ v = e v := by
    intro v hv
    rcases hv with hv | hv
    · have h1 := he₁' v (Or.inl hv)
      rw [he₂' v (Or.inl (by rw [h1]; omega)), h1]
    · have h1 := he₂' v (Or.inr (by omega))
      rw [h1] at hv ⊢
      exact he₁' v (Or.inr hv)
  have hw₁2 : (e₂ w₁ : ℕ) = 2 * i + 1 := by
    rw [he₂' w₁ (Or.inl (by rw [he₁w]; simp)), he₁w]
  have hw₂2 : (e₂ w₂ : ℕ) = 2 * i + 2 := by rw [he₂w]
  have he₂s : (e₂ s : ℕ) = 0 := by rw [hagree s (Or.inl (by omega))]; exact he
  have hH := layer_agree hagree
  refine ⟨e₂, he₂s, hH, ?_⟩
  have hl₁ : layerOf e₂ w₁ = i + 1 := by simp only [layerOf, hw₁2]; omega
  have hl₂ : layerOf e₂ w₂ = i + 1 := by simp only [layerOf, hw₂2]; omega
  have hL : ∀ x, layerOf e₂ x = i + 1 → x = w₁ ∨ x = w₂ := by
    intro x hx
    simp only [layerOf] at hx
    have : (e₂ x : ℕ) = 2 * i + 1 ∨ (e₂ x : ℕ) = 2 * i + 2 := by omega
    rcases this with h | h
    · exact Or.inl (e₂.injective (Fin.ext (h.trans hw₁2.symm)))
    · exact Or.inr (e₂.injective (Fin.ext (h.trans hw₂2.symm)))
  have hq₂ := P.quiet_congr hH hq
  have hinf := P.not_informed_of_quiet (lay := layerOf e₂) (by simp [layerOf, he₂s]) hq₂
  have hws : ∀ w, 2 * i + 1 ≤ (e w : ℕ) → w ≠ s := fun w hw h => by subst h; omega
  refine P.quiet_of_same_window hne hl₁ hl₂ hL (fun t ht v hv => hinf t ht v hv) ?_
  intro t ht1 ht2
  rw [P.tx_isSome_eq_pat _ (hws w₁ hw₁), P.tx_isSome_eq_pat _ (hws w₂ hw₂), hl₁, hl₂,
    ← P.pat_congr hH]
  have := hsame (t - D₀) (by omega)
  rwa [show D₀ + (t - D₀) = t by omega] at this

/-- **Theorem 1 + Theorem 2, corrected (relative) form: one layer of the construction.** Let the
listing `e` fix layers `0, …, i`, and suppose layer `i` is quiet before round `D₀` (so layer
`i + 1` is not informed at time `D₀`). If `∑_{r ≤ k} C(d, r) < n - (2i + 1)` (the number of ids
not used in layers `≤ i`), then the two ids of layer `i + 1` can be chosen (keeping layers `≤ i`)
so that layer `i + 1` is quiet before round `D₀ + d`, i.e. it does not relay the message to
layer `i + 2` before round `D₀ + d` (`not_informed_of_quiet`). -/
theorem exists_extension_quiet {s : V} {k : ℕ} (hk : KShotOnFamily P s k)
    {e : V ≃ Fin (Fintype.card V)} (he : (e s : ℕ) = 0) {i D₀ d : ℕ}
    (hq : P.Quiet (familyGraph e) s (fun u => layerOf e u = i) D₀)
    (hcount : ∑ r ∈ range (k + 1), d.choose r + 2 * (i + 1) ≤ Fintype.card V) :
    ∃ e' : V ≃ Fin (Fintype.card V), (e' s : ℕ) = 0 ∧
      P.Quiet (familyGraph e') s (fun u => layerOf e' u = i + 1) (D₀ + d) := by
  classical
  have hsum : 1 ≤ ∑ r ∈ range (k + 1), d.choose r := by
    calc 1 = d.choose 0 := by simp
      _ ≤ _ := single_le_sum (f := fun r => d.choose r) (fun _ _ => Nat.zero_le _) (by simp)
  have hp1 : 2 * i + 1 < Fintype.card V := by omega
  have hp2 : 2 * i + 2 < Fintype.card V := by omega
  let A := univ.filter fun w => 2 * i + 1 ≤ (e w : ℕ)
  have hA : Fintype.card V - (2 * i + 1) ≤ #A := card_tail_ge e _
  let S : V → Finset ℕ := fun w =>
    (range d).filter fun r => P.pat (layerOf e) s (i + 1) w (D₀ + r) = true
  -- each unused id has a window pattern with at most `k` transmissions
  have hS : Set.MapsTo S A (smallSubsets d k) := by
    intro w hw
    simp only [A, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw
    refine mem_smallSubsets (filter_subset _ _) ?_
    obtain ⟨ew, hew, hagree⟩ := exists_move e w ⟨2 * i + 1, hp1⟩ (by rw [Fin.le_def]; exact hw)
    have hagree' : ∀ v, ((e v : ℕ) < 2 * i + 1 ∨ (ew v : ℕ) < 2 * i + 1) → ew v = e v :=
      fun v hv => hagree v (by simpa [Fin.lt_def] using hv)
    have hews : (ew s : ℕ) = 0 := by rw [hagree' s (Or.inl (by omega))]; exact he
    have hws : w ≠ s := by rintro rfl; omega
    have hlw : layerOf ew w = i + 1 := by simp only [layerOf, hew]; omega
    have hH := layer_agree hagree'
    have hpat : ∀ t, (P.tx (familyGraph ew) s t w).isSome = P.pat (layerOf e) s (i + 1) w t := by
      intro t
      rw [familyGraph, P.tx_isSome_eq_pat _ hws, hlw, P.pat_congr hH]
    refine le_trans ?_ (hk ew hews w (D₀ + d))
    refine card_le_card_of_injOn (fun r => D₀ + r) ?_ ?_
    · intro r hr
      simp only [S, coe_filter, mem_range, Set.mem_ofPred_eq] at hr
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, hpat]
      exact ⟨by omega, hr.2⟩
    · intro a _ b _ h; simpa using h
  obtain ⟨w₁, hw₁, w₂, hw₂, hne, hS12⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to
      (by have := card_smallSubsets_le d k; omega) hS
  simp only [A, mem_filter, mem_univ, true_and] at hw₁ hw₂
  obtain ⟨e', he', -, hq'⟩ := exists_extension_of_same_window P (d := d) he hq hp2 hne hw₁ hw₂ (by
    intro r hr
    have := congrArg (fun S => r ∈ S) hS12
    simp only [S, mem_filter, mem_range, eq_iff_iff] at this
    rw [Bool.eq_iff_iff]
    exact ⟨fun h => (this.1 ⟨hr, h⟩).2, fun h => (this.2 ⟨hr, h⟩).2⟩)
  exact ⟨e', he', hq'⟩

/-- The paper's transmission tree `T(π, G_i)`: the unused ids `A` (positions `≥ 2i + 1`) with the
transmission patterns they would have as members of layer `i + 1` (absolute rounds). -/
noncomputable def treeIds (e : V ≃ Fin (Fintype.card V)) (i : ℕ) : Finset V :=
  univ.filter fun w => 2 * i + 1 ≤ (e w : ℕ)

/-- **Theorem 1 of the paper (absolute form, as stated).** If the transmission tree `T(π, G_i)`
of the unused ids does not have height `≤ h`, then the two ids of layer `i + 1` can be chosen
(keeping layers `≤ i`) so that layer `i + 2` is not informed after `h` rounds, i.e. the relay
from layer `i + 1` to layer `i + 2` happens in the paper's round `height(T(π, G_i))` or later. -/
theorem exists_extension_of_not_heightLE {s : V} {e : V ≃ Fin (Fintype.card V)}
    (he : (e s : ℕ) = 0) {i h : ℕ} (hp2 : 2 * i + 2 < Fintype.card V)
    (hT : ¬ HeightLE (treeIds e i) (P.pat (layerOf e) s (i + 1)) h) :
    ∃ e' : V ≃ Fin (Fintype.card V), (e' s : ℕ) = 0 ∧
      (∀ v, layerOf e v ≤ i ∨ layerOf e' v ≤ i → layerOf e v = layerOf e' v) ∧
      ∀ v, layerOf e' v = i + 2 → ¬ P.informed (familyGraph e') s h v := by
  classical
  simp only [HeightLE, not_forall] at hT
  obtain ⟨x, hx, hcell⟩ := hT
  have hxc : x ∈ cell (treeIds e i) (P.pat (layerOf e) s (i + 1)) h x := mem_cell_self hx
  obtain ⟨y, hy, hyx⟩ : ∃ y ∈ cell (treeIds e i) (P.pat (layerOf e) s (i + 1)) h x, y ≠ x := by
    by_contra hc
    push Not at hc
    exact hcell (eq_singleton_iff_unique_mem.2 ⟨hxc, hc⟩)
  simp only [cell, mem_filter] at hy
  simp only [treeIds, mem_filter, mem_univ, true_and] at hx hy
  obtain ⟨e', he', hH, hq⟩ := exists_extension_of_same_window P (D₀ := 0) (d := h) he
    (fun t ht => absurd ht (Nat.not_lt_zero t)) hp2 hyx hy.1 hx
    (fun r hr => by simpa using hy.2 r hr)
  refine ⟨e', he', hH, fun v hv => ?_⟩
  have := P.not_informed_of_quiet (lay := layerOf e') (by simp [layerOf, he']) hq h
    (by simp) v hv
  exact this

/-- The construction of the paper's bad graph `G_π`, layer by layer. -/
theorem exists_quiet_layers {s : V} {k : ℕ} (hk : KShotOnFamily P s k) (d : ℕ → ℕ) :
    ∀ m, (∀ j < m, ∑ r ∈ range (k + 1), (d j).choose r + 2 * (j + 1) ≤ Fintype.card V) →
      ∃ e : V ≃ Fin (Fintype.card V), (e s : ℕ) = 0 ∧
        P.Quiet (familyGraph e) s (fun u => layerOf e u = m) (∑ j ∈ range m, d j) := by
  intro m
  induction m with
  | zero =>
    intro _
    obtain ⟨e, he, -⟩ := exists_move (Fintype.equivFin V) s
      ⟨0, Fintype.card_pos_iff.2 ⟨s⟩⟩ (by rw [Fin.le_def]; exact Nat.zero_le _)
    exact ⟨e, by rw [he], fun t ht => absurd ht (by simp)⟩
  | succ m ih =>
    intro hd
    obtain ⟨e, he, hq⟩ := ih (fun j hj => hd j (by omega))
    rw [sum_range_succ]
    exact exists_extension_quiet P hk he hq (hd m (by omega))

/-- **Theorem 3 of the paper (corrected proof; exact form).** Let `P` be any deterministic
adaptive protocol that is `k`-shot on the family `G` (correctness is not assumed). For any
`m` with `2m + 2 ≤ n` and any delays `d₀, …, d_{m-1}` with
`∑_{r ≤ k} C(d_j, r) + 2(j + 1) ≤ n`, some network of `G` (source at position `0`) is not fully
informed after `d₀ + ⋯ + d_{m-1}` rounds. -/
theorem exists_slow_network {s : V} {k : ℕ} (hk : KShotOnFamily P s k) (m : ℕ) (d : ℕ → ℕ)
    (hm : 2 * m + 2 ≤ Fintype.card V)
    (hd : ∀ j < m, ∑ r ∈ range (k + 1), (d j).choose r + 2 * (j + 1) ≤ Fintype.card V) :
    ∃ e : V ≃ Fin (Fintype.card V), (e s : ℕ) = 0 ∧
      ∃ v, ¬ P.informed (familyGraph e) s (∑ j ∈ range m, d j) v := by
  obtain ⟨e, he, hq⟩ := exists_quiet_layers P hk d m hd
  refine ⟨e, he, e.symm ⟨2 * m + 1, by omega⟩, ?_⟩
  exact P.not_informed_of_quiet (lay := layerOf e) (by simp [layerOf, he]) hq _ le_rfl _
    (by simp only [layerOf, Equiv.apply_symm_apply]; omega)

/-- **Theorem 3, uniform form.** If `(d + 1)^k ≤ ⌊n/2⌋` (and `n ≥ 2`), some network of `G` is
not fully informed after `⌊n/4⌋ · d` rounds. -/
theorem exists_slow_network_uniform {s : V} {k : ℕ} (hk : KShotOnFamily P s k)
    (hn : 2 ≤ Fintype.card V) (d : ℕ) (hd : (d + 1) ^ k ≤ Fintype.card V / 2) :
    ∃ e : V ≃ Fin (Fintype.card V), (e s : ℕ) = 0 ∧
      ∃ v, ¬ P.informed (familyGraph e) s (Fintype.card V / 4 * d) v := by
  have := exists_slow_network P hk (Fintype.card V / 4) (fun _ => d) (by omega) (fun j hj => by
    have := sum_choose_le_pow d k
    omega)
  simpa [sum_const, card_range, smul_eq_mul] using this

/-- **Theorem 3 of the paper, `Ω(n^{(k+1)/k})` form.** For every `k ≥ 1` and every
deterministic adaptive protocol that is `k`-shot on the family `G`, if `n ≥ 2 · 4^k` then some
`n`-node network of `G` contains a node that is still uninformed after every number of rounds
`T ≤ n^{1 + 1/k} / 32`. -/
theorem exists_slow_network_rpow {s : V} {k : ℕ} (hk : KShotOnFamily P s k) (hk1 : 1 ≤ k)
    (hn : 2 * 4 ^ k ≤ Fintype.card V) :
    ∃ e : V ≃ Fin (Fintype.card V), (e s : ℕ) = 0 ∧ ∃ v, ∀ T : ℕ,
      (T : ℝ) ≤ (Fintype.card V : ℝ) ^ (1 + 1 / (k : ℝ)) / 32 →
        ¬ P.informed (familyGraph e) s T v := by
  set n := Fintype.card V with hn_def
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have h4k : 4 ≤ 4 ^ k := Nat.le_self_pow (by omega) 4
  have hn8 : 8 ≤ n := by omega
  set x : ℝ := ((n : ℝ) / 2) ^ (1 / (k : ℝ)) with hx
  have hn2 : (4 : ℝ) ^ k ≤ (n : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : 4 ^ k * 2 ≤ n)
  have hxk : x ^ k = (n : ℝ) / 2 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), one_div_mul_cancel hk0,
      Real.rpow_one]
  have hx4 : 4 ≤ x := by
    have : ((4 : ℝ) ^ k) ^ (1 / (k : ℝ)) ≤ x := Real.rpow_le_rpow (by positivity) hn2 (by positivity)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_one_div_cancel hk0,
      Real.rpow_one] at this
  set f := ⌊x⌋₊ with hf
  have hf4 : 4 ≤ f := Nat.le_floor (by exact_mod_cast hx4)
  have hfx : (f : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxf : x < f + 1 := Nat.lt_floor_add_one x
  have hd : (f - 1 + 1) ^ k ≤ n / 2 := by
    rw [Nat.sub_add_cancel (by omega), ← Nat.floor_div_eq_div (K := ℝ)]
    apply Nat.le_floor
    push_cast
    rw [← hxk]
    exact pow_le_pow_left₀ (by positivity) hfx k
  obtain ⟨e, he, v, hv⟩ := exists_slow_network_uniform P hk (by omega) (f - 1) hd
  refine ⟨e, he, v, fun T hT hi => hv (P.informed_mono ?_ hi)⟩
  -- `T ≤ ⌊n/4⌋ · (f - 1)`
  have h2k : (2 : ℝ) ^ (1 / (k : ℝ)) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / (k : ℝ)) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num)
            (by rw [div_le_one (by positivity)]; exact_mod_cast hk1)
      _ = 2 := Real.rpow_one 2
  have hxn : (n : ℝ) ^ (1 / (k : ℝ)) ≤ 2 * x := by
    rw [hx, Real.div_rpow (by positivity) (by norm_num)]
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    have : 0 ≤ (n : ℝ) ^ (1 / (k : ℝ)) := by positivity
    nlinarith
  have hpow : (n : ℝ) ^ (1 + 1 / (k : ℝ)) = n * (n : ℝ) ^ (1 / (k : ℝ)) := by
    rw [Real.rpow_add (by positivity), Real.rpow_one]
  have hn4 : (n : ℝ) / 8 ≤ ((n / 4 : ℕ) : ℝ) := by
    have : n ≤ 4 * (n / 4) + 3 := by omega
    have : (n : ℝ) ≤ 4 * ((n / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast this
    have : (8 : ℝ) ≤ n := by exact_mod_cast hn8
    linarith
  have hd1 : x / 2 ≤ ((f - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hTle : (T : ℝ) ≤ ((n / 4 * (f - 1) : ℕ) : ℝ) := by
    push_cast
    rw [hpow] at hT
    have h1 : 0 ≤ (n : ℝ) := by positivity
    have h2 : 0 ≤ x := by linarith
    calc (T : ℝ) ≤ n * (n : ℝ) ^ (1 / (k : ℝ)) / 32 := hT
      _ ≤ n * (2 * x) / 32 := by gcongr
      _ = ((n : ℝ) / 8) * (x / 2) := by ring
      _ ≤ ((n / 4 : ℕ) : ℝ) * ((f - 1 : ℕ) : ℝ) := by
        apply mul_le_mul hn4 hd1 (by positivity) (by positivity)
  exact_mod_cast hTle

end Family

/-! ## Non-vacuity, and why absolute tree heights do not add up -/

section Examples

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The protocol in which node `v` transmits exactly once, in round `idx v`, regardless of what
it knows (a spontaneous transmission, allowed in the paper's model). -/
def onceProtocol (idx : V → ℕ) : Protocol V Unit Unit where
  init _ _ := ()
  act v t _ := if t = idx v then some () else none
  δ _ _ _ _ := ()

/-- `onceProtocol` is `1`-shot on the family: the `k`-shot hypothesis is satisfiable by a
protocol that transmits. -/
theorem onceProtocol_kShot (idx : V → ℕ) (s : V) : KShotOnFamily (onceProtocol idx) s 1 := by
  intro e _ v T
  refine card_le_one.2 fun a ha b hb => ?_
  rw [Finset.mem_filter] at ha hb
  simp only [Protocol.tx, onceProtocol] at ha hb
  split_ifs at ha hb <;> simp_all

/-- For `onceProtocol` with injective `idx < B`, *every* absolute transmission tree `T(π, G_i)`
(any listing, any layer) has height `≤ B`: the ids are separated by the spontaneous transmissions
before any message arrives. So Theorem 1 (absolute form) bounds the relay round of every layer by
the same `height ≤ B`; these absolute bounds do not add up over the layers. A `k`-shot protocol
can spend one shot this way and still have `k - 1` shots left. -/
theorem onceProtocol_heightLE {idx : V → ℕ} (hidx : Function.Injective idx) {B : ℕ}
    (hB : ∀ v, idx v < B) (e : V ≃ Fin (Fintype.card V)) (s : V) (i : ℕ) :
    HeightLE (treeIds e i) ((onceProtocol idx).pat (layerOf e) s (i + 1)) B := by
  intro x hx
  ext y
  rw [cell, Finset.mem_filter, Finset.mem_singleton]
  simp only [Protocol.pat, onceProtocol]
  constructor
  · rintro ⟨-, hy⟩
    have := hy (idx x) (hB x)
    by_contra hne
    have : idx x ≠ idx y := fun h => hne (hidx h).symm
    simp_all
  · rintro rfl; exact ⟨hx, fun _ _ => rfl⟩

end Examples

end Podc.KShotRadioBroadcast.Adaptive
