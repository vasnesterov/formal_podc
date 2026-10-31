import Papers.PODC2015.DeterministicLoadBalancing.Model

/-!
# The potentials `φ_t(c)` and `φ'_t(c)` of good `s`-balancers

Berenbrink, Klasing, Kosowski, Mallmann-Trenn, Uznański, *Improved Analysis of Deterministic
Load-Balancing Schemes*, PODC 2015 (arXiv:1404.4344v4), Section 3 and Appendix B.

Graphs need not be regular: node `v` has `D v = deg v + dl` edges in `G⁺`, and the thresholds are
`c · D v` per node (for `d`-regular graphs this is the paper's `c·d⁺`). All quantities are natural
numbers, truncated subtraction playing the role of `max{·, 0}`.

* `phi G dl c x = ∑_v max{x v − c·D v, 0}` (the paper's `φ_t(c)`), `drop` is the paper's `Δ_t(c, u)`;
* `phi' G dl s c x = ∑_v max{c·D v + s − x v, 0}` (the paper's `φ'_t(c)`), `drop'` is `Δ'_t(c, u)`.

## Main results

* `phi_step`, `lemma_3_5`: Lemma 3.5 (one-step drop of `φ`), `phi_antitone`.
* `phi'_step`, `lemma_3_7`: Lemma 3.7 (one-step drop of `φ'`), `phi'_antitone`.
* `observation_3_6_false`, `observation_3_8_false`: Observations 3.6 / 3.8 as printed (drop
  `∑ max{s, ·}`) are false, already for a good `2`-balancer on `K₂` with two self-loops per node.
* `observation_3_6`, `observation_3_8`: the corrected versions (drop `∑ min{s, ·}`, which is what
  the paper uses in Appendix B.4).

## Proof technique

Instead of the paper's token colouring we use a capacity argument. For `φ`: every sender `u`
sends a fair share over each of its edges, so either all its edge values are `≥ c` (if
`⌊x_u/D_u⌋ ≥ c`) or all are `≤ c`; hence `∑_{e out of u} (f_e − c)⁺ = (x_u − c D_u)⁺`. At a
receiver `v`, `(x'_v − c D_v)⁺ ≤ ∑_{e into v} (f_e − c)⁺`, and self-preference yields the extra
`min{s, x_v − c D_v}` on `v`'s own self-loops. For `φ'` the self-loops of a node are lumped into one
edge of capacity `c·dl + s`, every original edge has capacity `c`, and the same bookkeeping is done
with `(b_e − f_e)⁺`.
-/

open Finset

namespace Podc.DeterministicLoadBalancing

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-! ### Definitions -/

section Defs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The potential `φ_t(c) = ∑_v max{x_t(v) − c·d⁺, 0}` (Section 3), with the per-node threshold
`c · D v`, `D v = deg v + dl`. -/
def phi (dl c : ℕ) (x : V → ℕ) : ℕ := ∑ v, (x v - c * (G.degree v + dl))

/-- The potential `φ'_t(c) = ∑_v max{c·d⁺ + s − x_t(v), 0}` (Section 3), with the per-node threshold
`c · D v`, `D v = deg v + dl`. -/
def phi' (dl s c : ℕ) (x : V → ℕ) : ℕ := ∑ v, (c * (G.degree v + dl) + s - x v)

end Defs

/-- The drop `Δ_t(c, u)` of Lemma 3.5 at a node with threshold `θ = c·d⁺` whose load goes from `x`
(time `t − 1`) to `x'` (time `t`). -/
def drop (θ s x x' : ℕ) : ℕ :=
  if x' < x ∧ θ < x ∧ x' < θ + s then min x (θ + s) - max x' θ else 0

/-- The drop `Δ'_t(c, u)` of Lemma 3.7 at a node with threshold `θ = c·d⁺` whose load goes from `x`
(time `t − 1`) to `x'` (time `t`). -/
def drop' (θ s x x' : ℕ) : ℕ :=
  if x < x' ∧ x < θ + s ∧ θ < x' then min x' (θ + s) - max x θ else 0

/-! ### Auxiliary sum lemmas -/

section SumAux

variable {ι : Type*} (S : Finset ι) (f : ι → ℕ) (c : ℕ)

private lemma sum_tsub_add_card_mul (h : ∀ i ∈ S, c ≤ f i) :
    ∑ i ∈ S, (f i - c) + #S * c = ∑ i ∈ S, f i := by
  rw [← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i hi => Nat.sub_add_cancel (h i hi)

private lemma sum_le_sum_tsub_add_card_mul :
    ∑ i ∈ S, f i ≤ ∑ i ∈ S, (f i - c) + #S * c := by
  rw [← smul_eq_mul, ← Finset.sum_const, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => le_tsub_add

private lemma sum_tsub_eq_zero (h : ∀ i ∈ S, f i ≤ c) : ∑ i ∈ S, (f i - c) = 0 :=
  Finset.sum_eq_zero fun i hi => Nat.sub_eq_zero_of_le (h i hi)

private lemma sum_le_card_mul (h : ∀ i ∈ S, f i ≤ c) : ∑ i ∈ S, f i ≤ #S * c := by
  simpa using Finset.sum_le_card_nsmul S f c h

private lemma const_tsub_sum_add (h : ∀ i ∈ S, f i ≤ c) :
    ∑ i ∈ S, (c - f i) + ∑ i ∈ S, f i = #S * c := by
  rw [← Finset.sum_add_distrib, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_congr rfl fun i hi => Nat.sub_add_cancel (h i hi)

private lemma card_mul_le_const_tsub_sum_add :
    #S * c ≤ ∑ i ∈ S, (c - f i) + ∑ i ∈ S, f i := by
  rw [← Finset.sum_add_distrib, ← smul_eq_mul, ← Finset.sum_const]
  exact Finset.sum_le_sum fun i _ => le_tsub_add

private lemma const_tsub_sum_eq_zero (h : ∀ i ∈ S, c ≤ f i) : ∑ i ∈ S, (c - f i) = 0 :=
  Finset.sum_eq_zero fun i hi => Nat.sub_eq_zero_of_le (h i hi)

private lemma card_mul_le_sum (h : ∀ i ∈ S, c ≤ f i) : #S * c ≤ ∑ i ∈ S, f i := by
  simpa using Finset.card_nsmul_le_sum S f c h

end SumAux

/-! ### Local consequences of `GoodStep` -/

section Local

variable {dl s k x keep : ℕ} {out : V → ℕ} {N : Finset V}

/-- What a good step guarantees locally, with `q = ⌊x/k⌋`: the self-loops carry at least
`dl·q + min{s, x mod k}` and at most `dl·(q+1)` tokens, every original edge carries `q` or `q+1`. -/
lemma GoodStep.bounds (h : GoodStep dl s k x out N keep) :
    dl * (x / k) + min s (x % k) ≤ keep ∧ keep ≤ dl * (x / k) + dl ∧
      ∀ w ∈ N, x / k ≤ out w ∧ out w ≤ x / k + 1 := by
  obtain ⟨hout, g, hg, hfair, hpref⟩ := h
  refine ⟨?_, ?_, fun w hw => ?_⟩
  · rw [← hg]
    have hi : ∀ i, x / k + (if g i = x / k + 1 then 1 else 0) ≤ g i := fun i => by
      rcases hfair i with h | ⟨_, h⟩ <;> split_ifs <;> omega
    calc dl * (x / k) + min s (x % k) ≤ dl * (x / k) + #{i | g i = x / k + 1} := by omega
      _ = ∑ i, (x / k + if g i = x / k + 1 then 1 else 0) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul, Finset.card_filter]
      _ ≤ ∑ i, g i := Finset.sum_le_sum fun i _ => hi i
  · rw [← hg]
    calc ∑ i, g i ≤ ∑ _i : Fin dl, (x / k + 1) :=
          Finset.sum_le_sum fun i _ => by rcases hfair i with h | ⟨_, h⟩ <;> omega
      _ = dl * (x / k) + dl := by simp [Nat.mul_succ]
  · rcases hout w hw with h | ⟨_, h⟩ <;> omega

variable {c : ℕ}

/-- Sender side for `φ`: `(keep − c·dl)⁺ + ∑_w (out w − c)⁺ = (x − c·D)⁺`. -/
lemma GoodStep.sender_phi (h : GoodStep dl s (#N + dl) x out N keep)
    (hcons : keep + ∑ w ∈ N, out w = x) :
    (keep - c * dl) + ∑ w ∈ N, (out w - c) = x - c * (#N + dl) := by
  obtain ⟨h1, h2, h3⟩ := h.bounds
  generalize x / (#N + dl) = q at h1 h2 h3
  rw [Nat.mul_add, Nat.mul_comm c #N, Nat.mul_comm c dl]
  rcases le_or_gt c q with hq | hq
  · have hc : ∀ w ∈ N, c ≤ out w := fun w hw => hq.trans (h3 w hw).1
    have e := sum_tsub_add_card_mul N out c hc
    have : dl * c ≤ dl * q := Nat.mul_le_mul_left _ hq
    omega
  · have hc : ∀ w ∈ N, out w ≤ c := fun w hw => (h3 w hw).2.trans hq
    have e := sum_tsub_eq_zero N out c hc
    have e2 := sum_le_card_mul N out c hc
    have : dl * (q + 1) ≤ dl * c := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ] at this
    omega

/-- The excess over the self-loops of a node with load `x > c·D` is at least `min{s, x − c·D}`
(self-preference). -/
lemma GoodStep.loop_excess (h : GoodStep dl s (#N + dl) x out N keep) (hs : s ≤ dl)
    (hdl : 0 < dl) : min s (x - c * (#N + dl)) ≤ keep - c * dl := by
  obtain ⟨h1, h2, -⟩ := h.bounds
  have hdm := Nat.div_add_mod x (#N + dl)
  have hml := Nat.mod_lt x (show 0 < #N + dl by omega)
  generalize x / (#N + dl) = q at h1 h2 hdm
  generalize x % (#N + dl) = r at h1 hdm hml
  rw [Nat.mul_comm c, Nat.mul_comm c dl]
  rcases lt_trichotomy q c with hq | rfl | hq
  · have : (#N + dl) * (q + 1) ≤ (#N + dl) * c := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ] at this
    omega
  · omega
  · have : dl * (c + 1) ≤ dl * q := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ] at this
    omega

/-- Receiver side for `φ`: `(x' − c·D)⁺ + Δ ≤ (keep − c·dl)⁺ + ∑_w (in w − c)⁺`, where `x'` is the
new load (own kept tokens plus the inflow from the neighbours) and `x` the old load. -/
lemma GoodStep.receiver_phi {inflow : V → ℕ} (h : GoodStep dl s (#N + dl) x out N keep)
    (hs : s ≤ dl) (hdl : 0 < dl) :
    (keep + ∑ w ∈ N, inflow w - c * (#N + dl)) +
        drop (c * (#N + dl)) s x (keep + ∑ w ∈ N, inflow w)
      ≤ (keep - c * dl) + ∑ w ∈ N, (inflow w - c) := by
  have hin := sum_le_sum_tsub_add_card_mul N inflow c
  have hloop := h.loop_excess (c := c) hs hdl
  have e : c * (#N + dl) = #N * c + c * dl := by ring
  rw [e] at hloop ⊢
  unfold drop
  split_ifs <;> omega

/-- Sender side for `φ'` (self-loops lumped into one edge of capacity `c·dl + s`, original edges
of capacity `c`): `(c·dl + s − keep)⁺ + ∑_w (c − out w)⁺ ≤ (c·D + s − x)⁺`. -/
lemma GoodStep.sender_phi' (h : GoodStep dl s (#N + dl) x out N keep)
    (hcons : keep + ∑ w ∈ N, out w = x) (hs : s ≤ dl) :
    (c * dl + s - keep) + ∑ w ∈ N, (c - out w) ≤ c * (#N + dl) + s - x := by
  obtain ⟨h1, h2, h3⟩ := h.bounds
  have hdm := Nat.div_add_mod x (#N + dl)
  generalize x / (#N + dl) = q at h1 h2 h3 hdm
  generalize x % (#N + dl) = r at h1 hdm
  rw [Nat.mul_add, Nat.mul_comm c #N, Nat.mul_comm c dl]
  rcases lt_trichotomy q c with hq | rfl | hq
  · have hc : ∀ w ∈ N, out w ≤ c := fun w hw => (h3 w hw).2.trans hq
    have e := const_tsub_sum_add N out c hc
    have : dl * (q + 1) ≤ dl * c := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ] at this
    omega
  · have hc : ∀ w ∈ N, q ≤ out w := fun w hw => (h3 w hw).1
    have e := const_tsub_sum_eq_zero N out q hc
    have e2 := card_mul_le_sum N out q hc
    rw [Nat.add_mul] at hdm
    omega
  · have hc : ∀ w ∈ N, c ≤ out w := fun w hw => (Nat.le_of_lt hq).trans (h3 w hw).1
    have e := const_tsub_sum_eq_zero N out c hc
    have : dl * (c + 1) ≤ dl * q := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ] at this
    omega

/-- The gap under the lumped self-loop capacity of a node with load `x < c·D + s` is at least
`min{s, c·D + s − x}` (self-preference). -/
lemma GoodStep.loop_gap (h : GoodStep dl s (#N + dl) x out N keep)
    (hcons : keep + ∑ w ∈ N, out w = x) (hs : s ≤ dl)
    (hx : x < c * (#N + dl) + s) :
    min s (c * (#N + dl) + s - x) ≤ c * dl + s - keep := by
  obtain ⟨h1, h2, h3⟩ := h.bounds
  have hdm := Nat.div_add_mod x (#N + dl)
  generalize x / (#N + dl) = q at h1 h2 h3 hdm
  generalize x % (#N + dl) = r at h1 hdm
  rw [Nat.mul_add, Nat.mul_comm c #N, Nat.mul_comm c dl] at hx ⊢
  rcases lt_trichotomy q c with hq | rfl | hq
  · have : dl * (q + 1) ≤ dl * c := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ] at this
    omega
  · have hc : ∀ w ∈ N, q ≤ out w := fun w hw => (h3 w hw).1
    have e2 := card_mul_le_sum N out q hc
    rw [Nat.add_mul] at hdm
    omega
  · have : (#N + dl) * (c + 1) ≤ (#N + dl) * q := Nat.mul_le_mul_left _ hq
    rw [Nat.mul_succ, Nat.add_mul] at this
    omega

/-- Receiver side for `φ'`: `(c·D + s − x')⁺ + Δ' ≤ (c·dl + s − keep)⁺ + ∑_w (c − in w)⁺`. -/
lemma GoodStep.receiver_phi' {inflow : V → ℕ} (h : GoodStep dl s (#N + dl) x out N keep)
    (hcons : keep + ∑ w ∈ N, out w = x) (hs : s ≤ dl) :
    (c * (#N + dl) + s - (keep + ∑ w ∈ N, inflow w)) +
        drop' (c * (#N + dl)) s x (keep + ∑ w ∈ N, inflow w)
      ≤ (c * dl + s - keep) + ∑ w ∈ N, (c - inflow w) := by
  have hin := card_mul_le_const_tsub_sum_add N inflow c
  have hgap := fun hx => h.loop_gap (c := c) hcons hs hx
  have e : c * (#N + dl) = #N * c + c * dl := by ring
  rw [e] at hgap ⊢
  unfold drop'
  split_ifs with hd
  · have := hgap hd.2.1
    omega
  · omega

end Local

/-! ### One-step lemmas -/

section Step

variable {G : SimpleGraph V} [DecidableRel G.Adj] {dl s : ℕ}

/-- One step of any execution in which every node performs a good step (Lemma 3.5, one-step form):
with loads `x`, flows `out u w` and kept tokens `keep u`, the new loads
`x' v = keep v + ∑_{w ∼ v} out w v` satisfy `φ(x') + ∑_v Δ(c, x v, x' v) ≤ φ(x)`. -/
theorem phi_step (c : ℕ) (x : V → ℕ) (out : V → V → ℕ) (keep : V → ℕ)
    (hcons : ∀ u, keep u + ∑ w ∈ G.neighborFinset u, out u w = x u)
    (hgood : ∀ u, GoodStep dl s (G.degree u + dl) (x u) (out u) (G.neighborFinset u) (keep u))
    (hs : s ≤ dl) (hdl : 0 < dl) :
    phi G dl c (fun v => keep v + ∑ w ∈ G.neighborFinset v, out w v) +
        ∑ v, drop (c * (G.degree v + dl)) s (x v) (keep v + ∑ w ∈ G.neighborFinset v, out w v)
      ≤ phi G dl c x := by
  unfold phi
  rw [← Finset.sum_add_distrib]
  calc _ ≤ ∑ v, ((keep v - c * dl) + ∑ w ∈ G.neighborFinset v, (out w v - c)) :=
        Finset.sum_le_sum fun v _ => (hgood v).receiver_phi hs hdl
    _ = ∑ u, ((keep u - c * dl) + ∑ w ∈ G.neighborFinset u, (out u w - c)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          sum_sum_neighbor_swap G (fun w v => out w v - c)]
    _ = _ := Finset.sum_congr rfl fun u _ => (hgood u).sender_phi (hcons u)

/-- One step of any execution in which every node performs a good step (Lemma 3.7, one-step form):
`φ'(x') + ∑_v Δ'(c, x v, x' v) ≤ φ'(x)`. -/
theorem phi'_step (c : ℕ) (x : V → ℕ) (out : V → V → ℕ) (keep : V → ℕ)
    (hcons : ∀ u, keep u + ∑ w ∈ G.neighborFinset u, out u w = x u)
    (hgood : ∀ u, GoodStep dl s (G.degree u + dl) (x u) (out u) (G.neighborFinset u) (keep u))
    (hs : s ≤ dl) :
    phi' G dl s c (fun v => keep v + ∑ w ∈ G.neighborFinset v, out w v) +
        ∑ v, drop' (c * (G.degree v + dl)) s (x v) (keep v + ∑ w ∈ G.neighborFinset v, out w v)
      ≤ phi' G dl s c x := by
  unfold phi'
  rw [← Finset.sum_add_distrib]
  calc _ ≤ ∑ v, ((c * dl + s - keep v) + ∑ w ∈ G.neighborFinset v, (c - out w v)) :=
        Finset.sum_le_sum fun v _ => (hgood v).receiver_phi' (hcons v) hs
    _ = ∑ u, ((c * dl + s - keep u) + ∑ w ∈ G.neighborFinset u, (c - out u w)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          sum_sum_neighbor_swap G (fun w v => c - out w v)]
    _ ≤ _ := Finset.sum_le_sum fun u _ => (hgood u).sender_phi' (hcons u) hs

end Step

/-! ### Lemmas 3.5 and 3.7 for balancers -/

section Balancer

variable {G : SimpleGraph V} [DecidableRel G.Adj] {dl s : ℕ} (A : Balancer G)

lemma Balancer.load_succ_eq (x₀ : V → ℕ) (t : ℕ) :
    A.load x₀ (t + 1) = fun v => A.kept x₀ t v + ∑ w ∈ G.neighborFinset v, A.flow x₀ t w v :=
  funext (A.load_succ x₀ t)

/-- Lemma 3.5 for any balancer whose every step is good (only the one-step part of
Definition 3.1 and `s ≤ d◦` are used). -/
theorem lemma_3_5_of_goodStep
    (hgood : ∀ v σ x, GoodStep dl s (G.degree v + dl) x (A.out v σ x) (G.neighborFinset v)
      (A.keep v σ x))
    (hs : s ≤ dl) (hdl : 0 < dl) (c : ℕ) (x₀ : V → ℕ) (t : ℕ) :
    phi G dl c (A.load x₀ (t + 1)) +
        ∑ v, drop (c * (G.degree v + dl)) s (A.load x₀ t v) (A.load x₀ (t + 1) v)
      ≤ phi G dl c (A.load x₀ t) := by
  rw [A.load_succ_eq]
  exact phi_step c (A.load x₀ t) (A.flow x₀ t) (A.kept x₀ t) (A.kept_add_sum_flow x₀ t)
    (fun u => hgood u _ _) hs hdl

/-- **Lemma 3.5** (monotonicity of potential). For a good `s`-balancer,
`φ_{t+1}(c) ≤ φ_t(c) − ∑_u Δ_{t+1}(c, u)`. -/
theorem lemma_3_5 (hA : A.IsGood dl s) (c : ℕ) (x₀ : V → ℕ) (t : ℕ) :
    phi G dl c (A.load x₀ (t + 1)) +
        ∑ v, drop (c * (G.degree v + dl)) s (A.load x₀ t v) (A.load x₀ (t + 1) v)
      ≤ phi G dl c (A.load x₀ t) :=
  lemma_3_5_of_goodStep A hA.2.2.2 hA.2.1 (by have := hA.1; have := hA.2.1; omega) c x₀ t

/-- Lemma 3.5, first part: `φ_t(c)` is non-increasing in time. -/
theorem phi_antitone (hA : A.IsGood dl s) (c : ℕ) (x₀ : V → ℕ) :
    Antitone fun t => phi G dl c (A.load x₀ t) :=
  antitone_nat_of_succ_le fun t => le_trans (Nat.le_add_right _ _) (lemma_3_5 A hA c x₀ t)

/-- Lemma 3.7 for any balancer whose every step is good. -/
theorem lemma_3_7_of_goodStep
    (hgood : ∀ v σ x, GoodStep dl s (G.degree v + dl) x (A.out v σ x) (G.neighborFinset v)
      (A.keep v σ x))
    (hs : s ≤ dl) (c : ℕ) (x₀ : V → ℕ) (t : ℕ) :
    phi' G dl s c (A.load x₀ (t + 1)) +
        ∑ v, drop' (c * (G.degree v + dl)) s (A.load x₀ t v) (A.load x₀ (t + 1) v)
      ≤ phi' G dl s c (A.load x₀ t) := by
  rw [A.load_succ_eq]
  exact phi'_step c (A.load x₀ t) (A.flow x₀ t) (A.kept x₀ t) (A.kept_add_sum_flow x₀ t)
    (fun u => hgood u _ _) hs

/-- **Lemma 3.7.** For a good `s`-balancer, `φ'_{t+1}(c) ≤ φ'_t(c) − ∑_u Δ'_{t+1}(c, u)`. -/
theorem lemma_3_7 (hA : A.IsGood dl s) (c : ℕ) (x₀ : V → ℕ) (t : ℕ) :
    phi' G dl s c (A.load x₀ (t + 1)) +
        ∑ v, drop' (c * (G.degree v + dl)) s (A.load x₀ t v) (A.load x₀ (t + 1) v)
      ≤ phi' G dl s c (A.load x₀ t) :=
  lemma_3_7_of_goodStep A hA.2.2.2 hA.2.1 c x₀ t

/-- Lemma 3.7, first part: `φ'_t(c)` is non-increasing in time. -/
theorem phi'_antitone (hA : A.IsGood dl s) (c : ℕ) (x₀ : V → ℕ) :
    Antitone fun t => phi' G dl s c (A.load x₀ t) :=
  antitone_nat_of_succ_le fun t => le_trans (Nat.le_add_right _ _) (lemma_3_7 A hA c x₀ t)

end Balancer

/-! ### Interval versions (Observations 3.6 and 3.8) -/

section Interval

private lemma telescope_drop (P : ℕ → ℕ) (Δ : ℕ → ℕ) (hP : ∀ τ, P (τ + 1) + Δ τ ≤ P τ)
    (t t' : ℕ) (h : t ≤ t') : P t' + ∑ τ ∈ Ico t t', Δ τ ≤ P t := by
  induction t', h using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn]; have := hP n; omega

private lemma telescope_node (y : ℕ → ℕ) (Δ : ℕ → ℕ) (hy : ∀ τ, y τ - y (τ + 1) ≤ Δ τ)
    (a b : ℕ) (h : a ≤ b) : y a - y b ≤ ∑ τ ∈ Ico a b, Δ τ := by
  induction b, h using Nat.le_induction with
  | base => simp
  | succ n hn ih => rw [Finset.sum_Ico_succ_top hn]; have := hy n; omega

/-- Abstract interval drop: if a potential `P` drops by `∑_v Δ τ v` in step `τ`, and each `Δ τ v`
bounds the decrease of a per-node quantity `y τ v`, then over `[t, t']` the potential drops by
`∑_{u ∈ U} y t u` for any set `U` of nodes whose `y` reaches `0` within `[t, t']`. -/
lemma potential_interval_drop (P : ℕ → ℕ) (Δ : ℕ → V → ℕ) (y : ℕ → V → ℕ)
    (hP : ∀ τ, P (τ + 1) + ∑ v, Δ τ v ≤ P τ) (hy : ∀ τ v, y τ v - y (τ + 1) v ≤ Δ τ v)
    {t t' : ℕ} (htt' : t ≤ t') (U : Finset V)
    (hU : ∀ u ∈ U, ∃ tu, t ≤ tu ∧ tu ≤ t' ∧ y tu u = 0) :
    P t' + ∑ u ∈ U, y t u ≤ P t := by
  have h1 := telescope_drop P (fun τ => ∑ v, Δ τ v) hP t t' htt'
  have h2 : ∑ u ∈ U, y t u ≤ ∑ τ ∈ Ico t t', ∑ v, Δ τ v := by
    rw [Finset.sum_comm]
    calc ∑ u ∈ U, y t u ≤ ∑ u ∈ U, ∑ τ ∈ Ico t t', Δ τ u := by
          refine Finset.sum_le_sum fun u hu => ?_
          obtain ⟨tu, ht, ht', h0⟩ := hU u hu
          calc y t u = y t u - y tu u := by rw [h0, Nat.sub_zero]
            _ ≤ ∑ τ ∈ Ico t tu, Δ τ u :=
                telescope_node (fun τ => y τ u) (fun τ => Δ τ u) (fun τ => hy τ u) t tu ht
            _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right ht')
      _ ≤ ∑ v, ∑ τ ∈ Ico t t', Δ τ v := Finset.sum_le_sum_of_subset (Finset.subset_univ U)
  omega

variable {G : SimpleGraph V} [DecidableRel G.Adj] {dl s : ℕ} (A : Balancer G)

/-- **Observation 3.6**, corrected (drop `min{s, ·}` instead of the printed `max{s, ·}`; this is the
form used in Appendix B.4). Let `t ≤ t'` and let `U` be a set of nodes `u` each of which has load
at most `c·d⁺` at some moment `t_u ∈ [t, t']`. Then
`φ_{t'}(c) ≤ φ_t(c) − ∑_{u ∈ U} min{s, x_t(u) − c·d⁺}`. (The paper's hypothesis
`x_t(u) ≥ c·d⁺ + 1` is not needed: otherwise the summand is `0`.) -/
theorem observation_3_6 (hA : A.IsGood dl s) (c : ℕ) (x₀ : V → ℕ) {t t' : ℕ} (htt' : t ≤ t')
    (U : Finset V)
    (hU : ∀ u ∈ U, ∃ tu, t ≤ tu ∧ tu ≤ t' ∧ A.load x₀ tu u ≤ c * (G.degree u + dl)) :
    phi G dl c (A.load x₀ t') + ∑ u ∈ U, min s (A.load x₀ t u - c * (G.degree u + dl))
      ≤ phi G dl c (A.load x₀ t) := by
  refine potential_interval_drop (fun τ => phi G dl c (A.load x₀ τ))
    (fun τ v => drop (c * (G.degree v + dl)) s (A.load x₀ τ v) (A.load x₀ (τ + 1) v))
    (fun τ v => min s (A.load x₀ τ v - c * (G.degree v + dl))) (lemma_3_5 A hA c x₀)
    (fun τ v => ?_) htt' U (fun u hu => ?_)
  · simp only [drop]
    split_ifs <;> omega
  · obtain ⟨tu, h1, h2, h3⟩ := hU u hu
    exact ⟨tu, h1, h2, by omega⟩

/-- **Observation 3.8**, corrected (drop `min{s, ·}` instead of the printed `max{s, ·}`). Let
`t ≤ t'` and let `U` be a set of nodes `u` each of which has load at least `c·d⁺ + s` at some moment
`t_u ∈ [t, t']`. Then `φ'_{t'}(c) ≤ φ'_t(c) − ∑_{u ∈ U} min{s, c·d⁺ + s − x_t(u)}`. (The paper's
hypothesis `x_t(u) < c·d⁺ + s` is not needed: otherwise the summand is `0`.) -/
theorem observation_3_8 (hA : A.IsGood dl s) (c : ℕ) (x₀ : V → ℕ) {t t' : ℕ} (htt' : t ≤ t')
    (U : Finset V)
    (hU : ∀ u ∈ U, ∃ tu, t ≤ tu ∧ tu ≤ t' ∧ c * (G.degree u + dl) + s ≤ A.load x₀ tu u) :
    phi' G dl s c (A.load x₀ t') + ∑ u ∈ U, min s (c * (G.degree u + dl) + s - A.load x₀ t u)
      ≤ phi' G dl s c (A.load x₀ t) := by
  refine potential_interval_drop (fun τ => phi' G dl s c (A.load x₀ τ))
    (fun τ v => drop' (c * (G.degree v + dl)) s (A.load x₀ τ v) (A.load x₀ (τ + 1) v))
    (fun τ v => min s (c * (G.degree v + dl) + s - A.load x₀ τ v)) (lemma_3_7 A hA c x₀)
    (fun τ v => ?_) htt' U (fun u hu => ?_)
  · simp only [drop']
    split_ifs <;> omega
  · obtain ⟨tu, h1, h2, h3⟩ := hU u hu
    exact ⟨tu, h1, h2, by omega⟩

end Interval

/-! ### Observations 3.6 and 3.8 as printed are false -/

section Counterexample

lemma k2_degree (v : Fin 2) : (⊤ : SimpleGraph (Fin 2)).degree v = 1 := by
  fin_cases v <;> decide

/-- `SEND(⌊x/3⌋)` on `K₂` (one original edge, two self-loops per node, `d⁺ = 3`): every node sends
`⌊x/3⌋` tokens to its neighbour and keeps the rest. -/
def k2Send : Balancer (⊤ : SimpleGraph (Fin 2)) :=
  Balancer.stateless ⊤ (fun _ x _ => x / 3) (fun _ x => x - x / 3) (by
    intro v x
    rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, k2_degree, one_smul]
    have := Nat.div_le_self x 3
    omega)

/-- `k2Send` is a good `2`-balancer (with `d◦ = 2`). -/
theorem k2Send_isGood : k2Send.IsGood 2 2 := by
  refine ⟨by norm_num, le_rfl, fun x₀ t v => ⟨fun w _ => ?_, ?_, fun w₁ _ w₂ _ => ?_⟩,
    fun v σ x => ?_⟩
  · rw [k2_degree]; exact le_rfl
  · rw [k2_degree]
    refine ⟨![k2Send.load x₀ t v / 3, k2Send.load x₀ t v - k2Send.load x₀ t v / 3 -
      k2Send.load x₀ t v / 3], ?_, fun i => ?_⟩
    · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      show _ = k2Send.load x₀ t v - k2Send.load x₀ t v / 3
      omega
    · fin_cases i
      · simp
      · simp; omega
  · exact le_of_eq rfl |>.trans (Nat.le_add_right _ _)
  · rw [k2_degree]
    show GoodStep 2 2 3 x (fun _ => x / 3) _ (x - x / 3)
    refine ⟨fun w _ => Or.inl rfl, ?_⟩
    obtain h | h | h : x % 3 = 0 ∨ x % 3 = 1 ∨ x % 3 = 2 := by omega
    · refine ⟨![x / 3, x / 3], ?_, fun i => ?_, ?_⟩
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
      · fin_cases i <;> exact Or.inl rfl
      · simp [h]
    · refine ⟨![x / 3 + 1, x / 3], ?_, fun i => ?_, ?_⟩
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
      · fin_cases i
        · exact Or.inr ⟨by omega, rfl⟩
        · exact Or.inl rfl
      · rw [Finset.card_filter, Fin.sum_univ_two]; simp [h]
    · refine ⟨![x / 3 + 1, x / 3 + 1], ?_, fun i => ?_, ?_⟩
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]; omega
      · fin_cases i <;> exact Or.inr ⟨by omega, rfl⟩
      · rw [Finset.card_filter, Fin.sum_univ_two]; simp [h]

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Observation 3.6 **as printed**: for `t ≤ t'` and `U` a set of nodes with `x_t(u) ≥ c·d⁺ + 1`
that have load `≤ c·d⁺` at some `t_u ∈ [t, t']`,
`φ_{t'}(c) ≤ φ_t(c) − ∑_{u ∈ U} max{s, x_t(u) − c·d⁺}` (in `ℤ`). -/
def Observation36Printed (A : Balancer G) (dl s : ℕ) : Prop :=
  ∀ (c : ℕ) (x₀ : V → ℕ) (t t' : ℕ) (U : Finset V), t ≤ t' →
    (∀ u ∈ U, c * (G.degree u + dl) + 1 ≤ A.load x₀ t u ∧
      ∃ tu, t ≤ tu ∧ tu ≤ t' ∧ A.load x₀ tu u ≤ c * (G.degree u + dl)) →
    (phi G dl c (A.load x₀ t') : ℤ) ≤ phi G dl c (A.load x₀ t) -
      ∑ u ∈ U, max (s : ℤ) ((A.load x₀ t u : ℤ) - c * (G.degree u + dl))

/-- Observation 3.8 **as printed**: for `t ≤ t'` and `U` a set of nodes with `x_t(u) < c·d⁺ + s`
that have load `≥ c·d⁺ + s` at some `t_u ∈ [t, t']`,
`φ'_{t'}(c) ≤ φ'_t(c) − ∑_{u ∈ U} max{s, c·d⁺ + s − x_t(u)}` (in `ℤ`). -/
def Observation38Printed (A : Balancer G) (dl s : ℕ) : Prop :=
  ∀ (c : ℕ) (x₀ : V → ℕ) (t t' : ℕ) (U : Finset V), t ≤ t' →
    (∀ u ∈ U, A.load x₀ t u < c * (G.degree u + dl) + s ∧
      ∃ tu, t ≤ tu ∧ tu ≤ t' ∧ c * (G.degree u + dl) + s ≤ A.load x₀ tu u) →
    (phi' G dl s c (A.load x₀ t') : ℤ) ≤ phi' G dl s c (A.load x₀ t) -
      ∑ u ∈ U, max (s : ℤ) (c * (G.degree u + dl) + s - (A.load x₀ t u : ℤ))

/-- **Observation 3.6 as printed is false.** `k2Send` is a good `2`-balancer on `K₂` (`d = 1`,
`d◦ = s = 2`, `d⁺ = 3`); with `c = 1` and loads `(4, 0)`, node `0` sends one token and keeps
`3`, the loads become `(3, 1)` and `φ(1)` drops from `1` to `0`, while the printed bound demands a
drop of `max{s, 4 − 3} = 2`. -/
theorem observation_3_6_false : k2Send.IsGood 2 2 ∧ ¬ Observation36Printed k2Send 2 2 := by
  refine ⟨k2Send_isGood, fun h => ?_⟩
  have := h 1 ![4, 0] 0 1 {0} (by norm_num) (by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact ⟨by decide, 1, by norm_num, le_rfl, by decide⟩)
  revert this
  decide

/-- **Observation 3.8 as printed is false.** For `k2Send` with `c = 0` (threshold `c·d⁺ + s = 2`)
and loads `(1, 3)`, the loads become `(2, 2)` and `φ'(0)` drops from `1` to `0`, while the printed
bound demands a drop of `max{s, 2 − 1} = 2`. -/
theorem observation_3_8_false : k2Send.IsGood 2 2 ∧ ¬ Observation38Printed k2Send 2 2 := by
  refine ⟨k2Send_isGood, fun h => ?_⟩
  have := h 0 ![1, 3] 0 1 {0} (by norm_num) (by
    intro u hu
    rw [Finset.mem_singleton] at hu
    subst hu
    exact ⟨by decide, 1, by norm_num, le_rfl, by decide⟩)
  revert this
  decide

end Counterexample

end Podc.DeterministicLoadBalancing
