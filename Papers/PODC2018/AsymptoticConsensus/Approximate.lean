import Papers.PODC2018.AsymptoticConsensus.LowerBounds
import Papers.PODC2018.AsymptoticConsensus.Psi
import Papers.PODC2018.AsymptoticConsensus.Exact
import Cslib.Foundations.Data.Real.Logb

/-!
# Approximate consensus: decision-time lower bounds (FNS'18, Section 9, Theorems 8–11)

An approximate consensus algorithm is given `ε` and `Δ` (baked into the algorithm here) and has to
decide; decisions must be `ε`-close (ε-Agreement) and lie in the convex hull of the initial values
(Validity), for every execution whose initial values have diameter `≤ Δ`.

* `DAlg`: a deterministic full-information algorithm with a decision function
  `dec : σ → Option V` (`none` = undecided).
* `DAlg.DecidesBy A N Δ ε T`: in every execution with pattern in `N` and initial diameter `≤ Δ`,
  at time `T` all agents have decided, decisions are pairwise `ε`-close and valid. Only the
  configuration at time `T` is constrained, so this is *weaker* than the paper's specification
  (irrevocable decisions at times `≤ T`), and the lower bounds below are stronger.
* `DAlg.decSet A Q s C`: the decisions reachable from `C` after `s` more rounds of a pattern
  in `Q` (the finite-horizon valency); `DAlg.ReachLeft A N Δ T s C`: `C` occurs in an admissible
  execution with `s` rounds left.

## Main results

* `ediam_le_pow_mul_of_chains`: the abstract finite-horizon chain engine.
* `DAlg.DecidesBy.ediam_decSet_blocks_le` (block moves, as in `Engine.lean`) and
  `DAlg.DecidesBy.ediam_decSet_le`, `DAlg.DecidesBy.dist_le_of_chains` (single graphs).
* `DAlg.DecidesBy.decSet_inter_of_closed` (finite-horizon Lemmas 7/20),
  `DAlg.DecidesBy.dec_of_closed`, `DAlg.DecidesBy.le_of_not_rooted` (a non-rooted graph in `N`
  forces `Δ ≤ ε`).
* **Theorem 8** (`theorem8`, `theorem8_logb`): `n = 2`, `{H₀, H₁, H₂} ⊆ N`: `Δ ≤ 3^T ε`, i.e.
  `T ≥ log₃(Δ/ε)`.
* **Theorem 9** (`theorem9`, `theorem9_deaf`, `theorem9_logb`, `theorem9_nonsplit`): `n ≥ 3`,
  `deaf(G) ⊆ N`: `Δ ≤ 2^T ε`, i.e. `T ≥ log₂(Δ/ε)`.
* **Theorem 10** (`theorem10`, `theorem10_logb`, `theorem10_rooted`): `n ≥ 4`, `Ψ₁, Ψ₂, Ψ₃ ∈ N`:
  `Δ ≤ 2^⌊T/(n-2)⌋ ε`, hence `T ≥ (n-2) log₂(Δ/ε)`. The `T mod (n-2)` leftover rounds are
  played (as `Ψ₀`) *before* the blocks; during them agent `1` cannot hear agent `0`
  (`psi0_agree_aux`).
* **Theorem 11** (`theorem11`, `theorem11_logb`): `n ≥ 2`, `N` source-incompatible with
  α-diameter `≤ D`: `Δ ≤ (n-1)(D+1)^T ε` (paper: `n` instead of `n - 1`), i.e.
  `T ≥ log_{D+1}(Δ/((n-1)ε))`.

The paper derives these theorems from the contraction-rate bounds by turning an approximate
consensus algorithm into an asymptotic one. We instead run the valency argument directly on
decisions at the finite horizon `T` (the "valency" of a configuration with `k` rounds left is the
set of decisions reachable in exactly `k` more rounds).
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Set
open scoped ENNReal

/-- **Finite-horizon chain engine.** Let `W k C` be a set attached to a state `C` with `k` moves
left. If `W (k+1) C` is covered by the sets `W k (mv m C)` of the successors (`m ∈ K`, finite), any
two successors are connected by a chain of length `≤ D` of consecutively intersecting successor
sets, the invariant `Inv` is preserved by moves and `diam (W 0 C) ≤ B` at the horizon, then
`diam (W k C) ≤ (D+1)^k B`.
-- CSLib candidate -/
theorem ediam_le_pow_mul_of_chains {Γ M V : Type*} [PseudoEMetricSpace V] (mv : M → Γ → Γ)
    (K : Finset M) (hK : K.Nonempty) (W : ℕ → Γ → Set V) (Inv : ℕ → Γ → Prop) (D : ℕ)
    (B : ℝ≥0∞) (h0 : ∀ C, Inv 0 C → Metric.ediam (W 0 C) ≤ B)
    (hcover : ∀ k C, Inv (k + 1) C → W (k + 1) C ⊆ ⋃ m ∈ K, W k (mv m C))
    (hinv : ∀ k C, Inv (k + 1) C → ∀ m ∈ K, Inv k (mv m C))
    (hchain : ∀ k C, Inv (k + 1) C → ∀ a ∈ K, ∀ b ∈ K,
      ChainLE K (fun m => W k (mv m C)) D a b) :
    ∀ k C, Inv k C → Metric.ediam (W k C) ≤ ((D : ℝ≥0∞) + 1) ^ k * B := by
  intro k
  induction k with
  | zero => intro C hC; simpa using h0 C hC
  | succ k ih =>
    intro C hC
    obtain ⟨m, hm, hle⟩ := exists_ediam_le_mul K hK (fun m => W k (mv m C)) (W (k + 1) C)
      (hcover k C hC) D (hchain k C hC)
    calc Metric.ediam (W (k + 1) C) ≤ (D + 1) * Metric.ediam (W k (mv m C)) := hle
      _ ≤ (D + 1) * ((D + 1) ^ k * B) := by gcongr; exact ih _ (hinv k C hC m hm)
      _ = ((D : ℝ≥0∞) + 1) ^ (k + 1) * B := by rw [pow_succ]; ring

variable {α σ V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Two initial values at distance exactly `Δ`. -/
theorem exists_dist_eq [Nontrivial V] {Δ : ℝ} (hΔ : 0 ≤ Δ) : ∃ w : V, dist 0 w = Δ := by
  obtain ⟨w, hw⟩ := exists_norm_eq V hΔ
  exact ⟨w, by rw [dist_comm, dist_zero_right, hw]⟩

omit [NormedSpace ℝ V] in
/-- A vector with values in `{v, w}` has diameter `≤ Δ` if `dist v w ≤ Δ`. -/
theorem adm_two {Δ : ℝ} (hΔ : 0 ≤ Δ) {v w : V} (hvw : dist v w ≤ Δ) {x : α → V}
    (hx : ∀ i, x i = v ∨ x i = w) : ∀ i j, dist (x i) (x j) ≤ Δ := by
  intro i j
  rcases hx i with hi | hi <;> rcases hx j with hj | hj <;> rw [hi, hj] <;>
    simp [hΔ, hvw, dist_comm w v ▸ hvw]

/-- A deterministic full-information algorithm with decisions: `init i v` is the initial state of
agent `i` with initial value `v`, `step` the transition function, and `dec s` the decision
recorded in state `s` (`none` if undecided); the same data as an exact consensus algorithm
(`EAlg`). The parameters `ε`, `Δ` are fixed in the algorithm. -/
abbrev DAlg (α σ V : Type*) := EAlg α σ V

namespace DAlg

variable (A : DAlg α σ V)

/-- `A` solves approximate consensus in `N` with parameters `Δ`, `ε` and has decided at time `T`:
in every execution with pattern in `N` and initial values of diameter `≤ Δ`, at time `T` every
agent has decided (Termination), any two decisions are `ε`-close (ε-Agreement), and decisions lie
in the convex hull of the initial values (Validity). -/
structure DecidesBy (N : Set (Graph α)) (Δ ε : ℝ) (T : ℕ) : Prop where
  termination : ∀ x : α → V, (∀ i j, dist (x i) (x j) ≤ Δ) → ∀ p ∈ Pat N, ∀ i,
    ∃ v, A.dec (conf A.step (A.initC x) p T i) = some v
  agreement : ∀ x : α → V, (∀ i j, dist (x i) (x j) ≤ Δ) → ∀ p ∈ Pat N, ∀ i j v w,
    A.dec (conf A.step (A.initC x) p T i) = some v →
    A.dec (conf A.step (A.initC x) p T j) = some w → dist v w ≤ ε
  validity : ∀ x : α → V, (∀ i j, dist (x i) (x j) ≤ Δ) → ∀ p ∈ Pat N, ∀ i v,
    A.dec (conf A.step (A.initC x) p T i) = some v → v ∈ convexHull ℝ (range x)

/-- `C` occurs in an admissible execution (pattern in `N`, initial diameter `≤ Δ`) with `s`
rounds left before the decision time `T`. -/
def ReachLeft (N : Set (Graph α)) (Δ : ℝ) (T s : ℕ) (C : α → σ) : Prop :=
  ∃ x : α → V, (∀ i j, dist (x i) (x j) ≤ Δ) ∧ ∃ p ∈ Pat N, s ≤ T ∧
    conf A.step (A.initC x) p (T - s) = C

/-- The decisions reachable from `C` after exactly `s` more rounds of a pattern in `Q`
(finite-horizon valency). -/
def decSet (Q : Set (ℕ → Graph α)) (s : ℕ) (C : α → σ) : Set V :=
  {v | ∃ q ∈ Q, ∃ i, A.dec (conf A.step C q s i) = some v}

variable {A}

omit [NormedSpace ℝ V] in
theorem ReachLeft.run {N : Set (Graph α)} {Δ : ℝ} {T s t : ℕ} {C : α → σ}
    (hC : A.ReachLeft N Δ T (s + t) C) {q : ℕ → Graph α} (hq : q ∈ Pat N) :
    A.ReachLeft N Δ T s (conf A.step C q t) := by
  obtain ⟨x, hx, p, hp, hle, rfl⟩ := hC
  refine ⟨x, hx, splice p (T - (s + t)) q, splice_mem_pat hp hq _, by omega, ?_⟩
  rw [show T - s = T - (s + t) + t by omega, conf_splice]

omit [NormedSpace ℝ V] in
theorem ReachLeft.next {N : Set (Graph α)} {Δ : ℝ} {T s : ℕ} {C : α → σ}
    (hC : A.ReachLeft N Δ T (s + 1) C) {G : Graph α} (hG : G ∈ N) :
    A.ReachLeft N Δ T s (next A.step G C) :=
  hC.run (q := fun _ => G) (const_mem_pat hG)

omit [NormedSpace ℝ V] in
theorem reachLeft_initC {N : Set (Graph α)} (hN : N.Nonempty) {Δ : ℝ} {T : ℕ} {x : α → V}
    (hx : ∀ i j, dist (x i) (x j) ≤ Δ) : A.ReachLeft N Δ T T (A.initC x) := by
  obtain ⟨G, hG⟩ := hN
  exact ⟨x, hx, fun _ => G, const_mem_pat hG, le_rfl, by simp⟩

/-- At the decision time, the decision set has diameter at most `ε` (ε-Agreement). -/
theorem DecidesBy.ediam_decSet_zero {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) (Q : Set (ℕ → Graph α)) {C : α → σ}
    (hC : A.ReachLeft N Δ T 0 C) : Metric.ediam (A.decSet Q 0 C) ≤ ENNReal.ofReal ε := by
  obtain ⟨x, hx, p, hp, -, rfl⟩ := hC
  refine Metric.ediam_le fun v hv w hw => ?_
  obtain ⟨_, -, i, hi⟩ := hv
  obtain ⟨_, -, j, hj⟩ := hw
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hA.agreement x hx p hp i j v w (by simpa using hi)
    (by simpa using hj))

/-- **Intersection via a deaf continuation** (the finite-horizon Lemma 7). If agent `ℓ` is in the
same state in `C₁` and `C₂`, `C₁` occurs with `s` rounds left, and some pattern of `Q` keeps `ℓ`
deaf, then the decision sets of `C₁` and `C₂` intersect. -/
theorem DecidesBy.decSet_inter_of_deaf {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) {Q : Set (ℕ → Graph α)} (hQ : Q ⊆ Pat N) {q : ℕ → Graph α}
    (hq : q ∈ Q) {ℓ : α} (hdeaf : ∀ t, Deaf (q t) ℓ) {s : ℕ} {C₁ C₂ : α → σ}
    (h₁ : A.ReachLeft N Δ T s C₁) (heq : C₁ ℓ = C₂ ℓ) :
    (A.decSet Q s C₁ ∩ A.decSet Q s C₂).Nonempty := by
  have h := (show A.ReachLeft N Δ T (0 + s) C₁ by simpa using h₁).run (hQ hq)
  obtain ⟨x, hx, p, hp, -, hpC⟩ := h
  obtain ⟨v, hv⟩ := hA.termination x hx p hp ℓ
  rw [Nat.sub_zero] at hpC
  rw [hpC] at hv
  refine ⟨v, ⟨q, hq, ℓ, hv⟩, q, hq, ℓ, ?_⟩
  rwa [← conf_agree_deaf hdeaf hdeaf heq]

/-- A deaf agent decides its own initial value (Validity in the constant execution). -/
theorem DecidesBy.mem_decSet_of_deaf {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) (hΔ : 0 ≤ Δ) {Q : Set (ℕ → Graph α)} (hQ : Q ⊆ Pat N)
    {q : ℕ → Graph α} (hq : q ∈ Q) {i : α} (hdeaf : ∀ t, Deaf (q t) i) (x : α → V) :
    x i ∈ A.decSet Q T (A.initC x) := by
  set y : α → V := fun _ => x i
  have hy : ∀ a b, dist (y a) (y b) ≤ Δ := fun a b => by simpa [y] using hΔ
  obtain ⟨u, hu⟩ := hA.termination y hy q (hQ hq) i
  have hval := hA.validity y hy q (hQ hq) i u hu
  have : Nonempty α := ⟨i⟩
  have hr : range y = {x i} := range_const
  rw [hr, convexHull_singleton, mem_singleton_iff] at hval
  subst hval
  refine ⟨q, hq, i, ?_⟩
  rw [conf_agree_deaf hdeaf hdeaf (C := A.initC x) (C' := A.initC y) rfl]
  exact hu

/-! ### The engine for block moves -/

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
theorem decSet_blockPat_subset {K : Set ι} {blk : ι → ℕ → Graph α} {L : ℕ} (hL : 0 < L)
    (k : ℕ) (C : α → σ) :
    A.decSet (BlockPat K blk L) (L * (k + 1)) C ⊆
      ⋃ m ∈ K, A.decSet (BlockPat K blk L) (L * k) (conf A.step C (blk m) L) := by
  rintro v ⟨_, ⟨c, hc, rfl⟩, i, hi⟩
  refine mem_biUnion (hc 0) ⟨_, blockSeq_mem (fun k => hc (1 + k)) (L := L) (blk := blk), i, ?_⟩
  have h1 := shift_blockSeq blk hL c 1
  rw [mul_one] at h1
  rw [show L * (k + 1) = L + L * k by ring, conf_add, h1, conf_blockSeq_block C blk hL c] at hi
  exact hi

/-- **Lower-bound engine for block moves.** If, from every configuration occurring with
`L (k+1)` rounds left, the decision sets (`L k` rounds left, block patterns) of any two
block-successors are joined by a chain of length `≤ D`, then every configuration occurring with
`L k` rounds left has a decision set of diameter `≤ (D+1)^k ε`. -/
theorem DecidesBy.ediam_decSet_blocks_le {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) (K : Finset ι) (hK : K.Nonempty) (blk : ι → ℕ → Graph α)
    {L : ℕ} (hL : 0 < L) (hblk : ∀ m ∈ K, ∀ t, blk m t ∈ N) (D : ℕ)
    (hchain : ∀ k C, A.ReachLeft N Δ T (L * (k + 1)) C → ∀ a ∈ K, ∀ b ∈ K,
      ChainLE K (fun m => A.decSet (BlockPat (K : Set ι) blk L) (L * k)
        (conf A.step C (blk m) L)) D a b)
    (k : ℕ) (C : α → σ) (hC : A.ReachLeft N Δ T (L * k) C) :
    Metric.ediam (A.decSet (BlockPat (K : Set ι) blk L) (L * k) C) ≤
      ((D : ℝ≥0∞) + 1) ^ k * ENNReal.ofReal ε :=
  ediam_le_pow_mul_of_chains (fun m C => conf A.step C (blk m) L) K hK
    (fun k C => A.decSet (BlockPat (K : Set ι) blk L) (L * k) C)
    (fun k C => A.ReachLeft N Δ T (L * k) C) D _
    (fun C hC => by simpa using hA.ediam_decSet_zero _ (by simpa using hC))
    (fun k C _ => by simpa using decSet_blockPat_subset (A := A) (K := (K : Set ι)) hL k C)
    (fun k C hC m hm => (show A.ReachLeft N Δ T (L * k + L) C by
      rwa [← Nat.mul_succ]).run (fun t => hblk m hm t))
    hchain k C hC

/-! ### The engine for network models (single graphs) -/

/-- **Lower-bound engine for network models.** If, from every configuration occurring with
`k+1` rounds left, the `k`-round decision sets (in the finite submodel `K ⊆ N`) of any two
successors `G.C`, `H.C` (`G, H ∈ K`) are joined by a chain of length `≤ D`, then every
configuration occurring with `k` rounds left has a decision set of diameter `≤ (D+1)^k ε`. -/
theorem DecidesBy.ediam_decSet_le {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) (K : Finset (Graph α)) (hK : K.Nonempty)
    (hKN : ∀ G ∈ K, G ∈ N) (D : ℕ)
    (hchain : ∀ k C, A.ReachLeft N Δ T (k + 1) C → ∀ G ∈ K, ∀ H ∈ K,
      ChainLE K (fun G => A.decSet (Pat (K : Set (Graph α))) k (next A.step G C)) D G H)
    (k : ℕ) (C : α → σ) (hC : A.ReachLeft N Δ T k C) :
    Metric.ediam (A.decSet (Pat (K : Set (Graph α))) k C) ≤
      ((D : ℝ≥0∞) + 1) ^ k * ENNReal.ofReal ε := by
  have h := hA.ediam_decSet_blocks_le K hK (fun G _ => G) one_pos (fun G hG _ => hKN G hG) D
    (fun k C hC a ha b hb => by
      rw [blockPat_one, one_mul]; exact hchain k C (by simpa using hC) a ha b hb)
    k C (by simpa using hC)
  rwa [blockPat_one, one_mul] at h

theorem DecidesBy.eps_nonneg [Nonempty α] {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) (hΔ : 0 ≤ Δ) (hN : N.Nonempty) : 0 ≤ ε := by
  obtain ⟨G, hG⟩ := hN
  obtain ⟨i⟩ := ‹Nonempty α›
  have hx : ∀ a b : α, dist ((fun _ => (0 : V)) a) ((fun _ => (0 : V)) b) ≤ Δ := by simpa
  obtain ⟨u, hu⟩ := hA.termination _ hx _ (const_mem_pat hG) i
  simpa using hA.agreement _ hx _ (const_mem_pat hG) i i u u hu hu

theorem pow_mul_ofReal (D k : ℕ) (ε : ℝ) :
    ((D : ℝ≥0∞) + 1) ^ k * ENNReal.ofReal ε = ENNReal.ofReal (((D : ℝ) + 1) ^ k * ε) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
    ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast, ENNReal.ofReal_one]

omit [NormedSpace ℝ V] in
theorem dist_le_of_edist_le {v w : V} {a : ℝ} (ha : 0 ≤ a) (h : edist v w ≤ ENNReal.ofReal a) :
    dist v w ≤ a := by
  rwa [edist_dist, ENNReal.ofReal_le_ofReal_iff ha] at h

/-- Single-graph engine, distance form: any two decisions reachable in `T` rounds (in `K`) from an
admissible initial configuration are at distance `≤ (D+1)^T ε`. -/
theorem DecidesBy.dist_le_of_chains {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) (K : Finset (Graph α)) (hK : K.Nonempty)
    (hKN : ∀ G ∈ K, G ∈ N) (D : ℕ)
    (hchain : ∀ k C, A.ReachLeft N Δ T (k + 1) C → ∀ G ∈ K, ∀ H ∈ K,
      ChainLE K (fun G => A.decSet (Pat (K : Set (Graph α))) k (next A.step G C)) D G H)
    {x : α → V} (hx : ∀ i j, dist (x i) (x j) ≤ Δ) {v w : V}
    (hv : v ∈ A.decSet (Pat (K : Set (Graph α))) T (A.initC x))
    (hw : w ∈ A.decSet (Pat (K : Set (Graph α))) T (A.initC x)) :
    dist v w ≤ ((D : ℝ) + 1) ^ T * ε := by
  obtain ⟨G, hG⟩ := hK
  have hN : N.Nonempty := ⟨G, hKN G hG⟩
  have h := hA.ediam_decSet_le K ⟨G, hG⟩ hKN D hchain T (A.initC x)
    (by simpa using reachLeft_initC hN hx)
  have hε : 0 ≤ ε := by
    obtain ⟨_, -, i, -⟩ := hv
    have : Nonempty α := ⟨i⟩
    exact hA.eps_nonneg ((dist_nonneg).trans (hx i i)) hN
  rw [pow_mul_ofReal] at h
  exact dist_le_of_edist_le (by positivity) ((Metric.edist_le_ediam_of_mem hv hw).trans h)

/-! ### Closed sets of agents -/

/-- Agents of a set `S` that only hears itself along `p` decide the common initial value `u` of
`S` (Validity in the constant execution). -/
theorem DecidesBy.dec_of_closed {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) (hΔ : 0 ≤ Δ) {p : ℕ → Graph α} (hp : p ∈ Pat N) {S : Set α}
    (hS : ∀ t, ∀ i ∈ S, ∀ j, Hears (p t) i j → j ∈ S) {x : α → V} {u : V}
    (hxu : ∀ i ∈ S, x i = u) {i : α} (hi : i ∈ S) :
    A.dec (conf A.step (A.initC x) p T i) = some u := by
  have hy : ∀ a b : α, dist ((fun _ => u) a) ((fun _ => u) b) ≤ Δ := by simp [hΔ]
  obtain ⟨u', hu'⟩ := hA.termination _ hy p hp i
  have hval := hA.validity _ hy p hp i u' hu'
  have : Nonempty α := ⟨i⟩
  rw [range_const, convexHull_singleton, mem_singleton_iff] at hval
  subst hval
  rw [conf_agree S (fun _ _ _ => SameIn.refl _ _) hS (C' := A.initC fun _ => u')
    (fun a ha => by simp [hxu a ha]) T i hi]
  exact hu'

/-- **Intersection via a closed set** (finite-horizon Lemmas 7 and 20). If `C₁`, `C₂` agree on
a nonempty set `S` of agents that is closed (only hears itself) along some `q ∈ Q`, and `C₁`
occurs with `s` rounds left, the decision sets of `C₁` and `C₂` intersect. -/
theorem DecidesBy.decSet_inter_of_closed {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) {Q : Set (ℕ → Graph α)} (hQ : Q ⊆ Pat N) {q : ℕ → Graph α}
    (hq : q ∈ Q) {S : Set α} (hSne : S.Nonempty) (hS : ∀ t, ∀ i ∈ S, ∀ j, Hears (q t) i j → j ∈ S)
    {s : ℕ} {C₁ C₂ : α → σ} (h₁ : A.ReachLeft N Δ T s C₁) (heq : ∀ i ∈ S, C₁ i = C₂ i) :
    (A.decSet Q s C₁ ∩ A.decSet Q s C₂).Nonempty := by
  obtain ⟨ℓ, hℓ⟩ := hSne
  have h := (show A.ReachLeft N Δ T (0 + s) C₁ by simpa using h₁).run (hQ hq)
  obtain ⟨x, hx, p, hp, -, hpC⟩ := h
  obtain ⟨v, hv⟩ := hA.termination x hx p hp ℓ
  rw [Nat.sub_zero] at hpC
  rw [hpC] at hv
  refine ⟨v, ⟨q, hq, ℓ, hv⟩, q, hq, ℓ, ?_⟩
  rwa [← conf_agree S (fun _ _ _ => SameIn.refl _ _) hS heq s ℓ hℓ]

/-- Decisions reachable from an admissible initial configuration are valid. -/
theorem DecidesBy.mem_hull_of_mem_decSet {N : Set (Graph α)} {Δ ε : ℝ} {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) {Q : Set (ℕ → Graph α)} (hQ : Q ⊆ Pat N) {x : α → V}
    (hx : ∀ i j, dist (x i) (x j) ≤ Δ) {v : V} (hv : v ∈ A.decSet Q T (A.initC x)) :
    v ∈ convexHull ℝ (range x) := by
  obtain ⟨q, hq, i, hi⟩ := hv
  exact hA.validity x hx q (hQ hq) i v hi

/-- **Rootedness is necessary.** If some graph `G ∈ N` has no root, then `G` splits the agents
into two nonempty closed sets, which can decide on any two initial values; hence `Δ ≤ ε`
(approximate consensus with `ε < Δ` is impossible). -/
theorem DecidesBy.le_of_not_rooted [Finite α] [Nonempty α] [Nontrivial V] {N : Set (Graph α)}
    {Δ ε : ℝ} {T : ℕ} (hA : A.DecidesBy N Δ ε T) (hΔ : 0 ≤ Δ) {G : Graph α} (hG : G ∈ N)
    (hno : ∀ r, ¬ Cslib.DynNet.IsRoot G r) : Δ ≤ ε := by
  classical
  have := Fintype.ofFinite α
  let anc : α → Finset α := fun i => Finset.univ.filter fun j => Relation.ReflTransGen G j i
  obtain ⟨i, -, hmin⟩ := Finset.univ.exists_min_image (fun i => (anc i).card)
    Finset.univ_nonempty
  obtain ⟨y, hy⟩ : ∃ y, ¬ Relation.ReflTransGen G i y := by
    simpa [Cslib.DynNet.IsRoot] using hno i
  let S1 : Set α := {j | Relation.ReflTransGen G j i}
  let S2 : Set α := {j | ¬ Relation.ReflTransGen G i j}
  have hdisj : ∀ z ∈ S1, z ∉ S2 := by
    intro z hz1 hz2
    have hsub : anc z ⊆ anc i := fun k hk => by
      simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact hk.trans hz1
    have hi : i ∉ anc z := by
      simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and]; exact hz2
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
      ⟨hsub, fun h => hi (h ▸ (Finset.mem_filter.2 ⟨Finset.mem_univ _,
        Relation.ReflTransGen.refl⟩))⟩)
    exact absurd (hmin z (Finset.mem_univ _)) (not_le.2 hlt)
  have hS1 : ∀ t, ∀ a ∈ S1, ∀ j, Hears ((fun _ : ℕ => G) t) a j → j ∈ S1 := by
    intro t a ha j hj
    rcases hj with rfl | hj
    · exact ha
    · exact Relation.ReflTransGen.head hj ha
  have hS2 : ∀ t, ∀ a ∈ S2, ∀ j, Hears ((fun _ : ℕ => G) t) a j → j ∈ S2 := by
    intro t a ha j hj
    rcases hj with rfl | hj
    · exact ha
    · exact fun h => ha (h.tail hj)
  obtain ⟨w, hw⟩ := exists_dist_eq (V := V) hΔ
  let x : α → V := fun j => if j ∈ S2 then w else 0
  have hx : ∀ a b, dist (x a) (x b) ≤ Δ :=
    adm_two hΔ hw.le (v := 0) (w := w) fun a => by by_cases h : a ∈ S2 <;> simp [x, h]
  have h1 := hA.dec_of_closed hΔ (const_mem_pat hG) hS1 (x := x) (u := 0)
    (fun a ha => by simp [x, hdisj a ha]) (i := i) Relation.ReflTransGen.refl
  have h2 := hA.dec_of_closed hΔ (const_mem_pat hG) hS2 (x := x) (u := w)
    (fun a ha => by simp [x, ha]) (i := y) hy
  have := hA.agreement x hx _ (const_mem_pat hG) i y 0 w h1 h2
  rwa [hw] at this

end DAlg

/-! ### Theorem 8: two agents -/

open DAlg

variable {σ V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Theorem 8 of FNS'18.** For `n = 2` agents and a network model containing `H₀, H₁, H₂`, if an
approximate consensus algorithm (parameters `Δ`, `ε`) has decided at time `T` in all admissible
executions, then `Δ ≤ 3^T ε`; i.e. some execution with initial diameter `≤ Δ` has decision time
at least `log₃(Δ/ε)`. -/
theorem theorem8 [Nontrivial V] (A : DAlg (Fin 2) σ V) {N : Set (Graph (Fin 2))}
    (hN : ({H0, H1, H2} : Set (Graph (Fin 2))) ⊆ N) {Δ ε : ℝ} (hΔ : 0 ≤ Δ) {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) : Δ ≤ 3 ^ T * ε := by
  have hKN : ∀ G ∈ N3, G ∈ N := fun G hG => hN (by simpa [N3] using hG)
  have hQ : Pat (N3 : Set (Graph (Fin 2))) ⊆ Pat N := pat_mono fun G hG => hKN G hG
  have m0 : H0 ∈ N3 := by simp [N3]
  have m1 : H1 ∈ N3 := by simp [N3]
  have m2 : H2 ∈ N3 := by simp [N3]
  set Y := fun (k : ℕ) (C : Fin 2 → σ) (G : Graph (Fin 2)) =>
    A.decSet (Pat (N3 : Set (Graph (Fin 2)))) k (next A.step G C)
  have i01 : ∀ k C, A.ReachLeft N Δ T (k + 1) C → (Y k C H0 ∩ Y k C H1).Nonempty :=
    fun k C hC => hA.decSet_inter_of_deaf hQ (const_mem_pat (by simpa using m2))
      (fun _ => deaf_H2) (hC.next (hKN _ m0)) (next_eq_of_agree sameIn_H0_H1 fun _ _ => rfl)
  have i02 : ∀ k C, A.ReachLeft N Δ T (k + 1) C → (Y k C H0 ∩ Y k C H2).Nonempty :=
    fun k C hC => hA.decSet_inter_of_deaf hQ (const_mem_pat (by simpa using m1))
      (fun _ => deaf_H1) (hC.next (hKN _ m0)) (next_eq_of_agree sameIn_H0_H2 fun _ _ => rfl)
  obtain ⟨w, hw⟩ := exists_dist_eq (V := V) hΔ
  set x : Fin 2 → V := fun i => if i = 0 then 0 else w
  have hx : ∀ i j, dist (x i) (x j) ≤ Δ := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [x, hw, hΔ, dist_comm (0 : V) w ▸ hw]
  have hv : x 0 ∈ A.decSet (Pat (N3 : Set (Graph (Fin 2)))) T (A.initC x) :=
    hA.mem_decSet_of_deaf hΔ hQ (const_mem_pat (by simpa using m1)) (fun _ => deaf_H1) x
  have hw' : x 1 ∈ A.decSet (Pat (N3 : Set (Graph (Fin 2)))) T (A.initC x) :=
    hA.mem_decSet_of_deaf hΔ hQ (const_mem_pat (by simpa using m2)) (fun _ => deaf_H2) x
  have h := hA.dist_le_of_chains N3 ⟨_, m0⟩ hKN 2 ?_ hx hv hw'
  · simp only [x] at h
    norm_num [hw] at h
    exact h
  · intro k C hC G hG H hH
    have e1 := i01 k C hC; have e2 := i02 k C hC
    rw [inter_comm] at e1 e2
    simp only [N3, Finset.mem_insert, Finset.mem_singleton] at hG hH
    rcases hG with rfl | rfl | rfl <;> rcases hH with rfl | rfl | rfl
    all_goals first
      | exact chainLE_refl (by assumption)
      | exact chainLE_of_inter (by norm_num) (by assumption) (by assumption) (i01 k C hC)
      | exact chainLE_of_inter (by norm_num) (by assumption) (by assumption) (i02 k C hC)
      | exact chainLE_of_inter (by norm_num) (by assumption) (by assumption) e1
      | exact chainLE_of_inter (by norm_num) (by assumption) (by assumption) e2
      | exact chainLE_two le_rfl m1 m0 m2 e1 (i02 k C hC)
      | exact chainLE_two le_rfl m2 m0 m1 e2 (i01 k C hC)

/-- **Theorem 8 of FNS'18**, logarithmic form: decision time `T ≥ log₃(Δ/ε)`. -/
theorem theorem8_logb [Nontrivial V] (A : DAlg (Fin 2) σ V) {N : Set (Graph (Fin 2))}
    (hN : ({H0, H1, H2} : Set (Graph (Fin 2))) ⊆ N) {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε)
    {T : ℕ} (hA : A.DecidesBy N Δ ε T) : Real.logb 3 (Δ / ε) ≤ T :=
  (Real.logb_div_le_iff_le_pow_mul (by norm_num) hΔ hε).2
    (theorem8 A hN hΔ.le hA)

/-! ### Theorem 9: deaf graphs -/

variable {α : Type*}

/-- **Theorem 9 of FNS'18** (with three deaf graphs, as in the final remark on Theorem 2). If `N`
contains `F_i` for every agent `i` of a set `S` of at least three agents and an approximate
consensus algorithm (parameters `Δ`, `ε`) has decided at time `T` in all admissible executions,
then `Δ ≤ 2^T ε`. -/
theorem theorem9 [Nontrivial V] (A : DAlg α σ V) (G : Graph α) (S : Finset α)
    (hS : 3 ≤ S.card) {N : Set (Graph α)} (hN : ∀ i ∈ S, deafG G i ∈ N) {Δ ε : ℝ}
    (hΔ : 0 ≤ Δ) {T : ℕ} (hA : A.DecidesBy N Δ ε T) : Δ ≤ 2 ^ T * ε := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ : ∃ i ∈ S, ∃ j ∈ S, i ≠ j := by
    by_contra h; push Not at h
    have := Finset.card_le_one.2 h; omega
  set K := S.image (deafG G)
  have hKN : ∀ F ∈ K, F ∈ N := by
    intro F hF; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hF; exact hN a ha
  have hQ : Pat (K : Set (Graph α)) ⊆ Pat N := pat_mono fun F hF => hKN F hF
  have mK : ∀ a ∈ S, (fun _ => deafG G a) ∈ Pat (K : Set (Graph α)) := fun a ha =>
    const_mem_pat (Finset.mem_coe.2 (Finset.mem_image_of_mem (deafG G) ha))
  obtain ⟨w, hw⟩ := exists_dist_eq (V := V) hΔ
  set x : α → V := fun k => if k = i then 0 else w
  have hx : ∀ a b, dist (x a) (x b) ≤ Δ := by
    intro a b
    by_cases ha : a = i <;> by_cases hb : b = i <;>
      simp [x, ha, hb, hw, hΔ, dist_comm (0 : V) w ▸ hw]
  have hv : x i ∈ A.decSet (Pat (K : Set (Graph α))) T (A.initC x) :=
    hA.mem_decSet_of_deaf hΔ hQ (mK i hi) (fun _ => deaf_deafG G i) x
  have hw' : x j ∈ A.decSet (Pat (K : Set (Graph α))) T (A.initC x) :=
    hA.mem_decSet_of_deaf hΔ hQ (mK j hj) (fun _ => deaf_deafG G j) x
  have h := hA.dist_le_of_chains K ⟨_, Finset.mem_image_of_mem _ hi⟩ hKN 1 ?_ hx hv hw'
  · simp only [x, hij.symm, ite_true, ite_false] at h
    norm_num [hw] at h
    exact h
  · intro k C hC F hF F' hF'
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hF
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hF'
    have hab2 : ({a, b} : Finset α).card < S.card := by
      have := Finset.card_insert_le a {b}; simp only [Finset.card_singleton] at this; omega
    obtain ⟨l, hl, hlab⟩ := Finset.exists_mem_notMem_of_card_lt_card hab2
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hlab
    refine chainLE_of_inter le_rfl hF hF' ?_
    exact hA.decSet_inter_of_deaf hQ (mK l hl) (fun _ => deaf_deafG G l) (hC.next (hKN _ hF))
      (next_eq_of_agree (sameIn_deafG G hlab.1 hlab.2) fun _ _ => rfl)

/-- **Theorem 9 of FNS'18** for `deaf(G)`: `n ≥ 3` agents and all `F_i ∈ N`. -/
theorem theorem9_deaf [Nontrivial V] [Fintype α] (hn : 3 ≤ Fintype.card α) (A : DAlg α σ V)
    (G : Graph α) {N : Set (Graph α)} (hN : ∀ i, deafG G i ∈ N) {Δ ε : ℝ} (hΔ : 0 ≤ Δ) {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) : Δ ≤ 2 ^ T * ε :=
  theorem9 A G Finset.univ hn (fun i _ => hN i) hΔ hA

/-- **Theorem 9 of FNS'18**, logarithmic form: decision time `T ≥ log₂(Δ/ε)`. -/
theorem theorem9_logb [Nontrivial V] [Fintype α] (hn : 3 ≤ Fintype.card α) (A : DAlg α σ V)
    (G : Graph α) {N : Set (Graph α)} (hN : ∀ i, deafG G i ∈ N) {Δ ε : ℝ} (hΔ : 0 < Δ)
    (hε : 0 < ε) {T : ℕ} (hA : A.DecidesBy N Δ ε T) : Real.logb 2 (Δ / ε) ≤ T :=
  (Real.logb_div_le_iff_le_pow_mul (by norm_num) hΔ hε).2
    (theorem9_deaf hn A G hN hΔ.le hA)

/-- **Theorem 9, non-split corollary**: in the model of all non-split graphs with `n ≥ 3`
agents, `Δ ≤ 2^T ε`. -/
theorem theorem9_nonsplit [Nontrivial V] [Fintype α] (hn : 3 ≤ Fintype.card α)
    (A : DAlg α σ V) {Δ ε : ℝ} (hΔ : 0 ≤ Δ) {T : ℕ} (hA : A.DecidesBy {G | NonSplit G} Δ ε T) :
    Δ ≤ 2 ^ T * ε :=
  theorem9_deaf hn A (complete α) (fun i => nonSplit_deafG_complete i) hΔ hA

/-! ### Theorem 10: rooted models (`Ψ` blocks) -/

/-- Before agent `0`'s value has travelled around the `Ψ₀` cycle (`s ≤ n - 3` rounds), agents `1`,
`2` and all agents `m ≥ s + 3` cannot distinguish configurations that differ only at agent `0`. -/
theorem psi0_agree_aux {σ' : Type*} (step : StepFn (Fin n) σ') (hn : 4 ≤ n) {C C' : Fin n → σ'}
    (hC : ∀ m, m ≠ ag hn 0 → C m = C' m) :
    ∀ s, s ≤ n - 3 → ∀ m : Fin n, (m.val = 1 ∨ m.val = 2 ∨ s + 3 ≤ m.val) →
      conf step C (fun _ => Psi n 0) s m = conf step C' (fun _ => Psi n 0) s m := by
  intro s
  induction s with
  | zero =>
    intro _ m hm
    refine hC m fun h => ?_
    subst h; simp [ag] at hm
  | succ s ih =>
    intro hs m hm
    refine next_eq_of_agree (SameIn.refl _ _) fun j hj => ih (by omega) j ?_
    rcases hm with hm | hm | hm
    · rcases hears_psi_low (by omega) hj with rfl | hj'
      · exact Or.inl hm
      · right; right; omega
    · rcases hears_psi_low (by omega) hj with rfl | hj'
      · exact Or.inr (Or.inl hm)
      · right; right; omega
    · rcases hears_psi_high (by omega) hj with rfl | hj'
      · right; right; omega
      · right; right; omega

/-- **Theorem 10 of FNS'18.** For `n ≥ 4` agents and a network model containing `Ψ₁, Ψ₂, Ψ₃`, if
an approximate consensus algorithm (parameters `Δ`, `ε`) has decided at time `T` in all admissible
executions, then `Δ ≤ 2^⌊T/(n-2)⌋ ε`. -/
theorem theorem10 [Nontrivial V] {n : ℕ} (hn : 4 ≤ n) (A : DAlg (Fin n) σ V)
    {N : Set (Graph (Fin n))} (hN : ∀ u, Psi n u ∈ N) {Δ ε : ℝ} (hΔ : 0 ≤ Δ) {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) : Δ ≤ 2 ^ (T / (n - 2)) * ε := by
  set L := n - 2 with hLdef
  have hL : 0 < L := by omega
  set blk : Fin 3 → ℕ → Graph (Fin n) := fun u _ => Psi n u
  set Q := BlockPat ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)) blk L
  have hsub : Q ⊆ Pat N := blockPat_subset fun u _ _ => hN u
  have hconst : ∀ u, (fun _ => Psi n u) ∈ Q := fun u => ⟨fun _ => u, fun _ => by simp, rfl⟩
  set k := T / L
  set r := T % L
  have hT : r + L * k = T := by rw [add_comm]; exact Nat.div_add_mod T L
  have hr : r < L := Nat.mod_lt T hL
  obtain ⟨w, hw⟩ := exists_dist_eq (V := V) hΔ
  set x : Fin n → V := fun m => if m = ag hn 0 then 0 else w
  have hx : ∀ i j, dist (x i) (x j) ≤ Δ :=
    adm_two hΔ hw.le (v := 0) (w := w) fun m => by by_cases h : m = ag hn 0 <;> simp [x, h]
  set C₀ := conf A.step (A.initC x) (fun _ => Psi n 0) r
  have hC₀ : A.ReachLeft N Δ T (L * k) C₀ :=
    ⟨x, hx, _, const_mem_pat (hN 0), by omega, by rw [show T - L * k = r by omega]⟩
  have h := hA.ediam_decSet_blocks_le Finset.univ Finset.univ_nonempty blk hL
    (fun u _ _ => hN u) 1 ?_ k C₀ hC₀
  · -- agent `0` (deaf in `Ψ₀`) decides `0`
    have hv : (0 : V) ∈ A.decSet Q (L * k) C₀ := by
      refine ⟨_, hconst 0, ag hn 0, ?_⟩
      have := conf_add (step := A.step) (A.initC x) (fun _ => Psi n 0) r (L * k)
      rw [hT, show shift r (fun _ : ℕ => Psi n 0) = fun _ => Psi n 0 from rfl] at this
      show A.dec (conf A.step (conf A.step (A.initC x) (fun _ => Psi n 0) r) (fun _ => Psi n 0)
        (L * k) (ag hn 0)) = some 0
      rw [← this]
      refine hA.dec_of_closed hΔ (const_mem_pat (hN 0)) (S := {ag hn 0})
        (fun t i hi j hj => ?_) (fun i hi => ?_) rfl
      · rw [mem_singleton_iff] at hi ⊢; subst hi; exact (deaf_psi hn 0).eq hj
      · rw [mem_singleton_iff] at hi; simp [x, hi]
    -- agent `1` has not heard of agent `0` after `r < n - 2` rounds of `Ψ₀`, then is deaf
    have hw' : w ∈ A.decSet Q (L * k) C₀ := by
      refine ⟨_, hconst 1, ag hn 1, ?_⟩
      set P := splice (fun _ => Psi n 0) r (fun _ => Psi n 1)
      have hP : P ∈ Pat N := splice_mem_pat (const_mem_pat (hN 0)) (const_mem_pat (hN 1)) r
      have e1 := conf_splice (step := A.step) (A.initC x) (fun _ => Psi n 0) (fun _ => Psi n 1) r
        (L * k)
      have e2 := conf_splice (step := A.step) (A.initC fun _ => w) (fun _ => Psi n 0)
        (fun _ => Psi n 1) r (L * k)
      rw [hT] at e1 e2
      have hag : conf A.step (A.initC x) (fun _ => Psi n 0) r (ag hn 1) =
          conf A.step (A.initC fun _ => w) (fun _ => Psi n 0) r (ag hn 1) :=
        psi0_agree_aux A.step hn (fun m hm => by simp [Algorithm.initC, x, hm]) r (by omega) _
          (Or.inl (by simp [ag]))
      have hdec := hA.dec_of_closed hΔ hP (S := univ) (fun _ _ _ _ _ => mem_univ _)
        (x := fun _ => w) (u := w) (fun _ _ => rfl) (mem_univ (ag hn 1))
      rw [e2, ← conf_agree_deaf (fun _ => deaf_psi hn 1) (fun _ => deaf_psi hn 1) hag] at hdec
      exact hdec
    have h2 := (Metric.edist_le_ediam_of_mem hv hw').trans h
    have hε : 0 ≤ ε := by
      have : Nonempty (Fin n) := ⟨ag hn 0⟩
      exact hA.eps_nonneg hΔ ⟨_, hN 0⟩
    rw [pow_mul_ofReal] at h2
    have := dist_le_of_edist_le (by positivity) h2
    rw [hw] at this
    norm_num at this
    exact this
  · intro k' C hC a _ b _
    obtain ⟨ℓ, hla, hlb⟩ : ∃ ℓ : Fin 3, ℓ ≠ a ∧ ℓ ≠ b := by
      have : ∀ a b : Fin 3, ∃ ℓ : Fin 3, ℓ ≠ a ∧ ℓ ≠ b := by decide
      exact this a b
    refine chainLE_of_inter le_rfl (Finset.mem_univ _) (Finset.mem_univ _) ?_
    have hC' : A.ReachLeft N Δ T (L * k' + L) C := by rwa [← Nat.mul_succ]
    refine hA.decSet_inter_of_closed hsub (hconst ℓ) (S := {ag hn ℓ}) (singleton_nonempty _)
      (fun t i hi j hj => ?_) (hC'.run (const_mem_pat (hN a))) (fun i hi => ?_)
    · rw [mem_singleton_iff] at hi ⊢; subst hi; exact (deaf_psi hn ℓ).eq hj
    · rw [mem_singleton_iff] at hi; subst hi; exact psi_agree A.step hn C hla hlb

/-- **Theorem 10 of FNS'18**, logarithmic form: decision time `T ≥ (n-2) log₂(Δ/ε)`. -/
theorem theorem10_logb [Nontrivial V] {n : ℕ} (hn : 4 ≤ n) (A : DAlg (Fin n) σ V)
    {N : Set (Graph (Fin n))} (hN : ∀ u, Psi n u ∈ N) {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε)
    {T : ℕ} (hA : A.DecidesBy N Δ ε T) : ((n : ℝ) - 2) * Real.logb 2 (Δ / ε) ≤ T := by
  have h := (Real.logb_div_le_iff_le_pow_mul (by norm_num) hΔ hε).2
    (theorem10 hn A hN hΔ.le hA)
  have hcast : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hdiv : ((n - 2 : ℕ) : ℝ) * ((T / (n - 2) : ℕ) : ℝ) ≤ T := by
    exact_mod_cast Nat.mul_div_le T (n - 2)
  rw [← hcast]
  calc ((n - 2 : ℕ) : ℝ) * Real.logb 2 (Δ / ε) ≤ ((n - 2 : ℕ) : ℝ) * ((T / (n - 2) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)
    _ ≤ T := hdiv

/-- **Theorem 10**, rooted corollary: in the model of all rooted graphs on `n ≥ 4` agents,
`Δ ≤ 2^⌊T/(n-2)⌋ ε`. -/
theorem theorem10_rooted [Nontrivial V] {n : ℕ} (hn : 4 ≤ n) (A : DAlg (Fin n) σ V) {Δ ε : ℝ}
    (hΔ : 0 ≤ Δ) {T : ℕ} (hA : A.DecidesBy {G | ∃ r, Cslib.DynNet.IsRoot G r} Δ ε T) :
    Δ ≤ 2 ^ (T / (n - 2)) * ε :=
  theorem10 hn A (N := {G | ∃ r, Cslib.DynNet.IsRoot G r}) (fun u => ⟨_, psi_isRoot hn u⟩) hΔ
    hA

/-! ### Theorem 11: source-incompatible models with α-diameter `≤ D` -/

/-- **Theorem 11 of FNS'18** (with `n - 1` instead of the paper's `n`). For `n ≥ 2` agents and a
source-incompatible network model `N` of α-diameter at most `D`, if an approximate consensus
algorithm (parameters `Δ`, `ε`) has decided at time `T` in all admissible executions, then
`Δ ≤ (n - 1) (D + 1)^T ε`. If some graph of `N` is not rooted, even `Δ ≤ ε` holds
(`DecidesBy.le_of_not_rooted`). -/
theorem theorem11 [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) (A : DAlg (Fin n) σ V)
    {N : Set (Graph (Fin n))} (hSI : SourceIncompatible N) {D : ℕ}
    (hD : AlphaDiamLE AlphaRel N D) {Δ ε : ℝ} (hΔ : 0 ≤ Δ) {T : ℕ} (hA : A.DecidesBy N Δ ε T) :
    Δ ≤ ((n : ℝ) - 1) * ((D : ℝ) + 1) ^ T * ε := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hN : N.Nonempty := by obtain ⟨G, hG, -⟩ := hSI ⟨0, by omega⟩; exact ⟨G, hG⟩
  have hε : 0 ≤ ε := hA.eps_nonneg hΔ hN
  have hn1 : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hD1 : (1 : ℝ) ≤ ((D : ℝ) + 1) ^ T := one_le_pow₀ (by linarith [D.cast_nonneg (α := ℝ)])
  by_cases hroot : ∀ G ∈ N, (Roots G).Nonempty
  swap
  · simp only [not_forall] at hroot
    obtain ⟨G, hG, hne⟩ := hroot
    have h := hA.le_of_not_rooted hΔ hG fun r hr => hne ⟨r, hr⟩
    have : 1 * 1 ≤ ((n : ℝ) - 1) * ((D : ℝ) + 1) ^ T := mul_le_mul hn1 hD1 zero_le_one (by linarith)
    nlinarith
  have hfin : N.Finite := Set.toFinite N
  have hK : ((hfin.toFinset : Finset (Graph (Fin n))) : Set (Graph (Fin n))) = N := by simp
  -- the engine: decision sets of configurations with `k` rounds left
  have hE : ∀ k C, A.ReachLeft N Δ T k C →
      Metric.ediam (A.decSet (Pat N) k C) ≤ ENNReal.ofReal (((D : ℝ) + 1) ^ k * ε) := by
    intro k C hC
    rw [← pow_mul_ofReal, ← hK]
    refine hA.ediam_decSet_le hfin.toFinset (by simpa using hN) (fun G hG => by simpa using hG)
      D ?_ k C hC
    intro k C hC G hG H hH
    rw [hK]
    obtain ⟨q, hq, c, hc0, hcq, hc⟩ := hD G (by simpa using hG) H (by simpa using hH)
    refine ⟨q, hq, c, hc0, hcq, fun r hr => ?_, fun r hr => ?_⟩
    · rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simpa [hc0] using hG
      · have := (hc (r - 1) (by omega)).2.1
        rw [Nat.sub_add_cancel hr0] at this
        simpa using this
    · -- Lemma 20: the roots of `K` are closed and have the same in-neighbours in both graphs
      obtain ⟨h1, -, K, hK', hrel⟩ := hc r hr
      exact hA.decSet_inter_of_closed subset_rfl (const_mem_pat hK') (hroot K hK')
        (fun _ i hi j hj => roots_closed hi hj) (hC.next h1)
        (fun i hi => next_eq_of_agree (hrel i hi) fun _ _ => rfl)
  -- Lemma 21: the staircase of initial configurations
  obtain ⟨w, hw⟩ := exists_dist_eq (V := V) hΔ
  let xs : ℕ → Fin n → V := fun k i => if i.val < k then w else 0
  have hxs : ∀ k, ∀ i j, dist (xs k i) (xs k j) ≤ Δ := fun k =>
    adm_two hΔ hw.le (v := 0) (w := w) fun i => by by_cases h : i.val < k <;> simp [xs, h]
  let Y : ℕ → Set V := fun k => A.decSet (Pat N) T (A.initC (xs k))
  have hint : ∀ k < n, (Y k ∩ Y (k + 1)).Nonempty := by
    intro k hk
    obtain ⟨G, hG, hkG⟩ := hSI ⟨k, hk⟩
    refine hA.decSet_inter_of_closed subset_rfl (const_mem_pat hG) (hroot G hG)
      (fun _ i hi j hj => roots_closed hi hj) (reachLeft_initC hN (hxs k)) fun i hi => ?_
    have hik : i.val ≠ k := by
      rintro h; apply hkG
      have : i = ⟨k, hk⟩ := Fin.ext h
      rw [← this]; exact hi
    simp only [Algorithm.initC, xs]
    congr 1
    by_cases h : i.val < k
    · simp [h, show i.val < k + 1 by omega]
    · simp [h, show ¬ i.val < k + 1 by omega]
  have hY0 : Y 0 ⊆ {0} := by
    intro z hz
    have := hA.mem_hull_of_mem_decSet subset_rfl (hxs 0) hz
    have hx : xs 0 = fun _ => 0 := by funext i; simp [xs]
    rwa [hx, range_const, convexHull_singleton] at this
  have hYn : Y n ⊆ {w} := by
    intro z hz
    have := hA.mem_hull_of_mem_decSet subset_rfl (hxs n) hz
    have hx : xs n = fun _ => w := by funext i; simp [xs, i.isLt]
    rwa [hx, range_const, convexHull_singleton] at this
  obtain ⟨z0, hz0, hz0'⟩ := hint 0 (by omega)
  obtain ⟨zl, hzl, hzl'⟩ := hint (n - 1) (by omega)
  have hz0e : z0 = 0 := hY0 hz0
  have hzle : zl = w := hYn (by rwa [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hzl')
  have hchain := edist_le_sum_chain (fun r => Y (r + 1)) (n - 2)
    (fun r hr => hint (r + 1) (by omega)) z0 hz0' zl (by rwa [show n - 2 + 1 = n - 1 by omega])
  rw [hz0e, hzle] at hchain
  have hsum : ∑ r ∈ Finset.range (n - 2 + 1), Metric.ediam (Y (r + 1)) ≤
      ENNReal.ofReal (((n : ℝ) - 1) * ((D : ℝ) + 1) ^ T * ε) := by
    calc ∑ r ∈ Finset.range (n - 2 + 1), Metric.ediam (Y (r + 1))
        ≤ ∑ _r ∈ Finset.range (n - 2 + 1), ENNReal.ofReal (((D : ℝ) + 1) ^ T * ε) :=
          Finset.sum_le_sum fun r _ => hE T _ (reachLeft_initC hN (hxs _))
      _ = ENNReal.ofReal (((n : ℝ) - 1) * ((D : ℝ) + 1) ^ T * ε) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc,
            ENNReal.ofReal_mul (by linarith), show n - 2 + 1 = n - 1 by omega,
            ← ENNReal.ofReal_natCast, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one,
            ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_mul (by positivity)]
  have := dist_le_of_edist_le (by positivity) (hchain.trans hsum)
  rwa [hw] at this

/-- **Theorem 11 of FNS'18**, logarithmic form: decision time `T ≥ log_{D+1}(Δ/((n-1)ε))`. -/
theorem theorem11_logb [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) (A : DAlg (Fin n) σ V)
    {N : Set (Graph (Fin n))} (hSI : SourceIncompatible N) {D : ℕ} (hD1 : 1 ≤ D)
    (hD : AlphaDiamLE AlphaRel N D) {Δ ε : ℝ} (hΔ : 0 < Δ) (hε : 0 < ε) {T : ℕ}
    (hA : A.DecidesBy N Δ ε T) : Real.logb ((D : ℝ) + 1) (Δ / (((n : ℝ) - 1) * ε)) ≤ T := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hD1' : (1 : ℝ) ≤ D := by exact_mod_cast hD1
  refine (Real.logb_div_le_iff_le_pow_mul (by linarith) hΔ (mul_pos hn1 hε)).2 ?_
  have := theorem11 hn A hSI hD hΔ.le hA
  linarith

end AsymptoticConsensus
