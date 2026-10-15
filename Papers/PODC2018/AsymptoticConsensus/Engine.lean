import Papers.PODC2018.AsymptoticConsensus.Valency

/-!
# The lower-bound engine: greedy executions with slowly shrinking valency

The proofs of Theorems 1, 2, 3 and 5 of FNS'18 share one argument: from the current
configuration, the valency is covered by the valencies of the (finitely many) successors, any two
successors are connected by a short chain of successors with intersecting valencies (Lemma 7 /
Lemma 12 / Lemma 20), hence some successor keeps a `1/(D+1)` fraction of the valency diameter.

We formalize it once, for *block moves*: a move `m ∈ K` applies the finite sequence of graphs
`blk m 0, …, blk m (L-1)`. Network models are the case `L = 1` (Theorems 1, 2, 5); the
`Ψ`-sequences of Theorem 3 use `L = n - 2`. Valencies are taken w.r.t. the set
`BlockPat K blk L` of patterns that are concatenations of blocks (the paper's "properties",
Section 6.1), which is shift-invariant at block boundaries, so no snapshots are needed.

Main results: `exists_block_run` (the greedy execution) and `le_rate_of_blocks`
(`(D+1)^{-1/L} ≤` contraction rate).
-/

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set
open scoped ENNReal

variable {α σ V ι : Type*}

/-- The pattern made of the blocks `blk (c 0), blk (c 1), …`, each of length `L`. -/
def blockSeq (blk : ι → ℕ → Graph α) (L : ℕ) (c : ℕ → ι) : ℕ → Graph α :=
  fun t => blk (c (t / L)) (t % L)

/-- Concatenations of blocks from `K` (a "property" in the sense of Section 6.1). -/
def BlockPat (K : Set ι) (blk : ι → ℕ → Graph α) (L : ℕ) : Set (ℕ → Graph α) :=
  {q | ∃ c : ℕ → ι, (∀ k, c k ∈ K) ∧ q = blockSeq blk L c}

theorem blockSeq_mem {K : Set ι} {blk : ι → ℕ → Graph α} {L : ℕ} {c : ℕ → ι}
    (hc : ∀ k, c k ∈ K) : blockSeq blk L c ∈ BlockPat K blk L := ⟨c, hc, rfl⟩

theorem blockPat_subset {K : Set ι} {blk : ι → ℕ → Graph α} {L : ℕ} {N : Set (Graph α)}
    (hblk : ∀ m ∈ K, ∀ t, blk m t ∈ N) : BlockPat K blk L ⊆ Pat N := by
  rintro _ ⟨c, hc, rfl⟩ t
  exact hblk _ (hc _) _

/-- For `L = 1`, block patterns over single graphs are exactly the patterns of the model. -/
theorem blockPat_one (K : Set (Graph α)) : BlockPat K (fun G _ => G) 1 = Pat K := by
  ext q
  constructor
  · rintro ⟨c, hc, rfl⟩ t; simpa [blockSeq] using hc t
  · intro hq; exact ⟨q, hq, by funext t; simp [blockSeq]⟩

variable {step : StepFn α σ}

theorem shift_blockSeq (blk : ι → ℕ → Graph α) {L : ℕ} (hL : 0 < L) (c : ℕ → ι) (k : ℕ) :
    shift (L * k) (blockSeq blk L c) = blockSeq blk L (fun j => c (k + j)) := by
  funext t
  simp only [shift, blockSeq]
  rw [Nat.mul_add_div hL, Nat.mul_add_mod]

theorem conf_blockSeq_block (C : α → σ) (blk : ι → ℕ → Graph α) {L : ℕ} (hL : 0 < L)
    (c : ℕ → ι) : conf step C (blockSeq blk L c) L = conf step C (blk (c 0)) L := by
  refine conf_congr C fun k hk => ?_
  simp [blockSeq, Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]

namespace Alg

variable [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Alg α σ V}

/-- **Lemma 4 / Lemma 10 for block patterns.** -/
theorem val_blockPat_subset {K : Set ι} {blk : ι → ℕ → Graph α} {L : ℕ} (hL : 0 < L)
    (C : α → σ) : A.val (BlockPat K blk L) C ⊆
      ⋃ m ∈ K, A.val (BlockPat K blk L) (conf A.step C (blk m) L) := by
  rintro z ⟨_, ⟨c, hc, rfl⟩, hz⟩
  refine mem_biUnion (hc 0) ⟨_, blockSeq_mem (fun k => hc (0 + 1 + k)) (L := L) (blk := blk), ?_⟩
  rw [← hasLimit_shift (p := blockSeq blk L c) L] at hz
  have h1 := shift_blockSeq blk hL c 1
  rw [mul_one] at h1
  rw [h1, conf_blockSeq_block C blk hL c] at hz
  simpa [add_comm] using hz

theorem val_blockPat_block_subset {K : Set ι} {blk : ι → ℕ → Graph α} {L : ℕ} (hL : 0 < L)
    {m : ι} (hm : m ∈ K) (C : α → σ) :
    A.val (BlockPat K blk L) (conf A.step C (blk m) L) ⊆ A.val (BlockPat K blk L) C := by
  rintro z ⟨_, ⟨c, hc, rfl⟩, hz⟩
  let c' : ℕ → ι := fun k => Nat.casesOn k m c
  refine ⟨blockSeq blk L c', blockSeq_mem (fun k => by cases k <;> simp [c', hm, hc]), ?_⟩
  rw [← hasLimit_shift (p := blockSeq blk L c') L]
  have h1 := shift_blockSeq blk hL c' 1
  rw [mul_one] at h1
  have hc' : (fun j => c' (1 + j)) = c := by funext j; rw [add_comm]
  rw [h1, conf_blockSeq_block C blk hL c', hc']
  exact hz

/-- **The greedy execution.** Under the chain hypothesis there is a sequence of blocks such that
after `k` blocks the (block-pattern) valency diameter has lost at most a factor `(D+1)^k`. -/
theorem exists_block_run {N : Set (Graph α)} (K : Finset ι) (hK : K.Nonempty)
    (blk : ι → ℕ → Graph α) {L : ℕ} (hL : 0 < L) (hblk : ∀ m ∈ K, ∀ t, blk m t ∈ N) (D : ℕ)
    (hchain : ∀ C, A.Reach N C → ∀ a ∈ K, ∀ b ∈ K,
      ChainLE K (fun m => A.val (BlockPat (K : Set ι) blk L) (conf A.step C (blk m) L)) D a b)
    (C₀ : α → σ) (h₀ : A.Reach N C₀) :
    ∃ c : ℕ → ι, (∀ k, c k ∈ K) ∧ ∀ k,
      Metric.ediam (A.val (BlockPat (K : Set ι) blk L) C₀) ≤ ((D : ℝ≥0∞) + 1) ^ k *
        Metric.ediam (A.val (BlockPat (K : Set ι) blk L)
          (conf A.step C₀ (blockSeq blk L c) (L * k))) := by
  obtain ⟨s, Cs, h0, hs, hsucc, hinv⟩ := exists_seq_of_step
    (fun m C => conf A.step C (blk m) L) (K : Set ι) (A.Reach N)
    (fun C => Metric.ediam (A.val (BlockPat (K : Set ι) blk L) C)) ((D : ℝ≥0∞) + 1)
    (fun C hC => by
      obtain ⟨m, hm, hle⟩ := exists_ediam_le_mul K hK
        (fun m => A.val (BlockPat (K : Set ι) blk L) (conf A.step C (blk m) L)) _
        (by simpa using val_blockPat_subset (K := (K : Set ι)) (A := A) hL C) D (hchain C hC)
      exact ⟨m, hm, hC.conf (hblk m hm) L, hle⟩) C₀ h₀
  refine ⟨s, hs, fun k => ?_⟩
  have hCs : ∀ k, Cs k = conf A.step C₀ (blockSeq blk L s) (L * k) := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [hsucc, ih, Nat.mul_succ, conf_add, shift_blockSeq blk hL s k,
        conf_blockSeq_block _ blk hL]
      simp
  rw [← hCs]
  exact (hinv k).2

/-- Converting a block-wise bound into a contraction-rate bound. -/
theorem le_rate_of_blockBound {N : Set (Graph α)} (x : α → V) {p : ℕ → Graph α}
    (hp : p ∈ Pat N) {L : ℕ} (hL : 0 < L) {a R : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ∞) (hR : 1 ≤ R)
    (hR' : R ≠ ∞)
    (h : ∀ k, a ≤ R ^ k * A.δ N (conf A.step (A.initC x) p (L * k))) :
    (R ^ ((L : ℝ)⁻¹))⁻¹ ≤ A.rate N := by
  set ρ : ℝ≥0∞ := R ^ ((L : ℝ)⁻¹)
  have hρL : ρ ^ L = R := ENNReal.rpow_inv_natCast_pow (by omega) R
  have hρ1 : 1 ≤ ρ := ENNReal.one_le_rpow hR (by positivity)
  have hρ : ρ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hR'
  have hR0 : R ≠ 0 := (lt_of_lt_of_le zero_lt_one hR).ne'
  refine le_rate x hp (a := a * R⁻¹) (by simp [ha, hR']) (ENNReal.mul_ne_top ha' (ENNReal.inv_ne_top.2 hR0)) fun t => ?_
  -- `k = ⌈t / L⌉`
  obtain ⟨k, hk, hk'⟩ : ∃ k, t ≤ L * k ∧ L * k ≤ t + L := by
    have h1 := Nat.div_add_mod (t + L - 1) L
    have h2 := Nat.mod_lt (t + L - 1) hL
    exact ⟨(t + L - 1) / L, by omega, by omega⟩
  have hδ : A.δ N (conf A.step (A.initC x) p (L * k)) ≤ A.δ N (conf A.step (A.initC x) p t) :=
    δ_conf_antitone hp _ hk
  have hRk : R ^ k ≤ R * ρ ^ t := by
    calc R ^ k = ρ ^ (L * k) := by rw [pow_mul, hρL]
      _ ≤ ρ ^ (t + L) := pow_le_pow_right₀ hρ1 hk'
      _ = R * ρ ^ t := by rw [pow_add, hρL, mul_comm]
  have h1 : a ≤ A.δ N (conf A.step (A.initC x) p t) * (R * ρ ^ t) :=
    calc a ≤ R ^ k * A.δ N (conf A.step (A.initC x) p (L * k)) := h k
      _ ≤ (R * ρ ^ t) * A.δ N (conf A.step (A.initC x) p t) := by gcongr
      _ = _ := mul_comm _ _
  have h2 := ENNReal.div_le_of_le_mul h1
  rwa [div_eq_mul_inv, ENNReal.mul_inv (Or.inr (ENNReal.pow_ne_top hρ)) (Or.inl hR'), ← mul_assoc,
    ENNReal.inv_pow] at h2

/-- **Lower-bound engine.** If the chain hypothesis holds for block moves with chains of length at
most `D`, then the contraction rate in `N` is at least `(D+1)^{-1/L}`, provided some initial
configuration has a positive block-valency diameter. -/
theorem le_rate_of_blocks [Nonempty α] [Finite α] {N : Set (Graph α)} (hA : A.Solves N)
    (K : Finset ι) (hK : K.Nonempty) (blk : ι → ℕ → Graph α) {L : ℕ} (hL : 0 < L)
    (hblk : ∀ m ∈ K, ∀ t, blk m t ∈ N) (D : ℕ)
    (hchain : ∀ C, A.Reach N C → ∀ a ∈ K, ∀ b ∈ K,
      ChainLE K (fun m => A.val (BlockPat (K : Set ι) blk L) (conf A.step C (blk m) L)) D a b)
    (x : α → V) (hx : Metric.ediam (A.val (BlockPat (K : Set ι) blk L) (A.initC x)) ≠ 0) :
    ((((D : ℝ≥0∞) + 1)) ^ ((L : ℝ)⁻¹))⁻¹ ≤ A.rate N := by
  have hN : N.Nonempty := by
    obtain ⟨m, hm⟩ := hK; exact ⟨_, hblk m hm 0⟩
  have hsub : BlockPat (K : Set ι) blk L ⊆ Pat N := blockPat_subset hblk
  obtain ⟨c, hc, hrun⟩ := exists_block_run K hK blk hL hblk D hchain _ (Reach.initC hN x)
  have hfin : Metric.ediam (A.val (BlockPat (K : Set ι) blk L) (A.initC x)) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (Metric.ediam_mono ((val_mono hsub _).trans
      (hA.val_initC_subset_hull hN x)))
    rw [convexHull_ediam]
    exact (Set.finite_range x).isBounded.ediam_ne_top
  refine le_rate_of_blockBound x (blockPat_subset hblk (blockSeq_mem (blk := blk) (L := L) hc)) hL hx hfin
    (by simp) (by simp) fun k => (hrun k).trans ?_
  gcongr
  exact Metric.ediam_mono (val_mono hsub _)

end Alg

end AsymptoticConsensus

namespace AsymptoticConsensus.Alg

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set
open scoped ENNReal

variable {α σ V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {A : Alg α σ V}

/-- **Lower-bound engine for network models** (block length `1`): if from every reachable
configuration any two graphs of the finite submodel `K ⊆ N` are joined by a chain of at most `D`
graphs of `K` whose successor valencies (in `K`) intersect consecutively, and some initial
configuration has a positive `K`-valency diameter, then the contraction rate in `N` is at least
`1/(D+1)`. -/
theorem le_rate_of_chains [Nonempty α] [Finite α] {N : Set (Graph α)} (hA : A.Solves N)
    (K : Finset (Graph α)) (hK : K.Nonempty) (hKN : ∀ G ∈ K, G ∈ N) (D : ℕ)
    (hchain : ∀ C, A.Reach N C → ∀ G ∈ K, ∀ H ∈ K,
      ChainLE K (fun G => A.val (Pat (K : Set (Graph α))) (next A.step G C)) D G H)
    (x : α → V) (hx : Metric.ediam (A.val (Pat (K : Set (Graph α))) (A.initC x)) ≠ 0) :
    ((D : ℝ≥0∞) + 1)⁻¹ ≤ A.rate N := by
  have := le_rate_of_blocks hA K hK (fun G _ => G) one_pos (fun G hG _ => hKN G hG) D
    (fun C hC a ha b hb => by rw [blockPat_one]; exact hchain C hC a ha b hb) x (by simpa [blockPat_one] using hx)
  simpa using this

end AsymptoticConsensus.Alg
