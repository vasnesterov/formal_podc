import Papers.PODC2017.DeltaEdgeColoring.Basic

/-!
# CD-Coloring (Algorithm 1): Theorems 2.4, 2.5, 2.6 and 3.2

Algorithm 1 (`CD-Coloring(G, D, S, t, x)`) recursively computes a connector, colours it with
`D(t-1)+1` colours (black box [17]), and recurses on the colour classes in parallel; after `x`
levels it colours the remaining classes directly with `D(⌈S/t^x⌉-1)+1` colours and returns the
tuple of all colours.

We unfold the recursion level by level: `stages … j` is the state after `j` recursion levels
(the union of all current subgraphs, their clique cover, the clique-size bound, and the index of
the current subgraph of every vertex, i.e. the tuple of connector colours so far, encoded in mixed
radix). Running all recursive calls "in parallel" on the colour classes is the same as one call on
the disjoint union `sameColor G φ` of the classes. The final colour of `v` is the pair
`⟨index, ψ v⟩`, encoded as `index · B + ψ v`.

The parameter `t` may depend on the recursion level and on the current clique size (`τ j S`);
Algorithm 1 uses a constant `t` (`cdColoring`), the algorithms `𝒜_x` of the proof of
Theorem 3.2 use `t = ⌊S^{1/(x+1)}⌋` at every level (`algA`).

## Main results

* `theorem_2_4`: after `x` levels with parameter `t`, the subgraph indices form a
  `((D(t-1)+1)^x, ⌈S/t^x⌉)`-clique-decomposition (in the paper's form `((tD)^x, S/t^x + 2)`).
* `theorem_2_5`: the resulting colouring is proper.
* `theorem_2_6`: it uses fewer than `(D(t-1)+1)^x · (D(⌈S/t^x⌉-1)+1) ≤ (tD)^x (S/t^x + 2) D`
  colours.
* `theorem_3_2`: for `D ≥ 2` and parameters `t` with `t² ≤ S` (in particular the paper's
  `t = ⌊S^{1/(x+1)}⌋`, `algA`), the colouring uses fewer than `D^{x+1} S` colours, without any
  colour reduction.
* `paper_inductive_step_fails`: the inequality used in the paper's inductive step for `𝒜_2`
  (`(D(t-1)+1) · D^{i+1} ⌈S/t⌉ ≤ D^{i+2} S`) is false for `D = 2`, `S = 31`, `t = ⌊√31⌋ = 5`.
-/

open Finset

namespace Podc.DeltaEdgeColoring

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

/-! ### Arithmetic helpers -/

lemma ceilDiv_ceilDiv (a : ℕ) {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    a ⌈/⌉ b ⌈/⌉ c = a ⌈/⌉ (b * c) := by
  refine le_antisymm ?_ ?_
  · rw [ceilDiv_le_iff_le_mul hc, ceilDiv_le_iff_le_mul hb, ← mul_assoc]
    exact le_smul_ceilDiv (Nat.mul_pos hb hc)
  · rw [ceilDiv_le_iff_le_mul (Nat.mul_pos hb hc), mul_assoc]
    calc a ≤ b * (a ⌈/⌉ b) := le_smul_ceilDiv hb
      _ ≤ b * (c * (a ⌈/⌉ b ⌈/⌉ c)) := Nat.mul_le_mul_left _ (le_smul_ceilDiv hc)

lemma one_le_ceilDiv {a b : ℕ} (ha : 1 ≤ a) (hb : 0 < b) : 1 ≤ a ⌈/⌉ b := by
  by_contra h
  have h0 : a ⌈/⌉ b = 0 := by omega
  have := (ceilDiv_le_iff_le_mul hb).1 h0.le
  omega

/-- Mixed-radix pairs: `a · B + b` with `b < B` determines `a` and `b`. -/
lemma mixed_eq_iff {a a' b b' B : ℕ} (hb : b < B) (hb' : b' < B) :
    a * B + b = a' * B + b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have hB : 0 < B := by omega
    have h1 : (a * B + b) / B = (a' * B + b') / B := by rw [h]
    rw [Nat.mul_comm a, Nat.mul_comm a', Nat.mul_add_div hB, Nat.mul_add_div hB,
      Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hb'] at h1
    simp only [add_zero] at h1
    subst h1
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma mixed_lt {a b A B : ℕ} (ha : a < A) (hb : b < B) : a * B + b < A * B := by
  have : (a + 1) * B ≤ A * B := Nat.mul_le_mul_right _ ha
  nlinarith

/-! ### The recursion, level by level -/

/-- The state after some recursion levels: the union `G` of the current subgraphs, its clique
cover `𝒬`, the clique-size bound `S`, the index `idx v` of the current subgraph of `v`, and the
number `pal` of possible indices. -/
structure Stage (V : Type*) where
  /-- The disjoint union of the current subgraphs `G_i`. -/
  G : SimpleGraph V
  /-- The identified cliques of the current subgraphs. -/
  𝒬 : Finset (Finset V)
  /-- The current bound on the clique size. -/
  S : ℕ
  /-- The index of the current subgraph containing `v` (connector colours so far). -/
  idx : V → ℕ
  /-- The number of possible indices. -/
  pal : ℕ

/-- One recursion level of Algorithm 1 with parameter `t` (lines 1–4 and 7): build the connector,
colour it with `D(t-1)+1` colours using the black box `col`, and pass to the colour classes. -/
def Stage.next (col : SimpleGraph V → ℕ → V → ℕ) (D t : ℕ) (st : Stage V) : Stage V :=
  let φ := col (connector t st.𝒬) (D * (t - 1))
  { G := sameColor st.G φ
    𝒬 := refine st.𝒬 φ
    S := st.S ⌈/⌉ t
    idx := fun v => st.idx v * (D * (t - 1) + 1) + φ v
    pal := st.pal * (D * (t - 1) + 1) }

/-- The state after `j` recursion levels; level `j` uses the parameter `τ j S_j`. -/
def stages (col : SimpleGraph V → ℕ → V → ℕ) (D : ℕ) (τ : ℕ → ℕ → ℕ) (G : SimpleGraph V)
    (𝒬 : Finset (Finset V)) (S : ℕ) : ℕ → Stage V
  | 0 => ⟨G, 𝒬, S, fun _ => 0, 1⟩
  | j + 1 => (stages col D τ G 𝒬 S j).next col D (τ j (stages col D τ G 𝒬 S j).S)

/-- The colouring computed after `x` recursion levels with parameter schedule `τ`: the subgraph
index paired with the final direct colouring (line 12) with `D(S_x - 1)+1` colours. -/
def cdColoringSched (col : SimpleGraph V → ℕ → V → ℕ) (D : ℕ) (τ : ℕ → ℕ → ℕ)
    (G : SimpleGraph V) (𝒬 : Finset (Finset V)) (S x : ℕ) (v : V) : ℕ :=
  let st := stages col D τ G 𝒬 S x
  st.idx v * (D * (st.S - 1) + 1) + col st.G (D * (st.S - 1)) v

/-- **Algorithm 1**, `CD-Coloring(G, D, S, t, x)` with the clique identification `𝒬`. -/
abbrev cdColoring (col : SimpleGraph V → ℕ → V → ℕ) (D t : ℕ) (G : SimpleGraph V)
    (𝒬 : Finset (Finset V)) (S x : ℕ) : V → ℕ :=
  cdColoringSched col D (fun _ _ => t) G 𝒬 S x

section Invariants

variable {col : SimpleGraph V → ℕ → V → ℕ} {D : ℕ} {τ : ℕ → ℕ → ℕ} {G : SimpleGraph V}
  {𝒬 : Finset (Finset V)} {S : ℕ}

/-- The invariant of the recursion. -/
structure StageInv (G : SimpleGraph V) (𝒬₀ : Finset (Finset V)) (D : ℕ) (st : Stage V) :
    Prop where
  cover : IsCliqueCover st.G st.𝒬 D st.S
  idx_lt : ∀ v, st.idx v < st.pal
  adj_iff : ∀ u v, st.G.Adj u v ↔ G.Adj u v ∧ st.idx u = st.idx v
  coversCliques : CoversCliques G 𝒬₀ → CoversCliques st.G st.𝒬

lemma stageInv_next (hcol : IsDeltaColorer col) {t : ℕ} (ht : 0 < t) {st : Stage V}
    (h : StageInv G 𝒬 D st) : StageInv G 𝒬 D (st.next col D t) := by
  set φ := col (connector t st.𝒬) (D * (t - 1)) with hφdef
  obtain ⟨hprop, hle⟩ := hcol (connector t st.𝒬) (D * (t - 1)) (connector_degree_le ht h.cover)
  have hφlt : ∀ v, φ v < D * (t - 1) + 1 := fun v => Nat.lt_succ_of_le (hle v)
  refine ⟨isCliqueCover_refine ht h.cover hprop, fun v => mixed_lt (h.idx_lt v) (hφlt v),
    fun u v => ?_, fun hc => (h.coversCliques hc).refine φ⟩
  change (sameColor st.G φ).Adj u v ↔ G.Adj u v ∧
    st.idx u * (D * (t - 1) + 1) + φ u = st.idx v * (D * (t - 1) + 1) + φ v
  rw [sameColor_adj, h.adj_iff, mixed_eq_iff (hφlt u) (hφlt v), and_assoc]

lemma stageInv_stages (hcol : IsDeltaColorer col) (hτ : ∀ j s, 0 < τ j s)
    (hc : IsCliqueCover G 𝒬 D S) (j : ℕ) : StageInv G 𝒬 D (stages col D τ G 𝒬 S j) := by
  induction j with
  | zero => exact ⟨hc, fun _ => Nat.one_pos, fun u v => by simp [stages], fun h => h⟩
  | succ j ih => exact stageInv_next hcol (hτ _ _) ih

/-- The colouring after any schedule is proper and uses fewer than `pal_x · (D(S_x-1)+1)`
colours. -/
lemma cdColoringSched_spec (hcol : IsDeltaColorer col) (hτ : ∀ j s, 0 < τ j s)
    (hc : IsCliqueCover G 𝒬 D S) (x : ℕ) :
    (∀ ⦃u v⦄, G.Adj u v → cdColoringSched col D τ G 𝒬 S x u ≠ cdColoringSched col D τ G 𝒬 S x v)
    ∧ ∀ v, cdColoringSched col D τ G 𝒬 S x v <
      (stages col D τ G 𝒬 S x).pal * (D * ((stages col D τ G 𝒬 S x).S - 1) + 1) := by
  set st := stages col D τ G 𝒬 S x
  have hinv := stageInv_stages hcol hτ hc x
  obtain ⟨hprop, hle⟩ := hcol st.G (D * (st.S - 1))
    (ncard_neighborSet_le_of_isCliqueCover hinv.cover)
  have hψ : ∀ v, col st.G (D * (st.S - 1)) v < D * (st.S - 1) + 1 :=
    fun v => Nat.lt_succ_of_le (hle v)
  refine ⟨fun u v huv heq => ?_, fun v => mixed_lt (hinv.idx_lt v) (hψ v)⟩
  rcases (mixed_eq_iff (hψ u) (hψ v)).1 heq with ⟨hidx, hcolr⟩
  exact hprop ((hinv.adj_iff u v).2 ⟨huv, hidx⟩) hcolr

end Invariants

/-! ### Algorithm 1 with a constant parameter `t` -/

section Constant

variable {col : SimpleGraph V → ℕ → V → ℕ} {D t : ℕ} {G : SimpleGraph V}
  {𝒬 : Finset (Finset V)} {S : ℕ}

lemma stages_const_S_pal (ht : 0 < t) (x : ℕ) :
    (stages col D (fun _ _ => t) G 𝒬 S x).S = S ⌈/⌉ t ^ x ∧
    (stages col D (fun _ _ => t) G 𝒬 S x).pal = (D * (t - 1) + 1) ^ x := by
  induction x with
  | zero => simp [stages]
  | succ x ih =>
    simp only [stages, Stage.next, ih.1, ih.2, pow_succ]
    exact ⟨ceilDiv_ceilDiv S (pow_pos ht x) ht, trivial⟩

/-- **Theorem 2.4** (clique decomposition). After `x` recursion levels with parameter `t > 0`,
the index `idx v` of the current subgraph partitions `V` into the sets `U_i = idx⁻¹(i)`,
`i < (D(t-1)+1)^x ≤ (tD)^x`; the current graph is exactly the union of the induced subgraphs
`G[U_i]`; it has a clique cover of diversity `≤ D` and clique size `≤ ⌈S/t^x⌉ ≤ S/t^x + 1` (the paper
states `S/t^x + 2`); and if
`𝒬` contains all cliques (e.g. `𝒬` = all maximal cliques), then every clique of every `G[U_i]` has at
most `⌈S/t^x⌉` vertices. -/
theorem theorem_2_4 (hcol : IsDeltaColorer col) (ht : 0 < t) (hD : 1 ≤ D)
    (hc : IsCliqueCover G 𝒬 D S) (x : ℕ) :
    let st := stages col D (fun _ _ => t) G 𝒬 S x
    (∀ v, st.idx v < (D * (t - 1) + 1) ^ x) ∧ (D * (t - 1) + 1) ^ x ≤ (t * D) ^ x ∧
    (∀ u v, st.G.Adj u v ↔ G.Adj u v ∧ st.idx u = st.idx v) ∧
    IsCliqueCover st.G st.𝒬 D (S ⌈/⌉ t ^ x) ∧
    ((S ⌈/⌉ t ^ x : ℕ) : ℝ) ≤ S / t ^ x + 1 ∧
    (CoversCliques G 𝒬 → ∀ K : Finset V, G.IsClique (K : Set V) →
      (∀ u ∈ K, ∀ v ∈ K, st.idx u = st.idx v) → #K ≤ S ⌈/⌉ t ^ x) := by
  intro st
  have hinv := stageInv_stages hcol (τ := fun _ _ => t) (fun _ _ => ht) hc x
  obtain ⟨hS, hpal⟩ := stages_const_S_pal (col := col) (D := D) (G := G) (𝒬 := 𝒬) (S := S) ht x
  have hcov : IsCliqueCover st.G st.𝒬 D (S ⌈/⌉ t ^ x) := hS ▸ hinv.cover
  refine ⟨fun v => hpal ▸ hinv.idx_lt v, Nat.pow_le_pow_left (by
      rcases t with _ | t
      · omega
      · simp only [Nat.add_sub_cancel]; nlinarith) x, hinv.adj_iff, hcov, ?_, ?_⟩
  · have htx : (0 : ℝ) < (t : ℝ) ^ x := by positivity
    have h1 : S ⌈/⌉ t ^ x * t ^ x < S + t ^ x := by
      rw [Nat.ceilDiv_eq_add_pred_div]
      have := Nat.div_mul_le_self (S + t ^ x - 1) (t ^ x)
      have : 0 < t ^ x := pow_pos ht x
      omega
    have h2 : ((S ⌈/⌉ t ^ x : ℕ) : ℝ) * (t : ℝ) ^ x ≤ S + (t : ℝ) ^ x := by
      exact_mod_cast h1.le
    rw [div_add' _ _ _ htx.ne', le_div_iff₀ htx]
    nlinarith
  · intro hall K hK hidx
    refine (hinv.coversCliques hall).card_le hcov ?_
    intro a ha b hb hab
    exact (hinv.adj_iff a b).2 ⟨hK ha hb hab, hidx a ha b hb⟩

/-- **Theorem 2.5.** The colouring computed by CD-Coloring is proper. -/
theorem theorem_2_5 (hcol : IsDeltaColorer col) (ht : 0 < t) (hc : IsCliqueCover G 𝒬 D S)
    (x : ℕ) ⦃u v : V⦄ (huv : G.Adj u v) :
    cdColoring col D t G 𝒬 S x u ≠ cdColoring col D t G 𝒬 S x v :=
  (cdColoringSched_spec hcol (fun _ _ => ht) hc x).1 huv

/-- **Theorem 2.6.** CD-Coloring uses fewer than `(D(t-1)+1)^x · (D(⌈S/t^x⌉-1)+1)` colours, which
is at most `(tD)^x · (S/t^x + 2) · D`. -/
theorem theorem_2_6 (hcol : IsDeltaColorer col) (ht : 0 < t) (hD : 1 ≤ D)
    (hc : IsCliqueCover G 𝒬 D S) (x : ℕ) (v : V) :
    cdColoring col D t G 𝒬 S x v < (D * (t - 1) + 1) ^ x * (D * (S ⌈/⌉ t ^ x - 1) + 1) ∧
    (((D * (t - 1) + 1) ^ x * (D * (S ⌈/⌉ t ^ x - 1) + 1) : ℕ) : ℝ) ≤
      ((t : ℝ) * D) ^ x * (S / t ^ x + 2) * D := by
  obtain ⟨hS, hpal⟩ := stages_const_S_pal (col := col) (D := D) (G := G) (𝒬 := 𝒬) (S := S) ht x
  have h := (cdColoringSched_spec hcol (τ := fun _ _ => t) (fun _ _ => ht) hc x).2 v
  rw [hS, hpal] at h
  refine ⟨h, ?_⟩
  obtain ⟨-, hpow, -, -, hreal, -⟩ := theorem_2_4 (col := col) (𝒬 := 𝒬) hcol ht hD hc x
  set k := S ⌈/⌉ t ^ x
  have h1 : D * (k - 1) + 1 ≤ D * (k + 1) := by
    have : D * (k - 1) ≤ D * k := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith
  have h1' : ((D * (k - 1) + 1 : ℕ) : ℝ) ≤ D * ((k : ℝ) + 1) := by exact_mod_cast h1
  have h2 : ((D * (t - 1) + 1) ^ x : ℕ) ≤ (t * D) ^ x := hpow
  have h2' : (((D * (t - 1) + 1) ^ x : ℕ) : ℝ) ≤ ((t : ℝ) * D) ^ x := by exact_mod_cast h2
  have hk : (k : ℝ) + 1 ≤ S / t ^ x + 2 := by linarith
  push_cast
  push_cast at h1' h2'
  calc ((D : ℝ) * ((t - 1 : ℕ) : ℝ) + 1) ^ x * ((D : ℝ) * ((k - 1 : ℕ) : ℝ) + 1)
      ≤ ((t : ℝ) * D) ^ x * (D * ((k : ℝ) + 1)) := by
        apply mul_le_mul h2' h1' (by positivity) (by positivity)
    _ ≤ ((t : ℝ) * D) ^ x * (D * (S / t ^ x + 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hk (by positivity)
    _ = ((t : ℝ) * D) ^ x * (S / t ^ x + 2) * D := by ring

end Constant

/-! ### Theorem 3.2: `D^{x+1} S` colours -/

/-- The key inequality: for `t² ≤ S`, one recursion level multiplies `D · S - 1` by at most `D`:
`(D(t-1)+1) · (D⌈S/t⌉ - 1) ≤ D · (D S - 1)`. -/
lemma step_bound {D S t : ℕ} (hD : 1 ≤ D) (ht : 0 < t) (htS : t * t ≤ S) :
    (D * (t - 1) + 1) * (D * (S ⌈/⌉ t) - 1) ≤ D * (D * S - 1) := by
  set k := S ⌈/⌉ t
  have hk1 : S ≤ t * k := le_smul_ceilDiv ht
  have hk2 : k * t < S + t := by
    rw [show k = (S + t - 1) / t from Nat.ceilDiv_eq_add_pred_div S t]
    have := Nat.div_mul_le_self (S + t - 1) t
    omega
  have hkt : t ≤ k := by
    by_contra h
    push Not at h
    have : t * k < t * t := Nat.mul_lt_mul_of_pos_left h ht
    omega
  have hk0 : 1 ≤ k := le_trans ht hkt
  have hDk : 1 ≤ D * k := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have hS1 : 1 ≤ S := le_trans (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) htS
  have hDS : 1 ≤ D * S := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  suffices h : ((D * (t - 1) + 1 : ℕ) : ℤ) * ((D * k - 1 : ℕ) : ℤ) ≤ (D : ℤ) * ((D * S - 1 : ℕ) : ℤ) by
    exact_mod_cast h
  rw [Nat.cast_sub hDk, Nat.cast_sub hDS]
  push_cast [Nat.cast_sub ht]
  have hk2' : (k : ℤ) * t ≤ S + t - 1 := by
    have : ((k * t : ℕ) : ℤ) < ((S + t : ℕ) : ℤ) := by exact_mod_cast hk2
    push_cast at this; linarith
  have hD' : (1 : ℤ) ≤ D := by exact_mod_cast hD
  have hkt' : (t : ℤ) ≤ k := by exact_mod_cast hkt
  nlinarith [mul_le_mul_of_nonneg_left hk2' (by positivity : (0 : ℤ) ≤ (D : ℤ) * D),
    mul_le_mul_of_nonneg_left hkt' (by nlinarith : (0 : ℤ) ≤ (D : ℤ) * (D - 1))]

/-- **Theorem 3.2** (number of colours). Let `D ≥ 2`, `S ≥ 1`, and let the parameter `t` chosen at
every recursion level satisfy `0 < t` and `t² ≤ S_cur` for the current clique-size bound `S_cur`
(e.g. the paper's `t = ⌊S_cur^{1/(x+1)}⌋`, see `theorem_3_2_algA`). Then the colouring is proper
and uses fewer than `D^{x+1} S` colours (in fact at most `D^x (D S - 1)`), with no colour reduction. -/
theorem theorem_3_2 {col : SimpleGraph V → ℕ → V → ℕ} {D : ℕ} {τ : ℕ → ℕ → ℕ}
    {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {S : ℕ}
    (hcol : IsDeltaColorer col) (hD : 2 ≤ D) (hS : 1 ≤ S)
    (hτ : ∀ j s, 0 < τ j s) (hτS : ∀ j s, 1 ≤ s → τ j s * τ j s ≤ s)
    (hc : IsCliqueCover G 𝒬 D S) (x : ℕ) :
    (∀ ⦃u v⦄, G.Adj u v → cdColoringSched col D τ G 𝒬 S x u ≠ cdColoringSched col D τ G 𝒬 S x v)
    ∧ ∀ v, cdColoringSched col D τ G 𝒬 S x v < D ^ (x + 1) * S := by
  obtain ⟨hprop, hlt⟩ := cdColoringSched_spec hcol hτ hc x
  refine ⟨hprop, fun v => (hlt v).trans_le ?_⟩
  -- invariant: `pal_j · (D S_j - 1) ≤ D^j · (D S - 1)` and `S_j ≥ 1`
  have key : ∀ j, 1 ≤ (stages col D τ G 𝒬 S j).S ∧
      (stages col D τ G 𝒬 S j).pal * (D * (stages col D τ G 𝒬 S j).S - 1) ≤
        D ^ j * (D * S - 1) := by
    intro j
    induction j with
    | zero => simp [stages, hS]
    | succ j ih =>
      obtain ⟨h1, h2⟩ := ih
      set st := stages col D τ G 𝒬 S j
      have hstep := step_bound (D := D) (S := st.S) (by omega) (hτ j st.S) (hτS j st.S h1)
      refine ⟨one_le_ceilDiv h1 (hτ j st.S), ?_⟩
      change st.pal * (D * (τ j st.S - 1) + 1) * (D * (st.S ⌈/⌉ τ j st.S) - 1) ≤ _
      calc st.pal * (D * (τ j st.S - 1) + 1) * (D * (st.S ⌈/⌉ τ j st.S) - 1)
          = st.pal * ((D * (τ j st.S - 1) + 1) * (D * (st.S ⌈/⌉ τ j st.S) - 1)) := by ring
        _ ≤ st.pal * (D * (D * st.S - 1)) := Nat.mul_le_mul_left _ hstep
        _ = D * (st.pal * (D * st.S - 1)) := by ring
        _ ≤ D * (D ^ j * (D * S - 1)) := Nat.mul_le_mul_left _ h2
        _ = D ^ (j + 1) * (D * S - 1) := by ring
  obtain ⟨h1, h2⟩ := key x
  set st := stages col D τ G 𝒬 S x
  have h3 : D * (st.S - 1) + 1 ≤ D * st.S - 1 := by
    rw [Nat.mul_sub_one]
    have : D ≤ D * st.S := Nat.le_mul_of_pos_right D h1
    omega
  have h4 : D * S - 1 < D * S := by
    have : 1 ≤ D * S := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
    omega
  calc st.pal * (D * (st.S - 1) + 1) ≤ st.pal * (D * st.S - 1) := Nat.mul_le_mul_left _ h3
    _ ≤ D ^ x * (D * S - 1) := h2
    _ ≤ D ^ x * (D * S) := Nat.mul_le_mul_left _ h4.le
    _ = D ^ (x + 1) * S := by ring

/-- `⌊S^{1/r}⌋`: the largest `t` with `t^r ≤ S`. -/
def floorRoot (r S : ℕ) : ℕ := Nat.findGreatest (fun t => t ^ r ≤ S) S

lemma floorRoot_spec {r S : ℕ} (hr : 2 ≤ r) (hS : 1 ≤ S) :
    0 < floorRoot r S ∧ floorRoot r S * floorRoot r S ≤ S := by
  have h1 : (fun t => t ^ r ≤ S) 1 := by simpa using hS
  have hpos : 1 ≤ floorRoot r S := Nat.le_findGreatest hS h1
  have hP : floorRoot r S ^ r ≤ S := Nat.findGreatest_spec (P := fun t => t ^ r ≤ S) hS h1
  refine ⟨hpos, ?_⟩
  calc floorRoot r S * floorRoot r S = floorRoot r S ^ 2 := by ring
    _ ≤ floorRoot r S ^ r := Nat.pow_le_pow_right hpos hr
    _ ≤ S := hP

/-- The parameter schedule of the paper's algorithm `𝒜_x` (proof of Theorem 3.2, Theorem 3.3):
at recursion level `j` (`𝒜_{x-j}`), with current clique size `S_j`, use
`t = ⌊S_j^{1/(x-j+1)}⌋` (so `t = ⌊S^{1/(x+1)}⌋` at the top level and `t = ⌊√S_j⌋` in `𝒜_1`).
Only the levels `j < x` are used; the `max 2` and the case `S_j = 0` only make the schedule total. -/
def algASched (x : ℕ) (j s : ℕ) : ℕ := if s = 0 then 1 else floorRoot (max 2 (x - j + 1)) s

/-- Sanity check of the schedule: `𝒜_2` on `S = 64` uses `t = ⌊64^{1/3}⌋ = 4`, then `𝒜_1` on
`S' = 16` uses `t = ⌊√16⌋ = 4`. -/
example : algASched 2 0 64 = 4 ∧ algASched 2 1 16 = 4 := by decide

/-- **Theorem 3.2** for the paper's algorithm `𝒜_x`: for `D ≥ 2` and `S ≥ 1` the `D^{x+1} S`
bound holds for `𝒜_x` (with `x` connector levels and `t = ⌊S^{1/(x+1)}⌋`, recomputed at every
level). -/
theorem theorem_3_2_algA {col : SimpleGraph V → ℕ → V → ℕ} {D : ℕ}
    {G : SimpleGraph V} {𝒬 : Finset (Finset V)} {S : ℕ}
    (hcol : IsDeltaColorer col) (hD : 2 ≤ D) (hS : 1 ≤ S)
    (hc : IsCliqueCover G 𝒬 D S) (x : ℕ) :
    (∀ ⦃u v⦄, G.Adj u v →
      cdColoringSched col D (algASched x) G 𝒬 S x u ≠ cdColoringSched col D (algASched x) G 𝒬 S x v)
    ∧ ∀ v, cdColoringSched col D (algASched x) G 𝒬 S x v < D ^ (x + 1) * S := by
  refine theorem_3_2 hcol hD hS (fun j s => ?_) (fun j s hs => ?_) hc x
  · unfold algASched
    split_ifs with h
    · exact Nat.one_pos
    · exact (floorRoot_spec (by omega) (Nat.one_le_iff_ne_zero.2 h)).1
  · unfold algASched
    have hs0 : s ≠ 0 := by omega
    simp only [hs0, ↓reduceIte]
    exact (floorRoot_spec (by omega) hs).2

/-- The paper's inductive step for `𝒜_{i+1}` bounds the colours by
`(D(t-1)+1) · D^{i+1} ⌈S/t⌉` (using only the induction hypothesis that `𝒜_i` uses `D^{i+1} S'`
colours) and claims this is `≤ D^{i+2} S` "for S larger than some constant since
`(D-1)(S/t) > Dt`, because `t = ⌊S^{1/(i+1)}⌋` and `i ≥ 2`". For `i = 1` (`t = ⌊√S⌋`) this fails
for arbitrarily large `S`; here `D = 2`, `S = 31`, `t = 5`: `9 · 4 · 7 = 252 > 248 = 2³ · 31`. -/
theorem paper_inductive_step_fails :
    floorRoot 2 31 = 5 ∧
    (2 * (5 - 1) + 1) * 2 ^ 2 * (31 ⌈/⌉ 5) > 2 ^ 3 * 31 := by
  refine ⟨by decide, by decide⟩

end Podc.DeltaEdgeColoring
