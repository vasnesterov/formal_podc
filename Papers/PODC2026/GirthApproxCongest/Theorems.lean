import Papers.PODC2026.GirthApproxCongest.Asymptotic
import Papers.PODC2026.GirthApproxCongest.Cycles
import Papers.PODC2026.GirthApproxCongest.PointsLines

/-!
# Main results of §6 (Chechik–Lifshitz–Mukhtar, *Girth Approximations in the CONGEST Model*)

Model (see the README): synchronous CONGEST on the underlying undirected network, `B`-bit messages
per edge, direction and round; node `v` knows its ID and the directions / weights of its incident
edges. Outputs: every node outputs `none` or an estimate, some node outputs an estimate, and
every estimate lies in `[girth, α · girth]` (`ApproxOutput`, the weakest convention). Randomized
algorithms: private random strings per node; the lower bound is conditional on the
(public-coin) randomized communication lower bound for set disjointness, `PubRandDisjLB`.

* `theorem_6_1`, `theorem_6_1_weighted` (fixed parameters, deterministic) and `_rand`:
  on the graphs of §6.0.1 / §6.1 built from `H` of girth `≥ 2k` with `m` edges and `q` layers,
  `q ≤ 2T + 1` or `m ≤ 2T(d + 1)B + 2`, i.e. `T = Ω(min(q, m / (B log n)))` (Theorem 6.1 with
  general `k` as in §6.2).
* `theorem_6_2_directed`, `theorem_6_2_weighted` and `_rand`: **Theorem 6.2**: for `k ≥ 3`,
  assuming `DenseHighGirth k` (Erdős–Simonovits), a `(k - ε)`-approximation of the girth needs
  `Ω(n^{k/(2k-1)} / (B log n))` rounds on networks of diameter `≤ 2 log₂ n + 4`.
* `theorem_6_1_directed_asymp`, `theorem_6_1_weighted_asymp`: the unconditional case `k = 3`
  (`DenseHighGirth 3` is proved in `PointsLines.lean`): `(3 - ε)`-approximation needs
  `Ω(n^{3/5} / (B log n))` rounds.
-/

namespace Podc.GirthApproxCongest

open Filter Finset Podc.MinWeightCycleCongest Cslib.Congest

open scoped ENNReal

/-! ### Fixed parameters -/

section Fixed

variable {L R : Type*} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R] {q d p : ℕ}
  {E : Finset (L × R)}

/-- **Theorem 6.1** (directed, deterministic; general `k` as in §6.2). Let `H` (edge set `E`)
have girth `≥ 2k`, let `G_{x,y}` be the graph of §6.0.1 with `q ≥ 2` layers and a shortcut tree
of depth `d` (`q ≤ 2^d`), relabelled to the node set `V`. If a deterministic CONGEST algorithm
with `B`-bit messages outputs within `T` rounds an `α`-approximation (`α < k`) of the girth of
every unweighted digraph on `V` whose underlying network has diameter `≤ 2(d + 1)`, then
`q ≤ 2T + 1` or `|E| ≤ T · 2(d + 1) · B + 2`. -/
theorem theorem_6_1 {V σ : Type*} [Fintype V] [DecidableEq V] (e : V ≃ Vtx L R q d p)
    {k W B T : ℕ} (hq : 2 ≤ q) (hqd : q ≤ 2 ^ d)
    (hgirth : ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth) {α : ℝ≥0∞} (hα : α < k)
    (A : Algorithm V (DInput V (W + 1)) σ B) (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ D : WDigraph V (W + 1), D.Unweighted → D.net.ediam ≤ 2 * (d + 1) →
      ApproxOutput α D.mwc (outputs A est D.net D.view T)) :
    q ≤ 2 * T + 1 ∨ E.card ≤ T * (2 * ((d + 1) * B)) + 2 :=
  dir_lowerBound_of_gap e hqd A est (gap_dir hα (by omega))
    (fun _ _ h => (dGraph_mwc_of_inter W hq h).le) (fun _ _ h => dGraph_mwc_of_disj W k hq hgirth h)
    hA

/-- **Theorem 6.1, randomized** (conditional on `PubRandDisjLB δ κ`). -/
theorem theorem_6_1_rand {L R : Type} [DecidableEq L] [DecidableEq R] [Fintype L] [Fintype R]
    {E : Finset (L × R)} {V ρ σ : Type} [Fintype V] [DecidableEq V] [Fintype ρ] [Nonempty ρ]
    (e : V ≃ Vtx L R q d p) {k W B T : ℕ} (hq : 2 ≤ q) (hqd : q ≤ 2 ^ d)
    (hgirth : ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth) {α : ℝ≥0∞} (hα : α < k)
    {δ κ : ℝ} (hDisj : PubRandDisjLB δ κ)
    (A : Algorithm V (DInput V (W + 1) × ρ) σ B) (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ D : WDigraph V (W + 1), D.Unweighted → D.net.ediam ≤ 2 * (d + 1) →
      (failCount A est D.net D.view T α D.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) :
    q ≤ 2 * T + 1 ∨ κ * E.card ≤ T * (2 * ((d + 1) * B)) + 2 :=
  dir_rand_lowerBound_of_gap e hqd A est (gap_dir hα (by omega)) hDisj
    (fun _ _ h => (dGraph_mwc_of_inter W hq h).le) (fun _ _ h => dGraph_mwc_of_disj W k hq hgirth h)
    hA

/-- **§6.1, Theorem 6.1 for undirected weighted graphs** (deterministic). Pipe edges weigh `1`,
input edges `Win`, tree edges `Wt ≥ k · Win` (all `≤ Wm`). If
`α · (2(q - 1) + 2 Win) < 2k Win` and an algorithm `α`-approximates the girth of every weighted
graph on `V` with positive weights in `{1, …, Wm}` and diameter `≤ 2(d + 1)` within `T` rounds, then
`q ≤ 2T + 1` or `|E| ≤ T · 2(d + 1) · B + 2`. -/
theorem theorem_6_1_weighted {V σ : Type*} [Fintype V] [DecidableEq V] (e : V ≃ Vtx L R q d p)
    {k Wm Win Wt B T : ℕ} (hq : 2 ≤ q) (hqd : q ≤ 2 ^ d) (hW : Win ≤ Wm) (hWt : Wt ≤ Wm)
    (hW1 : 1 ≤ Wm) (hkW : k * Win ≤ Wt)
    (hgirth : ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth) {α : ℝ≥0∞}
    (hα : α * ((2 * (q - 1) + 2 * Win : ℕ) : ℝ≥0∞) < ((2 * k * Win : ℕ) : ℝ≥0∞))
    (A : Algorithm V (V → Option (Fin (Wm + 1))) σ B) (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
      G.net.ediam ≤ 2 * (d + 1) →
      ApproxOutput α G.mwc (outputs A est G.net G.view T)) :
    q ≤ 2 * T + 1 ∨ E.card ≤ T * (2 * ((d + 1) * B)) + 2 := by
  have hk : 0 < 2 * k * Win := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hα
  have hWin : 1 ≤ Win := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
  have hWt1 : 1 ≤ Wt := le_trans (by nlinarith) hkW
  exact undir_lowerBound_of_gap (Win := Win) (Wt := Wt) e hqd A est hα
    (fun _ _ h => uGraph_mwc_of_inter hq hW hWt hW1 h)
    (fun _ _ h => uGraph_mwc_of_disj k hq hW hWt hW1 hgirth hkW h) hW hWt hWin hWt1 hA

/-- **§6.1, randomized** (conditional on `PubRandDisjLB δ κ`). -/
theorem theorem_6_1_weighted_rand {L R : Type} [DecidableEq L] [DecidableEq R] [Fintype L]
    [Fintype R] {E : Finset (L × R)} {V ρ σ : Type} [Fintype V] [DecidableEq V] [Fintype ρ]
    [Nonempty ρ] (e : V ≃ Vtx L R q d p) {k Wm Win Wt B T : ℕ} (hq : 2 ≤ q) (hqd : q ≤ 2 ^ d)
    (hW : Win ≤ Wm) (hWt : Wt ≤ Wm) (hW1 : 1 ≤ Wm) (hkW : k * Win ≤ Wt)
    (hgirth : ((2 * k : ℕ) : ℕ∞) ≤ (bipGraph E).egirth) {α : ℝ≥0∞}
    (hα : α * ((2 * (q - 1) + 2 * Win : ℕ) : ℝ≥0∞) < ((2 * k * Win : ℕ) : ℝ≥0∞))
    {δ κ : ℝ} (hDisj : PubRandDisjLB δ κ)
    (A : Algorithm V ((V → Option (Fin (Wm + 1))) × ρ) σ B) (est : V → σ → Option ℝ≥0∞)
    (hA : ∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
      G.net.ediam ≤ 2 * (d + 1) →
      (failCount A est G.net G.view T α G.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) :
    q ≤ 2 * T + 1 ∨ κ * E.card ≤ T * (2 * ((d + 1) * B)) + 2 := by
  have hk : 0 < 2 * k * Win := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hα
  have hWin : 1 ≤ Win := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
  have hWt1 : 1 ≤ Wt := le_trans (by nlinarith) hkW
  exact undir_rand_lowerBound_of_gap (Win := Win) (Wt := Wt) e hqd A est hα hDisj
    (fun _ _ h => uGraph_mwc_of_inter hq hW hWt hW1 h)
    (fun _ _ h => uGraph_mwc_of_disj k hq hW hWt hW1 hgirth hkW h) hW hWt hWin hWt1 hA

omit [Fintype L] [Fintype R] in
/-- **The value in Claim 6.2(1) is slightly off.** The paper states that in the intersecting
case the weighted girth *equals* `2q/ε · (1 + ε) = 2q + 2·Win` (with `Win = q/ε`). The pipes have
`q - 1` edges, so the intersecting cycle weighs `2(q - 1) + 2·Win`, strictly less. (Harmless:
only the upper bound is used.) -/
theorem claim_6_2_value_lt {Wm Win Wt : ℕ} {x y : E → Bool} (hq : 2 ≤ q) (hW : Win ≤ Wm)
    (hWt : Wt ≤ Wm) (hW1 : 1 ≤ Wm) (h : ∃ i, x i = true ∧ y i = true) :
    (uGraph (q := q) (d := d) (p := p) Wm Win Wt x y).mwc < ((2 * q + 2 * Win : ℕ) : ℝ≥0∞) :=
  (uGraph_mwc_of_inter hq hW hWt hW1 h).trans_lt (by exact_mod_cast (by omega))

end Fixed

/-! ### Theorem 6.2 -/

lemma diam_cast (n : ℕ) : 2 * (((dOf n : ℕ) : ℕ∞) + 1) = 2 * ((Nat.log 2 n : ℕ∞) + 2) := by
  simp only [dOf]; push_cast; ring

lemma qOf_le_two_pow (k n : ℕ) : qOf k n ≤ 2 ^ dOf n := (Nat.div_le_self _ _).trans (le_two_pow_dOf n)

/-- **Theorem 6.2** (directed, deterministic). Let `k ≥ 3` and assume `DenseHighGirth k` (the
Erdős–Simonovits even cycle conjecture in bipartite form). For every `α < k` there are `C > 0`
and `n₀` such that every deterministic CONGEST algorithm with `B`-bit messages that, on every
unweighted `n`-node digraph (`n ≥ n₀`) whose underlying network has diameter `≤ 2 log₂ n + 4`,
outputs an `α`-approximation of the girth within `T` rounds satisfies
`C · n^{k/(2k-1)} ≤ (T + 1)(B + 1)(log₂ n + 2)`, i.e. `T = Ω̃(n^{k/(2k-1)})` for `B = O(log n)`. -/
theorem theorem_6_2_directed {k : ℕ} (hk : 3 ≤ k) (hES : DenseHighGirth k) {α : ℝ≥0∞}
    (hα : α < k) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (V σ : Type) [Fintype V] [DecidableEq V] (W B T : ℕ),
      n₀ ≤ Fintype.card V → ∀ (A : Algorithm V (DInput V (W + 1)) σ B)
      (est : V → σ → Option ℝ≥0∞),
      (∀ D : WDigraph V (W + 1), D.Unweighted →
        D.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
        ApproxOutput α D.mwc (outputs A est D.net D.view T)) →
      C * (Fintype.card V : ℝ) ^ ((k : ℝ) / (2 * k - 1)) ≤
        (T + 1) * (B + 1) * (Nat.log 2 (Fintype.card V) + 2) := by
  obtain ⟨c, hc, hE⟩ := hES
  obtain ⟨C, hC, hev⟩ := core hk hc one_pos
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨C, hC, n₀, fun V σ _ _ W B T hn A est hA => ?_⟩
  obtain ⟨ha, hq2, hfin⟩ := hn₀ _ hn
  obtain ⟨E, hgirth, hcard⟩ := hE _ ha
  obtain ⟨p, ⟨e⟩⟩ := exists_equiv_vtx k V
  have h := theorem_6_1 (E := E) e hq2 (qOf_le_two_pow _ _) hgirth hα A est
    (fun D hD hdiam => hA D hD (by rwa [diam_cast] at hdiam))
  refine hfin T B E.card hcard ?_
  rcases h with h | h
  · exact Or.inl h
  · right; rw [one_mul]; exact_mod_cast h

/-- **Theorem 6.2** (directed, randomized), conditional on `PubRandDisjLB δ κ` with `κ > 0`. -/
theorem theorem_6_2_directed_rand {k : ℕ} (hk : 3 ≤ k) (hES : DenseHighGirth k) {α : ℝ≥0∞}
    (hα : α < k) {δ κ : ℝ} (hκ : 0 < κ) (hDisj : PubRandDisjLB δ κ) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (V ρ σ : Type) [Fintype V] [DecidableEq V] [Fintype ρ]
      [Nonempty ρ] (W B T : ℕ), n₀ ≤ Fintype.card V →
      ∀ (A : Algorithm V (DInput V (W + 1) × ρ) σ B) (est : V → σ → Option ℝ≥0∞),
      (∀ D : WDigraph V (W + 1), D.Unweighted →
        D.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
        (failCount A est D.net D.view T α D.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) →
      C * (Fintype.card V : ℝ) ^ ((k : ℝ) / (2 * k - 1)) ≤
        (T + 1) * (B + 1) * (Nat.log 2 (Fintype.card V) + 2) := by
  obtain ⟨c, hc, hE⟩ := hES
  obtain ⟨C, hC, hev⟩ := core hk hc hκ
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨C, hC, n₀, fun V ρ σ _ _ _ _ W B T hn A est hA => ?_⟩
  obtain ⟨ha, hq2, hfin⟩ := hn₀ _ hn
  obtain ⟨E, hgirth, hcard⟩ := hE _ ha
  obtain ⟨p, ⟨e⟩⟩ := exists_equiv_vtx k V
  have h := theorem_6_1_rand (E := E) e hq2 (qOf_le_two_pow _ _) hgirth hα hDisj A est
    (fun D hD hdiam => hA D hD (by rwa [diam_cast] at hdiam))
  refine hfin T B E.card hcard ?_
  rcases h with h | h
  · exact Or.inl h
  · right; exact_mod_cast h

/-- **Theorem 6.2** (undirected weighted, deterministic). Let `k ≥ 3`, assume
`DenseHighGirth k`, and let `α < k`. There are `M`, `C > 0` and `n₀` such that, for positive weights in
`{1, …, Wm}` with `Wm ≥ k M n` (polynomially bounded), every deterministic CONGEST algorithm that
outputs an `α`-approximation of the girth of every weighted `n`-node graph (`n ≥ n₀`) of
diameter `≤ 2 log₂ n + 4` within `T` rounds satisfies
`C · n^{k/(2k-1)} ≤ (T + 1)(B + 1)(log₂ n + 2)`. -/
theorem theorem_6_2_weighted {k : ℕ} (hk : 3 ≤ k) (hES : DenseHighGirth k) {α : ℝ≥0∞}
    (hα : α < k) :
    ∃ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (V σ : Type) [Fintype V] [DecidableEq V]
      (Wm B T : ℕ), n₀ ≤ Fintype.card V → k * M * Fintype.card V ≤ Wm →
      ∀ (A : Algorithm V (V → Option (Fin (Wm + 1))) σ B) (est : V → σ → Option ℝ≥0∞),
      (∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
        G.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
        ApproxOutput α G.mwc (outputs A est G.net G.view T)) →
      C * (Fintype.card V : ℝ) ^ ((k : ℝ) / (2 * k - 1)) ≤
        (T + 1) * (B + 1) * (Nat.log 2 (Fintype.card V) + 2) := by
  obtain ⟨M, hM1, hM⟩ := gap_undir hα
  obtain ⟨c, hc, hE⟩ := hES
  obtain ⟨C, hC, hev⟩ := core hk hc one_pos
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨M, C, hC, n₀, fun V σ _ _ Wm B T hn hWm A est hA => ?_⟩
  obtain ⟨ha, hq2, hfin⟩ := hn₀ _ hn
  obtain ⟨E, hgirth, hcard⟩ := hE _ ha
  obtain ⟨p, ⟨e⟩⟩ := exists_equiv_vtx k V
  have hqn : qOf k (Fintype.card V) ≤ Fintype.card V := Nat.div_le_self _ _
  have hMq : M * qOf k (Fintype.card V) ≤ M * Fintype.card V := Nat.mul_le_mul_left _ hqn
  have hkM : k * (M * qOf k (Fintype.card V)) ≤ Wm := by nlinarith
  have hW : M * qOf k (Fintype.card V) ≤ Wm := by nlinarith
  have hW1 : 1 ≤ Wm := by nlinarith
  have h := theorem_6_1_weighted (E := E) (k := k) (Win := M * qOf k (Fintype.card V))
    (Wt := k * (M * qOf k (Fintype.card V))) e hq2 (qOf_le_two_pow _ _) hW hkM hW1 le_rfl hgirth
    (hM _ (by omega)) A est (fun G hpos hdiam => hA G hpos (by rwa [diam_cast] at hdiam))
  refine hfin T B E.card hcard ?_
  rcases h with h | h
  · exact Or.inl h
  · right; rw [one_mul]; exact_mod_cast h

/-- **Theorem 6.2** (undirected weighted, randomized), conditional on `PubRandDisjLB δ κ`. -/
theorem theorem_6_2_weighted_rand {k : ℕ} (hk : 3 ≤ k) (hES : DenseHighGirth k) {α : ℝ≥0∞}
    (hα : α < k) {δ κ : ℝ} (hκ : 0 < κ) (hDisj : PubRandDisjLB δ κ) :
    ∃ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (V ρ σ : Type) [Fintype V] [DecidableEq V]
      [Fintype ρ] [Nonempty ρ] (Wm B T : ℕ), n₀ ≤ Fintype.card V →
      k * M * Fintype.card V ≤ Wm →
      ∀ (A : Algorithm V ((V → Option (Fin (Wm + 1))) × ρ) σ B) (est : V → σ → Option ℝ≥0∞),
      (∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
        G.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
        (failCount A est G.net G.view T α G.mwc : ℝ) ≤ δ * Fintype.card (V → ρ)) →
      C * (Fintype.card V : ℝ) ^ ((k : ℝ) / (2 * k - 1)) ≤
        (T + 1) * (B + 1) * (Nat.log 2 (Fintype.card V) + 2) := by
  obtain ⟨M, hM1, hM⟩ := gap_undir hα
  obtain ⟨c, hc, hE⟩ := hES
  obtain ⟨C, hC, hev⟩ := core hk hc hκ
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  refine ⟨M, C, hC, n₀, fun V ρ σ _ _ _ _ Wm B T hn hWm A est hA => ?_⟩
  obtain ⟨ha, hq2, hfin⟩ := hn₀ _ hn
  obtain ⟨E, hgirth, hcard⟩ := hE _ ha
  obtain ⟨p, ⟨e⟩⟩ := exists_equiv_vtx k V
  have hqn : qOf k (Fintype.card V) ≤ Fintype.card V := Nat.div_le_self _ _
  have hMq : M * qOf k (Fintype.card V) ≤ M * Fintype.card V := Nat.mul_le_mul_left _ hqn
  have hkM : k * (M * qOf k (Fintype.card V)) ≤ Wm := by nlinarith
  have hW : M * qOf k (Fintype.card V) ≤ Wm := by nlinarith
  have hW1 : 1 ≤ Wm := by nlinarith
  have h := theorem_6_1_weighted_rand (E := E) (k := k) (Win := M * qOf k (Fintype.card V))
    (Wt := k * (M * qOf k (Fintype.card V))) e hq2 (qOf_le_two_pow _ _) hW hkM hW1 le_rfl hgirth
    (hM _ (by omega)) hDisj A est (fun G hpos hdiam => hA G hpos (by rwa [diam_cast] at hdiam))
  refine hfin T B E.card hcard ?_
  rcases h with h | h
  · exact Or.inl h
  · right; exact_mod_cast h

/-! ### The unconditional case `k = 3` -/

lemma exponent_three : ((3 : ℕ) : ℝ) / (2 * ((3 : ℕ) : ℝ) - 1) = 3 / 5 := by norm_num

/-- **Theorem 6.1, asymptotic form** (directed, unconditional): a `(3 - ε)`-approximation of the
directed girth needs `Ω(n^{3/5} / (B log n))` rounds, even on networks of diameter
`≤ 2 log₂ n + 4`. -/
theorem theorem_6_1_directed_asymp {α : ℝ≥0∞} (hα : α < 3) :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (V σ : Type) [Fintype V] [DecidableEq V] (W B T : ℕ),
      n₀ ≤ Fintype.card V → ∀ (A : Algorithm V (DInput V (W + 1)) σ B)
      (est : V → σ → Option ℝ≥0∞),
      (∀ D : WDigraph V (W + 1), D.Unweighted →
        D.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
        ApproxOutput α D.mwc (outputs A est D.net D.view T)) →
      C * (Fintype.card V : ℝ) ^ (3 / 5 : ℝ) ≤
        (T + 1) * (B + 1) * (Nat.log 2 (Fintype.card V) + 2) := by
  have := theorem_6_2_directed le_rfl denseHighGirth_three (k := 3) (by exact_mod_cast hα)
  rwa [exponent_three] at this

/-- **§6.1, asymptotic form** (undirected weighted, unconditional): a `(3 - ε)`-approximation of
the weighted girth needs `Ω(n^{3/5} / (B log n))` rounds (weights `O(n)`). -/
theorem theorem_6_1_weighted_asymp {α : ℝ≥0∞} (hα : α < 3) :
    ∃ M : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ (V σ : Type) [Fintype V] [DecidableEq V]
      (Wm B T : ℕ), n₀ ≤ Fintype.card V → 3 * M * Fintype.card V ≤ Wm →
      ∀ (A : Algorithm V (V → Option (Fin (Wm + 1))) σ B) (est : V → σ → Option ℝ≥0∞),
      (∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
        G.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
        ApproxOutput α G.mwc (outputs A est G.net G.view T)) →
      C * (Fintype.card V : ℝ) ^ (3 / 5 : ℝ) ≤
        (T + 1) * (B + 1) * (Nat.log 2 (Fintype.card V) + 2) := by
  have := theorem_6_2_weighted le_rfl denseHighGirth_three (k := 3) (by exact_mod_cast hα)
  rwa [exponent_three] at this

end Podc.GirthApproxCongest

namespace Podc.GirthApproxCongest

/-- **The extremal bound quoted in §6 is off by one in the exponent.** The paper states
(attributing it to Bondy–Simonovits) that `ex(n, C_{<2k}) = O(n^{1+1/k})`. For `k = 3` this is
false: there are bipartite graphs on `2a` vertices with girth `≥ 6` (no cycle shorter than `6`)
and `Ω(a^{3/2})` edges (`denseHighGirth_three`), so no bound `C · n^{4/3}` holds. The correct
bound for girth `≥ 2k` is `O(n^{1+1/(k-1)})`, which is what §6.0.1 and §6.2 actually use. -/
theorem ex_bound_misquoted : ¬ ∃ C : ℝ, ∀ a : ℕ, 1 ≤ a → ∀ E : Finset (Fin a × Fin a),
    ((2 * 3 : ℕ) : ℕ∞) ≤ (bipGraph E).egirth →
      (E.card : ℝ) ≤ C * (2 * (a : ℝ)) ^ (1 + 1 / (3 : ℝ)) := by
  rintro ⟨C, hC⟩
  obtain ⟨c, hc, hE⟩ := denseHighGirth_three
  set N : ℝ := 4 * |C| / c + 1 with hN
  have hN0 : 0 < N := by positivity
  set a : ℕ := ⌈N ^ (6 : ℝ)⌉₊ + 1
  have ha1 : 1 ≤ a := by omega
  have ha0 : (0 : ℝ) < a := by positivity
  obtain ⟨E, hg, hcard⟩ := hE a ha1
  have h1 := hC a ha1 E hg
  have e1 : (1 + 1 / (((3 : ℕ) : ℝ) - 1) : ℝ) = 3 / 2 := by norm_num
  rw [e1] at hcard
  -- `(2a)^{4/3} ≤ 4 a^{4/3}`
  have h2 : (2 * (a : ℝ)) ^ (1 + 1 / (3 : ℝ)) ≤ 4 * (a : ℝ) ^ (4 / 3 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) ha0.le, show (1 + 1 / (3 : ℝ)) = 4 / 3 by norm_num]
    gcongr
    have : (2 : ℝ) ^ (4 / 3 : ℝ) ≤ 2 ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h4 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
    nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) (4 / 3 : ℝ)]
  have h3 : c * (a : ℝ) ^ (3 / 2 : ℝ) ≤ 4 * |C| * (a : ℝ) ^ (4 / 3 : ℝ) := by
    have hpos : 0 ≤ (2 * (a : ℝ)) ^ (1 + 1 / (3 : ℝ)) := by positivity
    calc c * (a : ℝ) ^ (3 / 2 : ℝ) ≤ E.card := hcard
      _ ≤ C * (2 * (a : ℝ)) ^ (1 + 1 / (3 : ℝ)) := h1
      _ ≤ |C| * (2 * (a : ℝ)) ^ (1 + 1 / (3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hpos
      _ ≤ |C| * (4 * (a : ℝ) ^ (4 / 3 : ℝ)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg C)
      _ = _ := by ring
  have hsplit : (a : ℝ) ^ (3 / 2 : ℝ) = (a : ℝ) ^ (4 / 3 : ℝ) * (a : ℝ) ^ (1 / 6 : ℝ) := by
    rw [← Real.rpow_add ha0]; norm_num
  rw [hsplit] at h3
  have hpow : 0 < (a : ℝ) ^ (4 / 3 : ℝ) := by positivity
  have h5 : c * (a : ℝ) ^ (1 / 6 : ℝ) ≤ 4 * |C| := by
    have := h3
    rw [show c * ((a : ℝ) ^ (4 / 3 : ℝ) * (a : ℝ) ^ (1 / 6 : ℝ)) =
      (c * (a : ℝ) ^ (1 / 6 : ℝ)) * (a : ℝ) ^ (4 / 3 : ℝ) by ring] at this
    exact le_of_mul_le_mul_right this hpow
  -- but `a^{1/6} ≥ N`
  have h6 : N ≤ (a : ℝ) ^ (1 / 6 : ℝ) := by
    have hNa : N ^ (6 : ℝ) ≤ a := by
      have := Nat.le_ceil (N ^ (6 : ℝ)); simp only [a]; push_cast; linarith
    calc N = (N ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
          rw [← Real.rpow_mul hN0.le]; norm_num
      _ ≤ (a : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_le_rpow (by positivity) hNa (by norm_num)
  have h7 : c * N ≤ 4 * |C| := (mul_le_mul_of_nonneg_left h6 hc.le).trans h5
  rw [hN, mul_add, mul_div_cancel₀ _ hc.ne'] at h7
  linarith

end Podc.GirthApproxCongest
