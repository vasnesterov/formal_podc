import Papers.PODC2011.FaultTolerantSpanners.Sampling
import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
import Mathlib

/-!
# The conversion theorem (Theorem 2.1 of Dinitz–Krauthgamer, PODC'11): explicit form

**Model.** A weighted simple graph `(G, w)` on a finite vertex type `V` (`n = |V|`), weights
`w : Sym2 V → ℝ≥0` (nonnegative edge lengths), vertex faults. A *`k`-spanner algorithm with size
bound `f`* (`SpannerAlg G w k f`) is modelled by its outputs on the induced subgraphs `G[S]`
(`G.deleteVerts Sᶜ` in CSLib's same-vertex-type convention): a subgraph `run S ≤ G[S]` with
`d_{run S}(u, v) ≤ k · d_{G[S]}(u, v)` for `u, v ∈ S` and at most `f |S|` edges. These are the only
graphs the conversion ever runs the algorithm on.

**Algorithm.** Repeat `α` times independently: every vertex joins `J` with probability `1 - 1/m`
(realised as a uniform label in `Fin m`, label `0` = survives, see `Sampling.lean`); run the
algorithm on `G \ J = G[surv]`. Output the union `ftUnion A ω` of the `α` spanners.

**Results.**
* `isWeightedVFTSpanner_ftUnion` — deterministic core: if for every fault set `F` (`|F| ≤ r`) and
  every edge `uv` of `G \ F` some iteration has `u, v` surviving and `F ⊆ J`, the union is an
  `r`-fault-tolerant `k`-spanner.
* `uprob_good` — that event has probability exactly `(1/m)² (1 - 1/m)^{|F|}` per iteration.
* `uprob_not_isVFT_le` — union bound: `Pr[not an r-FT k-spanner] ≤ (n+1)^r n² (1 - q)^α`, with
  `q = (1/m)² (1 - 1/m)^r`.
* `ncard_ftUnion_le`, `uprob_size_fail_le` — if every iteration keeps `≤ 2n/m` vertices then
  `|E(H)| ≤ α f(⌊2n/m⌋)`; this fails with probability `≤ α e^{-n/(3m)}`.
* `conversion_explicit` — both together.
-/

open Finset SimpleGraph Cslib.Probability
open scoped ENNReal NNReal

namespace DinitzKrauthgamer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A `k`-spanner algorithm with size bound `f`, as used by Theorem 2.1, given by its outputs on the
induced subgraphs `G[S] = G.deleteVerts Sᶜ` of a fixed weighted graph `(G, w)`. -/
structure SpannerAlg (G : SimpleGraph V) (w : Sym2 V → ℝ≥0) (k : ℕ) (f : ℕ → ℝ) where
  /-- The spanner built on `G[S]`. -/
  run : Finset V → SimpleGraph V
  /-- It is a subgraph of `G[S]`. -/
  le : ∀ S, run S ≤ G.deleteVerts (↑S : Set V)ᶜ
  /-- Stretch `k` (for vertices of `S`). -/
  stretch : ∀ S u v, u ∈ S → v ∈ S →
    (run S).wdist w u v ≤ k * (G.deleteVerts (↑S : Set V)ᶜ).wdist w u v
  /-- Size at most `f(|S|)`. -/
  size : ∀ S, ((run S).edgeSet.ncard : ℝ) ≤ f #S

variable {G : SimpleGraph V} {w : Sym2 V → ℝ≥0} {k : ℕ} {f : ℕ → ℝ}

/-- The output of the conversion for the samples `ω i` (`i < α`): the union of the spanners built
on the surviving vertex sets. -/
def ftUnion (A : SpannerAlg G w k f) {m α : ℕ} [NeZero m] (ω : Fin α → V → Fin m) :
    SimpleGraph V :=
  ⨆ i, A.run (surv (ω i))

/-- Iteration `s` is *good* for the fault set `F` and the pair `u, v`: `u, v` survive, `F ⊆ J`. -/
def Good {m : ℕ} [NeZero m] (F : Finset V) (u v : V) (s : V → Fin m) : Prop :=
  s u = 0 ∧ s v = 0 ∧ ∀ x ∈ F, s x ≠ 0

omit [DecidableEq V] in
lemma ftUnion_le (A : SpannerAlg G w k f) {m α : ℕ} [NeZero m] (ω : Fin α → V → Fin m) :
    ftUnion A ω ≤ G :=
  iSup_le fun _ => (A.le _).trans (deleteVerts_le _ _)

/-- **Correctness of the conversion, deterministic core** (proof of Theorem 2.1). -/
theorem isWeightedVFTSpanner_ftUnion (A : SpannerAlg G w k f) (hk : 1 ≤ k) {r m α : ℕ} [NeZero m]
    (ω : Fin α → V → Fin m)
    (h : ∀ F : Finset V, #F ≤ r → ∀ u v, G.Adj u v → u ∉ F → v ∉ F → ∃ i, Good F u v (ω i)) :
    IsWeightedVFTSpanner G (ftUnion A ω) w r k := by
  refine isWeightedVFTSpanner_of_adj hk (ftUnion_le A ω) fun F hF u v huv hu hv => ?_
  obtain ⟨i, hui, hvi, hFi⟩ := h F hF u v huv hu hv
  set S := surv (ω i)
  have huS : u ∈ S := by simp [S, surv, hui]
  have hvS : v ∉ (↑S : Set V)ᶜ := by simp [S, surv, hvi]
  have hFS : ∀ x ∈ S, x ∉ F := fun x hx hxF => hFi x hxF (by simpa [S, surv] using hx)
  -- `run S ≤ H \ F`
  have hle : A.run S ≤ (ftUnion A ω).deleteVerts F := by
    intro x y hxy
    have hxy' := A.le S hxy
    refine ⟨(le_iSup (fun j => A.run (surv (ω j))) i) hxy, ?_, ?_⟩
    · exact hFS x (by simpa using hxy'.2.1)
    · exact hFS y (by simpa using hxy'.2.2)
  calc ((ftUnion A ω).deleteVerts F).wdist w u v ≤ (A.run S).wdist w u v := wdist_anti hle
    _ ≤ k * (G.deleteVerts (↑S : Set V)ᶜ).wdist w u v :=
        A.stretch S u v huS (by simpa [S, surv] using hvi)
    _ ≤ k * w s(u, v) := by
        gcongr
        exact wdist_le_of_adj ⟨huv, by simpa using huS, hvS⟩

/-! ### Probability of a good iteration -/

lemma uprob_eq_zero_fin (m : ℕ) [NeZero m] : uprob (fun a : Fin m => a = 0) = 1 / m := by
  classical
  rw [uprob_eq_card_filter, filter_eq' univ (0 : Fin m)]
  simp

lemma uprob_true_of_nonempty {X : Type*} [Fintype X] [Nonempty X] :
    uprob (fun _ : X => True) = 1 := by
  rw [uprob_true]; simp [Fintype.card_ne_zero]

/-- **Probability of a good iteration**: `(1/m)² (1 - 1/m)^{|F|}`. -/
theorem uprob_good (m : ℕ) [NeZero m] (F : Finset V) {u v : V} (huv : u ≠ v) (hu : u ∉ F)
    (hv : v ∉ F) :
    uprob (Good (m := m) F u v) = (1 / (m : ℝ)) ^ 2 * (1 - 1 / (m : ℝ)) ^ #F := by
  classical
  let P : V → Fin m → Prop := fun x a =>
    if x = u ∨ x = v then a = 0 else if x ∈ F then a ≠ 0 else True
  have hP : Good (m := m) F u v = fun s => ∀ x, P x (s x) := by
    ext s
    constructor
    · rintro ⟨h1, h2, h3⟩ x
      simp only [P]
      split_ifs with hx hxF
      · rcases hx with rfl | rfl <;> assumption
      · exact h3 x hxF
    · intro h
      refine ⟨by simpa [P] using h u, by simpa [P] using h v, fun x hx => ?_⟩
      have hxu : x ≠ u := fun h' => hu (h' ▸ hx)
      have hxv : x ≠ v := fun h' => hv (h' ▸ hx)
      simpa [P, hxu, hxv, hx] using h x
  rw [hP, uprob_pi]
  have hcoord : ∀ x, uprob (P x) =
      if x = u ∨ x = v then 1 / (m : ℝ) else if x ∈ F then 1 - 1 / (m : ℝ) else 1 := by
    intro x
    simp only [P]
    split_ifs
    · exact uprob_eq_zero_fin m
    · rw [uprob_not, uprob_eq_zero_fin]
    · exact uprob_true_of_nonempty
  simp_rw [hcoord]
  rw [prod_ite, prod_const, prod_ite, prod_const, prod_const_one, mul_one]
  have h1 : (univ.filter fun x => x = u ∨ x = v) = {u, v} := by ext x; simp
  have h2 : ((univ.filter fun x => ¬ (x = u ∨ x = v)).filter fun x => x ∈ F) = F := by
    ext x
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    rintro hx (rfl | rfl)
    · exact hu hx
    · exact hv hx
  rw [h1, h2, card_pair huv]

/-! ### Union bound -/

/-- Marginals of the uniform distribution on a product. -/
lemma uprob_coord {ι X : Type*} [Fintype ι] [DecidableEq ι] [Fintype X] [Nonempty X] (i : ι)
    (P : X → Prop) : uprob (fun ω : ι → X => P (ω i)) = uprob P := by
  classical
  have := uprob_pi (ι := ι) (α := fun _ => X) (fun j => if j = i then P else fun _ => True)
  have h : (fun ω : ι → X => ∀ j, (if j = i then P else fun _ => True) (ω j)) =
      fun ω => P (ω i) := by
    ext ω
    constructor
    · intro h; simpa using h i
    · intro h j; split_ifs with hj
      · exact hj ▸ h
      · trivial
  rw [h] at this
  rw [this, Finset.prod_eq_single i]
  · simp
  · intro j _ hj; simp [hj, uprob_true_of_nonempty]
  · simp

/-- **Correctness with high probability** (Theorem 2.1, union bound over fault sets and edges):
`Pr[H is not an r-FT k-spanner] ≤ (n+1)^r · n² · (1 - (1/m)² (1 - 1/m)^r)^α`. -/
theorem uprob_not_isVFT_le (A : SpannerAlg G w k f) (hk : 1 ≤ k) (r m α : ℕ) [NeZero m] :
    uprob (fun ω : Fin α → V → Fin m => ¬ IsWeightedVFTSpanner G (ftUnion A ω) w r k) ≤
      ((Fintype.card V : ℝ) + 1) ^ r * (Fintype.card V : ℝ) ^ 2 *
        (1 - (1 / (m : ℝ)) ^ 2 * (1 - 1 / (m : ℝ)) ^ r) ^ α := by
  classical
  set n := Fintype.card V
  set q := (1 / (m : ℝ)) ^ 2 * (1 - 1 / (m : ℝ)) ^ r
  set FS := univ.filter fun F : Finset V => #F ≤ r
  let Bad : Finset V → V × V → (Fin α → V → Fin m) → Prop := fun F p ω =>
    G.Adj p.1 p.2 ∧ p.1 ∉ F ∧ p.2 ∉ F ∧ ∀ i, ¬ Good F p.1 p.2 (ω i)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)
  have hinv : 1 / (m : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hm1
  have h0 : 0 ≤ 1 / (m : ℝ) := by positivity
  have hq1 : q ≤ 1 := by
    have a : (1 / (m : ℝ)) ^ 2 ≤ 1 := pow_le_one₀ h0 hinv
    have b : (1 - 1 / (m : ℝ)) ^ r ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have c : 0 ≤ (1 - 1 / (m : ℝ)) ^ r := pow_nonneg (by linarith) _
    calc q = (1 / (m : ℝ)) ^ 2 * (1 - 1 / (m : ℝ)) ^ r := rfl
      _ ≤ 1 * 1 := mul_le_mul a b c zero_le_one
      _ = 1 := one_mul 1
  -- each bad event has probability at most `(1 - q)^α`
  have hbad : ∀ F ∈ FS, ∀ p ∈ (univ : Finset (V × V)), uprob (Bad F p) ≤ (1 - q) ^ α := by
    intro F hF p _
    by_cases hc : G.Adj p.1 p.2 ∧ p.1 ∉ F ∧ p.2 ∉ F
    · obtain ⟨hadj, hu, hv⟩ := hc
      calc uprob (Bad F p) ≤ uprob (fun ω : Fin α → V → Fin m =>
            ∀ i, (fun s => ¬ Good F p.1 p.2 s) (ω i)) := uprob_mono fun ω h => h.2.2.2
        _ = ∏ _i : Fin α, uprob (fun s => ¬ Good (m := m) F p.1 p.2 s) :=
            uprob_pi (fun _ s => ¬ Good F p.1 p.2 s)
        _ = (1 - uprob (Good (m := m) F p.1 p.2)) ^ α := by simp [uprob_not]
        _ ≤ (1 - q) ^ α := by
            have hg := uprob_good m F hadj.ne hu hv
            have hle : q ≤ uprob (Good (m := m) F p.1 p.2) := by
              rw [hg]
              exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by linarith) (by linarith)
                (mem_filter.mp hF).2) (by positivity)
            gcongr
            · linarith [uprob_le_one (Good (m := m) F p.1 p.2)]
    · calc uprob (Bad F p) ≤ uprob (fun _ : Fin α → V → Fin m => False) :=
            uprob_mono fun ω h => hc ⟨h.1, h.2.1, h.2.2.1⟩
        _ = 0 := uprob_false
        _ ≤ (1 - q) ^ α := pow_nonneg (by linarith) _
  -- reduce to the bad events
  have hsub : ∀ ω : Fin α → V → Fin m, ¬ IsWeightedVFTSpanner G (ftUnion A ω) w r k →
      ∃ F ∈ FS, ∃ p ∈ (univ : Finset (V × V)), Bad F p ω := by
    intro ω hω
    by_contra hcon
    apply hω
    refine isWeightedVFTSpanner_ftUnion A hk ω fun F hF u v huv hu hv => ?_
    by_contra hno
    push Not at hno
    exact hcon ⟨F, mem_filter.mpr ⟨mem_univ _, hF⟩, (u, v), mem_univ _, huv, hu, hv, hno⟩
  calc _ ≤ uprob (fun ω : Fin α → V → Fin m => ∃ F ∈ FS, ∃ p ∈ (univ : Finset (V × V)),
        Bad F p ω) := uprob_mono hsub
    _ ≤ ∑ F ∈ FS, uprob (fun ω => ∃ p ∈ (univ : Finset (V × V)), Bad F p ω) :=
        uprob_exists_le _ _
    _ ≤ ∑ F ∈ FS, ∑ p ∈ (univ : Finset (V × V)), uprob (Bad F p) :=
        sum_le_sum fun F _ => uprob_exists_le _ _
    _ ≤ ∑ F ∈ FS, ∑ p ∈ (univ : Finset (V × V)), (1 - q) ^ α :=
        sum_le_sum fun F hF => sum_le_sum fun p hp => hbad F hF p hp
    _ = (#FS : ℝ) * ((n : ℝ) ^ 2 * (1 - q) ^ α) := by
        rw [sum_const, sum_const, card_univ, Fintype.card_prod, nsmul_eq_mul, nsmul_eq_mul]
        push_cast; ring
    _ ≤ ((n : ℝ) + 1) ^ r * ((n : ℝ) ^ 2 * (1 - q) ^ α) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_faultSets_le r)
          (mul_nonneg (by positivity) (pow_nonneg (by linarith) _))
    _ = _ := by ring

/-! ### Size -/

omit [DecidableEq V] in
/-- If every iteration keeps at most `2n/m` vertices, then `|E(H)| ≤ α · f(⌊2n/m⌋)`. -/
theorem ncard_ftUnion_le (A : SpannerAlg G w k f) (hf : Monotone f) {m α : ℕ} [NeZero m]
    (ω : Fin α → V → Fin m)
    (h : ∀ i, (#(surv (ω i)) : ℝ) ≤ 2 * (Fintype.card V : ℝ) / m) :
    ((ftUnion A ω).edgeSet.ncard : ℝ) ≤ α * f ⌊2 * (Fintype.card V : ℝ) / m⌋₊ := by
  rw [ftUnion, edgeSet_iSup]
  calc ((⋃ i, (A.run (surv (ω i))).edgeSet).ncard : ℝ)
      ≤ ((∑ i, (A.run (surv (ω i))).edgeSet.ncard : ℕ) : ℝ) := by
        exact_mod_cast Set.ncard_iUnion_le_of_fintype _
    _ = ∑ i, ((A.run (surv (ω i))).edgeSet.ncard : ℝ) := by push_cast; rfl
    _ ≤ ∑ _i : Fin α, f ⌊2 * (Fintype.card V : ℝ) / m⌋₊ := by
        refine sum_le_sum fun i _ => (A.size _).trans (hf ?_)
        exact Nat.le_floor (h i)
    _ = α * f ⌊2 * (Fintype.card V : ℝ) / m⌋₊ := by simp

/-- The size condition fails with probability at most `α · e^{-n/(3m)}` (Chernoff + union bound
over the iterations). -/
theorem uprob_size_fail_le (m α : ℕ) [NeZero m] :
    uprob (fun ω : Fin α → V → Fin m =>
        ¬ ∀ i, (#(surv (ω i)) : ℝ) ≤ 2 * (Fintype.card V : ℝ) / m) ≤
      α * Real.exp (-((Fintype.card V : ℝ) / (3 * m))) := by
  calc _ ≤ uprob (fun ω : Fin α → V → Fin m => ∃ i ∈ (univ : Finset (Fin α)),
          2 * (Fintype.card V : ℝ) / m < #(surv (ω i))) :=
        uprob_mono fun ω h => by push Not at h; simpa using h
    _ ≤ ∑ i : Fin α, uprob (fun ω : Fin α → V → Fin m =>
          2 * (Fintype.card V : ℝ) / m < #(surv (ω i))) := uprob_exists_le _ _
    _ = ∑ _i : Fin α, uprob (fun s : V → Fin m => 2 * (Fintype.card V : ℝ) / m < #(surv s)) := by
        refine sum_congr rfl fun i _ => ?_
        exact uprob_coord i (fun s : V → Fin m => 2 * (Fintype.card V : ℝ) / m < #(surv s))
    _ ≤ ∑ _i : Fin α, Real.exp (-((Fintype.card V : ℝ) / (3 * m))) :=
        sum_le_sum fun _ _ => uprob_card_surv_gt_two_mul m
    _ = _ := by simp

/-- **Theorem 2.1, explicit form.** For every `m ≥ 1` and number of iterations `α`, with probability
at least `1 - (n+1)^r n² (1 - (1/m)²(1 - 1/m)^r)^α - α e^{-n/(3m)}`, the output is an `r`-fault-tolerant
`k`-spanner with at most `α · f(⌊2n/m⌋)` edges. -/
theorem conversion_explicit (A : SpannerAlg G w k f) (hk : 1 ≤ k) (hf : Monotone f)
    (r m α : ℕ) [NeZero m] :
    1 - ((Fintype.card V : ℝ) + 1) ^ r * (Fintype.card V : ℝ) ^ 2 *
          (1 - (1 / (m : ℝ)) ^ 2 * (1 - 1 / (m : ℝ)) ^ r) ^ α -
        α * Real.exp (-((Fintype.card V : ℝ) / (3 * m))) ≤
      uprob (fun ω : Fin α → V → Fin m => IsWeightedVFTSpanner G (ftUnion A ω) w r k ∧
        ((ftUnion A ω).edgeSet.ncard : ℝ) ≤ α * f ⌊2 * (Fintype.card V : ℝ) / m⌋₊) := by
  have h1 := uprob_not_isVFT_le A hk r m α
  have h2 := uprob_size_fail_le (V := V) m α
  have h3 := one_sub_sub_le_uprob_and
    (fun ω : Fin α → V → Fin m => IsWeightedVFTSpanner G (ftUnion A ω) w r k)
    (fun ω : Fin α → V → Fin m => ∀ i, (#(surv (ω i)) : ℝ) ≤ 2 * (Fintype.card V : ℝ) / m)
  have h4 := uprob_mono (Ω := Fin α → V → Fin m)
    (E := fun ω => IsWeightedVFTSpanner G (ftUnion A ω) w r k ∧
      ∀ i, (#(surv (ω i)) : ℝ) ≤ 2 * (Fintype.card V : ℝ) / m)
    (E' := fun ω => IsWeightedVFTSpanner G (ftUnion A ω) w r k ∧
      ((ftUnion A ω).edgeSet.ncard : ℝ) ≤ α * f ⌊2 * (Fintype.card V : ℝ) / m⌋₊)
    fun ω h => ⟨h.1, ncard_ftUnion_le A hf ω h.2⟩
  linarith

end DinitzKrauthgamer
