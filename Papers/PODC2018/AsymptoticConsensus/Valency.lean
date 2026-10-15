import Mathlib
import Cslib.Computability.Distributed.DynamicNetworks.HeardOf
import Cslib.Computability.Distributed.DynamicNetworks.Chain
import Cslib.Computability.Distributed.DynamicNetworks.Product

/-!
# Asymptotic consensus, valency and contraction rate (FNS'18, Sections 2–3)

Függer, Nowak, Schwarz. *Tight Bounds for Asymptotic and Approximate Consensus.* PODC 2018.

* `Alg`: a deterministic full-information round-based algorithm (initial state from the
  agent's identity and initial value, transition function, output `y`).
* `Alg.Solves A N`: `A` solves asymptotic consensus in the network model `N`
  (Convergence + Agreement + Validity, Section 2.1).
* `Alg.val A Q C`: the set of limits reachable from configuration `C` under patterns in `Q`;
  `Alg.paperVal A N C` is the paper's valency `Y*_N(C)` and agrees with `val` on reachable
  configurations (`val_eq_paperVal`).
* `Alg.δ A N C = diam Y*_N(C)` (an extended real), `Alg.rate A N` the contraction rate.
* Lemma 3 (`Solves.mono`, `val_mono`, `δ_mono`, `rate_mono`), Lemma 4 (`val_eq_iUnion`),
  Lemma 5 (`exists_δ_eq_union`), Lemma 7 (`val_inter_nonempty_lemma7`), Lemma 8 (`δ_initC`,
  `exists_δ_initC_pos`), and the necessity of rootedness (`Solves.exists_root`, from [8]).
-/

set_option linter.unusedSectionVars false

namespace AsymptoticConsensus

open Cslib.HeardOf Filter Topology Set
open scoped ENNReal

variable {α σ V : Type*}

/-- A deterministic full-information algorithm: `init i v` is the initial state of agent `i` with
initial value `v`, `step` the transition function, `out s` the output variable `y` of state `s`. -/
structure Alg (α σ V : Type*) where
  init : α → V → σ
  step : StepFn α σ
  out : σ → V

namespace Alg

variable [NormedAddCommGroup V] [NormedSpace ℝ V] (A : Alg α σ V)

/-- The initial configuration with initial values `x`. -/
def initC (x : α → V) : α → σ := fun i => A.init i (x i)

/-- All outputs converge to `z` in the run from `C` with pattern `p`. -/
def HasLimit (C : α → σ) (p : ℕ → Graph α) (z : V) : Prop :=
  ∀ i, Tendsto (fun t => A.out (conf A.step C p t i)) atTop (𝓝 z)

/-- `A` solves asymptotic consensus in the network model `N`: in every execution all outputs
converge to a common limit in the convex hull of the initial values. -/
def Solves (N : Set (Graph α)) : Prop :=
  ∀ x : α → V, ∀ p ∈ Pat N, ∃ z ∈ convexHull ℝ (range x), A.HasLimit (A.initC x) p z

/-- `C` is reachable by `A` in `N`. -/
def Reach (N : Set (Graph α)) (C : α → σ) : Prop :=
  ∃ x : α → V, ∃ p ∈ Pat N, ∃ t, conf A.step (A.initC x) p t = C

/-- The limits reachable from `C` with patterns in `Q` (history-free valency). -/
def val (Q : Set (ℕ → Graph α)) (C : α → σ) : Set V := {z | ∃ q ∈ Q, A.HasLimit C q z}

/-- The valency `Y*_N(C)` of the paper: limits of executions in which `C` occurs. -/
def paperVal (N : Set (Graph α)) (C : α → σ) : Set V :=
  {z | ∃ x : α → V, ∃ p ∈ Pat N, ∃ t, conf A.step (A.initC x) p t = C ∧
    A.HasLimit (A.initC x) p z}

/-- `δ_N(C) = diam Y*_N(C)` (extended reals: the paper's `sup ‖x - y‖`). -/
noncomputable def δ (N : Set (Graph α)) (C : α → σ) : ℝ≥0∞ := Metric.ediam (A.val (Pat N) C)

/-- The contraction rate `sup_E limsup_t δ_N(C_t)^{1/t}`. -/
noncomputable def rate (N : Set (Graph α)) : ℝ≥0∞ :=
  ⨆ x : α → V, ⨆ p ∈ Pat N,
    limsup (fun t : ℕ => A.δ N (conf A.step (A.initC x) p t) ^ ((t : ℝ)⁻¹)) atTop

variable {A}

/-! ### Limits along shifted runs -/

theorem hasLimit_shift {C : α → σ} {p : ℕ → Graph α} {z : V} (t : ℕ) :
    A.HasLimit (conf A.step C p t) (shift t p) z ↔ A.HasLimit C p z := by
  unfold HasLimit
  refine forall_congr' fun i => ?_
  simp_rw [← conf_add]
  have := tendsto_add_atTop_iff_nat (f := fun n => A.out (conf A.step C p n i)) (l := 𝓝 z) t
  simpa only [add_comm _ t] using this

theorem hasLimit_splice {C : α → σ} {p q : ℕ → Graph α} {z : V} (t : ℕ) :
    A.HasLimit C (splice p t q) z ↔ A.HasLimit (conf A.step C p t) q z := by
  rw [← hasLimit_shift (p := splice p t q) t, conf_splice_le C p q le_rfl]
  have : shift t (splice p t q) = q := by funext k; simp [shift, splice]
  rw [this]

theorem hasLimit_pcons {C : α → σ} {G : Graph α} {q : ℕ → Graph α} {z : V} :
    A.HasLimit C (pcons G q) z ↔ A.HasLimit (next A.step G C) q z := by
  rw [← hasLimit_shift (p := pcons G q) 1]
  have : shift 1 (pcons G q) = q := by funext k; rw [shift, add_comm]; rfl
  rw [this]; rfl

theorem HasLimit.unique [Nonempty α] {C : α → σ} {p : ℕ → Graph α} {z z' : V}
    (h : A.HasLimit C p z) (h' : A.HasLimit C p z') : z = z' :=
  tendsto_nhds_unique (h (Classical.arbitrary α)) (h' (Classical.arbitrary α))

/-- Two runs in which some agent `i` has the same states have the same limit. -/
theorem HasLimit.eq_of_agent {C C' : α → σ} {p p' : ℕ → Graph α} {z z' : V} (i : α)
    (h : A.HasLimit C p z) (h' : A.HasLimit C' p' z')
    (hi : ∀ t, conf A.step C p t i = conf A.step C' p' t i) : z = z' := by
  have := h' i
  simp_rw [← hi] at this
  exact tendsto_nhds_unique (h i) this

/-! ### Reachability -/

theorem Reach.initC {N : Set (Graph α)} (hN : N.Nonempty) (x : α → V) :
    A.Reach N (A.initC x) := by
  obtain ⟨G, hG⟩ := hN
  exact ⟨x, fun _ => G, fun _ => hG, 0, rfl⟩

theorem Reach.conf {N : Set (Graph α)} {C : α → σ} (hC : A.Reach N C) {q : ℕ → Graph α}
    (hq : q ∈ Pat N) (s : ℕ) : A.Reach N (conf A.step C q s) := by
  obtain ⟨x, p, hp, t, rfl⟩ := hC
  exact ⟨x, splice p t q, splice_mem_pat hp hq t, t + s, conf_splice _ _ _ _ _⟩

theorem Reach.next {N : Set (Graph α)} {C : α → σ} (hC : A.Reach N C) {G : Graph α}
    (hG : G ∈ N) : A.Reach N (next A.step G C) :=
  hC.conf (q := fun _ => G) (const_mem_pat hG) 1

/-- From a reachable configuration every continuation converges. -/
theorem Solves.exists_limit {N : Set (Graph α)} (hA : A.Solves N) {C : α → σ}
    (hC : A.Reach N C) {q : ℕ → Graph α} (hq : q ∈ Pat N) : ∃ z, A.HasLimit C q z := by
  obtain ⟨x, p, hp, t, rfl⟩ := hC
  obtain ⟨z, -, hz⟩ := hA x (splice p t q) (splice_mem_pat hp hq t)
  exact ⟨z, (hasLimit_splice t).1 hz⟩

/-- Validity from a reachable configuration: its valency lies in the hull of the initial values
of any execution reaching it. -/
theorem Solves.val_subset_hull [Nonempty α] {N : Set (Graph α)} (hA : A.Solves N) {x : α → V}
    {p : ℕ → Graph α} (hp : p ∈ Pat N) (t : ℕ) :
    A.val (Pat N) (conf A.step (A.initC x) p t) ⊆ convexHull ℝ (range x) := by
  rintro z ⟨q, hq, hz⟩
  obtain ⟨z', hz', hlim⟩ := hA x (splice p t q) (splice_mem_pat hp hq t)
  rw [← (hasLimit_splice t).2 hz |>.unique hlim] at hz'
  exact hz'

theorem Solves.val_initC_subset_hull [Nonempty α] {N : Set (Graph α)} (hA : A.Solves N)
    (hN : N.Nonempty) (x : α → V) : A.val (Pat N) (A.initC x) ⊆ convexHull ℝ (range x) := by
  obtain ⟨G, hG⟩ := hN
  exact hA.val_subset_hull (p := fun _ => G) (fun _ => hG) 0

theorem Solves.val_nonempty {N : Set (Graph α)} (hA : A.Solves N) (hN : N.Nonempty)
    {C : α → σ} (hC : A.Reach N C) : (A.val (Pat N) C).Nonempty := by
  obtain ⟨G, hG⟩ := hN
  obtain ⟨z, hz⟩ := hA.exists_limit hC (q := fun _ => G) (const_mem_pat hG)
  exact ⟨z, _, const_mem_pat hG, hz⟩

/-- The history-free valency coincides with the paper's valency on reachable configurations. -/
theorem val_eq_paperVal {N : Set (Graph α)} {C : α → σ} (hC : A.Reach N C) :
    A.val (Pat N) C = A.paperVal N C := by
  ext z
  constructor
  · rintro ⟨q, hq, hz⟩
    obtain ⟨x, p, hp, t, rfl⟩ := hC
    exact ⟨x, splice p t q, splice_mem_pat hp hq t, t, conf_splice_le _ _ _ le_rfl,
      (hasLimit_splice t).2 hz⟩
  · rintro ⟨x, p, hp, t, rfl, hz⟩
    exact ⟨shift t p, shift_mem_pat hp t, (hasLimit_shift t).2 hz⟩

/-! ### Lemma 3 -/

theorem val_mono {Q Q' : Set (ℕ → Graph α)} (h : Q' ⊆ Q) (C : α → σ) :
    A.val Q' C ⊆ A.val Q C := fun _ ⟨q, hq, hz⟩ => ⟨q, h hq, hz⟩

/-- **Lemma 3 (i)**. -/
theorem Solves.mono {N N' : Set (Graph α)} (hA : A.Solves N) (h : N' ⊆ N) : A.Solves N' :=
  fun x p hp => hA x p (pat_mono h hp)

/-- **Lemma 3 (ii)**. -/
theorem paperVal_mono {N N' : Set (Graph α)} (h : N' ⊆ N) (C : α → σ) :
    A.paperVal N' C ⊆ A.paperVal N C := fun _ ⟨x, p, hp, t, hC, hz⟩ =>
  ⟨x, p, pat_mono h hp, t, hC, hz⟩

/-- **Lemma 3 (iii)**. -/
theorem δ_mono {N N' : Set (Graph α)} (h : N' ⊆ N) (C : α → σ) : A.δ N' C ≤ A.δ N C :=
  Metric.ediam_mono (val_mono (pat_mono h) C)

/-- **Lemma 3 (iv)**. -/
theorem rate_mono {N N' : Set (Graph α)} (h : N' ⊆ N) : A.rate N' ≤ A.rate N := by
  refine iSup_mono fun x => iSup₂_le fun p hp => ?_
  refine le_iSup₂_of_le (f := fun p (_ : p ∈ Pat N) => limsup (fun t : ℕ =>
    A.δ N (conf A.step (A.initC x) p t) ^ ((t : ℝ)⁻¹)) atTop) p (pat_mono h hp) ?_
  refine limsup_le_limsup (Eventually.of_forall fun t => ?_)
  exact ENNReal.rpow_le_rpow (δ_mono h _) (by positivity)

/-! ### Lemma 4 -/

/-- **Lemma 4**: `Y*(C) = ⋃_{G ∈ N} Y*(G.C)`. -/
theorem val_eq_iUnion (N : Set (Graph α)) (C : α → σ) :
    A.val (Pat N) C = ⋃ G ∈ N, A.val (Pat N) (next A.step G C) := by
  ext z
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨q, hq, hz⟩
    refine ⟨q 0, hq 0, shift 1 q, shift_mem_pat hq 1, ?_⟩
    exact (hasLimit_shift (p := q) 1).2 hz
  · rintro ⟨G, hG, q, hq, hz⟩
    exact ⟨pcons G q, pcons_mem_pat hG hq, hasLimit_pcons.2 hz⟩

theorem val_next_subset {N : Set (Graph α)} {G : Graph α} (hG : G ∈ N) (C : α → σ) :
    A.val (Pat N) (next A.step G C) ⊆ A.val (Pat N) C := by
  rw [val_eq_iUnion N C]; exact subset_biUnion_of_mem (u := fun G => A.val (Pat N) (next A.step G C)) hG

theorem val_conf_subset {N : Set (Graph α)} {p : ℕ → Graph α} (hp : p ∈ Pat N) (C : α → σ) :
    ∀ t, A.val (Pat N) (conf A.step C p t) ⊆ A.val (Pat N) C := by
  intro t
  induction t with
  | zero => exact subset_rfl
  | succ t ih => exact (val_next_subset (hp t) _).trans ih

theorem δ_conf_antitone {N : Set (Graph α)} {p : ℕ → Graph α} (hp : p ∈ Pat N) (C : α → σ)
    {s t : ℕ} (hst : s ≤ t) : A.δ N (conf A.step C p t) ≤ A.δ N (conf A.step C p s) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [conf_add]
  exact Metric.ediam_mono (val_conf_subset (shift_mem_pat hp s) _ k)

/-! ### Lemma 5 -/

/-- **Lemma 5**: for a finite network model the valency diameter is attained by two successors. -/
theorem exists_δ_eq_union {N : Set (Graph α)} (hfin : N.Finite) (hN : N.Nonempty)
    (C : α → σ) : ∃ G ∈ N, ∃ H ∈ N, A.δ N C =
      Metric.ediam (A.val (Pat N) (next A.step G C) ∪ A.val (Pat N) (next A.step H C)) := by
  obtain ⟨G, hG, H, hH, h⟩ := Cslib.HeardOf.Chain.exists_ediam_eq_union hfin.toFinset
    (by simpa using hN) (fun G => A.val (Pat N) (next A.step G C))
  refine ⟨G, by simpa using hG, H, by simpa using hH, ?_⟩
  rw [← h, δ, val_eq_iUnion N C]
  simp

/-! ### Lemma 7 and its generalization -/

/-- If two reachable configurations agree on a nonempty set `S` of agents that is closed under
in-neighbours in some graph `K` (with `K^ω ∈ Q ⊆ Pat N`), their `Q`-valencies intersect (run `K`
forever from both). -/
theorem val_inter_nonempty_of_closed {N : Set (Graph α)} (hA : A.Solves N)
    {Q : Set (ℕ → Graph α)} (hQ : Q ⊆ Pat N) {K : Graph α} (hK : (fun _ => K) ∈ Q)
    {S : Set α} (hS : S.Nonempty) (hcl : ∀ i ∈ S, ∀ j, Hears K i j → j ∈ S)
    {C C' : α → σ} (hC : A.Reach N C) (hC' : A.Reach N C') (hag : ∀ i ∈ S, C i = C' i) :
    (A.val Q C ∩ A.val Q C').Nonempty := by
  obtain ⟨z, hz⟩ := hA.exists_limit hC (hQ hK)
  obtain ⟨z', hz'⟩ := hA.exists_limit hC' (hQ hK)
  obtain ⟨i, hi⟩ := hS
  have hrun := conf_agree (step := A.step) S (p := fun _ => K) (p' := fun _ => K)
    (fun _ i _ => SameIn.refl K i) (fun _ => hcl) hag
  have : z = z' := hz.eq_of_agent i hz' fun t => hrun t i hi
  subst this
  exact ⟨z, ⟨_, hK, hz⟩, ⟨_, hK, hz'⟩⟩

/-- Deaf version: reachable configurations in which `i` has the same state have intersecting
`Q`-valencies if `Q` contains `Dᵢ^ω` with `i` deaf in `Dᵢ`. -/
theorem val_inter_nonempty_of_deaf {N : Set (Graph α)} (hA : A.Solves N)
    {Q : Set (ℕ → Graph α)} (hQ : Q ⊆ Pat N) {Di : Graph α} (hD : (fun _ => Di) ∈ Q) {i : α}
    (hdeaf : Deaf Di i) {C C' : α → σ} (hC : A.Reach N C) (hC' : A.Reach N C')
    (hag : C i = C' i) : (A.val Q C ∩ A.val Q C').Nonempty :=
  val_inter_nonempty_of_closed hA hQ hD (S := {i}) (singleton_nonempty i)
    (fun k hk j hj => by rw [mem_singleton_iff] at hk ⊢; subst hk; exact hdeaf.eq hj) hC hC'
    (fun k hk => by rw [mem_singleton_iff] at hk; subst hk; exact hag)

/-- **Lemma 7.** If `i` has the same in-neighbours in `G, G' ∈ N`, its in-neighbours are in the
same state in `C` and `C'`, and some graph of `N` makes `i` deaf, then
`Y*(G.C) ∩ Y*(G'.C') ≠ ∅`. -/
theorem val_inter_nonempty_lemma7 {N : Set (Graph α)} (hA : A.Solves N) {G G' Di : Graph α}
    (hG : G ∈ N) (hG' : G' ∈ N) (hD : Di ∈ N) {i : α} (hdeaf : Deaf Di i) (hin : SameIn G G' i)
    {C C' : α → σ} (hC : A.Reach N C) (hC' : A.Reach N C')
    (hag : ∀ j, Hears G i j → C j = C' j) :
    (A.val (Pat N) (next A.step G C) ∩ A.val (Pat N) (next A.step G' C')).Nonempty :=
  val_inter_nonempty_of_deaf hA subset_rfl (const_mem_pat hD) hdeaf (hC.next hG) (hC'.next hG')
    (next_eq_of_agree hin hag)

/-! ### Lemma 8 -/

/-- Constant initial values force the limit. -/
theorem Solves.hasLimit_const {N : Set (Graph α)} (hA : A.Solves N) [Nonempty α] (v : V)
    {p : ℕ → Graph α} (hp : p ∈ Pat N) {z : V} (hz : A.HasLimit (A.initC fun _ => v) p z) :
    z = v := by
  obtain ⟨z', hz', hlim⟩ := hA (fun _ => v) p hp
  rw [range_const, convexHull_singleton, mem_singleton_iff] at hz'
  rw [hz.unique hlim, hz']

/-- If `i` is deaf throughout a pattern `q` of `Q ⊆ Pat N`, then `x i` is a reachable limit from
`initC x` (half of Lemma 8 and of Lemma 13). -/
theorem Solves.mem_val_of_deaf {N : Set (Graph α)} (hA : A.Solves N)
    {Q : Set (ℕ → Graph α)} (hQ : Q ⊆ Pat N) {q : ℕ → Graph α} (hq : q ∈ Q) {i : α}
    (hdeaf : ∀ t, Deaf (q t) i) (x : α → V) : x i ∈ A.val Q (A.initC x) := by
  have : Nonempty α := ⟨i⟩
  obtain ⟨z, -, hz⟩ := hA x q (hQ hq)
  obtain ⟨z', -, hz'⟩ := hA (fun _ => x i) q (hQ hq)
  have h1 : z = z' := hz.eq_of_agent i hz' (conf_agree_deaf hdeaf hdeaf rfl)
  have h2 : z' = x i := hA.hasLimit_const (x i) (hQ hq) hz'
  refine ⟨q, hq, ?_⟩
  rw [← h2, ← h1]; exact hz

/-- **Lemma 8.** If every agent is deaf in some graph of `N`, then `δ_N(C₀) = Δ(y(0))`. -/
theorem δ_initC [Nonempty α] {N : Set (Graph α)} (hA : A.Solves N) (hdeaf : ∀ i, ∃ D ∈ N, Deaf D i)
    (x : α → V) : A.δ N (A.initC x) = Metric.ediam (range x) := by
  obtain ⟨D, hD, -⟩ := hdeaf (Classical.arbitrary α)
  refine le_antisymm ?_ (Metric.ediam_mono ?_)
  · rw [← convexHull_ediam]
    exact Metric.ediam_mono (hA.val_initC_subset_hull ⟨D, hD⟩ x)
  · rintro _ ⟨i, rfl⟩
    obtain ⟨Di, hDi, hi⟩ := hdeaf i
    exact hA.mem_val_of_deaf subset_rfl (const_mem_pat hDi) (fun _ => hi) x

/-- **Lemma 8**, second part: some initial configuration has positive valency diameter. -/
theorem exists_δ_initC_pos [Nontrivial V] {N : Set (Graph α)} (hA : A.Solves N)
    (hdeaf : ∀ i, ∃ D ∈ N, Deaf D i) {i j : α} (hij : i ≠ j) :
    ∃ x : α → V, 0 < A.δ N (A.initC x) := by
  classical
  have : Nonempty α := ⟨i⟩
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  refine ⟨fun k => if k = i then v else w, ?_⟩
  rw [δ_initC hA hdeaf, Metric.ediam_pos_iff']
  exact ⟨v, ⟨i, by simp⟩, w, ⟨j, by simp [hij.symm]⟩, hvw⟩

/-! ### Rootedness is necessary ([8, Theorem 1], necessity) -/

/-- If `A` solves asymptotic consensus in `N` (and `V` is nontrivial), every graph of `N` is
rooted. -/
theorem Solves.exists_root [Nontrivial V] [Finite α] [Nonempty α] {N : Set (Graph α)}
    (hA : A.Solves N) {G : Graph α} (hG : G ∈ N) : ∃ r, Cslib.DynNet.IsRoot G r := by
  classical
  have := Fintype.ofFinite α
  by_contra hno
  push Not at hno
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
  obtain ⟨v, w, hvw⟩ := exists_pair_ne V
  let x : α → V := fun j => if j ∈ S2 then w else v
  obtain ⟨z, -, hz⟩ := hA x (fun _ => G) (const_mem_pat hG)
  -- agents of `S1` behave as in the all-`v` execution, agents of `S2` as in the all-`w` one
  have key : ∀ (S : Set α) (u : V), (∀ k ∈ S, x k = u) →
      (∀ k ∈ S, ∀ j, Hears G k j → j ∈ S) → ∀ k ∈ S, z = u := by
    intro S u hxS hcl k hk
    obtain ⟨z', -, hz'⟩ := hA (fun _ => u) (fun _ => G) (const_mem_pat hG)
    have hrun := conf_agree (step := A.step) S (C := A.initC x) (C' := A.initC fun _ => u)
      (p := fun _ => G) (p' := fun _ => G) (fun _ k _ => SameIn.refl G k) (fun _ => hcl)
      (fun k hk => by simp [initC, hxS k hk])
    rw [hz.eq_of_agent k hz' fun t => hrun t k hk]
    exact hA.hasLimit_const u (const_mem_pat hG) hz'
  have h1 : z = v := key S1 v (fun k hk => by simp [x, hdisj k hk])
    (fun k hk j hj => by
      rcases hj with rfl | hj
      · exact hk
      · exact Relation.ReflTransGen.head hj hk) i Relation.ReflTransGen.refl
  have h2 : z = w := key S2 w (fun k hk => by simp [x, hk])
    (fun k hk j hj => by
      rcases hj with rfl | hj
      · exact hk
      · exact fun hij => hk (hij.tail hj)) y hy
  exact hvw (h1.symm.trans h2)

/-! ### From explicit executions to the contraction rate -/

/-- If along some execution `a · r^t ≤ δ_N(C_t)` with `0 < a < ∞`, the contraction rate is at
least `r`. -/
theorem le_rate {N : Set (Graph α)} (x : α → V) {p : ℕ → Graph α} (hp : p ∈ Pat N)
    {a r : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ∞)
    (h : ∀ t, a * r ^ t ≤ A.δ N (conf A.step (A.initC x) p t)) : r ≤ A.rate N :=
  (Cslib.HeardOf.Chain.le_limsup_rpow_inv ha ha' h).trans
    (le_iSup_of_le x (le_iSup₂_of_le (f := fun p (_ : p ∈ Pat N) => limsup (fun t : ℕ =>
      A.δ N (conf A.step (A.initC x) p t) ^ ((t : ℝ)⁻¹)) atTop) p hp le_rfl))

end Alg

end AsymptoticConsensus
