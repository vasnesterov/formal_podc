import Papers.PODC2018.AsymptoticConsensus.Alpha

/-!
# Exact consensus and valencies (Section 7 of FNS'18)

* `EAlg`, `EAlg.Solves` (exact consensus: termination, irrevocability, agreement, validity),
  `ExactSolvable α V N`.
* `toAsym`: the asymptotic consensus algorithm derived from an exact one (proof of Theorem 4 ⇒):
  output the initial value until deciding, then the decision.
* **Theorem 4 (⇒)** (`theorem4_mp`): if exact consensus is solvable, some asymptotic consensus
  algorithm has only singleton or disconnected valencies (`ValencyProp`).
* `rate_toAsym`: ... and it has contraction rate `0` (the paper's remark in the introduction).
* Consequences of the lower bounds for exact consensus: `not_exactSolvable_N3` (two agents with
  `H0, H1, H2`), `not_exactSolvable_deaf` (`n ≥ 3`, `deaf(G)`).
* Flooding (`exactSolvable_of_common_root`): a common root of all graphs makes exact consensus
  solvable. Hence `sourceIncompatible_of_not_exactSolvable`, and Theorem 5 / Corollary 23 / Lemma
  21 in the paper's form, with hypothesis "exact consensus is not solvable" (`theorem5_paper`).
-/

set_option linter.unusedSectionVars false

namespace AsymptoticConsensus

open Cslib.HeardOf Cslib.HeardOf.Chain Filter Topology Set Classical
open Cslib.DynNet (IsRoot)
open scoped ENNReal

variable {α σ : Type*} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- An exact consensus algorithm: initial states, transition function, decision variable. -/
structure EAlg (α σ V : Type*) where
  init : α → V → σ
  step : StepFn α σ
  dec : σ → Option V

namespace EAlg

/-- Initial configuration. -/
def initC (B : EAlg α σ V) (x : α → V) : α → σ := fun i => B.init i (x i)

/-- `B` solves exact consensus in `N`: in every execution every agent decides, decisions are
irrevocable, agree, and are initial values. -/
def Solves (B : EAlg α σ V) (N : Set (Graph α)) : Prop :=
  ∀ x : α → V, ∀ p ∈ Pat N,
    (∀ i, ∃ t v, B.dec (conf B.step (B.initC x) p t i) = some v) ∧
    (∀ i t v, B.dec (conf B.step (B.initC x) p t i) = some v →
      ∀ s, t ≤ s → B.dec (conf B.step (B.initC x) p s i) = some v) ∧
    (∀ i j t s v w, B.dec (conf B.step (B.initC x) p t i) = some v →
      B.dec (conf B.step (B.initC x) p s j) = some w → v = w) ∧
    (∀ i t v, B.dec (conf B.step (B.initC x) p t i) = some v → v ∈ range x)

theorem Solves.mono {B : EAlg α σ V} {N N' : Set (Graph α)} (h : B.Solves N) (hN : N' ⊆ N) :
    B.Solves N' := fun x p hp => h x p (pat_mono hN hp)

end EAlg

/-- Exact consensus is solvable in `N` (agents `α`, values `V`). -/
def ExactSolvable (α V : Type) [NormedAddCommGroup V] (N : Set (Graph α)) : Prop :=
  ∃ (σ : Type) (B : EAlg α σ V), B.Solves N

/-- The asymptotic consensus algorithm derived from an exact one: keep the initial value, output
the decision once decided, the initial value before. -/
noncomputable def toAsym (B : EAlg α σ V) : Alg α (σ × V) V where
  init i v := (B.init i v, v)
  step i m := (B.step i fun j => (m j).map Prod.fst, ((m i).map Prod.snd).getD 0)
  out s := (B.dec s.1).getD s.2

theorem conf_toAsym (B : EAlg α σ V) (C : α → σ) (x : α → V) (p : ℕ → Graph α) (t : ℕ) :
    conf (toAsym B).step (fun i => (C i, x i)) p t = fun i => (conf B.step C p t i, x i) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [conf_succ, ih, conf_succ]
    funext i
    simp only [next, toAsym, msgs]
    congr 1
    · congr 1; funext j; simp only [msgs]; split_ifs <;> rfl
    · simp [hears_self]

theorem initC_toAsym (B : EAlg α σ V) (x : α → V) :
    (toAsym B).initC x = fun i => (B.initC x i, x i) := rfl

/-- In every execution of an exact consensus algorithm, from some time on every agent has decided
the same initial value `v`. -/
theorem EAlg.Solves.eventually [Finite α] [Nonempty α] {B : EAlg α σ V} {N : Set (Graph α)}
    (hB : B.Solves N) (x : α → V) {p : ℕ → Graph α} (hp : p ∈ Pat N) :
    ∃ T v, v ∈ range x ∧ ∀ s, T ≤ s → ∀ i, B.dec (conf B.step (B.initC x) p s i) = some v := by
  have := Fintype.ofFinite α
  obtain ⟨hterm, hirr, hagr, hval⟩ := hB x p hp
  choose t v hv using hterm
  let i₀ := Classical.arbitrary α
  refine ⟨Finset.univ.sup t, v i₀, hval i₀ _ _ (hv i₀), fun s hs i => ?_⟩
  have := hirr i (t i) (v i) (hv i) s ((Finset.le_sup (Finset.mem_univ i)).trans hs)
  rwa [hagr i i₀ _ _ _ _ (hv i) (hv i₀)] at this

theorem toAsym_solves [Finite α] [Nonempty α] {B : EAlg α σ V} {N : Set (Graph α)}
    (hB : B.Solves N) : (toAsym B).Solves N := by
  intro x p hp
  obtain ⟨T, v, hv, hdec⟩ := hB.eventually x hp
  refine ⟨v, subset_convexHull ℝ _ hv, fun i => tendsto_atTop_of_eventually_const (i₀ := T)
    fun s hs => ?_⟩
  rw [initC_toAsym, conf_toAsym]
  simp [toAsym, hdec s hs i]

/-- Limits of the derived algorithm are initial values. -/
theorem toAsym_limit_mem [Finite α] [Nonempty α] {B : EAlg α σ V} {N : Set (Graph α)}
    (hB : B.Solves N) (x : α → V) {p : ℕ → Graph α} (hp : p ∈ Pat N) {z : V}
    (hz : (toAsym B).HasLimit ((toAsym B).initC x) p z) : z ∈ range x := by
  obtain ⟨T, v, hv, hdec⟩ := hB.eventually x hp
  have hlim : (toAsym B).HasLimit ((toAsym B).initC x) p v := fun i =>
    tendsto_atTop_of_eventually_const (i₀ := T) fun s hs => by
      rw [initC_toAsym, conf_toAsym]; simp [toAsym, hdec s hs i]
  rwa [hz.unique hlim]

/-- "Singleton or disconnected" valencies of all initial configurations in all submodels. -/
def ValencyProp {σ : Type*} (A : Alg α σ V) (N : Set (Graph α)) : Prop :=
  ∀ N' ⊆ N, N'.Nonempty → ∀ x : α → V,
    (∃ z, A.val (Pat N') (A.initC x) = {z}) ∨ ¬ IsPreconnected (A.val (Pat N') (A.initC x))

theorem singleton_or_not_preconnected_of_finite {S : Set V} (hfin : S.Finite)
    (hne : S.Nonempty) : (∃ z, S = {z}) ∨ ¬ IsPreconnected S := by
  by_cases h : IsPreconnected S
  · left
    obtain ⟨z, hz⟩ := hne
    exact ⟨z, ((h.isDiscrete_iff_subsingleton.1 hfin.isDiscrete).eq_singleton_of_mem hz)⟩
  · exact Or.inr h

/-- **Theorem 4 (⇒) of FNS'18.** If exact consensus is solvable in `N`, there is an asymptotic
consensus algorithm for `N` all of whose valencies `Y*_{N'}(C₀)` (`N' ⊆ N`) are singletons or
disconnected. -/
theorem theorem4_mp [Finite α] [Nonempty α] {N : Set (Graph α)} {B : EAlg α σ V}
    (hB : B.Solves N) : (toAsym B).Solves N ∧ ValencyProp (toAsym B) N := by
  refine ⟨toAsym_solves hB, fun N' hN' hne x => singleton_or_not_preconnected_of_finite
    ((finite_range x).subset ?_) ((toAsym_solves (hB.mono hN')).val_nonempty hne
      (Alg.Reach.initC hne x))⟩
  rintro z ⟨q, hq, hz⟩
  exact toAsym_limit_mem hB x (pat_mono hN' hq) hz

/-- If in every execution some valency vanishes, the contraction rate is `0`. -/
theorem rate_eq_zero_of {σ : Type*} {A : Alg α σ V} {N : Set (Graph α)}
    (h : ∀ x : α → V, ∀ p ∈ Pat N, ∃ T, A.δ N (conf A.step (A.initC x) p T) = 0) :
    A.rate N = 0 := by
  refine le_antisymm (iSup_le fun x => iSup₂_le fun p hp => ?_) bot_le
  obtain ⟨T, hT⟩ := h x p hp
  calc limsup (fun t : ℕ => A.δ N (conf A.step (A.initC x) p t) ^ ((t : ℝ)⁻¹)) atTop
      ≤ limsup (fun _ : ℕ => (0 : ℝ≥0∞)) atTop := by
        refine limsup_le_limsup ?_
        filter_upwards [eventually_ge_atTop (T + 1)] with t ht
        have h0 : A.δ N (conf A.step (A.initC x) p t) = 0 :=
          le_antisymm ((Alg.δ_conf_antitone hp _ (by omega)).trans hT.le) bot_le
        rw [h0, ENNReal.zero_rpow_of_pos (inv_pos.2 (by exact_mod_cast (by omega : 0 < t)))]
    _ ≤ 0 := by simp

/-- In every execution of the derived algorithm the valency diameter eventually vanishes: after
all agents have decided, the valency is a singleton. -/
theorem δ_toAsym_eventually_zero [Finite α] [Nonempty α] {N : Set (Graph α)} {B : EAlg α σ V}
    (hB : B.Solves N) (x : α → V) {p : ℕ → Graph α} (hp : p ∈ Pat N) :
    ∃ T, (toAsym B).δ N (conf (toAsym B).step ((toAsym B).initC x) p T) = 0 := by
  obtain ⟨T, v, -, hdec⟩ := hB.eventually x hp
  refine ⟨T, Metric.ediam_subsingleton (Set.subsingleton_of_subset_singleton (a := v) ?_)⟩
  rintro z ⟨q, hq, hz⟩
  rw [← Alg.hasLimit_splice] at hz
  -- in the spliced execution all agents have decided `v` at time `T`
  obtain ⟨-, hirr, -, -⟩ := hB x (splice p T q) (splice_mem_pat hp hq T)
  have hlim : (toAsym B).HasLimit ((toAsym B).initC x) (splice p T q) v := fun i =>
    tendsto_atTop_of_eventually_const (i₀ := T) fun s hs => by
      have hT : B.dec (conf B.step (B.initC x) (splice p T q) T i) = some v := by
        rw [conf_splice_le _ _ _ le_rfl]; exact hdec T le_rfl i
      rw [initC_toAsym, conf_toAsym]; simp [toAsym, hirr i T v hT s hs]
  exact hz.unique hlim

/-- The asymptotic algorithm derived from an exact consensus algorithm has contraction rate `0`
("if exact consensus is solvable in `N`, an optimal contraction rate of `0` can be achieved"). -/
theorem rate_toAsym [Finite α] [Nonempty α] {N : Set (Graph α)} {B : EAlg α σ V}
    (hB : B.Solves N) : (toAsym B).rate N = 0 :=
  rate_eq_zero_of fun x _ hp => δ_toAsym_eventually_zero hB x hp

/-- If exact consensus is solvable in `N`, some asymptotic consensus algorithm has rate `0`. -/
theorem exists_rate_zero_of_exactSolvable {α : Type} [Finite α] [Nonempty α]
    {N : Set (Graph α)} (h : ExactSolvable α V N) :
    ∃ (σ : Type) (A : Alg α σ V), A.Solves N ∧ A.rate N = 0 := by
  obtain ⟨σ, B, hB⟩ := h
  exact ⟨σ × V, toAsym B, toAsym_solves hB, rate_toAsym hB⟩

/-- Exact consensus is not solvable for two agents in a model containing `H₀, H₁, H₂` (via
Theorem 1). -/
theorem not_exactSolvable_N3 [Nontrivial V] {N : Set (Graph (Fin 2))}
    (hN : ({H0, H1, H2} : Set (Graph (Fin 2))) ⊆ N) : ¬ ExactSolvable (Fin 2) V N := by
  rintro h
  obtain ⟨σ, A, hA, h0⟩ := exists_rate_zero_of_exactSolvable h
  have := theorem1 A hN hA
  rw [h0] at this
  exact absurd this (by simp)

/-- Exact consensus is not solvable with `n ≥ 3` agents in a model containing three deaf graphs
`F_i` (via Theorem 2). -/
theorem not_exactSolvable_deaf [Nontrivial V] {α : Type} [Fintype α] (G : Graph α)
    (S : Finset α) (hS : 3 ≤ S.card) {N : Set (Graph α)} (hN : ∀ i ∈ S, deafG G i ∈ N) :
    ¬ ExactSolvable α V N := by
  rintro h
  have : Nonempty α := by
    obtain ⟨i, -⟩ : S.Nonempty := Finset.card_pos.1 (by omega)
    exact ⟨i⟩
  obtain ⟨σ, A, hA, h0⟩ := exists_rate_zero_of_exactSolvable h
  have := theorem2 A G S hS hN hA
  rw [h0] at this
  exact absurd this (by simp)

/-! ### Flooding: a common root makes exact consensus solvable -/

/-- Flooding of the root's value: agent `r` starts with `some x_r`, everybody adopts any value it
receives, and decides it. -/
noncomputable def flood (r : α) : EAlg α (Option V) V where
  init i v := if i = r then some v else none
  step i m := if h : ∃ j v, m j = some (some v) then some h.choose_spec.choose else none
  dec s := s

theorem flood_dec_apply (r : α) (s : Option V) : (flood r).dec s = s := rfl

theorem flood_step_eq (r : α) (i : α) (m : α → Option (Option V)) :
    (flood r).step i m = if h : ∃ j v, m j = some (some v) then some h.choose_spec.choose
      else none := rfl

theorem flood_step_cases (r i : α) (m : α → Option (Option V)) :
    (flood r).step i m = none ∨ ∃ j v, m j = some (some v) ∧ (flood r).step i m = some v := by
  rw [flood_step_eq]
  split_ifs with h
  · exact Or.inr ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec, rfl⟩
  · exact Or.inl rfl

theorem flood_inv {r : α} (x : α → V) (p : ℕ → Graph α) :
    ∀ t i, conf (flood r).step ((flood r).initC x) p t i = none ∨
      conf (flood r).step ((flood r).initC x) p t i = some (x r) := by
  intro t
  induction t with
  | zero => intro i; by_cases h : i = r <;> simp [EAlg.initC, flood, h]
  | succ t ih =>
    intro i
    rw [conf_succ]
    simp only [next]
    rcases flood_step_cases r i (msgs (p t) (conf (flood r).step ((flood r).initC x) p t) i) with
      h | ⟨j, v, hj, hstep⟩
    · exact Or.inl h
    · right
      rw [hstep]
      unfold msgs at hj
      split_ifs at hj
      · have hj' := Option.some.inj hj
        rcases ih j with h' | h'
        · exact absurd (hj'.symm.trans h') (by simp)
        · exact hj'.symm.trans h'

theorem flood_mono {r : α} (x : α → V) (p : ℕ → Graph α) {t : ℕ} {i : α} {j : α}
    (hj : Hears (p t) i j) (h : conf (flood r).step ((flood r).initC x) p t j ≠ none) :
    conf (flood r).step ((flood r).initC x) p (t + 1) i ≠ none := by
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 h
  rw [conf_succ]
  simp only [next]
  have hex : ∃ j' v', msgs (p t) (conf (flood r).step ((flood r).initC x) p t) i j' =
      some (some v') := ⟨j, v, by simp [msgs, hj, hv]⟩
  rw [flood_step_eq]
  simp [hex]

/-- **Common root ⇒ exact consensus solvable** (the easy direction of [12]). -/
theorem exactSolvable_of_common_root {α : Type} [Fintype α] {N : Set (Graph α)} {r : α}
    (hr : ∀ G ∈ N, IsRoot G r) : ExactSolvable α V N := by
  refine ⟨Option V, flood r, fun x p hp => ?_⟩
  have hinv := flood_inv (r := r) x p
  -- informed agents
  let S : ℕ → Finset α := fun t => Finset.univ.filter fun i =>
    conf (flood r).step ((flood r).initC x) p t i ≠ none
  have memS : ∀ t i, i ∈ S t ↔ conf (flood r).step ((flood r).initC x) p t i ≠ none := by
    intro t i; simp [S]
  have hS0 : r ∈ S 0 := by rw [memS]; simp [EAlg.initC, flood]
  have hSmono : ∀ t, S t ⊆ S (t + 1) := fun t i hi => by
    rw [memS] at hi ⊢; exact flood_mono x p (hears_self _ i) hi
  have hrS : ∀ t, r ∈ S t := by
    intro t; induction t with
    | zero => exact hS0
    | succ t ih => exact hSmono t ih
  have hgrow : ∀ t, min (t + 1) (Fintype.card α) ≤ (S t).card := by
    intro t
    induction t with
    | zero => exact min_le_of_left_le (Finset.card_pos.2 ⟨r, hS0⟩)
    | succ t ih =>
      by_cases hfull : (S t).card = Fintype.card α
      · have := Finset.card_le_card (hSmono t); have := Finset.card_le_univ (S (t + 1)); omega
      · obtain ⟨y, hy⟩ : ∃ y, y ∉ S t := by
          by_contra h; push Not at h
          exact hfull (by rw [Finset.eq_univ_of_forall h, Finset.card_univ])
        obtain ⟨z, w, hzw, hz, hw⟩ := Cslib.DynNet.exists_edge_cross
          (S := fun i => i ∉ S t) (hr (p t) (hp t) y) (by simpa using hrS t) hy
        have hz' : z ∈ S t := not_not.1 hz
        have hw' : w ∈ S (t + 1) := by
          rw [memS] at hz' ⊢; exact flood_mono x p (Or.inr hzw) hz'
        have hss : S t ⊂ S (t + 1) := Finset.ssubset_iff_subset_ne.2
          ⟨hSmono t, fun h => hw (h ▸ hw')⟩
        have := Finset.card_lt_card hss; omega
  have hall : ∀ i, conf (flood r).step ((flood r).initC x) p (Fintype.card α) i = some (x r) := by
    intro i
    have h1 := hgrow (Fintype.card α)
    have hS : S (Fintype.card α) = Finset.univ :=
      Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) (by omega))
    have hi : i ∈ S (Fintype.card α) := hS ▸ Finset.mem_univ i
    rw [memS] at hi
    exact (hinv _ i).resolve_left hi
  have hdec : ∀ t i v, (flood r).dec (conf (flood r).step ((flood r).initC x) p t i) = some v →
      conf (flood r).step ((flood r).initC x) p t i = some (x r) ∧ v = x r := by
    intro t i v hv
    rw [flood_dec_apply] at hv
    rcases hinv t i with h | h
    · rw [h] at hv; exact absurd hv (by simp)
    · rw [h] at hv; exact ⟨h, (Option.some.inj hv).symm⟩
  refine ⟨fun i => ⟨_, _, by rw [flood_dec_apply]; exact hall i⟩, ?_, ?_, ?_⟩
  · intro i t v hv s hs
    obtain ⟨hc, rfl⟩ := hdec t i v hv
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hs
    rw [flood_dec_apply]
    induction k with
    | zero => exact hc
    | succ k ih =>
      have := flood_mono x p (hears_self _ i) (by rw [ih (by omega)]; simp)
      rw [← add_assoc]
      exact (hinv _ i).resolve_left this
  · intro i j t s v w hv hw
    exact (hdec t i v hv).2.trans (hdec s j w hw).2.symm
  · intro i t v hv
    exact ⟨r, (hdec t i v hv).2.symm⟩

/-- If exact consensus is not solvable, `N` is source-incompatible. -/
theorem sourceIncompatible_of_not_exactSolvable {α : Type} [Fintype α] {N : Set (Graph α)}
    (h : ¬ ExactSolvable α V N) : SourceIncompatible N := by
  intro r
  by_contra hr; push Not at hr
  exact h (exactSolvable_of_common_root fun G hG => hr G hG)

/-- **Theorem 5 of FNS'18** (paper form): if exact consensus is not solvable in `N` and the
α-diameter of `N` is at most `D`, every asymptotic consensus algorithm has contraction rate at least
`1/(D+1)`. -/
theorem theorem5_paper [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) {A : Alg (Fin n) σ V}
    {N : Set (Graph (Fin n))} (hA : A.Solves N) (hN : ¬ ExactSolvable (Fin n) V N) {D : ℕ}
    (hD : AlphaDiamLE AlphaRel N D) : ((D : ℝ≥0∞) + 1)⁻¹ ≤ A.rate N :=
  Alg.theorem5 hn hA (sourceIncompatible_of_not_exactSolvable hN) hD

/-- **Lemma 21 of FNS'18** (paper form, with `1/(n-1)` instead of `1/n`). -/
theorem lemma21_paper [Nontrivial V] {n : ℕ} (hn : 2 ≤ n) {A : Alg (Fin n) σ V}
    {N : Set (Graph (Fin n))} (hA : A.Solves N) (hN : ¬ ExactSolvable (Fin n) V N) (v : V) :
    ∃ x : Fin n → V, (∀ i, x i = 0 ∨ x i = v) ∧ edist 0 v ≤ (n - 1 : ℕ) * A.δ N (A.initC x) :=
  Alg.lemma21 hn hA (sourceIncompatible_of_not_exactSolvable hN) v

/-- Conversely, by Theorem 5, exact consensus is not solvable in a source-incompatible model of
finite α-diameter. -/
theorem not_exactSolvable_of_sourceIncompatible [Nontrivial V] {n : ℕ} (hn : 2 ≤ n)
    {N : Set (Graph (Fin n))} (hSI : SourceIncompatible N) {D : ℕ}
    (hD : AlphaDiamLE AlphaRel N D) : ¬ ExactSolvable (Fin n) V N := by
  rintro h
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨σ, A, hA, h0⟩ := exists_rate_zero_of_exactSolvable h
  have := Alg.theorem5 hn hA hSI hD
  rw [h0] at this
  exact absurd this (by simp)

end AsymptoticConsensus
