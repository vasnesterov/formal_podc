import Papers.PODC2010.BayesianIgnorance.UpperBounds

/-!
# Bayesian ignorance: Lemmas 3.6 and 3.7 (existential bounds on `worst-eq^P / worst-eq^C`)

Alon, Emek, Feldman, Tennenholtz, *Bayesian Ignorance* (PODC 2010), Lemmas 3.6, 3.7 and their
appendix proofs, on the graph `G_worst` of Figure 2: an undirected triangle `u, v, w` with
`c(uv) = k + 1`, `c(vw) = 1`, `c(uw) = 1 + ε`; agents `1, …, k` (here `some j`) travel from `u`
to `w`, agent `k + 1` (here `none`) from `u` to `v` or to `u` (random).

**The appendix proofs are swapped.** The construction of the "proof of Lemma 3.6" (destination `v`
with probability `1/2`, `1/k < ε < 3/(2k)`) yields `worst-eq^P = 3/2 + ε` and
`worst-eq^C ≥ (k+2)/2`, i.e. ratio `O(1/k)` — the statement of Lemma 3.7. The construction of the
"proof of Lemma 3.7" (destination `v` with probability `1/k`, `2/k - 1/k² < ε < 2/k`) yields
`worst-eq^P ≥ k + 2` and `worst-eq^C = O(1)`, i.e. ratio `Ω(k)` — the statement of Lemma 3.6.
Both statements are true; each is proved by the other's construction.

## Main statements

* `worstConstructionA`: the exact bounds of the first construction; the key step is
  `triA_socialCost` (every Bayesian equilibrium costs exactly `3/2 + ε`, i.e. the paper's
  "unique Bayesian equilibrium" up to agent `k+1`'s irrelevant choices).
* `worstConstructionB`: the exact bounds of the second construction; the key steps are
  `triB_isBayesEq` (the profile `s` is a Bayesian equilibrium; the paper's arithmetic
  `1 + 2/k - 2/k²` should read `1 + 2/k - 1/k²`) and `triB_nash_false` (the unique Nash cost at
  destination `u` is `1 + ε`; the paper writes "(u, v)" for "(u, w)").
* `lemma_3_6`, `lemma_3_7`: the existential statements, with explicit constant `4`, for
  `n = k + 1` agents.
-/

open Finset Cslib.GameTheory Cslib.GameTheory.BayesianGame
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

namespace Podc.BayesianIgnorance

/-- The vertices `u, v, w` of the graph `G_worst` (Figure 2). -/
inductive TriV | u | v | w
  deriving DecidableEq

instance : Fintype TriV := ⟨{.u, .v, .w}, fun x => by cases x <;> simp⟩

/-- The edges `uv` (cost `k+1`), `vw` (cost `1`), `uw` (cost `1+ε`) of `G_worst`. -/
inductive TriE | uv | vw | uw
  deriving DecidableEq

instance : Fintype TriE := ⟨{.uv, .vw, .uw}, fun x => by cases x <;> simp⟩

open TriV TriE

/-- End points of the edges of `G_worst`. -/
def triEnds : TriE → Sym2 TriV
  | .uv => s(u, v)
  | .vw => s(v, w)
  | .uw => s(u, w)

/-- `F` contains an edge joining `x` and `y`. -/
def triAdj (F : Finset TriE) (x y : TriV) : Prop := ∃ e ∈ F, triEnds e = s(x, y)

instance (F : Finset TriE) (x y : TriV) : Decidable (triAdj F x y) := by
  unfold triAdj; infer_instance

/-- Explicit reachability in the triangle along edges of `F` (paths of length `≤ 2` suffice). -/
def triReach (F : Finset TriE) (x y : TriV) : Prop :=
  x = y ∨ triAdj F x y ∨ ∃ z, triAdj F x z ∧ triAdj F z y

instance (F : Finset TriE) (x y : TriV) : Decidable (triReach F x y) := by
  unfold triReach; infer_instance

lemma triReach_step : ∀ (F : Finset TriE) (x y z : TriV), triReach F x y → triAdj F y z →
    triReach F x z := by decide

/-- The network `G_worst`: an undirected triangle with `c(uv) = k+1`, `c(vw) = 1`,
`c(uw) = 1+ε`. -/
noncomputable def triNet (k : ℕ) (ε : ℝ≥0) : Network TriV TriE :=
  Network.undirected triEnds fun e => match e with
    | .uv => (k : ℝ≥0) + 1
    | .vw => 1
    | .uw => 1 + ε

variable {k : ℕ} {ε : ℝ≥0}

@[simp] lemma triNet_cost_uv : (triNet k ε).cost uv = (k : ℝ≥0) + 1 := rfl
@[simp] lemma triNet_cost_vw : (triNet k ε).cost vw = 1 := rfl
@[simp] lemma triNet_cost_uw : (triNet k ε).cost uw = 1 + ε := rfl

lemma triNet_cost_pos (e : TriE) : 0 < (triNet k ε).cost e := by
  cases e <;> simp

lemma triConnects_iff (F : Finset TriE) (x y : TriV) :
    (triNet k ε).Connects F x y ↔ triReach F x y := by
  constructor
  · intro h
    induction h with
    | refl => exact Or.inl rfl
    | tail _ hst ih => exact triReach_step F _ _ _ ih hst
  · rintro (rfl | h | ⟨z, h1, h2⟩)
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single h
    · exact Relation.ReflTransGen.head h1 (Relation.ReflTransGen.single h2)

lemma triConnects_uw (F : Finset TriE) :
    (triNet k ε).Connects F u w ↔ uw ∈ F ∨ (uv ∈ F ∧ vw ∈ F) := by
  rw [triConnects_iff]; revert F; decide

lemma triConnects_uv (F : Finset TriE) :
    (triNet k ε).Connects F u v ↔ uv ∈ F ∨ (uw ∈ F ∧ vw ∈ F) := by
  rw [triConnects_iff]; revert F; decide

lemma triReachable (x y : TriV) : (triNet k ε).Reachable x y := by
  unfold Network.Reachable; rw [triConnects_iff]; revert x y; decide

/-- The minimal `(u,w)`-connecting edge sets. -/
lemma triMin_uw : ∀ X : Finset TriE, (uw ∈ X ∨ (uv ∈ X ∧ vw ∈ X)) →
    (∀ e ∈ X, ¬ (uw ∈ X.erase e ∨ (uv ∈ X.erase e ∧ vw ∈ X.erase e))) →
    X = {uw} ∨ X = {uv, vw} := by decide

/-- The minimal `(u,v)`-connecting edge sets. -/
lemma triMin_uv : ∀ X : Finset TriE, (uv ∈ X ∨ (uw ∈ X ∧ vw ∈ X)) →
    (∀ e ∈ X, ¬ (uv ∈ X.erase e ∨ (uw ∈ X.erase e ∧ vw ∈ X.erase e))) →
    X = {uv} ∨ X = {uw, vw} := by decide

/-! ### The Bayesian game: `k` deterministic agents and one random agent -/

/-- Type profiles: agents `some j` (`j < k`, the paper's agents `1, …, k`) travel from `u` to `w`;
agent `none` (the paper's agent `k+1`) travels from `u` to `v` if `b` and from `u` to `u`
otherwise. -/
def triTypes (k : ℕ) (b : Bool) : Option (Fin k) → TriV × TriV
  | some _ => (u, w)
  | none => if b then (u, v) else (u, u)

@[simp] lemma triTypes_some (b : Bool) (j : Fin k) : triTypes k b (some j) = (u, w) := rfl
@[simp] lemma triTypes_none_true : triTypes k true none = (u, v) := rfl
@[simp] lemma triTypes_none_false : triTypes k false none = (u, u) := rfl

/-- The distribution of the coin `b`: `true` with probability `qt`, `false` with probability
`qf`. -/
noncomputable def triBool (qt qf : ℝ≥0) (h : qt + qf = 1) : PMF Bool :=
  PMF.ofFintype (fun b => ((cond b qt qf : ℝ≥0) : ℝ≥0∞)) (by
    rw [Fintype.sum_bool]; simp only [Bool.cond_true, Bool.cond_false]; exact_mod_cast h)

/-- The common prior: agent `k+1`'s destination is `v` with probability `qt` and `u` with
probability `qf`; all other types are deterministic. -/
noncomputable def triPrior (k : ℕ) (qt qf : ℝ≥0) (h : qt + qf = 1) :
    PMF (Option (Fin k) → TriV × TriV) :=
  (triBool qt qf h).map (triTypes k)

/-- The action profile in which agents `1, …, k` buy `X` and agent `k+1` buys `Y`. -/
def triProf (X Y : Finset TriE) : Option (Fin k) → Finset TriE := fun i => Option.elim i Y fun _ => X

@[simp] lemma triProf_none (X Y : Finset TriE) : (triProf X Y : Option (Fin k) → _) none = Y := rfl
@[simp] lemma triProf_some (X Y : Finset TriE) (j : Fin k) :
    (triProf X Y : Option (Fin k) → _) (some j) = X := rfl

variable {qt qf : ℝ≥0} {hq : qt + qf = 1}

lemma triSum (g : (Option (Fin k) → TriV × TriV) → ℝ≥0∞) :
    ∑ t, triPrior k qt qf hq t * g t =
      (qt : ℝ≥0∞) * g (triTypes k true) + (qf : ℝ≥0∞) * g (triTypes k false) := by
  rw [triPrior, sum_map_mul, Fintype.sum_bool]
  simp [triBool, PMF.ofFintype_apply]

lemma triExCost (s : Option (Fin k) → TriV × TriV → Finset TriE) (i : Option (Fin k)) :
    ((triNet k ε).bayesGame (triPrior k qt qf hq)).exCost s i =
      (qt : ℝ≥0∞) * (triNet k ε).agentCost (triTypes k true) (play s (triTypes k true)) i +
      (qf : ℝ≥0∞) * (triNet k ε).agentCost (triTypes k false) (play s (triTypes k false)) i := by
  rw [exCost]; exact triSum _

lemma triSocialCost (s : Option (Fin k) → TriV × TriV → Finset TriE) :
    ((triNet k ε).bayesGame (triPrior k qt qf hq)).socialCost s =
      (qt : ℝ≥0∞) * ((triNet k ε).bayesGame (triPrior k qt qf hq)).stateCost (triTypes k true)
        (play s (triTypes k true)) +
      (qf : ℝ≥0∞) * ((triNet k ε).bayesGame (triPrior k qt qf hq)).stateCost (triTypes k false)
        (play s (triTypes k false)) := by
  rw [socialCost_eq]; exact triSum _

lemma triWorstEqC :
    ((triNet k ε).bayesGame (triPrior k qt qf hq)).worstEqC =
      (qt : ℝ≥0∞) * (⨆ (a : Option (Fin k) → Finset TriE)
        (_ : ((triNet k ε).bayesGame (triPrior k qt qf hq)).IsNashEq (triTypes k true) a),
          ((triNet k ε).bayesGame (triPrior k qt qf hq)).stateCost (triTypes k true) a) +
      (qf : ℝ≥0∞) * ⨆ (a : Option (Fin k) → Finset TriE)
        (_ : ((triNet k ε).bayesGame (triPrior k qt qf hq)).IsNashEq (triTypes k false) a),
          ((triNet k ε).bayesGame (triPrior k qt qf hq)).stateCost (triTypes k false) a := by
  rw [worstEqC, Network.bayesGame_prior, triSum]

/-! ### Loads in the symmetric profiles `triProf X Y` -/

lemma triLoadOthers_some (X Y : Finset TriE) (j : Fin k) (e : TriE) :
    Network.loadOthers (triProf X Y) (some j) e =
      (if e ∈ X then k - 1 else 0) + (if e ∈ Y then 1 else 0) := by
  have hsum : (∑ x : Fin k, if x = j then 0 else 1) = k - 1 := by
    rw [Finset.sum_ite, sum_const_zero, zero_add, sum_const, smul_eq_mul, mul_one,
      Finset.filter_ne' univ j, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
  unfold Network.loadOthers
  rw [Finset.card_filter, Fintype.sum_option]
  by_cases hX : e ∈ X <;> by_cases hY : e ∈ Y <;> simp [hX, hY, hsum]; omega

lemma triLoadOthers_none (X Y : Finset TriE) (e : TriE) :
    Network.loadOthers (triProf X Y : Option (Fin k) → _) none e = if e ∈ X then k else 0 := by
  unfold Network.loadOthers
  rw [Finset.card_filter, Fintype.sum_option]
  by_cases hX : e ∈ X <;> simp [hX]

lemma triLO_some (hk : 1 ≤ k) (X Y : Finset TriE) (j : Fin k) (e : TriE) :
    ((Network.loadOthers (triProf X Y) (some j) e : ℕ) : ℝ≥0) + 1 =
      (if e ∈ X then (k : ℝ≥0) else 1) + (if e ∈ Y then 1 else 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [triLoadOthers_some]
  by_cases hX : e ∈ X <;> by_cases hY : e ∈ Y <;> simp [hX, hY]

lemma triLO_none (X Y : Finset TriE) (e : TriE) :
    ((Network.loadOthers (triProf X Y : Option (Fin k) → _) none e : ℕ) : ℝ≥0) + 1 =
      if e ∈ X then (k : ℝ≥0) + 1 else 1 := by
  rw [triLoadOthers_none]; split_ifs <;> simp

lemma triPay_some (hk : 1 ≤ k) (X Y : Finset TriE) (j : Fin k) :
    (triNet k ε).payment (triProf X Y) (some j) = ∑ e ∈ X, (triNet k ε).cost e /
      ((if e ∈ X then (k : ℝ≥0) else 1) + (if e ∈ Y then 1 else 0)) := by
  rw [Network.payment_eq]; simp only [triLO_some hk]; rfl

lemma triPayUpd_some (hk : 1 ≤ k) (X Y : Finset TriE) (j : Fin k) (b : Finset TriE) :
    (triNet k ε).payment (Function.update (triProf X Y) (some j) b) (some j) =
      ∑ e ∈ b, (triNet k ε).cost e /
        ((if e ∈ X then (k : ℝ≥0) else 1) + (if e ∈ Y then 1 else 0)) := by
  rw [Network.payment_update]; simp only [triLO_some hk]

lemma triPay_none (X Y : Finset TriE) :
    (triNet k ε).payment (triProf X Y : Option (Fin k) → _) none = ∑ e ∈ Y, (triNet k ε).cost e /
      (if e ∈ X then (k : ℝ≥0) + 1 else 1) := by
  rw [Network.payment_eq]; simp only [triLO_none]; rfl

lemma triPayUpd_none (X Y : Finset TriE) (b : Finset TriE) :
    (triNet k ε).payment (Function.update (triProf X Y : Option (Fin k) → _) none b) none =
      ∑ e ∈ b, (triNet k ε).cost e / (if e ∈ X then (k : ℝ≥0) + 1 else 1) := by
  rw [Network.payment_update]; simp only [triLO_none]

/-! ### Generic NCS facts -/

section Generic

variable {V E ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq E] {N : Network V E}

-- CSLib candidate
/-- Buying a superset of one's edges costs at least as much. -/
lemma triPay_le_of_subset (a : ι → Finset E) (i : ι) {b : Finset E} (h : a i ⊆ b) :
    N.payment a i ≤ N.payment (Function.update a i b) i := by
  rw [Network.payment_eq, Network.payment_update]
  exact Finset.sum_le_sum_of_subset h

-- CSLib candidate
/-- A deviation `b` costs at least the share of any edge in `b`. -/
lemma triPay_ge_of_mem (a : ι → Finset E) (i : ι) {b : Finset E} {e : E} (h : e ∈ b) :
    N.cost e / ((Network.loadOthers a i e : ℝ≥0) + 1) ≤
      N.payment (Function.update a i b) i := by
  rw [Network.payment_update]
  exact Finset.single_le_sum (f := fun e => N.cost e / ((Network.loadOthers a i e : ℝ≥0) + 1))
    (fun _ _ => zero_le) h

-- CSLib candidate
/-- An agent who connects her terminals and has no cheaper connecting deviation does not gain by
any deviation. -/
lemma triAgentCost_le {t : ι → V × V} {a : ι → Finset E} {i : ι}
    (hc : N.Connects (a i) (t i).1 (t i).2)
    (h : ∀ b, N.Connects b (t i).1 (t i).2 → N.payment a i ≤
      N.payment (Function.update a i b) i) (b : Finset E) :
    N.agentCost t a i ≤ N.agentCost t (Function.update a i b) i := by
  rw [N.agentCost_of_connects hc]
  by_cases hb : N.Connects b (t i).1 (t i).2
  · rw [N.agentCost_of_connects (by simpa using hb)]
    exact_mod_cast h b hb
  · rw [N.agentCost_of_not_connects (by simpa using hb)]; exact le_top

-- CSLib candidate
/-- A sufficient condition for a Nash equilibrium of an underlying NCS game: everybody connects
and no connecting deviation is cheaper. -/
lemma triIsNashEq_of {p : PMF (ι → V × V)} {t : ι → V × V} {a : ι → Finset E}
    (hc : ∀ i, N.Connects (a i) (t i).1 (t i).2)
    (h : ∀ i b, N.Connects b (t i).1 (t i).2 → N.payment a i ≤
      N.payment (Function.update a i b) i) : (N.bayesGame p).IsNashEq t a :=
  fun i b => triAgentCost_le (hc i) (h i) b

-- CSLib candidate
/-- In a Nash equilibrium every agent with a reachable destination connects her terminals. -/
lemma triNash_connects {p : PMF (ι → V × V)} {t : ι → V × V} {a : ι → Finset E}
    (h : (N.bayesGame p).IsNashEq t a) [Fintype E] (i : ι) (hr : N.Reachable (t i).1 (t i).2) :
    N.Connects (a i) (t i).1 (t i).2 := by
  by_contra hc
  have h1 := h i Finset.univ
  simp only [Network.bayesGame_cost] at h1
  rw [N.agentCost_of_not_connects hc, N.agentCost_of_connects (by rw [Function.update_self]; exact hr)] at h1
  exact ENNReal.coe_ne_top (top_le_iff.1 h1)

-- CSLib candidate
/-- The social cost of a Nash equilibrium is at most the cost of all edges, if all destinations
are reachable. -/
lemma triNash_stateCost_le [Fintype E] {p : PMF (ι → V × V)} {t : ι → V × V} {a : ι → Finset E}
    (h : (N.bayesGame p).IsNashEq t a) (hr : ∀ i, N.Reachable (t i).1 (t i).2) :
    (N.bayesGame p).stateCost t a ≤ ((∑ e, N.cost e : ℝ≥0) : ℝ≥0∞) := by
  rw [N.stateCost_bayesGame_of_forall p fun i => triNash_connects h i (hr i)]
  exact_mod_cast Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end Generic

/-! ### Structure of the equilibria of the triangle game -/

lemma triBiUnion (hk : 1 ≤ k) (X Y : Finset TriE) :
    Finset.univ.biUnion (triProf X Y : Option (Fin k) → _) = X ∪ Y := by
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union, Option.exists,
    triProf_none, triProf_some]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inr h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr ⟨⟨0, hk⟩, h⟩
    · exact Or.inl h

lemma triStateCost (hk : 1 ≤ k) {p : PMF (Option (Fin k) → TriV × TriV)} {t : Option (Fin k) → TriV × TriV}
    (X Y : Finset TriE) (hc : ∀ i, (triNet k ε).Connects ((triProf X Y : Option (Fin k) → _) i)
      (t i).1 (t i).2) :
    ((triNet k ε).bayesGame p).stateCost t (triProf X Y) =
      ((∑ e ∈ X ∪ Y, (triNet k ε).cost e : ℝ≥0) : ℝ≥0∞) := by
  rw [(triNet k ε).stateCost_bayesGame_of_forall p hc, Network.totalCost, triBiUnion hk]

lemma triPlay {s : Option (Fin k) → TriV × TriV → Finset TriE} {X : Finset TriE}
    (hX : ∀ j, s (some j) (u, w) = X) (b : Bool) :
    play s (triTypes k b) = triProf X (s none (triTypes k b none)) := by
  funext i; rcases i with _ | j <;> simp [hX]

lemma triPrior_ne_zero (b : Bool) (hb : cond b qt qf ≠ 0) :
    triPrior k qt qf hq (triTypes k b) ≠ 0 := by
  refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum b)).ne'
  cases b <;> simpa [triBool, PMF.ofFintype_apply, pos_iff_ne_zero] using hb

lemma triSum_filter_none (g : (Option (Fin k) → TriV × TriV) → ℝ≥0∞) :
    ∑ t with t none = (u, v), triPrior k qt qf hq t * g t = (qt : ℝ≥0∞) * g (triTypes k true) := by
  rw [Finset.sum_filter]
  have : ∀ t : Option (Fin k) → TriV × TriV, (if t none = (u, v) then triPrior k qt qf hq t * g t
      else 0) = triPrior k qt qf hq t * (if t none = (u, v) then g t else 0) := fun t => by
    split_ifs <;> simp
  simp_rw [this]
  rw [triSum]
  simp

lemma triExCost_coe {s : Option (Fin k) → TriV × TriV → Finset TriE} {i : Option (Fin k)}
    (h1 : (triNet k ε).Connects (play s (triTypes k true) i) (triTypes k true i).1
      (triTypes k true i).2)
    (h2 : (triNet k ε).Connects (play s (triTypes k false) i) (triTypes k false i).1
      (triTypes k false i).2) :
    ((triNet k ε).bayesGame (triPrior k qt qf hq)).exCost s i =
      ((qt * (triNet k ε).payment (play s (triTypes k true)) i +
        qf * (triNet k ε).payment (play s (triTypes k false)) i : ℝ≥0) : ℝ≥0∞) := by
  rw [triExCost, (triNet k ε).agentCost_of_connects h1, (triNet k ε).agentCost_of_connects h2]
  push_cast; rfl

section Bayes

variable {s : Option (Fin k) → TriV × TriV → Finset TriE}
  (hs : ((triNet k ε).bayesGame (triPrior k qt qf hq)).IsBayesEq s)
include hs

lemma triExCost_ne_top (i : Option (Fin k)) :
    ((triNet k ε).bayesGame (triPrior k qt qf hq)).exCost s i ≠ ⊤ :=
  (triNet k ε).exCost_ne_top_of_isBayesEq _ hs i fun _ _ => triReachable _ _

lemma triBayes_connects (i : Option (Fin k)) (b : Bool) (hb : cond b qt qf ≠ 0) :
    (triNet k ε).Connects (s i (triTypes k b i)) (triTypes k b i).1 (triTypes k b i).2 := by
  by_contra hc
  apply triExCost_ne_top hs i
  have h : (triNet k ε).agentCost (triTypes k b) (play s (triTypes k b)) i = ⊤ :=
    (triNet k ε).agentCost_of_not_connects hc
  rw [triExCost]
  cases b
  · rw [h, ENNReal.mul_top (by simpa using hb)]; simp
  · rw [h, ENNReal.mul_top (by simpa using hb)]; simp

lemma triBayes_removable (i : Option (Fin k)) (b : Bool) (hb : cond b qt qf ≠ 0) {e : TriE}
    (he : e ∈ s i (triTypes k b i))
    (hconn : (triNet k ε).Connects ((s i (triTypes k b i)).erase e) (triTypes k b i).1
      (triTypes k b i).2) : False :=
  (triNet k ε).not_isBayesEq_of_removable hs (triExCost_ne_top hs i) he (triNet_cost_pos e) hconn
    rfl (triPrior_ne_zero b hb)

lemma triBayes_X (hqt : qt ≠ 0) (j : Fin k) :
    s (some j) (u, w) = {uw} ∨ s (some j) (u, w) = {uv, vw} := by
  have hc := triBayes_connects hs (some j) true (by simpa using hqt)
  simp only [triTypes_some] at hc
  refine triMin_uw _ ((triConnects_uw _).1 hc) fun e he hcon => ?_
  exact triBayes_removable hs (some j) true (by simpa using hqt) (e := e) (by simpa using he)
    (by simpa [triConnects_uw] using hcon)

lemma triBayes_Yv (hqt : qt ≠ 0) : s none (u, v) = {uv} ∨ s none (u, v) = {uw, vw} := by
  have hc := triBayes_connects hs none true (by simpa using hqt)
  simp only [triTypes_none_true] at hc
  refine triMin_uv _ ((triConnects_uv _).1 hc) fun e he hcon => ?_
  exact triBayes_removable hs none true (by simpa using hqt) (e := e) (by simpa using he)
    (by simpa [triConnects_uv] using hcon)

lemma triBayes_Yu (hqf : qf ≠ 0) : s none (u, u) = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun e he => ?_
  exact triBayes_removable hs none false (by simpa using hqf) (e := e) (by simpa using he)
    (by simpa using (triNet k ε).connects_refl _ u)

/-- Agent `k+1` cannot gain by deviating at type `(u, v)`. -/
lemma triCond_none (hqt : qt ≠ 0) (b : Finset TriE) :
    (triNet k ε).agentCost (triTypes k true) (play s (triTypes k true)) none ≤
      (triNet k ε).agentCost (triTypes k true)
        (Function.update (play s (triTypes k true)) none b) none := by
  have h := BayesianGame.IsBayesEq.cond_le _ hs none (triExCost_ne_top hs none) (u, v) b
  simp only [Network.bayesGame_prior, Network.bayesGame_cost] at h
  rw [triSum_filter_none (hq := hq), triSum_filter_none (hq := hq)] at h
  exact (ENNReal.mul_le_mul_iff_right (by simpa using hqt) ENNReal.coe_ne_top).1 h

end Bayes

/-! ### Construction A (the paper's "proof of Lemma 3.6"): agent `k+1` goes to `v` w.p. `1/2` -/

/-- In the state where agent `k+1` travels to `v`, the profile "agents `1..k` buy `{uv, vw}`,
agent `k+1` buys `{uv}`" is a Nash equilibrium (if `1/k ≤ ε`). -/
lemma triA_isNashEq (hk : 1 ≤ k) (hε : 1 / (k : ℝ) ≤ ε) {p : PMF (Option (Fin k) → TriV × TriV)} :
    ((triNet k ε).bayesGame p).IsNashEq (triTypes k true) (triProf {uv, vw} {uv}) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine triIsNashEq_of ?_ ?_
  · rintro (_ | j) <;> simp [triConnects_uw, triConnects_uv]
  · rintro (_ | j) b hb
    · simp only [triTypes_none_true, triConnects_uv] at hb
      rcases hb with h | ⟨h1, -⟩
      · exact triPay_le_of_subset _ _ (by simpa using h)
      · refine le_trans ?_ (triPay_ge_of_mem _ none h1)
        rw [triPay_none, triLO_none]
        simp
    · simp only [triTypes_some, triConnects_uw] at hb
      rcases hb with h1 | ⟨h1, h2⟩
      · refine le_trans ?_ (triPay_ge_of_mem _ (some j) h1)
        rw [triPay_some hk, triLO_some hk]
        simp
        rw [← NNReal.coe_le_coe]; push_cast; simpa using hε
      · exact triPay_le_of_subset _ _ (by simp [Finset.insert_subset_iff, h1, h2])

lemma triHalf_add_half : (1 / 2 : ℝ≥0) + 1 / 2 = 1 := add_halves 1

/-- The prior of construction A: agent `k+1`'s destination is `v` or `u` with probability `1/2`
each. -/
noncomputable def triPriorA (k : ℕ) : PMF (Option (Fin k) → TriV × TriV) :=
  triPrior k (1 / 2) (1 / 2) triHalf_add_half

/-- `worst-eq^C ≥ (k+2)/2` in construction A. -/
theorem triA_worstEqC_ge (hk : 1 ≤ k) (hε : 1 / (k : ℝ) ≤ ε) :
    ((k : ℝ≥0∞) + 2) / 2 ≤ ((triNet k ε).bayesGame (triPriorA k)).worstEqC := by
  rw [triPriorA, triWorstEqC]
  refine le_trans ?_ le_self_add
  have hst : ((triNet k ε).bayesGame (triPriorA k)).stateCost (triTypes k true)
      (triProf {uv, vw} {uv}) = (k : ℝ≥0∞) + 2 := by
    rw [triStateCost hk]
    · simp; ring
    · rintro (_ | j) <;> simp [triConnects_uw, triConnects_uv]
  rw [← hst, ENNReal.div_eq_inv_mul]
  gcongr
  · simp
  · exact le_iSup₂_of_le (f := fun a (_ : ((triNet k ε).bayesGame (triPriorA k)).IsNashEq
      (triTypes k true) a) => ((triNet k ε).bayesGame (triPriorA k)).stateCost
        (triTypes k true) a) _ (triA_isNashEq hk hε) le_rfl

/-- In construction A (with `k ≥ 2`, `ε < 3/(2k)`), **every** Bayesian equilibrium has social
cost `3/2 + ε`: agents `1, …, k` buy `{uw}`, agent `k+1` buys `{uw, vw}` at destination `v`
and nothing at destination `u`. -/
theorem triA_socialCost (hk : 2 ≤ k) (hε : (ε : ℝ) < 3 / (2 * k))
    {s : Option (Fin k) → TriV × TriV → Finset TriE}
    (hs : ((triNet k ε).bayesGame (triPriorA k)).IsBayesEq s) :
    ((triNet k ε).bayesGame (triPriorA k)).socialCost s = ((3 / 2 + ε : ℝ≥0) : ℝ≥0∞) := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hε1 : ε < 1 := by
    have : (3 : ℝ) / (2 * k) ≤ 3 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    exact_mod_cast (show (ε : ℝ) < 1 by linarith)
  have hh : (1 / 2 : ℝ≥0) ≠ 0 := by norm_num
  unfold triPriorA at hs ⊢
  have hX := triBayes_X hs hh
  have hYu := triBayes_Yu hs hh
  by_cases h1 : ∃ j, s (some j) (u, w) = {uv, vw}
  · exfalso
    obtain ⟨j, hj⟩ := h1
    by_cases h2 : ∃ j', s (some j') (u, w) = {uw}
    · -- case (i): agents on both routes; an agent on `{uv, vw}` switches to `{uw}`
      obtain ⟨j', hj'⟩ := h2
      have hne : j' ≠ j := by rintro rfl; rw [hj] at hj'; exact absurd hj' (by decide)
      refine absurd (hs (some j) fun _ => {uw}) (not_le.2 ?_)
      have hc : ∀ b, (triNet k ε).Connects (play s (triTypes k b) (some j))
          (triTypes k b (some j)).1 (triTypes k b (some j)).2 := fun b => by
        simp [hj, triConnects_uw]
      have hc' : ∀ b, (triNet k ε).Connects
          (play (Function.update s (some j) fun _ => {uw}) (triTypes k b) (some j))
          (triTypes k b (some j)).1 (triTypes k b (some j)).2 := fun b => by
        simp [triConnects_uw]
      rw [triExCost_coe (hc true) (hc false), triExCost_coe (hc' true) (hc' false)]
      refine ENNReal.coe_lt_coe.2 ?_
      have hge : ∀ b, 1 ≤ (triNet k ε).payment (play s (triTypes k b)) (some j) := by
        intro b
        have hmem : uv ∈ play s (triTypes k b) (some j) := by simp [hj]
        have hl := Network.load_le_card (play s (triTypes k b)) uv
        have hl0 := Network.load_pos hmem
        simp only [Fintype.card_option, Fintype.card_fin] at hl
        unfold Network.payment
        refine le_trans ?_ (Finset.single_le_sum (f := fun e => (triNet k ε).cost e /
          (Network.load (play s (triTypes k b)) e : ℝ≥0)) (fun _ _ => zero_le) hmem)
        rw [le_div_iff₀ (by exact_mod_cast hl0), one_mul, triNet_cost_uv]
        exact_mod_cast hl
      have hle : ∀ b, (triNet k ε).payment
          (play (Function.update s (some j) fun _ => {uw}) (triTypes k b)) (some j) ≤
          (1 + ε) / 2 := by
        intro b
        rw [play_update, Network.payment_update, Finset.sum_singleton, triNet_cost_uw]
        have hlo : 1 ≤ Network.loadOthers (play s (triTypes k b)) (some j) uw :=
          Finset.card_pos.2 ⟨some j', by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨by simpa using hne, by simp [hj']⟩⟩
        refine div_le_div_of_nonneg_left zero_le (by norm_num) ?_
        have : (1 : ℝ≥0) ≤ Network.loadOthers (play s (triTypes k b)) (some j) uw := by
          exact_mod_cast hlo
        calc (2 : ℝ≥0) = 1 + 1 := by norm_num
          _ ≤ _ := by gcongr
      calc (1 / 2) * (triNet k ε).payment
            (play (Function.update s (some j) fun _ => {uw}) (triTypes k true)) (some j) +
          (1 / 2) * (triNet k ε).payment
            (play (Function.update s (some j) fun _ => {uw}) (triTypes k false)) (some j)
          ≤ (1 / 2) * ((1 + ε) / 2) + (1 / 2) * ((1 + ε) / 2) := by
            gcongr <;> exact hle _
        _ < (1 / 2) * 1 + (1 / 2) * 1 := by
            rw [← mul_add, ← mul_add]
            refine mul_lt_mul_of_pos_left ?_ (by norm_num)
            rw [← NNReal.coe_lt_coe]; push_cast
            have : (ε : ℝ) < 1 := by exact_mod_cast hε1
            linarith
        _ ≤ _ := by gcongr <;> exact hge _
    · -- case (ii): all agents `1..k` on `{uv, vw}`
      have hall : ∀ j, s (some j) (u, w) = {uv, vw} := fun j =>
        (hX j).resolve_left fun h => h2 ⟨j, h⟩
      have hplay := triPlay hall
      rcases triBayes_Yv hs hh with hYv | hYv
      · -- agent `j` switches to `{uw}`
        refine absurd (hs (some j) fun _ => {uw}) (not_le.2 ?_)
        have hc : ∀ b, (triNet k ε).Connects (play s (triTypes k b) (some j))
            (triTypes k b (some j)).1 (triTypes k b (some j)).2 := fun b => by
          simp [hj, triConnects_uw]
        have hc' : ∀ b, (triNet k ε).Connects
            (play (Function.update s (some j) fun _ => {uw}) (triTypes k b) (some j))
            (triTypes k b (some j)).1 (triTypes k b (some j)).2 := fun b => by
          simp [triConnects_uw]
        rw [triExCost_coe (hc true) (hc false), triExCost_coe (hc' true) (hc' false)]
        refine ENNReal.coe_lt_coe.2 ?_
        rw [play_update, play_update, hplay, hplay]
        simp only [triTypes_none_true, triTypes_none_false, hYv, hYu]
        rw [triPay_some hk1, triPay_some hk1, triPayUpd_some hk1, triPayUpd_some hk1]
        simp
        rw [← NNReal.coe_lt_coe]; push_cast
        have hk0 : (0 : ℝ) < k := by linarith
        have e1 : ((k : ℝ) + 1) / k = 1 + (k : ℝ)⁻¹ := by field_simp
        have e2 : (3 : ℝ) / (2 * k) = 3 / 2 * (k : ℝ)⁻¹ := by field_simp
        rw [e1]; rw [e2] at hε; linarith
      · -- agent `k+1` switches to `{uv}` at destination `v`
        have h := triCond_none hs hh {uv}
        rw [hplay true] at h
        simp only [triTypes_none_true, hYv] at h
        rw [(triNet k ε).agentCost_of_connects (by simp [triConnects_uv]),
          (triNet k ε).agentCost_of_connects (by simp [triConnects_uv])] at h
        have h' := ENNReal.coe_le_coe.1 h
        rw [triPay_none, triPayUpd_none] at h'
        simp at h'
        exact absurd h' (not_le.2 (lt_add_of_le_of_pos le_self_add (by positivity)))
  · -- case (iii): all agents `1..k` on `{uw}`
    have hall : ∀ j, s (some j) (u, w) = {uw} := fun j =>
      (hX j).resolve_right fun h => h1 ⟨j, h⟩
    have hplay := triPlay hall
    rcases triBayes_Yv hs hh with hYv | hYv
    · exfalso
      have h := triCond_none hs hh {uw, vw}
      rw [hplay true] at h
      simp only [triTypes_none_true, hYv] at h
      rw [(triNet k ε).agentCost_of_connects (by simp [triConnects_uv]),
        (triNet k ε).agentCost_of_connects (by simp [triConnects_uv])] at h
      have h' := ENNReal.coe_le_coe.1 h
      rw [triPay_none, triPayUpd_none] at h'
      simp at h'
      rw [← NNReal.coe_le_coe] at h'; push_cast at h'
      have hk0 : (0 : ℝ) < k + 1 := by linarith
      rw [le_div_iff₀ hk0] at h'
      have : (ε : ℝ) < 1 := by exact_mod_cast hε1
      nlinarith
    · rw [triSocialCost, hplay, hplay]
      simp only [triTypes_none_true, triTypes_none_false, hYv, hYu]
      rw [triStateCost hk1, triStateCost hk1]
      · rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_add]
        congr 1
        simp
        rw [← NNReal.coe_inj]; push_cast; ring
      all_goals rintro (_ | j) <;>
        first | exact (triNet k ε).connects_refl _ _ | simp [triConnects_uw, triConnects_uv]

/-- `worst-eq^P = 3/2 + ε` in construction A. -/
theorem triA_worstEqP (hk : 2 ≤ k) (hε : (ε : ℝ) < 3 / (2 * k)) :
    ((triNet k ε).bayesGame (triPriorA k)).worstEqP = ((3 / 2 + ε : ℝ≥0) : ℝ≥0∞) := by
  refine le_antisymm (worstEqP_le _ fun s hs => (triA_socialCost hk hε hs).le) ?_
  obtain ⟨s, -, hs, -⟩ := exists_isBayesEq (triNet k ε) (triPriorA k)
  rw [← triA_socialCost hk hε hs]
  exact le_worstEqP _ hs

/-! ### Total edge cost and a general upper bound on `worst-eq^C` -/

lemma triUniv : (Finset.univ : Finset TriE) = {uv, vw, uw} := rfl

lemma triTotal : ∑ e, (triNet k ε).cost e = (k : ℝ≥0) + 3 + ε := by
  rw [triUniv]; simp; ring

lemma triWorstEqC_le (c : ℝ≥0∞)
    (hc : ∀ a, ((triNet k ε).bayesGame (triPrior k qt qf hq)).IsNashEq (triTypes k false) a →
      ((triNet k ε).bayesGame (triPrior k qt qf hq)).stateCost (triTypes k false) a ≤ c) :
    ((triNet k ε).bayesGame (triPrior k qt qf hq)).worstEqC ≤
      (qt : ℝ≥0∞) * (((k : ℝ≥0) + 3 + ε : ℝ≥0) : ℝ≥0∞) + (qf : ℝ≥0∞) * c := by
  rw [triWorstEqC]
  gcongr
  · refine iSup₂_le fun a ha => ?_
    rw [← triTotal]
    exact triNash_stateCost_le ha fun i => triReachable _ _
  · exact iSup₂_le hc

/-! ### Construction B (the paper's "proof of Lemma 3.7"): agent `k+1` goes to `v` w.p. `1/k` -/

lemma triInv_add : (k : ℝ≥0)⁻¹ + (1 - (k : ℝ≥0)⁻¹) = 1 := by
  refine add_tsub_cancel_of_le ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hk)

/-- The prior of construction B: agent `k+1`'s destination is `v` with probability `1/k` and `u`
with probability `1 - 1/k`. -/
noncomputable def triPriorB (k : ℕ) : PMF (Option (Fin k) → TriV × TriV) :=
  triPrior k (k : ℝ≥0)⁻¹ (1 - (k : ℝ≥0)⁻¹) triInv_add

/-- The strategy profile `s` of construction B: agents `1..k` buy `{uv, vw}`, agent `k+1` buys
`{uv}` at destination `v` and nothing at destination `u`. -/
def triSB : Option (Fin k) → TriV × TriV → Finset TriE := fun i τ =>
  Option.elim i (if τ = (u, v) then {uv} else ∅) fun _ => {uv, vw}

lemma triSB_play (b : Bool) :
    play triSB (triTypes k b) = triProf {uv, vw} (if b then {uv} else ∅) := by
  funext i; rcases i with _ | j <;> cases b <;> simp [triSB]

/-- The profile `s` of construction B is a Bayesian equilibrium when `2/k - 1/k² ≤ ε`. -/
theorem triB_isBayesEq (hk : 2 ≤ k) (hε : 2 / (k : ℝ) - 1 / (k : ℝ) ^ 2 ≤ ε) :
    ((triNet k ε).bayesGame (triPriorB k)).IsBayesEq triSB := by
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hinv : (k : ℝ≥0)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hk1)
  unfold triPriorB
  rintro (_ | j) σ
  · rw [triExCost, triExCost, play_update, play_update, triSB_play, triSB_play]
    gcongr
    · refine triAgentCost_le (by simp [triConnects_uv]) (fun b hb => ?_) _
      simp only [triTypes_none_true, triConnects_uv] at hb
      rcases hb with h | ⟨h1, -⟩
      · exact triPay_le_of_subset _ _ (by simpa using h)
      · refine le_trans ?_ (triPay_ge_of_mem _ none h1)
        rw [triPay_none, triLO_none]
        simp
    · refine triAgentCost_le ((triNet k ε).connects_refl _ _) (fun b _ => ?_) _
      simp [triPay_none]
  · by_cases hB : (triNet k ε).Connects (σ (u, w)) u w
    · have hc : ∀ b, (triNet k ε).Connects (play triSB (triTypes k b) (some j))
          (triTypes k b (some j)).1 (triTypes k b (some j)).2 := by
        intro b; rw [triSB_play]; simp [triConnects_uw]
      have hc' : ∀ b, (triNet k ε).Connects
          (play (Function.update triSB (some j) σ) (triTypes k b) (some j))
          (triTypes k b (some j)).1 (triTypes k b (some j)).2 := by
        intro b; rw [play_update]; simpa using hB
      rw [triExCost_coe (hc true) (hc false), triExCost_coe (hc' true) (hc' false)]
      refine ENNReal.coe_le_coe.2 ?_
      rw [play_update, play_update, triSB_play, triSB_play]
      simp only [triTypes_some]
      rw [triConnects_uw] at hB
      rcases hB with h | ⟨h1, h2⟩
      · calc _ ≤ (k : ℝ≥0)⁻¹ * (1 + ε) + (1 - (k : ℝ≥0)⁻¹) * (1 + ε) := by
              rw [triPay_some hk1, triPay_some hk1]
              simp
              rw [← NNReal.coe_le_coe]
              push_cast [NNReal.coe_sub hinv]
              have hk0 : (0 : ℝ) < k := by linarith
              have e : ((k : ℝ))⁻¹ * (1 + (k : ℝ)⁻¹) + (1 - (k : ℝ)⁻¹) * (((k : ℝ) + 1) / k +
                  (k : ℝ)⁻¹) = 1 + (2 / k - 1 / (k : ℝ) ^ 2) := by
                field_simp; ring
              rw [e]
              nlinarith
          _ ≤ _ := by
              gcongr <;>
              · refine le_trans ?_ (triPay_ge_of_mem _ _ h)
                rw [triLO_some hk1]; simp
      · gcongr <;> exact triPay_le_of_subset _ _ (by simp [Finset.insert_subset_iff, h1, h2])
    · have : ((triNet k ε).bayesGame (triPrior k (k : ℝ≥0)⁻¹ (1 - (k : ℝ≥0)⁻¹) triInv_add)).exCost
          (Function.update triSB (some j) σ) (some j) = ⊤ := by
        rw [triExCost, play_update, (triNet k ε).agentCost_of_not_connects (by simpa using hB)]
        rw [ENNReal.mul_top (by simp; omega)]; simp
      rw [this]; exact le_top

/-- In construction B, the social cost of `s` is `k + 2`. -/
theorem triB_socialCost (hk : 1 ≤ k) :
    ((triNet k ε).bayesGame (triPriorB k)).socialCost triSB = (k : ℝ≥0∞) + 2 := by
  unfold triPriorB
  rw [triSocialCost, triSB_play, triSB_play, triStateCost hk, triStateCost hk]
  · simp
    have hinv : (((k : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤ 1 :=
      ENNReal.coe_le_one_iff.2 (inv_le_one_of_one_le₀ (by exact_mod_cast hk))
    have e : (1 : ℝ≥0∞) + ((k : ℝ≥0∞) + 1) = k + 1 + 1 := by ring
    rw [e, ← add_mul, add_tsub_cancel_of_le hinv, one_mul]
    ring
  all_goals rintro (_ | j) <;>
    first | exact (triNet k ε).connects_refl _ _ | simp [triConnects_uw, triConnects_uv]

lemma triLoadOthers_none_le (a : Option (Fin k) → Finset TriE) (e : TriE) :
    Network.loadOthers a none e ≤ k := by
  unfold Network.loadOthers
  calc #{j | j ≠ none ∧ e ∈ a j} ≤ #(Finset.univ.erase (none : Option (Fin k))) :=
        Finset.card_le_card fun j hj => by simp at hj ⊢; exact hj.1
    _ = k := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_option,
          Fintype.card_fin]; simp

/-- When agent `k+1` stays at `u` and `ε < 2/k`, every Nash equilibrium of the underlying game
has agents `1..k` buy `{uw}` and agent `k+1` buy nothing, so its social cost is `1 + ε`. -/
theorem triB_nash_false (hk : 1 ≤ k) (hε : (ε : ℝ) < 2 / k) {p : PMF (Option (Fin k) → TriV × TriV)}
    {a : Option (Fin k) → Finset TriE}
    (h : ((triNet k ε).bayesGame p).IsNashEq (triTypes k false) a) :
    ((triNet k ε).bayesGame p).stateCost (triTypes k false) a = ((1 + ε : ℝ≥0) : ℝ≥0∞) := by
  have hY : a none = ∅ := Finset.eq_empty_of_forall_notMem fun e he =>
    (triNet k ε).not_isNashEq_of_removable h he (triNet_cost_pos e)
      ((triNet k ε).connects_refl _ u)
  have hX : ∀ j, a (some j) = {uw} ∨ a (some j) = {uv, vw} := by
    intro j
    have hc := triNash_connects h (some j) (triReachable _ _)
    simp only [triTypes_some] at hc
    refine triMin_uw _ ((triConnects_uw _).1 hc) fun e he hcon => ?_
    exact (triNet k ε).not_isNashEq_of_removable h he (triNet_cost_pos e)
      (by simpa [triConnects_uw] using hcon)
  by_cases h1 : ∃ j, a (some j) = {uv, vw}
  · exfalso
    obtain ⟨j, hj⟩ := h1
    have h2 := h (some j) {uw}
    simp only [Network.bayesGame_cost] at h2
    rw [(triNet k ε).agentCost_of_connects (by simp [hj, triConnects_uw]),
      (triNet k ε).agentCost_of_connects (by simp [triConnects_uw])] at h2
    have h3 := ENNReal.coe_le_coe.1 h2
    have hload : ∀ e, Network.load a e ≤ k := fun e => by
      rw [Network.load_eq a none e]; simpa [hY] using triLoadOthers_none_le a e
    have hlo : (triNet k ε).payment (Function.update a (some j) {uw}) (some j) ≤ 1 + ε := by
      rw [Network.payment_update, Finset.sum_singleton, triNet_cost_uw]
      exact div_le_self zero_le (le_add_self)
    have hdiv : ∀ e ∈ a (some j), (triNet k ε).cost e / (k : ℝ≥0) ≤
        (triNet k ε).cost e / (Network.load a e : ℝ≥0) := fun e he =>
      div_le_div_of_nonneg_left zero_le (by exact_mod_cast Network.load_pos he)
        (by exact_mod_cast hload e)
    have hge : ((k : ℝ≥0) + 1) / k + 1 / k ≤ (triNet k ε).payment a (some j) := by
      unfold Network.payment
      rw [hj, Finset.sum_pair (by decide)]
      have h1 := hdiv uv (by simp [hj])
      have h2 := hdiv vw (by simp [hj])
      simp only [triNet_cost_uv, triNet_cost_vw] at h1 h2 ⊢
      exact add_le_add h1 h2
    have hlt : 1 + ε < ((k : ℝ≥0) + 1) / k + 1 / k := by
      rw [← NNReal.coe_lt_coe]; push_cast
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have e : ((k : ℝ) + 1) / k + 1 / k = 1 + 2 / k := by field_simp; ring
      rw [e]; linarith
    exact absurd h3 (not_le.2 (hlo.trans_lt (hlt.trans_le hge)))
  · have hall : ∀ j, a (some j) = {uw} := fun j => (hX j).resolve_right fun h => h1 ⟨j, h⟩
    have ha : a = triProf {uw} ∅ := by
      funext i; rcases i with _ | j
      · simp [hY]
      · simp [hall]
    subst ha
    rw [triStateCost hk]
    · simp
    · rintro (_ | j)
      · exact (triNet k ε).connects_refl _ _
      · simp [triConnects_uw]

/-- When agent `k+1` stays at `u`, "agents `1..k` buy `{uw}`, agent `k+1` buys nothing" is a
Nash equilibrium (if `ε ≤ 1`). -/
lemma triB_isNashEq_false (hk : 1 ≤ k) (hε : ε ≤ 1) {p : PMF (Option (Fin k) → TriV × TriV)} :
    ((triNet k ε).bayesGame p).IsNashEq (triTypes k false) (triProf {uw} ∅) := by
  refine triIsNashEq_of ?_ ?_
  · rintro (_ | j)
    · exact (triNet k ε).connects_refl _ _
    · simp [triConnects_uw]
  · rintro (_ | j) b hb
    · simp [triPay_none]
    · simp only [triTypes_some, triConnects_uw] at hb
      rcases hb with h1 | ⟨h1, -⟩
      · exact triPay_le_of_subset _ _ (by simpa using h1)
      · refine le_trans ?_ (triPay_ge_of_mem _ (some j) h1)
        rw [triPay_some hk, triLO_some hk]
        simp
        rw [← NNReal.coe_le_coe]; push_cast
        have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
        have : (ε : ℝ) ≤ 1 := by exact_mod_cast hε
        rw [div_le_iff₀ (by linarith)]
        nlinarith

/-- `worst-eq^C ≤ (1 - 1/k)(1 + ε) + (1/k)(k + 3 + ε)` in construction B (`ε < 2/k`), and
`worst-eq^C ≥ (1 - 1/k)(1 + ε) > 0` (`ε ≤ 1`). -/
theorem triB_worstEqC (hk : 2 ≤ k) (hε : (ε : ℝ) < 2 / k) :
    (((1 - (k : ℝ≥0)⁻¹) * (1 + ε) : ℝ≥0) : ℝ≥0∞) ≤
        ((triNet k ε).bayesGame (triPriorB k)).worstEqC ∧
      ((triNet k ε).bayesGame (triPriorB k)).worstEqC ≤
        (((1 - (k : ℝ≥0)⁻¹) * (1 + ε) + (k : ℝ≥0)⁻¹ * ((k : ℝ≥0) + 3 + ε) : ℝ≥0) : ℝ≥0∞) := by
  have hk1 : 1 ≤ k := by omega
  have hε1 : ε ≤ 1 := by
    have : (2 : ℝ) / k ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast hk
    exact_mod_cast (show (ε : ℝ) ≤ 1 by linarith)
  unfold triPriorB
  constructor
  · rw [triWorstEqC]
    refine le_trans ?_ le_add_self
    rw [ENNReal.coe_mul, ← triB_nash_false hk1 hε (triB_isNashEq_false hk1 hε1)]
    gcongr
    exact le_iSup₂_of_le (f := fun a (_ : ((triNet k ε).bayesGame (triPrior k (k : ℝ≥0)⁻¹
      (1 - (k : ℝ≥0)⁻¹) triInv_add)).IsNashEq (triTypes k false) a) =>
        ((triNet k ε).bayesGame (triPrior k (k : ℝ≥0)⁻¹ (1 - (k : ℝ≥0)⁻¹) triInv_add)).stateCost
          (triTypes k false) a) _ (triB_isNashEq_false hk1 hε1) le_rfl
  · refine (triWorstEqC_le _ fun a ha => (triB_nash_false hk1 hε ha).le).trans ?_
    push_cast
    rw [add_comm]

/-! ### The two lemmas -/

/-- Construction A, exact statement (the appendix's "proof of Lemma 3.6", which actually proves
Lemma 3.7): on `G_worst` with `k ≥ 2` agents `u → w`, one agent `u → v` / `u → u` with probability
`1/2` each, and `1/k < ε < 3/(2k)`: `worst-eq^P = 3/2 + ε` and `worst-eq^C ≥ (k+2)/2`. -/
theorem worstConstructionA (hk : 2 ≤ k) (hε₁ : 1 / (k : ℝ) < ε) (hε₂ : (ε : ℝ) < 3 / (2 * k)) :
    ((triNet k ε).bayesGame (triPriorA k)).worstEqP = ((3 / 2 + ε : ℝ≥0) : ℝ≥0∞) ∧
      ((k : ℝ≥0∞) + 2) / 2 ≤ ((triNet k ε).bayesGame (triPriorA k)).worstEqC :=
  ⟨triA_worstEqP hk hε₂, triA_worstEqC_ge (by omega) hε₁.le⟩

/-- Construction B, exact statement (the appendix's "proof of Lemma 3.7", which actually proves
Lemma 3.6): on `G_worst` with `k ≥ 2` agents `u → w`, one agent `u → v` with probability `1/k`
and `u → u` with probability `1 - 1/k`, and `2/k - 1/k² ≤ ε < 2/k`: `worst-eq^P ≥ k + 2` and
`(1 - 1/k)(1 + ε) ≤ worst-eq^C ≤ (1 - 1/k)(1 + ε) + (1/k)(k + 3 + ε)`. -/
theorem worstConstructionB (hk : 2 ≤ k) (hε₁ : 2 / (k : ℝ) - 1 / (k : ℝ) ^ 2 ≤ ε)
    (hε₂ : (ε : ℝ) < 2 / k) :
    (k : ℝ≥0∞) + 2 ≤ ((triNet k ε).bayesGame (triPriorB k)).worstEqP ∧
      (((1 - (k : ℝ≥0)⁻¹) * (1 + ε) : ℝ≥0) : ℝ≥0∞) ≤
        ((triNet k ε).bayesGame (triPriorB k)).worstEqC ∧
      ((triNet k ε).bayesGame (triPriorB k)).worstEqC ≤
        (((1 - (k : ℝ≥0)⁻¹) * (1 + ε) + (k : ℝ≥0)⁻¹ * ((k : ℝ≥0) + 3 + ε) : ℝ≥0) : ℝ≥0∞) := by
  refine ⟨?_, triB_worstEqC hk hε₂⟩
  rw [← triB_socialCost (ε := ε) (by omega)]
  exact le_worstEqP _ (triB_isBayesEq hk hε₁)

/-- Lemma 3.6 of [Alon–Emek–Feldman–Tennenholtz 2010]: for every `k₀` there is a Bayesian NCS
game on an undirected 3-vertex graph with `n ≥ k₀` agents such that
`worst-eq^P / worst-eq^C = Ω(n)`; precisely `n · worst-eq^C ≤ 4 · worst-eq^P`, with
`0 < worst-eq^C` and `worst-eq^P < ∞`.

The paper's appendix "proof of Lemma 3.6" does not prove this (its construction gives the
opposite ratio `O(1/k)`); the statement is proved by the construction of the appendix's "proof of
Lemma 3.7" (`worstConstructionB`, with `ε = 2/k - 1/(2k²)`). The paper's game has `k + 1` agents. -/
theorem lemma_3_6 (k₀ : ℕ) : ∃ k ≥ k₀, ∃ (c : TriE → ℝ≥0) (p : PMF (Option (Fin k) → TriV × TriV)),
    0 < ((Network.undirected triEnds c).bayesGame p).worstEqC ∧
    ((Network.undirected triEnds c).bayesGame p).worstEqP ≠ ⊤ ∧
    (Fintype.card (Option (Fin k)) : ℝ≥0∞) * ((Network.undirected triEnds c).bayesGame p).worstEqC ≤
      4 * ((Network.undirected triEnds c).bayesGame p).worstEqP := by
  set k := max k₀ 3 with hkdef
  have hk : 3 ≤ k := le_max_right _ _
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  set ε : ℝ≥0 := ((4 * k - 1 : ℕ) : ℝ≥0) / (2 * (k : ℝ≥0) ^ 2) with hεdef
  have hεR : (ε : ℝ) = (4 * k - 1) / (2 * (k : ℝ) ^ 2) := by
    have h4 : ((4 * k - 1 : ℕ) : ℝ) = 4 * k - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    simp only [hεdef, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_mul, NNReal.coe_pow,
      NNReal.coe_ofNat]
    rw [h4]
  have hk0 : (0 : ℝ) < k := by linarith
  have hε₁ : 2 / (k : ℝ) - 1 / (k : ℝ) ^ 2 ≤ ε := by
    rw [hεR, div_sub_div _ _ hk0.ne' (by positivity), div_le_div_iff₀ (by positivity)
      (by positivity)]
    nlinarith
  have hε₂ : (ε : ℝ) < 2 / k := by
    rw [hεR, div_lt_div_iff₀ (by positivity) hk0]; nlinarith
  obtain ⟨hP, hC1, hC2⟩ := worstConstructionB (by omega) hε₁ hε₂
  have hN : Network.undirected triEnds (triNet k ε).cost = triNet k ε := rfl
  refine ⟨k, le_max_left _ _, (triNet k ε).cost, triPriorB k, ?_⟩
  rw [hN]
  refine ⟨?_, ?_, ?_⟩
  · refine lt_of_lt_of_le ?_ hC1
    have : (0 : ℝ≥0) < (1 - (k : ℝ≥0)⁻¹) * (1 + ε) := by
      refine mul_pos ?_ (by positivity)
      rw [tsub_pos_iff_lt]
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (by omega : 1 < k))
    exact_mod_cast this
  · -- `worst-eq^P ≤ n · opt^C ≤ n · K(s) < ∞` (Lemma 3.1)
    refine ne_top_of_le_ne_top ?_ (lemma_3_1 (triNet k ε) (triPriorB k))
    refine ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top ?_
      (optC_le_socialCost _ (triSB (k := k))))
    rw [triB_socialCost (by omega)]; simp
  · rw [Fintype.card_option, Fintype.card_fin]
    have hinv : (k : ℝ≥0)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast (by omega : 1 ≤ k))
    have hX : ((k : ℝ≥0) + 1) * ((1 - (k : ℝ≥0)⁻¹) * (1 + ε) + (k : ℝ≥0)⁻¹ * ((k : ℝ≥0) + 3 + ε))
        ≤ 4 * ((k : ℝ≥0) + 2) := by
      rw [← NNReal.coe_le_coe]
      push_cast [NNReal.coe_sub hinv]
      have e : (1 - (k : ℝ)⁻¹) * (1 + ε) + (k : ℝ)⁻¹ * (k + 3 + ε) = 2 + ε + 2 / k := by
        field_simp; ring
      have h2k : (2 : ℝ) / k ≤ 1 := by rw [div_le_one hk0]; linarith
      rw [e]; nlinarith
    calc ((k + 1 : ℕ) : ℝ≥0∞) * ((triNet k ε).bayesGame (triPriorB k)).worstEqC
        ≤ ((k + 1 : ℕ) : ℝ≥0∞) * (((1 - (k : ℝ≥0)⁻¹) * (1 + ε) + (k : ℝ≥0)⁻¹ *
          ((k : ℝ≥0) + 3 + ε) : ℝ≥0) : ℝ≥0∞) := by gcongr
      _ = ((((k : ℝ≥0) + 1) * ((1 - (k : ℝ≥0)⁻¹) * (1 + ε) + (k : ℝ≥0)⁻¹ *
          ((k : ℝ≥0) + 3 + ε)) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
      _ ≤ ((4 * ((k : ℝ≥0) + 2) : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hX
      _ = 4 * ((k : ℝ≥0∞) + 2) := by push_cast; ring
      _ ≤ _ := by gcongr

/-- Lemma 3.7 of [Alon–Emek–Feldman–Tennenholtz 2010]: for every `k₀` there is a Bayesian NCS
game on an undirected 3-vertex graph with `n ≥ k₀` agents such that
`worst-eq^P / worst-eq^C = O(1/n)`; precisely `n · worst-eq^P ≤ 4 · worst-eq^C`, with
`0 < worst-eq^P` and `worst-eq^C < ∞`.

The paper's appendix "proof of Lemma 3.7" does not prove this (its construction gives the
opposite ratio `Ω(k)`); the statement is proved by the construction of the appendix's "proof of
Lemma 3.6" (`worstConstructionA`, with `ε = 5/(4k)`). The paper's game has `k + 1` agents. -/
theorem lemma_3_7 (k₀ : ℕ) : ∃ k ≥ k₀, ∃ (c : TriE → ℝ≥0) (p : PMF (Option (Fin k) → TriV × TriV)),
    0 < ((Network.undirected triEnds c).bayesGame p).worstEqP ∧
    ((Network.undirected triEnds c).bayesGame p).worstEqC ≠ ⊤ ∧
    (Fintype.card (Option (Fin k)) : ℝ≥0∞) * ((Network.undirected triEnds c).bayesGame p).worstEqP ≤
      4 * ((Network.undirected triEnds c).bayesGame p).worstEqC := by
  set k := max k₀ 2 with hkdef
  have hk : 2 ≤ k := le_max_right _ _
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  set ε : ℝ≥0 := 5 / (4 * (k : ℝ≥0)) with hεdef
  have hεR : (ε : ℝ) = 5 / (4 * k) := by simp [hεdef]
  have hε₁ : 1 / (k : ℝ) < ε := by
    rw [hεR, div_lt_div_iff₀ hk0 (by positivity)]; nlinarith
  have hε₂ : (ε : ℝ) < 3 / (2 * k) := by
    rw [hεR, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  obtain ⟨hP, hC⟩ := worstConstructionA hk hε₁ hε₂
  have hN : Network.undirected triEnds (triNet k ε).cost = triNet k ε := rfl
  refine ⟨k, le_max_left _ _, (triNet k ε).cost, triPriorA k, ?_⟩
  rw [hN]
  refine ⟨?_, ?_, ?_⟩
  · rw [hP]; exact_mod_cast (show (0 : ℝ≥0) < 3 / 2 + ε by positivity)
  · unfold triPriorA
    refine ne_top_of_le_ne_top ?_ (triWorstEqC_le (((k : ℝ≥0) + 3 + ε : ℝ≥0) : ℝ≥0∞)
      fun a ha => ?_)
    · exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top,
        ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top⟩
    · rw [← triTotal]
      exact triNash_stateCost_le ha fun i => triReachable _ _
  · rw [Fintype.card_option, Fintype.card_fin, hP]
    have hX : ((k : ℝ≥0) + 1) * (3 / 2 + ε) ≤ 2 * ((k : ℝ≥0) + 2) := by
      rw [← NNReal.coe_le_coe]
      push_cast
      rw [hεR]
      have e : ((k : ℝ) + 1) * (3 / 2 + 5 / (4 * k)) = 3 / 2 * k + 11 / 4 + 5 / (4 * k) := by
        field_simp; ring
      have h5 : (5 : ℝ) / (4 * k) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      rw [e]; nlinarith
    calc ((k + 1 : ℕ) : ℝ≥0∞) * ((3 / 2 + ε : ℝ≥0) : ℝ≥0∞)
        = ((((k : ℝ≥0) + 1) * (3 / 2 + ε) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
      _ ≤ ((2 * ((k : ℝ≥0) + 2) : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.2 hX
      _ = 4 * (((k : ℝ≥0∞) + 2) / 2) := by
        rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc,
          ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]
        push_cast; ring
      _ ≤ _ := by gcongr

end Podc.BayesianIgnorance
