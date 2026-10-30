import Papers.PODC2024.PPGameDynamics.Ehrenfest
import Cslib.Computability.Distributed.PopulationProtocols.RandomScheduler

/-!
# The `k`-IGT dynamics and its count process (Definition 2.1, Section 2.2.1, Theorem 2.7)

Agents (a finite type `A`, `n = |A|`) have fixed strategy *kinds* `τ : A → Kind` (AC, AD or
GTFT); a GTFT agent additionally carries a generosity level `j ∈ Fin k` (level `j` is the paper's
`g_{j+1}`). The `k`-IGT dynamics (Definition 2.1) is the one-way population protocol `igt k`:
the initiator, if GTFT, increments its level after meeting an AC or GTFT agent and decrements it
after meeting an AD agent (truncated to `[0, k-1]`); nobody else changes.

The configuration space is `Cfg τ` (configurations whose kinds are `τ`); `counts C ∈ Δ_k^m`
(`m` = number of GTFT agents) is the paper's count vector `z`.

* `schedKernel_lump`: for any scheduler drawing an (initiator, responder) pair `ω` uniformly
  from a finite set in which every GTFT initiator has `cAD` AD partners and `cN` non-AD
  partners, the count process is *exactly* the `(k, a, b, m)`-Ehrenfest process with
  `a = w cN m`, `b = w cAD m` (`w` = probability of a pair).
* `replKernel` (initiator and responder drawn independently and uniformly from all `n` agents):
  `a = γ(1-β)`, `b = γβ` — the identification claimed in Section 2.4;
  `theorem_2_7_stationary`: the count process is the Ehrenfest process and its unique stationary
  distribution is multinomial with `p_j ∝ (1/β - 1)^(j-1)` (Theorem 2.7, stationary part).
* `distinctKernel` (the standard population-protocol scheduler: an ordered pair of *distinct*
  agents, CSLib's `uniformKernel`): `a = γ(n-1-βn)/(n-1)`, `b = γβn/(n-1)`, so the stationary
  distribution is multinomial with ratio `(n-1-βn)/(βn) ≠ 1/β - 1`;
  `distinct_counterexample`: a 3-agent instance where the formula of Theorem 2.7 is off.
-/

open Finset Matrix Cslib.Probability.Markov Cslib.PopulationProtocol

namespace Podc.PPGameDynamics

/-- Strategy kinds. -/
inductive Kind where
  | ac | ad | gtft
  deriving DecidableEq

/-- Strategies: AC, AD, or GTFT with generosity level `j` (the paper's `g_{j+1}`). -/
inductive Strat (k : ℕ) where
  | ac | ad | gtft (j : Fin k)
  deriving DecidableEq

variable {k : ℕ}

/-- `Strat k ≃ Option (Option (Fin k))`, for the `Fintype` instance. -/
def Strat.equiv : Strat k ≃ Option (Option (Fin k)) where
  toFun | .ac => none | .ad => some none | .gtft j => some (some j)
  invFun | none => .ac | some none => .ad | some (some j) => .gtft j
  left_inv s := by cases s <;> rfl
  right_inv o := by rcases o with _ | _ | _ <;> rfl

instance : Fintype (Strat k) := Fintype.ofEquiv _ Strat.equiv.symm

/-- The kind of a strategy. -/
def Strat.kind : Strat k → Kind
  | .ac => .ac | .ad => .ad | .gtft _ => .gtft

/-- `Inc(g_j) = g_{min(j+1, k)}`. -/
def inc (j : Fin k) : Fin k := ⟨min (j.val + 1) (k - 1), by omega⟩

/-- `Dec(g_j) = g_{max(j-1, 1)}`. -/
def dec (j : Fin k) : Fin k := ⟨j.val - 1, by omega⟩

/-- **Definition 2.1.** The `k`-IGT dynamics as a (one-way) population protocol. -/
def igt (k : ℕ) : Protocol (Strat k) where
  δ p q := match p with
    | .gtft j => (.gtft (if q = .ad then dec j else inc j), q)
    | p => (p, q)

variable {A : Type*} [Fintype A] [DecidableEq A] (τ : A → Kind)

/-- Configurations in which agent `u` has kind `τ u`. -/
abbrev Cfg := {C : Config A (Strat k) // ∀ u, (C u).kind = τ u}

/-- The number `m` of GTFT agents. -/
def numGTFT : ℕ := (univ.filter fun u => τ u = .gtft).card

/-- The number `βn` of AD agents. -/
def numAD : ℕ := (univ.filter fun u => τ u = .ad).card

variable {τ}

lemma igt_kind_fst (p q : Strat k) : ((igt k).δ p q).1.kind = p.kind := by
  cases p <;> rfl

lemma igt_snd (p q : Strat k) : ((igt k).δ p q).2 = q := by
  cases p <;> rfl

/-- One interaction of the `k`-IGT dynamics: initiator `u`, responder `v`. -/
def step (C : Cfg (k := k) τ) (u v : A) : Cfg (k := k) τ :=
  ⟨(igt k).interact C.1 u v, by
    intro x
    unfold Protocol.interact
    split_ifs with h1 h2
    · subst h1; rw [igt_kind_fst]; exact C.2 x
    · subst h2; rw [igt_snd]; exact C.2 x
    · exact C.2 x⟩

omit [Fintype A] [DecidableEq A] in
lemma gtft_iff (C : Cfg (k := k) τ) (u : A) : τ u = .gtft ↔ ∃ j, C.1 u = .gtft j := by
  rw [← C.2 u]
  cases C.1 u <;> simp [Strat.kind]

/-- The count vector `z = (z_1, …, z_k)` of a configuration. -/
def counts (C : Cfg (k := k) τ) : Simplex k (numGTFT τ) :=
  ⟨fun j => (univ.filter fun u => C.1 u = .gtft j).card, by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm, numGTFT, Finset.card_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : τ u = .gtft
    · obtain ⟨j, hj⟩ := (gtft_iff C u).1 h
      simp [hj, h]
    · have : ∀ j, C.1 u ≠ .gtft j := fun j hj => h ((gtft_iff C u).2 ⟨j, hj⟩)
      simp [this, h]⟩

/-- A `Simplex` vector satisfying the coordinate equations of a move is that move. -/
lemma Simplex.eq_move_of {m : ℕ} {x y : Simplex k m} {i j : Fin k} (hi : 0 < x.1 i)
    (h : ∀ l, y.1 l + (if l = i then 1 else 0) = x.1 l + (if l = j then 1 else 0)) :
    y = x.move i j := by
  by_cases hij : i = j
  · subst hij
    rw [x.move_of_not (by simp)]
    apply Subtype.ext; funext l; have := h l; omega
  · apply Subtype.ext; funext l
    have h1 := h l
    have h2 := x.move_val_add hi hij l
    omega

lemma counts_update (C : Cfg (k := k) τ) {u : A} {j : Fin k} (hu : C.1 u = .gtft j) (j' : Fin k)
    (D : Cfg (k := k) τ) (hD : D.1 = Function.update C.1 u (.gtft j')) :
    counts D = (counts C).move j j' := by
  have hpos : 0 < (counts C).1 j :=
    Finset.card_pos.2 ⟨u, by simp [hu]⟩
  refine Simplex.eq_move_of hpos fun l => ?_
  simp only [counts, Finset.card_filter, hD]
  have e1 := (Finset.add_sum_erase univ
    (fun x => if Function.update C.1 u (Strat.gtft j') x = Strat.gtft l then 1 else 0)
    (Finset.mem_univ u)).symm
  have e2 := (Finset.add_sum_erase univ
    (fun x => if C.1 x = Strat.gtft l then 1 else 0) (Finset.mem_univ u)).symm
  have e3 : ∑ x ∈ univ.erase u, (if Function.update C.1 u (Strat.gtft j') x = Strat.gtft l
      then 1 else 0) = ∑ x ∈ univ.erase u, (if C.1 x = Strat.gtft l then 1 else 0) :=
    Finset.sum_congr rfl fun x hx => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [e1, e2, e3]
  generalize (∑ x ∈ univ.erase u, (if C.1 x = Strat.gtft l then 1 else 0)) = S
  simp only [Function.update_self, hu, Strat.gtft.injEq]
  split_ifs <;> subst_vars <;> first | rfl | omega

/-- The level change of an interaction. -/
def newLevel (j : Fin k) (q : Strat k) : Fin k := if q = .ad then dec j else inc j

omit [Fintype A] in
lemma step_eq_update (C : Cfg (k := k) τ) {u : A} {j : Fin k} (hu : C.1 u = .gtft j) (v : A) :
    (step C u v).1 = Function.update C.1 u (.gtft (newLevel j (C.1 v))) := by
  funext x
  simp only [step, Protocol.interact, Function.update_apply]
  by_cases hxu : x = u
  · subst hxu
    simp [hu, igt, newLevel]
  · simp only [hxu, ↓reduceIte]
    split_ifs with hxv
    · subst hxv; rw [igt_snd]
    · rfl

omit [Fintype A] in
lemma step_of_not_gtft (C : Cfg (k := k) τ) {u : A} (hu : τ u ≠ .gtft) (v : A) :
    step C u v = C := by
  apply Subtype.ext
  funext x
  have hC : ∀ j, C.1 u ≠ .gtft j := fun j hj => hu ((gtft_iff C u).2 ⟨j, hj⟩)
  have hδ : (igt k).δ (C.1 u) (C.1 v) = (C.1 u, C.1 v) := by
    cases h : C.1 u with
    | gtft j => exact absurd h (hC j)
    | _ => rfl
  simp only [step, Protocol.interact, hδ]
  split_ifs with h1 h2 <;> subst_vars <;> rfl

/-- The counts after an interaction. -/
lemma counts_step (C : Cfg (k := k) τ) {u : A} {j : Fin k} (hu : C.1 u = .gtft j) (v : A) :
    counts (step C u v) = (counts C).move j (newLevel j (C.1 v)) :=
  counts_update C hu _ _ (step_eq_update C hu v)

/-! ## Lumping the agent-level chain to the Ehrenfest process -/

variable {Ω : Type*} [Fintype Ω]

/-- The agent-level Markov chain of the `k`-IGT dynamics under a scheduler that draws the pair
`pr ω = (initiator, responder)` with probability `w` for each `ω : Ω`. -/
noncomputable def schedKernel (τ : A → Kind) (w : ℝ) (pr : Ω → A × A) :
    Matrix (Cfg (k := k) τ) (Cfg (k := k) τ) ℝ :=
  randomMap (fun _ => w) (fun ω C => step C (pr ω).1 (pr ω).2)

lemma sum_ite_succ (i : Fin k) (c : Fin k → ℝ) (hc : c i = 0) :
    ∑ j : Fin k, (if j.val = i.val + 1 then c j else 0) = c (inc i) := by
  by_cases h : i.val + 1 < k
  · rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · have : inc i = ⟨i.val + 1, h⟩ := Fin.ext (by simp [inc]; omega)
      simp [this]
    · intro j _ hj; rw [ite_eq_right]; intro h'; exact hj (Fin.ext h')
    · simp
  · have : inc i = i := Fin.ext (by simp [inc]; omega)
    rw [this, hc]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; omega

lemma sum_ite_pred (i : Fin k) (c : Fin k → ℝ) (hc : c i = 0) :
    ∑ j : Fin k, (if i.val = j.val + 1 then c j else 0) = c (dec i) := by
  by_cases h : 0 < i.val
  · rw [Finset.sum_eq_single (dec i)]
    · rw [ite_eq_left (by simp [dec]; omega)]
    · intro j _ hj; rw [ite_eq_right]; intro h'; exact hj (Fin.ext (by simp [dec]; omega))
    · simp
  · have : dec i = i := Fin.ext (by simp [dec]; omega)
    rw [this, hc]
    exact Finset.sum_eq_zero fun j _ => by rw [ite_eq_right]; omega

lemma sum_ehrRate_mul {m : ℕ} (a b : ℝ) (g : Simplex k m → ℝ) (x : Simplex k m) (i : Fin k) :
    ∑ j, ehrRate a b i j * (g (x.move i j) - g x) =
      a * (g (x.move i (inc i)) - g x) + b * (g (x.move i (dec i)) - g x) := by
  have hc : g (x.move i i) - g x = 0 := by rw [x.move_of_not (by simp)]; ring
  have h : ∀ j, ehrRate a b i j * (g (x.move i j) - g x) =
      (if j.val = i.val + 1 then a * (g (x.move i j) - g x) else 0) +
      (if i.val = j.val + 1 then b * (g (x.move i j) - g x) else 0) := by
    intro j; unfold ehrRate; split_ifs <;> first | (exfalso; omega) | ring
  simp_rw [h, Finset.sum_add_distrib]
  rw [sum_ite_succ i (fun j => a * (g (x.move i j) - g x)) (by simp [hc]),
    sum_ite_pred i (fun j => b * (g (x.move i j) - g x)) (by simp [hc])]

/-- **The count process of the `k`-IGT dynamics is an Ehrenfest process** (Section 2.2.1),
for a general uniform scheduler in which every GTFT initiator has `cAD` AD partners and `cN`
other partners. -/
theorem schedKernel_lump {w : ℝ} {pr : Ω → A × A} (hw : w * Fintype.card Ω = 1) {cAD cN : ℕ}
    (hAD : ∀ u, τ u = .gtft → (univ.filter fun ω => (pr ω).1 = u ∧ τ (pr ω).2 = .ad).card = cAD)
    (hN : ∀ u, τ u = .gtft → (univ.filter fun ω => (pr ω).1 = u ∧ τ (pr ω).2 ≠ .ad).card = cN)
    (g : Simplex k (numGTFT τ) → ℝ) (C : Cfg (k := k) τ) :
    (ehrenfest k (w * cN * numGTFT τ) (w * cAD * numGTFT τ) (numGTFT τ) *ᵥ g) (counts C) =
      (schedKernel τ w pr *ᵥ (g ∘ counts)) C := by
  -- level-wise increments
  let U : Fin k → ℝ := fun j => g ((counts C).move j (inc j)) - g (counts C)
  let D : Fin k → ℝ := fun j => g ((counts C).move j (dec j)) - g (counts C)
  let F : Strat k → ℝ := fun s => match s with
    | .gtft j => cAD * D j + cN * U j
    | _ => 0
  -- the right-hand side
  have hR : (schedKernel τ w pr *ᵥ (g ∘ counts)) C = g (counts C) + w * ∑ u, F (C.1 u) := by
    rw [schedKernel, randomMap_mulVec]
    have hΔ : ∀ ω, g (counts (step C (pr ω).1 (pr ω).2)) = g (counts C) +
        (match C.1 (pr ω).1 with
          | .gtft j => if τ (pr ω).2 = .ad then D j else U j
          | _ => 0) := by
      intro ω
      cases hu : C.1 (pr ω).1 with
      | gtft j =>
        simp only
        rw [counts_step C hu]
        have hk : (C.1 (pr ω).2 = .ad) ↔ τ (pr ω).2 = .ad := by
          rw [← C.2 (pr ω).2]; cases C.1 (pr ω).2 <;> simp [Strat.kind]
        by_cases hv : τ (pr ω).2 = .ad
        · simp [hv, newLevel, hk.2 hv, D]
        · simp [hv, newLevel, mt hk.1 hv, U]
      | ac =>
        have : τ (pr ω).1 ≠ .gtft := by rw [← C.2]; simp [hu, Strat.kind]
        simp [step_of_not_gtft C this]
      | ad =>
        have : τ (pr ω).1 ≠ .gtft := by rw [← C.2]; simp [hu, Strat.kind]
        simp [step_of_not_gtft C this]
    simp only [Function.comp, hΔ, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hw, one_mul]
    congr 1
    congr 1
    rw [← Finset.sum_fiberwise univ (fun ω => (pr ω).1)]
    refine Finset.sum_congr rfl fun u _ => ?_
    cases hu : C.1 u with
    | gtft j =>
      have hg : τ u = .gtft := (gtft_iff C u).2 ⟨j, hu⟩
      have e : ∀ ω ∈ univ.filter (fun ω => (pr ω).1 = u),
          (match C.1 (pr ω).1 with
            | .gtft j => if τ (pr ω).2 = .ad then D j else U j
            | _ => 0) = if τ (pr ω).2 = .ad then D j else U j := by
        intro ω hω
        rw [(Finset.mem_filter.1 hω).2, hu]
      rw [Finset.sum_congr rfl e, Finset.sum_ite, Finset.sum_const, Finset.sum_const,
        Finset.filter_filter, Finset.filter_filter, hAD u hg, hN u hg]
      simp [F, nsmul_eq_mul]
    | ac =>
      refine Finset.sum_eq_zero fun ω hω => ?_
      rw [(Finset.mem_filter.1 hω).2, hu]
    | ad =>
      refine Finset.sum_eq_zero fun ω hω => ?_
      rw [(Finset.mem_filter.1 hω).2, hu]
  -- group the agents by level
  have hF : ∑ u, F (C.1 u) = ∑ j, ((counts C).1 j : ℝ) * (cAD * D j + cN * U j) := by
    have : ∀ u, F (C.1 u) = ∑ j, if C.1 u = .gtft j then cAD * D j + cN * U j else 0 := by
      intro u
      cases C.1 u with
      | gtft j => simp [F]
      | ac => simp [F]
      | ad => simp [F]
    simp_rw [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    rfl
  -- the left-hand side
  rw [hR, hF, ehrenfest, urnKernel_mulVec]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsum : ∑ j, ehrRate (w * cN * (numGTFT τ)) (w * cAD * (numGTFT τ)) i j * ((counts C).1 i / (numGTFT τ)) * (g ((counts C).move i j) - g (counts C))
      = ((counts C).1 i / (numGTFT τ)) * ∑ j, ehrRate (w * cN * (numGTFT τ)) (w * cAD * (numGTFT τ)) i j * (g ((counts C).move i j) - g (counts C)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsum, sum_ehrRate_mul]
  rcases Nat.eq_zero_or_pos (numGTFT τ) with hm | hm
  · have : (counts C).1 i = 0 := by
      have h := Finset.single_le_sum (f := (counts C).1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      rw [(counts C).2] at h; omega
    simp [this]
  · have hm' : (numGTFT τ : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [U, D]
    field_simp
    ring

/-- The `t`-step law of the count process is the `t`-step law of the Ehrenfest process. -/
theorem schedKernel_pow_counts {w : ℝ} {pr : Ω → A × A} (hw : w * Fintype.card Ω = 1)
    {cAD cN : ℕ}
    (hAD : ∀ u, τ u = .gtft → (univ.filter fun ω => (pr ω).1 = u ∧ τ (pr ω).2 = .ad).card = cAD)
    (hN : ∀ u, τ u = .gtft → (univ.filter fun ω => (pr ω).1 = u ∧ τ (pr ω).2 ≠ .ad).card = cN)
    (t : ℕ) (C : Cfg (k := k) τ) (y : Simplex k (numGTFT τ)) :
    ∑ D ∈ univ.filter (fun D => counts D = y), (schedKernel τ w pr ^ t) C D =
      (ehrenfest k (w * cN * numGTFT τ) (w * cAD * numGTFT τ) (numGTFT τ) ^ t) (counts C) y := by
  rw [pow_apply_eq_mulVec (ehrenfest k (w * cN * numGTFT τ) (w * cAD * numGTFT τ) (numGTFT τ) ^ t)
    (counts C) y, pow_mulVec_comp_of_lump counts
    (fun g C => schedKernel_lump hw hAD hN g C)]
  simp [mulVec, dotProduct, Finset.sum_filter]

/-! ### The two schedulers -/

lemma card_filter_fst_prod (u : A) (P : A → Prop) [DecidablePred P] :
    (univ.filter fun ω : A × A => ω.1 = u ∧ P ω.2).card = (univ.filter P).card := by
  refine Finset.card_bij (fun ω _ => ω.2) (fun ω hω => by simp_all) ?_ ?_
  · intro ω₁ h₁ ω₂ h₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Prod.ext (h₁.1.trans h₂.1.symm) h
  · intro v hv
    exact ⟨(u, v), by simpa using hv, rfl⟩

lemma card_filter_fst_pairs (u : A) (P : A → Prop) [DecidablePred P] :
    (univ.filter fun ω : Pairs A => ω.1.1 = u ∧ P ω.1.2).card =
      (univ.filter fun v => v ≠ u ∧ P v).card := by
  refine Finset.card_bij (fun ω _ => ω.1.2) ?_ ?_ ?_
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ⟨fun h => ω.2 (hω.1.trans h.symm), hω.2⟩
  · intro ω₁ h₁ ω₂ h₂ h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Subtype.ext (Prod.ext (h₁.1.trans h₂.1.symm) h)
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact ⟨⟨(u, v), Ne.symm hv.1⟩, by simpa using hv.2, rfl⟩

lemma card_pairs : Fintype.card (Pairs A) = Fintype.card A * (Fintype.card A - 1) := by
  rw [Fintype.card_subtype]
  have : (univ.filter fun p : A × A => p.1 ≠ p.2) = (univ : Finset A).offDiag := by
    ext p; simp
  rw [this, Finset.offDiag_card, Finset.card_univ, Nat.mul_sub, mul_one]

lemma numAD_add_numGTFT_le : numAD τ + numGTFT τ ≤ Fintype.card A := by
  rw [numAD, numGTFT, ← Finset.card_union_of_disjoint]
  · exact Finset.card_le_univ _
  · exact Finset.disjoint_filter.2 fun u _ h1 h2 => by rw [h1] at h2; cases h2

omit [DecidableEq A] in
lemma card_filter_not_ad : (univ.filter fun v => τ v ≠ .ad).card = Fintype.card A - numAD τ := by
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset A)) (fun v => τ v = .ad)
  simp only [ne_eq, numAD, Finset.card_univ] at this ⊢
  omega

variable (τ) in
/-- **Sampling with replacement**: initiator and responder are drawn independently and
uniformly from all `n` agents (this is the model behind the transition probabilities (5)). -/
noncomputable def replKernel : Matrix (Cfg (k := k) τ) (Cfg (k := k) τ) ℝ :=
  schedKernel τ (1 / (Fintype.card A : ℝ) ^ 2) (id : A × A → A × A)

variable (τ) in
/-- **The standard population-protocol scheduler**: an ordered pair of *distinct* agents is
drawn uniformly (as in CSLib's `uniformKernel`). -/
noncomputable def distinctKernel : Matrix (Cfg (k := k) τ) (Cfg (k := k) τ) ℝ :=
  schedKernel τ (1 / (Fintype.card (Pairs A) : ℝ)) (Subtype.val : Pairs A → A × A)

/-- The fractions `β = |AD| / n` and `γ = |GTFT| / n` of the `(α, β, γ)` population. -/
noncomputable def fracAD (τ : A → Kind) : ℝ := numAD τ / Fintype.card A
/-- See `fracAD`. -/
noncomputable def fracGTFT (τ : A → Kind) : ℝ := numGTFT τ / Fintype.card A

/-- **Section 2.4, with replacement.** The count process of the `k`-IGT dynamics is the
`(k, γ(1-β), γβ, m)`-Ehrenfest process. -/
theorem replKernel_counts (hn : 0 < Fintype.card A) (t : ℕ) (C : Cfg (k := k) τ)
    (y : Simplex k (numGTFT τ)) :
    ∑ D ∈ univ.filter (fun D => counts D = y), (replKernel τ ^ t) C D =
      (ehrenfest k (fracGTFT τ * (1 - fracAD τ)) (fracGTFT τ * fracAD τ) (numGTFT τ) ^ t)
        (counts C) y := by
  have hn' : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hle := numAD_add_numGTFT_le (τ := τ)
  have h := schedKernel_pow_counts (k := k) (τ := τ) (w := 1 / (Fintype.card A : ℝ) ^ 2)
    (pr := (id : A × A → A × A)) (cAD := numAD τ) (cN := Fintype.card A - numAD τ)
    (by rw [Fintype.card_prod]; push_cast; field_simp)
    (fun u _ => by simpa [numAD] using card_filter_fst_prod u (fun v => τ v = .ad))
    (fun u _ => by simpa [card_filter_not_ad] using card_filter_fst_prod u (fun v => τ v ≠ .ad))
    t C y
  have ea : 1 / (Fintype.card A : ℝ) ^ 2 * ((Fintype.card A - numAD τ : ℕ) : ℝ) * numGTFT τ =
      fracGTFT τ * (1 - fracAD τ) := by
    simp only [fracGTFT, fracAD]
    rw [Nat.cast_sub (by omega)]
    field_simp
  have eb : 1 / (Fintype.card A : ℝ) ^ 2 * (numAD τ : ℝ) * numGTFT τ =
      fracGTFT τ * fracAD τ := by
    simp only [fracGTFT, fracAD]
    field_simp
  rw [replKernel, h, ea, eb]

/-- **Section 2.4, standard scheduler (distinct agents).** The count process of the `k`-IGT
dynamics is the `(k, a', b', m)`-Ehrenfest process with `a' = γ (n-1-βn)/(n-1)`,
`b' = γ βn/(n-1)`. -/
theorem distinctKernel_counts (hn : 2 ≤ Fintype.card A) (t : ℕ) (C : Cfg (k := k) τ)
    (y : Simplex k (numGTFT τ)) :
    ∑ D ∈ univ.filter (fun D => counts D = y), (distinctKernel τ ^ t) C D =
      (ehrenfest k (fracGTFT τ * ((Fintype.card A - 1 - numAD τ : ℕ) / (Fintype.card A - 1 : ℝ)))
        (fracGTFT τ * (numAD τ / (Fintype.card A - 1 : ℝ))) (numGTFT τ) ^ t) (counts C) y := by
  have hn1 : (Fintype.card A - 1 : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hn
    linarith
  have hn' : (Fintype.card A : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ Fintype.card A := by exact_mod_cast hn
    linarith
  have hP : (Fintype.card (Pairs A) : ℝ) = Fintype.card A * (Fintype.card A - 1) := by
    rw [card_pairs, Nat.cast_mul, Nat.cast_sub (by omega)]; simp
  have hle := numAD_add_numGTFT_le (τ := τ)
  have h := schedKernel_pow_counts (k := k) (τ := τ) (w := 1 / (Fintype.card (Pairs A) : ℝ))
    (pr := (Subtype.val : Pairs A → A × A)) (cAD := numAD τ)
    (cN := Fintype.card A - 1 - numAD τ)
    (by rw [hP]; field_simp)
    (fun u hu => by
      rw [card_filter_fst_pairs u (fun v => τ v = .ad), numAD]
      congr 1; ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => h.2, fun h => ⟨fun e => (by subst e; rw [hu] at h; cases h), h⟩⟩)
    (fun u hu => by
      rw [card_filter_fst_pairs u (fun v => τ v ≠ .ad)]
      have e : (univ.filter fun v => v ≠ u ∧ τ v ≠ .ad) =
          (univ.filter fun v => τ v ≠ .ad).erase u := by
        ext v; simp
      rw [e, Finset.card_erase_of_mem (by simp [hu]), card_filter_not_ad]
      omega)
    t C y
  have ea : 1 / (Fintype.card (Pairs A) : ℝ) * ((Fintype.card A - 1 - numAD τ : ℕ) : ℝ) *
      numGTFT τ = fracGTFT τ * ((Fintype.card A - 1 - numAD τ : ℕ) / (Fintype.card A - 1 : ℝ)) := by
    simp only [fracGTFT]
    rw [hP]
    field_simp
  have eb : 1 / (Fintype.card (Pairs A) : ℝ) * (numAD τ : ℝ) * numGTFT τ =
      fracGTFT τ * (numAD τ / (Fintype.card A - 1 : ℝ)) := by
    simp only [fracGTFT]
    rw [hP]
    field_simp
  rw [distinctKernel, h, ea, eb]

/-- **Theorem 2.7 (stationary part)**, in the model of Section 2.2.1 (responder drawn uniformly
from all agents): if `0 < β` and there are GTFT agents, the count process `{z^t}` of the `k`-IGT
dynamics is the `(k, γ(1-β), γβ, m)`-Ehrenfest process, and its unique stationary distribution
is multinomial with parameters `m` and `p_j ∝ (1/β - 1)^(j-1)`. -/
theorem theorem_2_7_stationary (hk : 2 ≤ k) (hAD : 0 < numAD τ) (hm : 0 < numGTFT τ) :
    (∀ t (C : Cfg (k := k) τ) (y : Simplex k (numGTFT τ)),
      ∑ D ∈ univ.filter (fun D => counts D = y), (replKernel τ ^ t) C D =
        (ehrenfest k (fracGTFT τ * (1 - fracAD τ)) (fracGTFT τ * fracAD τ) (numGTFT τ) ^ t)
          (counts C) y) ∧
    IsStationary (ehrenfest k (fracGTFT τ * (1 - fracAD τ)) (fracGTFT τ * fracAD τ) (numGTFT τ))
      (multinomialPMF (ehrParam k (1 / fracAD τ - 1))) ∧
    ∀ π, IsDistribution π →
      IsStationary (ehrenfest k (fracGTFT τ * (1 - fracAD τ)) (fracGTFT τ * fracAD τ)
        (numGTFT τ)) π → π = multinomialPMF (ehrParam k (1 / fracAD τ - 1)) := by
  have hle := numAD_add_numGTFT_le (τ := τ)
  have hn : 0 < Fintype.card A := by omega
  have hn' : (0 : ℝ) < Fintype.card A := by exact_mod_cast hn
  have hβ0 : 0 < fracAD τ := div_pos (by exact_mod_cast hAD) hn'
  have hβ1 : fracAD τ < 1 := by
    rw [fracAD, div_lt_one hn']; exact_mod_cast (show numAD τ < Fintype.card A by omega)
  have hγ0 : 0 < fracGTFT τ := div_pos (by exact_mod_cast hm) hn'
  have hγ1 : fracGTFT τ ≤ 1 := by
    rw [fracGTFT, div_le_one hn']; exact_mod_cast (show numGTFT τ ≤ Fintype.card A by omega)
  have ha : 0 < fracGTFT τ * (1 - fracAD τ) := mul_pos hγ0 (by linarith)
  have hb : 0 < fracGTFT τ * fracAD τ := mul_pos hγ0 hβ0
  have hab : fracGTFT τ * (1 - fracAD τ) + fracGTFT τ * fracAD τ ≤ 1 := by nlinarith
  have hlam : fracGTFT τ * (1 - fracAD τ) / (fracGTFT τ * fracAD τ) = 1 / fracAD τ - 1 := by
    field_simp
  refine ⟨fun t C y => replKernel_counts hn t C y, ?_, fun π hπ hst => ?_⟩
  · rw [← hlam]; exact ehrenfest_isStationary ha hb hab (by omega)
  · rw [← hlam]; exact ehrenfest_stationary_unique (by omega) ha hb hab π hπ hst

/-! ### The formula of Theorem 2.7 fails for the standard (distinct-pair) scheduler -/

/-- Three agents: one AD agent and two GTFT agents (`β = 1/3`, `γ = 2/3`). -/
def τ₀ : Fin 3 → Kind := ![.ad, .gtft, .gtft]

lemma numAD_τ₀ : numAD τ₀ = 1 := by decide
lemma numGTFT_τ₀ : numGTFT τ₀ = 2 := by decide

lemma multinomialPMF_base_two (p : Fin 2 → ℝ) :
    multinomialPMF (m := 2) p (Simplex.base (by norm_num)) = p 0 ^ 2 := by
  rw [multinomialPMF_eq]
  simp [Simplex.base, Fin.prod_univ_two, Pi.single_apply, Nat.factorial]
  ring

/-- **The formula of Theorem 2.7 needs sampling with replacement.** For `k = 2` and the
population `τ₀` (one AD, two GTFT agents) under the standard population-protocol scheduler
(ordered pairs of distinct agents), the count process is the `(2, 1/3, 1/3, 2)`-Ehrenfest
process, whose stationary distribution is *not* the multinomial distribution with
`p_j ∝ (1/β - 1)^(j-1)` claimed in Theorem 2.7 (its ratio is `1`, not `1/β - 1 = 2`). -/
theorem distinct_counterexample :
    fracAD τ₀ = 1 / 3 ∧
    (∀ t (C : Cfg (k := 2) τ₀) (y : Simplex 2 (numGTFT τ₀)),
      ∑ D ∈ univ.filter (fun D => counts D = y), (distinctKernel τ₀ ^ t) C D =
        (ehrenfest 2 (1 / 3) (1 / 3) (numGTFT τ₀) ^ t) (counts C) y) ∧
    ¬ IsStationary (ehrenfest 2 (1 / 3) (1 / 3) (numGTFT τ₀))
      (multinomialPMF (ehrParam 2 (1 / fracAD τ₀ - 1))) := by
  have hβ : fracAD τ₀ = 1 / 3 := by
    simp [fracAD, numAD_τ₀]
  refine ⟨hβ, fun t C y => ?_, fun hst => ?_⟩
  · have e1 : fracGTFT τ₀ * (((Fintype.card (Fin 3) - 1 - numAD τ₀ : ℕ) : ℝ) /
        (Fintype.card (Fin 3) - 1 : ℝ)) = 1 / 3 := by
      simp [fracGTFT, numGTFT_τ₀, numAD_τ₀]; norm_num
    have e2 : fracGTFT τ₀ * (numAD τ₀ / (Fintype.card (Fin 3) - 1 : ℝ)) = 1 / 3 := by
      simp [fracGTFT, numGTFT_τ₀, numAD_τ₀]; norm_num
    exact (distinctKernel_counts (k := 2) (τ := τ₀) (by simp) t C y).trans (by rw [e1, e2])
  · rw [numGTFT_τ₀] at hst
    have h := ehrenfest_stationary_unique (k := 2) (m := 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 3)
      (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num) _
      (isDistribution_multinomialPMF (fun j => (ehrParam_pos (by norm_num)
        (by rw [hβ]; norm_num) j).le) (sum_ehrParam (by norm_num) (by rw [hβ]; norm_num))) hst
    have h0 := congrFun h (Simplex.base (by norm_num))
    rw [multinomialPMF_base_two, multinomialPMF_base_two, hβ] at h0
    simp [ehrParam, Fin.sum_univ_two] at h0

/-- Non-vacuity: the hypotheses of `theorem_2_7_stationary` hold for `τ₀` (`β = 1/3`). -/
example : IsStationary (ehrenfest 2 (fracGTFT τ₀ * (1 - fracAD τ₀)) (fracGTFT τ₀ * fracAD τ₀)
    (numGTFT τ₀)) (multinomialPMF (ehrParam 2 (1 / fracAD τ₀ - 1))) :=
  (theorem_2_7_stationary (k := 2) (τ := τ₀) le_rfl (by decide) (by decide)).2.1

end Podc.PPGameDynamics
