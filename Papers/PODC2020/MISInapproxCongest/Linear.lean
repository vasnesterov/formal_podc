import Papers.PODC2020.MISInapproxCongest.IndepSet
import Podc.Foundations.InformationTheory.Agreement
import Podc.Computability.CommunicationComplexity.Blackboard

/-!
# Section 4: the family of lower bound graphs `G_x̄` for the linear lower bound

The construction is generic in the code: messages `K` (the `k` indices of the input strings),
positions `P` (`|P| = M`, the paper's `ℓ + α`), alphabet `A`, and a code `c : K → P → A` such
that distinct codewords agree in at most `a` positions (the paper's Property 3 bound `α`). In the
paper `P = A = [ℓ + α]`, `K = Σ^α` and `c` is the Reed–Solomon code of Theorem 4.

Nodes are `Node t K P A = Fin t × (K ⊕ P × A)`: `(i, inl m)` is `v^i_m ∈ A^i`, `(i, inr (h, r))`
is `σ^i_{(h,r)} ∈ C^i_h`. Edges (`graph c`):
* `A^i` is a clique; `v^i_m` is adjacent to all of `Code^i` except `Code^i_m = {σ^i_{(h, c m h)}}`;
* each `C^i_h` is a clique, and `C^i_h`, `C^j_h` (`i ≠ j`) are joined by all edges except the
  perfect matching `σ^i_{(h,r)}`–`σ^j_{(h,r)}`. Both rules together: two code nodes are adjacent
  iff they have the same position `h` and different symbols `r`.
The weight of `v^i_m` is `W` (the paper's `ℓ`) if `x^i_m = 1` and `1` otherwise; code nodes have
weight `1`.

Main results (generic): Properties 1–3, Claim 4 (`card_code_le`), Corollary 2
(`corollary2`), Claims 1/3 (`claim3`), Claims 2/5 (`claim5_generic`, `claim2_generic`).
-/

set_option linter.unusedSectionVars false

namespace Podc.MISInapproxCongest

open Finset Cslib Cslib.CommunicationComplexity

/-- Nodes of the graph `G` with `t` copies of `H`. -/
abbrev Node (t : ℕ) (K P A : Type*) := Fin t × (K ⊕ P × A)

section Graph

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A]

/-- Adjacency of the fixed graph construction `G` of Section 4.1. -/
def gAdj (c : K → P → A) : Node t K P A → Node t K P A → Prop
  | ⟨i, .inl m⟩, ⟨j, .inl m'⟩ => i = j ∧ m ≠ m'
  | ⟨i, .inl m⟩, ⟨j, .inr (h, r)⟩ => i = j ∧ r ≠ c m h
  | ⟨i, .inr (h, r)⟩, ⟨j, .inl m⟩ => i = j ∧ r ≠ c m h
  | ⟨_, .inr (h, r)⟩, ⟨_, .inr (h', r')⟩ => h = h' ∧ r ≠ r'

/-- The fixed graph construction `G` of Section 4.1 (`t` copies `H^i` of the base graph `H`,
code gadgets of different copies joined by complete bipartite graphs minus a perfect matching). -/
def graph (c : K → P → A) : SimpleGraph (Node t K P A) where
  Adj := gAdj c
  symm := ⟨by
    rintro ⟨i, u | ⟨h, r⟩⟩ ⟨j, v | ⟨h', r'⟩⟩ <;> simp only [gAdj] <;> intro h <;>
      first | exact ⟨h.1.symm, Ne.symm h.2⟩ | exact ⟨h.1.symm, h.2⟩⟩
  loopless := ⟨by rintro ⟨i, u | ⟨h, r⟩⟩ <;> simp [gAdj]⟩

instance (c : K → P → A) : DecidableRel (graph (t := t) c).Adj := fun u v =>
  match u, v with
  | ⟨i, .inl m⟩, ⟨j, .inl m'⟩ => inferInstanceAs (Decidable (i = j ∧ m ≠ m'))
  | ⟨i, .inl m⟩, ⟨j, .inr (h, r)⟩ => inferInstanceAs (Decidable (i = j ∧ r ≠ c m h))
  | ⟨i, .inr (h, r)⟩, ⟨j, .inl m⟩ => inferInstanceAs (Decidable (i = j ∧ r ≠ c m h))
  | ⟨_, .inr (h, r)⟩, ⟨_, .inr (h', r')⟩ => inferInstanceAs (Decidable (h = h' ∧ r ≠ r'))

@[simp] theorem graph_adj_AA (c : K → P → A) (i j : Fin t) (m m' : K) :
    (graph c).Adj (i, .inl m) (j, .inl m') ↔ i = j ∧ m ≠ m' := Iff.rfl

@[simp] theorem graph_adj_AC (c : K → P → A) (i j : Fin t) (m : K) (h : P) (r : A) :
    (graph c).Adj (i, .inl m) (j, .inr (h, r)) ↔ i = j ∧ r ≠ c m h := Iff.rfl

@[simp] theorem graph_adj_CA (c : K → P → A) (i j : Fin t) (m : K) (h : P) (r : A) :
    (graph c).Adj (i, .inr (h, r)) (j, .inl m) ↔ i = j ∧ r ≠ c m h := Iff.rfl

@[simp] theorem graph_adj_CC (c : K → P → A) (i j : Fin t) (h h' : P) (r r' : A) :
    (graph c).Adj (i, .inr (h, r)) (j, .inr (h', r')) ↔ h = h' ∧ r ≠ r' := Iff.rfl

/-- Node weights of `G_x̄`: `v^i_m` has weight `W` if `x^i_m = 1` and `1` otherwise; all code
nodes have weight `1`. -/
def weight (W : ℕ) (x : Fin t → K → Bool) : Node t K P A → ℕ
  | ⟨i, .inl m⟩ => if x i m then W else 1
  | ⟨_, .inr _⟩ => 1

/-- `Code^i_m`, the code nodes of copy `i` representing the codeword of `m`. -/
def codeword [Fintype P] (c : K → P → A) (i : Fin t) (m : K) : Finset (Node t K P A) :=
  univ.image fun h => (i, .inr (h, c m h))

/-- The independent set of Property 1: `⋃_i Code^i_m ∪ {v^i_m | i ∈ [t]}`. -/
def commonSet [Fintype P] (c : K → P → A) (m : K) : Finset (Node t K P A) :=
  (univ.image fun i => ((i, .inl m) : Node t K P A)) ∪ univ.biUnion fun i => codeword c i m

/-- **Property 1.** For every `m`, `⋃_i Code^i_m ∪ {v^i_m | i ∈ [t]}` is independent. -/
theorem property1 [Fintype P] (c : K → P → A) (m : K) :
    IsIndep (graph (t := t) c) (commonSet c m) := by
  intro u hu v hv
  simp only [commonSet, codeword, mem_union, mem_image, mem_univ, true_and, mem_biUnion] at hu hv
  rcases hu with ⟨i, rfl⟩ | ⟨i, h, rfl⟩ <;> rcases hv with ⟨j, rfl⟩ | ⟨j, h', rfl⟩ <;> simp
  rintro rfl; rfl

/-- **Property 2.** For `i ≠ j` and `m₁ ≠ m₂`, at every position where the codewords differ, the
two code nodes are adjacent; there are at least `M - a` such positions (so these edges form a
matching of size `≥ M - a`; the paper's `ℓ`). -/
theorem property2 [Fintype P] (c : K → P → A) (i j : Fin t) (m₁ m₂ : K) :
    (∀ h, c m₁ h ≠ c m₂ h → (graph c).Adj (i, .inr (h, c m₁ h)) (j, .inr (h, c m₂ h))) ∧
      Fintype.card P - agree (c m₁) (c m₂) ≤ (univ.filter fun h => c m₁ h ≠ c m₂ h).card := by
  refine ⟨fun h hne => by simpa using hne, ?_⟩
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset P))
    (fun h => c m₁ h = c m₂ h)
  simp only [card_univ] at this
  unfold agree
  simp only [ne_eq]
  omega

/-- **Property 3.** For `i ≠ j`, `m₁ ≠ m₂` and an independent set `I`, the number of positions `h`
with both `σ^i_{(h, C(m₁)_h)} ∈ I` and `σ^j_{(h, C(m₂)_h)} ∈ I` is at most the agreement of the two
codewords (hence `≤ a`). -/
theorem property3 [Fintype P] (c : K → P → A) {I : Finset (Node t K P A)}
    (hI : IsIndep (graph c) I) (i j : Fin t) (m₁ m₂ : K) :
    (univ.filter fun h => (i, .inr (h, c m₁ h)) ∈ I ∧ (j, .inr (h, c m₂ h)) ∈ I).card ≤
      agree (c m₁) (c m₂) := by
  unfold agree
  apply card_le_card
  intro h
  simp only [mem_filter, mem_univ, true_and]
  rintro ⟨h1, h2⟩
  by_contra hne
  exact hI _ h1 _ h2 (by simpa using hne)

end Graph

/-! ### Counting lemmas (Claim 4, Corollary 2) -/

section Counting

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A] [Fintype K]
  [Fintype P] [Fintype A] (c : K → P → A)

/-- The `A`-nodes of copy `i` in `I`. -/
def aPart (I : Finset (Node t K P A)) (i : Fin t) : Finset K :=
  univ.filter fun m => (i, .inl m) ∈ I

/-- The code nodes of copy `i` in `I`. -/
def cPart (I : Finset (Node t K P A)) (i : Fin t) : Finset (P × A) :=
  univ.filter fun hr => (i, .inr hr) ∈ I

variable {c} {I : Finset (Node t K P A)}

theorem card_aPart_le_one (hI : IsIndep (graph c) I) (i : Fin t) : (aPart I i).card ≤ 1 :=
  card_le_one.2 fun m hm m' hm' => by
    by_contra hne
    exact hI _ (mem_filter.1 hm).2 _ (mem_filter.1 hm').2 (by simp [hne])

/-- An independent set contains at most one node of each clique `C^i_h`, hence at most `M`
nodes of `Code^i`. -/
theorem card_cPart_le (hI : IsIndep (graph c) I) (i : Fin t) :
    (cPart I i).card ≤ Fintype.card P := by
  refine (card_le_card_of_injOn Prod.fst (fun _ _ => mem_coe.2 (mem_univ _)) ?_).trans (by simp)
  rintro ⟨h, r⟩ hhr ⟨h', r'⟩ hhr' (he : h = h')
  subst he
  by_contra hne
  have : r ≠ r' := fun e => hne (by rw [e])
  exact hI _ (mem_filter.1 hhr).2 _ (mem_filter.1 hhr').2 (by simp [this])

/-- If `v^i_m ∈ I`, every code node of copy `i` in `I` lies in `Code^i_m`. -/
theorem cPart_snd (hI : IsIndep (graph c) I) {i : Fin t} {m : K} (hm : (i, .inl m) ∈ I) :
    ∀ hr ∈ cPart I i, hr.2 = c m hr.1 := by
  rintro ⟨h, r⟩ hhr
  by_contra hne
  exact hI _ hm _ (mem_filter.1 hhr).2 (by simpa using hne)

private theorem le_one_add_choose_two (n : ℕ) : n ≤ 1 + n.choose 2 := by
  rcases n with _ | n
  · simp
  · rw [Nat.choose_succ_succ, Nat.choose_one_right]; omega

/-- **Claim 4** (sharp form). Let `Hs` be a set of copies and `mm i` pairwise distinct messages
with `v^i_{mm i} ∈ I` for `i ∈ Hs`, where distinct codewords agree in at most `a` positions.
Then `I` contains at most `M + a · (|Hs| choose 2)` code nodes of the copies in `Hs`. -/
theorem card_code_le {a : ℕ} (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a)
    (hI : IsIndep (graph c) I) (Hs : Finset (Fin t)) (mm : Fin t → K)
    (hinj : Set.InjOn mm Hs) (hmem : ∀ i ∈ Hs, (i, .inl (mm i)) ∈ I) :
    ∑ i ∈ Hs, (cPart I i).card ≤ Fintype.card P + a * Hs.card.choose 2 := by
  classical
  set Q : Fin t → P → Prop := fun i h => (i, .inr (h, c (mm i) h)) ∈ I with hQ
  -- step 1: code nodes of copy `i` ↔ positions
  have h1 : ∀ i ∈ Hs, (cPart I i).card ≤ (univ.filter (Q i)).card := by
    intro i hi
    refine card_le_card_of_injOn Prod.fst ?_ ?_
    · rintro ⟨h, r⟩ hhr
      have e := cPart_snd hI (hmem i hi) _ hhr
      simp only at e
      subst e
      simpa [hQ] using (mem_filter.1 hhr).2
    · rintro ⟨h, r⟩ hhr ⟨h', r'⟩ hhr' (he : h = h')
      have e := cPart_snd hI (hmem i hi) _ hhr
      have e' := cPart_snd hI (hmem i hi) _ hhr'
      simp only at e e'
      subst he; rw [e, e']
  -- step 2: swap the sums
  have h2 : ∑ i ∈ Hs, (univ.filter (Q i)).card = ∑ h, (Hs.filter (Q · h)).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow Q
  -- step 3: per position, count pairs
  set Pr : Finset (Finset (Fin t)) := Hs.powersetCard 2
  have h3 : ∀ h, (Hs.filter (Q · h)).card ≤ 1 + (Pr.filter fun s => ∀ i ∈ s, Q i h).card := by
    intro h
    refine (le_one_add_choose_two _).trans (Nat.add_le_add_left ?_ 1)
    rw [← card_powersetCard]
    refine card_le_card fun s hs => ?_
    rw [mem_powersetCard] at hs
    refine mem_filter.2 ⟨mem_powersetCard.2 ⟨hs.1.trans (filter_subset _ _), hs.2⟩, ?_⟩
    intro i hi
    exact (mem_filter.1 (hs.1 hi)).2
  -- step 4: swap again
  have h4 : ∑ h, (Pr.filter fun s => ∀ i ∈ s, Q i h).card =
      ∑ s ∈ Pr, (univ.filter fun h => ∀ i ∈ s, Q i h).card :=
    (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun s h => ∀ i ∈ s, Q i h)).symm
  -- step 5: each pair shares at most `a` positions
  have h5 : ∀ s ∈ Pr, (univ.filter fun h => ∀ i ∈ s, Q i h).card ≤ a := by
    intro s hs
    rw [mem_powersetCard] at hs
    obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hs.2
    have hi : i ∈ Hs := hs.1 (by simp)
    have hj : j ∈ Hs := hs.1 (by simp)
    have hne : mm i ≠ mm j := fun e => hij (hinj hi hj e)
    refine le_trans (card_le_card fun h hh => ?_) (hc _ _ hne)
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, forall_eq_or_imp,
      forall_eq] at hh ⊢
    by_contra hne'
    exact hI _ hh.1 _ hh.2 (by simpa using hne')
  calc ∑ i ∈ Hs, (cPart I i).card ≤ ∑ i ∈ Hs, (univ.filter (Q i)).card := sum_le_sum h1
    _ = ∑ h, (Hs.filter (Q · h)).card := h2
    _ ≤ ∑ h : P, (1 + (Pr.filter fun s => ∀ i ∈ s, Q i h).card) := sum_le_sum fun h _ => h3 h
    _ = Fintype.card P + ∑ s ∈ Pr, (univ.filter fun h => ∀ i ∈ s, Q i h).card := by
        rw [sum_add_distrib, h4]; simp
    _ ≤ Fintype.card P + ∑ _s ∈ Pr, a := Nat.add_le_add_left (sum_le_sum h5) _
    _ = Fintype.card P + a * Hs.card.choose 2 := by
        rw [sum_const, card_powersetCard, smul_eq_mul, mul_comm]

end Counting

/-! ### Weights: Corollary 2, Claims 3 and 5 (generic) -/

section Weights

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A] [Fintype K]
  [Fintype P] [Fintype A] {c : K → P → A} {W : ℕ} {x : Fin t → K → Bool}

theorem card_filter_not_mem_univ_eq {t : ℕ} (Hs : Finset (Fin t)) :
    (univ.filter (· ∉ Hs)).card = t - Hs.card := by
  have := card_filter_add_card_filter_not (s := (univ : Finset (Fin t))) (· ∈ Hs)
  have e : univ.filter (· ∈ Hs) = Hs := by ext; simp
  rw [e, card_univ, Fintype.card_fin] at this
  omega

/-- The weight of a set of nodes, copy by copy. -/
theorem wsum_eq (I : Finset (Node t K P A)) :
    wsum (weight W x) I =
      ∑ i, ((∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m)) + (cPart I i).card) := by
  classical
  have e : wsum (weight W x) I = ∑ v, if v ∈ I then weight W x v else 0 := by
    rw [← sum_filter]; unfold wsum; congr 1; ext v; simp
  rw [e, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_sum_type, aPart, cPart, sum_filter, card_filter]
  congr 1

/-- The `A`-part of an independent set weighs at most `W` per copy (if `W ≥ 1`). -/
theorem sum_aPart_le (hW : 1 ≤ W) (hI : IsIndep (graph c) I) (i : Fin t) :
    ∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m) ≤ W := by
  calc ∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m) ≤ ∑ _m ∈ aPart I i, W :=
        sum_le_sum fun m _ => by simp only [weight]; split_ifs <;> omega
    _ ≤ W := by rw [sum_const, smul_eq_mul]; nlinarith [card_aPart_le_one hI i]

/-- In a copy without a heavy node of `I`, the `A`-part weighs at most `1`. -/
theorem sum_aPart_le_one (hI : IsIndep (graph c) I) (i : Fin t)
    (hi : ∀ m ∈ aPart I i, x i m = false) :
    ∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m) ≤ 1 := by
  calc ∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m) = ∑ _m ∈ aPart I i, 1 :=
        sum_congr rfl fun m hm => by simp [weight, hi m hm]
    _ ≤ 1 := by rw [sum_const, smul_eq_mul, mul_one]; exact card_aPart_le_one hI i

/-- **Corollary 2** (sharp form). If `v^i_{mm i} ∈ I` for `i ∈ Hs` with pairwise distinct
`mm i`, the copies in `Hs` contribute at most `|Hs| W + M + a (|Hs| choose 2)` to `w(I)`. -/
theorem corollary2_generic {a : ℕ} (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a) (hW : 1 ≤ W)
    {I : Finset (Node t K P A)} (hI : IsIndep (graph c) I) (Hs : Finset (Fin t)) (mm : Fin t → K)
    (hinj : Set.InjOn mm Hs) (hmem : ∀ i ∈ Hs, (i, .inl (mm i)) ∈ I) :
    ∑ i ∈ Hs, ((∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m)) + (cPart I i).card) ≤
      Hs.card * W + (Fintype.card P + a * Hs.card.choose 2) := by
  rw [sum_add_distrib]
  gcongr
  · calc ∑ i ∈ Hs, ∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m) ≤ ∑ _i ∈ Hs, W :=
          sum_le_sum fun i _ => sum_aPart_le hW hI i
      _ = Hs.card * W := by rw [sum_const, smul_eq_mul]
  · exact card_code_le hc hI Hs mm hinj hmem

/-- **Corollary 2** of the paper: for pairwise distinct `m_1, …, m_t` with `{v^i_{m_i}} ⊆ I`,
`w(I) ≤ t W + M + a (t choose 2)`; with the paper's parameters (`W = ℓ`, `M = ℓ + α`, `a ≤ α`)
this is `≤ (t + 1) ℓ + α t²` (`corollary2`). -/
theorem corollary2_all {a : ℕ} (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a) (hW : 1 ≤ W)
    {I : Finset (Node t K P A)} (hI : IsIndep (graph c) I) (mm : Fin t → K)
    (hinj : Function.Injective mm) (hmem : ∀ i, (i, .inl (mm i)) ∈ I) :
    wsum (weight W x) I ≤ t * W + (Fintype.card P + a * t.choose 2) := by
  rw [wsum_eq]
  simpa using corollary2_generic hc hW hI univ mm hinj.injOn fun i _ => hmem i

theorem inl_mem_commonSet (m m' : K) (i : Fin t) :
    ((i, .inl m') : Node t K P A) ∈ commonSet c m ↔ m' = m := by
  simp [commonSet, codeword, eq_comm]

theorem aPart_commonSet (m : K) (i : Fin t) : aPart (commonSet (t := t) c m) i = {m} := by
  ext m'; simp [aPart, commonSet, codeword, eq_comm]

theorem card_cPart_commonSet (m : K) (i : Fin t) :
    (cPart (commonSet (t := t) c m) i).card = Fintype.card P := by
  have hC : cPart (commonSet (t := t) c m) i = univ.image fun h => (h, c m h) := by
    ext ⟨h, r⟩; simp [cPart, commonSet, codeword, eq_comm]
  rw [hC, card_image_of_injective _ (fun h h' e => (Prod.mk.inj e).1), card_univ]

/-- **Claims 1 and 3** (generic). If all strings share an element `m`, the independent set of
Property 1 has weight `t (W + M)` (the paper's `t (2ℓ + α)`). -/
theorem claim3_generic {m : K} (hm : ∀ i, x i m = true) :
    IsIndep (graph (t := t) c) (commonSet c m) ∧
      wsum (weight W x) (commonSet (t := t) c m) = t * (W + Fintype.card P) := by
  refine ⟨property1 c m, ?_⟩
  rw [wsum_eq]
  simp only [aPart_commonSet, card_cPart_commonSet, sum_singleton, weight, hm, ite_true]
  rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Claims 2 and 5** (generic). If the strings are pairwise disjoint, every independent set `I`
has weight at most `p W + [p ≠ 0] (M + a (p choose 2)) + (t - p)(1 + M)` for some `p ≤ t` (the
number of copies in which `I` contains a heavy node). -/
theorem claim5_generic {a : ℕ} (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ a) (hW : 1 ≤ W)
    (hx : ∀ i j, i ≠ j → ∀ m, x i m = true → x j m = false)
    {I : Finset (Node t K P A)} (hI : IsIndep (graph c) I) :
    ∃ p ≤ t, wsum (weight W x) I ≤
      p * W + (if p = 0 then 0 else Fintype.card P + a * p.choose 2) +
        (t - p) * (1 + Fintype.card P) := by
  classical
  set Hs := univ.filter fun i => ∃ m ∈ aPart I i, x i m = true with hHs
  have hex : ∀ i ∈ Hs, ∃ m, m ∈ aPart I i ∧ x i m = true := fun i hi => by
    simpa [hHs] using hi
  have hlight : ∑ i ∈ univ.filter (· ∉ Hs),
      ((∑ m ∈ aPart I i, weight (P := P) (A := A) W x (i, .inl m)) + (cPart I i).card) ≤
        (t - Hs.card) * (1 + Fintype.card P) := by
    calc _ ≤ ∑ _i ∈ univ.filter (· ∉ Hs), (1 + Fintype.card P) := by
          refine sum_le_sum fun i hi => add_le_add (sum_aPart_le_one hI i fun m hm => ?_)
            (card_cPart_le hI i)
          have : i ∉ Hs := (mem_filter.1 hi).2
          simp only [hHs, mem_filter, mem_univ, true_and, not_exists, not_and] at this
          simpa using this m hm
      _ = (t - Hs.card) * (1 + Fintype.card P) := by
          rw [sum_const, smul_eq_mul, card_filter_not_mem_univ_eq Hs]
  refine ⟨Hs.card, card_le_univ _ |>.trans (by simp), ?_⟩
  rw [wsum_eq, ← sum_filter_add_sum_filter_not univ (· ∈ Hs)]
  have hfilt : univ.filter (· ∈ Hs) = Hs := by ext; simp
  rw [hfilt]
  rcases Nat.eq_zero_or_pos Hs.card with h0 | hpos
  · rw [card_eq_zero.1 h0] at hlight ⊢
    simpa using hlight
  · obtain ⟨i₀, hi₀⟩ := card_pos.1 hpos
    obtain ⟨m₀, -, -⟩ := hex i₀ hi₀
    have : Nonempty K := ⟨m₀⟩
    choose! mm hmm using hex
    have hinj : Set.InjOn mm Hs := by
      intro i hi j hj e
      by_contra hne
      have h1 := (hmm i hi).2
      have h2 := (hmm j hj).2
      rw [e] at h1
      have := hx i j hne _ h1
      simp_all
    have hmem : ∀ i ∈ Hs, (i, .inl (mm i)) ∈ I := fun i hi => (mem_filter.1 (hmm i hi).1).2
    have := corollary2_generic hc hW hI Hs mm hinj hmem (x := x)
    simp only [hpos.ne', ↓reduceIte]
    omega

end Weights

/-! ### The paper's statements (parameters `W = ℓ`, `M = ℓ + α`, agreement `≤ α`) -/

theorem two_mul_choose_two (n : ℕ) : 2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]; exact Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd

section Paper

variable {t : ℕ} {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A] [Fintype K]
  [Fintype P] [Fintype A] {c : K → P → A} {ℓ α : ℕ} {x : Fin t → K → Bool}

/-- **Claim 3** (and **Claim 1** for `t = 2`). If `x^1_m = ⋯ = x^t_m = 1` for some `m`, `G_x̄`
contains an independent set of weight at least `t (2ℓ + α)`. -/
theorem claim3 (hP : Fintype.card P = ℓ + α) (hx : CommonElement x) :
    ∃ I, IsIndep (graph c) I ∧ t * (2 * ℓ + α) ≤ wsum (weight ℓ x) I := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨h1, h2⟩ := claim3_generic (c := c) (W := ℓ) hm
  exact ⟨_, h1, by rw [h2, hP]; ring_nf; rfl⟩

/-- **Claim 1** (`t = 2`): if `x^1` and `x^2` intersect, there is an independent set of weight at
least `4ℓ + 2α`. -/
theorem claim1 {x : Fin 2 → K → Bool} (hP : Fintype.card P = ℓ + α) (hx : CommonElement x) :
    ∃ I, IsIndep (graph c) I ∧ 4 * ℓ + 2 * α ≤ wsum (weight ℓ x) I := by
  obtain ⟨I, hI, h⟩ := claim3 (c := c) hP hx
  exact ⟨I, hI, by omega⟩

/-- **Corollary 2.** If `t ≥ 1`, `m_1, …, m_t` are distinct and `v^i_{m_i} ∈ I` for all `i`, then
`w(I) ≤ (t + 1) ℓ + α t²`. -/
theorem corollary2 (hP : Fintype.card P = ℓ + α)
    (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ α) (ht : 1 ≤ t) (hℓ : 1 ≤ ℓ)
    {I : Finset (Node t K P A)} (hI : IsIndep (graph c) I) (mm : Fin t → K)
    (hinj : Function.Injective mm) (hmem : ∀ i, (i, .inl (mm i)) ∈ I) :
    wsum (weight ℓ x) I ≤ (t + 1) * ℓ + α * t ^ 2 := by
  have h := corollary2_all (x := x) hc hℓ hI mm hinj hmem
  have h2 := two_mul_choose_two t
  rw [hP] at h
  rcases t with _ | t
  · omega
  · simp only [Nat.add_sub_cancel] at h2
    nlinarith

/-- **Claim 5.** If the strings `x^1, …, x^t` are pairwise disjoint, every independent set of
`G_x̄` has weight at most `(t + 1) ℓ + α t²` (for `t, ℓ, α ≥ 1`). -/
theorem claim5 (hP : Fintype.card P = ℓ + α) (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ α)
    (ht : 1 ≤ t) (hℓ : 1 ≤ ℓ) (hα : 1 ≤ α) (hx : PairwiseDisjoint x)
    {I : Finset (Node t K P A)} (hI : IsIndep (graph c) I) :
    wsum (weight ℓ x) I ≤ (t + 1) * ℓ + α * t ^ 2 := by
  obtain ⟨p, hp, h⟩ := claim5_generic hc hℓ hx hI
  rw [hP] at h
  refine h.trans ?_
  have hC := two_mul_choose_two p
  set C := p.choose 2
  obtain ⟨d, rfl⟩ : ∃ d, t = p + d := ⟨t - p, by omega⟩
  rw [show p + d - p = d by omega]
  rcases p with _ | p
  · simp only [ite_true, zero_mul, zero_add, add_zero] at *
    have : d * d ≤ α * (d * d) := Nat.le_mul_of_pos_left _ hα
    have : d ≤ α * d := Nat.le_mul_of_pos_left _ hα
    nlinarith
  · simp only [Nat.add_one_ne_zero, ↓reduceIte]
    simp only [Nat.add_sub_cancel] at hC
    have h1 : 2 * (α * C) = α * ((p + 1) * p) := by rw [← hC]; ring
    have h2 : d ≤ α * d := Nat.le_mul_of_pos_left _ hα
    have h3 : α * d ≤ α * ((p + 1) * d) := Nat.mul_le_mul_left _ (by nlinarith)
    nlinarith

/-- **Claim 2** (`t = 2`). If `x^1` and `x^2` are disjoint, every independent set has weight at
most `3ℓ + 2α + 1` (for `ℓ ≥ 1`). -/
theorem claim2 {x : Fin 2 → K → Bool} (hP : Fintype.card P = ℓ + α)
    (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ α) (hℓ : 1 ≤ ℓ) (hx : PairwiseDisjoint x)
    {I : Finset (Node 2 K P A)} (hI : IsIndep (graph c) I) :
    wsum (weight ℓ x) I ≤ 3 * ℓ + 2 * α + 1 := by
  obtain ⟨p, hp, h⟩ := claim5_generic hc hℓ hx hI
  rw [hP] at h
  interval_cases p <;> simp at h <;> omega

end Paper

/-! ### Lemmas 1 and 2: the gap -/

/-- Arithmetic of **Lemma 1**: for every `ε > 0` there is `δ > 0` such that for `α ≤ δ ℓ` and
`ℓ ≥ 1/ε` the two cases of Claims 1 and 2 are separated by the factor `3/4 + ε`:
`3ℓ + 2α + 1 ≤ (3/4 + ε)(4ℓ + 2α)`. -/
theorem lemma1_gap {ε : ℝ} (hε : 0 < ε) :
    ∀ ℓ α : ℕ, (α : ℝ) ≤ ε * ℓ → 1 / ε ≤ ℓ →
      ((3 * ℓ + 2 * α + 1 : ℕ) : ℝ) ≤ (3 / 4 + ε) * ((4 * ℓ + 2 * α : ℕ) : ℝ) := by
  intro ℓ α hα hℓ
  have h1 : 1 ≤ ε * ℓ := by rwa [div_le_iff₀ hε, mul_comm] at hℓ
  push_cast
  nlinarith [Nat.cast_nonneg (α := ℝ) α]

/-- **Lemma 1.** For `t = 2` the family `G_x̄` is a `(3/4 + ε)`-approximate MaxIS family: if `x^1`,
`x^2` intersect then some independent set weighs `≥ β := 4ℓ + 2α`; if they are disjoint every
independent set weighs `≤ (3/4 + ε) β` (provided `α ≤ ε ℓ` and `ℓ ≥ 1/ε`, which holds for the
paper's `ℓ ≈ log k`, `α = log k / log log k` and large `k`). -/
theorem lemma1 {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A] [Fintype K]
    [Fintype P] [Fintype A] {c : K → P → A} {ℓ α : ℕ} (hP : Fintype.card P = ℓ + α)
    (hc : ∀ m m', m ≠ m' → agree (c m) (c m') ≤ α) {ε : ℝ} (hε : 0 < ε)
    (hαℓ : (α : ℝ) ≤ ε * ℓ) (hℓ : 1 / ε ≤ ℓ) (x : Fin 2 → K → Bool) :
    (CommonElement x → ∃ I, IsIndep (graph c) I ∧ 4 * ℓ + 2 * α ≤ wsum (weight ℓ x) I) ∧
    (PairwiseDisjoint x → ∀ I, IsIndep (graph c) I →
      (wsum (weight ℓ x) I : ℝ) ≤ (3 / 4 + ε) * ((4 * ℓ + 2 * α : ℕ) : ℝ)) := by
  have hℓ1 : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.2 fun h0 => by
    rw [h0, Nat.cast_zero] at hℓ
    exact absurd hℓ (not_le.2 (by positivity))
  refine ⟨fun hx => claim1 hP hx, fun hx I hI => ?_⟩
  exact le_trans (by exact_mod_cast claim2 hP hc hℓ1 hx hI) (lemma1_gap hε ℓ α hαℓ hℓ)

/-- Arithmetic of **Lemma 2**: with `t := ⌈1/ε⌉₊ + 3 > 2` players and `α t² ≤ ε t ℓ`,
`(t + 1) ℓ + α t² ≤ (1/2 + ε) · t (2ℓ + α)`. -/
theorem lemma2_gap {ε : ℝ} (hε : 0 < ε) (ℓ α : ℕ)
    (hα : (α : ℝ) * (⌈1 / ε⌉₊ + 3) ≤ ε * ℓ) :
    (((⌈1 / ε⌉₊ + 3 + 1) * ℓ + α * (⌈1 / ε⌉₊ + 3) ^ 2 : ℕ) : ℝ) ≤
      (1 / 2 + ε) * (((⌈1 / ε⌉₊ + 3) * (2 * ℓ + α) : ℕ) : ℝ) := by
  push_cast at hα ⊢
  set T : ℝ := ⌈1 / ε⌉₊ + 3
  have hT : 1 ≤ ε * T := by
    have : 1 / ε ≤ ⌈1 / ε⌉₊ := Nat.le_ceil _
    rw [div_le_iff₀ hε] at this
    simp only [T]; nlinarith
  have hℓ : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  have hα0 : (0 : ℝ) ≤ α := Nat.cast_nonneg α
  have hT0 : (0 : ℝ) ≤ T := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hα hT0, mul_le_mul_of_nonneg_right hT hℓ]

/-- **Lemma 2.** For every `ε > 0` there is `t > 2` (namely `⌈1/ε⌉ + 3`) such that `G_x̄` is a
`(1/2 + ε)`-approximate MaxIS family: if all strings share an element some independent set weighs
`≥ β := t (2ℓ + α)`; if they are pairwise disjoint every independent set weighs `≤ (1/2 + ε) β`
(provided `α t ≤ ε ℓ`, true for the paper's parameters and large `k`). -/
theorem lemma2 {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, 2 < t ∧ ∀ {K P A : Type*} [DecidableEq K] [DecidableEq P] [DecidableEq A]
      [Fintype K] [Fintype P] [Fintype A] {c : K → P → A} {ℓ α : ℕ},
      Fintype.card P = ℓ + α → (∀ m m', m ≠ m' → agree (c m) (c m') ≤ α) → 1 ≤ ℓ → 1 ≤ α →
      (α : ℝ) * t ≤ ε * ℓ → ∀ x : Fin t → K → Bool,
      (CommonElement x → ∃ I, IsIndep (graph c) I ∧ t * (2 * ℓ + α) ≤ wsum (weight ℓ x) I) ∧
      (PairwiseDisjoint x → ∀ I, IsIndep (graph c) I →
        (wsum (weight ℓ x) I : ℝ) ≤ (1 / 2 + ε) * ((t * (2 * ℓ + α) : ℕ) : ℝ)) := by
  refine ⟨⌈1 / ε⌉₊ + 3, by omega, ?_⟩
  intro K P A _ _ _ _ _ _ c ℓ α hP hc hℓ hα hαℓ x
  refine ⟨fun hx => claim3 hP hx, fun hx I hI => ?_⟩
  refine le_trans ?_ (lemma2_gap hε ℓ α (by exact_mod_cast hαℓ))
  exact_mod_cast claim5 hP hc (by omega) hℓ hα hx hI

end Podc.MISInapproxCongest
