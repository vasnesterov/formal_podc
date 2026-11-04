import Papers.PODC2011.HomonymsBA.Cover

/-!
# Proposition 1 and the lower bound of Theorem 19: `ℓ ≤ 3t` makes synchronous BA unsolvable

The covering system of Figure 1 of the paper: two copies (`false`/`true`) of an `n`-process system
with `ℓ = 3t` identifiers, split into three classes `X = [0, t)`, `Y = [t, 2t)`, `Z = [2t, 3t)`.
In copy `false` the processes `k ≥ 3t` all get identifier `0` (a stack of `n - 3t + 1` processes
with identifier `0 ∈ X`), in copy `true` they get identifier `t ∈ Y`. Copy `false` has input `v₀`,
copy `true` has input `v₁`. A process of segment `(b, c)` (copy `b`, class `c`) hears the segments
of the hexagon `Z₁ – X₀ – Y₀ – Z₀ – X₁ – Y₁ – Z₁` adjacent to it, and its own segment
(`segAdj`).

The three scenarios (all `n`-process synchronous runs with at most `t` Byzantine processes):
* `S₀`: copy `false` with `Z` Byzantine; the correct processes (`X₀ ∪ Y₀`) all have input `v₀`.
* `S₁`: copy `true` with `X` Byzantine; the correct processes (`Y₁ ∪ Z₁`) all have input `v₁`.
* `S₂`: copy `false` with `Y` Byzantine, where the `Z` processes are mapped to `Z₁` (input `v₁`).

By validity the process `(false, 0)` decides `v₀` in the cover and `(true, 2t)` decides `v₁`;
both are correct in `S₂`, contradicting agreement.

For numerate processes the Byzantine processes deliver the whole multiset sent by the cover
nodes they replace (several copies from the stack: unrestricted). For innumerate processes it is
enough to deliver one copy (the stack processes are clones, `cover_clone`), so the Byzantine
processes are restricted: this proves the lower bound of **Theorem 19** directly (the paper derives
it from the classical bound by a simulation, see `differencies.md`).

Main results: `prop1` (Proposition 1) and `thm19_lower` (necessity in Theorem 19).
-/

namespace Podc.HomonymsBA

open Finset

namespace Hexagon

variable {n t : ℕ}

/-- Segment adjacency on (copy, class): the hexagon `Z₁ – X₀ – Y₀ – Z₀ – X₁ – Y₁ – Z₁` plus
self-loops. -/
def segAdj (x y : Bool × Fin 3) : Bool :=
  if x.2 = y.2 then x.1 == y.1 else ((x.1 == y.1) == (x.2.val + y.2.val != 2))

lemma segAdj_clone : ∀ b₁ b₂ c x, segAdj (b₁, c) x = true → segAdj (b₂, c) x = true → b₁ = b₂ := by
  decide

lemma segAdj_S0 : ∀ b c c', c ≠ 2 → c' ≠ 2 → segAdj (b, c') (false, c) = true → b = false := by
  decide

lemma segAdj_S1 : ∀ b c c', c ≠ 0 → c' ≠ 0 → segAdj (b, c') (true, c) = true → b = true := by
  decide

lemma segAdj_S2 : ∀ b b' c c', ((b = false ∧ c = 0) ∨ (b = true ∧ c = 2)) → c' ≠ 1 →
    segAdj (b', c') (b, c) = true → (b' = false ∧ c' = 0) ∨ (b' = true ∧ c' = 2) := by
  decide

lemma segAdj_cl0 : ∀ c c', c ≠ 2 → c' ≠ 2 → segAdj (false, c') (false, c) = true := by decide
lemma segAdj_cl1 : ∀ c c', c ≠ 0 → c' ≠ 0 → segAdj (true, c') (true, c) = true := by decide
lemma segAdj_cl2 : ∀ b b' c c', ((b = false ∧ c = 0) ∨ (b = true ∧ c = 2)) →
    ((b' = false ∧ c' = 0) ∨ (b' = true ∧ c' = 2)) → segAdj (b', c') (b, c) = true := by decide

variable (t) in
/-- The class of an identifier: `X = 0`, `Y = 1`, `Z = 2`. -/
def cls (i : Fin (3 * t)) : Fin 3 :=
  ⟨i.val / t, by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp
    · exact (Nat.div_lt_iff_lt_mul ht).2 (by have := i.isLt; linarith)⟩

lemma cls_val {i : Fin (3 * t)} : (cls t i).val = i.val / t := rfl

variable (ht : 0 < t)
include ht

/-- Identifiers in copy `false`: `k < 3t` gets `k`, the others get `0` (class `X`). -/
def id₀ (k : Fin n) : Fin (3 * t) := if h : k.val < 3 * t then ⟨k, h⟩ else ⟨0, by omega⟩

/-- Identifiers in copy `true`: `k < 3t` gets `k`, the others get `t` (class `Y`). -/
def id₁ (k : Fin n) : Fin (3 * t) := if h : k.val < 3 * t then ⟨k, h⟩ else ⟨t, by omega⟩

omit ht in
lemma cls_zero (h : 0 < 3 * t) : cls t ⟨0, h⟩ = 0 := by ext; simp [cls_val]

lemma cls_t : cls t ⟨t, by omega⟩ = 1 := by ext; simp [cls_val, Nat.div_self ht]

lemma cls_two_t : cls t ⟨2 * t, by omega⟩ = 2 := by
  ext; simp [cls_val, Nat.mul_div_cancel _ ht]

lemma lt_of_cls_id₀ {k : Fin n} (h : cls t (id₀ ht k) ≠ 0) : k.val < 3 * t := by
  by_contra h'
  apply h
  simp only [id₀, h', dite_false]
  exact cls_zero (by omega)

lemma lt_of_cls_id₁ {k : Fin n} (h : cls t (id₁ ht k) ≠ 1) : k.val < 3 * t := by
  by_contra h'
  apply h
  simp only [id₁, h', dite_false]
  exact cls_t ht

lemma id₀_of_lt {k : Fin n} (h : k.val < 3 * t) : id₀ ht k = ⟨k, h⟩ := by simp [id₀, h]
lemma id₁_of_lt {k : Fin n} (h : k.val < 3 * t) : id₁ ht k = ⟨k, h⟩ := by simp [id₁, h]

lemma id₀_surj (hn : 3 * t < n) : Function.Surjective (id₀ (n := n) ht) := fun i =>
  ⟨⟨i, by omega⟩, by simp [id₀]⟩

lemma id₁_surj (hn : 3 * t < n) : Function.Surjective (id₁ (n := n) ht) := fun i =>
  ⟨⟨i, by omega⟩, by simp [id₁]⟩

lemma card_cls_le (c : Fin 3) : (univ.filter fun i : Fin (3 * t) => cls t i = c).card ≤ t := by
  have := Finset.card_le_card_of_injOn (s := univ.filter fun i : Fin (3 * t) => cls t i = c)
    (t := (univ : Finset (Fin t))) (fun i => ⟨i.val % t, Nat.mod_lt _ ht⟩) (by simp) ?_
  · simpa using this
  intro i hi j hj e
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hi hj
  simp only [Fin.mk.injEq] at e
  have hi' := cls_val (t := t) (i := i)
  have hj' := cls_val (t := t) (i := j)
  rw [hi] at hi'; rw [hj] at hj'
  ext
  rw [← Nat.div_add_mod i.val t, ← Nat.div_add_mod j.val t, ← hi', ← hj', e]

/-- A set of processes on which `id` is injective and lands in one class has at most `t`
elements. -/
lemma card_byz_le (id : Fin n → Fin (3 * t)) (c : Fin 3) (hlt : ∀ k, cls t (id k) = c → k.val < 3 * t)
    (hid : ∀ k (h : k.val < 3 * t), id k = ⟨k, h⟩) :
    (univ.filter fun k => cls t (id k) = c).card ≤ t := by
  refine le_trans (Finset.card_le_card_of_injOn id ?_ ?_) (card_cls_le ht c)
  · intro k hk; simpa using hk
  · intro k hk k' hk' e
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hk hk'
    rw [hid k (hlt k hk), hid k' (hlt k' hk')] at e
    exact Fin.ext (by simpa using e)

/-! ### The cover -/

/-- Identifiers in the cover. -/
def idQ (q : Bool × Fin n) : Fin (3 * t) := if q.1 then id₁ ht q.2 else id₀ ht q.2

/-- Inputs in the cover: `v₀` in copy `false`, `v₁` in copy `true`. -/
def inpQ {V : Type*} (v₀ v₁ : V) (q : Bool × Fin n) : V := if q.1 then v₁ else v₀

/-- Adjacency in the cover. -/
def adj (c' c : Bool × Fin n) : Prop :=
  segAdj (c'.1, cls t (idQ ht c')) (c.1, cls t (idQ ht c)) = true

variable {ℓ : ℕ} {V M S : Type*} (A : Algorithm (3 * t) V M S) (v₀ v₁ : V)

variable (n M) in
/-- The covering run of Figure 1. -/
noncomputable abbrev Rc : Run (Bool × Fin n) (3 * t) V M :=
  coverRun (idQ ht) (inpQ v₀ v₁) (adj ht)

/-- Processes of the same segment with the same identifier are clones. -/
lemma cover_clone : ∀ r (c₁ c₂ : Bool × Fin n), c₁.1 = c₂.1 → idQ ht c₁ = idQ ht c₂ →
    (Rc n ht M v₀ v₁).st A r c₁ = (Rc n ht M v₀ v₁).st A r c₂ := by
  classical
  intro r
  induction r with
  | zero =>
    intro c₁ c₂ h1 h2
    simp [coverRun, inpQ, h1, h2]
  | succ r ih =>
    intro c₁ c₂ h1 h2
    rw [Run.st_succ, Run.st_succ, ih c₁ c₂ h1 h2, Run.inbox_eq, Run.inbox_eq]
    congr 1
    have hadj : ∀ c, adj ht c c₁ ↔ adj ht c c₂ := by
      intro c; simp [adj, h1, h2]
    congr 1
    refine Finset.sum_congr (by ext c; simp [coverRun, hadj]) fun c _ => ?_
    simp [Run.msgFrom, coverRun, h2]

/-! ### The three scenarios -/

variable (n) in
/-- Byzantine sets. -/
def byz₀ : Finset (Fin n) := univ.filter fun k => cls t (id₀ ht k) = 2
variable (n) in
def byz₁ : Finset (Fin n) := univ.filter fun k => cls t (id₁ ht k) = 0
variable (n) in
def byz₂ : Finset (Fin n) := univ.filter fun k => cls t (id₀ ht k) = 1

/-- The embedding of `S₂`: `Z` processes go to copy `true`. -/
def e₂ (k : Fin n) : Bool × Fin n := (decide (cls t (id₀ ht k) = 2), k)

/-- Inputs of `S₂`. -/
def inp₂ (k : Fin n) : V := if cls t (id₀ ht k) = 2 then v₁ else v₀

variable (g : Multiset (Fin (3 * t) × M) → Multiset (Fin (3 * t) × M))

variable (n) in
noncomputable def S₀ : Run (Fin n) (3 * t) V M :=
  scenario A (idQ ht) (inpQ v₀ v₁) (adj ht) (id₀ ht) (byz₀ n ht) (fun _ => v₀) (fun k => (false, k)) g

variable (n) in
noncomputable def S₁ : Run (Fin n) (3 * t) V M :=
  scenario A (idQ ht) (inpQ v₀ v₁) (adj ht) (id₁ ht) (byz₁ n ht) (fun _ => v₁) (fun k => (true, k)) g

variable (n) in
noncomputable def S₂ : Run (Fin n) (3 * t) V M :=
  scenario A (idQ ht) (inpQ v₀ v₁) (adj ht) (id₀ ht) (byz₂ n ht) (inp₂ ht v₀ v₁) (e₂ ht) g

/-! #### Hypotheses of the scenario lemma for each scenario -/

lemma mem_byz₀ {k : Fin n} : k ∈ byz₀ n ht ↔ cls t (id₀ ht k) = 2 := by simp [byz₀]
lemma mem_byz₁ {k : Fin n} : k ∈ byz₁ n ht ↔ cls t (id₁ ht k) = 0 := by simp [byz₁]
lemma mem_byz₂ {k : Fin n} : k ∈ byz₂ n ht ↔ cls t (id₀ ht k) = 1 := by simp [byz₂]

/-- A process with identifier `j` (for `j < 3t`) in both copies. -/
def pj (hn : 3 * t < n) (j : Fin (3 * t)) : Fin n := ⟨j, by omega⟩

lemma id₀_pj (hn : 3 * t < n) (j : Fin (3 * t)) : id₀ ht (pj hn j) = j := by simp [pj, id₀]
lemma id₁_pj (hn : 3 * t < n) (j : Fin (3 * t)) : id₁ ht (pj hn j) = j := by simp [pj, id₁]

lemma byz_of_cls (hn : 3 * t < n) (id : Fin n → Fin (3 * t)) (hid : ∀ j, id (pj hn j) = j) (c : Fin 3)
    (j : Fin (3 * t)) (hj : cls t j = c) : ∃ b ∈ univ.filter (fun k => cls t (id k) = c), id b = j :=
  ⟨pj hn j, by simp [hid, hj], hid j⟩

lemma hout₀ (hn : 3 * t < n) : ∀ p ∉ byz₀ n ht, ∀ c, adj ht c (false, p) → (∀ q ∉ byz₀ n ht, (false, q) ≠ c) →
    ∃ b ∈ byz₀ n ht, id₀ ht b = idQ ht c := by
  intro p hp c hc hc'
  rw [mem_byz₀] at hp
  by_cases h2 : cls t (idQ ht c) = 2
  · exact byz_of_cls ht hn _ (id₀_pj ht hn) 2 _ h2
  · exfalso
    obtain ⟨b, k⟩ := c
    have hb := segAdj_S0 b _ _ hp h2 hc
    subst hb
    exact hc' k (by rw [mem_byz₀]; simpa [idQ] using h2) rfl

lemma hout₁ (hn : 3 * t < n) : ∀ p ∉ byz₁ n ht, ∀ c, adj ht c (true, p) → (∀ q ∉ byz₁ n ht, (true, q) ≠ c) →
    ∃ b ∈ byz₁ n ht, id₁ ht b = idQ ht c := by
  intro p hp c hc hc'
  rw [mem_byz₁] at hp
  by_cases h2 : cls t (idQ ht c) = 0
  · exact byz_of_cls ht hn _ (id₁_pj ht hn) 0 _ h2
  · exfalso
    obtain ⟨b, k⟩ := c
    have hb := segAdj_S1 b _ _ hp h2 hc
    subst hb
    exact hc' k (by rw [mem_byz₁]; simpa [idQ] using h2) rfl

lemma seg_e₂ {p : Fin n} (hp : p ∉ byz₂ n ht) :
    ((e₂ ht p).1 = false ∧ cls t (idQ ht (e₂ ht p)) = 0) ∨
      ((e₂ ht p).1 = true ∧ cls t (idQ ht (e₂ ht p)) = 2) := by
  rw [mem_byz₂] at hp
  by_cases h2 : cls t (id₀ ht p) = 2
  · right
    refine ⟨by simp [e₂, h2], ?_⟩
    have hlt := lt_of_cls_id₀ ht (k := p) (by rw [h2]; decide)
    simpa [e₂, h2, idQ, id₁_of_lt ht hlt, ← id₀_of_lt ht hlt] using h2
  · left
    refine ⟨by simp [e₂, h2], ?_⟩
    have : cls t (id₀ ht p) = 0 := by
      have := (cls t (id₀ ht p)).isLt
      apply Fin.ext; revert hp h2; generalize cls t (id₀ ht p) = c; revert c; decide
    simpa [e₂, h2, idQ] using this

lemma idQ_e₂ {p : Fin n} : idQ ht (e₂ ht p) = id₀ ht p := by
  by_cases h2 : cls t (id₀ ht p) = 2
  · have hlt := lt_of_cls_id₀ ht (k := p) (by rw [h2]; decide)
    simp [e₂, h2, idQ, id₁_of_lt ht hlt, id₀_of_lt ht hlt]
  · simp [e₂, h2, idQ]

lemma hout₂ (hn : 3 * t < n) : ∀ p ∉ byz₂ n ht, ∀ c, adj ht c (e₂ ht p) → (∀ q ∉ byz₂ n ht, e₂ ht q ≠ c) →
    ∃ b ∈ byz₂ n ht, id₀ ht b = idQ ht c := by
  intro p hp c hc hc'
  by_cases h1 : cls t (idQ ht c) = 1
  · exact byz_of_cls ht hn _ (id₀_pj ht hn) 1 _ h1
  · exfalso
    obtain ⟨b, k⟩ := c
    have hseg := seg_e₂ ht hp
    have hb := segAdj_S2 _ b _ _ hseg h1 hc
    rcases hb with ⟨rfl, h0⟩ | ⟨rfl, h2⟩
    · have hk : cls t (id₀ ht k) = 0 := by simpa [idQ] using h0
      exact hc' k (by rw [mem_byz₂, hk]; decide) (by simp [e₂, hk])
    · have hk1 : cls t (id₁ ht k) = 2 := by simpa [idQ] using h2
      have hlt := lt_of_cls_id₁ ht (k := k) (by rw [hk1]; decide)
      have hk : cls t (id₀ ht k) = 2 := by rwa [id₀_of_lt ht hlt, ← id₁_of_lt ht hlt]
      exact hc' k (by rw [mem_byz₂, hk]; decide) (by simp [e₂, hk])

/-! #### Admissibility of the scenarios -/

variable {g}

lemma valid₀ (hn : 3 * t < n) (hgm : ∀ m x, x ∈ g m → x ∈ m) : (S₀ n ht A v₀ v₁ g).Valid t :=
  valid_scenario A hgm (id₀_surj ht hn)
    (card_byz_le ht _ 2 (fun k hk => lt_of_cls_id₀ ht (by rw [hk]; decide))
      fun k h => id₀_of_lt ht h) (hout₀ ht hn)

lemma valid₁ (hn : 3 * t < n) (hgm : ∀ m x, x ∈ g m → x ∈ m) : (S₁ n ht A v₀ v₁ g).Valid t :=
  valid_scenario A hgm (id₁_surj ht hn)
    (card_byz_le ht _ 0 (fun k hk => lt_of_cls_id₁ ht (by rw [hk]; decide))
      fun k h => id₁_of_lt ht h) (hout₁ ht hn)

lemma valid₂ (hn : 3 * t < n) (hgm : ∀ m x, x ∈ g m → x ∈ m) : (S₂ n ht A v₀ v₁ g).Valid t :=
  valid_scenario A hgm (id₀_surj ht hn)
    (card_byz_le ht _ 1 (fun k hk => lt_of_cls_id₀ ht (by rw [hk]; decide))
      fun k h => id₀_of_lt ht h) (hout₂ ht hn)

/-- Outside cover nodes heard by a correct process with a common identifier are clones. -/
lemma clone_hyp {P : Type*} {byz : Finset P} {e : P → Bool × Fin n} :
    ∀ r, ∀ p ∉ byz, ∀ c c', adj ht c (e p) → (∀ q ∉ byz, e q ≠ c) → adj ht c' (e p) →
      (∀ q ∉ byz, e q ≠ c') → idQ ht c = idQ ht c' →
      (Rc n ht M v₀ v₁).st A r c = (Rc n ht M v₀ v₁).st A r c' := by
  intro r p _ c c' hc _ hc' _ hid
  refine cover_clone ht A v₀ v₁ r c c' ?_ hid
  unfold adj at hc hc'
  rw [hid] at hc
  exact segAdj_clone _ _ _ _ hc hc'

lemma restricted₀ (hn : 3 * t < n) [DecidableEq M] : (S₀ n ht A v₀ v₁ Multiset.dedup).Restricted :=
  restricted_scenario_dedup A (hout₀ ht hn) (clone_hyp ht A v₀ v₁)

lemma restricted₁ (hn : 3 * t < n) [DecidableEq M] : (S₁ n ht A v₀ v₁ Multiset.dedup).Restricted :=
  restricted_scenario_dedup A (hout₁ ht hn) (clone_hyp ht A v₀ v₁)

lemma restricted₂ (hn : 3 * t < n) [DecidableEq M] : (S₂ n ht A v₀ v₁ Multiset.dedup).Restricted :=
  restricted_scenario_dedup A (hout₂ ht hn) (clone_hyp ht A v₀ v₁)

/-! #### The contradiction -/

/-- The three scenarios cannot all satisfy Byzantine agreement if `v₀ ≠ v₁`. -/
theorem hexagon_contradiction (hn : 3 * t < n) (hg : ∀ s m m', A.step s (m + g m') = A.step s (m + m'))
    (hv : v₀ ≠ v₁) (h₀ : (S₀ n ht A v₀ v₁ g).BA A) (h₁ : (S₁ n ht A v₀ v₁ g).BA A)
    (h₂ : (S₂ n ht A v₀ v₁ g).BA A) : False := by
  -- process `0` (identifier `0 ∈ X`) and process `2t` (identifier `2t ∈ Z`)
  set k₀ : Fin n := ⟨0, by omega⟩
  set k₂ : Fin n := ⟨2 * t, by omega⟩
  have hk₀ : id₀ ht k₀ = ⟨0, by omega⟩ := id₀_of_lt ht (by simp [k₀]; omega)
  have hk₂ : id₀ ht k₂ = ⟨2 * t, by omega⟩ := id₀_of_lt ht (by simp [k₂]; omega)
  have hk₂' : id₁ ht k₂ = ⟨2 * t, by omega⟩ := id₁_of_lt ht (by simp [k₂]; omega)
  have c₀ : cls t (id₀ ht k₀) = 0 := by rw [hk₀]; exact cls_zero _
  have c₂ : cls t (id₀ ht k₂) = 2 := by rw [hk₂]; exact cls_two_t ht
  have c₂' : cls t (id₁ ht k₂) = 2 := by rw [hk₂']; exact cls_two_t ht
  -- `S₀`: `(false, k₀)` decides `v₀` in the cover
  have hid₀ : ∀ p ∉ byz₀ n ht, idQ ht (false, p) = id₀ ht p := fun _ _ => rfl
  have hd₀ : (Rc n ht M v₀ v₁).Decides A (false, k₀) v₀ := by
    have hp : k₀ ∉ byz₀ n ht := by rw [mem_byz₀, c₀]; decide
    obtain ⟨w, hw⟩ := h₀.termination k₀ hp
    have := h₀.validity v₀ (fun _ _ => rfl) k₀ hp w hw
    subst this
    exact (decides_scenario A hg hid₀ (fun _ _ => rfl) (fun _ _ _ _ h => by simpa using h)
      (fun p hp q hq => segAdj_cl0 _ _ (by simpa [idQ, mem_byz₀] using hp)
        (by simpa [idQ, mem_byz₀] using hq)) hp).1 hw
  -- `S₁`: `(true, k₂)` decides `v₁`
  have hid₁ : ∀ p ∉ byz₁ n ht, idQ ht (true, p) = id₁ ht p := fun _ _ => rfl
  have hd₁ : (Rc n ht M v₀ v₁).Decides A (true, k₂) v₁ := by
    have hp : k₂ ∉ byz₁ n ht := by rw [mem_byz₁, c₂']; decide
    obtain ⟨w, hw⟩ := h₁.termination k₂ hp
    have := h₁.validity v₁ (fun _ _ => rfl) k₂ hp w hw
    subst this
    exact (decides_scenario A hg hid₁ (fun _ _ => rfl) (fun _ _ _ _ h => by simpa using h)
      (fun p hp q hq => segAdj_cl1 _ _ (by simpa [idQ, mem_byz₁] using hp)
        (by simpa [idQ, mem_byz₁] using hq)) hp).1 hw
  -- `S₂`: both are correct
  have hcl₂ : ∀ p ∉ byz₂ n ht, ∀ q ∉ byz₂ n ht, adj ht (e₂ ht q) (e₂ ht p) := by
    intro p hp q hq
    have := segAdj_cl2 _ _ _ _ (seg_e₂ ht hp) (seg_e₂ ht hq)
    exact this
  have hinp₂ : ∀ p ∉ byz₂ n ht, inpQ v₀ v₁ (e₂ ht p) = inp₂ ht v₀ v₁ p := by
    intro p _; by_cases h : cls t (id₀ ht p) = 2 <;> simp [inpQ, inp₂, e₂, h]
  have hinj₂ : ∀ p ∉ byz₂ n ht, ∀ q ∉ byz₂ n ht, e₂ ht p = e₂ ht q → p = q :=
    fun _ _ _ _ h => (Prod.ext_iff.1 h).2
  have hD := fun {p} (hp : p ∉ byz₂ n ht) {v} => decides_scenario A hg
    (fun p _ => idQ_e₂ ht (p := p)) hinp₂ hinj₂ hcl₂ hp (v := v)
  have hp₀ : k₀ ∉ byz₂ n ht := by rw [mem_byz₂, c₀]; decide
  have hp₂ : k₂ ∉ byz₂ n ht := by rw [mem_byz₂, c₂]; decide
  have e₀ : e₂ ht k₀ = (false, k₀) := by simp [e₂, c₀]
  have e₂' : e₂ ht k₂ = (true, k₂) := by simp [e₂, c₂]
  have a₀ : (S₂ n ht A v₀ v₁ g).Decides A k₀ v₀ := (hD hp₀).2 (e₀ ▸ hd₀)
  have a₂ : (S₂ n ht A v₀ v₁ g).Decides A k₂ v₁ := (hD hp₂).2 (e₂' ▸ hd₁)
  exact hv (h₂.agreement k₀ hp₀ k₂ hp₂ v₀ v₁ a₀ a₂)

end Hexagon

open Hexagon

/-- No algorithm solves synchronous BA with `ℓ = 3t` identifiers (numerate processes,
unrestricted Byzantine processes). -/
theorem not_solves_three_t {n t : ℕ} (ht : 0 < t) (hn : 3 * t < n) {V M S : Type}
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) (A : Algorithm (3 * t) V M S) :
    ¬ Solves .sync .unrestricted n t A := by
  intro h
  have hS : ∀ R : Run (Fin n) (3 * t) V M, R.Valid t → R.gst = 0 → R.BA A :=
    fun R hR h0 => h (Fin n) (Fintype.card_fin n) R ⟨hR, fun _ => h0, fun h' => by cases h'⟩
  have hgm : ∀ (m : Multiset (Fin (3 * t) × M)) x, x ∈ (fun m => m) m → x ∈ m := fun _ _ h => h
  exact hexagon_contradiction ht A v₀ v₁ hn (g := fun m => m) (fun _ _ _ => rfl) hv
    (hS _ (valid₀ ht A v₀ v₁ hn hgm) rfl) (hS _ (valid₁ ht A v₀ v₁ hn hgm) rfl)
    (hS _ (valid₂ ht A v₀ v₁ hn hgm) rfl)

/-- No *innumerate* algorithm solves synchronous BA with `ℓ = 3t` identifiers, even against
*restricted* Byzantine processes. -/
theorem not_solves_three_t_innumerate {n t : ℕ} (ht : 0 < t) (hn : 3 * t < n) {V M S : Type}
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) (A : Algorithm (3 * t) V M S) (hA : A.Innumerate) :
    ¬ Solves .sync .restricted n t A := by
  classical
  intro h
  have hS : ∀ R : Run (Fin n) (3 * t) V M, R.Valid t → R.gst = 0 → R.Restricted → R.BA A :=
    fun R hR h0 hr => h (Fin n) (Fintype.card_fin n) R ⟨hR, fun _ => h0, fun _ => hr⟩
  have hgm : ∀ (m : Multiset (Fin (3 * t) × M)) x, x ∈ m.dedup → x ∈ m :=
    fun _ _ h => Multiset.mem_dedup.1 h
  have hg : ∀ s (m m' : Multiset (Fin (3 * t) × M)), A.step s (m + m'.dedup) = A.step s (m + m') :=
    fun s m m' => hA s _ _ fun x => by simp
  exact hexagon_contradiction ht A v₀ v₁ hn hg hv
    (hS _ (valid₀ ht A v₀ v₁ hn hgm) rfl (restricted₀ ht A v₀ v₁ hn))
    (hS _ (valid₁ ht A v₀ v₁ hn hgm) rfl (restricted₁ ht A v₀ v₁ hn))
    (hS _ (valid₂ ht A v₀ v₁ hn hgm) rfl (restricted₂ ht A v₀ v₁ hn))

/-- **Proposition 1.** Synchronous Byzantine agreement is unsolvable, even with numerate
processes, if `ℓ ≤ 3t` (in a system with `n > 3t` processes and `1 ≤ ℓ`; values with at least
two elements). -/
theorem prop1 {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : 0 < ℓ) (hℓt : ℓ ≤ 3 * t) {V : Type}
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) : ¬ Solvable .sync .unrestricted .numerate n ℓ t V := by
  intro h
  have ht : 0 < t := by omega
  obtain ⟨M, S, A, -, hA⟩ := h.mono_ids hℓ hℓt
  exact not_solves_three_t ht hn hv A hA

/-- **Theorem 19, necessity.** Synchronous Byzantine agreement with innumerate processes is
unsolvable against restricted Byzantine processes if `ℓ ≤ 3t` (`n > 3t`, `1 ≤ ℓ`). -/
theorem thm19_lower {n ℓ t : ℕ} (hn : 3 * t < n) (hℓ : 0 < ℓ) (hℓt : ℓ ≤ 3 * t) {V : Type}
    {v₀ v₁ : V} (hv : v₀ ≠ v₁) : ¬ Solvable .sync .restricted .innumerate n ℓ t V := by
  intro h
  have ht : 0 < t := by omega
  obtain ⟨M, S, A, hk, hA⟩ := h.mono_ids hℓ hℓt
  exact not_solves_three_t_innumerate ht hn hv A hk hA

end Podc.HomonymsBA
