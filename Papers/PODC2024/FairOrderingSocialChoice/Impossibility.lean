import Papers.PODC2024.FairOrderingSocialChoice.Defs

/-!
# Lemma 3.4: impossibility of exact `γ`-minimality with faulty replicas

G. Ramseyer, A. Goel. *Fair Ordering in Replicated Systems via Streaming Social Choice*
(arXiv 2304.02730v4; Brief Announcement at PODC 2024).

**Lemma 3.4.** No protocol achieves exact `γ`-minimality (Definition 3.3) with `f` faulty replicas
when `1/2 < γ ≤ 1` and `f > n mod (n - ⌈γ n⌉ + 1)`; this holds even for the weak version that only
constrains scenarios whose true `γ`-graph is acyclic. Main statement: `lemma_3_4`.

## The paper's proof does not work

The paper splits the replicas into `k = n / (n - m + 1)` groups of `d = n - m + 1` replicas
(`m = ⌈γ n⌉`), group `j` reporting the rotation `τ_{j+1} ≺ ⋯ ≺ τ_j`, plus `n mod d` faulty
replicas copying one group, and claims that the pairs `(τ_i, τ_j)`, `i < j`, then receive at least
`m` votes. In fact every arc of the cyclic order contains a whole group, so *every* ordered pair
gets at most `n - d = m - 1 < γ n` votes, and exact `γ`-minimality imposes no constraint on the
output (`lemma_3_4_paper_construction_vacuous`, concretely `lemma_3_4_paper_construction_n7`
for `n = 7`, `γ = 2/3`).

## Corrected proof

All scenarios share the *reported* profile `P` above (group `j` reports `rot j`, the extra `r`
replicas join group `0`). In scenario `i`, `|group i| - (n - m) ≤ r + 1 ≤ f` replicas of group `i`
are faulty and truly voted `rot (i + 1)`. Then group `i` has `n - m` true members and every other
group at least `d = n - m + 1`, so the only pair with `≥ m` true votes is `(τ_i, τ_{i+1})`: the true
`γ`-graph is a single edge (acyclic) and exact `γ`-minimality forces `τ_i` before `τ_{i+1}` in the
output on `P`. Since `P` is the same in all `k` scenarios, the output would contain the cycle
`τ₀ → τ₁ → ⋯ → τ_{k-1} → τ₀` (`cyclic_fails`). If `k = 1` (then `f ≥ m`), two transactions
suffice: everybody reports `τ₀ ≺ τ₁`; either all are honest, or `m` of them truly voted
`τ₁ ≺ τ₀`.

`lemma_3_4_n7_f1` proves the remark that `n = 7`, `γ = 2/3` admits `f = 1`, which the stated
condition (`f > 7 mod 3 = 1`) does not cover (`lemma_3_4_n7_f1_not_covered`); it uses groups of
unequal sizes `3, 3, 1`.

Model: deterministic protocol = aggregation map from reported profiles to output orders (static
setting, every replica votes on every transaction); faulty replicas report arbitrary orders.
-/

namespace Podc.FairOrderingSocialChoice

open Cslib.SocialChoice Finset Relation

namespace Impossibility

/-! ### Generic helpers -/

/-- A relation that strictly increases a natural-number rank has no cycles. -/
theorem not_transGen_self_of_rank {X : Type*} {R : X → X → Prop} (φ : X → ℕ)
    (h : ∀ a b, R a b → φ a < φ b) (x : X) : ¬ TransGen R x x := by
  have key : ∀ a b, TransGen R a b → φ a < φ b := by
    intro a b hab
    induction hab with
    | single hab => exact h _ _ hab
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact fun hx => lt_irrefl _ (key x x hx)

theorem atLeast_iff_ceil_le {ι X : Type*} [Fintype ι] (σ : Profile ι X) (γ : ℝ) (a b : X) :
    AtLeast σ γ a b ↔ ⌈γ * Fintype.card ι⌉₊ ≤ count σ a b := by
  unfold AtLeast; exact Nat.ceil_le.symm

theorem card_filter_comp_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β) (p : β → Prop)
    [DecidablePred p] : #{x | p (e x)} = #{y | p y} :=
  Finset.card_equiv e (by simp)

/-- The conclusion of Lemma 3.4 for one protocol `A`: there is a scenario with at most `f` faulty
replicas, whose true `γ`-graph is acyclic, in which `A` violates exact `γ`-minimality. -/
def Fails {ι X : Type*} [Fintype ι] (A : Aggregation ι X) (γ : ℝ) (f : ℕ) : Prop :=
  ∃ (T P : Profile ι X) (F : Finset ι), F.card ≤ f ∧ Agree T P F ∧
    (∀ x, ¬ TransGen (AtLeast T γ) x x) ∧ ¬ ExactlyMinimal T γ (A P)

theorem forced_of_not_fails {ι X : Type*} [Fintype ι] {A : Aggregation ι X} {γ : ℝ} {f : ℕ}
    (hA : ¬ Fails A γ f) {T P : Profile ι X} {F : Finset ι} (hF : F.card ≤ f)
    (hag : Agree T P F) (hac : ∀ x, ¬ TransGen (AtLeast T γ) x x) {a b : X}
    (hab : AtLeast T γ a b) : (A P).P a b := by
  by_contra h
  exact hA ⟨T, P, F, hF, hag, hac, fun hm => h (hm.P_of_acyclic hac hab)⟩

/-! ### Rotations of a cyclic order -/

variable {k : ℕ}

/-- Cyclic successor on `Fin k`. -/
def csucc (a : Fin k) : Fin k :=
  ⟨if a.val + 1 = k then 0 else a.val + 1, by have := a.isLt; split_ifs <;> omega⟩

/-- Rank of `t` in the rotation `τ_{j+1} ≺ τ_{j+2} ≺ ⋯ ≺ τ_j`. -/
def rk (j t : Fin k) : ℕ :=
  if (csucc j).val ≤ t.val then t.val - (csucc j).val else t.val + k - (csucc j).val

/-- The rotation vote `τ_{j+1} ≺ τ_{j+2} ≺ ⋯ ≺ τ_{j+k} = τ_j`; it "dissents" from the cyclic order
exactly on the edge `(τ_j, τ_{j+1})`. -/
noncomputable def rot (j : Fin k) : Pref (Fin k) := Pref.ofRank (rk j)

/-- `j` lies on the cyclic arc `a, a+1, …, b-1`. -/
def InArc (a b j : Fin k) : Prop :=
  if a.val < b.val then a.val ≤ j.val ∧ j.val < b.val else (a.val ≤ j.val ∨ j.val < b.val)

instance (a b j : Fin k) : Decidable (InArc a b j) := by unfold InArc; infer_instance

theorem rot_P_iff {a b : Fin k} (hab : a ≠ b) (j : Fin k) : (rot j).P a b ↔ ¬ InArc a b j := by
  have ha := a.isLt; have hb := b.isLt; have hj := j.isLt
  have hab' : a.val ≠ b.val := Fin.val_ne_of_ne hab
  unfold rot
  rw [Pref.ofRank_P_iff]
  · simp only [rk, csucc, InArc]; split_ifs <;> omega
  · simp only [rk, csucc]; split_ifs <;> omega

theorem count_rot {ι : Type*} [Fintype ι] (h : ι → Fin k) {a b : Fin k} (hab : a ≠ b) :
    count (fun x => rot (h x)) a b = #{x | ¬ InArc a b (h x)} := by
  classical
  rw [count_def]; congr 1; ext x; simp [rot_P_iff hab]

theorem count_self {ι X : Type*} [Fintype ι] (σ : Profile ι X) (a : X) : count σ a a = 0 := by
  classical
  rw [count_def]; simp [(σ _).irrefl]

/-- For profiles of rotations, `γ n` replicas put `a` before `b` iff at most `n - ⌈γ n⌉` replicas
vote a rotation dissenting on the arc from `a` to `b`. -/
theorem atLeast_rot_iff {ι : Type*} [Fintype ι] {n m : ℕ} {γ : ℝ} (hcard : Fintype.card ι = n)
    (hm : ⌈γ * n⌉₊ = m) (hmn : m ≤ n) (h : ι → Fin k) {a b : Fin k} (hab : a ≠ b) :
    AtLeast (fun x => rot (h x)) γ a b ↔ #{x | InArc a b (h x)} ≤ n - m := by
  rw [atLeast_iff_ceil_le, count_rot h hab, hcard, hm]
  have := card_filter_add_card_filter_not (s := (univ : Finset ι))
    (fun x => InArc a b (h x))
  rw [card_univ, hcard] at this
  omega

theorem inArc_self {a b : Fin k} (hab : a ≠ b) : InArc a b a := by
  have : a.val ≠ b.val := Fin.val_ne_of_ne hab
  simp only [InArc]; split_ifs <;> omega

theorem inArc_csucc {a b : Fin k} (hab : a ≠ b) (hb : b ≠ csucc a) : InArc a b (csucc a) := by
  have : a.val ≠ b.val := Fin.val_ne_of_ne hab
  have : b.val ≠ (csucc a).val := Fin.val_ne_of_ne hb
  have := a.isLt; have := b.isLt
  simp only [InArc, csucc] at *; split_ifs at * <;> omega

theorem inArc_csucc_iff (a j : Fin k) (hk : 2 ≤ k) : InArc a (csucc a) j ↔ j = a := by
  have := a.isLt; have := j.isLt
  rw [Fin.ext_iff]; simp only [InArc, csucc]; split_ifs <;> omega

theorem csucc_ne (a : Fin k) (hk : 2 ≤ k) : csucc a ≠ a := by
  have := a.isLt
  rw [Ne, Fin.ext_iff]; simp only [csucc]; split_ifs <;> omega

/-- A strict total order cannot contain the cycle `τ₀ → τ₁ → ⋯ → τ_{k-1} → τ₀`. -/
theorem no_cyclic_order (hk : 2 ≤ k) (out : Pref (Fin k)) (h : ∀ i, out.P i (csucc i)) : False := by
  have key : ∀ j (hj : j + 1 < k), out.P ⟨0, by omega⟩ ⟨j + 1, hj⟩ := by
    intro j
    induction j with
    | zero =>
      intro hj
      convert h ⟨0, by omega⟩ using 1
      ext; simp only [csucc]; split_ifs <;> omega
    | succ j ih =>
      intro hj
      refine out.trans (ih (by omega)) ?_
      convert h ⟨j + 1, by omega⟩ using 1
      ext; simp only [csucc]; split_ifs <;> omega
  have h1 := key (k - 2) (by omega)
  have h2 := h ⟨k - 2 + 1, by omega⟩
  have : csucc (⟨k - 2 + 1, by omega⟩ : Fin k) = ⟨0, by omega⟩ := by
    ext; simp only [csucc]; split_ifs <;> omega
  rw [this] at h2
  exact out.asymm h1 h2

/-- **Core of Lemma 3.4** (corrected argument). Replicas `ι` (`n` of them) report the rotations
`rot (g x)`. For each transaction `i`, scenario `i` has true votes `rot (h i x)`, in which at most
`n - m` replicas vote `rot i` and more than `n - m` vote each other rotation, and at most `f`
replicas lie (`h i x ≠ g x`). Then every protocol fails in one of these scenarios. -/
theorem cyclic_fails {ι : Type*} [Fintype ι] {n m f : ℕ} {γ : ℝ} (hcard : Fintype.card ι = n)
    (hm : ⌈γ * n⌉₊ = m) (hmn : m ≤ n) (hm0 : 0 < m) (hk : 2 ≤ k)
    (g : ι → Fin k) (h : Fin k → ι → Fin k)
    (h1 : ∀ i, #{x | h i x = i} ≤ n - m)
    (h2 : ∀ i j, j ≠ i → n - m < #{x | h i x = j})
    (h3 : ∀ i, #{x | h i x ≠ g x} ≤ f) (A : Aggregation ι (Fin k)) : Fails A γ f := by
  classical
  by_contra hA
  set P : Profile ι (Fin k) := fun x => rot (g x)
  have key : ∀ i a b, AtLeast (fun x => rot (h i x)) γ a b ↔ a = i ∧ b = csucc i := by
    intro i a b
    by_cases hab : a = b
    · subst hab
      rw [atLeast_iff_ceil_le, count_self, hcard, hm]
      constructor
      · intro h; omega
      · rintro ⟨rfl, h⟩; exact absurd h.symm (csucc_ne a hk)
    rw [atLeast_rot_iff hcard hm hmn _ hab]
    constructor
    · intro hle
      have only : ∀ j, InArc a b j → j = i := by
        intro j hj
        by_contra hji
        have := h2 i j hji
        have : #{x | h i x = j} ≤ #{x | InArc a b (h i x)} := by
          apply card_le_card; intro x; simp only [mem_filter, mem_univ, true_and]
          rintro rfl; exact hj
        omega
      have hai := only a (inArc_self hab)
      subst hai
      refine ⟨rfl, ?_⟩
      by_contra hb
      exact csucc_ne a hk (only _ (inArc_csucc hab hb))
    · rintro ⟨rfl, rfl⟩
      convert h1 a using 3
      exact inArc_csucc_iff _ _ hk
  have forced : ∀ i, (A P).P i (csucc i) := by
    intro i
    refine forced_of_not_fails hA (T := fun x => rot (h i x)) (F := {x | h i x ≠ g x}) (h3 i)
      ?_ ?_ ((key i _ _).2 ⟨rfl, rfl⟩)
    · intro x hx
      simp only [mem_filter, mem_univ, true_and, not_not] at hx
      simp [P, hx]
    · refine not_transGen_self_of_rank (fun t => if t = i then 0 else 1) ?_
      intro a b hab
      obtain ⟨rfl, rfl⟩ := (key i a b).1 hab
      simp [csucc_ne a hk]
  exact no_cyclic_order hk _ forced

/-! ### The replica groups -/

theorem ceil_facts {n : ℕ} {γ : ℝ} (hγ : 1 / 2 < γ) (hγ1 : γ ≤ 1) (hn : 0 < n) :
    ⌈γ * n⌉₊ ≤ n ∧ 0 < ⌈γ * n⌉₊ ∧ n < 2 * ⌈γ * n⌉₊ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨Nat.ceil_le.2 (by nlinarith), Nat.ceil_pos.2 (by positivity), ?_⟩
  have := Nat.le_ceil (γ * n)
  have : (n : ℝ) < 2 * ⌈γ * n⌉₊ := by nlinarith
  exact_mod_cast this

/-- Case `k = n / (n - m + 1) ≥ 2`: `k` groups of `d = n - m + 1` replicas, group `j` reporting
`rot j`, plus `r = n % d` extra replicas reporting `rot 0`. In scenario `i`, `|group i| - (n - m)`
replicas of group `i` (one, or `r + 1` for `i = 0`) truly vote `rot (i + 1)`. -/
theorem cyclic_data {n m f : ℕ} (hk : 2 ≤ n / (n - m + 1)) (hf : n % (n - m + 1) < f) :
    ∃ (g : Fin n → Fin (n / (n - m + 1))) (h : Fin (n / (n - m + 1)) → Fin n → Fin (n / (n - m + 1))),
      (∀ i, #{x | h i x = i} ≤ n - m) ∧ (∀ i j, j ≠ i → n - m < #{x | h i x = j}) ∧
      (∀ i, #{x | h i x ≠ g x} ≤ f) := by
  classical
  set d := n - m + 1 with hd
  set k := n / d with hkdef
  set r := n % d with hr
  have hcard : Fintype.card (Fin k × Fin d ⊕ Fin r) = n := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact Nat.div_add_mod' n d
  set e : Fin n ≃ (Fin k × Fin d ⊕ Fin r) := (Fintype.equivFinOfCardEq hcard).symm
  let i0 : Fin k := ⟨0, by omega⟩
  let g' : Fin k × Fin d ⊕ Fin r → Fin k := Sum.elim (fun p => p.1) (fun _ => i0)
  let h' : Fin k → Fin k × Fin d ⊕ Fin r → Fin k := fun i =>
    Sum.elim (fun p => if p.1 = i ∧ p.2.val = 0 then csucc i else p.1)
      (fun _ => if i0 = i then csucc i else i0)
  refine ⟨fun x => g' (e x), fun i x => h' i (e x), ?_, ?_, ?_⟩
  · intro i
    refine (card_filter_comp_equiv e (fun y => h' i y = i)).trans_le ?_
    calc #{y | h' i y = i}
        ≤ #((univ : Finset (Fin (d - 1))).image
            (fun t => (Sum.inl (i, ⟨t.val + 1, by omega⟩) : Fin k × Fin d ⊕ Fin r))) := by
          apply card_le_card
          intro y
          simp only [mem_filter, mem_univ, true_and, mem_image]
          rcases y with ⟨j, t⟩ | t
          · simp only [h', Sum.elim_inl]
            split_ifs with hc
            · intro hh; exact absurd hh (csucc_ne i (by omega))
            · rintro rfl
              refine ⟨⟨t.val - 1, by omega⟩, ?_⟩
              simp only [Sum.inl.injEq, Prod.mk.injEq, true_and]
              ext; simp only; omega
          · simp only [h', Sum.elim_inr]
            split_ifs with hc
            · intro hh; exact absurd hh (csucc_ne i (by omega))
            · intro hh; exact absurd hh hc
      _ ≤ d - 1 := by simpa using card_image_le (s := (univ : Finset (Fin (d - 1))))
      _ = n - m := by omega
  · intro i j hji
    refine lt_of_lt_of_le ?_ (card_filter_comp_equiv e (fun y => h' i y = j)).symm.le
    calc n - m < d := by omega
      _ = #((univ : Finset (Fin d)).image
            (fun t => (Sum.inl (j, t) : Fin k × Fin d ⊕ Fin r))) := by
          rw [card_image_of_injective _ (fun a b hab => by simpa using hab)]; simp
      _ ≤ #{y | h' i y = j} := by
          apply card_le_card
          intro y
          simp only [mem_filter, mem_univ, true_and, mem_image]
          rintro ⟨t, rfl⟩
          simp [h', hji]
  · intro i
    refine (card_filter_comp_equiv e (fun y => h' i y ≠ g' y)).trans_le ?_
    calc #{y | h' i y ≠ g' y}
        ≤ #(insert (Sum.inl (i, ⟨0, by omega⟩))
            ((univ : Finset (Fin r)).image (Sum.inr : Fin r → Fin k × Fin d ⊕ Fin r))) := by
          apply card_le_card
          intro y
          simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
          rcases y with ⟨j, t⟩ | t
          · simp only [h', g', Sum.elim_inl]
            split_ifs with hc
            · intro _; left; obtain ⟨rfl, ht⟩ := hc
              simp only [Sum.inl.injEq, Prod.mk.injEq, true_and]; ext; simpa using ht
            · intro hh; exact absurd rfl hh
          · intro _; right; exact ⟨t, rfl⟩
      _ ≤ r + 1 := by
          refine (card_insert_le _ _).trans ?_
          simpa using card_image_le (s := (univ : Finset (Fin r)))
      _ ≤ f := by omega

/-- Case `n / (n - m + 1) = 1` (then `f ≥ m`): two transactions, everybody reports `τ₀ ≺ τ₁`
(`= rot 1`). Scenario `0`: all honest. Scenario `1`: `m` faulty replicas truly vote `τ₁ ≺ τ₀`. -/
theorem two_data {n m f : ℕ} (hmn : m ≤ n) (hm0 : 0 < m) (hfm : m ≤ f) (h2m : n < 2 * m) :
    ∃ (g : Fin n → Fin 2) (h : Fin 2 → Fin n → Fin 2),
      (∀ i, #{x | h i x = i} ≤ n - m) ∧ (∀ i j, j ≠ i → n - m < #{x | h i x = j}) ∧
      (∀ i, #{x | h i x ≠ g x} ≤ f) := by
  classical
  have hlt : #{x : Fin n | x.val < m} = m := by
    rw [Fin.card_filter_val_lt]; omega
  have hnlt : #{x : Fin n | ¬ x.val < m} = n - m := by
    have := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun x => x.val < m)
    rw [card_univ, Fintype.card_fin] at this; omega
  refine ⟨fun _ => 1, fun i x => if i = 0 then 1 else if x.val < m then 0 else 1, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, one_ne_zero, ↓reduceIte, ite_eq_right_iff, zero_ne_one, imp_false]
      omega
  · intro i j hji
    fin_cases i <;> fin_cases j <;> simp at hji ⊢
    · omega
    · omega
  · intro i
    fin_cases i
    · simp
    · simp only [Fin.mk_one, one_ne_zero, ↓reduceIte, ne_eq, ite_eq_right_iff, zero_ne_one,
        imp_false, not_not]
      omega

end Impossibility

open Impossibility

/-! ### Lemma 3.4 -/

/-- **Lemma 3.4 of [Ramseyer–Goel]** (corrected proof). Let `1/2 < γ ≤ 1` and
`f > n mod (n - ⌈γ n⌉ + 1)`. Then there is a finite set of transactions (`Fin k`) such that every
deterministic protocol `A` (a map from reported profiles to output orders) violates exact
`γ`-minimality in some scenario with at most `f` faulty replicas whose true `γ`-graph is acyclic
(so even the weak version of the property — output a linear extension of the true `γ`-graph when
it is acyclic — is impossible). -/
theorem lemma_3_4 (n f : ℕ) (γ : ℝ) (hγ : 1 / 2 < γ) (hγ1 : γ ≤ 1) (hn : 0 < n)
    (hf : n % (n - ⌈γ * n⌉₊ + 1) < f) :
    ∃ k : ℕ, ∀ A : Aggregation (Fin n) (Fin k),
      ∃ (T P : Profile (Fin n) (Fin k)) (F : Finset (Fin n)),
        F.card ≤ f ∧ Agree T P F ∧ (∀ x, ¬ TransGen (AtLeast T γ) x x) ∧
          ¬ ExactlyMinimal T γ (A P) := by
  obtain ⟨hmn, hm0, h2m⟩ := ceil_facts hγ hγ1 hn
  set m := ⌈γ * n⌉₊ with hm
  by_cases hk : 2 ≤ n / (n - m + 1)
  · obtain ⟨g, h, h1, h2, h3⟩ := cyclic_data hk hf
    exact ⟨_, fun A => cyclic_fails (Fintype.card_fin n) hm.symm hmn hm0 hk g h h1 h2 h3 A⟩
  · have hd : n - m + 1 ≤ n := by omega
    have hk1 : n / (n - m + 1) = 1 := by
      have := Nat.div_pos hd (by omega : 0 < n - m + 1); omega
    have hmod : n % (n - m + 1) = m - 1 := by
      have := Nat.div_add_mod n (n - m + 1); rw [hk1] at this; omega
    obtain ⟨g, h, h1, h2, h3⟩ := two_data (f := f) hmn hm0 (by omega) h2m
    exact ⟨2, fun A => cyclic_fails (Fintype.card_fin n) hm.symm hmn hm0 le_rfl g h h1 h2 h3 A⟩

/-! ### The paper's own construction forces nothing -/

/-- **The construction in the paper's proof of Lemma 3.4 is vacuous.** In the paper's profile
every rotation `rot j` is reported by a group of at least `n - ⌈γ n⌉ + 1` replicas (groups of
`n - ⌈γ n⌉ + 1`, the remaining `n mod (n - ⌈γ n⌉ + 1)` replicas copying one group). In any such
profile *no* ordered pair is received by `γ n` replicas, contrary to the proof's claim that the
pairs `(τ_i, τ_j)`, `i < j`, receive at least `⌈γ n⌉` votes; so exact `γ`-minimality imposes no
constraint at all on the output. -/
theorem lemma_3_4_paper_construction_vacuous {k : ℕ} {ι : Type*} [Fintype ι] {γ : ℝ} (hγ : 1 / 2 < γ)
    (hγ1 : γ ≤ 1) (hn : 0 < Fintype.card ι) (g : ι → Fin k)
    (hg : ∀ j, Fintype.card ι - ⌈γ * Fintype.card ι⌉₊ < #{x | g x = j}) (a b : Fin k) :
    ¬ AtLeast (fun x => rot (g x)) γ a b := by
  classical
  obtain ⟨hmn, hm0, -⟩ := ceil_facts hγ hγ1 hn
  by_cases hab : a = b
  · subst hab; rw [atLeast_iff_ceil_le, count_self]; omega
  rw [atLeast_rot_iff rfl rfl hmn g hab]
  have := hg a
  have : #{x | g x = a} ≤ #{x | InArc a b (g x)} := by
    apply card_le_card; intro x; simp only [mem_filter, mem_univ, true_and]
    rintro hx; rw [hx]; exact inArc_self hab
  omega

namespace Impossibility

theorem ceil_two_thirds_seven : ⌈(2 / 3 : ℝ) * (7 : ℕ)⌉₊ = 5 := by
  rw [Nat.ceil_eq_iff (by norm_num)]; norm_num

/-- The paper's profile for `n = 7`, `γ = 2/3` (`⌈γ n⌉ = 5`, groups of `3`): replicas `0,1,2`
report `τ₀ ≺ τ₁`, replicas `4,5,6` report `τ₁ ≺ τ₀`, and the remaining replica `3` copies the
first group. -/
noncomputable def paperProfile7 : Profile (Fin 7) (Fin 2) :=
  fun x => rot (if x.val < 4 then 1 else 0)

end Impossibility

/-- Concrete instance of `lemma_3_4_paper_construction_vacuous`: in the paper's profile for
`n = 7`, `γ = 2/3`, `τ₀ ≺ τ₁` gets `4` votes and `τ₁ ≺ τ₀` gets `3`, both below `γ n = 14/3`. -/
theorem lemma_3_4_paper_construction_n7 :
    count paperProfile7 0 1 = 4 ∧ count paperProfile7 1 0 = 3 ∧
      ∀ a b, ¬ AtLeast paperProfile7 (2 / 3) a b := by
  refine ⟨?_, ?_, ?_⟩
  · unfold paperProfile7; rw [count_rot _ (by decide)]; decide
  · unfold paperProfile7; rw [count_rot _ (by decide)]; decide
  · intro a b
    rw [atLeast_iff_ceil_le, Fintype.card_fin, ceil_two_thirds_seven]
    by_cases hab : a = b
    · subst hab; rw [count_self]; omega
    · unfold paperProfile7; rw [count_rot _ hab]
      revert a b; decide

/-! ### `n = 7`, `γ = 2/3`, `f = 1` -/

namespace Impossibility

theorem atLeast_seven_iff (h : Fin 7 → Fin 3) (a b : Fin 3) :
    AtLeast (fun x => rot (h x)) (2 / 3) a b ↔ a ≠ b ∧ 5 ≤ #{x | ¬ InArc a b (h x)} := by
  rw [atLeast_iff_ceil_le, Fintype.card_fin, ceil_two_thirds_seven]
  by_cases hab : a = b
  · subst hab; rw [count_self]; simp
  · rw [count_rot _ hab]; simp [hab]

/-- Groups of sizes `3, 3, 1` reporting `rot 0, rot 1, rot 2`. -/
def group7 (x : Fin 7) : Fin 3 := if x.val < 3 then 0 else if x.val < 6 then 1 else 2

end Impossibility

/-- **The remark after Lemma 3.4** ("for `n = 7`, `γ = 2/3` the lemma admits `f = 1`") is true,
although `f = 1` violates the lemma's own condition `f > n mod (n - ⌈γ n⌉ + 1) = 1`
(see `lemma_3_4_n7_f1_not_covered`). Three transactions; groups of sizes `3, 3, 1` report
`rot 0, rot 1, rot 2` (counts `(τ₀,τ₁) : 4`, `(τ₁,τ₂) : 4`, `(τ₂,τ₀) : 6`). If one group-0 replica
truly voted `rot 2`, the true `γ`-graph is `τ₂ → τ₀ → τ₁`; if one group-1 replica truly voted
`rot 0`, it is `τ₁ → τ₂ → τ₀`. No output order is a linear extension of both. -/
theorem lemma_3_4_n7_f1 :
    ∃ k : ℕ, ∀ A : Aggregation (Fin 7) (Fin k),
      ∃ (T P : Profile (Fin 7) (Fin k)) (F : Finset (Fin 7)),
        F.card ≤ 1 ∧ Agree T P F ∧ (∀ x, ¬ TransGen (AtLeast T (2 / 3)) x x) ∧
          ¬ ExactlyMinimal T (2 / 3) (A P) := by
  refine ⟨3, fun A => ?_⟩
  by_contra hA
  change ¬ Fails A (2 / 3) 1 at hA
  set P : Profile (Fin 7) (Fin 3) := fun x => rot (group7 x)
  let hA' : Fin 7 → Fin 3 := fun x => if x = 0 then 2 else group7 x
  let hB' : Fin 7 → Fin 3 := fun x => if x = 3 then 0 else group7 x
  have kA : ∀ a b, AtLeast (fun x => rot (hA' x)) (2 / 3) a b ↔
      (a = 0 ∧ b = 1) ∨ (a = 2 ∧ b = 0) := by
    intro a b; rw [atLeast_seven_iff]; revert a b; decide
  have kB : ∀ a b, AtLeast (fun x => rot (hB' x)) (2 / 3) a b ↔
      (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 0) := by
    intro a b; rw [atLeast_seven_iff]; revert a b; decide
  have agA : Agree (fun x => rot (hA' x)) P {0} := by
    intro x hx; simp only [mem_singleton] at hx; simp [P, hA', hx]
  have agB : Agree (fun x => rot (hB' x)) P {3} := by
    intro x hx; simp only [mem_singleton] at hx; simp [P, hB', hx]
  have acA : ∀ x, ¬ TransGen (AtLeast (fun x => rot (hA' x)) (2 / 3)) x x :=
    not_transGen_self_of_rank (fun t => if t = 2 then 0 else if t = 0 then 1 else 2) (by
      intro a b hab; rcases (kA a b).1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
  have acB : ∀ x, ¬ TransGen (AtLeast (fun x => rot (hB' x)) (2 / 3)) x x :=
    not_transGen_self_of_rank (fun t => if t = 1 then 0 else if t = 2 then 1 else 2) (by
      intro a b hab; rcases (kB a b).1 hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide)
  have h01 := forced_of_not_fails hA (by simp) agA acA ((kA 0 1).2 (by decide))
  have h12 := forced_of_not_fails hA (by simp) agB acB ((kB 1 2).2 (by decide))
  have h20 := forced_of_not_fails hA (by simp) agB acB ((kB 2 0).2 (by decide))
  exact (A P).asymm h01 ((A P).trans h12 h20)

/-- `f = 1` is not covered by the stated condition of Lemma 3.4 for `n = 7`, `γ = 2/3`. -/
theorem lemma_3_4_n7_f1_not_covered : ¬ (7 % (7 - ⌈(2 / 3 : ℝ) * (7 : ℕ)⌉₊ + 1) < 1) := by
  rw [ceil_two_thirds_seven]; decide

end Podc.FairOrderingSocialChoice
