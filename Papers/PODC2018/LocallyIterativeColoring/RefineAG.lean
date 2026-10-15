import Cslib.Computability.Distributed.Local.LocallyIterative
import Mathlib

/-!
# Refine-AG: an `O(Δ·k)`-colouring in `O(Δ/k)` rounds (Section 3.3 of [BEG18])

Barenboim, Elkin, Goldenberg, *Locally-Iterative Distributed (Δ+1)-Coloring below
Szegedy–Vishwanathan Barrier*, PODC 2018 (arXiv 1712.00285v2), Section 3.3, Algorithm 3.

Colours are triples `⟨a, b, c⟩` with `a, b ∈ ℤ_q` (`q` prime) and `c ∈ ℕ` (`c < k` throughout).
A vertex with `a = 0` is *final* and keeps its colour. A *working* vertex `v` (`a_v ≠ 0`) looks for
an index `j < k` which is *free*, i.e.

1. `b_v + j·a_v ≠ b_u + j·a_u` for every neighbour colour `⟨a_u, b_u, c_u⟩` with `a_u ≠ 0`, and
2. `⟨b_v + j·a_v, j⟩ ≠ ⟨b_u, c_u⟩` for every neighbour colour with `a_u = 0`;

if there is one, it takes the least such `j` and becomes final with colour `⟨0, b_v + j·a_v, j⟩`;
otherwise its colour becomes `⟨a_v, b_v + k·a_v, 0⟩`. Only the *set* of neighbour colours is used.

## Main results

* `BEG18.RefineAG.isProper_run` — **Lemma 3.10**: a proper colouring satisfying the invariant
  `a ≠ 0 → c = 0` (e.g. `c = 0` everywhere initially) stays proper in every round.
* `BEG18.RefineAG.lemma_3_11` — **Lemma 3.11**: two adjacent working vertices agree on
  `b + j·a` for at most one index `j < k` (when `k ≤ q`).
* `BEG18.RefineAG.run_final` — **Lemma 3.12 / Corollary 3.13** (sharpened): if all degrees are
  at most `Δ`, `1 ≤ k` and `2Δ + k ≤ q`, then after `⌊2Δ/k⌋ + 1` rounds every vertex is final.
* `BEG18.RefineAG.corollary_3_13` — the resulting colouring is proper and every colour is
  `⟨0, b, j⟩` with `j < k`; encoded as `j·q + b` it is a proper colouring with `< k·q` colours.
* `BEG18.RefineAG.corollary_3_13_paper` — the same with the paper's constants (`q ≥ 2Δ + 3k`,
  `⌈2Δ/k⌉ + 1` rounds).
-/

namespace BEG18

open Cslib.LocallyIterative Finset

namespace RefineAG

/-- A colour `⟨a, b, c⟩` of Algorithm 3 of [BEG18]. -/
@[ext] structure Color (q : ℕ) where
  /-- First coordinate; `a = 0` means the colour is final. -/
  a : ZMod q
  /-- Second coordinate. -/
  b : ZMod q
  /-- Third coordinate: the index `j` with which the vertex finalized (`0` while working). -/
  c : ℕ

variable {V : Type*} {G : SimpleGraph V} {q : ℕ} (k : ℕ)

/-- The index `j` is *free* for a vertex of colour `x` whose neighbours have the colours `N`
(conditions 1 and 2 in lines 4–8 of Algorithm 3 of [BEG18]). -/
def Free (x : Color q) (N : Set (Color q)) (j : ℕ) : Prop :=
  (∀ y ∈ N, y.a ≠ 0 → x.b + j * x.a ≠ y.b + j * y.a) ∧
    (∀ y ∈ N, y.a = 0 → (x.b + j * x.a, j) ≠ (y.b, y.c))

open Classical in
/-- One round of Algorithm 3 (Refine-AG) of [BEG18] with parameter `k`. -/
noncomputable def step (x : Color q) (N : Set (Color q)) : Color q :=
  if x.a = 0 then x
  else if h : ∃ j, j < k ∧ Free x N j then ⟨0, x.b + Nat.find h * x.a, Nat.find h⟩
  else ⟨x.a, x.b + k * x.a, 0⟩

/-- Algorithm 3 (Refine-AG) of [BEG18] as a (round-independent) locally-iterative algorithm. -/
noncomputable def algorithm : Algorithm (Color q) := Algorithm.ofStep (step k)

variable {k}

theorem step_of_final {x : Color q} (hx : x.a = 0) (N : Set (Color q)) : step k x N = x := by
  simp [step, hx]

/-- The two possible outcomes of a round at a working vertex. -/
theorem step_of_working {x : Color q} (hx : x.a ≠ 0) (N : Set (Color q)) :
    (∃ j < k, Free x N j ∧ step k x N = ⟨0, x.b + j * x.a, j⟩) ∨
      ((∀ j < k, ¬ Free x N j) ∧ step k x N = ⟨x.a, x.b + k * x.a, 0⟩) := by
  classical
  by_cases h : ∃ j, j < k ∧ Free x N j
  · left
    refine ⟨Nat.find h, (Nat.find_spec h).1, (Nat.find_spec h).2, ?_⟩
    simp only [step, hx, ↓reduceIte, h, ↓reduceDIte]
  · right
    refine ⟨fun j hj hf => h ⟨j, hj, hf⟩, ?_⟩
    simp only [step, hx, ↓reduceIte, h, ↓reduceDIte]

/-- The invariant of Algorithm 3: a working colour has third coordinate `0`. -/
def Inv (x : Color q) : Prop := x.a ≠ 0 → x.c = 0

theorem inv_step {x : Color q} (hx : Inv x) (N : Set (Color q)) : Inv (step k x N) := by
  by_cases ha : x.a = 0
  · rwa [step_of_final ha]
  · rcases step_of_working (k := k) ha N with ⟨j, -, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [Inv]

theorem c_lt_step (hk : 0 < k) {x : Color q} (hx : x.c < k) (N : Set (Color q)) :
    (step k x N).c < k := by
  by_cases ha : x.a = 0
  · rwa [step_of_final ha]
  · rcases step_of_working (k := k) ha N with ⟨j, hj, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simpa

/-! ### Lemma 3.10: properness is preserved -/

/-- The key step of Lemma 3.10 of [BEG18]: adjacent vertices with distinct colours satisfying the
invariant get distinct colours. -/
theorem step_ne {x y : Color q} {Nx Ny : Set (Color q)} (hix : Inv x) (hiy : Inv y)
    (hy : y ∈ Nx) (hx : x ∈ Ny) (hne : x ≠ y) : step k x Nx ≠ step k y Ny := by
  -- a final colour `z` versus a working colour `w` that sees `z`
  have mixed : ∀ {z w : Color q} {Nz Nw : Set (Color q)}, z.a = 0 → w.a ≠ 0 → z ∈ Nw →
      step k z Nz ≠ step k w Nw := by
    intro z w Nz Nw hz hw hzw
    rw [step_of_final hz]
    rcases step_of_working (k := k) hw Nw with ⟨j, -, hf, h⟩ | ⟨-, h⟩ <;> rw [h] <;> intro e
    · exact hf.2 z hzw hz (by rw [e])
    · exact hw (by rw [← hz, e])
  by_cases hxa : x.a = 0 <;> by_cases hya : y.a = 0
  · rwa [step_of_final hxa, step_of_final hya]
  · exact mixed hxa hya hx
  · exact (mixed hya hxa hy).symm
  · rcases step_of_working (k := k) hxa Nx with ⟨i, -, hfi, hi⟩ | ⟨-, hi⟩ <;>
      rcases step_of_working (k := k) hya Ny with ⟨j, -, hfj, hj⟩ | ⟨-, hj⟩ <;>
      rw [hi, hj] <;> intro e <;> simp only [Color.mk.injEq] at e
    · obtain ⟨-, e, rfl⟩ := e
      exact hfi.1 y hy hya e
    · exact hya e.1.symm
    · exact hxa e.1
    · obtain ⟨ea, eb, -⟩ := e
      rw [ea, add_left_inj] at eb
      exact hne (Color.ext ea eb (by rw [hix hxa, hiy hya]))

variable (k) in
/-- **Lemma 3.10 of [BEG18].** If the initial colouring is proper and every working colour has
third coordinate `0` (e.g. `c = 0` everywhere, as in the paper), then Algorithm 3 produces a proper
colouring after every round; moreover the invariant `a ≠ 0 → c = 0` is maintained. -/
theorem isProper_run {c₀ : V → Color q} (h₀ : IsProper G c₀) (hinv : ∀ v, Inv (c₀ v)) (t : ℕ) :
    IsProper G ((algorithm k).run G c₀ t) ∧ ∀ v, Inv ((algorithm k).run G c₀ t v) := by
  refine Algorithm.run_induction (G := G) (P := fun c => IsProper G c ∧ ∀ v, Inv (c v)) _ c₀
    ⟨h₀, hinv⟩ (fun t ih => ?_) t
  rw [Algorithm.run_succ]
  exact ⟨fun u v huv => step_ne (ih.2 u) (ih.2 v) (mem_nbrColors_of_adj _ huv)
    (mem_nbrColors_of_adj _ huv.symm) (ih.1 huv), fun v => inv_step (ih.2 v) _⟩

/-- The third coordinate stays `< k`. -/
theorem c_lt_run (hk : 0 < k) {c₀ : V → Color q} (h₀ : ∀ v, (c₀ v).c < k) (t : ℕ) (v : V) :
    ((algorithm k).run G c₀ t v).c < k := by
  induction t generalizing v with
  | zero => exact h₀ v
  | succ t ih => exact c_lt_step hk (ih v) _

/-! ### Lemma 3.11 -/

/-- In a field `ℤ_q`, two distinct affine maps `x ↦ b + x·a` and `x ↦ b' + x·a'` agree on at most
one natural number `x < q`. -/
theorem affine_unique [Fact q.Prime] {a b a' b' : ZMod q} (h : (a, b) ≠ (a', b')) {i j : ℕ}
    (hi : i < q) (hj : j < q) (ei : b + i * a = b' + i * a') (ej : b + j * a = b' + j * a') :
    i = j := by
  have hsub : ((i : ZMod q) - j) * (a - a') = 0 := by linear_combination ei - ej
  rcases mul_eq_zero.1 hsub with h1 | h1
  · rw [sub_eq_zero, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hj] at h1
    exact h1
  · rw [sub_eq_zero] at h1
    subst h1
    exact absurd (by simpa using ei) fun hb => h (by rw [hb])

/-- **Lemma 3.11 of [BEG18].** If `u, v` have distinct working colours (`a ≠ 0`, hence `c = 0`)
and `k ≤ q`, then there is at most one index `j < k` with `b_v + j·a_v = b_u + j·a_u`. -/
theorem lemma_3_11 [Fact q.Prime] (hkq : k ≤ q) {x y : Color q} (hix : Inv x) (hiy : Inv y)
    (hxa : x.a ≠ 0) (hya : y.a ≠ 0) (hne : x ≠ y) {j₁ j₂ : ℕ} (hj₁ : j₁ < k) (hj₂ : j₂ < k)
    (e₁ : x.b + j₁ * x.a = y.b + j₁ * y.a) (e₂ : x.b + j₂ * x.a = y.b + j₂ * y.a) : j₁ = j₂ := by
  refine affine_unique (fun h => hne ?_) (by omega) (by omega) e₁ e₂
  simp only [Prod.mk.injEq] at h
  exact Color.ext h.1 h.2 (by rw [hix hxa, hiy hya])

/-! ### Dynamics of a single vertex -/

section Dynamics

variable (c₀ : V → Color q)

/-- A final vertex keeps its colour. -/
theorem run_succ_of_final {t : ℕ} {v : V} (h : ((algorithm k).run G c₀ t v).a = 0) :
    (algorithm k).run G c₀ (t + 1) v = (algorithm k).run G c₀ t v :=
  step_of_final h _

theorem run_of_final_of_le {t s : ℕ} {v : V} (h : ((algorithm k).run G c₀ t v).a = 0)
    (hts : t ≤ s) : (algorithm k).run G c₀ s v = (algorithm k).run G c₀ t v := by
  induction s, hts using Nat.le_induction with
  | base => rfl
  | succ s _ ih => rw [run_succ_of_final c₀ (ih ▸ h), ih]

/-- A vertex still working after round `t + 1` was working after round `t`, found no free index
in round `t`, and moved from `⟨a, b, c⟩` to `⟨a, b + k·a, 0⟩`. -/
theorem run_succ_of_working {t : ℕ} {v : V} (h : ((algorithm k).run G c₀ (t + 1) v).a ≠ 0) :
    ((algorithm k).run G c₀ t v).a ≠ 0 ∧
      (∀ j < k, ¬ Free ((algorithm k).run G c₀ t v) (nbrColors G ((algorithm k).run G c₀ t) v) j) ∧
      ((algorithm k).run G c₀ (t + 1) v).a = ((algorithm k).run G c₀ t v).a ∧
      ((algorithm k).run G c₀ (t + 1) v).b =
        ((algorithm k).run G c₀ t v).b + k * ((algorithm k).run G c₀ t v).a := by
  have ha : ((algorithm k).run G c₀ t v).a ≠ 0 := fun ha => h (by
    rw [run_succ_of_final c₀ ha, ha])
  change (step k _ _).a ≠ 0 at h
  change _ ∧ _ ∧ (step k _ _).a = _ ∧ (step k _ _).b = _
  rcases step_of_working (k := k) ha (nbrColors G ((algorithm k).run G c₀ t) v) with
    ⟨j, -, -, e⟩ | ⟨hf, e⟩ <;> rw [e] at h ⊢
  · exact absurd rfl h
  · exact ⟨ha, hf, rfl, rfl⟩

/-- While a vertex is working, its colour after `s` rounds is `⟨a₀, b₀ + k·s·a₀, 0⟩`, where
`⟨a₀, b₀, c₀⟩` is its initial colour. -/
theorem run_of_working {t : ℕ} {v : V} (h : ((algorithm k).run G c₀ t v).a ≠ 0) :
    ∀ s ≤ t, ((algorithm k).run G c₀ s v).a = (c₀ v).a ∧
      ((algorithm k).run G c₀ s v).b = (c₀ v).b + ((k * s : ℕ) : ZMod q) * (c₀ v).a := by
  induction t with
  | zero => intro s hs; obtain rfl := Nat.le_zero.mp hs; simp
  | succ t ih =>
    obtain ⟨h1, -, h2, h3⟩ := run_succ_of_working c₀ h
    intro s hs
    rcases Nat.of_le_succ hs with hs | rfl
    · exact ih h1 s hs
    · obtain ⟨ih1, ih2⟩ := ih h1 t le_rfl
      refine ⟨h2.trans ih1, ?_⟩
      rw [h3, ih1, ih2]
      push_cast; ring

/-- Working vertices were working in all earlier rounds. -/
theorem run_working_of_le {t s : ℕ} {v : V} (h : ((algorithm k).run G c₀ t v).a ≠ 0)
    (hs : s ≤ t) : ((algorithm k).run G c₀ s v).a ≠ 0 := by
  rwa [(run_of_working c₀ h s hs).1, ← (run_of_working c₀ h t le_rfl).1]

end Dynamics

/-! ### Lemma 3.12 and Corollary 3.13: every vertex finalizes within `⌊2Δ/k⌋ + 1` rounds -/

theorem pair_eq_of_mul_add_eq {R j R' j' : ℕ} (hj : j < k) (hj' : j' < k)
    (h : k * R + j = k * R' + j') : R = R' ∧ j = j' := by
  have h1 := congrArg (· / k) h
  have h2 := congrArg (· % k) h
  have hk : 0 < k := by omega
  simp only [Nat.mul_add_div hk, Nat.div_eq_of_lt hj, Nat.div_eq_of_lt hj', Nat.mul_add_mod,
    Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hj', add_zero] at h1 h2
  exact ⟨h1, h2⟩

variable [G.LocallyFinite] {Δ : ℕ}

/-- **Lemma 3.12 and Corollary 3.13 of [BEG18]** (sharpened constants). Let `q` be prime, all
degrees at most `Δ`, `1 ≤ k` and `2Δ + k ≤ q`. If the initial colouring is proper and satisfies the
invariant `a ≠ 0 → c = 0`, then after `⌊2Δ/k⌋ + 1` rounds of Algorithm 3 every vertex is final
(`a = 0`).

Proof: while `v` works, its colour in round `R` is `⟨a_v, b_v + kR·a_v, 0⟩`, so index `j` in
round `R` is blocked by a neighbour `u` iff `b_v + x·a_v = b_u + x·a_u` (`u` working) or
`b_v + x·a_v = b_u ∧ j = c_u` (`u` final, its colour constant), where `x = kR + j < k·h ≤ q`.
Each equation has at most one solution `x < q`, so each neighbour blocks at most `2` pairs
`(R, j)`, while a vertex that never finalizes has all `k·h > 2Δ` pairs blocked. -/
theorem run_final [Fact q.Prime] (hΔ : ∀ v, G.degree v ≤ Δ) (hk : 0 < k) (hq : 2 * Δ + k ≤ q)
    {c₀ : V → Color q} (h₀ : IsProper G c₀) (hinv : ∀ v, Inv (c₀ v)) (v : V) :
    ((algorithm k).run G c₀ (2 * Δ / k + 1) v).a = 0 := by
  classical
  by_contra hv
  set H := 2 * Δ / k + 1 with hH
  have hkH : k * H ≤ q := by
    have := Nat.mul_div_le (2 * Δ) k
    rw [hH, mul_add, mul_one]; omega
  have hlt : 2 * Δ < k * H := Nat.lt_mul_div_succ _ hk
  have hw := run_of_working c₀ hv
  have hva : (c₀ v).a ≠ 0 := by rw [← (hw H le_rfl).1]; exact hv
  set P := range H ×ˢ range k with hP
  -- `u` blocks the index `j` in round `R` while working (`W`) or while final (`F`)
  let W : ℕ × ℕ → V → Prop := fun p u =>
    ((algorithm k).run G c₀ p.1 u).a ≠ 0 ∧
      ((algorithm k).run G c₀ p.1 v).b + p.2 * ((algorithm k).run G c₀ p.1 v).a =
        ((algorithm k).run G c₀ p.1 u).b + p.2 * ((algorithm k).run G c₀ p.1 u).a
  let F : ℕ × ℕ → V → Prop := fun p u =>
    ((algorithm k).run G c₀ p.1 u).a = 0 ∧
      ((algorithm k).run G c₀ p.1 v).b + p.2 * ((algorithm k).run G c₀ p.1 v).a =
        ((algorithm k).run G c₀ p.1 u).b ∧ p.2 = ((algorithm k).run G c₀ p.1 u).c
  have hx : ∀ p ∈ P, k * p.1 + p.2 < q := by
    intro p hp
    simp only [hP, mem_product, mem_range] at hp
    have : k * p.1 + p.2 < k * H := by nlinarith
    omega
  -- closed form of `b_v + j·a_v` in round `R`
  have hvform : ∀ p ∈ P, ((algorithm k).run G c₀ p.1 v).b + p.2 * ((algorithm k).run G c₀ p.1 v).a
      = (c₀ v).b + ((k * p.1 + p.2 : ℕ) : ZMod q) * (c₀ v).a := by
    intro p hp
    simp only [hP, mem_product, mem_range] at hp
    obtain ⟨h1, h2⟩ := hw p.1 hp.1.le
    rw [h1, h2]; push_cast; ring
  -- every pair `(R, j)` is blocked by some neighbour
  have hblock : ∀ p ∈ P, ∃ u ∈ G.neighborFinset v, W p u ∨ F p u := by
    intro p hp
    have hp' := hp
    simp only [hP, mem_product, mem_range] at hp'
    have hnf := (run_succ_of_working c₀ (run_working_of_le c₀ hv (by omega : p.1 + 1 ≤ H))).2.1
      p.2 hp'.2
    simp only [Free, not_and_or, not_forall, not_not, exists_prop] at hnf
    rcases hnf with ⟨y, hy, hya, hyb⟩ | ⟨y, hy, hya, hyb⟩
    · obtain ⟨u, hu, rfl⟩ := hy
      exact ⟨u, (G.mem_neighborFinset v u).2 hu, Or.inl ⟨hya, hyb⟩⟩
    · obtain ⟨u, hu, rfl⟩ := hy
      simp only [Prod.mk.injEq] at hyb
      exact ⟨u, (G.mem_neighborFinset v u).2 hu, Or.inr ⟨hya, hyb⟩⟩
  -- each neighbour blocks at most one pair while working
  have hW : ∀ u ∈ G.neighborFinset v, (P.filter fun p => W p u).card ≤ 1 := by
    intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    rw [Finset.card_le_one]
    intro p hp p' hp'
    simp only [mem_filter] at hp hp'
    have hwu := run_of_working c₀ hp.2.1
    have hua : (c₀ u).a ≠ 0 := by rw [← (hwu p.1 le_rfl).1]; exact hp.2.1
    have hne : ((c₀ v).a, (c₀ v).b) ≠ ((c₀ u).a, (c₀ u).b) := by
      intro e
      simp only [Prod.mk.injEq] at e
      exact h₀ hu (Color.ext e.1 e.2 (by rw [hinv v hva, hinv u hua]))
    have form : ∀ p ∈ P, W p u →
        (c₀ v).b + ((k * p.1 + p.2 : ℕ) : ZMod q) * (c₀ v).a =
          (c₀ u).b + ((k * p.1 + p.2 : ℕ) : ZMod q) * (c₀ u).a := by
      intro p hp hWp
      rw [← hvform p hp, hWp.2]
      obtain ⟨h1, h2⟩ := run_of_working c₀ hWp.1 p.1 le_rfl
      rw [h1, h2]; push_cast; ring
    have := affine_unique hne (hx p hp.1) (hx p' hp'.1) (form p hp.1 hp.2) (form p' hp'.1 hp'.2)
    have hp1 := hp.1; have hp1' := hp'.1
    simp only [hP, mem_product, mem_range] at hp1 hp1'
    obtain ⟨e1, e2⟩ := pair_eq_of_mul_add_eq hp1.2 hp1'.2 this
    exact Prod.ext e1 e2
  -- each neighbour blocks at most one pair while final
  have hF : ∀ u ∈ G.neighborFinset v, (P.filter fun p => F p u).card ≤ 1 := by
    intro u _
    rw [Finset.card_le_one]
    have key : ∀ p ∈ P.filter (fun p => F p u), ∀ p' ∈ P.filter (fun p => F p u),
        p.1 ≤ p'.1 → p = p' := by
      intro p hp p' hp' hle
      simp only [mem_filter] at hp hp'
      have hconst := run_of_final_of_le c₀ hp.2.1 hle
      have hne : ((c₀ v).a, (c₀ v).b) ≠ ((0 : ZMod q), ((algorithm k).run G c₀ p.1 u).b) := by
        intro e; exact hva (Prod.mk.injEq _ _ _ _ ▸ e).1
      have e1 : (c₀ v).b + ((k * p.1 + p.2 : ℕ) : ZMod q) * (c₀ v).a =
          ((algorithm k).run G c₀ p.1 u).b + ((k * p.1 + p.2 : ℕ) : ZMod q) * 0 := by
        rw [mul_zero, add_zero, ← hvform p hp.1, hp.2.2.1]
      have e2 : (c₀ v).b + ((k * p'.1 + p'.2 : ℕ) : ZMod q) * (c₀ v).a =
          ((algorithm k).run G c₀ p.1 u).b + ((k * p'.1 + p'.2 : ℕ) : ZMod q) * 0 := by
        rw [mul_zero, add_zero, ← hvform p' hp'.1, hp'.2.2.1, hconst]
      have := affine_unique hne (hx p hp.1) (hx p' hp'.1) e1 e2
      have hp1 := hp.1; have hp1' := hp'.1
      simp only [hP, mem_product, mem_range] at hp1 hp1'
      obtain ⟨e1, e2⟩ := pair_eq_of_mul_add_eq hp1.2 hp1'.2 this
      exact Prod.ext e1 e2
    intro p hp p' hp'
    rcases le_total p.1 p'.1 with hle | hle
    · exact key p hp p' hp' hle
    · exact (key p' hp' p hp hle).symm
  -- counting
  have hsub : P ⊆ (G.neighborFinset v).biUnion
      fun u => P.filter (fun p => W p u) ∪ P.filter (fun p => F p u) := by
    intro p hp
    obtain ⟨u, hu, hWF⟩ := hblock p hp
    refine mem_biUnion.2 ⟨u, hu, ?_⟩
    rcases hWF with h | h
    · exact mem_union_left _ (mem_filter.2 ⟨hp, h⟩)
    · exact mem_union_right _ (mem_filter.2 ⟨hp, h⟩)
  have h1 := (card_le_card hsub).trans card_biUnion_le
  have h2 : ∑ u ∈ G.neighborFinset v,
      (P.filter (fun p => W p u) ∪ P.filter (fun p => F p u)).card ≤
        ∑ u ∈ G.neighborFinset v, 2 :=
    sum_le_sum fun u hu => (card_union_le _ _).trans (by have := hW u hu; have := hF u hu; omega)
  have hcardP : P.card = H * k := by rw [hP, card_product, card_range, card_range]
  rw [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at h2
  have := h1.trans h2
  have := hΔ v
  have := mul_comm H k
  omega

/-- All vertices stay final after `⌊2Δ/k⌋ + 1` rounds. -/
theorem run_final_of_le [Fact q.Prime] (hΔ : ∀ v, G.degree v ≤ Δ) (hk : 0 < k)
    (hq : 2 * Δ + k ≤ q) {c₀ : V → Color q} (h₀ : IsProper G c₀) (hinv : ∀ v, Inv (c₀ v)) {t : ℕ}
    (ht : 2 * Δ / k + 1 ≤ t) (v : V) : ((algorithm k).run G c₀ t v).a = 0 := by
  have h := run_final hΔ hk hq h₀ hinv v
  rwa [run_of_final_of_le c₀ h ht]

/-- The final colour `⟨0, b, j⟩` (with `j < k`) written as the natural number `j·q + b`. -/
def toNat (x : Color q) : ℕ := x.c * q + x.b.val

/-- **Corollary 3.13 of [BEG18]** (sharpened constants). Let `q` be prime, all degrees at most
`Δ`, `1 ≤ k` and `2Δ + k ≤ q`. Starting from a proper colouring with third coordinates `0`, after
any number `t ≥ ⌊2Δ/k⌋ + 1` of rounds of Algorithm 3 the colouring is proper, every colour has the
form `⟨0, b, j⟩` with `j < k`, and so `⟨0, b, j⟩ ↦ j·q + b` is a proper colouring with at most
`k·q` colours. -/
theorem corollary_3_13 [Fact q.Prime] (hΔ : ∀ v, G.degree v ≤ Δ) (hk : 0 < k)
    (hq : 2 * Δ + k ≤ q) {c₀ : V → Color q} (h₀ : IsProper G c₀) (hc₀ : ∀ v, (c₀ v).c = 0)
    {t : ℕ} (ht : 2 * Δ / k + 1 ≤ t) :
    IsProper G ((algorithm k).run G c₀ t) ∧
      (∀ v, ((algorithm k).run G c₀ t v).a = 0 ∧ ((algorithm k).run G c₀ t v).c < k) ∧
      IsProper G (fun v => toNat ((algorithm k).run G c₀ t v)) ∧
      ∀ v, toNat ((algorithm k).run G c₀ t v) < k * q := by
  have hinv : ∀ v, Inv (c₀ v) := fun v _ => hc₀ v
  have hprop := (isProper_run k h₀ hinv t).1
  have hfin := fun v => run_final_of_le hΔ hk hq h₀ hinv ht v
  have hc := c_lt_run (G := G) hk (fun v => (hc₀ v).trans_lt hk) t
  have hb : ∀ v, ((algorithm k).run G c₀ t v).b.val < q := fun v => ZMod.val_lt _
  refine ⟨hprop, fun v => ⟨hfin v, hc v⟩, fun u v huv e => hprop huv ?_, fun v => ?_⟩
  · simp only [toNat] at e
    rw [mul_comm, mul_comm _ q] at e
    obtain ⟨e1, e2⟩ := pair_eq_of_mul_add_eq (hb u) (hb v) e
    exact Color.ext (by rw [hfin u, hfin v]) (ZMod.val_injective _ e2) e1
  · simp only [toNat]
    have := hc v; have := hb v
    nlinarith

/-- **Corollary 3.13 of [BEG18]** with the paper's constants: `q ≥ 2Δ + 3k` and `⌈2Δ/k⌉ + 1`
rounds. -/
theorem corollary_3_13_paper [Fact q.Prime] (hΔ : ∀ v, G.degree v ≤ Δ) (hk : 0 < k)
    (hq : 2 * Δ + 3 * k ≤ q) {c₀ : V → Color q} (h₀ : IsProper G c₀) (hc₀ : ∀ v, (c₀ v).c = 0) :
    IsProper G ((algorithm k).run G c₀ ((2 * Δ + k - 1) / k + 1)) ∧
      (∀ v, ((algorithm k).run G c₀ ((2 * Δ + k - 1) / k + 1) v).a = 0 ∧
        ((algorithm k).run G c₀ ((2 * Δ + k - 1) / k + 1) v).c < k) ∧
      IsProper G (fun v => toNat ((algorithm k).run G c₀ ((2 * Δ + k - 1) / k + 1) v)) ∧
      ∀ v, toNat ((algorithm k).run G c₀ ((2 * Δ + k - 1) / k + 1) v) < k * q :=
  corollary_3_13 hΔ hk (by omega) h₀ hc₀
    (Nat.succ_le_succ (Nat.div_le_div_right (by omega)))

end RefineAG

end BEG18
