import Papers.PODC2025.RendezvousLabeledLine.LocalBasic
import Cslib.Computability.Distributed.Local.Linial

/-!
# MIS and colourings of sparse power graphs of the labelled line (Lemma 2.1)

Rules on the labelled line, `IsLocal` and `IsEquivar` are defined in `LocalBasic`.

* `colRule S k n Δ` is the colouring of the power graph `G^k[S]` (nodes of `S`, edges between
  nodes at distance `1..k`) computed by Linial's colour reduction (CSLib
  `Cslib.LocallyIterative.linial`, `log* n + 3` rounds of `G^k[S]`, i.e. `k (log* n + 3)` rounds of
  the line), starting from the labels: proper, with colours `< max (16 Δ²) 256`, when
  `G^k[S]` has maximum degree `≤ Δ` (`colRule_spec`).
* `misRule S k n` is a maximal independent set of `G^k[S]`, obtained from `colRule S k n 2` by a
  sweep over the `256` colour classes. This is Lemma 2.1 of the paper (the case used there:
  maximum degree `2`), here with explicit constants.
* `ncard_nbrs_le_of_packed`: under `p`-packing, `G^k[S]` has maximum degree `≤ 2 ⌊k / p⌋`.
-/

namespace Podc.RendezvousLabeledLine

open Function

/-! ### The construction -/

open Cslib.LocallyIterative

section Construction

variable (S : (ℤ → ℕ) → ℤ → Prop) (k n : ℕ)

/-- The power graph `G^k[S ℓ]`: nodes of `S ℓ`, edges between nodes at distance `1..k`. -/
def misGraph (ℓ : ℤ → ℕ) : SimpleGraph ℤ where
  Adj u w := S ℓ u ∧ S ℓ w ∧ u ≠ w ∧ |u - w| ≤ (k : ℤ)
  symm := ⟨fun _ _ ⟨h1, h2, h3, h4⟩ => ⟨h2, h1, h3.symm, by rwa [abs_sub_comm]⟩⟩
  loopless := ⟨fun _ ⟨_, _, h, _⟩ => h rfl⟩

/-- `G^k[S ℓ]` is locally finite (neighbours of `v` lie in `[v - k, v + k]`). -/
noncomputable instance misGraph.instLocallyFinite (ℓ : ℤ → ℕ) :
    (misGraph S k ℓ).LocallyFinite := fun v =>
  ((Set.finite_Icc (v - k) (v + k)).subset fun u (h : (misGraph S k ℓ).Adj v u) => by
    have := abs_le.1 h.2.2.2; constructor <;> linarith).fintype

open Classical in
/-- Initial colouring for Linial's algorithm: the label on `S ℓ`, `0` elsewhere (nodes outside
`S ℓ` are isolated in `G^k[S ℓ]`). -/
noncomputable def misInit (ℓ : ℤ → ℕ) (v : ℤ) : ℕ := if S ℓ v then ℓ v else 0

/-- The colouring of `G^k[S ℓ]` after `log* n + 3` rounds of Linial's colour reduction for
maximum degree `Δ`, starting from the labels (initial palette `max n 1`, so that `n = 0` is
harmless; `log* (max n 1) = log* n`). -/
noncomputable def colRule (Δ : ℕ) (ℓ : ℤ → ℕ) : ℤ → ℕ :=
  (linial (max n 1) Δ).run (misGraph S k ℓ) (misInit S ℓ) (Nat.logStar n + 3)

/-- Sweep over the colour classes of `colRule S k n 2`: after phase `c`, nodes of colour `< c`
have decided; a node of colour `c` joins unless a neighbour already joined. -/
def misSweep (ℓ : ℤ → ℕ) : ℕ → ℤ → Prop
  | 0 => fun _ => False
  | c + 1 => fun v => misSweep ℓ c v ∨
      (S ℓ v ∧ colRule S k n 2 ℓ v = c ∧ ∀ u, (misGraph S k ℓ).Adj v u → ¬ misSweep ℓ c u)

end Construction

/-- A maximal independent set of `G^k[S ℓ]` computed in `k (log* n + 259)` rounds (Lemma 2.1),
when the labels of `S`-nodes are `< n`. -/
noncomputable def misRule (S : (ℤ → ℕ) → ℤ → Prop) (k n : ℕ) : (ℤ → ℕ) → ℤ → Prop :=
  fun ℓ => misSweep S k n ℓ 256

/-! ### Correctness -/

section Spec

variable {S : (ℤ → ℕ) → ℤ → Prop} {k n : ℕ} {ℓ : ℤ → ℕ}

@[simp] lemma misGraph_adj {u w : ℤ} :
    (misGraph S k ℓ).Adj u w ↔ S ℓ u ∧ S ℓ w ∧ u ≠ w ∧ |u - w| ≤ (k : ℤ) := Iff.rfl

lemma misSweep_sub : ∀ c v, misSweep S k n ℓ c v → S ℓ v
  | 0, _, h => h.elim
  | c + 1, v, h => h.elim (misSweep_sub c v) (·.1)

/-- The sweep produces an independent set of `G^k[S ℓ]` when the colouring is proper. -/
lemma misSweep_indep (hc : IsProper (misGraph S k ℓ) (colRule S k n 2 ℓ)) :
    ∀ c u w, misSweep S k n ℓ c u → misSweep S k n ℓ c w → ¬ (misGraph S k ℓ).Adj u w
  | 0, _, _, h, _, _ => h.elim
  | c + 1, u, w, hu, hw, hadj => by
    rcases hu with hu | ⟨-, hcu, hu⟩ <;> rcases hw with hw | ⟨-, hcw, hw⟩
    · exact misSweep_indep hc c u w hu hw hadj
    · exact hw u hadj.symm hu
    · exact hu w hadj hw
    · exact hc hadj (hcu.trans hcw.symm)

/-- After phase `c`, every node of `S ℓ` of colour `< c` is in the set or has a neighbour in it. -/
lemma misSweep_dom : ∀ c v, S ℓ v → colRule S k n 2 ℓ v < c →
    misSweep S k n ℓ c v ∨ ∃ u, (misGraph S k ℓ).Adj v u ∧ misSweep S k n ℓ c u
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | c + 1, v, hv, hlt => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with hlt | heq
    · rcases misSweep_dom c v hv hlt with h | ⟨u, hu, h⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨u, hu, Or.inl h⟩
    · by_cases h : ∃ u, (misGraph S k ℓ).Adj v u ∧ misSweep S k n ℓ c u
      · obtain ⟨u, hu, h⟩ := h
        exact Or.inr ⟨u, hu, Or.inl h⟩
      · push Not at h
        exact Or.inl (Or.inr ⟨hv, heq, fun u hu => h u hu⟩)

/-- The degree of `v` in `G^k[S ℓ]`, as the number of `S`-nodes within distance `k`. -/
lemma misGraph_degree (v : ℤ) (hv : S ℓ v) :
    (misGraph S k ℓ).degree v = {u | S ℓ u ∧ u ≠ v ∧ |u - v| ≤ (k : ℤ)}.ncard := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  congr 1
  ext u
  simp only [SimpleGraph.mem_neighborSet, misGraph_adj, Set.mem_ofPred_eq, abs_sub_comm v u,
    ne_comm (a := v)]
  tauto

lemma misGraph_degree_eq_zero (v : ℤ) (hv : ¬ S ℓ v) : (misGraph S k ℓ).degree v = 0 := by
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨u, hu⟩ => hv hu.1⟩

/-- Under `p`-packing (`p ≥ 1`), an `S`-node has at most `⌊k / p⌋` `S`-nodes within distance `k`
on each side. -/
lemma ncard_nbrs_le_of_packed {p : ℕ} (hpack : Packed (S ℓ) p) (hp : 1 ≤ p) {v : ℤ}
    (hv : S ℓ v) : {u | S ℓ u ∧ u ≠ v ∧ |u - v| ≤ (k : ℤ)}.ncard ≤ 2 * (k / p) := by
  set q : ℤ := ((k / p : ℕ) : ℤ) with hq
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hqk : q = (k : ℤ) / p := by rw [hq]; push_cast; rfl
  let f : ℤ → ℤ := fun u => if v < u then (u - v) / p else -((v - u) / p)
  have hmem : ∀ u ∈ {u | S ℓ u ∧ u ≠ v ∧ |u - v| ≤ (k : ℤ)},
      f u ∈ (((Finset.Icc (-q) q).erase 0 : Finset ℤ) : Set ℤ) := by
    rintro u ⟨hu, huv, hk⟩
    have h1 := hpack u v hu hv huv
    have h2 := abs_le.1 hk
    simp only [Finset.coe_erase, Finset.coe_Icc, Set.mem_sdiff, Set.mem_Icc,
      Set.mem_singleton_iff, f]
    rw [le_abs'] at h1
    split_ifs with h
    · have a1 : 1 ≤ (u - v) / p := by
        rw [Int.le_ediv_iff_mul_le hp']; omega
      have a2 : (u - v) / p ≤ q := hqk ▸ Int.ediv_le_ediv hp' (by linarith)
      refine ⟨⟨by linarith, a2⟩, by omega⟩
    · have a1 : 1 ≤ (v - u) / p := by
        rw [Int.le_ediv_iff_mul_le hp']; omega
      have a2 : (v - u) / p ≤ q := hqk ▸ Int.ediv_le_ediv hp' (by linarith)
      refine ⟨⟨by linarith, by linarith⟩, by omega⟩
  have hinj : Set.InjOn f {u | S ℓ u ∧ u ≠ v ∧ |u - v| ≤ (k : ℤ)} := by
    rintro u ⟨hu, huv, -⟩ w ⟨hw, hwv, -⟩ he
    by_contra hne
    have h1 := hpack u w hu hw hne
    have hu' := hpack u v hu hv huv
    have hw' := hpack w v hw hv hwv
    rw [le_abs'] at h1 hu' hw'
    have e1 := Int.mul_ediv_add_emod (u - v) (p : ℤ)
    have e2 := Int.mul_ediv_add_emod (w - v) (p : ℤ)
    have e3 := Int.mul_ediv_add_emod (v - u) (p : ℤ)
    have e4 := Int.mul_ediv_add_emod (v - w) (p : ℤ)
    have r1 := Int.emod_nonneg (u - v) hp'.ne'
    have r2 := Int.emod_nonneg (w - v) hp'.ne'
    have r3 := Int.emod_nonneg (v - u) hp'.ne'
    have r4 := Int.emod_nonneg (v - w) hp'.ne'
    have s1 := Int.emod_lt_of_pos (u - v) hp'
    have s2 := Int.emod_lt_of_pos (w - v) hp'
    have s3 := Int.emod_lt_of_pos (v - u) hp'
    have s4 := Int.emod_lt_of_pos (v - w) hp'
    have d1 : 1 ≤ (u - v) / p ∨ u < v := by
      by_cases h : v < u
      · left; rw [Int.le_ediv_iff_mul_le hp']; omega
      · right; omega
    have d2 : 1 ≤ (w - v) / p ∨ w < v := by
      by_cases h : v < w
      · left; rw [Int.le_ediv_iff_mul_le hp']; omega
      · right; omega
    have d3 : 1 ≤ (v - u) / p ∨ v < u := by
      by_cases h : u < v
      · left; rw [Int.le_ediv_iff_mul_le hp']; omega
      · right; omega
    have d4 : 1 ≤ (v - w) / p ∨ v < w := by
      by_cases h : w < v
      · left; rw [Int.le_ediv_iff_mul_le hp']; omega
      · right; omega
    simp only [f] at he
    split_ifs at he with g1 g2 g2
    · rw [he] at e1; rcases h1 with h1 | h1 <;> linarith
    · omega
    · omega
    · have he' : (v - u) / p = (v - w) / p := by linarith
      rw [he'] at e3; rcases h1 with h1 | h1 <;> linarith
  refine (Set.ncard_le_ncard_of_injOn f hmem hinj (Finset.finite_toSet _)).trans ?_
  have hq0 : 0 ≤ q := Int.natCast_nonneg _
  rw [Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.mem_Icc.2 ⟨by omega, hq0⟩),
    Int.card_Icc]
  omega

/-- The degree bound used for Lemma 2.1: under `p`-packing with `k < 2p`, `G^k[S ℓ]` has maximum
degree `2`. -/
lemma ncard_nbrs_le_two {p : ℕ} (hpack : Packed (S ℓ) p) (hk : k + 1 ≤ 2 * p) {v : ℤ}
    (hv : S ℓ v) : {u | S ℓ u ∧ u ≠ v ∧ |u - v| ≤ (k : ℤ)}.ncard ≤ 2 := by
  have hp : 1 ≤ p := by omega
  have : k / p ≤ 1 := Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul (by omega)).2 (by omega))
  exact (ncard_nbrs_le_of_packed hpack hp hv).trans (by omega)

end Spec

/-- **Linial's colouring of `G^k[S ℓ]`** (used in Lemmas 2.1 and 3.5). If every `S`-node has at
most `Δ ≥ 1` `S`-nodes within distance `k` and labels on `S ℓ` are `< n`, then `colRule S k n Δ ℓ`
is a proper colouring of `G^k[S ℓ]` with colours `< max (16 Δ²) 256`. -/
theorem colRule_spec (S : (ℤ → ℕ) → ℤ → Prop) (k n Δ : ℕ) (hΔ : 1 ≤ Δ) {ℓ : ℤ → ℕ}
    (hℓ : Injective ℓ)
    (hdeg : ∀ v, S ℓ v → {u | S ℓ u ∧ u ≠ v ∧ |u - v| ≤ (k : ℤ)}.ncard ≤ Δ)
    (hn : ∀ v, S ℓ v → ℓ v < n) :
    (∀ u w, S ℓ u → S ℓ w → u ≠ w → |u - w| ≤ (k : ℤ) →
      colRule S k n Δ ℓ u ≠ colRule S k n Δ ℓ w) ∧
    (∀ v, colRule S k n Δ ℓ v < max (16 * Δ ^ 2) 256) := by
  have hdeg' : ∀ v, (misGraph S k ℓ).degree v ≤ Δ := fun v => by
    by_cases hv : S ℓ v
    · rw [misGraph_degree v hv]; exact hdeg v hv
    · rw [misGraph_degree_eq_zero v hv]; omega
  have hc₀ : IsProper (misGraph S k ℓ) (misInit S ℓ) := by
    rintro u w ⟨hu, hw, huw, -⟩
    simp only [misInit, hu, hw, ite_true]
    exact fun h => huw (hℓ h)
  have hlt : ∀ v, misInit S ℓ v < max n 1 := by
    intro v
    unfold misInit
    split_ifs with h
    · exact lt_max_of_lt_left (hn v h)
    · exact lt_max_of_lt_right one_pos
  have hT : Nat.logStar (max n 1) + 3 ≤ Nat.logStar n + 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [Nat.logStar_of_le_one]
    · rw [max_eq_left hn0]
  exact ⟨fun u w hu hw huw hk => linial_isProper hdeg' hc₀ hlt _ ⟨hu, hw, huw, hk⟩,
    fun v => linial_lt hΔ hdeg' hc₀ hlt hT v⟩

/-! ### Locality -/

lemma abs_sub_le_add_of_le {x u v a b : ℤ} (h1 : |x - u| ≤ a) (h2 : |u - v| ≤ b) :
    |x - v| ≤ a + b := (abs_sub_le x u v).trans (add_le_add h1 h2)

section Local

variable {S : (ℤ → ℕ) → ℤ → Prop} {ρ : ℕ} (hS : IsLocal S ρ) (k n : ℕ) {ℓ ℓ' : ℤ → ℕ}
  (hℓ : Injective ℓ) (hℓ' : Injective ℓ')
include hS hℓ hℓ'

lemma S_eq_of_agree {v r : ℤ} (hr : (ρ : ℤ) ≤ r) (h : ∀ x, |x - v| ≤ r → ℓ' x = ℓ x) :
    S ℓ' v = S ℓ v :=
  hS ℓ ℓ' hℓ hℓ' v fun x hx => h x (hx.trans hr)

lemma misGraph_adj_iff_of_agree {v r : ℤ} (hr : (ρ : ℤ) + k ≤ r)
    (h : ∀ x, |x - v| ≤ r → ℓ' x = ℓ x) (u : ℤ) :
    (misGraph S k ℓ').Adj v u ↔ (misGraph S k ℓ).Adj v u := by
  have h0 : (0 : ℤ) ≤ k := by positivity
  by_cases hu : |v - u| ≤ (k : ℤ)
  · have h1 := S_eq_of_agree hS hℓ hℓ' (r := r) (by linarith) h
    have h2 : S ℓ' u = S ℓ u := hS ℓ ℓ' hℓ hℓ' u fun x hx =>
      h x ((abs_sub_le_add_of_le hx (abs_sub_comm v u ▸ hu)).trans (by linarith))
    simp only [misGraph_adj, h1, h2]
  · simp [misGraph_adj, hu]

lemma run_eq_of_agree (A : Algorithm ℕ) : ∀ (t : ℕ) (v r : ℤ), (ρ : ℤ) + k * t ≤ r →
    (∀ x, |x - v| ≤ r → ℓ' x = ℓ x) →
    A.run (misGraph S k ℓ') (misInit S ℓ') t v = A.run (misGraph S k ℓ) (misInit S ℓ) t v
  | 0, v, r, hr, h => by
    have h1 := S_eq_of_agree hS hℓ hℓ' (r := r) (by simpa using hr) h
    have h2 : ℓ' v = ℓ v := h v (by simp; omega)
    rw [Algorithm.run_zero, Algorithm.run_zero, misInit, misInit, h1, h2]
  | t + 1, v, r, hr, h => by
    have h0 : (0 : ℤ) ≤ k := by positivity
    have h0' : (0 : ℤ) ≤ k * t := by positivity
    have hr' : (ρ : ℤ) + k * t + k ≤ r := by push_cast at hr; linarith
    rw [Algorithm.run_succ_apply, Algorithm.run_succ_apply,
      run_eq_of_agree A t v r (by linarith) h]
    congr 1
    ext x
    simp only [mem_nbrColors]
    refine exists_congr fun u => ?_
    rw [misGraph_adj_iff_of_agree hS k hℓ hℓ' (r := r) (by linarith) h u]
    refine and_congr_right fun hadj => ?_
    have hk : |u - v| ≤ (k : ℤ) := by rw [abs_sub_comm]; exact hadj.2.2.2
    rw [run_eq_of_agree A t u (r - k) (by linarith) fun y hy =>
      h y ((abs_sub_le_add_of_le hy hk).trans (by linarith))]

lemma colRule_eq_of_agree (Δ : ℕ) {v r : ℤ} (hr : (ρ : ℤ) + k * (Nat.logStar n + 3) ≤ r)
    (h : ∀ x, |x - v| ≤ r → ℓ' x = ℓ x) : colRule S k n Δ ℓ' v = colRule S k n Δ ℓ v :=
  run_eq_of_agree hS k hℓ hℓ' _ _ v r (by push_cast; linarith) h

lemma misSweep_eq_of_agree : ∀ (c : ℕ) (v r : ℤ),
    (ρ : ℤ) + k * (Nat.logStar n + 3) + k * c ≤ r → (∀ x, |x - v| ≤ r → ℓ' x = ℓ x) →
    misSweep S k n ℓ' c v = misSweep S k n ℓ c v
  | 0, _, _, _, _ => rfl
  | c + 1, v, r, hr, h => by
    have h0 : (0 : ℤ) ≤ k * c := by positivity
    have h0' : (0 : ℤ) ≤ k := by positivity
    have hr' : (ρ : ℤ) + k * (Nat.logStar n + 3) + k * c + k ≤ r := by push_cast at hr; linarith
    have h0'' : (0 : ℤ) ≤ k * (Nat.logStar n + 3) := by positivity
    show (_ ∨ _) = (_ ∨ _)
    rw [misSweep_eq_of_agree c v r (by linarith) h, S_eq_of_agree hS hℓ hℓ' (r := r)
      (by linarith) h, colRule_eq_of_agree hS k n hℓ hℓ' 2 (by linarith) h]
    congr 3
    apply propext
    refine forall_congr' fun u => ?_
    rw [misGraph_adj_iff_of_agree hS k hℓ hℓ' (r := r) (by linarith) h u]
    refine imp_congr_right fun hadj => ?_
    have hk : |u - v| ≤ (k : ℤ) := by rw [abs_sub_comm]; exact hadj.2.2.2
    rw [misSweep_eq_of_agree c u (r - k) (by linarith) fun y hy =>
      h y ((abs_sub_le_add_of_le hy hk).trans (by linarith))]

end Local

/-- Locality of `colRule`: `log* n + 3` rounds of `G^k`, i.e. `k (log* n + 3)` rounds of the line
(on top of the radius `ρ` needed to compute `S`). -/
theorem colRule_isLocal {S : (ℤ → ℕ) → ℤ → Prop} {ρ : ℕ} (hS : IsLocal S ρ) (k n Δ : ℕ) :
    IsLocal (colRule S k n Δ) (ρ + k * (Nat.logStar n + 3)) :=
  fun _ _ hℓ hℓ' _ hv => colRule_eq_of_agree hS k n hℓ hℓ' Δ (le_of_eq (by push_cast; ring)) hv

/-! ### Equivariance -/

lemma misFrame_surjective (v : ℤ) (ε : ℤˣ) : Surjective (frame v ε) := fun u =>
  ⟨ε * (u - v), by rcases Int.units_eq_one_or ε with rfl | rfl <;> simp [frame]⟩

section Equivar

variable {S : (ℤ → ℕ) → ℤ → Prop} (hS : IsEquivar S) (k n : ℕ) (ℓ : ℤ → ℕ) (v : ℤ) (ε : ℤˣ)
include hS

lemma misGraph_adj_frame (i j : ℤ) :
    (misGraph S k (ℓ ∘ frame v ε)).Adj i j ↔ (misGraph S k ℓ).Adj (frame v ε i) (frame v ε j) := by
  simp only [misGraph_adj, hS ℓ v ε, abs_frame_sub_frame, (frame_injective v ε).ne_iff]

lemma run_frame (A : Algorithm ℕ) : ∀ (t : ℕ) (i : ℤ),
    A.run (misGraph S k (ℓ ∘ frame v ε)) (misInit S (ℓ ∘ frame v ε)) t i =
      A.run (misGraph S k ℓ) (misInit S ℓ) t (frame v ε i)
  | 0, i => by rw [Algorithm.run_zero, Algorithm.run_zero, misInit, misInit, hS ℓ v ε i]; rfl
  | t + 1, i => by
    rw [Algorithm.run_succ_apply, Algorithm.run_succ_apply, run_frame A t i]
    congr 1
    ext x
    simp only [mem_nbrColors]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨frame v ε j, (misGraph_adj_frame hS k ℓ v ε i j).1 hj, (run_frame A t j).symm⟩
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨j, rfl⟩ := misFrame_surjective v ε u
      exact ⟨j, (misGraph_adj_frame hS k ℓ v ε i j).2 hu, run_frame A t j⟩

lemma colRule_frame (Δ : ℕ) (i : ℤ) :
    colRule S k n Δ (ℓ ∘ frame v ε) i = colRule S k n Δ ℓ (frame v ε i) :=
  run_frame hS k ℓ v ε _ _ i

lemma misSweep_frame : ∀ (c : ℕ) (i : ℤ),
    misSweep S k n (ℓ ∘ frame v ε) c i = misSweep S k n ℓ c (frame v ε i)
  | 0, _ => rfl
  | c + 1, i => by
    show (_ ∨ _) = (_ ∨ _)
    rw [misSweep_frame c i, hS ℓ v ε, colRule_frame hS k n ℓ v ε]
    congr 3
    apply propext
    conv_rhs => rw [(misFrame_surjective v ε).forall]
    refine forall_congr' fun j => ?_
    rw [misGraph_adj_frame hS k ℓ v ε i j, misSweep_frame c j]

end Equivar

/-- `colRule` is computed on the unoriented line. -/
theorem colRule_isEquivar {S : (ℤ → ℕ) → ℤ → Prop} (hS : IsEquivar S) (k n Δ : ℕ) :
    IsEquivar (colRule S k n Δ) := fun ℓ v ε i => colRule_frame hS k n ℓ v ε Δ i

/-- **Lemma 2.1** (MIS on power graphs of sparse subsets of the line). If `S ℓ` is `p`-packed with
`k < 2p` (so that `G^k[S ℓ]` has maximum degree `2`) and labels on `S ℓ` are `< n`, then
`misRule S k n ℓ` is a maximal independent set of `G^k[S ℓ]`. -/
theorem misRule_spec (S : (ℤ → ℕ) → ℤ → Prop) (k n p : ℕ) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ)
    (hpack : Packed (S ℓ) p) (hk : k + 1 ≤ 2 * p) (hn : ∀ v, S ℓ v → ℓ v < n) :
    (∀ v, misRule S k n ℓ v → S ℓ v) ∧
    (∀ u w, misRule S k n ℓ u → misRule S k n ℓ w → u ≠ w → (k : ℤ) < |u - w|) ∧
    (∀ v, S ℓ v → ∃ w, misRule S k n ℓ w ∧ |w - v| ≤ (k : ℤ)) := by
  have hsub : ∀ v, misRule S k n ℓ v → S ℓ v := fun v => misSweep_sub 256 v
  obtain ⟨hprop, hcol⟩ := colRule_spec S k n 2 (by norm_num) hℓ
    (fun v hv => ncard_nbrs_le_two hpack hk hv) hn
  norm_num at hcol
  refine ⟨hsub, fun u w hu hw huw => ?_, fun v hv => ?_⟩
  · by_contra h
    push Not at h
    exact misSweep_indep (fun x y hxy => hprop x y hxy.1 hxy.2.1 hxy.2.2.1 hxy.2.2.2) 256 u w
      hu hw ⟨hsub u hu, hsub w hw, huw, h⟩
  · rcases misSweep_dom 256 v hv (hcol v) with h | ⟨u, hu, h⟩
    · exact ⟨v, h, by simp⟩
    · exact ⟨u, h, by rw [abs_sub_comm]; exact hu.2.2.2⟩

/-- Locality of `misRule` (Lemma 2.1: `O(log* n)` rounds of `G^k`, i.e. `O(k log* n)` rounds). -/
theorem misRule_isLocal {S : (ℤ → ℕ) → ℤ → Prop} {ρ : ℕ} (hS : IsLocal S ρ) (k n : ℕ) :
    IsLocal (misRule S k n) (ρ + k * (Nat.logStar n + 259)) :=
  fun _ _ hℓ hℓ' v hv => misSweep_eq_of_agree hS k n hℓ hℓ' 256 v _ (le_of_eq (by push_cast; ring)) hv

/-- `misRule` is computed on the unoriented line. -/
theorem misRule_isEquivar {S : (ℤ → ℕ) → ℤ → Prop} (hS : IsEquivar S) (k n : ℕ) :
    IsEquivar (misRule S k n) := fun ℓ v ε i => misSweep_frame hS k n ℓ v ε 256 i

end Podc.RendezvousLabeledLine
