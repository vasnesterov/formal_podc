import Mathlib

/-!
# Dispersers and robust committee assignment (Section 6 and Theorem 3.8)

Formalization of Section 6 ("Disperser") and Theorem 3.8 of
A. Constantinescu, M. Dufay, A. Paramonov, R. Wattenhofer,
*From Few to Many Faults: Optimal Adaptive Byzantine Agreement* (PODC 2026, arXiv 2505.19989).

* `IsDisperser` — Definition 6.1 for `ε = 1/2`, with a bipartite graph given by its left
  adjacency lists `adj : L → Finset R`.
* `exists_disperser` — existence of `(k, 1/2)` dispersers by a counting (union bound) argument.
  The paper only cites this fact (Theorem 6.2, Radhakrishnan–Ta-Shma); we prove it.
* `theorem_6_2` — the Theorem-6.2-shaped corollary: left degree `≤ 2 (⌈log₂ n⌉ + 1)` and
  `k = ⌈m / (⌈log₂ n⌉ + 1)⌉`, for all `n` and `m ≥ 1` (the paper's restriction `m ≤ n` is not needed).
* `Compromised`, `Blocked` — Definition 3.7.
* `theorem_3_8` — Theorem 3.8 with explicit constants: `(4f̂+1)(⌈log₂ n⌉+1)` committees,
  every party in at most `2(⌈log₂ n⌉+1)` committees, and at most `4 f̂` blocked parties
  (so `c_b = 4`) for every byzantine set of size `≤ f̂`. Unconditional (no `M ≤ N` side condition).
* `theorem_3_8_of_disperser` — the paper's own derivation of Theorem 3.8 from an abstract version
  of Theorem 6.2 with constants `c_d`, `c_k`; `theorem_6_2_constants` shows that hypothesis holds
  (with `c_d = c_k = 2`) in the range of `m` where it can hold at all.

Throughout, the paper's `log n` is rendered as `Nat.clog 2 n + 1` (`= ⌈log₂ n⌉ + 1`), which is
`Θ(log n)` and positive also for `n ≤ 1`.
-/

namespace Podc.FewToManyFaultsBA

open Finset

section Disperser

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq R]

/-- The neighbourhood `N(S) = ⋃_{u ∈ S} adj u` of a set `S` of left vertices in the bipartite
graph with left adjacency lists `adj`. -/
def nbhd (adj : L → Finset R) (S : Finset L) : Finset R := S.biUnion adj

/-- Definition 6.1 of the paper for `ε = 1/2`: the bipartite graph with left adjacency lists
`adj` is a `(k, 1/2)` disperser if every set `S` of at least `k` left vertices has
`|N(S)| ≥ |R| / 2`.

Difference from the paper: Definition 6.1 asks every left vertex to have degree exactly `d`; here
the degree bound `(adj u).card ≤ d` is stated separately wherever it is needed (a degree-`≤ d`
graph can be padded to an exactly-`d`-regular multigraph without shrinking neighbourhoods). -/
def IsDisperser (adj : L → Finset R) (k : ℕ) : Prop :=
  ∀ S : Finset L, k ≤ S.card → Fintype.card R ≤ 2 * (nbhd adj S).card

omit [Fintype L] [Fintype R] in
theorem nbhd_mono (adj : L → Finset R) {S T : Finset L} (h : S ⊆ T) :
    nbhd adj S ⊆ nbhd adj T :=
  biUnion_subset_biUnion_of_subset_left adj h

omit [Fintype L] [Fintype R] in
theorem mem_nbhd {adj : L → Finset R} {S : Finset L} {v : R} :
    v ∈ nbhd adj S ↔ ∃ u ∈ S, v ∈ adj u :=
  mem_biUnion

omit [Fintype L] in
/-- It suffices to check the disperser property on sets of size exactly `k`
(neighbourhoods are monotone). -/
theorem isDisperser_of_card_eq {adj : L → Finset R} {k : ℕ}
    (h : ∀ S : Finset L, S.card = k → Fintype.card R ≤ 2 * (nbhd adj S).card) :
    IsDisperser adj k := by
  intro S hS
  obtain ⟨T, hTS, hT⟩ := exists_subset_card_eq hS
  exact (h T hT).trans (Nat.mul_le_mul_left 2 (card_le_card (nbhd_mono adj hTS)))

/-- The functions `g : L → Fin d → R` (a left vertex `u` is joined to `g u 0, …, g u (d-1)`)
that send every edge out of `S` into `A`. -/
private def badSet [DecidableEq L] (d : ℕ) (S : Finset L) (A : Finset R) :
    Finset (L → Fin d → R) :=
  Fintype.piFinset fun u => if u ∈ S then Fintype.piFinset (fun _ : Fin d => A) else univ

omit [DecidableEq R] in
private theorem card_badSet [DecidableEq L] (d : ℕ) (S : Finset L) (A : Finset R) :
    (badSet d S A).card =
      (A.card ^ d) ^ S.card * (Fintype.card R ^ d) ^ (Fintype.card L - S.card) := by
  rw [badSet, Fintype.card_piFinset]
  simp only [apply_ite Finset.card, Fintype.card_piFinset, prod_const, card_univ,
    Fintype.card_fin, Fintype.card_fun]
  rw [prod_ite, prod_const, prod_const, filter_mem_eq_inter, univ_inter]
  congr 2
  rw [filter_not, filter_mem_eq_inter, univ_inter, card_sdiff_of_subset (subset_univ S), card_univ]

-- CSLib candidate
/-- **Existence of `(k, 1/2)` dispersers** (the content of Theorem 6.2, proved by counting).
If `k ⌈log₂ |L|⌉ + |R| < k d` (which forces `k ≥ 1`), there is a bipartite graph between `L` and `R` with
all left degrees at most `d` that is a `(k, 1/2)` disperser.

Proof: among all `|R|^{|L| d}` maps `g : L → Fin d → R`, a map is bad only if some `k`-set `S` has
`N(S)` inside some set `A` of size `⌊(|R|-1)/2⌋`; the union bound gives at most
`C(|L|,k) C(|R|,a) a^{kd} |R|^{(|L|-k)d} < |R|^{|L| d}` bad maps, using
`C(|L|,k) ≤ 2^{k ⌈log₂ |L|⌉}`, `C(|R|,a) ≤ 2^{|R|}` and `2a < |R|`. -/
theorem exists_disperser {k d : ℕ}
    (h : k * Nat.clog 2 (Fintype.card L) + Fintype.card R < k * d) :
    ∃ adj : L → Finset R, (∀ u, (adj u).card ≤ d) ∧ IsDisperser adj k := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card R) with hM | hM
  · exact ⟨fun _ => ∅, by simp, fun S _ => by simp [hM]⟩
  set N := Fintype.card L with hN
  set M := Fintype.card R with hMdef
  set a := (M - 1) / 2 with ha
  have h2a : 2 * a < M := by omega
  let B : Finset (L → Fin d → R) :=
    ((univ : Finset L).powersetCard k ×ˢ (univ : Finset R).powersetCard a).biUnion
      fun p => badSet d p.1 p.2
  have hB : B.card < (univ : Finset (L → Fin d → R)).card := by
    have hcardB : B.card ≤ N.choose k * M.choose a * ((a ^ d) ^ k * (M ^ d) ^ (N - k)) := by
      refine card_biUnion_le.trans ?_
      rw [sum_congr rfl fun p hp => ?_, sum_const, card_product, card_powersetCard,
        card_powersetCard, card_univ, card_univ, smul_eq_mul]
      · simp only [mem_product, mem_powersetCard] at hp
        rw [card_badSet, hp.1.2, hp.2.2]
    have huniv : (univ : Finset (L → Fin d → R)).card = (M ^ d) ^ N := by
      simp [hN, hMdef]
    rw [huniv]
    refine lt_of_le_of_lt hcardB ?_
    rcases lt_or_ge N k with hNk | hkN
    · rw [Nat.choose_eq_zero_of_lt hNk]
      simp only [zero_mul]
      positivity
    -- the key estimate `C(N,k) C(M,a) a^{dk} < M^{dk}`
    have hC : N.choose k * M.choose a < 2 ^ (d * k) := by
      calc N.choose k * M.choose a ≤ (2 ^ Nat.clog 2 N) ^ k * 2 ^ M :=
            Nat.mul_le_mul ((Nat.choose_le_pow N k).trans
              (Nat.pow_le_pow_left (Nat.le_pow_clog one_lt_two N) k))
              (Nat.choose_le_two_pow M a)
        _ = 2 ^ (k * Nat.clog 2 N + M) := by rw [← pow_mul, ← pow_add, mul_comm k]
        _ < 2 ^ (d * k) := Nat.pow_lt_pow_right one_lt_two (by rw [mul_comm d]; exact h)
    have hpow : 2 ^ (d * k) * a ^ (d * k) ≤ M ^ (d * k) := by
      rw [← mul_pow]; exact Nat.pow_le_pow_left h2a.le _
    have hMpos : 0 < M ^ (d * k) := by positivity
    have key : N.choose k * M.choose a * a ^ (d * k) < M ^ (d * k) := by
      refine Nat.lt_of_mul_lt_mul_left (a := 2 ^ (d * k)) ?_
      calc 2 ^ (d * k) * (N.choose k * M.choose a * a ^ (d * k))
          = N.choose k * M.choose a * (2 ^ (d * k) * a ^ (d * k)) := by ring
        _ ≤ N.choose k * M.choose a * M ^ (d * k) := Nat.mul_le_mul_left _ hpow
        _ < 2 ^ (d * k) * M ^ (d * k) := Nat.mul_lt_mul_of_pos_right hC hMpos
    have hsplit : (M ^ d) ^ N = (M ^ d) ^ k * (M ^ d) ^ (N - k) := by
      rw [← pow_add, Nat.add_sub_cancel' hkN]
    rw [pow_mul, pow_mul] at key
    rw [hsplit, ← mul_assoc]
    exact Nat.mul_lt_mul_of_pos_right key (by positivity)
  obtain ⟨g, -, hg⟩ := exists_mem_notMem_of_card_lt_card hB
  refine ⟨fun u => univ.image (g u), fun u => card_image_le.trans (by simp), ?_⟩
  apply isDisperser_of_card_eq
  intro S hS
  by_contra hlt
  push Not at hlt
  obtain ⟨A, hNA, -, hA⟩ := exists_subsuperset_card_eq (subset_univ (nbhd (fun u => univ.image (g u)) S))
    (show (nbhd (fun u => univ.image (g u)) S).card ≤ a by omega) (by rw [card_univ]; omega)
  apply hg
  simp only [B, mem_biUnion, mem_product, mem_powersetCard]
  refine ⟨(S, A), ⟨⟨subset_univ _, hS⟩, subset_univ _, hA⟩, ?_⟩
  simp only [badSet, Fintype.mem_piFinset]
  intro u
  split_ifs with hu
  · simp only [Fintype.mem_piFinset]
    intro i
    exact hNA (mem_nbhd.2 ⟨u, hu, mem_image_of_mem _ (mem_univ i)⟩)
  · exact mem_univ _

/-- The disperser size `k = ⌈m / (⌈log₂ n⌉ + 1)⌉` used in `theorem_6_2`, written as a natural
number ceiling division. -/
def dispK (n m : ℕ) : ℕ := (m + Nat.clog 2 n) / (Nat.clog 2 n + 1)

theorem one_le_dispK {n m : ℕ} (hm : 1 ≤ m) : 1 ≤ dispK n m :=
  (Nat.one_le_div_iff (Nat.succ_pos _)).2 (by omega)

theorem le_dispK_mul (n m : ℕ) : m ≤ dispK n m * (Nat.clog 2 n + 1) := by
  have h1 := Nat.div_add_mod (m + Nat.clog 2 n) (Nat.clog 2 n + 1)
  have h2 := Nat.mod_lt (m + Nat.clog 2 n) (show 0 < Nat.clog 2 n + 1 by omega)
  unfold dispK
  rw [mul_comm]
  omega

theorem dispK_mul_le (n m : ℕ) : dispK n m * (Nat.clog 2 n + 1) ≤ m + Nat.clog 2 n :=
  Nat.div_mul_le_self _ _

/-- **Theorem 6.2** (for `ε = 1/2`, with explicit constants). For all `n` and `m ≥ 1` there is a
`(k, 1/2)` disperser with `|L| = n`, `|R| = m`, left degree at most `2 (⌈log₂ n⌉ + 1) = O(log n)`
and `k = dispK n m = ⌈m / (⌈log₂ n⌉ + 1)⌉`, i.e. `k = O(m / log n)` (for `m ≥ log n`; always
`k ≥ 1`, see `one_le_dispK`). The paper's hypothesis `m ≤ n` is not needed. -/
theorem theorem_6_2 (n m : ℕ) (hm : 1 ≤ m) :
    ∃ adj : Fin n → Finset (Fin m), (∀ u, (adj u).card ≤ 2 * (Nat.clog 2 n + 1)) ∧
      IsDisperser adj (dispK n m) := by
  apply exists_disperser
  simp only [Fintype.card_fin]
  have h1 := le_dispK_mul n m
  have h2 := one_le_dispK (n := n) hm
  have : dispK n m * (2 * (Nat.clog 2 n + 1)) =
      dispK n m * Nat.clog 2 n + dispK n m * (Nat.clog 2 n + 1) + dispK n m := by ring
  omega

end Disperser

section Committees

variable {P C : Type*}

/-- Definition 3.7: under the assignment `assign` of parties to (sets of) committees and the set
`F` of byzantine parties, committee `c` is *compromised* if it contains a byzantine party. -/
def Compromised (assign : P → Finset C) (F : Finset P) (c : C) : Prop :=
  ∃ p ∈ F, c ∈ assign p

/-- Definition 3.7: party `p` is *blocked* if all committees it is assigned to are compromised. -/
def Blocked (assign : P → Finset C) (F : Finset P) (p : P) : Prop :=
  ∀ c ∈ assign p, Compromised assign F c

instance [DecidableEq C] (assign : P → Finset C) (F : Finset P) :
    DecidablePred (Blocked assign F) :=
  fun _ => by unfold Blocked Compromised; infer_instance

/-- Byzantine parties are blocked (used in Lemma 8.8). -/
theorem blocked_of_mem {assign : P → Finset C} {F : Finset P} {p : P} (hp : p ∈ F) :
    Blocked assign F p :=
  fun _ hc => ⟨p, hp, hc⟩

/-- A party that is not blocked is assigned to some committee containing no byzantine party
(used in Lemma 8.8). -/
theorem exists_clean_committee_of_not_blocked {assign : P → Finset C} {F : Finset P} {p : P}
    (h : ¬ Blocked assign F p) : ∃ c ∈ assign p, ∀ q ∈ F, c ∉ assign q := by
  simpa [Blocked, Compromised] using h

/-- A non-blocked party is honest. -/
theorem not_mem_of_not_blocked {assign : P → Finset C} {F : Finset P} {p : P}
    (h : ¬ Blocked assign F p) : p ∉ F :=
  fun hp => h (blocked_of_mem hp)

/-- The core of the proof of Theorem 3.8 (Observations I and II): if the assignment is a
`(k, 1/2)` disperser with degrees at most `d` and there are more than `2 f d` committees, then
any set of at most `f` byzantine parties blocks fewer than `k` parties. -/
theorem card_blocked_lt [Fintype P] [Fintype C] [DecidableEq C] {assign : P → Finset C}
    {k d f : ℕ} (hdisp : IsDisperser assign k) (hdeg : ∀ p, (assign p).card ≤ d)
    (hM : 2 * (f * d) < Fintype.card C) {F : Finset P} (hF : F.card ≤ f) :
    (univ.filter (Blocked assign F)).card < k := by
  by_contra hk
  push Not at hk
  have h1 := hdisp _ hk
  -- Observation II: at most `f d` committees are compromised
  have hsub : nbhd assign (univ.filter (Blocked assign F)) ⊆ nbhd assign F := by
    intro c hc
    obtain ⟨p, hp, hcp⟩ := mem_nbhd.1 hc
    obtain ⟨q, hq, hcq⟩ := (mem_filter.1 hp).2 c hcp
    exact mem_nbhd.2 ⟨q, hq, hcq⟩
  have h2 : (nbhd assign F).card ≤ f * d :=
    card_biUnion_le.trans <| (sum_le_card_nsmul _ _ d fun p _ => hdeg p).trans <| by
      rw [smul_eq_mul]; exact Nat.mul_le_mul_right d hF
  have h3 := card_le_card hsub
  omega

/-- **Theorem 3.8** with explicit constants. Given `n` parties and `f̂`, there is an assignment of
the parties to `M = (4 f̂ + 1)(⌈log₂ n⌉ + 1) = O(f̂ log n)` committees such that
1. there are `M` committees;
2. every party is in at most `2 (⌈log₂ n⌉ + 1) = O(log n)` committees;
3. for every set `F` of at most `f̂` byzantine parties — chosen after the assignment, hence the
   quantifier order — at most `4 f̂` parties are blocked (`c_b = 4`).

Unlike the paper's proof, this does not need `M ≤ n` (the disperser is built directly by
`exists_disperser`) and also covers `f̂ = 0`. -/
theorem theorem_3_8 (n f : ℕ) :
    ∃ (M : ℕ) (assign : Fin n → Finset (Fin M)),
      M = (4 * f + 1) * (Nat.clog 2 n + 1) ∧
      (∀ p, (assign p).card ≤ 2 * (Nat.clog 2 n + 1)) ∧
      ∀ F : Finset (Fin n), F.card ≤ f → (univ.filter (Blocked assign F)).card ≤ 4 * f := by
  set ℓ := Nat.clog 2 n + 1 with hℓ
  obtain ⟨assign, hdeg, hdisp⟩ := exists_disperser (L := Fin n) (R := Fin ((4 * f + 1) * ℓ))
    (k := 4 * f + 1) (d := 2 * ℓ) (by
      simp only [Fintype.card_fin]
      rw [← mul_add]
      exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega))
  refine ⟨_, assign, rfl, hdeg, fun F hF => ?_⟩
  have := card_blocked_lt hdisp hdeg (f := f) (by
    simp only [Fintype.card_fin]
    have : 2 * (f * (2 * ℓ)) + ℓ = (4 * f + 1) * ℓ := by ring
    omega) hF
  omega

/-- The paper's derivation of Theorem 3.8 from Theorem 6.2 with unpacked constants `c_d`, `c_k`:
assuming dispersers with `|L| = N`, `|R| = M`, degree `≤ c_d log N` and `k ≤ c_k M / log N`
exist (here: `k (⌈log₂ N⌉ + 1) ≤ c_k M`), whenever `log N ≤ M ≤ N`, then for `f̂ ≥ 1` with
`M := 4 c_d f̂ log n ≤ n` there is an assignment to `M` committees, each party in
`≤ c_d log n` committees, with fewer than `c_b f̂ = 4 c_k c_d f̂` blocked parties.

The hypothesis is restricted to `log N ≤ M`: for `1 ≤ M` much smaller than `log N` the paper's
unpacked Theorem 6.2 would force `k = 0`, which is impossible. `theorem_6_2_constants` shows the
restricted hypothesis holds with `c_d = c_k = 2`. -/
theorem theorem_3_8_of_disperser (c_d c_k : ℕ)
    (H : ∀ N M : ℕ, Nat.clog 2 N + 1 ≤ M → M ≤ N → ∃ (k : ℕ) (adj : Fin N → Finset (Fin M)),
      (∀ u, (adj u).card ≤ c_d * (Nat.clog 2 N + 1)) ∧ k * (Nat.clog 2 N + 1) ≤ c_k * M ∧
      IsDisperser adj k)
    (n f : ℕ) (hf : 1 ≤ f) (hcd : 1 ≤ c_d) (hMn : 4 * c_d * f * (Nat.clog 2 n + 1) ≤ n) :
    ∃ assign : Fin n → Finset (Fin (4 * c_d * f * (Nat.clog 2 n + 1))),
      (∀ p, (assign p).card ≤ c_d * (Nat.clog 2 n + 1)) ∧
      ∀ F : Finset (Fin n), F.card ≤ f →
        (univ.filter (Blocked assign F)).card < 4 * c_k * c_d * f := by
  set ℓ := Nat.clog 2 n + 1 with hℓ
  have hℓpos : 0 < ℓ := Nat.succ_pos _
  have hfc : 1 ≤ c_d * f := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hlog : ℓ ≤ 4 * c_d * f * ℓ := by
    calc ℓ = 1 * ℓ := (one_mul ℓ).symm
      _ ≤ 4 * c_d * f * ℓ := Nat.mul_le_mul_right ℓ (by nlinarith)
  obtain ⟨k, assign, hdeg, hk, hdisp⟩ := H n _ hlog hMn
  rw [← hℓ] at hdeg hk
  refine ⟨assign, hdeg, fun F hF => ?_⟩
  have hlt := card_blocked_lt hdisp hdeg (f := f) (by
    simp only [Fintype.card_fin]
    have h0 : 0 < f * (c_d * ℓ) := by positivity
    have : 4 * c_d * f * ℓ = 2 * (f * (c_d * ℓ)) + 2 * (f * (c_d * ℓ)) := by ring
    omega) hF
  have hk' : k ≤ 4 * c_k * c_d * f := by
    refine Nat.le_of_mul_le_mul_right ?_ hℓpos
    calc k * ℓ ≤ c_k * (4 * c_d * f * ℓ) := hk
      _ = 4 * c_k * c_d * f * ℓ := by ring
  omega

/-- Non-vacuity of `theorem_3_8_of_disperser`: its hypothesis (unpacked Theorem 6.2 for
`log N ≤ M ≤ N`) holds with `c_d = c_k = 2`, by `theorem_6_2`. -/
theorem theorem_6_2_constants :
    ∀ N M : ℕ, Nat.clog 2 N + 1 ≤ M → M ≤ N → ∃ (k : ℕ) (adj : Fin N → Finset (Fin M)),
      (∀ u, (adj u).card ≤ 2 * (Nat.clog 2 N + 1)) ∧ k * (Nat.clog 2 N + 1) ≤ 2 * M ∧
      IsDisperser adj k := by
  intro N M hM _
  obtain ⟨adj, hdeg, hdisp⟩ := theorem_6_2 N M (by omega)
  exact ⟨_, adj, hdeg, by have := dispK_mul_le N M; omega, hdisp⟩

end Committees

end Podc.FewToManyFaultsBA
