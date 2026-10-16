import Papers.PODC2011.FaultTolerantSpanners.TwoSpanner.Defs

/-!
# Lemma 3.1, exactness of IP (3), validity of LP (4), Lemma 3.2 (core) and the integrality gap
example of Section 3.2 of Dinitz–Krauthgamer [DK11]

[DK11] M. Dinitz, R. Krauthgamer, *Fault-Tolerant Spanners: Better and Simpler*, PODC 2011
(arXiv 1101.5753).

* `isFTSpanner_two_iff` — **Lemma 3.1**: `H ⊆ E` is an `r`-fault-tolerant 2-spanner of the
  (loopless, directed, unit-length) graph `(V, E)` iff it satisfies every arc of `E`.
* `IsIP3Feasible` — integer program (3), written literally.
* `isFTSpanner_iff_exists_ip3` — IP (3) is an exact formulation ("it is easy to see …").
* `IsIP3Feasible.toLP4` — the knapsack-cover inequalities are valid for IP (3); every integral
  feasible solution of IP (3) is feasible for LP (4).
* `exists_lp4_of_isFTSpanner` — consequently `LP (4) ≤ OPT`.
* `sum_sdiff_le_of_top`, `exists_top_subset`, `knapsack_of_top` — the core of **Lemma 3.2**
  (separation oracle): for a fixed arc and a fixed size `j`, the hardest knapsack-cover constraint
  is the one for the `j` paths of largest flow. (Running time / the Ellipsoid method are not
  modelled.)
* `GapExample` — the integrality-gap example of Section 3.2 for the plain relaxation of IP (3).
-/

open Finset

namespace DinitzKrauthgamer

variable {V : Type*}

/-! ### Directed walks -/

namespace DWalk

variable {E H : Finset (V × V)} {F : Finset V}

lemma append {u w v : V} {m n : ℕ} (h₁ : DWalk E F u w m) (h₂ : DWalk E F w v n) :
    DWalk E F u v (m + n) := by
  induction h₁ with
  | nil u => simpa using h₂
  | cons hE hu hw _ ih =>
    have := DWalk.cons hE hu hw (ih h₂)
    rwa [Nat.add_right_comm] at this

lemma single {u v : V} (h : (u, v) ∈ E) (hu : u ∉ F) (hv : v ∉ F) : DWalk E F u v 1 :=
  .cons h hu hv (.nil v)

lemma two {u z v : V} (h₁ : (u, z) ∈ E) (h₂ : (z, v) ∈ E) (hu : u ∉ F) (hz : z ∉ F)
    (hv : v ∉ F) : DWalk E F u v 2 :=
  .cons h₁ hu hz (single h₂ hz hv)

lemma mono (hHE : H ⊆ E) {u v : V} {n : ℕ} (h : DWalk H F u v n) : DWalk E F u v n := by
  induction h with
  | nil u => exact .nil u
  | cons hH hu hw _ ih => exact .cons (hHE hH) hu hw ih

lemma eq_of_length_zero {u v : V} (h : DWalk E F u v 0) : u = v := by
  cases h; rfl

lemma of_length_one {u v : V} (h : DWalk E F u v 1) : (u, v) ∈ E ∧ u ∉ F ∧ v ∉ F := by
  cases h with
  | cons hE hu hw h' => cases h'; exact ⟨hE, hu, hw⟩

lemma of_length_two {u v : V} (h : DWalk E F u v 2) :
    ∃ z, (u, z) ∈ E ∧ (z, v) ∈ E ∧ u ∉ F ∧ z ∉ F ∧ v ∉ F := by
  cases h with
  | cons hE hu hw h' =>
    obtain ⟨h1, h2, h3⟩ := h'.of_length_one
    exact ⟨_, hE, h1, hu, h2, h3⟩

end DWalk

variable [Fintype V] [DecidableEq V]

lemma mids_mono {E H : Finset (V × V)} (h : H ⊆ E) (u v : V) : mids H u v ⊆ mids E u v := by
  intro z hz
  rw [mem_mids] at hz ⊢
  exact ⟨h hz.1, h hz.2⟩

/-! ### Lemma 3.1 -/

/-- **Lemma 3.1 of [DK11].** For a loopless directed graph `G = (V, E)` with unit lengths, a
subgraph `H ⊆ E` is an `r`-fault-tolerant 2-spanner iff for every `(u, v) ∈ E` either
`(u, v) ∈ H` or `H` contains at least `r + 1` paths of length 2 from `u` to `v`.

(In the "only if" direction the paper claims that `H \ W` has *no* `u`–`v` path, `W` being the set
of midpoints; only "no `u`–`v` path of length `≤ 2`" holds, which suffices.) -/
theorem isFTSpanner_two_iff {E H : Finset (V × V)} {r : ℕ} (hE : Loopless E) (hHE : H ⊆ E) :
    IsFTSpanner E H r 2 ↔ ∀ uv ∈ E, Satisfies H r uv := by
  constructor
  · rintro ⟨-, hsp⟩ ⟨u, v⟩ huv
    by_contra hns
    simp only [Satisfies, not_or, not_le] at hns
    obtain ⟨hnot, hcard⟩ := hns
    have huF : u ∉ mids H u v := fun h => hnot (mem_mids.mp h).2
    have hvF : v ∉ mids H u v := fun h => hnot (mem_mids.mp h).1
    obtain ⟨m, hm, hw⟩ :=
      hsp (mids H u v) (by omega) u v huF hvF 1 (DWalk.single huv huF hvF)
    interval_cases m
    · exact hE _ huv hw.eq_of_length_zero
    · exact hnot hw.of_length_one.1
    · obtain ⟨z, h1, h2, -, hz, -⟩ := hw.of_length_two
      exact hz (mem_mids.mpr ⟨h1, h2⟩)
  · intro hsat
    refine ⟨hHE, fun F hF u v hu hv n hw => ?_⟩
    clear hu hv
    induction hw with
    | nil u => exact ⟨0, le_refl _, .nil u⟩
    | @cons a b w n hab ha hb _ ih =>
      obtain ⟨m, hm, hw'⟩ := ih
      rcases hsat _ hab with h | h
      · exact ⟨m + 1, by omega, .cons h ha hb hw'⟩
      · obtain ⟨z, hz, hzF⟩ := Finset.exists_mem_notMem_of_card_lt_card
          (s := F) (t := mids H a b) (by simp only at h; omega)
        rw [mem_mids] at hz
        exact ⟨2 + m, by omega, (DWalk.two hz.1 hz.2 ha hzF hb).append hw'⟩

/-! ### IP (3) is exact, and LP (4) is a relaxation -/

/-- Feasibility for the **integer program (3)** of [DK11]: capacity constraints (as in LP (4)),
covering constraints `(r + 1) x_{(u,v)} + ∑_{P ∈ P_{u,v}} f_P ≥ r + 1`, `x_e ∈ {0, 1}`, `f_P ≥ 0`. -/
structure IsIP3Feasible (E : Finset (V × V)) (r : ℕ) (x : V × V → ℝ) (f : V × V → V → ℝ) :
    Prop where
  /-- Capacity constraints `∑_{P ∈ P_{u,v} : e ∈ P} f_P ≤ x_e`. -/
  capacity : ∀ uv ∈ E, ∀ e ∈ E,
    ∑ z ∈ (mids E uv.1 uv.2).filter (fun z => (uv.1, z) = e ∨ (z, uv.2) = e), f uv z ≤ x e
  /-- Covering constraints `(r + 1) x_{(u,v)} + ∑_{P ∈ P_{u,v}} f_P ≥ r + 1`. -/
  cover : ∀ uv ∈ E, ((r : ℝ) + 1) * x uv + ∑ z ∈ mids E uv.1 uv.2, f uv z ≥ (r : ℝ) + 1
  /-- Integrality `x_e ∈ {0, 1}`. -/
  x_binary : ∀ e ∈ E, x e = 0 ∨ x e = 1
  /-- `f_P ≥ 0`. -/
  f_nonneg : ∀ uv ∈ E, ∀ z ∈ mids E uv.1 uv.2, 0 ≤ f uv z

/-- The `0/1` indicator vector of an arc set. -/
def arcInd (H : Finset (V × V)) : V × V → ℝ := fun e => if e ∈ H then 1 else 0

/-- The `0/1` flow of a subgraph `H`: one unit on each length-2 path of `H`. -/
def pathInd (H : Finset (V × V)) : V × V → V → ℝ :=
  fun uv z => if z ∈ mids H uv.1 uv.2 then 1 else 0

/-- In a loopless graph, a single arc `e` lies on at most one length-2 path from `u` to `v`. -/
lemma card_filter_uses_le_one {E : Finset (V × V)} (hE : Loopless E) (u v : V) (e : V × V) :
    #((mids E u v).filter (fun z => (u, z) = e ∨ (z, v) = e)) ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [mem_filter, mem_mids] at ha hb
  obtain ⟨⟨ha1, ha2⟩, ha3⟩ := ha
  obtain ⟨⟨hb1, hb2⟩, hb3⟩ := hb
  rcases ha3 with rfl | rfl <;> rcases hb3 with h | h <;>
    simp only [Prod.mk.injEq] at h
  · exact h.2.symm
  · exact absurd h.1.symm (hE _ hb1)
  · exact absurd h.1 (hE _ ha1)
  · exact h.1.symm

/-- A sum over a set with at most one element is bounded by any common nonnegative bound. -/
lemma sum_le_of_card_le_one {ι : Type*} {s : Finset ι} {g : ι → ℝ} {t : ℝ} (hs : #s ≤ 1)
    (hg : ∀ i ∈ s, g i ≤ t) (ht : 0 ≤ t) : ∑ i ∈ s, g i ≤ t := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i, -⟩
  · simpa using ht
  have : Nonempty ι := ⟨i⟩
  obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hs
  rcases Finset.subset_singleton_iff.mp ha with rfl | rfl
  · simpa using ht
  · simpa using hg a (by simp)

namespace IsIP3Feasible

variable {E : Finset (V × V)} {r : ℕ} {x : V × V → ℝ} {f : V × V → V → ℝ}

lemma x_nonneg (h : IsIP3Feasible E r x f) {e : V × V} (he : e ∈ E) : 0 ≤ x e := by
  rcases h.x_binary e he with h | h <;> simp [h]

lemma x_le_one (h : IsIP3Feasible E r x f) {e : V × V} (he : e ∈ E) : x e ≤ 1 := by
  rcases h.x_binary e he with h | h <;> simp [h]

lemma flow_le_left (h : IsIP3Feasible E r x f) {uv : V × V} (huv : uv ∈ E) {z : V}
    (hz : z ∈ mids E uv.1 uv.2) : f uv z ≤ x (uv.1, z) := by
  refine le_trans ?_ (h.capacity uv huv _ (mem_mids.mp hz).1)
  refine Finset.single_le_sum (f := fun z => f uv z) (fun z hz' => h.f_nonneg uv huv z ?_) ?_
  · exact (Finset.mem_filter.mp hz').1
  · exact Finset.mem_filter.mpr ⟨hz, Or.inl rfl⟩

/-- Validity of the knapsack-cover inequalities (Section 3.2 of [DK11]): every feasible solution
of IP (3) is feasible for LP (4). Note that `f_P ≤ 1` (used for `P ∈ W`) follows from the capacity
constraints. -/
theorem toLP4 (h : IsIP3Feasible E r x f) : IsLP4Feasible E r x f where
  capacity := h.capacity
  knapsack := by
    intro uv huv W hW hWr
    have hsum := h.f_nonneg uv huv
    rcases h.x_binary uv huv with h0 | h1
    · have hc := h.cover uv huv
      rw [h0, mul_zero, zero_add] at hc
      rw [h0, mul_zero, zero_add]
      have hsplit := Finset.sum_sdiff hW (f := fun z => f uv z)
      have hWle : ∑ z ∈ W, f uv z ≤ #W := by
        have : ∑ z ∈ W, f uv z ≤ ∑ z ∈ W, (1 : ℝ) := Finset.sum_le_sum fun z hz =>
          (h.flow_le_left huv (hW hz)).trans (h.x_le_one (mem_mids.mp (hW hz)).1)
        simpa using this
      linarith
    · rw [h1, mul_one]
      have : 0 ≤ ∑ z ∈ mids E uv.1 uv.2 \ W, f uv z :=
        Finset.sum_nonneg fun z hz => hsum z (Finset.mem_sdiff.mp hz).1
      linarith
  x_nonneg := fun _ he => h.x_nonneg he
  x_le_one := fun _ he => h.x_le_one he
  f_nonneg := h.f_nonneg

end IsIP3Feasible

/-- Exactness of IP (3) (Section 3.2 of [DK11]: "it is easy to see that the following integer
program is an exact formulation"): for a loopless `E` and `H ⊆ E`, `H` is an `r`-fault-tolerant
2-spanner iff its indicator vector extends (with some flow `f`) to a feasible solution of IP (3). -/
theorem isFTSpanner_iff_exists_ip3 {E H : Finset (V × V)} {r : ℕ} (hE : Loopless E)
    (hHE : H ⊆ E) : IsFTSpanner E H r 2 ↔ ∃ f, IsIP3Feasible E r (arcInd H) f := by
  rw [isFTSpanner_two_iff hE hHE]
  constructor
  · intro hsat
    refine ⟨pathInd H, ⟨?_, ?_, ?_, ?_⟩⟩
    · intro uv _ e he
      by_cases heH : e ∈ H
      · refine sum_le_of_card_le_one (card_filter_uses_le_one hE _ _ _) (fun z _ => ?_)
          (by simp [arcInd, heH])
        simp only [pathInd, arcInd, heH, ite_true]
        split_ifs <;> norm_num
      · have : ∀ z ∈ (mids E uv.1 uv.2).filter (fun z => (uv.1, z) = e ∨ (z, uv.2) = e),
            pathInd H uv z = 0 := by
          intro z hz
          simp only [mem_filter] at hz
          simp only [pathInd, mem_mids, ite_eq_right_iff, one_ne_zero, imp_false, not_and]
          intro h1 h2
          rcases hz.2 with rfl | rfl <;> contradiction
        rw [Finset.sum_eq_zero this]
        simp [arcInd, heH]
    · intro uv huv
      have hnn : 0 ≤ ∑ z ∈ mids E uv.1 uv.2, pathInd H uv z :=
        Finset.sum_nonneg fun z _ => by simp only [pathInd]; split_ifs <;> norm_num
      rcases hsat uv huv with h | h
      · simp only [arcInd, h, ite_true, mul_one]; linarith
      · have : ∑ z ∈ mids E uv.1 uv.2, pathInd H uv z = #(mids H uv.1 uv.2) := by
          simp only [pathInd]
          rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
            Finset.inter_eq_right.mpr (mids_mono hHE _ _)]
        rw [this]
        have hx : 0 ≤ arcInd H uv := by simp only [arcInd]; split_ifs <;> norm_num
        have : ((r : ℝ) + 1) ≤ #(mids H uv.1 uv.2) := by exact_mod_cast h
        nlinarith
    · intro e _; simp only [arcInd]; split_ifs <;> simp
    · intro uv _ z _; simp only [pathInd]; split_ifs <;> norm_num
  · rintro ⟨f, hf⟩ uv huv
    by_cases h : uv ∈ H
    · exact Or.inl h
    · right
      have hc := hf.cover uv huv
      simp only [arcInd, h, ite_false, mul_zero, zero_add] at hc
      have hlp := hf.toLP4
      have hle : ∑ z ∈ mids E uv.1 uv.2, f uv z ≤
          ∑ z ∈ mids E uv.1 uv.2, (if z ∈ mids H uv.1 uv.2 then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun z hz => ?_
        have h1 := hlp.flow_le_left huv hz
        have h2 := hlp.flow_le_right huv hz
        simp only [arcInd] at h1 h2
        by_cases hzH : z ∈ mids H uv.1 uv.2
        · rw [ite_eq_left hzH]; rw [mem_mids] at hzH; simpa [hzH.1] using h1
        · rw [ite_eq_right hzH]; rw [mem_mids, not_and_or] at hzH
          rcases hzH with h' | h'
          · simpa [h'] using h1
          · simpa [h'] using h2
      rw [Finset.sum_boole, Finset.filter_mem_eq_inter,
        Finset.inter_eq_right.mpr (mids_mono hHE _ _)] at hle
      exact_mod_cast hc.trans hle

/-- Every feasible solution `(x, f)` of IP (3) (for loopless `E`) yields the `r`-fault-tolerant
2-spanner `{e ∈ E | x_e = 1}`, of cost equal to the objective value `∑_e c_e x_e`. -/
theorem IsIP3Feasible.isFTSpanner {E : Finset (V × V)} {r : ℕ} {x : V × V → ℝ}
    {f : V × V → V → ℝ} (hE : Loopless E) (h : IsIP3Feasible E r x f) (c : V × V → ℝ) :
    IsFTSpanner E (E.filter fun e => x e = 1) r 2 ∧
      cost c (E.filter fun e => x e = 1) = lpValue c E x := by
  set H := E.filter fun e => x e = 1
  have hxE : ∀ e ∈ E, x e = arcInd H e := by
    intro e he
    simp only [arcInd, H, mem_filter, he, true_and]
    rcases h.x_binary e he with h0 | h1
    · rw [h0]; norm_num
    · rw [ite_eq_left h1, h1]
  constructor
  · refine (isFTSpanner_iff_exists_ip3 hE (Finset.filter_subset _ _)).mpr ⟨f, ?_⟩
    refine ⟨fun uv huv e he => ?_, fun uv huv => ?_, fun e he => ?_, h.f_nonneg⟩
    · rw [← hxE e he]; exact h.capacity uv huv e he
    · rw [← hxE uv huv]; exact h.cover uv huv
    · rw [← hxE e he]; exact h.x_binary e he
  · simp only [cost, lpValue, H, Finset.sum_filter]
    refine Finset.sum_congr rfl fun e he => ?_
    rcases h.x_binary e he with h0 | h1
    · rw [h0]; simp
    · rw [ite_eq_left h1, h1, mul_one]

/-- `LP (4) ≤ OPT` (Section 3.2 of [DK11]): every `r`-fault-tolerant 2-spanner `H` of a loopless
`E` gives a feasible solution of LP (4) whose value is the cost of `H`. -/
theorem exists_lp4_of_isFTSpanner {E H : Finset (V × V)} {r : ℕ} (hE : Loopless E)
    (hH : IsFTSpanner E H r 2) (c : V × V → ℝ) :
    ∃ x f, IsLP4Feasible E r x f ∧ lpValue c E x = cost c H := by
  obtain ⟨f, hf⟩ := (isFTSpanner_iff_exists_ip3 hE hH.1).mp hH
  refine ⟨arcInd H, f, hf.toLP4, ?_⟩
  simp only [lpValue, cost, arcInd, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hH.1]

/-! ### Lemma 3.2: the separation oracle for the knapsack-cover constraints -/

/-- Core of the separation oracle of **Lemma 3.2 of [DK11]**: if `W₀ ⊆ P` has the same size as
`W ⊆ P` and consists of paths of largest flow (every flow in `W₀` is at least every flow in
`P \ W₀`), then `∑_{P \ W₀} f ≤ ∑_{P \ W} f`; i.e. among the knapsack-cover constraints with
`|W| = j` the one for the `j` paths of largest flow is the hardest. -/
theorem sum_sdiff_le_of_top {ι : Type*} [DecidableEq ι] {g : ι → ℝ} {P W W₀ : Finset ι}
    (hW : W ⊆ P) (hW₀ : W₀ ⊆ P) (hcard : #W₀ = #W)
    (htop : ∀ a ∈ W₀, ∀ b ∈ P \ W₀, g b ≤ g a) :
    ∑ z ∈ P \ W₀, g z ≤ ∑ z ∈ P \ W, g z := by
  have h1 := Finset.sum_sdiff hW (f := g)
  have h2 := Finset.sum_sdiff hW₀ (f := g)
  have h3 := Finset.sum_inter_add_sum_sdiff W W₀ g
  have h4 := Finset.sum_inter_add_sum_sdiff W₀ W g
  rw [Finset.inter_comm] at h4
  have hc1 := Finset.card_sdiff_add_card_inter W W₀
  have hc2 := Finset.card_sdiff_add_card_inter W₀ W
  rw [Finset.inter_comm] at hc2
  have hcd : #(W \ W₀) = #(W₀ \ W) := by omega
  suffices key : ∑ z ∈ W \ W₀, g z ≤ ∑ z ∈ W₀ \ W, g z by linarith
  rcases (W \ W₀).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.card_empty] at hcd
    rw [he, Finset.card_eq_zero.mp hcd.symm]
  · obtain ⟨b, hb, hbt⟩ := Finset.exists_mem_eq_sup' hne g
    have hbP : b ∈ P \ W₀ := by
      rw [Finset.mem_sdiff] at hb ⊢; exact ⟨hW hb.1, hb.2⟩
    calc ∑ z ∈ W \ W₀, g z ≤ #(W \ W₀) • (W \ W₀).sup' hne g :=
          Finset.sum_le_card_nsmul _ _ _ fun z hz => Finset.le_sup' g hz
      _ = #(W₀ \ W) • g b := by rw [hcd, hbt]
      _ ≤ ∑ z ∈ W₀ \ W, g z :=
          Finset.card_nsmul_le_sum _ _ _ fun a ha => htop a (Finset.mem_sdiff.mp ha).1 b hbP

/-- Existence of the set of the `j` paths of largest flow (used in Lemma 3.2 of [DK11]). -/
theorem exists_top_subset {ι : Type*} [DecidableEq ι] (g : ι → ℝ) (P : Finset ι) {j : ℕ}
    (hj : j ≤ #P) : ∃ W₀ ⊆ P, #W₀ = j ∧ ∀ a ∈ W₀, ∀ b ∈ P \ W₀, g b ≤ g a := by
  induction j with
  | zero => exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  | succ j ih =>
    obtain ⟨W₀, hsub, hcard, htop⟩ := ih (by omega)
    have hne : (P \ W₀).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub]; omega
    obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image (P \ W₀) g hne
    have hmW : m ∉ W₀ := (Finset.mem_sdiff.mp hm).2
    refine ⟨insert m W₀, Finset.insert_subset (Finset.mem_sdiff.mp hm).1 hsub, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hmW, hcard]
    · intro a ha b hb
      have hb' : b ∈ P \ W₀ := by
        simp only [Finset.mem_sdiff, Finset.mem_insert, not_or] at hb ⊢
        exact ⟨hb.1, hb.2.2⟩
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact hmax b hb'
      · exact htop a ha b hb'

/-- **Lemma 3.2 of [DK11]** (correctness of the separation oracle): for a fixed arc `uv`, the
knapsack-cover constraints for all `W ⊆ P_{u,v}` with `|W| ≤ r` hold iff, for every `j ≤ r`, the
constraint holds for one (any) chosen set `top j` of `j` paths of largest flow. -/
theorem knapsack_iff_top {E : Finset (V × V)} {r : ℕ} {x : V × V → ℝ} {f : V × V → V → ℝ}
    {uv : V × V} (top : ℕ → Finset V)
    (htop : ∀ j ≤ r, j ≤ #(mids E uv.1 uv.2) → top j ⊆ mids E uv.1 uv.2 ∧ #(top j) = j ∧
      ∀ a ∈ top j, ∀ b ∈ mids E uv.1 uv.2 \ top j, f uv b ≤ f uv a) :
    (∀ W ⊆ mids E uv.1 uv.2, #W ≤ r →
        ((r : ℝ) + 1 - #W) * x uv + ∑ z ∈ mids E uv.1 uv.2 \ W, f uv z ≥ (r : ℝ) + 1 - #W) ↔
      (∀ j ≤ r, j ≤ #(mids E uv.1 uv.2) →
        ((r : ℝ) + 1 - j) * x uv + ∑ z ∈ mids E uv.1 uv.2 \ top j, f uv z ≥ (r : ℝ) + 1 - j) := by
  constructor
  · intro h j hj hjm
    obtain ⟨hsub, hcard, -⟩ := htop j hj hjm
    simpa [hcard] using h (top j) hsub (by omega)
  · intro h W hW hWr
    obtain ⟨hsub, hcard, ht⟩ := htop #W hWr (Finset.card_le_card hW)
    have := h #W hWr (Finset.card_le_card hW)
    have hle := sum_sdiff_le_of_top (g := f uv) hW hsub hcard ht
    linarith

/-! ### The integrality gap example of Section 3.2 -/

/-- The relaxation of IP (3) (Section 3.2 of [DK11]): capacity and covering constraints with
`0 ≤ x_e ≤ 1` instead of `x_e ∈ {0, 1}`, without the knapsack-cover inequalities. -/
structure IsIP3RelaxFeasible (E : Finset (V × V)) (r : ℕ) (x : V × V → ℝ)
    (f : V × V → V → ℝ) : Prop where
  capacity : ∀ uv ∈ E, ∀ e ∈ E,
    ∑ z ∈ (mids E uv.1 uv.2).filter (fun z => (uv.1, z) = e ∨ (z, uv.2) = e), f uv z ≤ x e
  cover : ∀ uv ∈ E, ((r : ℝ) + 1) * x uv + ∑ z ∈ mids E uv.1 uv.2, f uv z ≥ (r : ℝ) + 1
  x_nonneg : ∀ e ∈ E, 0 ≤ x e
  x_le_one : ∀ e ∈ E, x e ≤ 1
  f_nonneg : ∀ uv ∈ E, ∀ z ∈ mids E uv.1 uv.2, 0 ≤ f uv z

namespace GapExample

variable {r : ℕ}

/-- The vertex `u`. -/
def u : Bool ⊕ Fin r := .inl false
/-- The vertex `v`. -/
def v : Bool ⊕ Fin r := .inl true
/-- The vertex `w_i`. -/
def w (i : Fin r) : Bool ⊕ Fin r := .inr i

variable (r) in
/-- The arcs: `(u, v)` and `(u, w_i)`, `(w_i, v)` for `i ∈ [r]`. -/
def arcs : Finset ((Bool ⊕ Fin r) × (Bool ⊕ Fin r)) :=
  insert (u, v) ((univ.image fun i => (u, w i)) ∪ (univ.image fun i => (w i, v)))

/-- Costs: `M` on `(u, v)`, `1` on all other arcs. -/
def costs (M : ℝ) : (Bool ⊕ Fin r) × (Bool ⊕ Fin r) → ℝ := fun e => if e = (u, v) then M else 1

lemma mem_arcs {e : (Bool ⊕ Fin r) × (Bool ⊕ Fin r)} :
    e ∈ arcs r ↔ e = (u, v) ∨ (∃ i, e = (u, w i)) ∨ (∃ i, e = (w i, v)) := by
  simp [arcs, eq_comm]

lemma loopless : Loopless (arcs r) := by
  intro e he
  rcases mem_arcs.mp he with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> simp [u, v, w]

lemma mids_arcs_uv : mids (arcs r) u v = univ.image w := by
  ext z
  simp only [mem_mids, mem_arcs, Finset.mem_image, Finset.mem_univ, true_and]
  rcases z with b | i
  · simp [u, v, w, Prod.ext_iff]
  · simp [u, v, w, Prod.ext_iff]

lemma card_mids_arcs_uv : #(mids (arcs r) u v) = r := by
  have hw : Function.Injective (w (r := r)) := Sum.inr_injective
  rw [mids_arcs_uv, Finset.card_image_of_injective _ hw]
  simp

lemma uv_mem_arcs : ((u, v) : (Bool ⊕ Fin r) × (Bool ⊕ Fin r)) ∈ arcs r := by simp [arcs]

/-- Integrality gap example, Section 3.2 of [DK11]: every `r`-fault-tolerant 2-spanner contains
the arc `(u, v)` (the set of all `w_i` is a valid fault set). -/
theorem uv_mem_of_isFTSpanner {H : Finset ((Bool ⊕ Fin r) × (Bool ⊕ Fin r))}
    (hH : IsFTSpanner (arcs r) H r 2) : (u, v) ∈ H := by
  rcases (isFTSpanner_two_iff loopless hH.1).mp hH _ uv_mem_arcs with h | h
  · exact h
  · have := Finset.card_le_card (mids_mono hH.1 u v)
    rw [card_mids_arcs_uv] at this
    simp only at h
    omega

/-- Hence `OPT ≥ M` in the integrality gap example. -/
theorem cost_ge_of_isFTSpanner {M : ℝ} (hM : 0 ≤ M) {H : Finset ((Bool ⊕ Fin r) × (Bool ⊕ Fin r))}
    (hH : IsFTSpanner (arcs r) H r 2) : M ≤ cost (costs M) H := by
  have := Finset.single_le_sum (f := costs M)
    (fun e _ => by simp only [costs]; split_ifs <;> linarith) (uv_mem_of_isFTSpanner hH)
  simpa [costs, cost] using this

/-- The fractional solution of the relaxation of IP (3): `x_{(u,v)} = 1/(r+1)`, `x = 1` on the
other arcs, one unit of flow on each path `u → w_i → v`. -/
noncomputable def xFrac : (Bool ⊕ Fin r) × (Bool ⊕ Fin r) → ℝ :=
  fun e => if e = (u, v) then 1 / ((r : ℝ) + 1) else 1

/-- The flow of the fractional solution. -/
def fFrac : (Bool ⊕ Fin r) × (Bool ⊕ Fin r) → Bool ⊕ Fin r → ℝ :=
  fun uv _ => if uv = (u, v) then 1 else 0

/-- Integrality gap example, Section 3.2 of [DK11]: the relaxation of IP (3) has a feasible
solution of value `M / (r + 1) + 2r`. -/
theorem ip3Relax_feasible :
    IsIP3RelaxFeasible (arcs r) r xFrac fFrac ∧
      lpValue (costs M) (arcs r) xFrac = M / ((r : ℝ) + 1) + 2 * r := by
  have hr : (0 : ℝ) < r + 1 := by positivity
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro uv huv e he
    by_cases huv' : uv = (u, v)
    · subst huv'
      by_cases he' : e = (u, v)
      · subst he'
        rw [Finset.sum_eq_zero]
        · simp [xFrac]; positivity
        intro z hz
        simp only [mem_filter, mem_mids, Prod.mk.injEq] at hz
        obtain ⟨⟨h1, h2⟩, h | h⟩ := hz
        · exact absurd (h.2 ▸ h2 : ((v, v) : (Bool ⊕ Fin r) × (Bool ⊕ Fin r)) ∈ arcs r) (by
            intro hh; exact loopless _ hh rfl)
        · exact absurd (h.1 ▸ h1 : ((u, u) : (Bool ⊕ Fin r) × (Bool ⊕ Fin r)) ∈ arcs r) (by
            intro hh; exact loopless _ hh rfl)
      · refine sum_le_of_card_le_one (card_filter_uses_le_one loopless _ _ _) (fun z _ => ?_)
          (by simp [xFrac, he'])
        simp [fFrac, xFrac, he']
    · rw [Finset.sum_eq_zero (fun z _ => by simp [fFrac, huv'])]
      simp only [xFrac]; split_ifs <;> positivity
  · intro uv huv
    by_cases huv' : uv = (u, v)
    · subst huv'
      simp only [xFrac, fFrac, ite_true, Finset.sum_const, card_mids_arcs_uv, nsmul_eq_mul,
        mul_one]
      field_simp
      linarith
    · have : 0 ≤ ∑ z ∈ mids (arcs r) uv.1 uv.2, fFrac uv z :=
        Finset.sum_nonneg fun z _ => by simp only [fFrac, ite_eq_right huv']; norm_num
      simp only [xFrac, huv', ite_false, mul_one]
      linarith
  · intro e _; simp only [xFrac]; split_ifs <;> positivity
  · intro e _
    simp only [xFrac]
    split_ifs
    · rw [div_le_one hr]; linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
    · exact le_refl _
  · intro uv _ z _; simp only [fFrac]; split_ifs <;> norm_num
  · have hnot : ((u, v) : (Bool ⊕ Fin r) × (Bool ⊕ Fin r)) ∉
        (univ.image fun i => (u, w i)) ∪ (univ.image fun i => (w i, v)) := by
      simp [u, v, w]
    have hdisj : Disjoint (univ.image fun i : Fin r => ((u, w i) : (Bool ⊕ Fin r) × (Bool ⊕ Fin r)))
        (univ.image fun i => (w i, v)) := by
      rw [Finset.disjoint_left]
      simp [u, v, w]
    rw [lpValue, arcs, Finset.sum_insert hnot, Finset.sum_union hdisj,
      Finset.sum_image (fun i _ j _ h => by simpa [w] using h),
      Finset.sum_image (fun i _ j _ h => by simpa [w] using h)]
    simp [costs, xFrac, u, v, w]
    ring

/-- Integrality gap example, Section 3.2 of [DK11]: every feasible solution of LP (4) has
`x_{(u,v)} = 1` (by the knapsack-cover constraint for `W = P_{u,v}`), hence value `≥ M`. -/
theorem lp4_x_uv_eq_one {x : (Bool ⊕ Fin r) × (Bool ⊕ Fin r) → ℝ}
    {f : (Bool ⊕ Fin r) × (Bool ⊕ Fin r) → Bool ⊕ Fin r → ℝ} (h : IsLP4Feasible (arcs r) r x f) :
    x (u, v) = 1 := by
  have := h.knapsack (u, v) uv_mem_arcs (mids (arcs r) u v) (subset_refl _)
    (by rw [card_mids_arcs_uv])
  simp only [card_mids_arcs_uv, sdiff_self, Finset.bot_eq_empty, Finset.sum_empty, add_zero] at this
  have := h.x_le_one _ uv_mem_arcs
  linarith

theorem lp4_value_ge {M : ℝ} (hM : 0 ≤ M) {x : (Bool ⊕ Fin r) × (Bool ⊕ Fin r) → ℝ}
    {f : (Bool ⊕ Fin r) × (Bool ⊕ Fin r) → Bool ⊕ Fin r → ℝ} (h : IsLP4Feasible (arcs r) r x f) :
    M ≤ lpValue (costs M) (arcs r) x := by
  have := Finset.single_le_sum (f := fun e => costs M e * x e)
    (fun e he => mul_nonneg (by simp only [costs]; split_ifs <;> linarith) (h.x_nonneg e he))
    uv_mem_arcs
  simpa [costs, lp4_x_uv_eq_one h, lpValue] using this

end GapExample

end DinitzKrauthgamer
