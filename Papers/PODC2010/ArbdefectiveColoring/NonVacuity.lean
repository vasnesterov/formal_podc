import Papers.PODC2010.ArbdefectiveColoring.Parameters

/-!
# Non-vacuity of the black box of Lemma 2.1

The theorems of Sections 3–4 assume Lemma 2.1 (Kuhn's `O(log* n)`-round defective colouring) as a
hypothesis `Lemma21 V C R`. We show that this hypothesis is satisfiable, with `C = 1` and
`R = n` rounds (every vertex learns its whole component and computes a canonical defective
colouring of it), using the classical existence result:

* `exists_defective` (Lovász 1966): every graph of maximum degree `≤ Δ` has a `⌊Δ/q⌋`-defective
  `q`-colouring (a `q`-colouring minimizing the number of monochromatic edges).
* `Lemma21.satisfiable`: `Lemma21 V 1 n`.
-/

open Finset Cslib.Local

namespace Podc.ArbdefectiveColoring

open scoped Classical

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V]

-- CSLib candidate: Lovász's defective colouring lemma (`SimpleGraph/DefectiveColoring.lean`)
section Lovasz

variable (G : SimpleGraph V) {β : Type*}

/-- Indicator of a monochromatic ordered edge. -/
noncomputable def mono (c : V → β) (w u : V) : ℕ := if G.Adj w u ∧ c u = c w then 1 else 0

/-- The number of neighbours of `v` of colour `j`. -/
noncomputable def nbrCnt (c : V → β) (v : V) (j : β) : ℕ := #{u | G.Adj v u ∧ c u = j}

lemma sum_nbrCnt_le [Fintype β] (c : V → β) (v : V) : ∑ j, nbrCnt G c v j ≤ deg G v := by
  simp only [nbrCnt]
  rw [← card_biUnion]
  · refine card_le_card fun u hu => ?_
    simp only [mem_biUnion, mem_filter, mem_univ, true_and] at hu ⊢
    obtain ⟨_, h, _⟩ := hu; exact h
  · intro i _ j _ hij
    exact disjoint_filter.2 fun u _ hi hj => hij (hi.2.symm.trans hj.2)

/-- Twice the number of monochromatic edges. -/
noncomputable def monoCount (c : V → β) : ℕ := ∑ w, ∑ u, mono G c w u

/-- Splitting off the vertex `v`: `Φ(c) = 2 · #{monochromatic edges at v} + (rest)`. -/
lemma monoCount_eq (c : V → β) (v : V) :
    monoCount G c = 2 * #{u | G.Adj v u ∧ c u = c v} +
      ∑ w ∈ univ.erase v, ∑ u ∈ univ.erase v, mono G c w u := by
  have hs : ∑ u, mono G c v u = #{u | G.Adj v u ∧ c u = c v} := by
    rw [card_filter]; rfl
  have hs' : ∑ w, mono G c w v = #{u | G.Adj v u ∧ c u = c v} := by
    rw [card_filter]
    refine sum_congr rfl fun w _ => ?_
    simp only [mono]
    congr 1
    exact propext ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  have hvv : mono G c v v = 0 := by simp [mono]
  have h1 : monoCount G c = ∑ w, mono G c w v + ∑ w, ∑ u ∈ univ.erase v, mono G c w u := by
    rw [monoCount, ← sum_add_distrib]
    exact sum_congr rfl fun w _ => (add_sum_erase _ _ (mem_univ v)).symm
  have h2 : ∑ w, ∑ u ∈ univ.erase v, mono G c w u =
      ∑ u ∈ univ.erase v, mono G c v u + ∑ w ∈ univ.erase v, ∑ u ∈ univ.erase v, mono G c w u :=
    (add_sum_erase _ _ (mem_univ v)).symm
  have h3 : ∑ u ∈ univ.erase v, mono G c v u = ∑ u, mono G c v u := by
    rw [← add_sum_erase _ _ (mem_univ v), hvv, zero_add]
  rw [h1, h2, h3, hs, hs']
  ring

/-- Recolouring `v` with `j` changes `Φ` by `2 (#{neighbours of colour j} - #{neighbours of the
old colour})`. -/
lemma monoCount_update (c : V → β) (v : V) (j : β) :
    monoCount G (Function.update c v j) + 2 * nbrCnt G c v (c v) =
      monoCount G c + 2 * nbrCnt G c v j := by
  rw [monoCount_eq G (Function.update c v j) v, monoCount_eq G c v]
  have hrest : ∑ w ∈ univ.erase v, ∑ u ∈ univ.erase v, mono G (Function.update c v j) w u =
      ∑ w ∈ univ.erase v, ∑ u ∈ univ.erase v, mono G c w u :=
    sum_congr rfl fun w hw => sum_congr rfl fun u hu => by
      simp [mono, Function.update_of_ne (ne_of_mem_erase hw),
        Function.update_of_ne (ne_of_mem_erase hu)]
  have hnew : #{u | G.Adj v u ∧ Function.update c v j u = Function.update c v j v} =
      #{u | G.Adj v u ∧ c u = j} := by
    congr 1
    refine filter_congr fun u _ => ?_
    simp only [Function.update_self]
    constructor
    · rintro ⟨h, h'⟩; exact ⟨h, by rwa [Function.update_of_ne h.ne'] at h'⟩
    · rintro ⟨h, h'⟩; exact ⟨h, by rwa [Function.update_of_ne h.ne']⟩
  rw [hrest, hnew, nbrCnt, nbrCnt]
  ring

/-- **Lovász's lemma** (defective colourings exist): every graph of maximum degree `≤ Δ` has a
`⌊Δ/q⌋`-defective colouring with `q > 0` colours. -/
theorem exists_defective {Δ q : ℕ} (hq : 0 < q) (hG : MaxDegLE G Δ) :
    ∃ c : V → Fin q, IsDefective G c (Δ / q) := by
  obtain ⟨c, -, hmin⟩ := (univ : Finset (V → Fin q)).exists_min_image (monoCount G)
    ⟨fun _ => ⟨0, hq⟩, mem_univ _⟩
  refine ⟨c, fun v => ?_⟩
  by_contra hlt
  push Not at hlt
  -- a colour used by at most `⌊Δ/q⌋` neighbours
  have hsum : ∑ j : Fin q, nbrCnt G c v j ≤ Δ := (sum_nbrCnt_le G c v).trans (hG v)
  obtain ⟨j, -, hj⟩ := (univ : Finset (Fin q)).exists_min_image (nbrCnt G c v)
    ⟨⟨0, hq⟩, mem_univ _⟩
  have hjle : nbrCnt G c v j ≤ Δ / q := by
    rw [Nat.le_div_iff_mul_le hq]
    calc nbrCnt G c v j * q = ∑ _i : Fin q, nbrCnt G c v j := by simp [mul_comm]
      _ ≤ ∑ i : Fin q, nbrCnt G c v i := sum_le_sum fun i _ => hj i (mem_univ i)
      _ ≤ Δ := hsum
  have hupd := monoCount_update G c v j
  have := hmin (Function.update c v j) (mem_univ _)
  have hlt' : Δ / q < nbrCnt G c v (c v) := hlt
  omega

end Lovasz

/-! ### A (slow) algorithm satisfying the black box of Lemma 2.1 -/

/-- A canonical `⌊Δ/q⌋`-defective `q`-colouring of `G` (if `G` has maximum degree `≤ Δ`). -/
noncomputable def lovaszCol (Δ q : ℕ) (G : SimpleGraph V) : V → ℕ :=
  if h : ∃ c : V → Fin q, IsDefective G c (Δ / q) then fun v => (Classical.choose h v : ℕ)
  else fun _ => 0

/-- The `n`-round algorithm: every vertex gathers its component (`loc G v n`) and outputs its
colour in the canonical defective colouring of it. -/
noncomputable def lovaszAlg (Δ q : ℕ) (G : SimpleGraph V) (v : V) : ℕ :=
  lovaszCol Δ q (loc G v (Fintype.card V)) v

lemma edist_lt_card_iff {G : SimpleGraph V} {u x : V} :
    G.edist u x < Fintype.card V ↔ G.Reachable u x := by
  constructor
  · intro h
    exact SimpleGraph.edist_ne_top_iff_reachable.1 (ne_top_of_lt h)
  · intro h
    obtain ⟨p, hp⟩ := h.exists_isPath
    exact (SimpleGraph.edist_le p).trans_lt (by exact_mod_cast hp.length_lt)

/-- Within a component, all vertices see the same localized graph. -/
lemma loc_card_eq {G : SimpleGraph V} {u v : V} (h : G.Reachable v u) :
    loc G u (Fintype.card V) = loc G v (Fintype.card V) := by
  ext x y
  simp only [loc, edist_lt_card_iff]
  constructor
  · rintro ⟨hxy, hx | hy⟩
    · exact ⟨hxy, Or.inl (h.trans hx)⟩
    · exact ⟨hxy, Or.inr (h.trans hy)⟩
  · rintro ⟨hxy, hx | hy⟩
    · exact ⟨hxy, Or.inl (h.symm.trans hx)⟩
    · exact ⟨hxy, Or.inr (h.symm.trans hy)⟩

/-- The `n`-round algorithm computes a `⌊Δ/q⌋`-defective `q`-colouring of every graph of maximum
degree `≤ Δ`. -/
noncomputable def lovaszDefectiveAlg (Δ q : ℕ) (hq : 0 < q) :
    DefectiveAlg V Δ (Δ / q) q (Fintype.card V) := by
  refine { col := lovaszAlg Δ q, isLocal := ?_, defective := ?_, lt := ?_ }
  · intro G _ G' _ v hv
    simp only [lovaszAlg, loc_eq_of_gAgree hv.1]
  · intro G hG v
    set H := loc G v (Fintype.card V)
    have hH : MaxDegLE H Δ := fun w =>
      (card_le_card fun u hu => by
        simp only [mem_filter, mem_univ, true_and] at hu ⊢; exact (loc_le G v _) hu).trans (hG w)
    have hex : ∃ c : V → Fin q, IsDefective H c (Δ / q) := exists_defective H hq hH
    have hcol : ∀ u, G.Reachable v u → lovaszAlg Δ q G u = lovaszCol Δ q H u := fun u hu => by
      simp only [lovaszAlg, loc_card_eq hu, H]
    have hvadj : ∀ u, G.Adj v u ↔ H.Adj v u := fun u => by
      have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨v⟩
      simp only [H, loc, SimpleGraph.edist_self]
      exact ⟨fun h => ⟨h, Or.inl (by exact_mod_cast this)⟩, fun h => h.1⟩
    refine le_trans (le_of_eq ?_) (Classical.choose_spec hex v)
    have hdef : ∀ u, lovaszCol Δ q H u = (Classical.choose hex u : ℕ) := fun u => by
      simp [lovaszCol, hex]
    congr 1
    ext u
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hcol u h1.reachable, hcol v (SimpleGraph.Reachable.refl v), hdef, hdef] at h2
      exact ⟨(hvadj u).1 h1, Fin.ext h2⟩
    · rintro ⟨h1, h2⟩
      have h1' := (hvadj u).2 h1
      refine ⟨h1', ?_⟩
      rw [hcol u h1'.reachable, hcol v (SimpleGraph.Reachable.refl v), hdef, hdef, h2]
  · intro G _ v
    simp only [lovaszAlg, lovaszCol]
    split_ifs with h
    · exact (Classical.choose h v).isLt
    · exact hq

/-- **Lemma 2.1 is satisfiable** (with `C = 1` and `n` rounds). -/
theorem Lemma21.satisfiable : Lemma21 V 1 (Fintype.card V) := by
  intro Δ q hq
  have D := lovaszDefectiveAlg (V := V) Δ q hq
  exact ⟨{ D with lt := fun G hG v => (D.lt G hG v).trans_le (by nlinarith) }⟩

end Podc.ArbdefectiveColoring
