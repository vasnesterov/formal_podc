import Papers.PODC2024.DataCenterRouting.Model
import Cslib.Foundations.Combinatorics.Matrix.Birkhoff

/-!
# Link-disjoint routing of a matching (Lemma 5.2, footnote 5)

A matching `S` of the macro-switch graph `G^MS` (flows with pairwise distinct sources and pairwise
distinct destinations) can be routed link-disjointly in the Clos network `C_n`: consider the
`2n × 2n` matrix `A i o = #{f ∈ S : I(s_f) = I_i, O(t_f) = O_o}`. Its row and column sums are at
most `n` (each input/output switch has `n` servers), so by König's line-colouring theorem
(`Matrix.exists_split_parts` with `D = 1`) it splits into `n` matrices `P m` with row and column
sums at most `1`. Sending exactly `P m i o` of the flows of `S` from `I_i` to `O_o` through the
middle switch `M_m` uses every link `I_i M_m` and `M_m O_o` at most once.

## Main statements

* `Podc.DataCenterRouting.exists_map_card_filter_eq`: a finite set of size `∑ i, c i` admits a map
  to `ι` whose fibers have sizes `c i`;
* `Podc.DataCenterRouting.exists_routing_feasible_of_isMatching`: the `0/1` allocation of a
  matching is feasible in `C_n` for a suitable routing.
-/

namespace Podc.DataCenterRouting

open Cslib.RateAllocation Finset

-- CSLib candidate
/-- Distributing a finite set according to prescribed fiber sizes: a finite set `s` of size
`∑ i, c i` admits a map `g : α → ι` such that exactly `c i` elements of `s` are sent to `i`. -/
theorem exists_map_card_filter_eq {α ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (s : Finset α) (c : ι → ℕ) (h : s.card = ∑ i, c i) :
    ∃ g : α → ι, ∀ i, (s.filter fun a => g a = i).card = c i := by
  classical
  have hcard : Fintype.card s = Fintype.card (Σ i, Fin (c i)) := by
    simp [h]
  let e : s ≃ Σ i, Fin (c i) := Fintype.equivOfCardEq hcard
  refine ⟨fun a => if ha : a ∈ s then (e ⟨a, ha⟩).1 else Classical.arbitrary ι, fun i => ?_⟩
  have h1 : (s.filter fun a => (if ha : a ∈ s then (e ⟨a, ha⟩).1 else Classical.arbitrary ι) = i)
      = (univ.filter fun x : s => (e x).1 = i).map (Function.Embedding.subtype _) := by
    ext a
    simp only [mem_filter, mem_map, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨ha, hi⟩
      exact ⟨⟨a, ha⟩, by simpa [ha] using hi, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, by simpa [x.2] using hx⟩
  rw [h1, card_map]
  have h2 : (univ.filter fun x : s => (e x).1 = i).card =
      (univ.filter fun y : Σ i, Fin (c i) => y.1 = i).card :=
    card_bij' (fun x _ => e x) (fun y _ => e.symm y) (by simp) (by simp) (by simp) (by simp)
  rw [h2]
  have h3 : (univ.filter fun y : Σ i, Fin (c i) => y.1 = i) =
      (univ : Finset (Fin (c i))).map (Function.Embedding.sigmaMk i) := by
    ext ⟨j, k⟩
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.sigmaMk_apply]
    constructor
    · rintro rfl; exact ⟨k, rfl⟩
    · rintro ⟨k', hk'⟩; exact (Sigma.mk.inj_iff.1 hk').1.symm
  rw [h3, card_map, card_univ, Fintype.card_fin]

variable {n : ℕ} {F : Type*}

/-- The load of a link under the `0/1` allocation of `S` is the number of flows of `S` crossing
it. -/
theorem load_indicatorAlloc {L : Type*} [DecidableEq L] [Fintype F] (N : Network F L)
    (S : Finset F) (ℓ : L) :
    N.load (indicatorAlloc S) ℓ = ((S.filter fun f => ℓ ∈ N.path f).card : ℝ) := by
  classical
  unfold Network.load indicatorAlloc
  rw [Finset.sum_boole]
  congr 2
  ext f
  simp [and_comm]

/-- **Footnote 5 / Lemma 5.2** of [Ferreira–Atre–Sherry–Sobrinho, PODC 2024]: a matching of
`G^MS` can be routed link-disjointly in `C_n` (König's line-colouring theorem), so its `0/1`
allocation is feasible in the Clos network. -/
theorem exists_routing_feasible_of_isMatching [Fintype F] (fl : Flows n F) {S : Finset F}
    (hS : IsMatching fl S) :
    ∃ r : F → Fin n, (clos fl r).Feasible (indicatorAlloc S) := by
  classical
  have hnn : ∀ f, 0 ≤ indicatorAlloc S f := fun f => by
    unfold indicatorAlloc; split_ifs <;> norm_num
  rcases isEmpty_or_nonempty F with hF | ⟨⟨f₀⟩⟩
  · refine ⟨fun f => isEmptyElim f, hnn, fun ℓ => ?_⟩
    rw [load_indicatorAlloc, Subsingleton.elim S ∅]
    simp
  have : Nonempty (Fin n) := ⟨(fl.src f₀).2⟩
  -- the flows of `S` from `I_i` to `O_o`
  let s : Fin (2 * n) → Fin (2 * n) → Finset F := fun i o =>
    S.filter fun f => (fl.src f).1 = i ∧ (fl.dst f).1 = o
  let A : Matrix (Fin (2 * n)) (Fin (2 * n)) ℕ := fun i o => (s i o).card
  have hrow : ∀ i, ∑ o, A i o ≤ Fintype.card (Fin n) * 1 := by
    intro i
    have hsum : ∑ o, A i o = (S.filter fun f => (fl.src f).1 = i).card := by
      rw [card_eq_sum_card_fiberwise (f := fun f => (fl.dst f).1) (t := univ)
        (fun _ _ => mem_univ _)]
      refine sum_congr rfl fun o _ => ?_
      simp only [A, s, filter_filter]
    rw [hsum, Fintype.card_fin, mul_one]
    calc (S.filter fun f => (fl.src f).1 = i).card ≤ (univ : Finset (Fin n)).card :=
          card_le_card_of_injOn (fun f => (fl.src f).2) (fun _ _ => mem_univ _)
            (fun f hf g hg hfg => by
              simp only [coe_filter, Set.mem_ofPred_eq] at hf hg
              exact hS.1 hf.1 hg.1 (Prod.ext (hf.2.trans hg.2.symm) hfg))
      _ = n := by simp
  have hcol : ∀ o, ∑ i, A i o ≤ Fintype.card (Fin n) * 1 := by
    intro o
    have hsum : ∑ i, A i o = (S.filter fun f => (fl.dst f).1 = o).card := by
      rw [card_eq_sum_card_fiberwise (f := fun f => (fl.src f).1) (t := univ)
        (fun _ _ => mem_univ _)]
      refine sum_congr rfl fun i _ => ?_
      simp only [A, s, filter_filter]
      congr 1
      ext f
      simp only [mem_filter]
      tauto
    rw [hsum, Fintype.card_fin, mul_one]
    calc (S.filter fun f => (fl.dst f).1 = o).card ≤ (univ : Finset (Fin n)).card :=
          card_le_card_of_injOn (fun f => (fl.dst f).2) (fun _ _ => mem_univ _)
            (fun f hf g hg hfg => by
              simp only [coe_filter, Set.mem_ofPred_eq] at hf hg
              exact hS.2 hf.1 hg.1 (Prod.ext (hf.2.trans hg.2.symm) hfg))
      _ = n := by simp
  obtain ⟨P, hP, hPr, hPc⟩ := Matrix.exists_split_parts (ι := Fin n) A 1 hrow hcol
  have hsplit : ∀ i o, ∃ g : F → Fin n, ∀ m, ((s i o).filter fun f => g f = m).card = P m i o :=
    fun i o => exists_map_card_filter_eq (s i o) (fun m => P m i o) (hP i o).symm
  choose g hg using hsplit
  let r : F → Fin n := fun f => g (fl.src f).1 (fl.dst f).1 f
  refine ⟨r, hnn, fun ℓ => ?_⟩
  rw [load_indicatorAlloc, clos_cap, Nat.cast_le_one]
  cases ℓ with
  | srcLink t =>
    refine card_le_one.2 fun f hf g' hg' => ?_
    simp only [mem_filter, mem_clos_path, Link.srcLink.injEq, reduceCtorEq, or_false] at hf hg'
    exact hS.1 hf.1 hg'.1 (hf.2.symm.trans hg'.2)
  | dstLink t =>
    refine card_le_one.2 fun f hf g' hg' => ?_
    simp only [mem_filter, mem_clos_path, Link.dstLink.injEq, reduceCtorEq, false_or] at hf hg'
    exact hS.2 hf.1 hg'.1 (hf.2.symm.trans hg'.2)
  | up i m =>
    rw [card_eq_sum_card_fiberwise (f := fun f => (fl.dst f).1) (t := univ)
      (fun _ _ => mem_univ _)]
    refine le_trans (le_of_eq ?_) (hPr m i)
    refine sum_congr rfl fun o _ => ?_
    rw [← hg i o m]
    congr 1
    ext f
    simp only [mem_filter, mem_clos_path, Link.up.injEq, reduceCtorEq, false_or, or_false, s, r]
    constructor
    · rintro ⟨⟨hf, rfl, hm⟩, rfl⟩
      exact ⟨⟨hf, rfl, rfl⟩, hm.symm⟩
    · rintro ⟨⟨hf, rfl, rfl⟩, hm⟩
      exact ⟨⟨hf, rfl, hm.symm⟩, rfl⟩
  | down m o =>
    rw [card_eq_sum_card_fiberwise (f := fun f => (fl.src f).1) (t := univ)
      (fun _ _ => mem_univ _)]
    refine le_trans (le_of_eq ?_) (hPc m o)
    refine sum_congr rfl fun i _ => ?_
    rw [← hg i o m]
    congr 1
    ext f
    simp only [mem_filter, mem_clos_path, Link.down.injEq, reduceCtorEq, false_or, or_false, s, r]
    constructor
    · rintro ⟨⟨hf, hm, rfl⟩, rfl⟩
      exact ⟨⟨hf, rfl, rfl⟩, hm.symm⟩
    · rintro ⟨⟨hf, rfl, rfl⟩, hm⟩
      exact ⟨⟨hf, hm.symm, rfl⟩, rfl⟩

end Podc.DataCenterRouting
