import Podc.Computability.Distributed.CongestedClique.Phases
import Cslib.Foundations.Combinatorics.Matrix.Birkhoff

-- CSLib candidate: Cslib/Computability/Distributed/CongestedClique/Oblivious.lean

/-!
# Oblivious routing on the congested clique

A direct step whose *communication pattern is fixed in advance* — the number `A u v` of words that
`u` sends to `v` does not depend on the states — and in which every node sends and receives at most
`|V| * D` words, can be executed in two direct steps of width at most `D`, i.e. in `2 * D` rounds
(Dolev, Lenzen, Peled, *"Tri, tri again": finding triangles and small subgraphs in a distributed
setting*, DISC 2012, Lemma 1).

Proof: by König's line-colouring theorem in matrix form (`Matrix.exists_split_parts`) the matrix
`A` splits into `|V|` matrices `P m` (one per intermediate node `m`) with row and column sums at
most `D`, `∑ m, P m u v = A u v`. The list from `u` to `v` is cut into `|V|` consecutive segments,
the `m`-th of length `P m u v`. In the first hop `u` sends to `m` the concatenation over `v` of the
`m`-th segments of its lists (length `∑ v, P m u v ≤ D`); in the second hop `m` forwards to `v` the
concatenation over `u` of the segments destined to `v` (length `∑ u, P m u v ≤ D`); `v` cuts the
received lists and reassembles the original lists. All cuts are computable by every node since `P`
depends only on the fixed pattern `A`.

## Main statements

* `Cslib.CongestedClique.Prog.exists_oblivious`: the oblivious routing lemma.
* `Cslib.CongestedClique.Prog.exists_oblivious_step`: the same, followed by a continuation.
-/

namespace Cslib.CongestedClique

open Finset

namespace Oblivious

variable {W : Type}

/-! ### Concatenation and cutting of lists indexed by `Fin k` -/

/-- Concatenation of the lists `f 0, f 1, …, f (k-1)`. -/
def cat {k : ℕ} (f : Fin k → List W) : List W := (List.ofFn f).flatten

/-- The `j`-th piece of `l` when `l` is cut into consecutive pieces of lengths `len 0, len 1, …`. -/
def seg {k : ℕ} (len : Fin k → ℕ) (l : List W) (j : Fin k) : List W :=
  ((List.ofFn len).splitLengths l).getD j []

lemma splitLengths_flatten (L : List (List W)) : (L.map List.length).splitLengths L.flatten = L := by
  induction L with
  | nil => rfl
  | cons a L ih => simp [ih]

lemma mem_of_mem_splitLengths (sz : List ℕ) (l : List W) :
    ∀ x ∈ sz.splitLengths l, ∀ w ∈ x, w ∈ l := by
  induction sz generalizing l with
  | nil => simp
  | cons n sz ih =>
    intro x hx w hw
    simp only [List.splitLengths_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact List.mem_of_mem_take hw
    · exact List.mem_of_mem_drop (ih _ x hx w hw)

lemma seg_cat {k : ℕ} (len : Fin k → ℕ) (f : Fin k → List W) (h : ∀ j, (f j).length = len j) :
    seg len (cat f) = f := by
  funext j
  have hl : List.ofFn len = (List.ofFn f).map List.length := by
    simp [List.map_ofFn, Function.comp_def, h]
  simp only [seg, cat, hl, splitLengths_flatten]
  simp

lemma cat_seg {k : ℕ} (len : Fin k → ℕ) (l : List W) (h : l.length ≤ ∑ j, len j) :
    cat (seg len l) = l := by
  have hL : List.ofFn (seg len l) = (List.ofFn len).splitLengths l := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp [seg, List.getElem?_eq_getElem h2]
  rw [cat, hL, List.flatten_splitLengths]
  simpa [List.sum_ofFn] using h

lemma length_seg {k : ℕ} (len : Fin k → ℕ) (l : List W) (h : ∑ j, len j ≤ l.length) (j : Fin k) :
    (seg len l j).length = len j := by
  have hj : (j : ℕ) < ((List.ofFn len).splitLengths l).length := by simp
  rw [seg, List.getD_eq_getElem _ _ hj, List.splitLengths_length_getElem]
  · simp
  · simpa [List.sum_ofFn] using h

lemma mem_of_mem_seg {k : ℕ} {len : Fin k → ℕ} {l : List W} {j : Fin k} {w : W}
    (hw : w ∈ seg len l j) : w ∈ l := by
  have hj : (j : ℕ) < ((List.ofFn len).splitLengths l).length := by simp
  rw [seg, List.getD_eq_getElem _ _ hj] at hw
  exact mem_of_mem_splitLengths _ _ _ (List.getElem_mem hj) w hw

@[simp] lemma length_cat {k : ℕ} (f : Fin k → List W) : (cat f).length = ∑ j, (f j).length := by
  simp [cat, List.length_flatten, List.sum_ofFn, Function.comp_def]

@[simp] lemma mem_cat {k : ℕ} {f : Fin k → List W} {w : W} : w ∈ cat f ↔ ∃ j, w ∈ f j := by
  simp [cat, List.mem_flatten, List.mem_ofFn]

/-! ### The same, indexed by a finite type -/

variable {ι : Type} [Fintype ι]

/-- Concatenation of the lists `f i` in the order of `Fintype.equivFin ι`. -/
noncomputable def catI (f : ι → List W) : List W := cat fun j => f ((Fintype.equivFin ι).symm j)

/-- The piece of `l` with index `i` when `l` is cut into pieces of lengths `len i`, in the order of
`Fintype.equivFin ι`. -/
noncomputable def segI (len : ι → ℕ) (l : List W) (i : ι) : List W :=
  seg (fun j => len ((Fintype.equivFin ι).symm j)) l (Fintype.equivFin ι i)

lemma segI_catI (len : ι → ℕ) (f : ι → List W) (h : ∀ i, (f i).length = len i) :
    segI len (catI f) = f := by
  funext i
  simp only [segI, catI]
  rw [seg_cat _ _ (fun j => h _)]
  simp

lemma catI_segI (len : ι → ℕ) (l : List W) (h : l.length ≤ ∑ i, len i) :
    catI (segI len l) = l := by
  simp only [catI, segI, Equiv.apply_symm_apply]
  apply cat_seg
  rwa [Equiv.sum_comp (Fintype.equivFin ι).symm len]

lemma length_segI (len : ι → ℕ) (l : List W) (h : ∑ i, len i ≤ l.length) (i : ι) :
    (segI len l i).length = len i := by
  rw [segI, length_seg]
  · simp
  · rwa [Equiv.sum_comp (Fintype.equivFin ι).symm len]

lemma mem_of_mem_segI {len : ι → ℕ} {l : List W} {i : ι} {w : W} (hw : w ∈ segI len l i) :
    w ∈ l :=
  mem_of_mem_seg hw

@[simp] lemma length_catI (f : ι → List W) : (catI f).length = ∑ i, (f i).length := by
  rw [catI, length_cat, Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (f i).length)]

@[simp] lemma mem_catI {f : ι → List W} {w : W} : w ∈ catI f ↔ ∃ i, w ∈ f i := by
  simp only [catI, mem_cat]
  constructor
  · rintro ⟨j, hw⟩; exact ⟨_, hw⟩
  · rintro ⟨i, hw⟩; exact ⟨Fintype.equivFin ι i, by simpa using hw⟩

end Oblivious

namespace Prog

open Oblivious

variable {V W : Type} [Fintype V]

/-- The two-hop program of the oblivious routing lemma, for a split `P` of the pattern
(`P m u v` words from `u` to `v` travel through the intermediate node `m`). -/
noncomputable def twoHop {σ τ : Type} (P : V → V → V → ℕ) (send : V → σ → V → List W)
    (recv : V → σ → (V → List W) → τ) : Prog V W σ τ :=
  step .direct
    (fun u x m => catI fun v => segI (fun m' => P m' u v) (send u x v) m)
    (fun _ x r => (x, r))
  (step .direct
    (fun m (y : σ × (V → List W)) v => catI fun u => segI (fun v' => P m u v') (y.2 u) v)
    (fun v y r => recv v y.1 fun u => catI fun m => segI (fun u' => P m u' v) (r m) u)
  (done τ))

/-- **Oblivious routing** (Dolev, Lenzen, Peled, DISC 2012, Lemma 1): a direct step whose pattern
`A` (the lengths of the lists) is fixed in advance and has row and column sums at most `|V| * D`
can be executed in `2 * D` rounds; the words sent are among the words of the original step. -/
theorem exists_oblivious {σ τ : Type} (A : V → V → ℕ) (D : ℕ)
    (hr : ∀ u, ∑ v, A u v ≤ Fintype.card V * D) (hc : ∀ v, ∑ u, A u v ≤ Fintype.card V * D)
    (send : V → σ → V → List W) (hlen : ∀ u x v, (send u x v).length = A u v)
    (recv : V → σ → (V → List W) → τ) :
    ∃ Q : Prog V W σ τ, ∀ s, Q.run s = next send recv s ∧ Q.rounds s ≤ 2 * D ∧
      ∀ ok : W → Prop, (∀ u v, ∀ w ∈ send u (s u) v, ok w) → Q.Valid ok s := by
  obtain ⟨P, hPA, hPr, hPc⟩ := Matrix.exists_split_parts (ι := V) A D hr hc
  refine ⟨twoHop P send recv, fun s => ?_⟩
  -- lengths of the segments
  have hseg : ∀ u x v m, (segI (fun m' => P m' u v) (send u x v) m).length = P m u v :=
    fun u x v m => length_segI _ _ (by rw [hlen, hPA]) m
  -- the lists forwarded by the intermediate nodes
  have hfwd : ∀ m v, (catI fun u => segI (fun v' => P m u v')
      (catI fun v' => segI (fun m' => P m' u v') (send u (s u) v') m) v) =
      catI fun u => segI (fun m' => P m' u v) (send u (s u) v) m := by
    intro m v
    congr 1; funext u
    rw [segI_catI _ _ (fun v' => hseg u (s u) v' m)]
  refine ⟨?_, ?_, ?_⟩
  · funext v
    simp only [twoHop, run_step, run_done, next, hfwd]
    congr 1; funext u
    have h1 : ∀ m, segI (fun u' => P m u' v)
        (catI fun u => segI (fun m' => P m' u v) (send u (s u) v) m) u =
        segI (fun m' => P m' u v) (send u (s u) v) m := fun m => by
      rw [segI_catI _ _ (fun u' => hseg u' (s u') v m)]
    simp only [h1]
    exact catI_segI _ _ (by rw [hlen, hPA])
  · simp only [twoHop, rounds_step_direct, rounds_done]
    have h1 : width (fun u x m => catI fun v => segI (fun m' => P m' u v) (send u x v) m) s ≤ D := by
      rw [width_le_iff]
      intro u m
      simp only [length_catI, hseg]
      exact hPr m u
    have h2 : width (fun m (y : σ × (V → List W)) v =>
        catI fun u => segI (fun v' => P m u v') (y.2 u) v)
        (next (fun u x m => catI fun v => segI (fun m' => P m' u v) (send u x v) m)
          (fun _ x r => (x, r)) s) ≤ D := by
      rw [width_le_iff]
      intro m v
      simp only [next, hfwd, length_catI, hseg]
      exact hPc m v
    omega
  · intro ok hok
    simp only [twoHop, Valid, next, hfwd]
    refine ⟨?_, by simp, ?_, by simp, trivial⟩
    · intro u m w hw
      obtain ⟨v, hv⟩ := mem_catI.mp hw
      exact hok u v w (mem_of_mem_segI hv)
    · intro m v w hw
      obtain ⟨u, hu⟩ := mem_catI.mp hw
      exact hok u v w (mem_of_mem_segI hu)

/-- Oblivious routing followed by a continuation `rest`: the step `step .direct send recv rest`
with a fixed pattern of row and column sums at most `|V| * D` can be replaced by a program with
the same result taking at most `2 * D` rounds plus the rounds of `rest`. -/
theorem exists_oblivious_step {σ τ ρ : Type} (A : V → V → ℕ) (D : ℕ)
    (hr : ∀ u, ∑ v, A u v ≤ Fintype.card V * D) (hc : ∀ v, ∑ u, A u v ≤ Fintype.card V * D)
    (send : V → σ → V → List W) (hlen : ∀ u x v, (send u x v).length = A u v)
    (recv : V → σ → (V → List W) → τ) (rest : Prog V W τ ρ) :
    ∃ Q : Prog V W σ ρ, ∀ s, Q.run s = rest.run (next send recv s) ∧
      Q.rounds s ≤ 2 * D + rest.rounds (next send recv s) ∧
      ∀ ok : W → Prop, (∀ u v, ∀ w ∈ send u (s u) v, ok w) →
        rest.Valid ok (next send recv s) → Q.Valid ok s := by
  obtain ⟨Q, hQ⟩ := exists_oblivious A D hr hc send hlen recv
  refine ⟨Q.append rest, fun s => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hQ s
  refine ⟨by rw [run_append, h1], by rw [rounds_append, h1]; omega, fun ok hok hrest => ?_⟩
  rw [valid_append, h1]
  exact ⟨h3 ok hok, hrest⟩

end Prog

end Cslib.CongestedClique
