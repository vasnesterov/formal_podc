import Papers.PODC2014.RandomizationTwoHop.Norris
import Cslib.Computability.Distributed.PortNumbering.Basic

-- CSLib candidate (paper-local for now; see README)

/-!
# Port numberings induced by a 2-hop colouring

In a graph whose colouring `c` (values in a linear order) is injective on every neighbourhood, a
node can number its ports by sorting its neighbours by colour: port `i` of `v` leads to the
neighbour of `v` with the `i`-th smallest colour. This is how the paper's algorithms (which work
with local views without port numbers) simulate a port-numbering algorithm `A_R`: the simulated
graphs carry this numbering (`colorPN`). It is a simple port numbering of `G`
(`colorPN_isSimple`, `colorPN_toSimpleGraph`).

The port of `v` towards `u` is `rankC v (c u)`, the number of neighbours of `v` with smaller
colour; it depends only on the colours around `v`, so a bijection between two neighbourhoods
that preserves colours preserves degrees, ports and remote ports (`rankC_eq_of_equiv`,
`pick_eq_of_equiv`). This is the basis of the locality lemma for runs (`Model.lean`).
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph Cslib.PortNumbering

variable {V C : Type} [LinearOrder C] (G : SimpleGraph V) (c : V → C)

/-- The number of neighbours of `v` with colour `< a`. -/
noncomputable def rankC (v : V) (a : C) : ℕ := Set.ncard {w | G.Adj v w ∧ c w < a}

/-- The degree of `v`. -/
noncomputable def cdeg (v : V) : ℕ := Set.ncard (G.neighborSet v)

/-- Colours are injective on every neighbourhood. -/
def NbhdInj : Prop := ∀ v, Set.InjOn c (G.neighborSet v)

/-- The neighbour of `v` behind port `i` (if any). -/
noncomputable def pick (v : V) (i : ℕ) : V :=
  open Classical in
  if h : ∃ u, G.Adj v u ∧ rankC G c v (c u) = i then h.choose else v

variable {G c} [Finite V]

theorem rankC_lt_cdeg {v u : V} (hu : G.Adj v u) : rankC G c v (c u) < cdeg G v := by
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine ⟨fun w hw => hw.1, fun h => ?_⟩
  have := (h hu).2; exact lt_irrefl _ this

theorem rankC_strictMono {v u u' : V} (hu : G.Adj v u) (h : c u < c u') :
    rankC G c v (c u) < rankC G c v (c u') := by
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine ⟨fun w hw => ⟨hw.1, hw.2.trans h⟩, fun hs => ?_⟩
  have := (hs ⟨hu, h⟩).2; exact lt_irrefl _ this

theorem rankC_injOn (hc : NbhdInj G c) (v : V) :
    Set.InjOn (fun u => rankC G c v (c u)) (G.neighborSet v) := by
  intro u hu u' hu' he
  by_contra hne
  have hc' : c u ≠ c u' := fun e => hne (hc v hu hu' e)
  rcases lt_or_gt_of_ne hc' with h | h
  · exact absurd he (rankC_strictMono hu h).ne
  · exact absurd he (rankC_strictMono hu' h).ne'

theorem exists_rankC_eq (hc : NbhdInj G c) {v : V} {i : ℕ} (hi : i < cdeg G v) :
    ∃ u, G.Adj v u ∧ rankC G c v (c u) = i := by
  have himg : (fun u => rankC G c v (c u)) '' G.neighborSet v = Set.Iio (cdeg G v) := by
    apply Set.eq_of_subset_of_ncard_le
    · rintro _ ⟨u, hu, rfl⟩; exact rankC_lt_cdeg hu
    · rw [(rankC_injOn hc v).ncard_image, Set.ncard_Iio, Nat.card_Iio]; rfl
    · exact Set.finite_Iio _
  have : i ∈ Set.Iio (cdeg G v) := hi
  rw [← himg] at this
  obtain ⟨u, hu, rfl⟩ := this
  exact ⟨u, hu, rfl⟩

theorem pick_spec (hc : NbhdInj G c) {v : V} {i : ℕ} (hi : i < cdeg G v) :
    G.Adj v (pick G c v i) ∧ rankC G c v (c (pick G c v i)) = i := by
  have h := exists_rankC_eq hc hi
  unfold pick; simp only [h, ↓reduceDIte]; exact h.choose_spec

theorem pick_rankC (hc : NbhdInj G c) {v u : V} (hu : G.Adj v u) :
    pick G c v (rankC G c v (c u)) = u := by
  have hs := pick_spec hc (rankC_lt_cdeg (c := c) hu)
  exact rankC_injOn hc v hs.1 hu hs.2

/-- The colour-sorted port numbering of `G` (requires `NbhdInj G c`). -/
noncomputable def colorPN' (hc : NbhdInj G c) : PNGraph V where
  deg := cdeg G
  p v i := (pick G c v i, rankC G c (pick G c v i) (c v))
  p_lt v i hi := rankC_lt_cdeg (pick_spec hc hi).1.symm
  p_p v i hi := by
    have hs := pick_spec hc hi
    simp only [pick_rankC hc hs.1.symm, hs.2]

variable (G c) in
/-- The colour-sorted port numbering of `G`; if colours repeat in some neighbourhood we return
the (irrelevant) port numbering without ports. -/
noncomputable def colorPN : PNGraph V :=
  open Classical in
  if hc : NbhdInj G c then colorPN' hc
  else ⟨fun _ => 0, fun v _ => (v, 0), fun _ _ h => absurd h (Nat.not_lt_zero _),
    fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

theorem colorPN_deg (hc : NbhdInj G c) (v : V) : (colorPN G c).deg v = cdeg G v := by
  unfold colorPN; simp only [hc, ↓reduceDIte]; rfl

theorem colorPN_nbr (hc : NbhdInj G c) (v : V) (i : ℕ) :
    (colorPN G c).nbr v i = pick G c v i := by
  unfold colorPN; simp only [hc, ↓reduceDIte]; rfl

theorem colorPN_rport (hc : NbhdInj G c) (v : V) (i : ℕ) :
    (colorPN G c).rport v i = rankC G c (pick G c v i) (c v) := by
  unfold colorPN; simp only [hc, ↓reduceDIte]; rfl

theorem colorPN_isSimple (hc : NbhdInj G c) : (colorPN G c).IsSimple := by
  refine ⟨fun v i hi => ?_, fun v i j hi hj he => ?_⟩
  · rw [colorPN_deg hc] at hi; rw [colorPN_nbr hc]; exact (pick_spec hc hi).1.ne.symm
  · rw [colorPN_deg hc] at hi hj; rw [colorPN_nbr hc, colorPN_nbr hc] at he
    rw [← (pick_spec hc hi).2, ← (pick_spec hc hj).2, he]

theorem colorPN_toSimpleGraph (hc : NbhdInj G c) : (colorPN G c).toSimpleGraph = G := by
  ext u v
  rw [PNGraph.toSimpleGraph_adj]
  constructor
  · rintro ⟨-, i, hi, rfl⟩
    rw [colorPN_deg hc] at hi; rw [colorPN_nbr hc]; exact (pick_spec hc hi).1
  · intro h
    refine ⟨h.ne, rankC G c u (c v), ?_, ?_⟩
    · rw [colorPN_deg hc]; exact rankC_lt_cdeg h
    · rw [colorPN_nbr hc, pick_rankC hc h]

/-! ### Colour-preserving bijections of neighbourhoods -/

variable {W : Type} {H : SimpleGraph W} {d : W → C}

omit [Finite V] in

theorem rankC_eq_of_equiv {u : V} {v : W} (e : G.neighborSet u ≃ H.neighborSet v)
    (he : ∀ x : G.neighborSet u, d (e x) = c x) (a : C) : rankC H d v a = rankC G c u a := by
  unfold rankC
  have : {w | H.Adj v w ∧ d w < a} = (fun x => (e x).1) '' {x : G.neighborSet u | c x < a} ∪ ∅ := by
    ext w; simp only [Set.mem_ofPred_eq, Set.union_empty, Set.mem_image]
    constructor
    · rintro ⟨hw, hwa⟩
      refine ⟨e.symm ⟨w, hw⟩, ?_, by simp⟩
      rw [← he]; simpa using hwa
    · rintro ⟨x, hx, rfl⟩; exact ⟨(e x).2, by rw [he]; exact hx⟩
  rw [this, Set.union_empty, Set.ncard_image_of_injective _
    (fun x y h => e.injective (Subtype.ext h))]
  rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
  congr 1; ext w; simp [and_comm]

omit [Finite V] in
theorem cdeg_eq_of_equiv {u : V} {v : W} (e : G.neighborSet u ≃ H.neighborSet v) :
    cdeg H v = cdeg G u := by
  unfold cdeg; rw [Set.ncard_congr' e.symm]

theorem pick_eq_of_equiv [Finite W] (hc : NbhdInj G c) (hd : NbhdInj H d) {u : V} {v : W}
    (e : G.neighborSet u ≃ H.neighborSet v) (he : ∀ x : G.neighborSet u, d (e x) = c x) {i : ℕ}
    (hi : i < cdeg G u) :
    pick H d v i = (e ⟨pick G c u i, (pick_spec hc hi).1⟩).1 := by
  have hs := pick_spec hc hi
  have h1 := (e ⟨_, hs.1⟩).2
  have : rankC H d v (d (e ⟨_, hs.1⟩)) = i := by
    rw [he, rankC_eq_of_equiv e he]; exact hs.2
  exact (congrArg (pick H d v) this).symm.trans (pick_rankC hd h1)

end Podc.RandomizationTwoHop
