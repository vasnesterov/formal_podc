import Papers.PODC2019.AutomaticSpeedup.Problem

/-!
# The speedup theorem for abstract view systems (Brandt, PODC 2019, §4.1–4.2)

The proof of Theorem 1 only uses a few structural facts about neighbourhoods. We isolate them in
`ViewSystem`: a class of port-numbered graphs (`Graph`, `Node`, `deg`, `nbr`, `rport`) together with
* `nv G v` — the radius-`t` view `N^t(v)` of a node,
* `ev G v i` — the radius-`t` view `N^t(e)` of the edge `e` behind port `i` of `v`, *seen from `v`*
  (i.e. with `v` marked as the endpoint we are interested in),
* `pv G v` — the radius-`(t-1)` view `N^{t-1}(v)`,
and the facts that `N^t(v)` determines each `N^t(e)` (`evOf`), that `N^t(e)` determines
`N^{t-1}(v)` and the port of `e` at `v` (`pvOf`, `portOf`), that the view of `e` seen from the
other endpoint is a function of the view seen from `v` (`flip`), and that views determine degrees.

An algorithm running in time `t` is a function of `nv` (`SolvesN`), a "half-round" algorithm is a
function of `ev` (`SolvesE`), and a `(t-1)`-round algorithm a function of `pv` (`SolvesP`).
`Ind1`/`Ind2` are the two clauses of `t`-independence (§3).

The concrete instance (port-numbering model, full-information views) is in `PortNumbering.lean`.

Main results:
* `solvesE_toEdge`, `solvesP_toPrev`: the forward half steps (proof of Theorem 1, (1) ⇒ (2)),
* `solvesE_ofPrev`, `solvesN_ofEdge`: the backward half steps ((2) ⇒ (1)). The first one needs
  `EdgeAsym`: the two endpoints of every edge must have different views of the edge. The paper
  does not assume this, and without it the statement is false (`Counterexample.lean`).
* `solvesE_max`, `solvesP_max`: the maximality simplification (Theorem 2).
* `speedup_forward`, `speedup_backward`, `speedupMax_forward`, `speedupMax_backward`.
-/

-- CSLib candidate (abstract round elimination)
namespace AutomaticSpeedup

open Problem

universe u

/-- An abstract system of graphs with radius-`t` node views, radius-`t` edge views and
radius-`(t-1)` node views. -/
structure ViewSystem where
  Graph : Type u
  Node : Graph → Type u
  deg : (G : Graph) → Node G → ℕ
  nbr : (G : Graph) → Node G → ℕ → Node G
  rport : (G : Graph) → Node G → ℕ → ℕ
  rport_lt : ∀ G v i, i < deg G v → rport G v i < deg G (nbr G v i)
  nbr_nbr : ∀ G v i, i < deg G v → nbr G (nbr G v i) (rport G v i) = v
  rport_rport : ∀ G v i, i < deg G v → rport G (nbr G v i) (rport G v i) = i
  /-- Radius-`t` node views. -/
  NV : Type u
  /-- Radius-`t` edge views, seen from one endpoint. -/
  EV : Type u
  /-- Radius-`(t-1)` node views. -/
  PV : Type u
  nv : (G : Graph) → Node G → NV
  ev : (G : Graph) → Node G → ℕ → EV
  pv : (G : Graph) → Node G → PV
  evOf : NV → ℕ → EV
  ev_eq : ∀ G v i, i < deg G v → ev G v i = evOf (nv G v) i
  degN : NV → ℕ
  deg_eq_degN : ∀ G v, deg G v = degN (nv G v)
  pvOf : EV → PV
  pv_eq : ∀ G v i, i < deg G v → pv G v = pvOf (ev G v i)
  portOf : EV → ℕ
  portOf_ev : ∀ G v i, i < deg G v → portOf (ev G v i) = i
  flip : EV → EV
  ev_flip : ∀ G v i, i < deg G v → ev G (nbr G v i) (rport G v i) = flip (ev G v i)
  degP : PV → ℕ
  deg_eq_degP : ∀ G v, deg G v = degP (pv G v)

namespace ViewSystem

variable (S : ViewSystem.{u}) {L : Type*}

/-- `out` is a correct solution of `P` (at maximum degree `Δ`) on `G`: labels in `f Δ`, every edge
configuration in `g Δ`, every node configuration in `h Δ`. -/
def Correct (P : Problem L) (Δ : ℕ) (G : S.Graph) (out : S.Node G → ℕ → L) : Prop :=
  (∀ v, ∀ i < S.deg G v, out v i ∈ P.f Δ) ∧
  (∀ v, ∀ i < S.deg G v,
    ({out v i, out (S.nbr G v i) (S.rport G v i)} : Multiset L) ∈ P.g Δ) ∧
  (∀ v, (Multiset.range (S.deg G v)).map (out v) ∈ P.h Δ)

/-- `A` solves `P` on all graphs of the system, looking only at radius-`t` node views. -/
def SolvesN (P : Problem L) (Δ : ℕ) (A : S.NV → ℕ → L) : Prop :=
  ∀ G, S.Correct P Δ G fun v i => A (S.nv G v) i

/-- `B` solves `P`, the output at `(v, e)` depending only on the view of `e` from `v`. -/
def SolvesE (P : Problem L) (Δ : ℕ) (B : S.EV → L) : Prop :=
  ∀ G, S.Correct P Δ G fun v i => B (S.ev G v i)

/-- `C` solves `P` looking only at radius-`(t-1)` node views. -/
def SolvesP (P : Problem L) (Δ : ℕ) (C : S.PV → ℕ → L) : Prop :=
  ∀ G, S.Correct P Δ G fun v i => C (S.pv G v) i

/-- Clause 1 of `t`-independence (§3): two extensions of an edge view, one along each endpoint,
can be realized simultaneously. -/
def Ind1 : Prop :=
  ∀ G v i, i < S.deg G v →
    ∀ H₁ w₁ k₁, k₁ < S.deg H₁ w₁ → S.ev H₁ w₁ k₁ = S.ev G v i →
    ∀ H₂ w₂ k₂, k₂ < S.deg H₂ w₂ → S.ev H₂ w₂ k₂ = S.ev G (S.nbr G v i) (S.rport G v i) →
    ∃ H w k, k < S.deg H w ∧ S.ev H w k = S.ev G v i ∧ S.nv H w = S.nv H₁ w₁ ∧
      S.nv H (S.nbr H w k) = S.nv H₂ w₂

/-- Clause 2 of `t`-independence (§3): extensions of a radius-`(t-1)` node view along the
different incident edges can be realized simultaneously. -/
def Ind2 : Prop :=
  ∀ G v (Hs : ℕ → S.Graph) (ws : ∀ i, S.Node (Hs i)),
    (∀ i < S.deg G v, S.pv (Hs i) (ws i) = S.pv G v) →
    ∃ H w, S.pv H w = S.pv G v ∧ ∀ i < S.deg G v, S.ev H w i = S.ev (Hs i) (ws i) i

/-- The two endpoints of every edge see the edge differently (edge symmetry breaking). -/
def EdgeAsym : Prop :=
  ∀ G v i, i < S.deg G v → S.ev G (S.nbr G v i) (S.rport G v i) ≠ S.ev G v i

variable {S}

theorem flip_flip_ev {G : S.Graph} {v : S.Node G} {i : ℕ} (hi : i < S.deg G v) :
    S.flip (S.flip (S.ev G v i)) = S.ev G v i := by
  have h1 := S.ev_flip G (S.nbr G v i) (S.rport G v i) (S.rport_lt G v i hi)
  rw [S.nbr_nbr G v i hi, S.rport_rport G v i hi, S.ev_flip G v i hi] at h1
  exact h1.symm

theorem portOf_flip {G : S.Graph} {v : S.Node G} {i : ℕ} (hi : i < S.deg G v) :
    S.portOf (S.flip (S.ev G v i)) = S.rport G v i := by
  rw [← S.ev_flip G v i hi, S.portOf_ev _ _ _ (S.rport_lt G v i hi)]

theorem pvOf_flip {G : S.Graph} {v : S.Node G} {i : ℕ} (hi : i < S.deg G v) :
    S.pvOf (S.flip (S.ev G v i)) = S.pv G (S.nbr G v i) := by
  rw [← S.ev_flip G v i hi, ← S.pv_eq _ _ _ (S.rport_lt G v i hi)]

/-! ### Forward direction: `Π` in time `t` ⇒ `Π_{1/2}` on edge views -/

/-- The algorithm `A_{1/2}` of §4.1: at `(v, e)` output the set of all labels that `A` outputs at
`(v, e)` in some extension of the edge view along `v`. -/
def toEdge (A : S.NV → ℕ → L) : S.EV → Set L :=
  fun x => {o | ∃ H w k, k < S.deg H w ∧ S.ev H w k = x ∧ A (S.nv H w) k = o}

theorem mem_toEdge {A : S.NV → ℕ → L} {G : S.Graph} {v : S.Node G} {i : ℕ}
    (hi : i < S.deg G v) : A (S.nv G v) i ∈ toEdge A (S.ev G v i) :=
  ⟨G, v, i, hi, rfl, rfl⟩

/-- `A_{1/2}` solves `Π_{1/2}` (proof of Theorem 1, parts A and B). -/
theorem solvesE_toEdge (hI : S.Ind1) {P : Problem L} {Δ : ℕ}
    (hΔ : ∀ G v, S.deg G v ≤ Δ) {A : S.NV → ℕ → L} (hA : S.SolvesN P Δ A) : S.SolvesE P.edgeStep Δ (toEdge A) := by
  intro G
  refine ⟨?_, ?_, ?_⟩
  · rintro v i - o ⟨H, w, k, hk, -, rfl⟩
    exact (hA H).1 w k hk
  · intro v i hi
    rw [edgeStep_g_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro o ⟨H, w, k, hk, -, rfl⟩; exact (hA H).1 w k hk
    · rintro o ⟨H, w, k, hk, -, rfl⟩; exact (hA H).1 w k hk
    · rintro y ⟨H₁, w₁, k₁, hk₁, he₁, rfl⟩ z ⟨H₂, w₂, k₂, hk₂, he₂, rfl⟩
      obtain ⟨H, w, k, hk, he, hn₁, hn₂⟩ := hI G v i hi H₁ w₁ k₁ hk₁ he₁ H₂ w₂ k₂ hk₂ he₂
      have hkk : k₁ = k := by
        rw [← S.portOf_ev _ _ _ hk₁, he₁, ← he, S.portOf_ev _ _ _ hk]
      have hrr : k₂ = S.rport H w k := by
        rw [← S.portOf_ev _ _ _ hk₂, he₂, S.ev_flip G v i hi, ← he, portOf_flip hk]
      have : ({A (S.nv H w) k, A (S.nv H (S.nbr H w k)) (S.rport H w k)} : Multiset L) ∈ P.g Δ :=
        (hA H).2.1 w k hk
      rw [hn₁, hn₂] at this; subst hkk; rwa [hrr]
  · intro v
    refine nodeEx_map_range_of (hΔ G v) ?_ (fun i => A (S.nv G v) i)
      (fun i hi => mem_toEdge hi) ((hA G).2.2 v)
    rintro i - o ⟨H, w, k, hk, -, rfl⟩; exact (hA H).1 w k hk

/-- The algorithm `A_1` of §4.1, derived from an edge-view algorithm `B`: at `(v, e)` output the
set of all labels that `B` outputs at `(v, e)` in some extension of `N^{t-1}(v)` along `e`. -/
def toPrev (B : S.EV → L) : S.PV → ℕ → Set L :=
  fun p i => {y | ∃ H w, S.pv H w = p ∧ i < S.deg H w ∧ B (S.ev H w i) = y}

theorem mem_toPrev {B : S.EV → L} {G : S.Graph} {v : S.Node G} {i : ℕ}
    (hi : i < S.deg G v) : B (S.ev G v i) ∈ toPrev B (S.pv G v) i :=
  ⟨G, v, rfl, hi, rfl⟩

/-- `A_1` solves `(Π')_1` whenever `B` solves `Π'` on edge views (proof of Theorem 1; as the paper
remarks, `Π'` need not be of the form `Π_{1/2}`). -/
theorem solvesP_toPrev (hI : S.Ind2) {P : Problem L} {Δ : ℕ} (hΔ : ∀ G v, S.deg G v ≤ Δ)
    {B : S.EV → L} (hB : S.SolvesE P Δ B) : S.SolvesP P.nodeStep Δ (toPrev B) := by
  have hf : ∀ p i, toPrev B p i ⊆ P.f Δ := by
    rintro p i y ⟨H, w, -, hi, rfl⟩; exact (hB H).1 w i hi
  intro G
  refine ⟨fun v i _ => hf _ _, fun v i hi => ?_, fun v => ?_⟩
  · rw [nodeStep_g_iff]
    exact ⟨hf _ _, hf _ _, _, mem_toPrev hi, _, mem_toPrev (S.rport_lt G v i hi), (hB G).2.1 v i hi⟩
  · refine ⟨by simpa using hΔ G v, ?_, ?_⟩
    · simp only [Multiset.mem_map, Multiset.mem_range, forall_exists_index, and_imp]
      rintro _ i - rfl; exact hf _ _
    · intro m hm
      rcases isEmpty_or_nonempty L with hL | hL
      · have hm0 : m = 0 := Multiset.eq_zero_of_forall_notMem fun a => isEmptyElim a
        subst hm0
        have hd : S.deg G v = 0 := by
          have := Multiset.rel_zero_left.1 hm
          simpa using congrArg Multiset.card this
        have := (hB G).2.2 v
        simpa [hd] using this
      obtain ⟨y, hy, rfl⟩ := rel_mem_map_range.1 hm
      choose Hs ws hpv hlt hyB using fun i (hi : i < S.deg G v) => hy i hi
      classical
      let Hs' : ℕ → S.Graph := fun i => if hi : i < S.deg G v then Hs i hi else G
      let ws' : ∀ i, S.Node (Hs' i) := fun i =>
        if hi : i < S.deg G v then cast (by simp [Hs', hi]) (ws i hi) else cast (by simp [Hs', hi]) v
      have key : ∀ i (hi : i < S.deg G v), S.pv (Hs' i) (ws' i) = S.pv G v ∧
          S.ev (Hs' i) (ws' i) i = S.ev (Hs i hi) (ws i hi) i := by
        intro i hi
        have e1 : Hs' i = Hs i hi := by simp [Hs', hi]
        have e2 : HEq (ws' i) (ws i hi) := by simp [ws', hi]
        clear_value Hs' ws'
        revert e2
        generalize ws' i = a
        revert a
        rw [e1]
        intro a e2
        cases e2
        exact ⟨hpv i hi, rfl⟩
      obtain ⟨H, w, hpvw, hev⟩ := hI G v Hs' ws' fun i hi => (key i hi).1
      have hdeg : S.deg H w = S.deg G v := by rw [S.deg_eq_degP, S.deg_eq_degP G, hpvw]
      have := (hB H).2.2 w
      rw [hdeg] at this
      convert this using 1
      refine Multiset.map_congr rfl fun i hi => ?_
      rw [Multiset.mem_range] at hi
      show y i = B (S.ev H w i)
      rw [hev i hi, (key i hi).2, hyB i hi]

/-! ### Backward direction -/

/-- A consistent choice of one endpoint of every edge from the edge view: the endpoint whose view
of the edge comes first in a fixed well-order. Consistent whenever `EdgeAsym` holds. -/
def First (x : S.EV) : Prop := WellOrderingRel x (S.flip x)

theorem first_or_first (hS : S.EdgeAsym) {G : S.Graph} {v : S.Node G} {i : ℕ}
    (hi : i < S.deg G v) :
    (First (S.ev G v i) ∧ ¬ First (S.flip (S.ev G v i))) ∨
      (¬ First (S.ev G v i) ∧ First (S.flip (S.ev G v i))) := by
  have hne : S.flip (S.ev G v i) ≠ S.ev G v i := by rw [← S.ev_flip G v i hi]; exact hS G v i hi
  unfold First
  rw [flip_flip_ev hi]
  rcases trichotomous_of WellOrderingRel (S.ev G v i) (S.flip (S.ev G v i)) with h | h | h
  · exact Or.inl ⟨h, asymm h⟩
  · exact absurd h.symm hne
  · exact Or.inr ⟨asymm h, h⟩

open Classical in
/-- From a `(t-1)`-round algorithm `C` for `(Π')_1`, an edge-view algorithm for `Π'`: the first
endpoint (`First`) picks a pair `(o, o')` from the two outputs of `C` at the edge that is good for
`Π'`, and both endpoints output their part of it. -/
noncomputable def ofPrev [Nonempty L] (P : Problem L) (Δ : ℕ) (C : S.PV → ℕ → Set L) :
    S.EV → L :=
  let pick : S.EV → L × L := fun x => Classical.epsilon fun p : L × L =>
    p.1 ∈ C (S.pvOf x) (S.portOf x) ∧ p.2 ∈ C (S.pvOf (S.flip x)) (S.portOf (S.flip x)) ∧
      ({p.1, p.2} : Multiset L) ∈ P.g Δ
  fun x => if First x then (pick x).1 else (pick (S.flip x)).2

/-- Backward half step `(Π')_1 ⇒ Π'` (proof of Theorem 1, (2) ⇒ (1), first half), under edge
symmetry breaking. -/
theorem solvesE_ofPrev [Nonempty L] (hS : S.EdgeAsym) {P : Problem L} {Δ : ℕ}
    {C : S.PV → ℕ → Set L} (hC : S.SolvesP P.nodeStep Δ C) : S.SolvesE P Δ (ofPrev P Δ C) := by
  classical
  set pick : S.EV → L × L := fun x => Classical.epsilon fun p : L × L =>
    p.1 ∈ C (S.pvOf x) (S.portOf x) ∧ p.2 ∈ C (S.pvOf (S.flip x)) (S.portOf (S.flip x)) ∧
      ({p.1, p.2} : Multiset L) ∈ P.g Δ with hpick
  have hof : ∀ x, ofPrev P Δ C x = if First x then (pick x).1 else (pick (S.flip x)).2 :=
    fun x => rfl
  -- the pick at a realized edge view is good
  have hgood : ∀ G v i, i < S.deg G v →
      (pick (S.ev G v i)).1 ∈ C (S.pv G v) i ∧
      (pick (S.ev G v i)).2 ∈ C (S.pv G (S.nbr G v i)) (S.rport G v i) ∧
      ({(pick (S.ev G v i)).1, (pick (S.ev G v i)).2} : Multiset L) ∈ P.g Δ := by
    intro G v i hi
    have hex : ∃ p : L × L, p.1 ∈ C (S.pvOf (S.ev G v i)) (S.portOf (S.ev G v i)) ∧
        p.2 ∈ C (S.pvOf (S.flip (S.ev G v i))) (S.portOf (S.flip (S.ev G v i))) ∧
        ({p.1, p.2} : Multiset L) ∈ P.g Δ := by
      rw [pvOf_flip hi, portOf_flip hi, ← S.pv_eq _ _ _ hi, S.portOf_ev _ _ _ hi]
      obtain ⟨-, -, y, hy, z, hz, hyz⟩ := nodeStep_g_iff.1 ((hC G).2.1 v i hi)
      exact ⟨(y, z), hy, hz, hyz⟩
    have := Classical.epsilon_spec hex
    have e1 : C (S.pvOf (S.ev G v i)) (S.portOf (S.ev G v i)) = C (S.pv G v) i := by
      rw [← S.pv_eq _ _ _ hi, S.portOf_ev _ _ _ hi]
    have e2 : C (S.pvOf (S.flip (S.ev G v i))) (S.portOf (S.flip (S.ev G v i))) =
        C (S.pv G (S.nbr G v i)) (S.rport G v i) := by rw [pvOf_flip hi, portOf_flip hi]
    exact ⟨e1 ▸ this.1, e2 ▸ this.2.1, this.2.2⟩
  -- the output at a realized half-edge is in the set output by `C`
  have hmem : ∀ G v i, i < S.deg G v → ofPrev P Δ C (S.ev G v i) ∈ C (S.pv G v) i := by
    intro G v i hi
    rw [hof]
    split_ifs
    · exact (hgood G v i hi).1
    · have hj := S.rport_lt G v i hi
      have := (hgood G _ _ hj).2.1
      rwa [S.nbr_nbr G v i hi, S.rport_rport G v i hi, S.ev_flip G v i hi] at this
  have hsub : ∀ G v i, i < S.deg G v → C (S.pv G v) i ⊆ P.f Δ := fun G v i hi =>
    (hC G).1 v i hi
  intro G
  refine ⟨fun v i hi => hsub G v i hi (hmem G v i hi), fun v i hi => ?_, fun v => ?_⟩
  · show ({ofPrev P Δ C (S.ev G v i), ofPrev P Δ C (S.ev G (S.nbr G v i) (S.rport G v i))} :
      Multiset L) ∈ P.g Δ
    rw [S.ev_flip G v i hi]
    rcases first_or_first hS hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [hof, hof, ite_eq_left h1, ite_eq_right h2, flip_flip_ev hi]
      exact (hgood G v i hi).2.2
    · rw [hof, hof, ite_eq_right h1, ite_eq_left h2, Multiset.pair_comm]
      have hj := S.rport_lt G v i hi
      have := (hgood G _ _ hj).2.2
      rwa [S.ev_flip G v i hi] at this
  · exact ((hC G).2.2 v).map_range _ fun i hi => hmem G v i hi

/-- From an edge-view algorithm `B` for `Π_{1/2}`, a node-view algorithm for `Π`: every node picks,
for its own ports, a choice of labels from the sets output by `B` that is good for `h`. -/
noncomputable def ofEdge [Nonempty L] (P : Problem L) (Δ : ℕ) (B : S.EV → Set L) :
    S.NV → ℕ → L :=
  fun n => Classical.epsilon fun y : ℕ → L =>
    (∀ i < S.degN n, y i ∈ B (S.evOf n i)) ∧ (Multiset.range (S.degN n)).map y ∈ P.h Δ

/-- Backward half step `Π_{1/2} ⇒ Π` (proof of Theorem 1, (2) ⇒ (1), second half). -/
theorem solvesN_ofEdge [Nonempty L] {P : Problem L} {Δ : ℕ} {B : S.EV → Set L}
    (hB : S.SolvesE P.edgeStep Δ B) : S.SolvesN P Δ (ofEdge P Δ B) := by
  have hspec : ∀ G v, (∀ i < S.deg G v, ofEdge P Δ B (S.nv G v) i ∈ B (S.ev G v i)) ∧
      (Multiset.range (S.deg G v)).map (ofEdge P Δ B (S.nv G v)) ∈ P.h Δ := by
    intro G v
    have hex : ∃ y : ℕ → L, (∀ i < S.degN (S.nv G v), y i ∈ B (S.evOf (S.nv G v) i)) ∧
        (Multiset.range (S.degN (S.nv G v))).map y ∈ P.h Δ := by
      obtain ⟨-, -, y, hy, hh⟩ := nodeEx_map_range.1 ((hB G).2.2 v)
      refine ⟨y, fun i hi => ?_, ?_⟩
      · rw [← S.deg_eq_degN] at hi; rw [← S.ev_eq _ _ _ hi]; exact hy i hi
      · rw [← S.deg_eq_degN]; exact hh
    have := Classical.epsilon_spec hex
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [S.ev_eq _ _ _ hi]; exact this.1 i (S.deg_eq_degN G v ▸ hi)
    · rw [S.deg_eq_degN]; exact this.2
  intro G
  refine ⟨fun v i hi => (hB G).1 v i hi ((hspec G v).1 i hi), fun v i hi => ?_,
    fun v => (hspec G v).2⟩
  have := edgeStep_g_iff.1 ((hB G).2.1 v i hi)
  exact this.2.2 _ ((hspec G v).1 i hi) _ ((hspec G _).1 _ (S.rport_lt G v i hi))

/-! ### Monotonicity in the problem -/

theorem Correct.mono {P Q : Problem L} {Δ : ℕ} {G : S.Graph} {out : S.Node G → ℕ → L}
    (h : S.Correct P Δ G out) (hf : P.f Δ ⊆ Q.f Δ) (hg : P.g Δ ⊆ Q.g Δ) (hh : P.h Δ ⊆ Q.h Δ) :
    S.Correct Q Δ G out :=
  ⟨fun v i hi => hf (h.1 v i hi), fun v i hi => hg (h.2.1 v i hi), fun v => hh (h.2.2 v)⟩

/-! ### Theorem 1 -/

/-- **Theorem 1, (1) ⇒ (2)** (abstract form): a `t`-round algorithm for `Π` yields a
`(t-1)`-round algorithm for `Π_1`, on any `t`-independent system of maximum degree `≤ Δ`. -/
theorem speedup_forward (hI1 : S.Ind1) (hI2 : S.Ind2) {P : Problem L} {Δ : ℕ}
    (hΔ : ∀ G v, S.deg G v ≤ Δ) {A : S.NV → ℕ → L} (hA : S.SolvesN P Δ A) :
    S.SolvesP P.speedup Δ (toPrev (toEdge A)) :=
  solvesP_toPrev hI2 hΔ (solvesE_toEdge hI1 hΔ hA)

/-- **Theorem 1, (2) ⇒ (1)** (abstract form), under edge symmetry breaking. No independence is
needed for this direction. -/
theorem speedup_backward [Nonempty L] (hS : S.EdgeAsym) {P : Problem L} {Δ : ℕ}
    {C : S.PV → ℕ → Set (Set L)} (hC : S.SolvesP P.speedup Δ C) :
    S.SolvesN P Δ (ofEdge P Δ (ofPrev P.edgeStep Δ C)) :=
  solvesN_ofEdge (solvesE_ofPrev hS hC)

/-! ### Maximality (§4.2, Theorem 2) -/

theorem EdgeAll.mono_right {P : Problem L} {Δ : ℕ} {Y Z Z' : Set L} (h : P.EdgeAll Δ Y Z)
    (hZ : Z' ⊆ Z) : P.EdgeAll Δ Y Z' :=
  ⟨h.1, hZ.trans h.2.1, fun y hy z hz => h.2.2 y hy z (hZ hz)⟩

theorem exists_maxL {P : Problem L} {Δ : ℕ} {Y Z : Set L} (h : P.EdgeAll Δ Y Z) :
    ∃ Y', Y ⊆ Y' ∧ P.EdgeAll Δ Y' Z ∧ ∀ Y'', Y' ⊂ Y'' → ¬ P.EdgeAll Δ Y'' Z := by
  obtain ⟨m, hYm, hm⟩ := zorn_subset_nonempty {Y' | P.EdgeAll Δ Y' Z} (fun c hc _ _ => by
    refine ⟨⋃₀ c, ⟨?_, h.2.1, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · rintro y ⟨Y', hY', hy⟩; exact (hc hY').1 hy
    · rintro y ⟨Y', hY', hy⟩ z hz; exact (hc hY').2.2 y hy z hz) Y h
  exact ⟨m, hYm, hm.1, fun Y'' hlt hY'' => hlt.2 (hm.2 hY'' hlt.1)⟩

open Classical in
/-- A maximal superset `Y' ⊇ Y` such that `{Y', Z}` still satisfies Property 1. -/
noncomputable def maxL (P : Problem L) (Δ : ℕ) (Y Z : Set L) : Set L :=
  if h : P.EdgeAll Δ Y Z then Classical.choose (exists_maxL h) else Y

theorem maxL_spec {P : Problem L} {Δ : ℕ} {Y Z : Set L} (h : P.EdgeAll Δ Y Z) :
    Y ⊆ maxL P Δ Y Z ∧ P.EdgeAll Δ (maxL P Δ Y Z) Z ∧
      ∀ Y'', maxL P Δ Y Z ⊂ Y'' → ¬ P.EdgeAll Δ Y'' Z := by
  simp only [maxL, h, ↓reduceDIte]; exact Classical.choose_spec (exists_maxL h)

/-- The pair `(O, O')` chosen in the proof of Theorem 2: first enlarge `O_u` maximally, then
`O_v`. -/
noncomputable def maxPair (P : Problem L) (Δ : ℕ) (Ou Ov : Set L) : Set L × Set L :=
  (maxL P Δ Ou Ov, maxL P Δ Ov (maxL P Δ Ou Ov))

theorem maxPair_spec {P : Problem L} {Δ : ℕ} {Ou Ov : Set L} (h : P.EdgeAll Δ Ou Ov) :
    Ou ⊆ (maxPair P Δ Ou Ov).1 ∧ Ov ⊆ (maxPair P Δ Ou Ov).2 ∧
      P.EdgeAllMax Δ (maxPair P Δ Ou Ov).1 (maxPair P Δ Ou Ov).2 := by
  obtain ⟨h1, h2, h3⟩ := maxL_spec h
  obtain ⟨h4, h5, h6⟩ := maxL_spec h2.symm
  refine ⟨h1, h4, h5.symm, fun Y'' hlt hY'' => h3 Y'' hlt (EdgeAll.mono_right hY'' h4),
    fun Z' hlt hZ' => h6 Z' hlt hZ'.symm⟩

open Classical in
/-- The edge-view algorithm of Theorem 2 (maximal version of `B`). -/
noncomputable def maxEdge (P : Problem L) (Δ : ℕ) (B : S.EV → Set L) : S.EV → Set L :=
  fun x => if First x then (maxPair P Δ (B x) (B (S.flip x))).1
    else (maxPair P Δ (B (S.flip x)) (B x)).2

theorem NodeEx.mono_map_range {P : Problem L} {Δ d : ℕ} {Y Y' : ℕ → Set L}
    (h : P.NodeEx Δ ((Multiset.range d).map Y)) (hY : ∀ i < d, Y i ⊆ Y' i)
    (hf : ∀ i < d, Y' i ⊆ P.f Δ) : P.NodeEx Δ ((Multiset.range d).map Y') := by
  obtain ⟨h1, -, m', hm', hh⟩ := h
  refine ⟨by simpa using h1, ?_, m', ?_, hh⟩
  · simp only [Multiset.mem_map, Multiset.mem_range, forall_exists_index, and_imp]
    rintro _ i hi rfl; exact hf i hi
  · rw [Multiset.rel_map_right] at hm' ⊢
    exact hm'.mono fun a _ i hi ha => hY i (Multiset.mem_range.1 hi) ha

/-- Theorem 2, first half: with edge symmetry breaking, an edge-view algorithm for `Π_{1/2}`
yields one for `Π'_{1/2}`. -/
theorem solvesE_max (hS : S.EdgeAsym) {P : Problem L} {Δ : ℕ} {B : S.EV → Set L}
    (hB : S.SolvesE P.edgeStep Δ B) : S.SolvesE P.edgeStepMax Δ (maxEdge P Δ B) := by
  classical
  have hall : ∀ G v i, i < S.deg G v → P.EdgeAll Δ (B (S.ev G v i)) (B (S.flip (S.ev G v i))) := by
    intro G v i hi; rw [← S.ev_flip G v i hi]; exact edgeStep_g_iff.1 ((hB G).2.1 v i hi)
  -- the output contains the original one and is good
  have hsup : ∀ G v i, i < S.deg G v →
      B (S.ev G v i) ⊆ maxEdge P Δ B (S.ev G v i) ∧ maxEdge P Δ B (S.ev G v i) ⊆ P.f Δ := by
    intro G v i hi
    have hall' := (hall G v i hi).symm
    rw [← flip_flip_ev hi] at hall'
    simp only [maxEdge]
    split_ifs
    · exact ⟨(maxPair_spec (hall G v i hi)).1, (maxPair_spec (hall G v i hi)).2.2.1.1⟩
    · have := maxPair_spec hall'
      rw [flip_flip_ev hi] at this
      exact ⟨this.2.1, this.2.2.1.2.1⟩
  intro G
  refine ⟨fun v i hi => (hsup G v i hi).2, fun v i hi => ?_, fun v => ?_⟩
  · show ({maxEdge P Δ B (S.ev G v i), maxEdge P Δ B (S.ev G (S.nbr G v i) (S.rport G v i))} :
      Multiset (Set L)) ∈ P.edgeStepMax.g Δ
    rw [edgeStepMax_g_iff, S.ev_flip G v i hi]
    rcases first_or_first hS hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [maxEdge, h1, h2, ite_true, ite_false, flip_flip_ev hi]
      exact (maxPair_spec (hall G v i hi)).2.2
    · simp only [maxEdge, h1, h2, ite_true, ite_false, flip_flip_ev hi]
      exact (maxPair_spec (hall G v i hi).symm).2.2.symm
  · exact NodeEx.mono_map_range ((hB G).2.2 v) (fun i hi => (hsup G v i hi).1)
      (fun i hi => (hsup G v i hi).2)

theorem map_range_update {α : Type*} [DecidableEq α] {d i : ℕ} (hi : i < d) (F : ℕ → α) (a : α) :
    (Multiset.range d).map (Function.update F i a) =
      a ::ₘ ((Multiset.range d).map F).erase (F i) := by
  have hr : Multiset.range d = i ::ₘ (Multiset.range d).erase i :=
    (Multiset.cons_erase (Multiset.mem_range.2 hi)).symm
  have hne : ((Multiset.range d).erase i).map (Function.update F i a) =
      ((Multiset.range d).erase i).map F := by
    refine Multiset.map_congr rfl fun j hj => ?_
    rw [(Multiset.nodup_range d).mem_erase_iff] at hj
    exact Function.update_of_ne hj.1 _ _
  rw [hr, Multiset.map_cons, Multiset.map_cons, Function.update_self, hne,
    Multiset.erase_cons_head]

theorem exists_chain_upper {α : Type*} {c : Set (ℕ → Set α)} (hc : IsChain (· ≤ ·) c)
    {y : ℕ → Set α} (hy : y ∈ c) (d : ℕ) (z : ℕ → α)
    (hz : ∀ i < d, ∃ F ∈ c, z i ∈ F i) : ∃ F ∈ c, ∀ i < d, z i ∈ F i := by
  induction d with
  | zero => exact ⟨y, hy, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ d ih =>
    obtain ⟨F, hF, hFz⟩ := ih fun i hi => hz i (Nat.lt_succ_of_lt hi)
    obtain ⟨F', hF', hz'⟩ := hz d (Nat.lt_succ_self d)
    rcases hc.total hF hF' with h | h
    · refine ⟨F', hF', fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h i (hFz i hi)
      · exact hz'
    · refine ⟨F, hF, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hFz i hi
      · exact h _ hz'

theorem exists_maxFam [Nonempty L] {P : Problem L} {Δ d : ℕ} {Y : ℕ → Set L}
    (h : P.NodeAll Δ ((Multiset.range d).map Y)) :
    ∃ F : ℕ → Set L, (∀ i < d, Y i ⊆ F i) ∧ P.NodeAll Δ ((Multiset.range d).map F) ∧
      ∀ i < d, ∀ Y', F i ⊂ Y' → ¬ P.NodeAll Δ ((Multiset.range d).map (Function.update F i Y')) := by
  classical
  set s : Set (ℕ → Set L) :=
    {F | (∀ i < d, Y i ⊆ F i) ∧ P.NodeAll Δ ((Multiset.range d).map F)} with hs
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ s (fun c hc hch y hy => by
    refine ⟨fun i => ⋃ F ∈ c, F i, ⟨fun i hi => (hc hy).1 i hi |>.trans
      (Set.subset_biUnion_of_mem (u := fun F => F i) hy), ?_⟩, fun F hF i =>
        Set.subset_biUnion_of_mem (u := fun F => F i) hF⟩
    rw [nodeAll_map_range]
    have hy' := nodeAll_map_range.1 (hc hy).2
    refine ⟨hy'.1, fun i hi => ?_, fun z hz => ?_⟩
    · simp only [Set.iUnion_subset_iff]
      exact fun F hF => (nodeAll_map_range.1 (hc hF).2).2.1 i hi
    · simp only [Set.mem_iUnion, exists_prop] at hz
      obtain ⟨F, hF, hFz⟩ := exists_chain_upper hch hy d z hz
      exact (nodeAll_map_range.1 (hc hF).2).2.2 z hFz) Y ⟨fun _ _ => le_rfl, h⟩
  refine ⟨m, hm.1.1, hm.1.2, fun i hi Y' hlt hY' => hlt.2 ?_⟩
  have hle : m ≤ Function.update m i Y' := by
    intro j; by_cases hj : j = i
    · subst hj; simp [hlt.1]
    · simp [Function.update_of_ne hj]
  have := hm.2 ⟨fun j hj => (hm.1.1 j hj).trans (hle j), hY'⟩ hle i
  simpa using this

open Classical in
/-- Maximal enlargement of a node's family of outputs (proof of Theorem 2, dual case). -/
noncomputable def maxFam [Nonempty L] (P : Problem L) (Δ d : ℕ) (Y : ℕ → Set L) : ℕ → Set L :=
  if h : P.NodeAll Δ ((Multiset.range d).map Y) then Classical.choose (exists_maxFam h) else Y

theorem maxFam_spec [Nonempty L] {P : Problem L} {Δ d : ℕ} {Y : ℕ → Set L}
    (h : P.NodeAll Δ ((Multiset.range d).map Y)) :
    (∀ i < d, Y i ⊆ maxFam P Δ d Y i) ∧
      P.NodeAllMax Δ ((Multiset.range d).map (maxFam P Δ d Y)) := by
  classical
  have hs := Classical.choose_spec (exists_maxFam h)
  simp only [maxFam, h, ↓reduceDIte]
  refine ⟨hs.1, hs.2.1, ?_⟩
  simp only [Multiset.mem_map, Multiset.mem_range, forall_exists_index, and_imp]
  rintro _ i hi rfl Y' hlt hY'
  refine hs.2.2 i hi Y' hlt ?_
  convert hY' using 1
  convert map_range_update hi _ Y'

/-- Theorem 2, second half: a `(t-1)`-round algorithm for `(Π')_1` yields one for the simplified
`(Π')'_1` (port numbers give the symmetry breaking at nodes). -/
theorem solvesP_max [Nonempty L] {P : Problem L} {Δ : ℕ} {C : S.PV → ℕ → Set L}
    (hC : S.SolvesP P.nodeStep Δ C) :
    S.SolvesP P.nodeStepMax Δ (fun p => maxFam P Δ (S.degP p) (C p)) := by
  have hspec : ∀ G v, (∀ i < S.deg G v, C (S.pv G v) i ⊆
        maxFam P Δ (S.degP (S.pv G v)) (C (S.pv G v)) i) ∧
      P.NodeAllMax Δ ((Multiset.range (S.deg G v)).map
        (maxFam P Δ (S.degP (S.pv G v)) (C (S.pv G v)))) := by
    intro G v
    have h := (hC G).2.2 v
    rw [S.deg_eq_degP] at h ⊢
    exact maxFam_spec h
  have hf : ∀ G v, ∀ i < S.deg G v, maxFam P Δ (S.degP (S.pv G v)) (C (S.pv G v)) i ⊆ P.f Δ := by
    intro G v i hi
    exact (nodeAll_map_range.1 (hspec G v).2.1).2.1 i hi
  intro G
  refine ⟨fun v i hi => hf G v i hi, fun v i hi => ?_, fun v => (hspec G v).2⟩
  show ({maxFam P Δ (S.degP (S.pv G v)) (C (S.pv G v)) i,
    maxFam P Δ (S.degP (S.pv G (S.nbr G v i))) (C (S.pv G (S.nbr G v i))) (S.rport G v i)} :
      Multiset (Set L)) ∈ P.nodeStepMax.g Δ
  rw [nodeStepMax_g_iff]
  obtain ⟨-, -, y, hy, z, hz, hyz⟩ := nodeStep_g_iff.1 ((hC G).2.1 v i hi)
  have hj := S.rport_lt G v i hi
  exact ⟨hf G v i hi, hf G _ _ hj, y, (hspec G v).1 i hi hy, z, (hspec G _).1 _ hj hz, hyz⟩

/-- **Theorem 2, (1) ⇒ (2)** (abstract form). -/
theorem speedupMax_forward (hI1 : S.Ind1) (hI2 : S.Ind2) (hS : S.EdgeAsym) {P : Problem L}
    {Δ : ℕ} (hΔ : ∀ G v, S.deg G v ≤ Δ) {A : S.NV → ℕ → L} (hA : S.SolvesN P Δ A) :
    ∃ C : S.PV → ℕ → Set (Set L), S.SolvesP P.speedupMax Δ C :=
  ⟨_, solvesP_max (solvesP_toPrev hI2 hΔ (solvesE_max hS (solvesE_toEdge hI1 hΔ hA)))⟩

/-- **Theorem 2, (2) ⇒ (1)** (abstract form). -/
theorem speedupMax_backward [Nonempty L] (hS : S.EdgeAsym) {P : Problem L} {Δ : ℕ}
    {C : S.PV → ℕ → Set (Set L)} (hC : S.SolvesP P.speedupMax Δ C) :
    ∃ A : S.NV → ℕ → L, S.SolvesN P Δ A := by
  have h1 : S.SolvesP P.edgeStepMax.nodeStep Δ C := fun G =>
    (hC G).mono subset_rfl subset_rfl (nodeStepMax_h_subset _ _)
  have h2 := solvesE_ofPrev hS h1
  have h3 : S.SolvesE P.edgeStep Δ (ofPrev P.edgeStepMax Δ C) := fun G =>
    (h2 G).mono subset_rfl (edgeStepMax_g_subset _ _) subset_rfl
  exact ⟨_, solvesN_ofEdge h3⟩

end ViewSystem

end AutomaticSpeedup
