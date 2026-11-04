import Papers.PODC2014.RandomizationTwoHop.Lang

/-!
# Algorithm `A*` (§3.1, Figure 3)

`A*` is a deterministic anonymous algorithm for `Πᶜ` that proceeds in phases `p = 1, 2, …`.
Every node `v` keeps a bit string `b(v)` (initially empty); `I^p = (V, E, i, c, b^p)`.
In phase `p`, node `v`

* **Update-Graph**: computes its view `L = L(v, I^p)` and the set `F` of the view graphs of all
  *candidates* `Ĝ` (C1: at most `p` nodes; C2: some node of `Ĝ` has view `L`; C3: `Ĝ` without
  the bits is an instance of `Πᶜ`); if `F ≠ ∅` it selects the smallest one `Ĝ*` (fewest nodes,
  ties broken by a fixed order) and the node `v*` of `Ĝ*` corresponding to `v`;
* **Update-Output**: simulates `A_R` on `Ĝ*` with the bits `b̂*` as random bits for
  `l = min |b̂*(u)|` rounds; if all nodes output (the simulation is *successful*), `v` outputs
  the output of `v*`;
* **Update-Bits**: if some `p`-extension of `b̂*` (bit strings of length `p` extending `b̂*`)
  induces a successful `p`-round simulation, `v` sets `b(v)` to the value at `v*` of the smallest
  such extension.

## Formalization

All objects are functions of views, represented by walk languages:

* `bL p W`: the bit string `b^p(v)` of a node with depth-infinity view `W` (labels: input and
  colour). Phase `p` only looks at `Lv p W = trunc p (relabel (bL p) W)`, the view of tree
  depth `p` (i.e. `L_{p+1}(v, I^p)`) in the graph labelled with input, colour and bits.
  **Change w.r.t. the paper:** the paper uses `L_p(v, I^p)` (tree depth `p - 1`). With port
  numbers, `p - 1` simulated rounds depend on the view of tree depth `p` (see `decided_local`), so
  with depth `p - 1` Lemma 9's argument breaks; we use one more level. Computing it takes `p`
  rounds, exactly the paper's round count for this step.
* The view graph `Ĝ*` is represented canonically by its node set `S` (a set of walk languages);
  the simulation runs on the infinite view graph `viewLGraph G` of a graph `G` realizing `S`
  chosen canonically from `S` (by choice), with colour-sorted ports. Ties in the selection and
  the "smallest" extension are resolved by choice functions of the (canonical) data; any fixed
  rule works (the analysis only uses that it is a function of the data).
* `outPhase p W`: the output produced in phase `p` (if any).
* `astar`: the message-passing algorithm (`Flood.lean`): every node floods its truncated walk
  language and, in round `r`, evaluates phase `⌊√r⌋` (the view is deep enough by then:
  `bL_depthLocal`).
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph

namespace AStar

variable {In Out C : Type} [LinearOrder C] (Pb : Problem In Out) (AR : RAlg In Out)

/-- Labels of `I^p`: input, colour, bits. -/
abbrev L1 (In C : Type) := (In × C) × List Bool

/-- Candidates for phase `p` (conditions C1–C3), for the view `Lv` of the node. -/
def IsCand (p : ℕ) (Lv : Set (List (L1 In C))) (G : LGraph (L1 In C)) : Prop :=
  Nat.card G.V ≤ p ∧ (∃ v, trunc p (⟪G⟫ v) = Lv) ∧ (colored C Pb).inst (G.map Prod.fst)

/-- The set `F` of (view graphs of) candidates, each represented by its set of views. -/
def Fam (p : ℕ) (Lv : Set (List (L1 In C))) : Set (Set (Set (List (L1 In C)))) :=
  {S | ∃ G, IsCand Pb p Lv G ∧ Set.range ⟪G⟫ = S}

open Classical in
/-- Select a set with the minimum number of elements, ties broken by a fixed well-order. -/
noncomputable def select {α : Type} (F : Set (Set α)) : Option (Set α) :=
  if h : F.Nonempty then
    some (WellFounded.min ((WellOrderingRel.isWellOrder (α := Set α)).wf)
      {S | S ∈ F ∧ S.ncard = Nat.find (⟨_, h.some, h.some_mem, rfl⟩ : ∃ k, ∃ S ∈ F, S.ncard = k)}
      (by
        obtain ⟨S, hS, hk⟩ := Nat.find_spec (⟨_, h.some, h.some_mem, rfl⟩ : ∃ k, ∃ S ∈ F, S.ncard = k)
        exact ⟨S, hS, hk⟩))
  else none

theorem select_spec {α : Type} {F : Set (Set α)} {S : Set α} (h : select F = some S) :
    S ∈ F ∧ ∀ S' ∈ F, S.ncard ≤ S'.ncard := by
  classical
  unfold select at h
  split_ifs at h with hne
  obtain rfl := Option.some.inj h
  have hm := WellFounded.min_mem ((WellOrderingRel.isWellOrder (α := Set α)).wf)
      {S | S ∈ F ∧ S.ncard = Nat.find (⟨_, hne.some, hne.some_mem, rfl⟩ : ∃ k, ∃ S ∈ F, S.ncard = k)}
      (by
        obtain ⟨S, hS, hk⟩ := Nat.find_spec (⟨_, hne.some, hne.some_mem, rfl⟩ : ∃ k, ∃ S ∈ F, S.ncard = k)
        exact ⟨S, hS, hk⟩)
  obtain ⟨hmF, hmk⟩ := hm
  refine ⟨hmF, fun S' hS' => ?_⟩
  have := Nat.find_min' (⟨_, hne.some, hne.some_mem, rfl⟩ : ∃ k, ∃ S ∈ F, S.ncard = k) ⟨S', hS', rfl⟩
  omega

theorem select_eq_none {α : Type} {F : Set (Set α)} (h : select F = none) : F = ∅ := by
  classical
  unfold select at h
  split_ifs at h with hne
  exact Set.not_nonempty_iff_eq_empty.1 hne

/-- `G` realizes the view-graph node set `S` (and is 2-hop coloured). -/
def Realizes (S : Set (Set (List (L1 In C)))) (G : LGraph (L1 In C)) : Prop :=
  IsTwoHopColoring G.G (Prod.snd ∘ Prod.fst ∘ G.lab) ∧ Set.range ⟪G⟫ = S

/-- Simulation of `A_R` on `J` with colour-sorted ports, bits `b`. -/
noncomputable def sim (J : LGraph (L1 In C)) (b : J.V → List Bool) : ℕ → J.V → Option Out :=
  runC AR (Prod.fst ∘ Prod.fst) (Prod.snd ∘ Prod.fst) (X := J) (fun T => bitsOf (b T))

/-- The bits carried by the labels. -/
def bitsJ (J : LGraph (L1 In C)) (T : J.V) : List Bool := (J.lab T).2

/-- The successful `p`-extensions (Update-Bits). -/
def extSet (p : ℕ) (J : LGraph (L1 In C)) : Set (J.V → List Bool) :=
  {b' | (∀ T, bitsJ J T <+: b' T ∧ (b' T).length = p) ∧ ∀ T, (sim AR J b' p T).isSome}

open Classical in
/-- Phase `p` on the selected view graph `J` (Update-Output and Update-Bits). -/
noncomputable def phaseJ (p : ℕ) (Lv : Set (List (L1 In C))) (J : LGraph (L1 In C)) :
    Option Out × Option (List Bool) :=
  if hv : ∃ T : J.V, trunc p (⟪J⟫ T) = Lv then
    let l := ⨅ T, (bitsJ J T).length
    (if ∀ T, (sim AR J (bitsJ J) l T).isSome then sim AR J (bitsJ J) l hv.choose else none,
     if hB : (extSet AR p J).Nonempty then some (hB.some hv.choose) else none)
  else (none, none)

open Classical in
/-- Phase `p` given the selected node set `S`. -/
noncomputable def phaseS (p : ℕ) (Lv : Set (List (L1 In C))) (S : Set (Set (List (L1 In C)))) :
    Option Out × Option (List Bool) :=
  if h : ∃ G, Realizes S G then phaseJ AR p Lv (viewLGraph h.choose) else (none, none)

/-- Phase `p` of a node with view `Lv` (`Lv = L_{p+1}(v, I^p)`): its output (if any) and its new
bit string (if it changes). -/
noncomputable def phase (p : ℕ) (Lv : Set (List (L1 In C))) : Option Out × Option (List Bool) :=
  match select (Fam Pb p Lv) with
  | none => (none, none)
  | some S => phaseS AR p Lv S

/-- `bL p W`: the bit string `b^p(v)` of a node whose depth-infinity view is `W`. -/
noncomputable def bL : ℕ → Set (List (In × C)) → List Bool
  | 0, _ => []
  | p + 1, W => ((phase Pb AR p (trunc p (relabel (bL p) W))).2).getD (bL p W)

/-- The view used in phase `p`: tree depth `p` of the graph with bits `b^p`. -/
noncomputable def Lv (p : ℕ) (W : Set (List (In × C))) : Set (List (L1 In C)) :=
  trunc p (relabel (bL Pb AR p) W)

/-- The output of a node with view `W` in phase `p`, if any. -/
noncomputable def outPhase (p : ℕ) (W : Set (List (In × C))) : Option Out :=
  (phase Pb AR p (Lv Pb AR p W)).1

theorem bL_succ (p : ℕ) (W : Set (List (In × C))) :
    bL Pb AR (p + 1) W = ((phase Pb AR p (Lv Pb AR p W)).2).getD (bL Pb AR p W) := rfl

/-- Depth needed for `bL p`: `Db 0 = 0`, `Db (p+1) = p + Db p`. -/
def Db : ℕ → ℕ
  | 0 => 0
  | p + 1 => p + Db p

theorem bL_depthLocal (p : ℕ) : DepthLocal (Db p) (bL (C := C) Pb AR p) := by
  induction p with
  | zero => intro _ _ _; rfl
  | succ p ih =>
    intro T T' h
    have hL : Lv (C := C) Pb AR p T = Lv Pb AR p T' := by
      unfold Lv
      exact trunc_relabel_congr ih (by simpa [Db, Nat.add_comm] using h)
    rw [bL_succ, bL_succ, hL, ih T T' (trunc_eq_of_le (by simp [Db]) h)]

theorem outPhase_depthLocal (p : ℕ) : DepthLocal (Db (p + 1)) (outPhase (C := C) Pb AR p) := by
  intro T T' h
  have hL : Lv (C := C) Pb AR p T = Lv Pb AR p T' := by
    unfold Lv
    exact trunc_relabel_congr (bL_depthLocal Pb AR p) (by simpa [Db, Nat.add_comm] using h)
  unfold outPhase; rw [hL]

theorem Db_succ_le (p : ℕ) : Db (p + 1) ≤ p * p := by
  induction p with
  | zero => simp [Db]
  | succ p ih => simp only [Db] at ih ⊢; nlinarith

end AStar

end Podc.RandomizationTwoHop
