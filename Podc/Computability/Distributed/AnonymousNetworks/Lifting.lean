import Podc.Computability.Distributed.AnonymousNetworks.Basic

-- CSLib candidate: Cslib/Computability/Distributed/AnonymousNetworks/Lifting.lean

/-!
# Fibrations and the Lifting lemma

* `Fibration G B`: a surjective vertex map `φ` whose restriction to the in-neighbourhood of every
  vertex `i` is a bijection onto the in-neighbourhood of `φ i` (for simple graphs the edge map of a
  graph fibration is determined by the vertex map). `Fibration.Compatible m` adds what the
  communication model `m` lets agents observe: outdegrees (outdegree awareness) and output ports
  (output port awareness).
* `Fibration.runFrom_comp` (Lifting lemma, Lemma 3.1 of Charron-Bost–Lambein-Monette): executions on
  the base lift fibrewise to executions on the total graph.
* `Fibration.eq_of_computesOn` (Lemma 3.2): a function computed on both `G` and `B` satisfies
  `f^φ = f`.
* `Network.map`: relabelling a network along a bijection; `IsoClosed`; Lemma 3.3
  (`Computes.perm_eq`): a function computable in an isomorphism-closed class is invariant under
  permutations of its arguments, on the lengths of the networks of the class.
-/

namespace Cslib.AnonNet

open Finset Filter Topology

universe u v

variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

/-- A fibration of (static, simple) networks. -/
structure Fibration (G : Network V) (B : Network W) where
  /-- The vertex map. -/
  toFun : V → W
  surjective : Function.Surjective toFun
  /-- In-neighbourhoods are mapped bijectively. -/
  bijOn : ∀ i, Set.BijOn toFun (G.inN i) (B.inN (toFun i))

namespace Fibration

variable {G : Network V} {B : Network W}

/-- What the fibration must preserve so that the model `m` cannot tell `G` from `B` locally. -/
def Compatible (φ : Fibration G B) : CommModel → Prop
  | .broadcast => True
  | .symmetric => True
  | .outdegree => ∀ j, B.outdeg (φ.toFun j) = G.outdeg j
  | .outPort => ∀ j, B.outdeg (φ.toFun j) = G.outdeg j ∧
      ∀ i ∈ G.out j, B.port (φ.toFun j) (φ.toFun i) = G.port j i

variable {I : Type u} {X : Type v}

lemma send_eq (φ : Fibration G B) {m : CommModel} (hφ : φ.Compatible m)
    {A : Algorithm I X} (hA : m.Allowed A) (q : A.Q) {i j : V} (hij : i ∈ G.out j) :
    A.send q (G.outdeg j) (G.port j i) =
      A.send q (B.outdeg (φ.toFun j)) (B.port (φ.toFun j) (φ.toFun i)) := by
  cases m with
  | broadcast => exact hA _ _ _ _ _
  | symmetric => exact hA _ _ _ _ _
  | outdegree => rw [hφ j]; exact hA _ _ _ _
  | outPort => rw [(hφ j).1, (hφ j).2 i hij]

lemma recv_comp (φ : Fibration G B) {m : CommModel} (hφ : φ.Compatible m)
    {A : Algorithm I X} (hA : m.Allowed A) (C : W → A.Q) (i : V) :
    G.recv A (C ∘ φ.toFun) i = B.recv A C (φ.toFun i) := by
  unfold Network.recv
  have himg : (G.inN i).image φ.toFun = B.inN (φ.toFun i) :=
    Finset.coe_inj.1 (by rw [Finset.coe_image]; exact (φ.bijOn i).image_eq)
  have hinj : Set.InjOn φ.toFun (G.inN i) := (φ.bijOn i).injOn
  rw [← himg, Finset.image_val_of_injOn hinj, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro j hj
  have hj' : i ∈ G.out j := (G.mem_inN).1 (by simpa using hj)
  simp only [Function.comp]
  exact φ.send_eq hφ hA _ hj'

/-- **Lemma 3.1 (Lifting lemma).** Every execution of `A` on the base `B`, copied fibrewise, is an
execution of `A` on `G`. -/
theorem runFrom_comp (φ : Fibration G B) {m : CommModel} (hφ : φ.Compatible m)
    {A : Algorithm I X} (hA : m.Allowed A) (C₀ : W → A.Q) (t : ℕ) :
    G.runFrom A (C₀ ∘ φ.toFun) t = B.runFrom A C₀ t ∘ φ.toFun := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Network.runFrom_succ, Network.runFrom_succ, ih]
    funext i
    simp only [Network.step, Function.comp]
    rw [← φ.recv_comp hφ hA]

theorem run_comp (φ : Fibration G B) {m : CommModel} (hφ : φ.Compatible m)
    {A : Algorithm I X} (hA : m.Allowed A) (x : W → I) (t : ℕ) :
    G.run A (x ∘ φ.toFun) t = B.run A x t ∘ φ.toFun :=
  φ.runFrom_comp hφ hA (A.init ∘ x) t

/-- **Lemma 3.2.** If `f` is computed by `A` on both `G` and `B`, then `f^φ = f`: for every
input vector `x` of `B`, `f (x ∘ φ) = f x`. -/
theorem eq_of_computesOn [TopologicalSpace X] [T2Space X] {n m' : ℕ} {G : Network (Fin n)}
    {B : Network (Fin m')} (φ : Fibration G B) {m : CommModel} (hφ : φ.Compatible m)
    {A : Algorithm I X} (hA : m.Allowed A) {valid : List I → Prop} {f : List I → X}
    (hG : ComputesOn A G valid f) (hB : ComputesOn A B valid f) (hn : 0 < n)
    (x : Fin m' → I) (hx : valid (List.ofFn x)) (hxφ : valid (List.ofFn (x ∘ φ.toFun))) :
    f (List.ofFn (x ∘ φ.toFun)) = f (List.ofFn x) := by
  let i : Fin n := ⟨0, hn⟩
  have h1 := hG (x ∘ φ.toFun) hxφ i
  have h2 := hB x hx (φ.toFun i)
  have : (fun t => A.out (G.run A (x ∘ φ.toFun) t i)) =
      fun t => A.out (B.run A x t (φ.toFun i)) := by
    funext t; rw [φ.run_comp hφ hA]; rfl
  rw [this] at h1
  exact tendsto_nhds_unique h1 h2

end Fibration

/-! ### Relabelling and isomorphism invariance -/

namespace Network

/-- Relabel a network along a bijection of the vertices. -/
def map (N : Network V) (σ : V ≃ W) : Network W where
  out w := (N.out (σ.symm w)).map σ.toEmbedding
  self_mem w := by simpa using N.self_mem (σ.symm w)
  port w w' := N.port (σ.symm w) (σ.symm w')
  port_lt w w' h := by
    rw [Finset.card_map]
    apply N.port_lt
    simpa [Finset.mem_map_equiv] using h
  port_injOn w := by
    intro a ha b hb hab
    simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply] at hab
    simp [N.port_injOn _ ha' hb' hab]

@[simp] lemma mem_out_map (N : Network V) (σ : V ≃ W) {w w' : W} :
    w' ∈ (N.map σ).out w ↔ σ.symm w' ∈ N.out (σ.symm w) := by
  simp [map, Finset.mem_map_equiv]

/-- The bijection `σ` is a fibration `N → N.map σ` (an isomorphism), compatible with every model. -/
def isoFibration (N : Network V) (σ : V ≃ W) : Fibration N (N.map σ) where
  toFun := σ
  surjective := σ.surjective
  bijOn i := by
    refine ⟨?_, σ.injective.injOn, ?_⟩
    · intro j hj
      simp only [Finset.mem_coe, mem_inN, mem_out_map, Equiv.symm_apply_apply] at hj ⊢
      exact hj
    · intro w hw
      refine ⟨σ.symm w, ?_, by simp⟩
      simp only [Finset.mem_coe, mem_inN, mem_out_map, Equiv.symm_apply_apply] at hw ⊢
      exact hw

lemma isoFibration_compatible (N : Network V) (σ : V ≃ W) (m : CommModel) :
    (N.isoFibration σ).Compatible m := by
  cases m with
  | broadcast => trivial
  | symmetric => trivial
  | outdegree =>
    intro j; simp [isoFibration, outdeg, map]
  | outPort =>
    intro j; refine ⟨by simp [isoFibration, outdeg, map], fun i _ => ?_⟩
    simp [isoFibration, map]

lemma map_stronglyConnected {N : Network V} (h : N.StronglyConnected) (σ : V ≃ W) :
    (N.map σ).StronglyConnected := by
  intro a b
  have := h (σ.symm a) (σ.symm b)
  have key : ∀ x y, Relation.ReflTransGen N.Adj x y →
      Relation.ReflTransGen (N.map σ).Adj (σ x) (σ y) := by
    intro x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _ e ih =>
      refine ih.tail ?_
      simpa [Adj] using e
  simpa using key _ _ this

lemma map_symmetric {N : Network V} (h : N.Symmetric) (σ : V ≃ W) : (N.map σ).Symmetric := by
  intro i j hij
  simp only [mem_out_map] at hij ⊢
  exact h _ _ hij

end Network

/-- A network class closed under relabelling (isomorphism). -/
def IsoClosed (C : NetClass) : Prop :=
  ∀ n (N : Network (Fin n)) (σ : Fin n ≃ Fin n), C n N → C n (N.map σ)

lemma staticSC_isoClosed : IsoClosed staticSC :=
  fun _ _ σ h => Network.map_stronglyConnected h σ

lemma sizeLE_isoClosed (B : ℕ) : IsoClosed (sizeLE B) :=
  fun _ _ σ h => ⟨Network.map_stronglyConnected h.1 σ, h.2⟩

lemma sizeEq_isoClosed (k : ℕ) : IsoClosed (sizeEq k) :=
  fun _ _ σ h => ⟨Network.map_stronglyConnected h.1 σ, h.2⟩

lemma CommModel.netOK_map {m : CommModel} {N : Network V} (h : m.NetOK N) (σ : V ≃ W) :
    m.NetOK (N.map σ) := by
  cases m with
  | symmetric => exact Network.map_symmetric h σ
  | _ => trivial

variable {I : Type u} {X : Type v}

/-- **Lemma 3.3.** If `A` computes `f` in an isomorphism-closed class containing a network with `n`
agents, then `f` is invariant under permutations of vectors of length `n` (for valid inputs). -/
theorem Computes.perm_eq [TopologicalSpace X] [T2Space X] {m : CommModel} {C : NetClass}
    {valid : List I → Prop} {f : List I → X} {A : Algorithm I X} (hA : m.Allowed A)
    (hC : IsoClosed C) (hcomp : Computes m C valid f A) {n : ℕ} (hn : 0 < n)
    {N : Network (Fin n)} (hN : C n N) (hNm : m.NetOK N) {l l' : List I} (hl : l.length = n)
    (hperm : l.Perm l') (hv : valid l) (hv' : valid l') : f l' = f l := by
  classical
  subst hl
  obtain ⟨σ, hσ⟩ := exists_equiv_ofFn_comp_eq l.get (l' := l') (by rw [List.ofFn_get]; exact hperm)
  have hG : ComputesOn A N valid f := hcomp _ hn N hN hNm
  have hB : ComputesOn A (N.map σ) valid f :=
    hcomp _ hn _ (hC _ N σ hN) (CommModel.netOK_map hNm σ)
  have := (N.isoFibration σ).eq_of_computesOn (N.isoFibration_compatible σ m) hA hG hB hn l.get
    (by rw [List.ofFn_get]; exact hv)
    (by change valid (List.ofFn (l.get ∘ σ)); rw [hσ]; exact hv')
  change f (List.ofFn (l.get ∘ σ)) = f (List.ofFn l.get) at this
  rwa [hσ, List.ofFn_get] at this

end Cslib.AnonNet
