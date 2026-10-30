import Mathlib

/-!
# Weak models of distributed computing: the model (§1 of Hella et al.)

We formalize §1 of Hella, Järvisalo, Kuusisto, Laurinharju, Lempiäinen, Luosto, Suomela,
Virtema, *Weak models of distributed computing, with connections to modal logic*
(PODC 2012; full version arXiv:1205.2051v3).

* Graphs are finite simple graphs `G : SimpleGraph V` with `[Finite V]`; `deg G v` is the number
  of neighbours.
* Ports: `Port G = Σ v, Fin (deg G v)` (the paper numbers ports `1, …, deg v`; we use
  `0, …, deg v - 1`).
* A port numbering (§1.2) is a bijection `p : P(G) → P(G)` with `A(p) = A(G)`
  (`PortNumbering`); it is consistent if `p` is an involution.
* A distributed state machine (§1.1) for degree bound `Δ` is `Machine Δ Y`: stopping states `Y`,
  intermediate states `Z`, messages `M` with the "no message" symbol `m0`, initial states `z0`
  (a function of the degree), message construction `μ : Z → ℕ → M` (port index `0 ≤ i < Δ`) and
  transition `δ : Z → (Fin Δ → M) → Y ⊕ Z`.
* The execution (§1.3) is `Machine.state`, defined literally as in the paper (incoming vector
  ordered by in-port number, padded with `m0`; stopped nodes send `m0` and keep their state).
* Algorithm classes (§1.5): `Machine.IsMultiset`, `Machine.IsSet`, `Machine.IsBroadcast`.
* Problem classes (§1.6): `VVc`, `VV`, `MV`, `SV`, `VB`, `MB`, `SB` and the constant-time
  versions `VVc1`, …, `SB1`.
-/

namespace Podc.WeakModelsModalLogic

open Function

section Graph

variable {V : Type*}

/-- The degree of a node: the number of its neighbours. -/
noncomputable def deg (G : SimpleGraph V) (v : V) : ℕ := Nat.card (G.neighborSet v)

/-- The ports `P(G)` of a graph: pairs `(v, i)` with `i < deg v`. -/
abbrev Port (G : SimpleGraph V) := Σ v : V, Fin (deg G v)

/-- `G ∈ F(Δ)`: the maximum degree of `G` is at most `Δ` (finiteness of `V` is a separate
`[Finite V]` assumption). -/
def MaxDegLE (G : SimpleGraph V) (Δ : ℕ) : Prop := ∀ v, deg G v ≤ Δ

/-- A port numbering of `G` (§1.2): a bijection `p` of the set of ports with `A(p) = A(G)`, i.e.
`{(u, v) : p((u,i)) = (v,j) for some i, j} = {(u, v) : {u, v} ∈ E}` (the two inclusions are the
fields `adj` and `cover`, see `PortNumbering.A_eq`). If `p((v, i)) = (u, j)`, a message sent by
`v` to its port `i` is received by `u` from its port `j`. -/
structure PortNumbering (G : SimpleGraph V) where
  /-- The bijection `p : P(G) → P(G)`. -/
  p : Port G ≃ Port G
  /-- `A(p) ⊆ A(G)`. -/
  adj : ∀ x : Port G, G.Adj x.1 (p x).1
  /-- `A(G) ⊆ A(p)`. -/
  cover : ∀ u v, G.Adj u v → ∃ x : Port G, x.1 = u ∧ (p x).1 = v

namespace PortNumbering

variable {G : SimpleGraph V} (P : PortNumbering G)

/-- The two fields `adj` and `cover` say exactly `A(p) = A(G)`. -/
theorem A_eq : {e : V × V | ∃ x : Port G, x.1 = e.1 ∧ (P.p x).1 = e.2} =
    {e : V × V | G.Adj e.1 e.2} := by
  ext ⟨u, v⟩
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, rfl, rfl⟩; exact P.adj x
  · exact P.cover u v

/-- A port numbering is consistent if `p` is an involution. -/
def Consistent : Prop := ∀ x, P.p (P.p x) = x

/-- The neighbour behind out-port `i` of `u`. -/
def outNbr (u : V) (i : Fin (deg G u)) : V := (P.p ⟨u, i⟩).1

/-- The neighbour behind in-port `i` of `v` (the sender of the messages received there). -/
def inNbr (v : V) (i : Fin (deg G v)) : V := (P.p.symm ⟨v, i⟩).1

theorem adj_outNbr (u : V) (i) : G.Adj u (P.outNbr u i) := P.adj ⟨u, i⟩

theorem adj_inNbr (v : V) (i) : G.Adj v (P.inNbr v i) := by
  have := P.adj (P.p.symm ⟨v, i⟩)
  simp only [Equiv.apply_symm_apply] at this
  exact this.symm

theorem outNbr_surj (u v : V) (h : G.Adj u v) : ∃ i, P.outNbr u i = v := by
  obtain ⟨⟨u', i⟩, rfl, hv⟩ := P.cover u v h
  exact ⟨i, hv⟩

theorem inNbr_surj (v w : V) (h : G.Adj v w) : ∃ i, P.inNbr v i = w := by
  obtain ⟨⟨w', j⟩, rfl, hv⟩ := P.cover w v h.symm
  rcases hx : P.p ⟨w', j⟩ with ⟨v', i⟩
  rw [hx] at hv
  subst hv
  refine ⟨i, ?_⟩
  simp [inNbr, ← hx]

/-- A surjection `Fin (deg v) → N(v)` is a bijection. -/
theorem injective_of_surj {v : V} (f : Fin (deg G v) → V) (hf : ∀ i, G.Adj v (f i))
    (hs : ∀ w, G.Adj v w → ∃ i, f i = w) : Injective f := by
  let g : Fin (deg G v) → G.neighborSet v := fun i => ⟨f i, hf i⟩
  have hg : Surjective g := by
    rintro ⟨w, hw⟩
    obtain ⟨i, hi⟩ := hs w hw
    exact ⟨i, Subtype.ext hi⟩
  have hcard : Nat.card (Fin (deg G v)) = Nat.card (G.neighborSet v) := by
    simp [deg]
  have hinj : Injective g := ((Nat.bijective_iff_surjective_and_card g).2 ⟨hg, hcard⟩).1
  intro i j hij
  exact hinj (Subtype.ext hij)

theorem injective_outNbr (u : V) : Injective (P.outNbr u) :=
  injective_of_surj _ (P.adj_outNbr u) (P.outNbr_surj u)

theorem injective_inNbr (v : V) : Injective (P.inNbr v) :=
  injective_of_surj _ (P.adj_inNbr v) (P.inNbr_surj v)

open Classical in
/-- `π(u, v)`: the out-port of `u` that is connected to `v` (`0` if `u`, `v` are not adjacent). -/
noncomputable def outPort (u v : V) : ℕ :=
  if h : ∃ i, P.outNbr u i = v then (h.choose : ℕ) else 0

theorem outPort_lt {u v : V} (h : G.Adj u v) : P.outPort u v < deg G u := by
  have h' : ∃ i, P.outNbr u i = v := P.outNbr_surj u v h
  simp only [outPort, h', dite_true]
  exact h'.choose.2

theorem outNbr_outPort {u v : V} (h : G.Adj u v) :
    P.outNbr u ⟨P.outPort u v, P.outPort_lt h⟩ = v := by
  have h' : ∃ i, P.outNbr u i = v := P.outNbr_surj u v h
  have := h'.choose_spec
  convert this using 2
  ext; simp [outPort, h']

theorem outPort_outNbr (u : V) (i : Fin (deg G u)) : P.outPort u (P.outNbr u i) = i := by
  have h := P.adj_outNbr u i
  have := P.outNbr_outPort h
  exact congrArg Fin.val (P.injective_outNbr u this)

/-- The sender port of in-port `i` of `v` is `π(inNbr v i, v)`. -/
theorem symm_snd (v : V) (i : Fin (deg G v)) :
    ((P.p.symm ⟨v, i⟩).2 : ℕ) = P.outPort (P.inNbr v i) v := by
  have h : P.outNbr (P.inNbr v i) (P.p.symm ⟨v, i⟩).2 = v := by
    simp [outNbr, inNbr]
  have h2 := P.outPort_outNbr (P.inNbr v i) (P.p.symm ⟨v, i⟩).2
  rw [h] at h2
  exact h2.symm

end PortNumbering

end Graph

/-! ### Distributed state machines and their execution -/

/-- A distributed state machine for `F(Δ)` (§1.1) with stopping states `Y`. Ports are numbered
`0, …, Δ - 1`; the values of `μ z i` for `i ≥ Δ` are irrelevant. -/
structure Machine (Δ : ℕ) (Y : Type) where
  /-- Intermediate states. -/
  Z : Type
  /-- Messages. -/
  M : Type
  /-- The "no message" symbol. -/
  m0 : M
  /-- Initial state as a function of the degree. -/
  z0 : ℕ → Y ⊕ Z
  /-- `μ z i`: the message sent to port `i` in state `z`. -/
  μ : Z → ℕ → M
  /-- State transition on the vector of received messages. -/
  δ : Z → (Fin Δ → M) → Y ⊕ Z

namespace Machine

variable {Δ : ℕ} {Y : Type} (A : Machine Δ Y)

/-- `μ` extended to stopping states: stopped nodes send `m0`. -/
def send : Y ⊕ A.Z → ℕ → A.M
  | .inl _, _ => A.m0
  | .inr z, i => A.μ z i

/-- `δ` extended to stopping states: stopped nodes keep their state. -/
def update : Y ⊕ A.Z → (Fin Δ → A.M) → Y ⊕ A.Z
  | .inl y, _ => .inl y
  | .inr z, a => A.δ z a

@[simp] theorem send_inl (y : Y) (i : ℕ) : A.send (.inl y) i = A.m0 := rfl
@[simp] theorem send_inr (z : A.Z) (i : ℕ) : A.send (.inr z) i = A.μ z i := rfl
@[simp] theorem update_inl (y : Y) a : A.update (.inl y) a = .inl y := rfl
@[simp] theorem update_inr (z : A.Z) a : A.update (.inr z) a = A.δ z a := rfl

variable {V : Type*} (G : SimpleGraph V) (P : PortNumbering G)

/-- The vector `~a(u)` received by `u` when the state vector is `x` (§1.3): the message on in-port
`i < deg u` is `μ(x(v), j)` where `(v, j) = p⁻¹((u, i))`; entries `i ≥ deg u` are `m0`. -/
noncomputable def recv (x : V → Y ⊕ A.Z) (u : V) : Fin Δ → A.M := fun i =>
  if h : (i : ℕ) < deg G u then
    A.send (x (P.p.symm ⟨u, ⟨i, h⟩⟩).1) (P.p.symm ⟨u, ⟨i, h⟩⟩).2
  else A.m0

/-- One synchronous round. -/
noncomputable def step (x : V → Y ⊕ A.Z) : V → Y ⊕ A.Z := fun u =>
  A.update (x u) (A.recv G P x u)

/-- The initial state vector `x₀(u) = z₀(deg u)`. -/
noncomputable def init : V → Y ⊕ A.Z := fun u => A.z0 (deg G u)

/-- The state vector `x_t` of the execution of `A` in `(G, p)`. -/
noncomputable def state (t : ℕ) : V → Y ⊕ A.Z := (A.step G P)^[t] (A.init G)

theorem state_zero : A.state G P 0 = A.init G := rfl

theorem state_succ (t : ℕ) : A.state G P (t + 1) = A.step G P (A.state G P t) :=
  iterate_succ_apply' _ _ _

/-- `A` stops in time `T` in `(G, p)` with output `S`. -/
def StopsWith (T : ℕ) (S : V → Y) : Prop := ∀ u, A.state G P T u = .inl (S u)

/-- Class `Multiset` (§1.5): `δ` depends only on the multiset of received messages. -/
def IsMultiset : Prop :=
  ∀ z (a b : Fin Δ → A.M), Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val →
    A.δ z a = A.δ z b

/-- Class `Set` (§1.5): `δ` depends only on the set of received messages. -/
def IsSet : Prop := ∀ z (a b : Fin Δ → A.M), Set.range a = Set.range b → A.δ z a = A.δ z b

/-- Class `Broadcast` (§1.5): the same message is sent to all ports. -/
def IsBroadcast : Prop := ∀ z (i j : ℕ), i < Δ → j < Δ → A.μ z i = A.μ z j

theorem range_eq_of_multiset_eq {M : Type*} {a b : Fin Δ → M}
    (h : Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val) :
    Set.range a = Set.range b := by
  ext x
  have := congrArg (x ∈ ·) h
  simpa [eq_comm] using this

theorem IsSet.isMultiset {A : Machine Δ Y} (h : A.IsSet) : A.IsMultiset :=
  fun z a b hab => h z a b (range_eq_of_multiset_eq hab)

end Machine

/-! ### Graph problems and problem classes -/

/-- A graph problem (§1.4): to each graph `G = (V, E)` a set of solutions `S : V → Y`. -/
def GraphProblem (Y : Type) : Type 1 := ∀ ⦃V : Type⦄, SimpleGraph V → Set (V → Y)

/-- An algorithm: a sequence `(A_Δ)` of distributed state machines. -/
def Algorithm (Y : Type) : Type 1 := (Δ : ℕ) → Machine Δ Y

namespace Algorithm

variable {Y : Type}

/-- `A` solves `Π` in time `T` (§1.4): for all `Δ`, all finite `G ∈ F(Δ)` and all port numberings
`p`, `A_Δ` stops in time `T(Δ, |V|)` in `(G, p)` with an output in `Π(G)`. -/
def SolvesIn (A : Algorithm Y) (Pr : GraphProblem Y) (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ (Δ : ℕ) (V : Type) [Finite V] (G : SimpleGraph V), MaxDegLE G Δ → ∀ P : PortNumbering G,
    ∃ S : V → Y, (A Δ).StopsWith G P (T Δ (Nat.card V)) S ∧ S ∈ Pr G

/-- `A` solves `Π` in time `T` assuming consistency. -/
def SolvesInC (A : Algorithm Y) (Pr : GraphProblem Y) (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ (Δ : ℕ) (V : Type) [Finite V] (G : SimpleGraph V), MaxDegLE G Δ → ∀ P : PortNumbering G,
    P.Consistent → ∃ S : V → Y, (A Δ).StopsWith G P (T Δ (Nat.card V)) S ∧ S ∈ Pr G

theorem SolvesIn.solvesInC {A : Algorithm Y} {Pr T} (h : A.SolvesIn Pr T) : A.SolvesInC Pr T :=
  fun Δ V _ G hG P _ => h Δ V G hG P

end Algorithm

/-- `Pr` is solvable by an algorithm all of whose machines satisfy `C` (in some time `T`). -/
def Solvable {Y : Type} (C : ∀ {Δ : ℕ}, Machine Δ Y → Prop) (Pr : GraphProblem Y) : Prop :=
  ∃ (A : Algorithm Y) (T : ℕ → ℕ → ℕ), (∀ Δ, C (A Δ)) ∧ A.SolvesIn Pr T

/-- `Pr` is solvable in constant time (a time bound depending on `Δ` only) by an algorithm all of
whose machines satisfy `C`. -/
def Solvable1 {Y : Type} (C : ∀ {Δ : ℕ}, Machine Δ Y → Prop) (Pr : GraphProblem Y) : Prop :=
  ∃ (A : Algorithm Y) (T : ℕ → ℕ), (∀ Δ, C (A Δ)) ∧ A.SolvesIn Pr (fun Δ _ => T Δ)

variable (Y : Type)

/-- `VVc`: solvable by a `Vector` algorithm assuming consistency. -/
def VVc : Set (GraphProblem Y) := {Pr | ∃ (A : Algorithm Y) (T : ℕ → ℕ → ℕ), A.SolvesInC Pr T}
/-- `VV`: solvable by a `Vector` algorithm. -/
def VV : Set (GraphProblem Y) := {Pr | Solvable (fun _ => True) Pr}
/-- `MV`: solvable by a `Multiset` algorithm. -/
def MV : Set (GraphProblem Y) := {Pr | Solvable (fun A => A.IsMultiset) Pr}
/-- `SV`: solvable by a `Set` algorithm. -/
def SV : Set (GraphProblem Y) := {Pr | Solvable (fun A => A.IsSet) Pr}
/-- `VB`: solvable by a `Broadcast` algorithm. -/
def VB : Set (GraphProblem Y) := {Pr | Solvable (fun A => A.IsBroadcast) Pr}
/-- `MB`: solvable by a `Multiset ∩ Broadcast` algorithm. -/
def MB : Set (GraphProblem Y) := {Pr | Solvable (fun A => A.IsMultiset ∧ A.IsBroadcast) Pr}
/-- `SB`: solvable by a `Set ∩ Broadcast` algorithm. -/
def SB : Set (GraphProblem Y) := {Pr | Solvable (fun A => A.IsSet ∧ A.IsBroadcast) Pr}

/-- `VVc(1)`. -/
def VVc1 : Set (GraphProblem Y) :=
  {Pr | ∃ (A : Algorithm Y) (T : ℕ → ℕ), A.SolvesInC Pr (fun Δ _ => T Δ)}
/-- `VV(1)`. -/
def VV1 : Set (GraphProblem Y) := {Pr | Solvable1 (fun _ => True) Pr}
/-- `MV(1)`. -/
def MV1 : Set (GraphProblem Y) := {Pr | Solvable1 (fun A => A.IsMultiset) Pr}
/-- `SV(1)`. -/
def SV1 : Set (GraphProblem Y) := {Pr | Solvable1 (fun A => A.IsSet) Pr}
/-- `VB(1)`. -/
def VB1 : Set (GraphProblem Y) := {Pr | Solvable1 (fun A => A.IsBroadcast) Pr}
/-- `MB(1)`. -/
def MB1 : Set (GraphProblem Y) := {Pr | Solvable1 (fun A => A.IsMultiset ∧ A.IsBroadcast) Pr}
/-- `SB(1)`. -/
def SB1 : Set (GraphProblem Y) := {Pr | Solvable1 (fun A => A.IsSet ∧ A.IsBroadcast) Pr}

/-! ### Trivial containments (Figure 5a) -/

variable {Y}

theorem Solvable.mono {C C' : ∀ {Δ : ℕ}, Machine Δ Y → Prop} (h : ∀ {Δ} (A : Machine Δ Y), C A → C' A)
    {Pr : GraphProblem Y} (hs : Solvable C Pr) : Solvable C' Pr := by
  obtain ⟨A, T, hA, hT⟩ := hs
  exact ⟨A, T, fun Δ => h _ (hA Δ), hT⟩

theorem Solvable1.mono {C C' : ∀ {Δ : ℕ}, Machine Δ Y → Prop} (h : ∀ {Δ} (A : Machine Δ Y), C A → C' A)
    {Pr : GraphProblem Y} (hs : Solvable1 C Pr) : Solvable1 C' Pr := by
  obtain ⟨A, T, hA, hT⟩ := hs
  exact ⟨A, T, fun Δ => h _ (hA Δ), hT⟩

theorem Solvable1.solvable {C : ∀ {Δ : ℕ}, Machine Δ Y → Prop} {Pr : GraphProblem Y}
    (hs : Solvable1 C Pr) : Solvable C Pr := by
  obtain ⟨A, T, hA, hT⟩ := hs
  exact ⟨A, _, hA, hT⟩

theorem SB_subset_MB : SB Y ⊆ MB Y := fun _ h => by
  simp only [SB, MB, Set.mem_ofPred_eq] at h ⊢; exact Solvable.mono (fun _ h => ⟨h.1.isMultiset, h.2⟩) h
theorem MB_subset_VB : MB Y ⊆ VB Y := fun _ h => by
  simp only [MB, VB, Set.mem_ofPred_eq] at h ⊢; exact Solvable.mono (fun _ h => h.2) h
theorem MB_subset_MV : MB Y ⊆ MV Y := fun _ h => by
  simp only [MB, MV, Set.mem_ofPred_eq] at h ⊢; exact Solvable.mono (fun _ h => h.1) h
theorem SB_subset_SV : SB Y ⊆ SV Y := fun _ h => by
  simp only [SB, SV, Set.mem_ofPred_eq] at h ⊢; exact Solvable.mono (fun _ h => h.1) h
theorem SV_subset_MV : SV Y ⊆ MV Y := fun _ h => by
  simp only [SV, MV, Set.mem_ofPred_eq] at h ⊢; exact Solvable.mono (fun _ h => h.isMultiset) h
theorem MV_subset_VV : MV Y ⊆ VV Y := fun _ h => by
  simp only [MV, VV, Set.mem_ofPred_eq] at h ⊢; exact Solvable.mono (fun _ _ => trivial) h
theorem VB_subset_VV : VB Y ⊆ VV Y := fun _ h => by
  simp only [VB, VV, Set.mem_ofPred_eq] at h ⊢; exact Solvable.mono (fun _ _ => trivial) h
theorem VV_subset_VVc : VV Y ⊆ VVc Y := fun _ ⟨A, T, _, h⟩ => ⟨A, T, h.solvesInC⟩

theorem SB1_subset_MB1 : SB1 Y ⊆ MB1 Y := fun _ h => by
  simp only [SB1, MB1, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.mono (fun _ h => ⟨h.1.isMultiset, h.2⟩) h
theorem MB1_subset_VB1 : MB1 Y ⊆ VB1 Y := fun _ h => by
  simp only [MB1, VB1, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.mono (fun _ h => h.2) h
theorem MB1_subset_MV1 : MB1 Y ⊆ MV1 Y := fun _ h => by
  simp only [MB1, MV1, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.mono (fun _ h => h.1) h
theorem SB1_subset_SV1 : SB1 Y ⊆ SV1 Y := fun _ h => by
  simp only [SB1, SV1, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.mono (fun _ h => h.1) h
theorem SV1_subset_MV1 : SV1 Y ⊆ MV1 Y := fun _ h => by
  simp only [SV1, MV1, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.mono (fun _ h => h.isMultiset) h
theorem MV1_subset_VV1 : MV1 Y ⊆ VV1 Y := fun _ h => by
  simp only [MV1, VV1, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.mono (fun _ _ => trivial) h
theorem VB1_subset_VV1 : VB1 Y ⊆ VV1 Y := fun _ h => by
  simp only [VB1, VV1, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.mono (fun _ _ => trivial) h
theorem VV1_subset_VVc1 : VV1 Y ⊆ VVc1 Y := fun _ ⟨A, T, _, h⟩ => ⟨A, T, h.solvesInC⟩

theorem VVc1_subset_VVc : VVc1 Y ⊆ VVc Y := fun _ ⟨A, T, h⟩ => ⟨A, _, h⟩
theorem VV1_subset_VV : VV1 Y ⊆ VV Y := fun _ h => by
  simp only [VV1, VV, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.solvable h
theorem MV1_subset_MV : MV1 Y ⊆ MV Y := fun _ h => by
  simp only [MV1, MV, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.solvable h
theorem SV1_subset_SV : SV1 Y ⊆ SV Y := fun _ h => by
  simp only [SV1, SV, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.solvable h
theorem VB1_subset_VB : VB1 Y ⊆ VB Y := fun _ h => by
  simp only [VB1, VB, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.solvable h
theorem MB1_subset_MB : MB1 Y ⊆ MB Y := fun _ h => by
  simp only [MB1, MB, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.solvable h
theorem SB1_subset_SB : SB1 Y ⊆ SB Y := fun _ h => by
  simp only [SB1, SB, Set.mem_ofPred_eq] at h ⊢; exact Solvable1.solvable h

end Podc.WeakModelsModalLogic
