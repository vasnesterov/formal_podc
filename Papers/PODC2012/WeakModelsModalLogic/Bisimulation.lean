import Papers.PODC2012.WeakModelsModalLogic.Model

/-!
# Kripke models `K_{a,b}(G, p)`, bisimulation, and Corollary 3 (§4 of Hella et al.)

For a port numbering `p` of `G` the paper defines accessibility relations
`R(i,j) = {(u, v) : p((v, j)) = (u, i)}` (`u` receives from `v` on in-port `i`, sent by `v` to its
out-port `j`), `R(i,*) = ⋃ⱼ R(i,j)` and `R(*,*) = ⋃ R(i,j) = E`, and the valuation
`τ(qᵢ) = {v : deg v = i}`. We only need bisimulations of a model with itself:

* `IsBisimPP P Z`: `Z` is a bisimulation of `K_{+,+}(G, p)`;
* `IsBisimPM P Z`: `Z` is a bisimulation of `K_{+,-}(G, p)`;
* `IsBisimMM G Z`: `Z` is a bisimulation of `K_{-,-}(G, p)` (independent of `p`).

Condition (B1) (agreement on all `qᵢ`, `i ∈ [Δ]`) is stated as `deg v = deg v'`; for graphs in
`F(Δ)` the two are equivalent.

Instead of going through the modal-logic characterisation (Theorem 2) and Fact 1, we prove
directly that bisimilar nodes run through identical states for every algorithm of the
corresponding class (`state_eq_of_bisimPP`, `…PM`, `…MM`); Corollary 3 (`cor3a`, `cor3b`,
`cor3c`) follows.
-/

namespace Podc.WeakModelsModalLogic

open Function

variable {V : Type*} {G : SimpleGraph V}

theorem port_eq_iff (x : Port G) (u : V) (i : ℕ) (hi : i < deg G u) :
    x = ⟨u, ⟨i, hi⟩⟩ ↔ x.1 = u ∧ (x.2 : ℕ) = i := by
  obtain ⟨w, j⟩ := x
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    simp only at h1 h2
    subst h1
    subst h2
    rfl

namespace PortNumbering

variable (P : PortNumbering G)

/-- `R(i,j) = {(u, v) : p((v, j)) = (u, i)}`. -/
def R (i j : ℕ) (u v : V) : Prop :=
  ∃ (hj : j < deg G v) (hi : i < deg G u), P.p ⟨v, ⟨j, hj⟩⟩ = ⟨u, ⟨i, hi⟩⟩

/-- `R(i,*) = ⋃ⱼ R(i,j)`. -/
def Rin (i : ℕ) (u v : V) : Prop := ∃ j, P.R i j u v

theorem R_iff (i j : ℕ) (u v : V) :
    P.R i j u v ↔ ∃ hi : i < deg G u, (P.p.symm ⟨u, ⟨i, hi⟩⟩).1 = v ∧
      ((P.p.symm ⟨u, ⟨i, hi⟩⟩).2 : ℕ) = j := by
  constructor
  · rintro ⟨hj, hi, h⟩
    refine ⟨hi, ?_⟩
    rw [← h, Equiv.symm_apply_apply]
    exact ⟨rfl, rfl⟩
  · rintro ⟨hi, h1, h2⟩
    have hj : j < deg G v := by
      subst h1 h2; exact (P.p.symm ⟨u, ⟨i, hi⟩⟩).2.2
    refine ⟨hj, hi, ?_⟩
    rw [← Equiv.eq_symm_apply, eq_comm, port_eq_iff]
    exact ⟨h1, h2⟩

/-- The sender of in-port `i` of `u` is related to `u` by `R(i, j)`. -/
theorem R_symm_apply (u : V) (i : ℕ) (hi : i < deg G u) :
    P.R i (P.p.symm ⟨u, ⟨i, hi⟩⟩).2 u (P.p.symm ⟨u, ⟨i, hi⟩⟩).1 :=
  (P.R_iff _ _ _ _).2 ⟨hi, rfl, rfl⟩

theorem R_adj {i j : ℕ} {u v : V} (h : P.R i j u v) : G.Adj u v := by
  obtain ⟨hj, hi, h⟩ := h
  have := P.adj ⟨v, ⟨j, hj⟩⟩
  rw [h] at this
  exact this.symm

/-- `R(*,*)` is the edge set: every edge carries some `R(i,j)`. -/
theorem exists_R_of_adj {u v : V} (h : G.Adj u v) : ∃ i j, P.R i j u v := by
  obtain ⟨i, hi⟩ := P.inNbr_surj u v h
  exact ⟨i, _, (P.R_iff _ _ _ _).2 ⟨i.2, hi, rfl⟩⟩

/-- `Z` is a bisimulation of `K_{+,+}(G, p)` with itself. -/
def IsBisimPP (Z : V → V → Prop) : Prop :=
  ∀ v v', Z v v' → deg G v = deg G v' ∧
    (∀ i j w, P.R i j v w → ∃ w', P.R i j v' w' ∧ Z w w') ∧
    (∀ i j w', P.R i j v' w' → ∃ w, P.R i j v w ∧ Z w w')

/-- `Z` is a bisimulation of `K_{+,-}(G, p)` with itself. -/
def IsBisimPM (Z : V → V → Prop) : Prop :=
  ∀ v v', Z v v' → deg G v = deg G v' ∧
    (∀ i w, P.Rin i v w → ∃ w', P.Rin i v' w' ∧ Z w w') ∧
    (∀ i w', P.Rin i v' w' → ∃ w, P.Rin i v w ∧ Z w w')

/-- `u` and `v` are bisimilar in `K_{+,+}(G, p)`. -/
def BisimilarPP (u v : V) : Prop := ∃ Z, P.IsBisimPP Z ∧ Z u v

/-- `u` and `v` are bisimilar in `K_{+,-}(G, p)`. -/
def BisimilarPM (u v : V) : Prop := ∃ Z, P.IsBisimPM Z ∧ Z u v

end PortNumbering

/-- `Z` is a bisimulation of `K_{-,-}(G, p)` with itself (the only relation is `R(*,*) = E`). -/
def IsBisimMM (G : SimpleGraph V) (Z : V → V → Prop) : Prop :=
  ∀ v v', Z v v' → deg G v = deg G v' ∧
    (∀ w, G.Adj v w → ∃ w', G.Adj v' w' ∧ Z w w') ∧
    (∀ w', G.Adj v' w' → ∃ w, G.Adj v w ∧ Z w w')

/-- `u` and `v` are bisimilar in `K_{-,-}(G, p)`. -/
def BisimilarMM (G : SimpleGraph V) (u v : V) : Prop := ∃ Z, IsBisimMM G Z ∧ Z u v

namespace Machine

variable {Δ : ℕ} {Y : Type} (A : Machine Δ Y) (P : PortNumbering G)

/-- The message received on in-port `i` of `u` from `w` (which sent it to its port `j`). -/
theorem recv_eq_of_R (x : V → Y ⊕ A.Z) {u w : V} (i : Fin Δ) {j : ℕ} (hR : P.R i j u w) :
    A.recv G P x u i = A.send (x w) j := by
  obtain ⟨hj, hi, h⟩ := hR
  have e : P.p.symm ⟨u, ⟨i, hi⟩⟩ = ⟨w, ⟨j, hj⟩⟩ := by rw [← h, Equiv.symm_apply_apply]
  simp only [recv, dif_pos hi]
  rw [e]

theorem recv_eq_m0 (x : V → Y ⊕ A.Z) {u : V} (i : Fin Δ) (hi : ¬ (i : ℕ) < deg G u) :
    A.recv G P x u i = A.m0 := by
  simp [recv, hi]

/-- Nodes that are bisimilar in `K_{+,+}(G, p)` run through the same states, for every
algorithm (class `Vector`). -/
theorem state_eq_of_bisimPP {Z : V → V → Prop} (hZ : P.IsBisimPP Z) :
    ∀ t v v', Z v v' → A.state G P t v = A.state G P t v' := by
  intro t
  induction t with
  | zero => intro v v' h; simp [state_zero, init, (hZ v v' h).1]
  | succ t ih =>
    intro v v' h
    obtain ⟨hdeg, hB2, -⟩ := hZ v v' h
    rw [state_succ]
    simp only [step]
    rw [ih v v' h]
    congr 1
    funext i
    by_cases hi : (i : ℕ) < deg G v
    · obtain ⟨w', hw', hZw⟩ := hB2 _ _ _ (P.R_symm_apply v i hi)
      rw [A.recv_eq_of_R P _ i (P.R_symm_apply v i hi), A.recv_eq_of_R P _ i hw', ih _ _ hZw]
    · have hi' : ¬ (i : ℕ) < deg G v' := hdeg ▸ hi
      rw [A.recv_eq_m0 P _ i hi, A.recv_eq_m0 P _ i hi']

theorem send_broadcast (hA : A.IsBroadcast) (s : Y ⊕ A.Z) {i j : ℕ} (hi : i < Δ) (hj : j < Δ) :
    A.send s i = A.send s j := by
  cases s with
  | inl _ => rfl
  | inr z => exact hA z i j hi hj

/-- Nodes that are bisimilar in `K_{+,-}(G, p)` run through the same states, for every
algorithm in `Broadcast`. -/
theorem state_eq_of_bisimPM (hA : A.IsBroadcast) (hG : MaxDegLE G Δ) {Z : V → V → Prop}
    (hZ : P.IsBisimPM Z) :
    ∀ t v v', Z v v' → A.state G P t v = A.state G P t v' := by
  intro t
  induction t with
  | zero => intro v v' h; simp [state_zero, init, (hZ v v' h).1]
  | succ t ih =>
    intro v v' h
    obtain ⟨hdeg, hB2, -⟩ := hZ v v' h
    rw [state_succ]
    simp only [step]
    rw [ih v v' h]
    congr 1
    funext i
    by_cases hi : (i : ℕ) < deg G v
    · obtain ⟨w', ⟨j', hw'⟩, hZw⟩ := hB2 _ _ ⟨_, P.R_symm_apply v i hi⟩
      rw [A.recv_eq_of_R P _ i (P.R_symm_apply v i hi), A.recv_eq_of_R P _ i hw', ih _ _ hZw]
      apply send_broadcast A hA
      · exact lt_of_lt_of_le (P.p.symm ⟨v, ⟨i, hi⟩⟩).2.2 (hG _)
      · obtain ⟨hj, -, -⟩ := hw'
        exact lt_of_lt_of_le hj (hG _)
    · have hi' : ¬ (i : ℕ) < deg G v' := hdeg ▸ hi
      rw [A.recv_eq_m0 P _ i hi, A.recv_eq_m0 P _ i hi']

theorem range_recv_subset (hA : A.IsBroadcast) (hG : MaxDegLE G Δ) (x : V → Y ⊕ A.Z)
    {v v' : V} (hdeg : deg G v = deg G v')
    (hB : ∀ w, G.Adj v w → ∃ w', G.Adj v' w' ∧ x w = x w') :
    Set.range (A.recv G P x v) ⊆ Set.range (A.recv G P x v') := by
  rintro _ ⟨i, rfl⟩
  by_cases hi : (i : ℕ) < deg G v
  · obtain ⟨w', hw', hxw⟩ := hB _ (P.adj_inNbr v ⟨i, hi⟩)
    obtain ⟨i', hi'⟩ := P.inNbr_surj v' w' hw'
    refine ⟨⟨i', lt_of_lt_of_le i'.2 (hG v')⟩, ?_⟩
    rw [A.recv_eq_of_R P _ ⟨i', _⟩ (P.R_symm_apply v' i' i'.2),
      A.recv_eq_of_R P _ i (P.R_symm_apply v i hi)]
    have e1 : x (P.p.symm ⟨v', ⟨i', i'.2⟩⟩).1 = x w' := by rw [← hi']; rfl
    have e2 : x (P.p.symm ⟨v, ⟨i, hi⟩⟩).1 = x w' := hxw
    rw [e1, e2]
    apply send_broadcast A hA
    · exact lt_of_lt_of_le (P.p.symm ⟨v', ⟨i', i'.2⟩⟩).2.2 (hG _)
    · exact lt_of_lt_of_le (P.p.symm ⟨v, ⟨i, hi⟩⟩).2.2 (hG _)
  · have hi' : ¬ (i : ℕ) < deg G v' := hdeg ▸ hi
    exact ⟨i, by rw [A.recv_eq_m0 P _ i hi, A.recv_eq_m0 P _ i hi']⟩

/-- Nodes that are bisimilar in `K_{-,-}(G, p)` run through the same states, for every
algorithm in `Set ∩ Broadcast`. -/
theorem state_eq_of_bisimMM (hS : A.IsSet) (hA : A.IsBroadcast) (hG : MaxDegLE G Δ)
    {Z : V → V → Prop} (hZ : IsBisimMM G Z) :
    ∀ t v v', Z v v' → A.state G P t v = A.state G P t v' := by
  intro t
  induction t with
  | zero => intro v v' h; simp [state_zero, init, (hZ v v' h).1]
  | succ t ih =>
    intro v v' h
    obtain ⟨hdeg, hB2, hB3⟩ := hZ v v' h
    rw [state_succ]
    simp only [step]
    rw [ih v v' h]
    cases hx : A.state G P t v' with
    | inl y => rfl
    | inr z =>
      simp only [update_inr]
      apply hS
      apply le_antisymm
      · exact A.range_recv_subset P hA hG _ hdeg
          (fun w hw => (hB2 w hw).imp fun w' hw' => ⟨hw'.1, ih _ _ hw'.2⟩)
      · exact A.range_recv_subset P hA hG _ hdeg.symm
          (fun w' hw' => (hB3 w' hw').imp fun w hw => ⟨hw.1, (ih _ _ hw.2).symm⟩)

end Machine

/-! ### Corollary 3 -/

variable {Y : Type}

/-- Corollary 3 (a). If some port numbering makes all nodes of `X` bisimilar in `K_{+,+}(G, p)`
and every solution of `Π(G)` distinguishes two nodes of `X`, then `Π ∉ VV`. -/
theorem cor3a {V : Type} [Finite V] (G : SimpleGraph V) (Δ : ℕ) (hG : MaxDegLE G Δ)
    (X : Set V) (Pr : GraphProblem Y) (hPr : ∀ S ∈ Pr G, ∃ u ∈ X, ∃ v ∈ X, S u ≠ S v)
    (P : PortNumbering G) (hX : ∀ u ∈ X, ∀ v ∈ X, P.BisimilarPP u v) : Pr ∉ VV Y := by
  rintro ⟨A, T, -, hA⟩
  obtain ⟨S, hS, hSP⟩ := hA Δ V G hG P
  obtain ⟨u, hu, v, hv, hne⟩ := hPr S hSP
  obtain ⟨Z, hZ, huv⟩ := hX u hu v hv
  have := (A Δ).state_eq_of_bisimPP P hZ (T Δ (Nat.card V)) u v huv
  rw [hS u, hS v] at this
  exact hne (Sum.inl_injective this)

/-- Corollary 3 (b). The same with `K_{+,-}(G, p)` and `VB`. -/
theorem cor3b {V : Type} [Finite V] (G : SimpleGraph V) (Δ : ℕ) (hG : MaxDegLE G Δ)
    (X : Set V) (Pr : GraphProblem Y) (hPr : ∀ S ∈ Pr G, ∃ u ∈ X, ∃ v ∈ X, S u ≠ S v)
    (P : PortNumbering G) (hX : ∀ u ∈ X, ∀ v ∈ X, P.BisimilarPM u v) : Pr ∉ VB Y := by
  rintro ⟨A, T, hB, hA⟩
  obtain ⟨S, hS, hSP⟩ := hA Δ V G hG P
  obtain ⟨u, hu, v, hv, hne⟩ := hPr S hSP
  obtain ⟨Z, hZ, huv⟩ := hX u hu v hv
  have := (A Δ).state_eq_of_bisimPM P (hB Δ) hG hZ (T Δ (Nat.card V)) u v huv
  rw [hS u, hS v] at this
  exact hne (Sum.inl_injective this)

/-- Corollary 3 (c). The same with `K_{-,-}(G, p)` and `SB`. (Bisimilarity in `K_{-,-}` does
not depend on `p`, but a port numbering must exist; it always does, see `Lemma15.lean`.) -/
theorem cor3c {V : Type} [Finite V] (G : SimpleGraph V) (Δ : ℕ) (hG : MaxDegLE G Δ)
    (X : Set V) (Pr : GraphProblem Y) (hPr : ∀ S ∈ Pr G, ∃ u ∈ X, ∃ v ∈ X, S u ≠ S v)
    (P : PortNumbering G) (hX : ∀ u ∈ X, ∀ v ∈ X, BisimilarMM G u v) : Pr ∉ SB Y := by
  rintro ⟨A, T, hB, hA⟩
  obtain ⟨S, hS, hSP⟩ := hA Δ V G hG P
  obtain ⟨u, hu, v, hv, hne⟩ := hPr S hSP
  obtain ⟨Z, hZ, huv⟩ := hX u hu v hv
  have := (A Δ).state_eq_of_bisimMM P (hB Δ).1 (hB Δ).2 hG hZ (T Δ (Nat.card V)) u v huv
  rw [hS u, hS v] at this
  exact hne (Sum.inl_injective this)

end Podc.WeakModelsModalLogic
