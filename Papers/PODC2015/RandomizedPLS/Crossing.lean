import Papers.PODC2015.RandomizedPLS.Basic

/-!
# The crossing of two copies (Definition 4.2) and what nodes see after crossing

`Copies.cross K i j hij` is the configuration obtained from `c` by replacing every pair of edges
`{u, v}` of copy `i` and `{σ u, σ v}` of copy `j` by `{u, σ v}` and `{σ u, v}`, where
`σ = emb j ∘ (emb i)⁻¹`. Port numbers are kept: the new neighbour sits at the port of the old one.

* `cross_nbrs_map_eq`: if the labels agree on the two copies, every node sees the same labels at
  every port in `c` and in the crossing (the heart of Proposition 4.3).
* `cross_received`: in the crossing, the node at port `q` of `x` sends the certificate of its port
  towards `x`, which is the port of the original neighbour towards `x` (port preservation).
-/

namespace Podc.RandomizedPLS

open Classical

namespace Copies

variable {S : Type} {c : Config S} {r : ℕ} (K : Copies c r)

lemma adj_of_isArc {i j : Fin r} {x w : c.V} (h : K.IsArc i j x w) : c.Adj x w := by
  obtain ⟨k, -, a, b, hab, rfl, rfl⟩ := h
  exact K.hom k a b hab

/-- Unfolding an arc: it lies in copy `i` or in copy `j`. -/
lemma isArc_cases {i j : Fin r} (hij : i ≠ j) {x w : c.V} (h : K.IsArc i j x w) :
    ∃ a b, K.H.Adj a b ∧ ((K.emb i a = x ∧ K.emb i b = w ∧ K.newNbr i j x w = K.emb j b) ∨
      (K.emb j a = x ∧ K.emb j b = w ∧ K.newNbr i j x w = K.emb i b)) := by
  obtain ⟨k, hk, a, b, hab, hx, hw⟩ := id h
  refine ⟨a, b, hab, ?_⟩
  rcases hk with rfl | rfl
  · left; refine ⟨hx, hw, ?_⟩
    rw [newNbr, ite_eq_left h, ← hw, swap_emb_left]
  · right; refine ⟨hx, hw, ?_⟩
    rw [newNbr, ite_eq_left h, ← hw, swap_emb_right K hij]

lemma newNbr_of_not_isArc {i j : Fin r} {x w : c.V} (h : ¬ K.IsArc i j x w) :
    K.newNbr i j x w = w := by
  rw [newNbr, ite_eq_right h]

/-- The new neighbour along an arc of copy `i` or `j` is the sibling in the other copy. -/
lemma newNbr_emb {i j : Fin r} (hij : i ≠ j) {k : Fin r} (hk : k = i ∨ k = j) {a b : K.W}
    (hab : K.H.Adj a b) :
    K.newNbr i j (K.emb k a) (K.emb k b) = K.emb (if k = i then j else i) b := by
  have harc : K.IsArc i j (K.emb k a) (K.emb k b) := ⟨k, hk, a, b, hab, rfl, rfl⟩
  rw [newNbr, ite_eq_left harc]
  rcases hk with rfl | rfl
  · rw [ite_eq_left rfl, swap_emb_left]
  · rw [ite_eq_right (Ne.symm hij), swap_emb_right K hij]

/-- Only nodes of copies `i` and `j` get new neighbours. -/
lemma newNbr_of_not_mem {i j : Fin r} {x w : c.V} (hx : ∀ a, K.emb i a ≠ x ∧ K.emb j a ≠ x) :
    K.newNbr i j x w = w := by
  apply newNbr_of_not_isArc
  rintro ⟨k, hk, a, b, -, hxa, -⟩
  rcases hk with rfl | rfl
  · exact (hx a).1 hxa
  · exact (hx a).2 hxa

lemma newNbr_injOn {i j : Fin r} (hij : i ≠ j) (x : c.V) {w₁ w₂ : c.V} (h₁ : w₁ ∈ c.nbrs x)
    (h₂ : w₂ ∈ c.nbrs x) (h : K.newNbr i j x w₁ = K.newNbr i j x w₂) : w₁ = w₂ := by
  by_cases a₁ : K.IsArc i j x w₁ <;> by_cases a₂ : K.IsArc i j x w₂
  · obtain ⟨a, b, -, H1⟩ := K.isArc_cases hij a₁
    obtain ⟨a', b', -, H2⟩ := K.isArc_cases hij a₂
    rcases H1 with ⟨hx, hw, hn⟩ | ⟨hx, hw, hn⟩ <;>
      rcases H2 with ⟨hx', hw', hn'⟩ | ⟨hx', hw', hn'⟩ <;> rw [hn, hn'] at h
    · rw [← hw, ← hw', K.inj j h]
    · exact absurd (hx.trans hx'.symm) (K.disj _ _ _ _ hij)
    · exact absurd (hx'.trans hx.symm) (K.disj _ _ _ _ hij)
    · rw [← hw, ← hw', K.inj i h]
  · exfalso
    rw [K.newNbr_of_not_isArc a₂] at h
    obtain ⟨a, b, -, H1⟩ := K.isArc_cases hij a₁
    rcases H1 with ⟨hx, -, hn⟩ | ⟨hx, -, hn⟩ <;> rw [hn] at h <;> subst h <;> rw [← hx] at h₂
    · exact K.indep i j a b hij h₂
    · exact K.indep j i a b (Ne.symm hij) h₂
  · exfalso
    rw [K.newNbr_of_not_isArc a₁] at h
    obtain ⟨a, b, -, H1⟩ := K.isArc_cases hij a₂
    rcases H1 with ⟨hx, -, hn⟩ | ⟨hx, -, hn⟩ <;> rw [hn] at h <;> subst h <;> rw [← hx] at h₁
    · exact K.indep i j a b hij h₁
    · exact K.indep j i a b (Ne.symm hij) h₁
  · rwa [K.newNbr_of_not_isArc a₁, K.newNbr_of_not_isArc a₂] at h

lemma newNbr_ne_self {i j : Fin r} (hij : i ≠ j) {x w : c.V} (hw : w ∈ c.nbrs x) :
    K.newNbr i j x w ≠ x := by
  by_cases a : K.IsArc i j x w
  · obtain ⟨a', b, -, H1⟩ := K.isArc_cases hij a
    rcases H1 with ⟨hx, -, hn⟩ | ⟨hx, -, hn⟩ <;> rw [hn, ← hx]
    · exact K.disj j i b a' (Ne.symm hij)
    · exact K.disj i j b a' hij
  · rw [K.newNbr_of_not_isArc a]
    rintro rfl
    exact c.loopless _ hw

/-- The new neighbour of the new neighbour is the node itself. -/
lemma newNbr_newNbr {i j : Fin r} (hij : i ≠ j) {x w : c.V} (hw : w ∈ c.nbrs x) :
    ∃ x' ∈ c.nbrs (K.newNbr i j x w), K.newNbr i j (K.newNbr i j x w) x' = x ∧
      c.port (K.newNbr i j x w) x' = c.port w x := by
  by_cases a : K.IsArc i j x w
  · obtain ⟨a', b, hab, H1⟩ := K.isArc_cases hij a
    rcases H1 with ⟨hx, hw', hn⟩ | ⟨hx, hw', hn⟩ <;> rw [hn]
    · refine ⟨K.emb j a', K.hom j b a' hab.symm, ?_, ?_⟩
      · have : K.IsArc i j (K.emb j b) (K.emb j a') := ⟨j, Or.inr rfl, b, a', hab.symm, rfl, rfl⟩
        rw [newNbr, ite_eq_left this, swap_emb_right K hij, hx]
      · rw [← hx, ← hw', K.port_eq j i b a' hab.symm]
    · refine ⟨K.emb i a', K.hom i b a' hab.symm, ?_, ?_⟩
      · have : K.IsArc i j (K.emb i b) (K.emb i a') := ⟨i, Or.inl rfl, b, a', hab.symm, rfl, rfl⟩
        rw [newNbr, ite_eq_left this, swap_emb_left, hx]
      · rw [← hx, ← hw', K.port_eq i j b a' hab.symm]
  · rw [K.newNbr_of_not_isArc a]
    refine ⟨x, c.symm _ _ hw, ?_, rfl⟩
    exact K.newNbr_of_not_isArc fun h => a (K.isArc_symm h)

/-- The crossing `σ₁(G)` of copies `i` and `j` (Definition 4.2), with the same states. -/
@[reducible] noncomputable def cross (i j : Fin r) (hij : i ≠ j) : Config S where
  V := c.V
  nbrs x := (c.nbrs x).map (K.newNbr i j x)
  nodup x := (c.nodup x).map_on fun _ h₁ _ h₂ h => K.newNbr_injOn hij x h₁ h₂ h
  loopless x h := by
    obtain ⟨w, hw, he⟩ := List.mem_map.1 h
    exact K.newNbr_ne_self hij hw he
  symm x y h := by
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
    obtain ⟨x', hx', he, -⟩ := K.newNbr_newNbr hij hw
    exact List.mem_map.2 ⟨x', hx', he⟩
  state := c.state
  deg := c.deg
  deg_eq x := by rw [List.length_map, c.deg_eq]

variable {K}


lemma _root_.Podc.RandomizedPLS.idxOf_map_injOn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (l : List α) (hinj : ∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) {x : α} (hx : x ∈ l) :
    (l.map f).idxOf (f x) = l.idxOf x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    by_cases hy : y = x
    · subst hy; simp
    · have hne : f y ≠ f x := fun h => hy (hinj _ (by simp) _ hx h)
      rw [List.map_cons, List.idxOf_cons_ne _ hne, List.idxOf_cons_ne _ hy]
      exact congrArg (· + 1) (ih (fun a ha b hb => hinj a (by simp [ha]) b (by simp [hb]))
        ((List.mem_cons.1 hx).resolve_left (Ne.symm hy)))

@[simp] lemma cross_V (i j : Fin r) (hij : i ≠ j) : (K.cross i j hij).V = c.V := rfl

lemma cross_nbrs (i j : Fin r) (hij : i ≠ j) (x : c.V) :
    (K.cross i j hij).nbrs x = (c.nbrs x).map (K.newNbr i j x) := rfl

@[simp] lemma cross_state (i j : Fin r) (hij : i ≠ j) : (K.cross i j hij).state = c.state := rfl

@[simp] lemma cross_deg (i j : Fin r) (hij : i ≠ j) : (K.cross i j hij).deg = c.deg := rfl

/-- If a function agrees on copies `i` and `j`, it is invariant under the new-neighbour map. -/
lemma comp_newNbr {α : Type*} {i j : Fin r} (hij : i ≠ j) (ℓ : c.V → α)
    (hℓ : ∀ a b, K.H.Adj a b → ℓ (K.emb i a) = ℓ (K.emb j a)) (x w : c.V) : ℓ (K.newNbr i j x w) = ℓ w := by
  by_cases a : K.IsArc i j x w
  · obtain ⟨a', b, hab, H1⟩ := K.isArc_cases hij a
    have hba := hab.symm
    rcases H1 with ⟨-, hw, hn⟩ | ⟨-, hw, hn⟩ <;> rw [hn, ← hw]
    · exact (hℓ b a' (by assumption)).symm
    · exact hℓ b a' (by assumption)
  · rw [K.newNbr_of_not_isArc a]

/-- **Core of Proposition 4.3.** If the labels agree on copies `i` and `j`, then every node sees
the same labels at every port in `c` and in the crossing. -/
lemma cross_nbrs_map_eq {α : Type*} {i j : Fin r} (hij : i ≠ j) (ℓ : c.V → α)
    (hℓ : ∀ a b, K.H.Adj a b → ℓ (K.emb i a) = ℓ (K.emb j a)) (x : c.V) :
    ((K.cross i j hij).nbrs x).map ℓ = (c.nbrs x).map ℓ := by
  rw [cross_nbrs, List.map_map]
  exact List.map_congr_left fun w _ => K.comp_newNbr hij ℓ hℓ x w

/-- A deterministic verifier accepts `c` iff it accepts the crossing, when the labels agree on the
two crossed copies. -/
lemma accepts_cross_iff {ver : Verifier S} {i j : Fin r} (hij : i ≠ j) (ℓ : c.V → List Bool)
    (hℓ : ∀ a b, K.H.Adj a b → ℓ (K.emb i a) = ℓ (K.emb j a)) :
    Accepts ver (K.cross i j hij) ℓ ↔ Accepts ver c ℓ := by
  unfold Accepts
  refine forall_congr' fun (x : c.V) => ?_
  change ver (c.state x) (ℓ x) (((K.cross i j hij).nbrs x).map ℓ) = true ↔ _
  rw [K.cross_nbrs_map_eq hij ℓ hℓ x]

/-- In the crossing, the port of `x` at the new neighbour replacing `w` equals the port of `x` at
`w` in `c` (port preservation). -/
lemma cross_port_newNbr {i j : Fin r} (hij : i ≠ j) {x w : c.V} (hw : w ∈ c.nbrs x) :
    (K.cross i j hij).port (K.newNbr i j x w) x = c.port w x := by
  obtain ⟨x', hx', he, hp⟩ := K.newNbr_newNbr hij hw
  have := idxOf_map_injOn (K.newNbr i j (K.newNbr i j x w)) (c.nbrs (K.newNbr i j x w))
    (fun a ha b hb h => K.newNbr_injOn hij _ ha hb h) hx'
  rw [he] at this
  exact this.trans hp

/-- The certificates received in the crossing: at the port of `x` where `w` was, `x` now receives
from the new neighbour the certificate of the same port number that `w` used towards `x`. -/
lemma cross_received {L : Type} (σ : RScheme S L) {i j : Fin r} (hij : i ≠ j) (ℓ : c.V → L)
    (ω : σ.Coins c ℓ) (x : c.V) :
    σ.received (K.cross i j hij) ℓ ω x =
      (c.nbrs x).map fun w => σ.sent c ℓ ω (K.newNbr i j x w) (c.port w x) := by
  change ((c.nbrs x).map (K.newNbr i j x)).map
    (fun y => σ.sent c ℓ ω y ((K.cross i j hij).port y x)) = _
  rw [List.map_map]
  exact List.map_congr_left fun w hw => by
    simp only [Function.comp_apply, K.cross_port_newNbr hij hw]

end Copies

end Podc.RandomizedPLS
