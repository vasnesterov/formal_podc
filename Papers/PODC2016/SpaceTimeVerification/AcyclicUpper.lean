import Papers.PODC2016.SpaceTimeVerification.AcyclicLabels

/-!
# The upper bound for acyclicity (Section 4.2): Lemma 17, Theorem 8

*Space-Time Tradeoffs for Distributed Verification* (Ostrovsky, Perry, Rosenbaum;
arXiv:1605.06814), Section 4.2.

* `Check t G ℓ v`: the verifier's decision at `v`. It replaces Algorithm 1 (`Verify`): instead of
  simulating the message-passing algorithm round by round, we state directly the predicate on the
  labelled radius-`t` ball of `v` that Algorithm 1 decides (the proof of Lemma 17 shows that the
  algorithm accepts iff these conditions hold). Every node checks orientation and block conditions
  1–4; the tail `v` of a block `B` checks the colours and the value of `B` and of all child blocks
  of `B` (whose tails are at distance exactly `t` below `v`).
* `lemma17`: all nodes accept iff the labelling is correct (Definition 14).
* `check_transfer`: the check only depends on the labelled `t`-ball (`BallIso t`).
* `acycTPLS`, `theorem8`: a `t`-PLS for acyclicity on connected graphs with labels of
  `5 + ⌈⌈log₂ n⌉ / t⌉` bits, for every `t ≥ 2`; `theorem8_bits`: the same with labels that are
  bit strings.
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph

/-- The family of connected graphs (Definition 6). -/
abbrev acycFamily : CProp Unit := fun _ G _ => G.Connected

/-- The predicate `acyclic` (Definition 6). -/
abbrev acycPred : CProp Unit := fun _ G _ => G.IsAcyclic

/-! ### The local check and Lemma 17 -/

section Check

variable {V : Type*} (t : ℕ) (G : SimpleGraph V) (ℓ : V → AcLab)

/-- The verifier's decision at `v` (replacing Algorithm 1, see the module docstring): orientation
and block conditions 1–4 at `v`, and, for every block `B` with tail `v`, colours and value of `B`
and of the child blocks of `B`. -/
def Check (v : V) : Prop :=
  OrientAt G ℓ v ∧ HeadAt G ℓ v ∧ TailAt t G ℓ v ∧ MidAt t G ℓ v ∧ HeadNear G ℓ (· ≤ t) v ∧
    ∀ B, IsBlock t G ℓ B → B.getLast? = some v →
      (∀ x ∈ B, ∀ y ∈ B, (ℓ x).c = (ℓ y).c) ∧
      (blockVal ℓ B = 0 ↔ ∃ h ∈ B.head?, IsRoot G ℓ h) ∧
      ∀ B', IsBlock t G ℓ B' → IsParentBlock G ℓ B B' →
        (∀ x ∈ B, ∀ y ∈ B', (ℓ x).c ≠ (ℓ y).c) ∧ blockVal ℓ B' = blockVal ℓ B + t

variable {t G ℓ}

lemma exists_getLast_of_isBlock {B : List V} (hB : IsBlock t G ℓ B) : ∃ x, B.getLast? = some x := by
  obtain ⟨-, -, h, hh, -⟩ := hB
  cases B with
  | nil => simp at hh
  | cons y B => exact ⟨_, List.getLast?_eq_some_getLast (List.cons_ne_nil y B)⟩

/-- **Lemma 17** (for the local check replacing Algorithm 1): all nodes accept iff the labelling
is correct. -/
theorem lemma17 : (∀ v, Check t G ℓ v) ↔ Correct t G ℓ := by
  constructor
  · intro h
    refine ⟨fun v => (h v).1, fun v => ⟨(h v).2.1, (h v).2.2.1, (h v).2.2.2.1, (h v).2.2.2.2.1⟩,
      ⟨fun B hB => ?_, fun B B' hB hB' hp => ?_⟩, ⟨fun B hB => ?_, fun B B' hB hB' hp => ?_⟩⟩ <;>
    obtain ⟨x, hx⟩ := exists_getLast_of_isBlock hB
    · exact ((h x).2.2.2.2.2 B hB hx).1
    · exact (((h x).2.2.2.2.2 B hB hx).2.2 B' hB' hp).1
    · exact ((h x).2.2.2.2.2 B hB hx).2.1
    · exact (((h x).2.2.2.2.2 B hB hx).2.2 B' hB' hp).2
  · rintro ⟨ho, hb, hc, hd⟩ v
    exact ⟨ho v, (hb v).1, (hb v).2.1, (hb v).2.2.1, (hb v).2.2.2, fun B hB _ =>
      ⟨hc.1 B hB, hd.1 B hB, fun B' hB' hp => ⟨hc.2 B B' hB hB' hp, hd.2 B B' hB hB' hp⟩⟩⟩

end Check

/-! ### Locality of the check -/

section Transfer

/-- The data of a ball isomorphism (`BallIso`) for acyclicity labels. -/
structure LIso {V W : Type*} (t : ℕ) (G : SimpleGraph V) (ℓ : V → AcLab) (v : V)
    (G' : SimpleGraph W) (ℓ' : W → AcLab) (φ : V → W) : Prop where
  inj : ∀ a b, G.edist v a ≤ t → G.edist v b ≤ t → φ a = φ b → a = b
  lab : ∀ a, G.edist v a ≤ t → ℓ' (φ a) = ℓ a
  adj : ∀ a, G.edist v a < t → ∀ b, G.Adj a b → G'.Adj (φ a) (φ b)
  surj : ∀ a, G.edist v a < t → ∀ b', G'.Adj (φ a) b' → ∃ b, G.Adj a b ∧ φ b = b'

variable {V W : Type*} {t : ℕ} {G : SimpleGraph V} {ℓ : V → AcLab} {v : V}
  {G' : SimpleGraph W} {ℓ' : W → AcLab} {φ : V → W}

lemma edist_le_succ_of_adj {a b : V} (h : G.Adj a b) : G.edist v b ≤ G.edist v a + 1 := by
  calc G.edist v b ≤ G.edist v a + G.edist a b := G.edist_triangle
    _ = G.edist v a + 1 := by rw [edist_eq_one_iff_adj.2 h]

lemma enat_lt {e : ℕ∞} {k n : ℕ} (h : e ≤ k) (hk : k < n) : e < n :=
  h.trans_lt (by exact_mod_cast hk)

lemma enat_le {e : ℕ∞} {k n : ℕ} (h : e ≤ k) (hk : k ≤ n) : e ≤ n :=
  h.trans (by exact_mod_cast hk)

lemma enat_succ {e : ℕ∞} {k : ℕ} (h : e ≤ k) : e + 1 ≤ ((k + 1 : ℕ) : ℕ∞) := by
  push_cast; exact add_le_add h le_rfl

variable (hφ : LIso t G ℓ v G' ℓ' φ)
include hφ

lemma LIso.adj_iff {a b : V} (ha : G.edist v a < t) (hb : G.edist v b ≤ t) :
    G.Adj a b ↔ G'.Adj (φ a) (φ b) := by
  refine ⟨hφ.adj a ha b, fun h => ?_⟩
  obtain ⟨b₀, hab₀, he⟩ := hφ.surj a ha _ h
  have hb₀ : G.edist v b₀ ≤ t :=
    (edist_le_succ_of_adj hab₀).trans (Order.add_one_le_of_lt ha)
  rwa [hφ.inj b₀ b hb₀ hb he] at hab₀

lemma LIso.isPar_iff {a b : V} (ha : G.edist v a < t) (hb : G.edist v b ≤ t) :
    IsPar G ℓ a b ↔ IsPar G' ℓ' (φ a) (φ b) := by
  unfold IsPar
  rw [hφ.adj_iff ha hb, hφ.lab a ha.le, hφ.lab b hb]

lemma LIso.isPar_iff' {a b : V} (ha : G.edist v a < t) (hb : G.edist v b ≤ t) :
    IsPar G ℓ b a ↔ IsPar G' ℓ' (φ b) (φ a) := by
  unfold IsPar
  rw [G.adj_comm, G'.adj_comm, hφ.adj_iff ha hb, hφ.lab a ha.le, hφ.lab b hb]

lemma LIso.exists_par_iff {a : V} (ha : G.edist v a < t) (Q : AcLab → Prop) :
    (∃ u, IsPar G ℓ a u ∧ Q (ℓ u)) ↔ ∃ u', IsPar G' ℓ' (φ a) u' ∧ Q (ℓ' u') := by
  constructor
  · rintro ⟨u, hu, hq⟩
    have hu' : G.edist v u ≤ t := (edist_le_succ_of_adj hu.1).trans (Order.add_one_le_of_lt ha)
    exact ⟨φ u, (hφ.isPar_iff ha hu').1 hu, by rwa [hφ.lab u hu']⟩
  · rintro ⟨u', hu', hq⟩
    obtain ⟨u, hau, rfl⟩ := hφ.surj a ha _ hu'.1
    have hu : G.edist v u ≤ t := (edist_le_succ_of_adj hau).trans (Order.add_one_le_of_lt ha)
    exact ⟨u, (hφ.isPar_iff ha hu).2 hu', by rwa [← hφ.lab u hu]⟩

lemma LIso.isRoot_iff {a : V} (ha : G.edist v a < t) : IsRoot G ℓ a ↔ IsRoot G' ℓ' (φ a) := by
  have := hφ.exists_par_iff ha (fun _ => True)
  simp only [and_true] at this
  exact not_congr this

omit hφ in
/-- Chains starting near `v` are mapped to chains. -/
lemma chain_fwd {R : V → V → Prop} {R' : W → W → Prop}
    (hR : ∀ a b, G.edist v a < t → G.edist v b ≤ t → (R a b ↔ R' (φ a) (φ b)))
    (hRadj : ∀ a b, R a b → G.Adj a b) :
    ∀ (l : List V) (a : V) (k : ℕ), G.edist v a ≤ k → k + l.length ≤ t → (a :: l).IsChain R →
      ((a :: l).map φ).IsChain R' ∧ ∀ x ∈ a :: l, G.edist v x ≤ ((k + l.length : ℕ) : ℕ∞)
  | [], a, k, ha, _, _ => ⟨List.isChain_singleton _, by simpa using ha⟩
  | b :: l, a, k, ha, hk, hc => by
    rw [List.isChain_cons_cons] at hc
    have hb : G.edist v b ≤ ((k + 1 : ℕ) : ℕ∞) :=
      (edist_le_succ_of_adj (hRadj _ _ hc.1)).trans (enat_succ ha)
    simp only [List.length_cons] at hk
    obtain ⟨ih1, ih2⟩ := chain_fwd hR hRadj l b (k + 1) hb (by omega) hc.2
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.map_cons, List.isChain_cons_cons]
      exact ⟨(hR a b (enat_lt ha (by omega)) (enat_le hb (by omega))).1 hc.1, by simpa using ih1⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact enat_le ha (by simp)
      · simpa [Nat.add_assoc, Nat.add_comm 1] using ih2 x hx

/-- Chains starting near `φ v` lift to chains. -/
lemma LIso.chain_bwd {R : V → V → Prop} {R' : W → W → Prop}
    (hR : ∀ a b, G.edist v a < t → G.edist v b ≤ t → (R a b ↔ R' (φ a) (φ b)))
    (hR'adj : ∀ a b, R' a b → G'.Adj a b) :
    ∀ (l' : List W) (a : V) (k : ℕ), G.edist v a ≤ k → k + l'.length ≤ t →
      (φ a :: l').IsChain R' → ∃ l, l.map φ = l' ∧ (a :: l).IsChain R
  | [], a, _, _, _, _ => ⟨[], rfl, List.isChain_singleton _⟩
  | b' :: l', a, k, ha, hk, hc => by
    rw [List.isChain_cons_cons] at hc
    simp only [List.length_cons] at hk
    have hat : G.edist v a < t := enat_lt ha (by omega)
    obtain ⟨b, hab, rfl⟩ := hφ.surj a hat _ (hR'adj _ _ hc.1)
    have hb : G.edist v b ≤ ((k + 1 : ℕ) : ℕ∞) := (edist_le_succ_of_adj hab).trans (enat_succ ha)
    obtain ⟨l, hl, hc'⟩ := LIso.chain_bwd hR hR'adj l' b (k + 1) hb (by omega) hc.2
    exact ⟨b :: l, by simp [hl], List.isChain_cons_cons.2
      ⟨(hR a b hat (enat_le hb (by omega))).2 hc.1, hc'⟩⟩

omit hφ in
lemma isBlock_rev_iff {X : Type*} {H : SimpleGraph X} {m : X → AcLab} {a : X} {l : List X} :
    IsBlock t H m (a :: l).reverse ↔
      (a :: l).IsChain (IsPar H m) ∧ l.length + 1 = t ∧ ∃ h ∈ (a :: l).getLast?, (m h).b = .head := by
  unfold IsBlock OrientedPath
  rw [List.isChain_reverse, List.head?_reverse, List.length_reverse, List.length_cons]
  tauto

omit hφ in
lemma getLast_eq_iff {X : Type*} {B : List X} {a : X} :
    B.getLast? = some a ↔ ∃ l, B = (a :: l).reverse := by
  constructor
  · intro h
    rw [← List.head?_reverse] at h
    cases hB : B.reverse with
    | nil => simp [hB] at h
    | cons x l =>
      rw [hB] at h; cases h
      exact ⟨l, by rw [← hB, List.reverse_reverse]⟩
  · rintro ⟨l, rfl⟩; simp

omit hφ in
lemma exists_mem_option_iff {o : Option V} (P : AcLab → Prop) (hlab : ∀ x ∈ o, ℓ' (φ x) = ℓ x) :
    (∃ h ∈ o.map φ, P (ℓ' h)) ↔ ∃ h ∈ o, P (ℓ h) := by
  cases o with
  | none => simp
  | some x => simp [hlab x rfl]

omit hφ in
lemma blockVal_map {B : List V} (hlab : ∀ x ∈ B, ℓ' (φ x) = ℓ x) :
    blockVal ℓ' (B.map φ) = blockVal ℓ B := by
  unfold blockVal
  rw [List.map_map]
  congr 1
  exact List.map_congr_left fun x hx => by simp [hlab x hx]

/-- Blocks with tail `v` are mapped to blocks with tail `φ v`; their nodes are at distance `< t`. -/
lemma LIso.block_fwd {l : List V} (hB : IsBlock t G ℓ (v :: l).reverse) :
    IsBlock t G' ℓ' ((v :: l).map φ).reverse ∧ ∀ x ∈ v :: l, G.edist v x < t := by
  rw [isBlock_rev_iff] at hB
  obtain ⟨hc, hlen, hh⟩ := hB
  obtain ⟨hc', hdist⟩ := chain_fwd (v := v) (t := t) (φ := φ) (G := G) (fun a b ha hb => hφ.isPar_iff ha hb) (fun _ _ h => h.1)
    l v 0 (by simp) (by omega) hc
  have hlt : ∀ x ∈ v :: l, G.edist v x < t := fun x hx => enat_lt (hdist x hx) (by omega)
  refine ⟨?_, hlt⟩
  rw [List.map_cons, isBlock_rev_iff, List.length_map, ← List.map_cons, List.getLast?_map,
    exists_mem_option_iff (fun b => b.b = .head)
      (fun x hx => hφ.lab x (hlt x (List.mem_of_getLast? hx)).le)]
  exact ⟨by simpa using hc', hlen, hh⟩

/-- Blocks with tail `φ v` lift to blocks with tail `v`. -/
lemma LIso.block_bwd {l' : List W} (hB : IsBlock t G' ℓ' (φ v :: l').reverse) :
    ∃ l, l.map φ = l' ∧ IsBlock t G ℓ (v :: l).reverse := by
  rw [isBlock_rev_iff] at hB
  obtain ⟨hc, hlen, hh⟩ := hB
  obtain ⟨l, rfl, hcl⟩ := hφ.chain_bwd (fun a b ha hb => hφ.isPar_iff ha hb) (fun _ _ h => h.1)
    l' v 0 (by simp) (by omega) hc
  refine ⟨l, rfl, ?_⟩
  rw [isBlock_rev_iff]
  refine ⟨hcl, by simpa using hlen, ?_⟩
  obtain ⟨-, hdist⟩ := chain_fwd (v := v) (t := t) (φ := φ) (G := G) (fun a b ha hb => hφ.isPar_iff ha hb) (fun _ _ h => h.1)
    l v 0 (by simp) (by simp at hlen; omega) hcl
  rw [← exists_mem_option_iff (fun b => b.b = .head)
    (fun x hx => hφ.lab x (enat_le (hdist x (List.mem_of_getLast? hx)) (by simp at hlen; omega))),
    ← List.getLast?_map]
  simpa using hh

omit hφ in
/-- Child blocks of a block with tail `v`, as chains `v, w₀, …, w_{t-1}` going down. -/
lemma child_iff {X : Type*} {H : SimpleGraph X} {m : X → AcLab} {a : X} {l B' : List X} :
    (IsBlock t H m B' ∧ IsParentBlock H m (a :: l).reverse B') ↔
      (a :: B').IsChain (fun x y => IsPar H m y x) ∧ B'.length = t ∧
        ∃ h ∈ B'.head?, (m h).b = .head := by
  unfold IsBlock IsParentBlock OrientedPath
  rw [List.isChain_cons]
  have hl : (a :: l).reverse.getLast? = some a := by simp
  constructor
  · rintro ⟨⟨hlen, hc, hh⟩, x, hx, y, hy, hpar⟩
    rw [hl] at hx; cases hx
    exact ⟨⟨fun z hz => by rw [hy] at hz; cases hz; exact hpar, hc⟩, hlen, hh⟩
  · rintro ⟨⟨hpar, hc⟩, hlen, h, hh, hb⟩
    exact ⟨⟨hlen, hc, h, hh, hb⟩, a, hl, h, hh, hpar h hh⟩

/-- **Locality of the check**: the decision at `v` transfers along a ball isomorphism. -/
theorem LIso.check_transfer (ht : 1 ≤ t) (h : Check t G ℓ v) : Check t G' ℓ' (φ v) := by
  obtain ⟨hO, hH, hT, hM, hN, hBl⟩ := h
  have hv0 : G.edist v v < t := by simp; omega
  have hlv := hφ.lab v hv0.le
  have hnb : ∀ {a}, G.Adj v a → G.edist v a ≤ t := fun ha =>
    (edist_le_succ_of_adj ha).trans (Order.add_one_le_of_lt hv0)
  have hexB : (∃ B, IsBlock t G ℓ B ∧ B.getLast? = some v) ↔
      ∃ B, IsBlock t G' ℓ' B ∧ B.getLast? = some (φ v) := by
    simp only [getLast_eq_iff]
    constructor
    · rintro ⟨B, hB, l, rfl⟩
      exact ⟨_, (hφ.block_fwd hB).1, l.map φ, rfl⟩
    · rintro ⟨B, hB, l', rfl⟩
      obtain ⟨l, -, hl⟩ := hφ.block_bwd hB
      exact ⟨_, hl, l, rfl⟩
  have hP : (IsRoot G ℓ v ∨ ∃ u, IsPar G ℓ v u ∧ (ℓ u).b = .tail) ↔
      (IsRoot G' ℓ' (φ v) ∨ ∃ u, IsPar G' ℓ' (φ v) u ∧ (ℓ' u).b = .tail) :=
    or_congr (hφ.isRoot_iff hv0) (hφ.exists_par_iff hv0 (fun x => x.b = .tail))
  refine ⟨⟨fun u₁ u₂ h₁ h₂ => ?_, fun x' hx' hnx' => ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- orientation: unique parent
    obtain ⟨a₁, ha₁, rfl⟩ := hφ.surj v hv0 _ h₁.1
    obtain ⟨a₂, ha₂, rfl⟩ := hφ.surj v hv0 _ h₂.1
    rw [hO.1 a₁ a₂ ((hφ.isPar_iff hv0 (hnb ha₁)).2 h₁) ((hφ.isPar_iff hv0 (hnb ha₂)).2 h₂)]
  · -- orientation: children
    obtain ⟨x, hx, rfl⟩ := hφ.surj v hv0 _ hx'
    rw [hφ.lab x (hnb hx), hlv]
    exact hO.2 x hx fun hp => hnx' ((hφ.isPar_iff hv0 (hnb hx)).1 hp)
  · unfold HeadAt; rw [hlv, ← hP]; exact hH
  · unfold TailAt; rw [hlv, ← hexB]; exact hT
  · unfold MidAt; rw [hlv, ← hP, ← hexB]; exact hM
  · -- condition 4
    obtain ⟨L, hL, hlast, hlen, hh⟩ := hN
    obtain ⟨l, rfl⟩ := getLast_eq_iff.1 hlast
    have hc : (v :: l).IsChain (IsPar G ℓ) := by
      unfold OrientedPath at hL; rwa [List.isChain_reverse] at hL
    simp only [List.length_reverse, List.length_cons] at hlen
    obtain ⟨hc', hdist⟩ := chain_fwd (v := v) (t := t) (φ := φ) (G := G)
      (fun a b ha hb => hφ.isPar_iff ha hb) (fun _ _ h => h.1) l v 0 (by simp) (by omega) hc
    refine ⟨((v :: l).map φ).reverse, ?_, by simp, by simpa using hlen, ?_⟩
    · unfold OrientedPath; rw [List.isChain_reverse]; exact hc'
    · rw [List.head?_reverse, List.getLast?_map, exists_mem_option_iff (fun b => b.b = .head)
        (fun x hx => hφ.lab x (enat_le (hdist x (List.mem_of_getLast? hx)) (by omega)))]
      rwa [List.head?_reverse] at hh
  · -- blocks with tail `φ v`
    intro B' hB' hlast'
    obtain ⟨l', rfl⟩ := getLast_eq_iff.1 hlast'
    obtain ⟨l, rfl, hB⟩ := hφ.block_bwd hB'
    obtain ⟨-, hdist⟩ := hφ.block_fwd hB
    have hlab : ∀ x ∈ v :: l, ℓ' (φ x) = ℓ x := fun x hx => hφ.lab x (hdist x hx).le
    obtain ⟨hc1, hd1, hch⟩ := hBl _ hB (by simp)
    have heq : (φ v :: l.map φ).reverse = ((v :: l).reverse).map φ := by simp
    have hval : blockVal ℓ' (φ v :: l.map φ).reverse = blockVal ℓ (v :: l).reverse := by
      rw [heq, blockVal_map]
      intro x hx; exact hlab x (List.mem_reverse.1 hx)
    refine ⟨?_, ?_, ?_⟩
    · intro x' hx' y' hy'
      rw [heq] at hx' hy'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hy'
      rw [hlab x (List.mem_reverse.1 hx), hlab y (List.mem_reverse.1 hy)]
      exact hc1 x hx y hy
    · rw [hval, hd1, heq, List.head?_map]
      cases ho : (v :: l).reverse.head? with
      | none => simp
      | some x =>
        simp only [Option.map_some, Option.mem_def, Option.some.injEq, exists_eq_left']
        exact hφ.isRoot_iff (hdist x (List.mem_reverse.1 (List.mem_of_head? ho)))
    · intro C' hC' hpar'
      obtain ⟨hcC, hlenC, hhC⟩ := (child_iff (t := t)).1 ⟨hC', hpar'⟩
      obtain ⟨C, rfl, hcC0⟩ := hφ.chain_bwd (R := fun x y => IsPar G ℓ y x)
        (R' := fun x y => IsPar G' ℓ' y x) (fun a b ha hb => hφ.isPar_iff' ha hb)
        (fun _ _ h => h.1.symm) C' v 0 (by simp) (by omega) hcC
      simp only [List.length_map] at hlenC
      obtain ⟨-, hdC⟩ := chain_fwd (v := v) (t := t) (φ := φ) (G := G)
        (R' := fun x y => IsPar G' ℓ' y x) (fun a b ha hb => hφ.isPar_iff' ha hb)
        (fun _ _ h => h.1.symm) C v 0 (by simp) (by omega) hcC0
      have hlabC : ∀ x ∈ C, ℓ' (φ x) = ℓ x := fun x hx =>
        hφ.lab x (enat_le (hdC x (List.mem_cons_of_mem _ hx)) (by omega))
      have hC : IsBlock t G ℓ C ∧ IsParentBlock G ℓ (v :: l).reverse C := by
        refine (child_iff (t := t)).2 ⟨hcC0, hlenC, ?_⟩
        rwa [List.head?_map, exists_mem_option_iff (fun b => b.b = .head)
          (fun x hx => hlabC x (List.mem_of_head? hx))] at hhC
      obtain ⟨hdiff, hvalC⟩ := hch C hC.1 hC.2
      refine ⟨fun x' hx' y' hy' => ?_, by rw [blockVal_map hlabC, hval, hvalC]⟩
      rw [heq] at hx'
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hx'
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hy'
      rw [hlab x (List.mem_reverse.1 hx), hlabC y hy]
      exact hdiff x hx y hy

end Transfer

/-! ### Theorem 8 -/

section Theorem8

/-- The check transfers along `BallIso t` of the labelled configurations (the `isLocal` field). -/
theorem check_isLocal {t : ℕ} (ht : 1 ≤ t) {V W : Type} (G : SimpleGraph V) (I : V → Unit)
    (ℓ : V → AcLab) (v : V) (G' : SimpleGraph W) (I' : W → Unit) (ℓ' : W → AcLab) (w : W)
    (h : BallIso t G (fun u => (I u, ℓ u)) v G' (fun u => (I' u, ℓ' u)) w)
    (hv : Check t G ℓ v) : Check t G' ℓ' w := by
  obtain ⟨φ, rfl, hinj, hlab, hadj, hsurj⟩ := h
  exact LIso.check_transfer ⟨hinj, fun a ha => congrArg Prod.snd (hlab a ha), hadj, hsurj⟩ ht hv

/-- The `t`-PLS for acyclicity of Section 4.2 (`t ≥ 2`): the prover gives the honest labels of
the proof of Proposition 16 (share width `⌈⌈log₂ n⌉ / t⌉`), the verifier is the local check
`Check t` (it reads `t` but not `n`: share widths are read off the labels). -/
noncomputable def acycTPLS (t : ℕ) (ht : 2 ≤ t) : TPLS Unit AcLab acycFamily acycPred t where
  prove G _ := honestLabels t G
  verify G _ ℓ v := Check t G ℓ v
  isLocal G I ℓ v G' I' ℓ' w h hv := check_isLocal (by omega) G I ℓ v G' I' ℓ' w h hv
  complete G _ _ hP v := lemma17.2 (honestLabels_correct ht hP) v
  sound G _ _ ℓ h := isAcyclic_of_correct (by omega) (lemma17.1 h)

/-- Bit size of an acyclicity label: 2 bits for `a`, 2 for `b`, 1 for `c`, and `|d|`. -/
def acLabSize (x : AcLab) : ℕ := 5 + x.d.length

/-- **Theorem 8** (label size): for every `t ≥ 2` there is a `t`-PLS for acyclicity (on connected
graphs) with labels of `5 + ⌈⌈log₂ n⌉ / t⌉ = O((log n) / t)` bits on `n`-node graphs. -/
theorem theorem8 (t : ℕ) (ht : 2 ≤ t) :
    ∃ S : TPLS Unit AcLab acycFamily acycPred t,
      S.CostLE acLabSize fun n => 5 + (Nat.clog 2 n + t - 1) / t := by
  refine ⟨acycTPLS t ht, fun {V} _ G I _ _ v => ?_⟩
  simp [acycTPLS, honestLabels, honestLab, acLabSize, shareWidth, Nat.card_eq_fintype_card]

/-- Re-encoding the labels of a `t`-PLS: labels `enc x`, verifier applied to the decoded labels. -/
def TPLS.recode {ι Λ Λ' : Type} {F P : CProp ι} {t : ℕ} (S : TPLS ι Λ F P t) (enc : Λ → Λ')
    (dec : Λ' → Λ) (hdec : ∀ x, dec (enc x) = x) : TPLS ι Λ' F P t where
  prove G I v := enc (S.prove G I v)
  verify G I ℓ v := S.verify G I (dec ∘ ℓ) v
  isLocal G I ℓ v G' I' ℓ' w h hv := by
    obtain ⟨φ, h1, h2, h3, h4, h5⟩ := h
    exact S.isLocal G I (dec ∘ ℓ) v G' I' (dec ∘ ℓ') w
      ⟨φ, h1, h2, fun a ha => congrArg (Prod.map id dec) (h3 a ha), h4, h5⟩ hv
  complete G I hF hP v := by
    have := S.complete G I hF hP v
    simpa [Function.comp_def, hdec] using this
  sound G I hF ℓ h := S.sound G I hF (dec ∘ ℓ) h

/-- Two bits for the block label. -/
def encB : BLab → Bool × Bool
  | .head => (false, false)
  | .mid => (true, false)
  | .tail => (false, true)

/-- Encoding of an acyclicity label as a bit string of length `5 + |d|`. -/
def encLab (x : AcLab) : List Bool :=
  [decide (x.a.val % 2 = 1), decide (x.a.val / 2 = 1), (encB x.b).1, (encB x.b).2, x.c] ++ x.d

/-- Decoding of bit strings into acyclicity labels (inverse of `encLab`). -/
def decLab : List Bool → AcLab
  | a₀ :: a₁ :: b₀ :: b₁ :: c :: d =>
    ⟨if a₁ then 2 else if a₀ then 1 else 0, if b₁ then .tail else if b₀ then .mid else .head, c, d⟩
  | _ => ⟨0, .head, false, []⟩

lemma decLab_encLab (x : AcLab) : decLab (encLab x) = x := by
  rcases x with ⟨a, b, c, d⟩
  fin_cases a <;> cases b <;> simp [encLab, decLab, encB]

/-- **Theorem 8** with labels that are bit strings: for every `t ≥ 2` there is a `t`-PLS for
acyclicity (on connected graphs) with labels of `5 + ⌈⌈log₂ n⌉ / t⌉` bits on `n`-node graphs. -/
theorem theorem8_bits (t : ℕ) (ht : 2 ≤ t) :
    ∃ S : TPLS Unit (List Bool) acycFamily acycPred t,
      S.CostLE List.length fun n => 5 + (Nat.clog 2 n + t - 1) / t := by
  refine ⟨(acycTPLS t ht).recode encLab decLab decLab_encLab, fun {V} _ G I _ _ v => ?_⟩
  simp [TPLS.recode, encLab, acycTPLS, honestLabels, honestLab, shareWidth,
    Nat.card_eq_fintype_card]
  omega

end Theorem8


end Podc.SpaceTimeVerification
