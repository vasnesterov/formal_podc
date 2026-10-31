import Papers.PODC2015.RandomizedPLS.Compile
import Cslib.Foundations.Data.List.BitEncoding

/-!
# The universal scheme (Lemma 3.4, Corollary 3.5)

Lemma 3.4 (cited from [20, 30]): with states of `k` bits, every predicate has a PLS whose label is a
description of the whole configuration. We formalize the classical scheme:

* the label of `v` is `lab (index of v) D`, where `D` lists, for every node in some enumeration,
  its state and the indices of its neighbours ordered by port (bit-encoded with CSLib's
  self-delimiting `encList`);
* the verifier at `v` checks that its own row of `D` carries its state, that the neighbour at each
  port `p` carries the label `lab (D[i].2[p]) D`, and that `D` describes a connected legal
  configuration (an existential check: the local computation is unbounded, as in the paper).

Soundness needs the implicit assumptions of the paper's model: configurations are connected, the
states contain distinct identities, and `P` is invariant under port-preserving isomorphisms
(`Config.Iso`). Label length (`universal_labelBound`):
`2 log n + 4 + 2n(4k + 3) + 4(2 log n + 3) · Σ_v deg v = O(nk + m log n)`; the paper states
`O(nk + min{n², m log n})` (we do not formalize the adjacency-matrix variant for dense graphs).

Corollary 3.5 (`cor_3_5`): via Theorem 3.1, a one-sided RPLS with certificates of
`O(log n + log k)` bits.
-/

namespace Podc.RandomizedPLS

open Classical Cslib.BitEncoding

variable {S : Type}

/-- A port-preserving isomorphism of configurations preserving the states. -/
def Config.Iso (c c' : Config S) : Prop :=
  ∃ f : c.V ≃ c'.V, ∀ v, c'.state (f v) = c.state v ∧ c'.nbrs (f v) = (c.nbrs v).map f

namespace Universal

/-- A description: for every node, its state and the indices of its neighbours by port. -/
abbrev Desc (S : Type) := List (S × List ℕ)

/-- The description of `c` along an enumeration of its nodes. -/
noncomputable def desc (c : Config S) (e : c.V ≃ Fin (Fintype.card c.V)) : Desc S :=
  List.ofFn fun j => (c.state (e.symm j), (c.nbrs (e.symm j)).map fun w => (e w : ℕ))

variable (encS : S → List Bool)

/-- Encoding of a row. -/
def encRow (x : S × List ℕ) : List Bool := encList (encS x.1 :: x.2.map encN)

/-- Encoding of a description. -/
def encD (D : Desc S) : List Bool := encList (D.map (encRow encS))

/-- The label: own index and the description. -/
def lab (i : ℕ) (D : Desc S) : List Bool := encList [encN i, encD encS D]

lemma encList_injective : Function.Injective encList := fun a b h => by
  rw [← decList_encList a, h, decList_encList]

lemma encN_injective : Function.Injective encN := fun a b h => by
  rw [← decN_encN a, h, decN_encN]

variable {encS}

lemma lab_inj (hS : Function.Injective encS) {i i' : ℕ} {D D' : Desc S}
    (h : lab encS i D = lab encS i' D') : i = i' ∧ D = D' := by
  have h1 := encList_injective h
  simp only [List.cons.injEq, and_true] at h1
  refine ⟨encN_injective h1.1, ?_⟩
  have h2 := encList_injective h1.2
  refine (List.map_injective_iff.2 ?_) h2
  intro x y hxy
  have h3 := encList_injective hxy
  simp only [List.cons.injEq] at h3
  exact Prod.ext (hS h3.1) ((List.map_injective_iff.2 encN_injective) h3.2)

variable (encS) (P : Config S → Prop)

/-- `D` describes a connected configuration satisfying `P`. -/
def Valid (D : Desc S) : Prop :=
  ∃ (c' : Config S) (e : c'.V ≃ Fin (Fintype.card c'.V)), desc c' e = D ∧ P c' ∧ c'.Connected

/-- The universal verifier. -/
noncomputable def ver : Verifier S := fun s x ys =>
  decide (∃ i D, x = lab encS i D ∧ ∃ h : i < D.length, D[i].1 = s ∧
    ys = D[i].2.map (fun j => lab encS j D) ∧ Valid P D)

/-- The universal prover. -/
noncomputable def prover (c : Config S) (v : c.V) : List Bool :=
  lab encS (Fintype.equivFin c.V v) (desc c (Fintype.equivFin c.V))

lemma desc_length (c : Config S) (e : c.V ≃ Fin (Fintype.card c.V)) :
    (desc c e).length = Fintype.card c.V := List.length_ofFn

lemma desc_getElem (c : Config S) (e : c.V ≃ Fin (Fintype.card c.V)) (j : ℕ)
    (hj : j < (desc c e).length) :
    (desc c e)[j] = (c.state (e.symm ⟨j, by rwa [desc_length] at hj⟩),
      (c.nbrs (e.symm ⟨j, by rwa [desc_length] at hj⟩)).map fun w => (e w : ℕ)) := by
  simp [desc]

variable {encS P}

lemma accepts_prover {c : Config S} (hP : P c) (hc : c.Connected) :
    Accepts (ver encS P) c (prover encS c) := by
  intro v
  set e := Fintype.equivFin c.V
  simp only [ver, decide_eq_true_eq]
  have hi : (e v : ℕ) < (desc c e).length := by rw [desc_length]; exact (e v).2
  refine ⟨e v, desc c e, rfl, hi, ?_, ?_, c, e, rfl, hP, hc⟩
  · rw [desc_getElem]; simp
  · rw [desc_getElem]
    simp only [Fin.eta, Equiv.symm_apply_apply, List.map_map]
    rfl

/-- Soundness of the universal scheme. -/
lemma sound {F : Config S → Prop} (hS : Function.Injective encS)
    (hconn : ∀ c, F c → c.Connected) (hid : ∀ c, F c → Function.Injective c.state)
    (hiso : ∀ c c', F c → Config.Iso c c' → P c' → P c)
    {c : Config S} (hF : F c) (hP : ¬ P c) (ℓ : c.V → List Bool) :
    ¬ Accepts (ver encS P) c ℓ := by
  intro hacc
  have hv : ∀ v, ∃ i D, ℓ v = lab encS i D ∧ ∃ h : i < D.length, D[i].1 = c.state v ∧
      (c.nbrs v).map ℓ = D[i].2.map (fun j => lab encS j D) ∧ Valid P D := fun v => by
    have := hacc v
    simpa [ver] using this
  choose I Dd hlab hlt hst hnb hval using hv
  -- neighbours carry the same description
  have hadj : ∀ v w, w ∈ c.nbrs v → Dd w = Dd v := by
    intro v w hw
    have : ℓ w ∈ ((Dd v)[I v]'(hlt v)).2.map (fun j => lab encS j (Dd v)) := by
      rw [← hnb v]; exact List.mem_map_of_mem hw
    obtain ⟨j, -, hj⟩ := List.mem_map.1 this
    rw [hlab w] at hj
    exact (lab_inj hS hj).2.symm
  have hc := hconn c hF
  obtain ⟨v₀⟩ := hc.nonempty
  have hconst : ∀ v, Dd v = Dd v₀ := by
    intro v
    obtain ⟨p⟩ := hc.preconnected v₀ v
    induction p with
    | nil => rfl
    | cons h p ih => exact ih.trans (hadj _ _ h)
  obtain ⟨c', e, hdesc, hP', hc'⟩ := hval v₀
  have hlen : ∀ v, I v < Fintype.card c'.V := fun v => by
    have := hlt v; rw [hconst v, ← hdesc, desc_length] at this; exact this
  let φ : c.V → c'.V := fun v => e.symm ⟨I v, hlen v⟩
  have hrow : ∀ v, (Dd v)[I v]'(hlt v) = (c'.state (φ v), (c'.nbrs (φ v)).map fun w => (e w : ℕ)) := by
    intro v
    have h1 : (Dd v)[I v]'(hlt v) = (desc c' e)[I v]'(by rw [desc_length]; exact hlen v) :=
      List.getElem_of_eq ((hconst v).trans hdesc.symm) _
    rw [h1, desc_getElem]
  have hstate : ∀ v, c'.state (φ v) = c.state v := fun v => by
    have := hst v; rw [hrow v] at this; exact this
  have hnbrs : ∀ v, c'.nbrs (φ v) = (c.nbrs v).map φ := by
    intro v
    have h1 := hnb v
    rw [hrow v, List.map_map] at h1
    have h2 : (c.nbrs v).map ℓ = ((c.nbrs v).map φ).map
        ((fun j => lab encS j (Dd v)) ∘ fun w => (e w : ℕ)) := by
      rw [List.map_map]
      refine List.map_congr_left fun w hw => ?_
      simp only [Function.comp_apply, φ, Equiv.apply_symm_apply]
      rw [hlab w, hadj v w hw]
    rw [h2] at h1
    have hinj : Function.Injective ((fun j => lab encS j (Dd v)) ∘ fun w : c'.V => (e w : ℕ)) := by
      intro x y hxy
      have := (lab_inj hS hxy).1
      exact e.injective (Fin.ext this)
    exact ((List.map_injective_iff.2 hinj) h1).symm
  have hφinj : Function.Injective φ := fun v w h => hid c hF (by rw [← hstate v, ← hstate w, h])
  have hreach : ∀ a b (p : c'.graph.Walk a b), (∃ v, φ v = a) → ∃ v, φ v = b := by
    intro a b p
    induction p with
    | nil => exact id
    | cons h p ih =>
      rintro ⟨v, rfl⟩
      apply ih
      have h' : _ ∈ c'.nbrs (φ v) := h
      rw [hnbrs v] at h'
      obtain ⟨w, -, hw⟩ := List.mem_map.1 h'
      exact ⟨w, hw⟩
  have hφsurj : Function.Surjective φ := fun y => by
    obtain ⟨p⟩ := hc'.preconnected (φ v₀) y
    exact hreach _ _ p ⟨v₀, rfl⟩
  let f := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  exact hP (hiso c c' hF ⟨f, fun v => ⟨hstate v, hnbrs v⟩⟩ hP')

variable (encS)

lemma length_encN_lt {x n : ℕ} (hx : x < n) : (encN x).length ≤ Nat.log 2 n + 1 :=
  (length_encN x).trans (Nat.add_le_add_right (Nat.log_mono_right hx.le) 1)

lemma length_encRow (x : S × List ℕ) :
    (encRow encS x).length = 2 * (encS x.1).length + 1 +
      (x.2.map fun j => 2 * (encN j).length + 1).sum := by
  simp [encRow, length_encList, List.map_map, Function.comp_def]

/-- The label length of the universal prover: `O(nk + m log n)`. -/
theorem length_prover (c : Config S) (k : ℕ) (hk : ∀ v, (encS (c.state v)).length ≤ k)
    (v : c.V) :
    (prover encS c v).length ≤ 2 * Nat.log 2 (Fintype.card c.V) + 4 +
      2 * (Fintype.card c.V * (4 * k + 3)) +
      4 * (2 * Nat.log 2 (Fintype.card c.V) + 3) * ∑ u, (c.nbrs u).length := by
  set n := Fintype.card c.V
  set e := Fintype.equivFin c.V
  set L := Nat.log 2 n
  have hrow : ∀ u : c.V, (encRow encS (c.state u, (c.nbrs u).map fun w => (e w : ℕ))).length ≤
      2 * k + 1 + (c.nbrs u).length * (2 * L + 3) := by
    intro u
    rw [length_encRow]
    have h1 := hk u
    have h2 : (((c.nbrs u).map fun w => (e w : ℕ)).map fun j => 2 * (encN j).length + 1).sum ≤
        (c.nbrs u).length * (2 * L + 3) := by
      rw [List.map_map]
      have := List.sum_le_length_nsmul (((c.nbrs u).map ((fun j => 2 * (encN j).length + 1) ∘
        fun w => (e w : ℕ)))) (2 * L + 3) (by
          intro x hx
          obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
          have := length_encN_lt (n := n) (e w).2
          simp only [Function.comp_apply]; omega)
      simpa using this
    simp only at h2 ⊢
    omega
  have hD : (encD encS (desc c e)).length ≤ n * (4 * k + 3) +
      2 * (2 * L + 3) * ∑ u, (c.nbrs u).length := by
    rw [encD, length_encList, List.map_map, desc, List.map_ofFn, List.sum_ofFn]
    calc ∑ j : Fin n, ((fun s => 2 * s.length + 1) ∘ encRow encS ∘ fun j : Fin n =>
          (c.state (e.symm j), (c.nbrs (e.symm j)).map fun w => (e w : ℕ))) j
        ≤ ∑ j : Fin n, (4 * k + 3 + 2 * (2 * L + 3) * (c.nbrs (e.symm j)).length) :=
          Finset.sum_le_sum fun j _ => by
            have := hrow (e.symm j)
            simp only [Function.comp_apply]
            nlinarith
      _ = n * (4 * k + 3) + 2 * (2 * L + 3) * ∑ u, (c.nbrs u).length := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, smul_eq_mul]
          congr 2
          exact Equiv.sum_comp e.symm (fun u => (c.nbrs u).length)
  have hi := length_encN_lt (n := n) (e v).2
  simp only [prover, lab, length_encList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  change 2 * (encN (e v)).length + 1 + (2 * (encD encS (desc c e)).length + 1 + 0) ≤ _
  nlinarith

variable {encS}

/-- **Lemma 3.4 of [BFP15]** (universal PLS; cited there from [20, 30]). Assume, as in the paper's
model, that configurations are connected, that states contain distinct identities, that `P` is
invariant under port-preserving isomorphisms, and that states are encoded injectively with at most
`k c` bits. Then `(F, P)` has a PLS with labels of `O(nk + m log n)` bits. -/
theorem lemma_3_4 {F : Config S → Prop} (hS : Function.Injective encS)
    (hconn : ∀ c, F c → c.Connected) (hid : ∀ c, F c → Function.Injective c.state)
    (hiso : ∀ c c', F c → Config.Iso c c' → P c' → P c) (k : Config S → ℕ)
    (hk : ∀ c, F c → ∀ v, (encS (c.state v)).length ≤ k c) :
    IsPLS (ver encS P) (prover encS) F P ∧
    LabelBound (prover encS) F P (fun c => 2 * Nat.log 2 (Fintype.card c.V) + 4 +
      2 * (Fintype.card c.V * (4 * k c + 3)) +
      4 * (2 * Nat.log 2 (Fintype.card c.V) + 3) * ∑ u, (c.nbrs u).length) :=
  ⟨⟨fun c hF hP => accepts_prover hP (hconn c hF), fun c hF hP ℓ => sound hS hconn hid hiso hF hP ℓ⟩,
    fun c hF _ v => length_prover encS c (k c) (hk c hF) v⟩

end Universal

end Podc.RandomizedPLS

namespace Podc.RandomizedPLS

open Classical Universal

variable {S : Type} {encS : S → List Bool} {P : Config S → Prop}

lemma universal_bound_le (c : Config S) (k : ℕ) (hn : 0 < Fintype.card c.V) :
    2 * Nat.log 2 (Fintype.card c.V) + 4 + 2 * (Fintype.card c.V * (4 * k + 3)) +
      4 * (2 * Nat.log 2 (Fintype.card c.V) + 3) * ∑ u, (c.nbrs u).length ≤
    32 * (k + 1) * Fintype.card c.V ^ 3 := by
  set n := Fintype.card c.V
  have hdeg : ∑ u, (c.nbrs u).length ≤ n * n := by
    calc ∑ u, (c.nbrs u).length ≤ ∑ _u : c.V, n :=
          Finset.sum_le_sum fun u _ => (c.nodup u).length_le_card
      _ = n * n := by simp [n]
  have hlog : Nat.log 2 n ≤ n := (Nat.log_lt_self 2 hn.ne').le
  have h1 : 1 ≤ n := hn
  have hn2 : n ≤ n * n := Nat.le_mul_of_pos_left n hn
  have hn3 : n * n ≤ n ^ 3 := by rw [pow_succ, pow_two]; exact Nat.le_mul_of_pos_right _ hn
  have h4 : 4 * (2 * Nat.log 2 n + 3) * ∑ u, (c.nbrs u).length ≤ 4 * (2 * n + 3) * (n * n) :=
    Nat.mul_le_mul (by omega) hdeg
  have : 4 * (2 * n + 3) * (n * n) = 8 * n ^ 3 + 12 * (n * n) := by ring
  have hk : k * n ≤ k * n ^ 3 := Nat.mul_le_mul_left k (hn2.trans hn3)
  nlinarith

/-- **Corollary 3.5 of [BFP15].** Under the assumptions of Lemma 3.4, `(F, P)` has a one-sided
(edge-independent) RPLS with certificates of `2 log₂(32 (k + 1) n³) + 6 = O(log n + log k)`
bits. -/
theorem cor_3_5 {F : Config S → Prop} (hS : Function.Injective encS)
    (hconn : ∀ c, F c → c.Connected) (hid : ∀ c, F c → Function.Injective c.state)
    (hiso : ∀ c c', F c → Config.Iso c c' → P c' → P c) (k : Config S → ℕ)
    (hk : ∀ c, F c → ∀ v, (encS (c.state v)).length ≤ k c) :
    ∃ (e : EIScheme S (List (List Bool))) (prover : ∀ c : Config S, c.V → List (List Bool)),
      IsRPLS e.toRScheme prover F P 1 (2 / 3) ∧
      CertBound e.toRScheme prover F P
        (fun c => 2 * Nat.log 2 (32 * (k c + 1) * Fintype.card c.V ^ 3) + 6) := by
  obtain ⟨hpls, hlab⟩ := lemma_3_4 hS hconn hid hiso k hk
  obtain ⟨hR, hB⟩ := theorem_3_1 hpls hlab
  refine ⟨_, _, hR, fun c hF hP v ω i hi => (hB c hF hP v ω i hi).trans ?_⟩
  have hn : 0 < Fintype.card c.V := Fintype.card_pos_iff.2 (hconn c hF).nonempty
  have := Nat.log_mono_right (b := 2) (universal_bound_le c (k c) hn)
  simp only
  omega

end Podc.RandomizedPLS
