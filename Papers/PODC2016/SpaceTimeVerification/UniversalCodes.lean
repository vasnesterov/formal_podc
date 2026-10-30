import Papers.PODC2016.SpaceTimeVerification.Universal

/-!
# Theorem 1: the universal `t`-PLS with labels `O((ns + min{n², m log n})/t)`

Two injective codes of configurations on `Fin n` (states encoded by an injective
`encS : ι → List Bool` with `|encS x| ≤ s`), both built with CSLib's self-delimiting
`Cslib.BitEncoding.encList`:

* `matCode`: `n` in unary, the `n` states, and the `n` rows of the adjacency matrix:
  `≤ (2n+1) + n(2s+1) + n(2n+1)` bits (`length_matCode_le`);
* `edgeCode`: `n` in unary, the `n` states, and the list of edges, each written as the two
  endpoints in binary with `Nat.size n = ⌊log₂ n⌋ + 1` bits:
  `≤ (2n+1) + n(2s+1) + m(4 size n + 1)` bits (`length_edgeCode_le`);
* `minCode`: one flag bit and the shorter of the two.

`theorem1` instantiates the generic scheme `universal` of `Universal.lean` with `minCode` and
`k = ⌈t/2⌉` shares.
-/

namespace Podc.SpaceTimeVerification

open SimpleGraph Cslib.BitEncoding Universal

namespace Universal

variable {ι : Type} (encS : ι → List Bool)

/-- Unary header (the number of nodes) followed by the encoded states. -/
def header (c : Conf ι) : List (List Bool) :=
  List.replicate c.1 true :: List.ofFn fun i => encS (c.2.2 i)

/-- A code built from the header and a per-graph part `part`. -/
def withPart (part : ∀ N, SimpleGraph (Fin N) → List (List Bool)) (c : Conf ι) : List Bool :=
  encList (header encS c ++ part c.1 c.2.1)

variable {encS}

lemma withPart_injective (hencS : Function.Injective encS)
    (part : ∀ N, SimpleGraph (Fin N) → List (List Bool))
    (hpart : ∀ N, Function.Injective (part N)) : Function.Injective (withPart encS part) := by
  rintro ⟨N₁, H₁, J₁⟩ ⟨N₂, H₂, J₂⟩ h
  have h' := congrArg decList h
  simp only [withPart, decList_encList, header, List.cons_append, List.cons.injEq] at h'
  obtain ⟨hN, h2⟩ := h'
  have hN' : N₁ = N₂ := by simpa using congrArg List.length hN
  subst hN'
  obtain ⟨hJ, hH⟩ := List.append_inj h2 (by simp)
  have hJ' : J₁ = J₂ := funext fun i => hencS (congrFun (List.ofFn_injective hJ) i)
  rw [hpart N₁ hH, hJ']

/-- `Σ (2|x|+1)` over a list of strings of length `≤ p`. -/
lemma sum_map_le (L : List (List Bool)) (p : ℕ) (h : ∀ x ∈ L, x.length ≤ p) :
    (L.map fun x => 2 * x.length + 1).sum ≤ L.length * (2 * p + 1) := by
  rw [← length_encList]; exact length_encList_le L p h

lemma length_withPart_le (s : ℕ) (hs : ∀ x, (encS x).length ≤ s)
    (part : ∀ N, SimpleGraph (Fin N) → List (List Bool)) (c : Conf ι) :
    (withPart encS part c).length ≤
      (2 * c.1 + 1) + c.1 * (2 * s + 1) + ((part c.1 c.2.1).map fun x => 2 * x.length + 1).sum := by
  rw [withPart, length_encList, header, List.cons_append, List.map_cons, List.sum_cons,
    List.map_append, List.sum_append, List.length_replicate]
  have := sum_map_le (List.ofFn fun i => encS (c.2.2 i)) s (by simp [hs])
  rw [List.length_ofFn] at this
  omega

/-! ### Adjacency matrix -/

/-- The rows of the adjacency matrix. -/
noncomputable def matRows (N : ℕ) (H : SimpleGraph (Fin N)) : List (List Bool) := by
  classical
  exact List.ofFn fun i => List.ofFn fun j => decide (H.Adj i j)

lemma matRows_injective (N : ℕ) : Function.Injective (matRows N) := by
  intro H₁ H₂ h
  classical
  ext i j
  have := congrFun (List.ofFn_injective (congrFun (List.ofFn_injective h) i)) j
  simpa using this

variable (encS) in
/-- The adjacency-matrix code. -/
noncomputable def matCode : Conf ι → List Bool := withPart encS matRows

lemma length_matCode_le (s : ℕ) (hs : ∀ x, (encS x).length ≤ s) (c : Conf ι) :
    (matCode encS c).length ≤ (2 * c.1 + 1) + c.1 * (2 * s + 1) + c.1 * (2 * c.1 + 1) := by
  have h1 := length_withPart_le s hs matRows c
  have h2 := sum_map_le (matRows c.1 c.2.1) c.1 (by classical simp [matRows])
  have h3 : (matRows c.1 c.2.1).length = c.1 := by classical simp [matRows]
  rw [h3] at h2
  exact h1.trans (by omega)

/-! ### Edge list -/

/-- An unordered pair of nodes of `Fin N`: the smaller and the larger index, `w` bits each. -/
def sym2Bits {N : ℕ} (w : ℕ) : Sym2 (Fin N) → List Bool :=
  Sym2.lift ⟨fun a b => bitsW w (min a b : Fin N) ++ bitsW w (max a b : Fin N), fun a b => by
    dsimp only; rw [min_comm, max_comm]⟩

lemma sym2_eq_min_max {N : ℕ} (a b : Fin N) : s(a, b) = s(min a b, max a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, Sym2.eq_swap]

lemma sym2Bits_injective (N : ℕ) : Function.Injective (sym2Bits (N := N) (Nat.size N)) := by
  have hlt : ∀ i : Fin N, (i : ℕ) < 2 ^ Nat.size N := fun i => i.2.trans (Nat.lt_size_self N)
  intro z z' h
  induction z using Sym2.ind with | _ a b => ?_
  induction z' using Sym2.ind with | _ a' b' => ?_
  simp only [sym2Bits, Sym2.lift_mk] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  have e1 := Fin.ext (bitsW_inj (hlt _) (hlt _) h1)
  have e2 := Fin.ext (bitsW_inj (hlt _) (hlt _) h2)
  rw [sym2_eq_min_max a b, sym2_eq_min_max a' b', e1, e2]

/-- The edge list. -/
noncomputable def edgeList (N : ℕ) (H : SimpleGraph (Fin N)) : List (List Bool) := by
  classical
  exact H.edgeFinset.toList.map (sym2Bits (Nat.size N))

lemma mem_edgeList {N : ℕ} {H : SimpleGraph (Fin N)} {z : Sym2 (Fin N)} :
    sym2Bits (Nat.size N) z ∈ edgeList N H ↔ z ∈ H.edgeSet := by
  classical
  simp only [edgeList, List.mem_map, Finset.mem_toList, mem_edgeFinset]
  exact ⟨fun ⟨z', hz', h⟩ => sym2Bits_injective N h ▸ hz', fun h => ⟨z, h, rfl⟩⟩

lemma edgeList_injective (N : ℕ) : Function.Injective (edgeList N) := by
  intro H₁ H₂ h
  rw [← edgeSet_inj]
  ext z
  rw [← mem_edgeList, ← mem_edgeList, h]

lemma length_edgeList (N : ℕ) (H : SimpleGraph (Fin N)) :
    (edgeList N H).length = Nat.card H.edgeSet := by
  classical
  rw [edgeList, List.length_map, Finset.length_toList, Nat.card_eq_card_toFinset]
  congr 1

variable (encS) in
/-- The edge-list code. -/
noncomputable def edgeCode : Conf ι → List Bool := withPart encS edgeList

lemma length_edgeCode_le (s : ℕ) (hs : ∀ x, (encS x).length ≤ s) (c : Conf ι) :
    (edgeCode encS c).length ≤
      (2 * c.1 + 1) + c.1 * (2 * s + 1) + Nat.card c.2.1.edgeSet * (4 * Nat.size c.1 + 1) := by
  have h1 := length_withPart_le s hs edgeList c
  have h2 := sum_map_le (edgeList c.1 c.2.1) (2 * Nat.size c.1) (by
    classical
    simp only [edgeList, List.mem_map]
    rintro _ ⟨z, -, rfl⟩
    induction z using Sym2.ind with | _ a b => simp [sym2Bits]; omega)
  rw [length_edgeList, show 2 * (2 * Nat.size c.1) + 1 = 4 * Nat.size c.1 + 1 by ring] at h2
  refine h1.trans ?_
  omega

/-! ### The shorter of the two -/

variable (encS) in
/-- One flag bit, then the shorter of the adjacency-matrix and edge-list codes. -/
noncomputable def minCode (c : Conf ι) : List Bool :=
  if (matCode encS c).length ≤ (edgeCode encS c).length then false :: matCode encS c
  else true :: edgeCode encS c

lemma minCode_injective (hencS : Function.Injective encS) : Function.Injective (minCode encS) := by
  have hm := withPart_injective hencS matRows matRows_injective
  have he := withPart_injective hencS edgeList edgeList_injective
  intro c c' h
  unfold minCode at h
  split_ifs at h with h1 h2 h2
  · exact hm (List.cons_injective h)
  · simp at h
  · simp at h
  · exact he (List.cons_injective h)

lemma length_minCode (c : Conf ι) :
    (minCode encS c).length = min (matCode encS c).length (edgeCode encS c).length + 1 := by
  unfold minCode
  split_ifs with h
  · simp [min_eq_left h]
  · simp [min_eq_right (le_of_lt (not_le.1 h))]

end Universal

/-- The size `R(n, m) = n (2s + 3) + 2 + min{n (2n + 1), m (4 ⌈log₂(n+1)⌉ + 1)}` of the code of
a configuration with `n` nodes, `m` edges and states of `≤ s` bits (`= Θ(ns + min{n², m log n})`
for `s ≥ 1`). -/
def univSize (s n m : ℕ) : ℕ := n * (2 * s + 3) + 2 + min (n * (2 * n + 1)) (m * (4 * Nat.size n + 1))

lemma length_minCode_toConf {ι : Type} {encS : ι → List Bool} (s : ℕ)
    (hs : ∀ x, (encS x).length ≤ s) {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι) :
    (minCode encS (toConf G I)).length ≤ univSize s (Nat.card V) (Nat.card G.edgeSet) := by
  rw [length_minCode]
  have h1 := length_matCode_le s hs (toConf G I)
  have h2 := length_edgeCode_le s hs (toConf G I)
  have hm : Nat.card (toConf G I).2.1.edgeSet = Nat.card G.edgeSet :=
    (Nat.card_congr (Iso.map (Finite.equivFin V) G).mapEdgeSet).symm
  have h1' : (matCode encS (toConf G I)).length ≤ (2 * Nat.card V + 1) +
      Nat.card V * (2 * s + 1) + Nat.card V * (2 * Nat.card V + 1) := h1
  have h2' : (edgeCode encS (toConf G I)).length ≤ (2 * Nat.card V + 1) +
      Nat.card V * (2 * s + 1) + Nat.card G.edgeSet * (4 * Nat.size (Nat.card V) + 1) := by
    rw [← hm]; exact h2
  have h3 := min_le_min h1' h2'
  rw [min_add_add_left] at h3
  have h4 : Nat.card V * (2 * s + 3) = Nat.card V * (2 * s + 1) + 2 * Nat.card V := by ring
  unfold univSize
  rw [h4]
  generalize min (matCode encS (toConf G I)).length (edgeCode encS (toConf G I)).length = A at h3 ⊢
  generalize min (Nat.card V * (2 * Nat.card V + 1))
    (Nat.card G.edgeSet * (4 * Nat.size (Nat.card V) + 1)) = B at h3 ⊢
  omega

/-- **Theorem 1** of [Ostrovsky–Perry–Rosenbaum, *Space-Time Tradeoffs for Distributed
Verification*] (universal `t`-PLS). Let the states `ι` be encoded injectively with `≤ s` bits
(they contain unique identifiers, so the states of a configuration are pairwise distinct), let
`F` be a family of connected configurations with diameter `D ≥ (t - 2)/2` (i.e. `t ≤ 2D + 2`: the
paper's "`t ∈ Ω(D)`" must read `t ∈ O(D)`), and let `P` be invariant under state-preserving
isomorphisms. For every `t ≥ 1` there is a `t`-PLS for `(F, P)` whose labels have at most
`2 R / t + ⌊log₂ t⌋ + 2` bits, `R = univSize s n m = Θ(ns + min{n², m log n})`. -/
theorem theorem1 {ι : Type} (encS : ι → List Bool) (hencS : Function.Injective encS) (s : ℕ)
    (hs : ∀ x, (encS x).length ≤ s) (F P : CProp ι) (hP : IsoInvariant P) (t : ℕ) (ht : 1 ≤ t)
    (hF : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I →
      G.Connected ∧ Function.Injective I ∧ t ≤ 2 * G.diam + 2) :
    ∃ S : TPLS ι (List Bool) F P t, ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (I : V → ι),
      F V G I → ∀ v, (S.prove G I v).length ≤
        2 * univSize s (Fintype.card V) (Nat.card G.edgeSet) / t + Nat.size t + 1 := by
  set k := (t + 1) / 2
  have hk : 0 < k := by omega
  have hkt : 2 * k ≤ t + 1 := by omega
  have hF' : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I →
      G.Connected ∧ Function.Injective I ∧ k ≤ G.diam + 1 := fun G I h =>
    ⟨(hF G I h).1, (hF G I h).2.1, by have := (hF G I h).2.2; omega⟩
  refine ⟨universal (minCode encS) (minCode_injective hencS) F P hP k t hk hkt hF', ?_⟩
  intro V _ G I _ v
  refine (universal_length _ _ F P hP k t hk hkt hF' G I v).trans ?_
  have hR := length_minCode_toConf s hs G I
  rw [Nat.card_eq_fintype_card] at hR
  set R := univSize s (Fintype.card V) (Nat.card G.edgeSet)
  have h1 : Nat.size k ≤ Nat.size t := Nat.size_le_size (by omega)
  have h2 : (minCode encS (toConf G I)).length ⌈/⌉ k ≤ 2 * R / t + 1 := by
    refine (Nat.ceilDiv_mono k hR).trans (Nat.ceilDiv_le_of_le_mul hk ?_)
    have h3 := Nat.lt_mul_div_succ (2 * R) (show 0 < t by omega)
    have h4 : t * (2 * R / t + 1) ≤ 2 * (k * (2 * R / t + 1)) := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  omega

/-- Theorem 1 with a bound in terms of `n` only (`m ≤ n²`): the verification complexity
(`TPLS.CostLE`) is at most `2 (n (2s + 3) + 2 + n (2n + 1)) / t + ⌊log₂ t⌋ + 2`. -/
theorem theorem1_costLE {ι : Type} (encS : ι → List Bool) (hencS : Function.Injective encS)
    (s : ℕ) (hs : ∀ x, (encS x).length ≤ s) (F P : CProp ι) (hP : IsoInvariant P) (t : ℕ)
    (ht : 1 ≤ t)
    (hF : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → ι), F V G I →
      G.Connected ∧ Function.Injective I ∧ t ≤ 2 * G.diam + 2) :
    ∃ S : TPLS ι (List Bool) F P t, S.CostLE List.length
      (fun n => 2 * (n * (2 * s + 3) + 2 + n * (2 * n + 1)) / t + Nat.size t + 1) := by
  obtain ⟨S, hS⟩ := theorem1 encS hencS s hs F P hP t ht hF
  refine ⟨S, ?_⟩
  intro V _ G I hFG _ v
  refine (hS G I hFG v).trans ?_
  have h1 : univSize s (Fintype.card V) (Nat.card G.edgeSet) ≤
      Fintype.card V * (2 * s + 3) + 2 + Fintype.card V * (2 * Fintype.card V + 1) := by
    unfold univSize; omega
  have h2 := Nat.div_le_div_right (c := t) (Nat.mul_le_mul_left 2 h1)
  beta_reduce
  omega

/-- Theorem 1 with explicit identifiers: states are pairs (input `a : σ`, identifier `< 2^β`),
inputs encoded injectively with `≤ s` bits, identifiers pairwise distinct. Labels have at most
`2 R / t + ⌊log₂ t⌋ + 2` bits with `R = univSize (s + β) n m`. -/
theorem theorem1_ids {σ : Type} (encσ : σ → List Bool) (henc : Function.Injective encσ)
    (s β : ℕ) (hs : ∀ a, (encσ a).length ≤ s) (F P : CProp (σ × Fin (2 ^ β)))
    (hP : IsoInvariant P) (t : ℕ) (ht : 1 ≤ t)
    (hF : ∀ {V : Type} [Finite V] (G : SimpleGraph V) (I : V → σ × Fin (2 ^ β)), F V G I →
      G.Connected ∧ Function.Injective (fun v => (I v).2) ∧ t ≤ 2 * G.diam + 2) :
    ∃ S : TPLS (σ × Fin (2 ^ β)) (List Bool) F P t, ∀ {V : Type} [Fintype V]
      (G : SimpleGraph V) (I : V → σ × Fin (2 ^ β)), F V G I → ∀ v, (S.prove G I v).length ≤
        2 * univSize (s + β) (Fintype.card V) (Nat.card G.edgeSet) / t + Nat.size t + 1 := by
  let encS : σ × Fin (2 ^ β) → List Bool := fun x => bitsW β x.2 ++ encσ x.1
  have hencS : Function.Injective encS := by
    rintro ⟨a, i⟩ ⟨a', i'⟩ h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    exact Prod.ext (henc h2) (Fin.ext (bitsW_inj i.2 i'.2 h1))
  have hlen : ∀ x, (encS x).length ≤ s + β := fun x => by
    have := hs x.1
    simp only [encS, List.length_append, length_bitsW]
    omega
  exact theorem1 encS hencS (s + β) hlen F P hP t ht fun G I h =>
    ⟨(hF G I h).1, fun a b hab => (hF G I h).2.1 (congrArg Prod.snd hab), (hF G I h).2.2⟩

/-- Non-vacuity: the hypotheses of `theorem1` hold for the family of all connected
configurations with pairwise distinct states and diameter `≥ (t - 2)/2`. -/
example {ι : Type} (encS : ι → List Bool) (hencS : Function.Injective encS) (s : ℕ)
    (hs : ∀ x, (encS x).length ≤ s) (P : CProp ι) (hP : IsoInvariant P) (t : ℕ) (ht : 1 ≤ t) :
    ∃ S : TPLS ι (List Bool)
      (fun _ G I => G.Connected ∧ Function.Injective I ∧ t ≤ 2 * G.diam + 2) P t,
      ∀ {V : Type} [Fintype V] (G : SimpleGraph V) (I : V → ι),
        (G.Connected ∧ Function.Injective I ∧ t ≤ 2 * G.diam + 2) → ∀ v,
        (S.prove G I v).length ≤
          2 * univSize s (Fintype.card V) (Nat.card G.edgeSet) / t + Nat.size t + 1 :=
  theorem1 encS hencS s hs _ P hP t ht fun _ _ h => h

lemma pathGraph_walk_le {N : ℕ} {a b : Fin N} (p : (pathGraph N).Walk a b) :
    (b : ℕ) ≤ a + p.length := by
  induction p with
  | nil => simp
  | cons h _ ih => rw [pathGraph_adj] at h; simp only [Walk.length_cons]; omega

/-- Non-vacuity: the path on `n + 1` nodes is connected with diameter `≥ n`, so the family above
contains configurations for every `t`. -/
lemma pathGraph_le_diam (n : ℕ) : (pathGraph (n + 1)).Connected ∧ n ≤ (pathGraph (n + 1)).diam := by
  have hc := pathGraph_connected n
  refine ⟨hc, ?_⟩
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist (0 : Fin (n + 1)) (Fin.last n)
  have h1 := pathGraph_walk_le p
  have h2 := dist_le_diam (connected_iff_ediam_ne_top.1 hc) (u := (0 : Fin (n + 1)))
    (v := Fin.last n)
  simp only [Fin.val_last, Fin.val_zero, zero_add] at h1
  omega

end Podc.SpaceTimeVerification
