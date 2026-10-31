import Mathlib
import Cslib.Probability.Finite.Uniform

/-!
# Randomized proof-labeling schemes: the model (Section 2 of Baruch–Fraigniaud–Patt-Shamir)

M. Baruch, P. Fraigniaud, B. Patt-Shamir. *Randomized Proof-Labeling Schemes.* PODC 2015.

* `Config S`: a port-numbered configuration (Section 2.1). The node set `V` is any finite type;
  `nbrs v : List V` lists the neighbours of `v` by port number (port `i` is `(nbrs v)[i]`, ports are
  numbered from `0`); every node has a state in `S` (identities, inputs, weights, … are part of the
  state). Graphs are simple (`nodup`, `loopless`, `symm`); connectivity is a property
  (`Config.Connected`) that families may require.
* `IsPLS ver prover F P` (deterministic proof-labeling scheme, Section 2.2): labels are bit strings;
  the verifier at `v` sees its state, its label and the labels of its neighbours ordered by port.
* `RScheme` (randomized verifier, Section 2.2): node `v` draws private coins uniformly from a finite
  space `Ω (state) (label) (degree)`; from its coins it computes one certificate (a bit string) per
  port; node `v` then decides from its state, its label and the certificates received from its
  neighbours (ordered by port). Coins of distinct nodes are independent (product space `Coins`).
  `IsRPLS σ prover F P pacc prej`: completeness `Pr[accept] ≥ pacc` on legal configurations with the
  prover's labels, soundness `Pr[reject] ≥ prej` on illegal configurations for every labelling.
  One-sided: `pacc = 1, prej = 1/2`; two-sided: `pacc = prej = 2/3`.
* `EIScheme` (Definition 4.5, edge-independent schemes): every port has its own independent coin.
* Verification complexity: `LabelBound` (PLS) and `CertBound` (RPLS) bound the label / certificate
  lengths on legal configurations by a function `κ` of the configuration (e.g. of `n`).
* `Copies c r`: `r` pairwise independent port-preserving copies `emb i : W → V` of a pattern graph `H`
  (Definition 4.1 and the hypotheses of Proposition 4.3); `Copies.cross i j` is the crossing of
  Definition 4.2 induced by `σ = emb j ∘ (emb i)⁻¹`.
-/

namespace Podc.RandomizedPLS

open Classical

/-! ### Configurations -/

/-- A port-numbered configuration with states in `S`. -/
structure Config (S : Type) where
  /-- The nodes. -/
  V : Type
  [fin : Fintype V]
  [deq : DecidableEq V]
  /-- `nbrs v` lists the neighbours of `v`; the index in the list is the port number. -/
  nbrs : V → List V
  nodup : ∀ v, (nbrs v).Nodup
  loopless : ∀ v, v ∉ nbrs v
  symm : ∀ v w, w ∈ nbrs v → v ∈ nbrs w
  /-- The state of each node (identity, input, …). -/
  state : V → S
  /-- The degree (a field, so that operations keeping all degrees can keep it definitionally). -/
  deg : V → ℕ := fun v => (nbrs v).length
  deg_eq : ∀ v, deg v = (nbrs v).length := by intros; rfl

attribute [instance] Config.fin Config.deq

namespace Config

variable {S : Type} (c : Config S)

/-- Adjacency. -/
def Adj (v w : c.V) : Prop := w ∈ c.nbrs v

/-- The underlying simple graph. -/
def graph : SimpleGraph c.V where
  Adj v w := w ∈ c.nbrs v
  symm := ⟨fun v w h => c.symm v w h⟩
  loopless := ⟨fun v h => c.loopless v h⟩

@[simp] lemma graph_adj (v w : c.V) : c.graph.Adj v w ↔ w ∈ c.nbrs v := Iff.rfl

/-- The port of `v` at which `w` is attached (meaningful when `w ∈ nbrs v`). -/
def port (v w : c.V) : ℕ := (c.nbrs v).idxOf w

/-- The network is connected. -/
def Connected : Prop := c.graph.Connected

lemma neighborFinset_eq (v : c.V) : c.graph.neighborFinset v = (c.nbrs v).toFinset := by
  ext w; simp [SimpleGraph.mem_neighborFinset]

/-- The degree in the graph is the length of the port list. -/
lemma degree_eq (v : c.V) : c.graph.degree v = (c.nbrs v).length := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_eq,
    List.toFinset_card_of_nodup (c.nodup v)]

end Config

/-! ### Deterministic proof-labeling schemes -/

/-- A deterministic local verifier: state, own label, labels of the neighbours ordered by port. -/
abbrev Verifier (S : Type) := S → List Bool → List (List Bool) → Bool

/-- The verifier accepts `c` with labels `ℓ`: it outputs `true` at every node. -/
def Accepts {S : Type} (ver : Verifier S) (c : Config S) (ℓ : c.V → List Bool) : Prop :=
  ∀ v, ver (c.state v) (ℓ v) ((c.nbrs v).map ℓ) = true

/-- `(prover, ver)` is a proof-labeling scheme for `(F, P)` (Section 2.2). -/
def IsPLS {S : Type} (ver : Verifier S) (prover : ∀ c : Config S, c.V → List Bool)
    (F P : Config S → Prop) : Prop :=
  (∀ c, F c → P c → Accepts ver c (prover c)) ∧
  (∀ c, F c → ¬ P c → ∀ ℓ : c.V → List Bool, ¬ Accepts ver c ℓ)

/-- Verification complexity of a PLS: the labels on legal configurations have at most `κ c` bits. -/
def LabelBound {S : Type} (prover : ∀ c : Config S, c.V → List Bool) (F P : Config S → Prop)
    (κ : Config S → ℕ) : Prop :=
  ∀ c, F c → P c → ∀ v, (prover c v).length ≤ κ c

/-! ### Randomized proof-labeling schemes -/

/-- A randomized verifier with labels in `L`: private coins, certificates per port, local decision. -/
structure RScheme (S L : Type) where
  /-- The coin space of a node with the given state, label and degree (uniform distribution). -/
  Ω : S → L → ℕ → Type
  [fin : ∀ s ℓ d, Fintype (Ω s ℓ d)]
  [ne : ∀ s ℓ d, Nonempty (Ω s ℓ d)]
  /-- `cert s ℓ d ω i`: the certificate sent on port `i`. -/
  cert : ∀ s ℓ d, Ω s ℓ d → ℕ → List Bool
  /-- The decision: state, own label, certificates received, ordered by port. -/
  dec : S → L → List (List Bool) → Bool

attribute [instance] RScheme.fin RScheme.ne

namespace RScheme

variable {S L : Type} (σ : RScheme S L) (c : Config S) (ℓ : c.V → L)

/-- The joint coins of all nodes. -/
abbrev Coins := ∀ v : c.V, σ.Ω (c.state v) (ℓ v) (c.deg v)

/-- The certificate sent by `w` on port `i`. -/
def sent (ω : σ.Coins c ℓ) (w : c.V) (i : ℕ) : List Bool :=
  σ.cert (c.state w) (ℓ w) (c.deg w) (ω w) i

/-- The certificates received by `v`, ordered by the ports of `v`: from the neighbour `w` at port
`i`, the certificate that `w` sends on its port towards `v`. -/
def received (ω : σ.Coins c ℓ) (v : c.V) : List (List Bool) :=
  (c.nbrs v).map fun w => σ.sent c ℓ ω w (c.port w v)

/-- All nodes accept. -/
def AcceptsAll (ω : σ.Coins c ℓ) : Prop :=
  ∀ v, σ.dec (c.state v) (ℓ v) (σ.received c ℓ ω v) = true

/-- The probability that the verifier accepts `c` with labels `ℓ`. -/
noncomputable def accProb : ℝ := Cslib.Probability.uprob (σ.AcceptsAll c ℓ)

end RScheme

/-- `(σ, prover)` is a randomized proof-labeling scheme for `(F, P)` with acceptance probability
`pacc` on legal configurations and rejection probability `prej` on illegal ones. -/
def IsRPLS {S L : Type} (σ : RScheme S L) (prover : ∀ c : Config S, c.V → L)
    (F P : Config S → Prop) (pacc prej : ℝ) : Prop :=
  (∀ c, F c → P c → pacc ≤ σ.accProb c (prover c)) ∧
  (∀ c, F c → ¬ P c → ∀ ℓ : c.V → L, prej ≤ 1 - σ.accProb c ℓ)

/-- One-sided RPLS: legal configurations are accepted with probability `1`, illegal ones rejected
with probability `≥ 1/2`. -/
def IsOneSided {S L : Type} (σ : RScheme S L) (prover : ∀ c : Config S, c.V → L)
    (F P : Config S → Prop) : Prop := IsRPLS σ prover F P 1 (1 / 2)

/-- Two-sided RPLS: success probability `≥ 2/3` on both sides. -/
def IsTwoSided {S L : Type} (σ : RScheme S L) (prover : ∀ c : Config S, c.V → L)
    (F P : Config S → Prop) : Prop := IsRPLS σ prover F P (2 / 3) (2 / 3)

/-- Verification complexity of an RPLS (Definition 2.1): on legal configurations, with the
prover's labels, every certificate (on every port `i < deg v`, for every outcome of the coins) has
at most `κ c` bits. -/
def CertBound {S L : Type} (σ : RScheme S L) (prover : ∀ c : Config S, c.V → L)
    (F P : Config S → Prop) (κ : Config S → ℕ) : Prop :=
  ∀ c, F c → P c → ∀ v (ω : σ.Ω (c.state v) (prover c v) (c.deg v)) i, i < c.deg v →
    (σ.cert _ _ _ ω i).length ≤ κ c

/-- An edge-independent randomized verifier (Definition 4.5): every port has its own independent
coin, drawn uniformly from `Ω₀ s ℓ d`. -/
structure EIScheme (S L : Type) where
  /-- The coin space of one port. -/
  Ω₀ : S → L → ℕ → Type
  [fin : ∀ s ℓ d, Fintype (Ω₀ s ℓ d)]
  [ne : ∀ s ℓ d, Nonempty (Ω₀ s ℓ d)]
  /-- `cert s ℓ d i x`: the certificate on port `i` when the coin of port `i` is `x`. -/
  cert : ∀ s ℓ d, ℕ → Ω₀ s ℓ d → List Bool
  /-- The decision. -/
  dec : S → L → List (List Bool) → Bool

attribute [instance] EIScheme.fin EIScheme.ne

/-- An edge-independent scheme as a randomized verifier: the coins of a node of degree `d` are
`d` independent per-port coins. -/
def EIScheme.toRScheme {S L : Type} (e : EIScheme S L) : RScheme S L where
  Ω s ℓ d := Fin d → e.Ω₀ s ℓ d
  cert s ℓ d ω i := if h : i < d then e.cert s ℓ d i (ω ⟨i, h⟩) else []
  dec := e.dec

/-- Acceptance with probability `1` means acceptance for every outcome of the coins. -/
lemma RScheme.accProb_eq_one_iff {S L : Type} (σ : RScheme S L) (c : Config S) (ℓ : c.V → L) :
    σ.accProb c ℓ = 1 ↔ ∀ ω, σ.AcceptsAll c ℓ ω := by
  unfold RScheme.accProb Cslib.Probability.uprob
  have hpos : (0 : ℝ) < Fintype.card (σ.Coins c ℓ) := by exact_mod_cast Fintype.card_pos
  rw [div_eq_one_iff_eq hpos.ne', Nat.card_eq_fintype_card]
  constructor
  · intro h ω
    have h' : Fintype.card {ω // σ.AcceptsAll c ℓ ω} = Fintype.card (σ.Coins c ℓ) := by
      exact_mod_cast h
    by_contra hω
    have := Fintype.card_subtype_lt (p := σ.AcceptsAll c ℓ) hω
    omega
  · intro h
    have : Fintype.card {ω // σ.AcceptsAll c ℓ ω} = Fintype.card (σ.Coins c ℓ) :=
      Fintype.card_congr (Equiv.subtypeUnivEquiv h)
    exact_mod_cast this

lemma RScheme.accProb_le_one {S L : Type} (σ : RScheme S L) (c : Config S) (ℓ : c.V → L) :
    σ.accProb c ℓ ≤ 1 := Cslib.Probability.uprob_le_one _

lemma RScheme.accProb_nonneg {S L : Type} (σ : RScheme S L) (c : Config S) (ℓ : c.V → L) :
    0 ≤ σ.accProb c ℓ := Cslib.Probability.uprob_nonneg _

/-! ### Bounded bit strings -/

/-- The bit strings of length at most `m`. -/
def bitStrings (m : ℕ) : Finset (List Bool) :=
  (Finset.range (m + 1)).biUnion fun k => Finset.univ.image fun v : Fin k → Bool => List.ofFn v

lemma mem_bitStrings {m : ℕ} {l : List Bool} (hl : l.length ≤ m) : l ∈ bitStrings m := by
  simp only [bitStrings, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨l.length, by omega, l.get, List.ofFn_get l⟩

lemma card_bitStrings (m : ℕ) : (bitStrings m).card ≤ 2 ^ (m + 1) - 1 := by
  have hsum : ∀ m, ∑ k ∈ Finset.range (m + 1), 2 ^ k = 2 ^ (m + 1) - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
      rw [pow_succ 2 (m + 1)]
      omega
  calc (bitStrings m).card ≤ ∑ k ∈ Finset.range (m + 1),
        (Finset.univ.image fun v : Fin k → Bool => List.ofFn v).card := Finset.card_biUnion_le
    _ ≤ ∑ k ∈ Finset.range (m + 1), 2 ^ k := Finset.sum_le_sum fun k _ =>
        Finset.card_image_le.trans (by simp)
    _ = 2 ^ (m + 1) - 1 := hsum m

/-! ### Binary encoding of indices -/

/-- Binary digits (least significant first) as bits. -/
def encN (t : ℕ) : List Bool := (Nat.digits 2 t).map fun d => decide (d = 1)

/-- Decoding of `encN`. -/
def decN (l : List Bool) : ℕ := Nat.ofDigits 2 (l.map fun b => if b then 1 else 0)

lemma decN_encN (t : ℕ) : decN (encN t) = t := by
  unfold decN encN
  rw [List.map_map]
  conv_rhs => rw [← Nat.ofDigits_digits 2 t]
  congr 1
  conv_rhs => rw [← List.map_id (Nat.digits 2 t)]
  refine List.map_congr_left fun d hd => ?_
  have := Nat.digits_lt_base (by norm_num) hd
  simp only [Function.comp_apply, id]
  interval_cases d <;> simp

lemma length_encN (t : ℕ) : (encN t).length ≤ Nat.log 2 t + 1 := by
  unfold encN
  rw [List.length_map]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · rw [Nat.digits_len 2 t (by norm_num) ht.ne']

/-! ### Copies of a pattern and crossings (Definitions 4.1–4.2) -/

/-- `r` pairwise independent, port-preserving copies of a pattern graph `H` on `W` inside the
configuration `c` (the hypotheses of Proposition 4.3 / Theorem 4.4). Copy `i` is the subgraph
`H_i = emb i (H)`; `σ_i = emb i ∘ (emb 0)⁻¹`. -/
structure Copies {S : Type} (c : Config S) (r : ℕ) where
  /-- The vertices of the pattern. -/
  W : Type
  [finW : Fintype W]
  [deqW : DecidableEq W]
  /-- The pattern graph (its `s` edges are the edges of each copy). -/
  H : SimpleGraph W
  /-- The copies. -/
  emb : Fin r → W → c.V
  inj : ∀ i, Function.Injective (emb i)
  /-- Distinct copies are vertex-disjoint (Definition 4.1). -/
  disj : ∀ i j a b, i ≠ j → emb i a ≠ emb j b
  /-- Distinct copies are not joined by an edge of `c` (Definition 4.1). -/
  indep : ∀ i j a b, i ≠ j → ¬ c.Adj (emb i a) (emb j b)
  /-- Each copy is a subgraph of `c`. -/
  hom : ∀ i a b, H.Adj a b → c.Adj (emb i a) (emb i b)
  /-- The isomorphisms between the copies preserve port numbers. -/
  port_eq : ∀ i j a b, H.Adj a b → c.port (emb i a) (emb i b) = c.port (emb j a) (emb j b)

attribute [instance] Copies.finW Copies.deqW

namespace Copies

variable {S : Type} {c : Config S} {r : ℕ} (K : Copies c r)

/-- The number of edges `s` of the pattern. -/
noncomputable def s : ℕ := K.H.edgeFinset.card

/-- The swap `σ ∪ σ⁻¹` exchanging copy `i` and copy `j`. -/
noncomputable def swap (i j : Fin r) (v : c.V) : c.V :=
  if h : ∃ a, K.emb i a = v then K.emb j h.choose
  else if h' : ∃ a, K.emb j a = v then K.emb i h'.choose else v

lemma swap_emb_left (i j : Fin r) (a : K.W) : K.swap i j (K.emb i a) = K.emb j a := by
  have h : ∃ a', K.emb i a' = K.emb i a := ⟨a, rfl⟩
  rw [swap, dite_eq_left h, K.inj i h.choose_spec]

lemma swap_emb_right {i j : Fin r} (hij : i ≠ j) (a : K.W) :
    K.swap i j (K.emb j a) = K.emb i a := by
  have h : ¬ ∃ a', K.emb i a' = K.emb j a := by
    rintro ⟨a', h⟩; exact K.disj i j a' a hij h
  have h' : ∃ a', K.emb j a' = K.emb j a := ⟨a, rfl⟩
  rw [swap, dite_eq_right h, dite_eq_left h', K.inj j h'.choose_spec]

lemma swap_of_not_mem {i j : Fin r} {v : c.V} (hi : ∀ a, K.emb i a ≠ v)
    (hj : ∀ a, K.emb j a ≠ v) : K.swap i j v = v := by
  rw [swap, dite_eq_right (by push_neg; exact hi), dite_eq_right (by push_neg; exact hj)]

/-- `(x, w)` is an arc of copy `i` or of copy `j`. -/
def IsArc (i j : Fin r) (x w : c.V) : Prop :=
  ∃ k, (k = i ∨ k = j) ∧ ∃ a b, K.H.Adj a b ∧ K.emb k a = x ∧ K.emb k b = w

lemma isArc_symm {i j : Fin r} {x w : c.V} (h : K.IsArc i j x w) : K.IsArc i j w x := by
  obtain ⟨k, hk, a, b, hab, rfl, rfl⟩ := h
  exact ⟨k, hk, b, a, hab.symm, rfl, rfl⟩

/-- The new neighbour replacing `w` in the list of `x` after crossing copies `i` and `j`. -/
noncomputable def newNbr (i j : Fin r) (x w : c.V) : c.V :=
  if K.IsArc i j x w then K.swap i j w else w

end Copies

end Podc.RandomizedPLS
