import Papers.PODC2018.InteractiveDistributedProofs.LowerBound.Setup
import Papers.PODC2018.InteractiveDistributedProofs.LowerBound.ColourRefinement

/-!
# Lemma 3.11 is false

Lemma 3.11 of the paper claims: for every simple protocol deciding `Sym` on the dumbbell class `𝒢`
and all distinct `F₁, F₂ ∈ 𝓕`, `‖μ_A(F₁) − μ_A(F₂)‖₁ ≥ 2/3`, where `μ_A(F)` is the law of the random
set `𝓜_A(F, r)` under uniform challenges `r`. The paper's argument: by Corollary 3.10 the event
"`𝓜_A(·, r)` intersects `𝓜_B(F₁, r)`" has probability `≥ 2/3` for `F₁` and `≤ 1/3` for `F₂`. But this
"event" depends on `r` itself, so it is not an event on the domain of `μ_A`, which is only the
*marginal* law of `𝓜_A(F, r)`. A correct simple protocol can make all `μ_A(F)` equal by masking the
response with the challenges of the bridge nodes.

## The counterexample

Challenges are bits, responses are pairs of bits. Fix `v_A = a 0` and a test vertex `j₀ = 1`; the bit
`ι(F)` says whether `0 ∼ 1` in `F` (node `v_A` reads it off its view: is `a 1` among its neighbours?).
In `cexProtocol`:
* `x_A` (and `x_B`) accepts iff `M(x_A) = M(x_B)` and `m₁ ⊕ r_{x_A} = m₂ ⊕ r_{x_B}` for its response
  `m = (m₁, m₂)` — so the protocol is simple (`cexProtocol_isSimple`, Definition 6);
* `v_A` accepts iff `M(x_A)₁ = ι(F_A) ⊕ r_{x_A}`, `v_B` accepts iff `M(x_B)₂ = ι(F_B) ⊕ r_{x_B}`;
  all other nodes accept.

Then `𝓜_A(F, r) = {(ι(F) ⊕ r_{x_A}, ι(F) ⊕ r_{x_B})}` (`MA_eq`), whose law is uniform over the four
singletons whatever `ι(F)` is (`μA_eq`, by flipping the two bridge challenges). On `G(F, F)` the
honest prover is always accepted (`accProb_self`); on `G(F_A, F_B)` with `ι(F_A) ≠ ι(F_B)` all of
`v_A, x_A, v_B` accepting forces `ι(F_A) = ι(F_B)`, so every prover is always rejected
(`accProb_ne`).

With the 6-vertex asymmetric graphs `F₁` (edges `02 03 05 12 14 23`) and `F₂ = F₁ + {01}` (so
`ι(F₁) = 0`, `ι(F₂) = 1`), the family `𝓕 = {F₁, F₂}` satisfies the paper's requirements
(`cexFamily_ok`), `G(F₁, F₂)` and `G(F₂, F₁)` are asymmetric while `G(F, F)` is symmetric, the
protocol decides `Sym` on `𝒢` with perfect completeness and soundness (`cexPr_decides`), and
`μ_A(F₁) = μ_A(F₂)` (`μA_F₁_eq_F₂`): `lemma_3_11_false`.

Asymmetry and non-isomorphism are certified by colour refinement (`ColourRefinement.lean`), with
colour tables computed externally and checked by `decide +kernel`.
-/

open Finset Cslib.Probability

namespace Podc.InteractiveDistributedProofs.LowerBound

open DVert ColourRefinement

/-! ### Graphs given by edge lists, and Boolean adjacency of dumbbells -/

/-- Boolean adjacency on `Fin k` read off an edge list (pairs of naturals, either orientation). -/
def edgeB {k : ℕ} (E : List (ℕ × ℕ)) (i j : Fin k) : Bool :=
  (i != j) && (E.contains (i.val, j.val) || E.contains (j.val, i.val))

/-- The simple graph on `Fin k` with edge list `E`. -/
def ofEdges {k : ℕ} (E : List (ℕ × ℕ)) : SimpleGraph (Fin k) where
  Adj i j := edgeB E i j = true
  symm := ⟨fun i j h => by
    simp only [edgeB, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.or_eq_true] at h ⊢
    exact ⟨fun e => h.1 e.symm, h.2.symm⟩⟩
  loopless := ⟨fun i h => by simp [edgeB] at h⟩

instance {k : ℕ} (E : List (ℕ × ℕ)) : DecidableRel (ofEdges (k := k) E).Adj :=
  fun i j => inferInstanceAs (Decidable (edgeB E i j = true))

/-- Boolean adjacency of the dumbbell `G(F_A, F_B)`, given Boolean adjacencies `gA`, `gB` of the
sides. -/
def dAdjB {k : ℕ} (gA gB : Fin k → Fin k → Bool) (vA : Fin k) : DVert k → DVert k → Bool
  | a i, a j => gA i j
  | b i, b j => gB i j
  | a i, xA => decide (i = vA)
  | xA, a i => decide (i = vA)
  | xA, xB => true
  | xB, xA => true
  | b i, xB => decide (i = vA)
  | xB, b i => decide (i = vA)
  | _, _ => false

/-- The dumbbell's adjacency in terms of Boolean adjacencies of its sides. -/
theorem dumbbell_adj_iff {k : ℕ} {FA FB : SimpleGraph (Fin k)} {gA gB : Fin k → Fin k → Bool}
    (hA : ∀ i j, FA.Adj i j ↔ gA i j = true) (hB : ∀ i j, FB.Adj i j ↔ gB i j = true)
    (vA : Fin k) (u v : DVert k) : (dumbbell FA FB vA).Adj u v ↔ dAdjB gA gB vA u v = true := by
  cases u <;> cases v <;> simp [dumbbell, dAdj, dAdjB, hA, hB]

/-- Position of a dumbbell vertex in the colour tables. -/
def dIdx {k : ℕ} : DVert k → ℕ
  | a i => i
  | b i => k + i
  | xA => 2 * k
  | xB => 2 * k + 1

/-! ### The two concrete graphs -/

/-- Edge list of `F₁` (6 vertices, 6 edges). -/
def E₁ : List (ℕ × ℕ) := [(0, 2), (0, 3), (0, 5), (1, 2), (1, 4), (2, 3)]
/-- Edge list of `F₂` = `F₁` plus the edge `{0, 1}`. -/
def E₂ : List (ℕ × ℕ) := [(0, 1), (0, 2), (0, 3), (0, 5), (1, 2), (1, 4), (2, 3)]

/-- Boolean adjacency of `F₁`. -/
def g₁ : Fin 6 → Fin 6 → Bool := edgeB E₁
/-- Boolean adjacency of `F₂`. -/
def g₂ : Fin 6 → Fin 6 → Bool := edgeB E₂

/-- The graph `F₁`. -/
def F₁ : SimpleGraph (Fin 6) := ofEdges E₁
/-- The graph `F₂`. -/
def F₂ : SimpleGraph (Fin 6) := ofEdges E₂

/-- Joint colour refinement of `F₁ ⊔ F₂`, restricted to `F₁`. -/
def t₁ : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0],
    [2, 1, 2, 1, 0, 0],
    [6, 3, 8, 4, 0, 1],
    [7, 4, 9, 5, 0, 1]]
/-- Joint colour refinement of `F₁ ⊔ F₂`, restricted to `F₂`. -/
def t₂ : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0],
    [3, 2, 2, 1, 0, 0],
    [10, 7, 9, 5, 1, 2],
    [11, 8, 10, 6, 2, 3]]
/-- Colour refinement of `G(F₁, F₂)` (`v_A = 0`). -/
def t₁₂ : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [3, 1, 2, 1, 0, 0, 4, 2, 2, 1, 0, 0, 1, 1],
    [12, 4, 10, 7, 0, 2, 13, 9, 11, 8, 1, 3, 5, 6]]
/-- Colour refinement of `G(F₂, F₁)` (`v_A = 0`). -/
def t₂₁ : List (List ℕ) :=
  [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [4, 2, 2, 1, 0, 0, 3, 1, 2, 1, 0, 0, 1, 1],
    [13, 9, 11, 8, 1, 3, 12, 4, 10, 7, 0, 2, 6, 5]]

/-- Colour-refinement certificate for `F₁`. -/
theorem cert_F₁ : ∀ j < 3, RefineStep g₁ g₁
    (tbl (fun i : Fin 6 => i.val) t₁ j) (tbl (fun i : Fin 6 => i.val) t₁ (j + 1))
    (tbl (fun i : Fin 6 => i.val) t₁ j) (tbl (fun i : Fin 6 => i.val) t₁ (j + 1)) := by
  decide +kernel

/-- Colour-refinement certificate for `G(F₁, F₂)`. -/
theorem cert_G₁₂ : ∀ j < 2, RefineStep (dAdjB g₁ g₂ 0) (dAdjB g₁ g₂ 0)
    (tbl dIdx t₁₂ j) (tbl dIdx t₁₂ (j + 1)) (tbl dIdx t₁₂ j) (tbl dIdx t₁₂ (j + 1)) := by
  decide +kernel

/-! ### The protocol -/

section Protocol

variable {k : ℕ}

/-- The bridge predicate `f_{x_A} = f_{x_B}` of the counterexample: with `r_A, r_B` the challenges of
the two bridge nodes (both visible to each of them), the response `m = (m₁, m₂)` is accepted iff
`m₁ ⊕ r_A = m₂ ⊕ r_B`. -/
def bridgeOK (cv : DVert k → Option Bool) (m : Bool × Bool) : Prop :=
  match cv xA, cv xB with
  | some ca, some cb => (m.1 ^^ ca) = (m.2 ^^ cb)
  | _, _ => False

/-- The counterexample protocol (challenges `Bool`, responses `Bool × Bool`), parametrized by a vertex
`j₀`; the dumbbell's bridge is attached at `v_A = a vA`, `v_B = b vA` with `j₀ ≠ vA`.

* `x_A` accepts iff `m₁ ⊕ r_{x_A} = m₂ ⊕ r_{x_B}` for its response `m` and `M(x_A) = M(x_B)`;
  `x_B` symmetrically.
* A node `a i` that sees `x_A` (that is, `v_A`) computes the bit `ι_A` = "is `a j₀` my neighbour"
  from its view and accepts iff `M(x_A)₁ = ι_A ⊕ r_{x_A}`; a node `b i` that sees `x_B` accepts iff
  `M(x_B)₂ = ι_B ⊕ r_{x_B}`, where `ι_B` = "is `b j₀` my neighbour". All other nodes accept.

Neighbourhood tests read the `some` positions of the view (cf. `viewNbhd_mask`). -/
def cexProtocol (j₀ : Fin k) : AMProtocol (DVert k) Bool (Bool × Bool) where
  out
    | xA, w => match w xA, w xB with
      | some (ca, ma), some (cb, mb) => (ma.1 ^^ ca) = (ma.2 ^^ cb) ∧ ma = mb
      | _, _ => False
    | xB, w => match w xA, w xB with
      | some (ca, ma), some (cb, mb) => (mb.1 ^^ ca) = (mb.2 ^^ cb) ∧ mb = ma
      | _, _ => False
    | a _, w => match w xA with
      | some (ca, ma) => ma.1 = ((w (a j₀)).isSome ^^ ca)
      | none => True
    | b _, w => match w xB with
      | some (cb, mb) => mb.2 = ((w (b j₀)).isSome ^^ cb)
      | none => True

variable {FA FB : SimpleGraph (Fin k)} {vA j₀ : Fin k}

open Classical in
/-- The local view on a dumbbell, unfolded. -/
theorem mask_dumbbell {α : Type*} (v u : DVert k) (x : DVert k → α) :
    mask (dumbbell FA FB vA) v x u = if u = v ∨ dAdj FA FB vA v u then some (x u) else none := by
  unfold mask
  simp only [mem_cnbhd]
  exact if_congr Iff.rfl rfl rfl

/-- The decision of `x_A`. -/
theorem out_xA (c : DVert k → Bool) (Mr : DVert k → Bool × Bool) :
    (cexProtocol j₀).out xA (mask (dumbbell FA FB vA) xA fun u => (c u, Mr u)) ↔
      ((Mr xA).1 ^^ c xA) = ((Mr xA).2 ^^ c xB) ∧ Mr xA = Mr xB := by
  simp [cexProtocol, mask_dumbbell, dAdj]

/-- The decision of `x_B`. -/
theorem out_xB (c : DVert k → Bool) (Mr : DVert k → Bool × Bool) :
    (cexProtocol j₀).out xB (mask (dumbbell FA FB vA) xB fun u => (c u, Mr u)) ↔
      ((Mr xB).1 ^^ c xA) = ((Mr xB).2 ^^ c xB) ∧ Mr xB = Mr xA := by
  simp [cexProtocol, mask_dumbbell, dAdj]

/-- `f_{x_A}` on the view of `x_A`. -/
theorem bridgeOK_xA (c : DVert k → Bool) (m : Bool × Bool) :
    bridgeOK (mask (dumbbell FA FB vA) xA c) m ↔ (m.1 ^^ c xA) = (m.2 ^^ c xB) := by
  simp [bridgeOK, mask_dumbbell, dAdj]

/-- `f_{x_B}` on the view of `x_B`. -/
theorem bridgeOK_xB (c : DVert k → Bool) (m : Bool × Bool) :
    bridgeOK (mask (dumbbell FA FB vA) xB c) m ↔ (m.1 ^^ c xA) = (m.2 ^^ c xB) := by
  simp [bridgeOK, mask_dumbbell, dAdj]

/-- The decision of a node `a i`: only `v_A = a vA` checks something. -/
theorem out_a (hj : j₀ ≠ vA) {ι : Bool} (hι : FA.Adj vA j₀ ↔ ι = true) (i : Fin k)
    (c : DVert k → Bool) (Mr : DVert k → Bool × Bool) :
    (cexProtocol j₀).out (a i) (mask (dumbbell FA FB vA) (a i) fun u => (c u, Mr u)) ↔
      (i = vA → (Mr xA).1 = (ι ^^ c xA)) := by
  by_cases hi : i = vA
  · subst hi
    cases ι <;> simp_all [cexProtocol, mask_dumbbell, dAdj]
  · simp [cexProtocol, mask_dumbbell, dAdj, hi]

/-- The decision of a node `b i`: only `v_B = b vA` checks something. -/
theorem out_b (hj : j₀ ≠ vA) {ι : Bool} (hι : FB.Adj vA j₀ ↔ ι = true) (i : Fin k)
    (c : DVert k → Bool) (Mr : DVert k → Bool × Bool) :
    (cexProtocol j₀).out (b i) (mask (dumbbell FA FB vA) (b i) fun u => (c u, Mr u)) ↔
      (i = vA → (Mr xB).2 = (ι ^^ c xB)) := by
  by_cases hi : i = vA
  · subst hi
    cases ι <;> simp_all [cexProtocol, mask_dumbbell, dAdj]
  · simp [cexProtocol, mask_dumbbell, dAdj, hi]

/-- The counterexample protocol is simple (Definition 6), with `f_{x_A} = f_{x_B} = bridgeOK`, on
every dumbbell (in particular on every class `𝒢` of dumbbells). -/
theorem cexProtocol_isSimple (𝓕 : Finset (SimpleGraph (Fin k))) (vA j₀ : Fin k) :
    IsSimple (cexProtocol j₀) 𝓕 vA bridgeOK bridgeOK := by
  rintro G ⟨FA, -, FB, -, rfl⟩ c Mr
  rw [out_xA, out_xB, bridgeOK_xA, bridgeOK_xB]
  exact ⟨Iff.rfl, Iff.rfl⟩

/-- **`𝓜_A(F, r)` is a singleton**: if `ι` is the bit "`vA` is adjacent to `j₀` in `F`", then
`𝓜_A(F, r) = {(ι ⊕ r_{x_A}, ι ⊕ r_{x_B})}`. -/
theorem MA_eq (hj : j₀ ≠ vA) {F : SimpleGraph (Fin k)} {ι : Bool} (hι : F.Adj vA j₀ ↔ ι = true)
    (c : DVert k → Bool) :
    MA (cexProtocol j₀) vA bridgeOK F c = {((ι ^^ c xA), (ι ^^ c xB))} := by
  ext m
  simp only [MA, Set.mem_ofPred_eq, Set.mem_singleton_iff, out_a hj hι, bridgeOK_xA]
  constructor
  · rintro ⟨Mr, rfl, hacc, hf⟩
    have h1 := hacc vA rfl
    rw [h1] at hf
    have h2 : (Mr xA).2 = (ι ^^ c xB) := by
      have := congrArg (· ^^ c xB) hf
      simpa [Bool.xor_assoc] using this.symm
    exact Prod.ext h1 h2
  · rintro rfl
    exact ⟨fun _ => ((ι ^^ c xA), (ι ^^ c xB)), rfl, fun _ _ => rfl, by simp⟩

/-- Uniform challenges: flipping the challenges of both bridge nodes. -/
def flipBridge (c : DVert k → Bool) : DVert k → Bool :=
  fun u => decide (u = xA ∨ u = xB) ^^ c u

/-- Flipping is an involution. -/
theorem flipBridge_involutive : Function.Involutive (flipBridge (k := k)) := by
  intro c
  funext u
  simp [flipBridge]

/-- The law of `{(ι ⊕ r_{x_A}, ι ⊕ r_{x_B})}` does not depend on `ι`. -/
theorem uprob_singleton_xor (ι : Bool) (S : Set (Bool × Bool)) :
    uprob (fun c : DVert k → Bool => ({((ι ^^ c xA), (ι ^^ c xB))} : Set (Bool × Bool)) = S) =
      uprob (fun c : DVert k → Bool => ({(c xA, c xB)} : Set (Bool × Bool)) = S) := by
  cases ι
  · simp
  · unfold uprob
    congr 2
    refine Nat.card_congr ((flipBridge_involutive.toPerm _).subtypeEquiv fun c => ?_)
    simp [flipBridge]

/-- **`μ_A(F)` is the same for every `F`** (on which the bit `ι` is defined): the uniform law of
`{(r_{x_A}, r_{x_B})}`. -/
theorem μA_eq (hj : j₀ ≠ vA) {F : SimpleGraph (Fin k)} {ι : Bool} (hι : F.Adj vA j₀ ↔ ι = true) :
    μA (cexProtocol j₀) vA bridgeOK F =
      fun S => uprob (fun c : DVert k → Bool => ({(c xA, c xB)} : Set (Bool × Bool)) = S) := by
  funext S
  simp only [μA, MA_eq hj hι]
  exact uprob_singleton_xor ι S

/-- **Perfect completeness** on `G(F, F)`: the honest prover sends `(ι ⊕ r_{x_A}, ι ⊕ r_{x_B})` to
every node, and all nodes accept for every challenge vector. -/
theorem accProb_self (hj : j₀ ≠ vA) {F : SimpleGraph (Fin k)} {ι : Bool}
    (hι : F.Adj vA j₀ ↔ ι = true) :
    (cexProtocol j₀).accProb (dumbbell F F vA) (fun c _ => ((ι ^^ c xA), (ι ^^ c xB))) = 1 := by
  have hacc : (cexProtocol j₀).Accepts (dumbbell F F vA) (fun c _ => ((ι ^^ c xA), (ι ^^ c xB))) =
      fun _ => True := by
    funext c
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    rintro (i | i | - | -)
    · exact (out_a hj hι i c _).2 fun _ => rfl
    · exact (out_b hj hι i c _).2 fun _ => rfl
    · refine (out_xA c _).2 ⟨?_, rfl⟩
      simp
    · refine (out_xB c _).2 ⟨?_, rfl⟩
      simp
  rw [AMProtocol.accProb, hacc, uprob_true]
  simp

/-- **Perfect soundness** on `G(F_A, F_B)` when the bits `ι_A ≠ ι_B` differ: no response vector makes
`v_A`, `x_A` and `v_B` accept simultaneously. -/
theorem accProb_ne (hj : j₀ ≠ vA) {ιA ιB : Bool} (hA : FA.Adj vA j₀ ↔ ιA = true)
    (hB : FB.Adj vA j₀ ↔ ιB = true) (hne : ιA ≠ ιB) (P : (DVert k → Bool) → DVert k → Bool × Bool) :
    (cexProtocol j₀).accProb (dumbbell FA FB vA) P = 0 := by
  have hacc : (cexProtocol j₀).Accepts (dumbbell FA FB vA) P = fun _ => False := by
    funext c
    refine propext ⟨fun h => ?_, False.elim⟩
    have h1 := (out_a hj hA vA c _).1 (h (a vA)) rfl
    have h2 := (out_b hj hB vA c _).1 (h (b vA)) rfl
    obtain ⟨h3, h4⟩ := (out_xA c _).1 (h xA)
    rw [← h4] at h2
    rw [h1, h2] at h3
    simp at h3
    exact hne h3
  rw [AMProtocol.accProb, hacc, uprob_false]

end Protocol

/-! ### Graph facts: asymmetry, non-isomorphism, symmetry of `G(F, F)` -/

section Graphs

/-- A graph with Boolean adjacency `g` is asymmetric if a colour-refinement chain for `g` ends in an
injective colouring. -/
theorem not_sym_of_refine {V : Type*} [Fintype V] {G : SimpleGraph V} {g : V → V → Bool}
    (hg : ∀ u v, G.Adj u v ↔ g u v = true) (c : ℕ → V → ℕ) (n : ℕ) (h0 : ∀ v w, c 0 v = c 0 w)
    (hs : ∀ j < n, RefineStep g g (c j) (c (j + 1)) (c j) (c (j + 1)))
    (hinj : ∀ u v, c n u = c n v → u = v) : ¬ Sym G := by
  rintro ⟨ρ, ⟨hb, hadj⟩, hne⟩
  exact hne (eq_id_of_refine c n h0 hs hinj hb fun u v => Bool.eq_iff_iff.2 (by
    rw [← hg, ← hg]; exact hadj u v))

/-- The swap `a i ↔ b i`, `x_A ↔ x_B`. -/
def swapAB {k : ℕ} : DVert k → DVert k
  | a i => b i
  | b i => a i
  | xA => xB
  | xB => xA

/-- `G(F, F)` is symmetric: the swap of the two sides is a non-trivial automorphism. -/
theorem sym_dumbbell_self {k : ℕ} (F : SimpleGraph (Fin k)) (vA : Fin k) :
    Sym (dumbbell F F vA) := by
  refine ⟨swapAB, ⟨Function.Involutive.bijective fun u => by cases u <;> rfl, fun u v => ?_⟩,
    fun h => ?_⟩
  · cases u <;> cases v <;> simp [swapAB, dumbbell, dAdj]
  · have := congrFun h xA
    simp [swapAB] at this

/-- `F₁`'s adjacency is `g₁`. -/
theorem F₁_adj (i j : Fin 6) : F₁.Adj i j ↔ g₁ i j = true := Iff.rfl
/-- `F₂`'s adjacency is `g₂`. -/
theorem F₂_adj (i j : Fin 6) : F₂.Adj i j ↔ g₂ i j = true := Iff.rfl

/-- `F₁` is asymmetric. -/
theorem not_sym_F₁ : ¬ Sym F₁ :=
  not_sym_of_refine F₁_adj (tbl (fun i : Fin 6 => i.val) t₁) 3 (by decide) cert_F₁ (by decide)

/-- Colour-refinement certificate for `F₂`. -/
theorem cert_F₂ : ∀ j < 3, RefineStep g₂ g₂
    (tbl (fun i : Fin 6 => i.val) t₂ j) (tbl (fun i : Fin 6 => i.val) t₂ (j + 1))
    (tbl (fun i : Fin 6 => i.val) t₂ j) (tbl (fun i : Fin 6 => i.val) t₂ (j + 1)) := by
  decide +kernel

/-- `F₂` is asymmetric. -/
theorem not_sym_F₂ : ¬ Sym F₂ :=
  not_sym_of_refine F₂_adj (tbl (fun i : Fin 6 => i.val) t₂) 3 (by decide) cert_F₂ (by decide)

/-- Joint colour-refinement certificate for `F₁` and `F₂`. -/
theorem cert_F₁₂ : ∀ j < 3, RefineStep g₁ g₂
    (tbl (fun i : Fin 6 => i.val) t₁ j) (tbl (fun i : Fin 6 => i.val) t₁ (j + 1))
    (tbl (fun i : Fin 6 => i.val) t₂ j) (tbl (fun i : Fin 6 => i.val) t₂ (j + 1)) := by
  decide +kernel

/-- `F₁` and `F₂` are not isomorphic (they even have different numbers of edges). -/
theorem not_iso_F₁_F₂ : IsEmpty (F₁ ≃g F₂) := by
  refine ⟨fun φ => not_iso_of_refine (tbl (fun i : Fin 6 => i.val) t₁)
    (tbl (fun i : Fin 6 => i.val) t₂) 3 (by decide) cert_F₁₂ (by decide) φ.bijective
    fun u v => Bool.eq_iff_iff.2 ?_⟩
  rw [← F₁_adj, ← F₂_adj]
  exact φ.map_adj_iff

/-- Colour-refinement certificate for `G(F₂, F₁)`. -/
theorem cert_G₂₁ : ∀ j < 2, RefineStep (dAdjB g₂ g₁ 0) (dAdjB g₂ g₁ 0)
    (tbl dIdx t₂₁ j) (tbl dIdx t₂₁ (j + 1)) (tbl dIdx t₂₁ j) (tbl dIdx t₂₁ (j + 1)) := by
  decide +kernel

/-- `G(F₁, F₂)` is asymmetric. -/
theorem not_sym_G₁₂ : ¬ Sym (dumbbell F₁ F₂ 0) :=
  not_sym_of_refine (dumbbell_adj_iff F₁_adj F₂_adj 0) (tbl dIdx t₁₂) 2 (by decide) cert_G₁₂
    (by decide)

/-- `G(F₂, F₁)` is asymmetric. -/
theorem not_sym_G₂₁ : ¬ Sym (dumbbell F₂ F₁ 0) :=
  not_sym_of_refine (dumbbell_adj_iff F₂_adj F₁_adj 0) (tbl dIdx t₂₁) 2 (by decide) cert_G₂₁
    (by decide)

/-- In `F₁`, `0` and `1` are not adjacent. -/
theorem F₁_adj_01 : F₁.Adj 0 1 ↔ false = true := (F₁_adj 0 1).trans (by decide)
/-- In `F₂`, `0` and `1` are adjacent. -/
theorem F₂_adj_01 : F₂.Adj 0 1 ↔ true = true := (F₂_adj 0 1).trans (by decide)

/-- `F₁ ≠ F₂`. -/
theorem F₁_ne_F₂ : F₁ ≠ F₂ := by
  intro h
  have := F₂_adj_01.2 rfl
  rw [← h] at this
  exact absurd (F₁_adj_01.1 this) (by decide)

end Graphs

/-! ### The counterexample -/

section Main

open Classical in
/-- The family `𝓕 = {F₁, F₂}`. -/
noncomputable def cexFamily : Finset (SimpleGraph (Fin 6)) := {F₁, F₂}

/-- Membership in `𝓕`. -/
theorem mem_cexFamily {F : SimpleGraph (Fin 6)} : F ∈ cexFamily ↔ F = F₁ ∨ F = F₂ := by
  classical
  simp [cexFamily]

/-- `𝓕 = {F₁, F₂}` satisfies the paper's requirements: asymmetric, pairwise non-isomorphic graphs. -/
theorem cexFamily_ok : FamilyOK cexFamily := by
  refine ⟨fun F hF => ?_, fun F hF F' hF' hne => ?_⟩
  · rcases mem_cexFamily.1 hF with rfl | rfl
    · exact not_sym_F₁
    · exact not_sym_F₂
  · rcases mem_cexFamily.1 hF with rfl | rfl <;> rcases mem_cexFamily.1 hF' with rfl | rfl
    · exact absurd rfl hne
    · exact not_iso_F₁_F₂
    · exact ⟨fun φ => not_iso_F₁_F₂.false φ.symm⟩
    · exact absurd rfl hne

/-- The counterexample protocol on `𝒢 = {G(F_A, F_B) : F_A, F_B ∈ {F₁, F₂}}`: bridge at `v_A = 0`,
test vertex `j₀ = 1`. -/
def cexPr : AMProtocol (DVert 6) Bool (Bool × Bool) := cexProtocol 1

/-- The test vertex differs from `v_A`. -/
theorem one_ne_zero_fin6 : (1 : Fin 6) ≠ 0 := by decide

/-- **The protocol decides `Sym` on `𝒢` (with perfect completeness and soundness).** On `G(F, F)`
(symmetric) the honest prover is accepted with probability `1`; on `G(F₁, F₂)` and `G(F₂, F₁)`
(asymmetric) every prover is accepted with probability `0`. -/
theorem cexPr_decides : cexPr.Decides (InClass cexFamily 0) Sym := by
  rintro G ⟨FA, hA, FB, hB, rfl⟩
  rcases mem_cexFamily.1 hA with rfl | rfl <;> rcases mem_cexFamily.1 hB with rfl | rfl
  · refine ⟨fun _ => ⟨fun c _ => ((false ^^ c xA), (false ^^ c xB)), ?_⟩,
      fun h => absurd (sym_dumbbell_self _ _) h⟩
    rw [cexPr, accProb_self one_ne_zero_fin6 F₁_adj_01]
    norm_num
  · refine ⟨fun h => absurd h not_sym_G₁₂, fun _ P => ?_⟩
    rw [cexPr, accProb_ne one_ne_zero_fin6 F₁_adj_01 F₂_adj_01 (by decide)]
    norm_num
  · refine ⟨fun h => absurd h not_sym_G₂₁, fun _ P => ?_⟩
    rw [cexPr, accProb_ne one_ne_zero_fin6 F₂_adj_01 F₁_adj_01 (by decide)]
    norm_num
  · refine ⟨fun _ => ⟨fun c _ => ((true ^^ c xA), (true ^^ c xB)), ?_⟩,
      fun h => absurd (sym_dumbbell_self _ _) h⟩
    rw [cexPr, accProb_self one_ne_zero_fin6 F₂_adj_01]
    norm_num

/-- `μ_A(F₁) = μ_A(F₂)`. -/
theorem μA_F₁_eq_F₂ : μA cexPr 0 bridgeOK F₁ = μA cexPr 0 bridgeOK F₂ := by
  rw [cexPr, μA_eq one_ne_zero_fin6 F₁_adj_01, μA_eq one_ne_zero_fin6 F₂_adj_01]

/-- `‖μ − μ‖₁ = 0`. -/
theorem l1_self {M : Type*} [Fintype M] (μ : Set M → ℝ) : l1 μ μ = 0 := by
  simp [l1]

/-- **Lemma 3.11 is false.** There are a family `𝓕` of asymmetric, pairwise non-isomorphic graphs, a
simple dAM protocol (Definition 6) deciding `Sym` on the dumbbell class `𝒢` built from `𝓕` (even with
perfect completeness and soundness, and with 1-bit challenges and 2-bit responses), and two distinct
`F₁, F₂ ∈ 𝓕` with `μ_A(F₁) = μ_A(F₂)`; in particular `‖μ_A(F₁) − μ_A(F₂)‖₁ = 0 < 2/3`. -/
theorem lemma_3_11_false : ∃ (k : ℕ) (𝓕 : Finset (SimpleGraph (Fin k))) (vA : Fin k)
    (pr : AMProtocol (DVert k) Bool (Bool × Bool))
    (fA fB : (DVert k → Option Bool) → Bool × Bool → Prop),
    FamilyOK 𝓕 ∧ IsSimple pr 𝓕 vA fA fB ∧ pr.Decides (InClass 𝓕 vA) Sym ∧
      (∃ F₁ ∈ 𝓕, ∃ F₂ ∈ 𝓕, F₁ ≠ F₂ ∧ μA pr vA fA F₁ = μA pr vA fA F₂) ∧
      ¬ Lemma311Claim pr 𝓕 vA fA := by
  have h₁ : F₁ ∈ cexFamily := mem_cexFamily.2 (Or.inl rfl)
  have h₂ : F₂ ∈ cexFamily := mem_cexFamily.2 (Or.inr rfl)
  refine ⟨6, cexFamily, 0, cexPr, bridgeOK, bridgeOK, cexFamily_ok,
    cexProtocol_isSimple _ _ _, cexPr_decides, ⟨F₁, h₁, F₂, h₂, F₁_ne_F₂, μA_F₁_eq_F₂⟩,
    fun h => ?_⟩
  have := h F₁ h₁ F₂ h₂ F₁_ne_F₂
  rw [μA_F₁_eq_F₂, l1_self] at this
  norm_num at this

end Main

end Podc.InteractiveDistributedProofs.LowerBound
