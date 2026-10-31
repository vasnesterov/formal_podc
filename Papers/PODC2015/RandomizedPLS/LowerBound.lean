import Papers.PODC2015.RandomizedPLS.Restrict

/-!
# The crossing lower-bound tool: deterministic schemes and one-sided randomized schemes

* `prop_4_3`: Proposition 4.3, in the form its proof establishes: with labels of at most `κ` bits on
  `G` and `(2^(κ+1) - 1)^(2s) < r`, there are two copies `i ≠ j` such that the verifier accepts the
  crossing `σ_ij₁(G)` with the labels of `G` iff it accepts `G`.
* `thm_4_4`: Theorem 4.4 for a *legal* `G` whose crossings are all illegal (the only case the paper
  proves and uses): `r ≤ (2^(κ+1) - 1)^(2s)`, i.e. `κ + 1 ≥ log₂ r / (2s)` (`thm_4_4_log`).
  The crossings may be outside `F` as long as a union of their components is an illegal member of `F`
  (`Refuted`), as needed in Section 5.
* `prop_4_8`: Proposition 4.8 (one-sided RPLS), with certificates of at most `κ` bits:
  `r ≤ (2^(2^(κ+1) - 1))^(2s)`, i.e. `2s(2^(κ+1) - 1) ≥ log₂ r`.

The paper's Theorems 4.4 and 4.7 also allow `P(G) = FALSE` (with all crossings legal); that case is
false, see `Counterexample.lean`.
-/

namespace Podc.RandomizedPLS

open Classical

variable {S : Type}

/-- A crossing *refutes* `(F, P)` if it is an illegal member of `F`, or if a union of its connected
components (a set of nodes closed under taking neighbours) is. -/
def Refuted (F P : Config S → Prop) (c' : Config S) : Prop :=
  (F c' ∧ ¬ P c') ∨
    ∃ (U : Set c'.V) (hU : ∀ v ∈ U, ∀ w ∈ c'.nbrs v, w ∈ U),
      F (c'.restrict U hU) ∧ ¬ P (c'.restrict U hU)

namespace Copies

variable {c : Config S} {r : ℕ} (K : Copies c r)

/-- The vertices of the pattern that are incident to an edge. -/
noncomputable def supp : Finset K.W := Finset.univ.filter fun a => ∃ b, K.H.Adj a b

/-- A pattern with `s` edges has at most `2s` non-isolated vertices. -/
lemma card_supp_le : K.supp.card ≤ 2 * K.s := by
  classical
  have h := K.H.sum_degrees_eq_twice_card_edges
  rw [Copies.s, ← h]
  calc K.supp.card = ∑ a ∈ K.supp, 1 := by simp
    _ ≤ ∑ a ∈ K.supp, K.H.degree a := Finset.sum_le_sum fun a ha => by
        obtain ⟨b, hb⟩ := (Finset.mem_filter.1 ha).2
        exact Finset.card_pos.2 ⟨b, by simpa using hb⟩
    _ ≤ ∑ a, K.H.degree a := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

lemma s_eq_zero_of_supp (h : K.supp.card = 0) : K.s = 0 := by
  by_contra hs
  obtain ⟨e, he⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hs)
  induction e using Sym2.ind with
  | _ a b =>
    have hab : K.H.Adj a b := by simpa using he
    have : a ∈ K.supp := Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab⟩
    rw [Finset.card_eq_zero] at h
    simp [h] at this

/-- **Pigeonhole for labels.** If all labels have at most `κ` bits and `(2^(κ+1)-1)^(2s) < r`, two
distinct copies carry the same labels on the non-isolated vertices of the pattern. -/
lemma exists_same_labels {α : Type*} (ℓ : c.V → α) (A : Finset α) (hA : ∀ v, ℓ v ∈ A)
    (hr : A.card ^ (2 * K.s) < r) :
    ∃ i j, i ≠ j ∧ ∀ a b, K.H.Adj a b → ℓ (K.emb i a) = ℓ (K.emb j a) := by
  let f : Fin r → (K.supp → A) := fun i a => ⟨ℓ (K.emb i a.1), hA _⟩
  have hcard : Fintype.card (K.supp → A) < Fintype.card (Fin r) := by
    rw [Fintype.card_fun, Fintype.card_coe, Fintype.card_coe, Fintype.card_fin]
    refine lt_of_le_of_lt ?_ hr
    rcases Nat.eq_zero_or_pos A.card with h0 | hpos
    · rw [h0]
      rcases Nat.eq_zero_or_pos K.supp.card with h1 | h1
      · rw [h1, K.s_eq_zero_of_supp h1]
      · rw [zero_pow h1.ne']; exact Nat.zero_le _
    · exact Nat.pow_le_pow_right hpos K.card_supp_le
  obtain ⟨i, j, hij, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  refine ⟨i, j, hij, fun a b hab => ?_⟩
  have := congrFun hf ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab⟩⟩
  exact congrArg Subtype.val this

end Copies

/-- **Proposition 4.3 of [BFP15]** (the statement its proof establishes). Let `G` carry labels of at
most `κ` bits and contain `r` pairwise independent port-preserving copies of a pattern with `s`
edges. If `(2^(κ+1) - 1)^(2s) < r`, then there are copies `i ≠ j` such that the verifier accepts
`G` iff it accepts the crossing `(σ_j ∘ σ_i⁻¹)₁(G)`, both with the labels of `G`. -/
theorem prop_4_3 (ver : Verifier S) {c : Config S} {r : ℕ} (K : Copies c r)
    (ℓ : c.V → List Bool) (κ : ℕ) (hκ : ∀ v, (ℓ v).length ≤ κ)
    (hr : (2 ^ (κ + 1) - 1) ^ (2 * K.s) < r) :
    ∃ i j, ∃ hij : i ≠ j, Accepts ver (K.cross i j hij) ℓ ↔ Accepts ver c ℓ := by
  obtain ⟨i, j, hij, h⟩ := K.exists_same_labels ℓ (bitStrings κ) (fun v => mem_bitStrings (hκ v))
    (lt_of_le_of_lt (Nat.pow_le_pow_left (card_bitStrings κ) _) hr)
  exact ⟨i, j, hij, K.accepts_cross_iff hij ℓ h⟩

/-- Deterministic acceptance of a refuting crossing contradicts soundness. -/
lemma not_accepts_of_refuted {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} (h : IsPLS ver prover F P) {c' : Config S} (hc' : Refuted F P c')
    (ℓ : c'.V → List Bool) : ¬ Accepts ver c' ℓ := by
  intro hacc
  rcases hc' with ⟨hF, hP⟩ | ⟨U, hU, hF, hP⟩
  · exact h.2 c' hF hP ℓ hacc
  · exact h.2 _ hF hP _ (accepts_restrict hU hacc)

/-- **Theorem 4.4 of [BFP15]** (for `P(G) = TRUE`, the case the paper proves and uses; the case
`P(G) = FALSE` is false, see `thm_4_4_false`). Let `(ver, prover)` be a PLS for `(F, P)`, and let
`G ∈ F` be legal, with labels of at most `κ` bits, containing `r` pairwise independent
port-preserving copies of a pattern with `s` edges such that every crossing of two copies is
refuted. Then `r ≤ (2^(κ+1) - 1)^(2s)`. -/
theorem thm_4_4 {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} (h : IsPLS ver prover F P) {c : Config S} (hF : F c) (hP : P c)
    {r : ℕ} (K : Copies c r) (κ : ℕ) (hκ : ∀ v, (prover c v).length ≤ κ)
    (hbad : ∀ i j (hij : i ≠ j), Refuted F P (K.cross i j hij)) :
    r ≤ (2 ^ (κ + 1) - 1) ^ (2 * K.s) := by
  by_contra hr
  obtain ⟨i, j, hij, hiff⟩ := prop_4_3 ver K (prover c) κ hκ (not_le.1 hr)
  exact not_accepts_of_refuted h (hbad i j hij) _ (hiff.2 (h.1 c hF hP))

/-- Theorem 4.4 in logarithmic form: the verification complexity is at least `log₂ r / (2s) - 1`,
i.e. `Ω(log r / s)`. -/
theorem thm_4_4_log {ver : Verifier S} {prover : ∀ c : Config S, c.V → List Bool}
    {F P : Config S → Prop} (h : IsPLS ver prover F P) {c : Config S} (hF : F c) (hP : P c)
    {r : ℕ} (K : Copies c r) (κ : ℕ) (hκ : ∀ v, (prover c v).length ≤ κ)
    (hbad : ∀ i j (hij : i ≠ j), Refuted F P (K.cross i j hij)) :
    Real.logb 2 r ≤ 2 * K.s * (κ + 1) := by
  have h1 := thm_4_4 h hF hP K κ hκ hbad
  have h2 : r ≤ 2 ^ (2 * K.s * (κ + 1)) := by
    calc r ≤ (2 ^ (κ + 1) - 1) ^ (2 * K.s) := h1
      _ ≤ (2 ^ (κ + 1)) ^ (2 * K.s) := Nat.pow_le_pow_left (Nat.sub_le _ _) _
      _ = 2 ^ (2 * K.s * (κ + 1)) := by rw [← pow_mul, mul_comm]
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0; simp; positivity
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)]
    exact_mod_cast (by exact_mod_cast h2 : (r : ℝ) ≤ (2 : ℝ) ^ (2 * K.s * (κ + 1)))

/-! ### One-sided randomized schemes -/

namespace RScheme

variable {L : Type} (σ : RScheme S L)

/-- The support of the certificate sent by a node with state `s`, label `ℓ` and degree `d` on port
`p`, restricted to bit strings of length `≤ κ`. -/
noncomputable def supp (κ : ℕ) (s : S) (ℓ : L) (d p : ℕ) : Finset (List Bool) :=
  (bitStrings κ).filter fun γ => ∃ ω : σ.Ω s ℓ d, σ.cert s ℓ d ω p = γ

end RScheme

/-- **Proposition 4.8 of [BFP15]** (one-sided RPLS, explicit form). Let `(σ, prover)` be a one-sided
RPLS for `(F, P)`, `G ∈ F` legal, with certificates of at most `κ` bits on `G`, containing `r`
pairwise independent port-preserving copies of a pattern with `s` edges, every crossing of two
copies being refuted. Then `r ≤ (2^(2^(κ+1) - 1))^(2s)`. -/
theorem prop_4_8 {L : Type} {σ : RScheme S L} {prover : ∀ c : Config S, c.V → L}
    {F P : Config S → Prop} (h : IsOneSided σ prover F P) {c : Config S} (hF : F c) (hP : P c)
    {r : ℕ} (K : Copies c r) (κ : ℕ)
    (hκ : ∀ v (ω : σ.Ω (c.state v) (prover c v) (c.deg v)) i, i < c.deg v →
      (σ.cert _ _ _ ω i).length ≤ κ)
    (hbad : ∀ i j (hij : i ≠ j), Refuted F P (K.cross i j hij)) :
    r ≤ (2 ^ (2 ^ (κ + 1) - 1)) ^ (2 * K.s) := by
  set ℓ := prover c
  by_contra hr
  -- pigeonhole on the supports of the certificates sent along the darts of the pattern
  let g : Fin r → (K.H.Dart → (bitStrings κ).powerset) := fun i d =>
    ⟨σ.supp κ (c.state (K.emb i d.fst)) (ℓ (K.emb i d.fst)) (c.deg (K.emb i d.fst))
      (c.port (K.emb i d.fst) (K.emb i d.snd)), Finset.mem_powerset.2 (Finset.filter_subset _ _)⟩
  have hcard : Fintype.card (K.H.Dart → (bitStrings κ).powerset) < Fintype.card (Fin r) := by
    rw [Fintype.card_fun, Fintype.card_coe, Finset.card_powerset, Fintype.card_fin,
      SimpleGraph.dart_card_eq_twice_card_edges]
    refine lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num)
      (card_bitStrings κ)) _) ?_
    rw [Copies.s] at hr
    simpa using not_le.1 hr
  obtain ⟨i, j, hij, hg⟩ := Fintype.exists_ne_map_eq_of_card_lt g hcard
  have hsupp : ∀ (d : K.H.Dart),
      σ.supp κ (c.state (K.emb i d.fst)) (ℓ (K.emb i d.fst)) (c.deg (K.emb i d.fst))
        (c.port (K.emb i d.fst) (K.emb i d.snd)) =
      σ.supp κ (c.state (K.emb j d.fst)) (ℓ (K.emb j d.fst)) (c.deg (K.emb j d.fst))
        (c.port (K.emb j d.fst) (K.emb j d.snd)) := fun d =>
    congrArg Subtype.val (congrFun hg d)
  have hall : ∀ ω, σ.AcceptsAll c ℓ ω := (σ.accProb_eq_one_iff c ℓ).1
    (le_antisymm (σ.accProb_le_one c ℓ) (h.1 c hF hP))
  -- every certificate that a sender of the crossing may send to `x` could be sent in `G` by the
  -- original neighbour of `x` on the same port
  have key : ∀ (x w : c.V), w ∈ c.nbrs x → ∀ ω₀ : σ.Ω (c.state (K.newNbr i j x w))
      (ℓ (K.newNbr i j x w)) (c.deg (K.newNbr i j x w)),
      ∃ z : σ.Ω (c.state w) (ℓ w) (c.deg w), σ.cert _ _ _ z (c.port w x) =
        σ.cert _ _ _ ω₀ (c.port w x) := by
    intro x w hw ω₀
    by_cases ha : K.IsArc i j x w
    · obtain ⟨a, b, hab, H1⟩ := K.isArc_cases hij ha
      -- the sibling `y` of `w` sends on the same port; supports agree
      have aux : ∀ k k' : Fin r, (∀ d : K.H.Dart,
          σ.supp κ (c.state (K.emb k' d.fst)) (ℓ (K.emb k' d.fst)) (c.deg (K.emb k' d.fst))
            (c.port (K.emb k' d.fst) (K.emb k' d.snd)) =
          σ.supp κ (c.state (K.emb k d.fst)) (ℓ (K.emb k d.fst)) (c.deg (K.emb k d.fst))
            (c.port (K.emb k d.fst) (K.emb k d.snd))) →
          K.emb k a = x → K.emb k b = w → K.newNbr i j x w = K.emb k' b →
          ∃ z : σ.Ω (c.state w) (ℓ w) (c.deg w), σ.cert _ _ _ z (c.port w x) =
            σ.cert _ _ _ ω₀ (c.port w x) := by
        intro k k' hs hx hw' hn
        subst hx hw'
        have hp : c.port (K.emb k b) (K.emb k a) = c.port (K.emb k' b) (K.emb k' a) :=
          K.port_eq k k' b a hab.symm
        have hlt : c.port (K.emb k' b) (K.emb k' a) < c.deg (K.emb k' b) := by
          rw [c.deg_eq]; exact List.idxOf_lt_length_of_mem (K.hom k' b a hab.symm)
        revert ω₀
        rw [hn]
        intro ω₀
        have hmem : σ.cert _ _ _ ω₀ (c.port (K.emb k b) (K.emb k a)) ∈
            σ.supp κ (c.state (K.emb k' b)) (ℓ (K.emb k' b)) (c.deg (K.emb k' b))
              (c.port (K.emb k' b) (K.emb k' a)) := by
          rw [hp]
          exact Finset.mem_filter.2 ⟨mem_bitStrings (hκ _ ω₀ _ hlt), ω₀, rfl⟩
        rw [hs ⟨(b, a), hab.symm⟩] at hmem
        obtain ⟨-, z, hz⟩ := Finset.mem_filter.1 hmem
        exact ⟨z, by rw [hz, hp]⟩
      rcases H1 with ⟨hx, hw', hn⟩ | ⟨hx, hw', hn⟩
      · exact aux i j (fun d => (hsupp d).symm) hx hw' hn
      · exact aux j i hsupp hx hw' hn
    · revert ω₀
      rw [K.newNbr_of_not_isArc ha]
      exact fun ω₀ => ⟨ω₀, rfl⟩
  have hcross : ∀ ω, σ.AcceptsAll (K.cross i j hij) ℓ ω := by
    intro ω (x : c.V)
    let ω' : σ.Coins c ℓ := fun w =>
      if hw : w ∈ c.nbrs x then (key x w hw (ω (K.newNbr i j x w))).choose else ω w
    have hrec : σ.received c ℓ ω' x = σ.received (K.cross i j hij) ℓ ω x := by
      refine Eq.trans ?_ (Copies.cross_received σ hij ℓ ω x).symm
      unfold RScheme.received
      refine List.map_congr_left fun w hw => ?_
      simp only [RScheme.sent, ω', hw, ↓reduceDIte]
      exact (key x w hw (ω (K.newNbr i j x w))).choose_spec
    have := hall ω' x
    change σ.dec (c.state x) (ℓ x) _ = true
    rwa [← hrec]
  -- the crossing (or a union of its components) is illegal, yet accepted with probability one
  have hacc1 : σ.accProb (K.cross i j hij) ℓ = 1 := (σ.accProb_eq_one_iff _ _).2 hcross
  rcases hbad i j hij with ⟨hF', hP'⟩ | ⟨U, hU, hF', hP'⟩
  · have := h.2 _ hF' hP' ℓ
    rw [hacc1] at this; norm_num at this
  · have h1 : σ.accProb ((K.cross i j hij).restrict U hU) (fun v => ℓ v.1) = 1 :=
      (σ.accProb_eq_one_iff _ _).2 (σ.acceptsAll_restrict hU ℓ hcross)
    have := h.2 _ hF' hP' (fun v => ℓ v.1)
    rw [h1] at this; norm_num at this

/-- Proposition 4.8 in logarithmic form: `2s · (2^(κ+1) - 1) ≥ log₂ r`, hence
`κ ≥ log₂ log₂ r - log₂ s - 2` (`Ω(log log r)` for fixed `s`). -/
theorem prop_4_8_log {L : Type} {σ : RScheme S L} {prover : ∀ c : Config S, c.V → L}
    {F P : Config S → Prop} (h : IsOneSided σ prover F P) {c : Config S} (hF : F c) (hP : P c)
    {r : ℕ} (K : Copies c r) (κ : ℕ)
    (hκ : ∀ v (ω : σ.Ω (c.state v) (prover c v) (c.deg v)) i, i < c.deg v →
      (σ.cert _ _ _ ω i).length ≤ κ)
    (hbad : ∀ i j (hij : i ≠ j), Refuted F P (K.cross i j hij)) :
    Real.logb 2 r ≤ 2 * K.s * 2 ^ (κ + 1) := by
  have h1 := prop_4_8 h hF hP K κ hκ hbad
  have h2 : r ≤ 2 ^ (2 * K.s * 2 ^ (κ + 1)) := by
    calc r ≤ (2 ^ (2 ^ (κ + 1) - 1)) ^ (2 * K.s) := h1
      _ ≤ (2 ^ (2 ^ (κ + 1))) ^ (2 * K.s) :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _)) _
      _ = 2 ^ (2 * K.s * 2 ^ (κ + 1)) := by rw [← pow_mul, mul_comm]
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0; simp
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by exact_mod_cast hpos)]
    exact_mod_cast (by exact_mod_cast h2 : (r : ℝ) ≤ (2 : ℝ) ^ (2 * K.s * 2 ^ (κ + 1)))

end Podc.RandomizedPLS
