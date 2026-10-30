import Papers.PODC2025.RoundEfficientColoring.Algorithm2
import Papers.PODC2025.RoundEfficientColoring.Encoding
import Papers.PODC2025.RoundEfficientColoring.ZeroComm

/-!
# Theorem 2: deterministic `(2Δ - 1)`-edge colouring with `O(n)` bits in one round

Chang–Mishra–Nguyen–Salim, PODC 2025, Lemma 5.1, Lemma 5.4 (communication part) and Theorem 2.

The vertex set is `Fin n`. A protocol is a `Cslib.CommunicationComplexity.OneRoundProtocol`:
both parties send one message simultaneously and then output colours for their own edges.

* `lemma51Protocol` (**Lemma 5.1**, `Δ ≤ 7`): Alice colours greedily with `2Δ - 1` colours and
  sends, for every vertex, the set of colours she uses there (`13 n` bits); Bob colours greedily
  avoiding them; Bob sends nothing.
* `alg2Protocol` (Algorithm 2, `8 ≤ Δ ≤ n`): both send the encoded `Plan.info`
  (`encInfo`): the greedy cover (unary length, colours in binary of width `⌊log₂ n⌋ + 1`, levels in
  unary — the paper's arrays `V_i` transposed) and three bit arrays (`9n` bits). Its length is
  `≤ 112 n` (`length_encInfo_le`).
* `theorem_2`: for all `n, Δ` a one-round protocol of cost `≤ 224 n` solving `(2Δ - 1)`-edge
  colouring on every input of maximum degree `≤ Δ`; `theorem_2_tree`: the same as a protocol tree
  of `Cslib.CommunicationComplexity.Protocol` with cost `≤ 224 n + 2`.
-/

namespace Podc.RoundEfficientColoring

open SimpleGraph Finset Cslib.CommunicationComplexity

/-! ### Encoding of `Info` -/

lemma binary_prefix {w c c' : ℕ} {l l' : List Bool} (hc : c < 2 ^ w) (hc' : c' < 2 ^ w)
    (h : binary w c ++ l = binary w c' ++ l') : c = c' ∧ l = l' := by
  obtain ⟨h1, h2⟩ := List.append_inj h (by rw [length_binary, length_binary])
  have := congrArg bitsVal h1
  rw [bitsVal_binary, bitsVal_binary, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] at this
  exact ⟨this, h2⟩

lemma flatMap_binary_prefix {w : ℕ} :
    ∀ {cs cs' : List ℕ} {l l' : List Bool}, cs.length = cs'.length →
      (∀ c ∈ cs, c < 2 ^ w) → (∀ c ∈ cs', c < 2 ^ w) →
      cs.flatMap (binary w) ++ l = cs'.flatMap (binary w) ++ l' → cs = cs' ∧ l = l'
  | [], [], _, _, _, _, _, h => ⟨rfl, by simpa using h⟩
  | c :: cs, c' :: cs', l, l', hlen, hb, hb', h => by
    simp only [List.flatMap_cons, List.append_assoc] at h
    obtain ⟨rfl, h'⟩ := binary_prefix (hb c (by simp)) (hb' c' (by simp)) h
    obtain ⟨rfl, h''⟩ := flatMap_binary_prefix (by simpa using hlen)
      (fun x hx => hb x (by simp [hx])) (fun x hx => hb' x (by simp [hx])) h'
    exact ⟨rfl, h''⟩

variable {n : ℕ}

instance : Inhabited (Info (Fin n)) := ⟨⟨[], fun _ => 0, fun _ => false, fun _ => false,
  fun _ _ => false⟩⟩

/-- The bit encoding of a message of Algorithm 2 (colours in binary with `w` digits). -/
def encInfo (w : ℕ) (i : Info (Fin n)) : List Bool :=
  unary i.cs.length ++ (i.cs.flatMap (binary w) ++ ((List.ofFn i.lvl).flatMap unary ++
    ((List.ofFn i.cov).flatMap bit ++ ((List.ofFn i.high).flatMap bit ++
      (List.ofFn fun v => fun j : Fin 7 => i.used7 v j).flatMap bitArray))))

/-- Well-formed messages: colours fit in `w` bits, `used7` is only set below `7`. -/
def WFInfo (w : ℕ) (i : Info (Fin n)) : Prop :=
  (∀ c ∈ i.cs, c < 2 ^ w) ∧ ∀ v j, 7 ≤ j → i.used7 v j = false

lemma encInfo_injective {w : ℕ} {i i' : Info (Fin n)} (hi : WFInfo w i) (hi' : WFInfo w i')
    (h : encInfo w i = encInfo w i') : i = i' := by
  unfold encInfo at h
  obtain ⟨hlen, h⟩ := prefixInj_unary h
  obtain ⟨h1, h⟩ := flatMap_binary_prefix hlen hi.1 hi'.1 h
  obtain ⟨h2, h⟩ := prefixInj_unary.ofFn h
  obtain ⟨h3, h⟩ := prefixInj_bit.ofFn h
  obtain ⟨h4, h⟩ := prefixInj_bit.ofFn h
  have h' := (prefixInj_bitArray.ofFn (l := []) (l' := []) (by simpa using h)).1
  have h5 : i.used7 = i'.used7 := by
    funext v j
    by_cases hj : j < 7
    · exact congrFun (congrFun h' v) ⟨j, hj⟩
    · rw [hi.2 v j (by omega), hi'.2 v j (by omega)]
  cases i; cases i'
  simp only [Info.mk.injEq]
  exact ⟨h1, h2, h3, h4, h5⟩

open Classical in
/-- Decoding of `encInfo`. -/
noncomputable def decInfo (w : ℕ) (l : List Bool) : Info (Fin n) :=
  if h : ∃ i : Info (Fin n), WFInfo w i ∧ encInfo w i = l then h.choose else default

lemma decInfo_encInfo {w : ℕ} {i : Info (Fin n)} (hi : WFInfo w i) :
    decInfo w (encInfo w i) = i := by
  have hex : ∃ i' : Info (Fin n), WFInfo w i' ∧ encInfo w i' = encInfo w i := ⟨i, hi, rfl⟩
  rw [decInfo, dite_eq_left hex]
  exact encInfo_injective hex.choose_spec.1 hi hex.choose_spec.2

lemma length_encInfo (w : ℕ) (i : Info (Fin n)) :
    (encInfo w i).length = (i.cs.length + 1) + i.cs.length * w + ∑ v, (i.lvl v + 1) + 9 * n := by
  simp only [encInfo, List.length_append, length_unary, length_flatMap_ofFn_unary]
  rw [length_flatMap_const (fun c => length_binary w c),
    length_flatMap_const (m := 1) (fun _ => rfl), length_flatMap_const (m := 1) (fun _ => rfl),
    length_flatMap_const (m := 7) (fun _ => by simp [bitArray])]
  simp only [List.length_ofFn]
  ring

/-- The colour width used by Algorithm 2 on `n` vertices. -/
def colorWidth (n : ℕ) : ℕ := Nat.log 2 n + 1

lemma lt_two_pow_colorWidth (n : ℕ) : n < 2 ^ colorWidth n := Nat.lt_pow_succ_log_self (by norm_num) n

lemma two_pow_colorWidth_le {n : ℕ} (hn : 1 ≤ n) : 2 ^ colorWidth n ≤ 2 * n := by
  unfold colorWidth
  rw [pow_succ, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))

/-! ### Algorithm 2 as a one-round protocol -/

variable {Δ : ℕ}

lemma plan_wf {X : SimpleGraph (Fin n)} (p : Plan Δ X) (hΔn : Δ ≤ n) :
    WFInfo (colorWidth n) p.info := by
  refine ⟨fun c hc => ?_, fun v j hj => ?_⟩
  · have := p.cs_lt c hc
    have := lt_two_pow_colorWidth n
    omega
  · simp only [Plan.info, decide_eq_false_iff_not, not_and]
    intro h; omega

/-- The message of Algorithm 2 has `O(n)` bits. -/
lemma length_encInfo_le (hn : 1 ≤ n) {X : SimpleGraph (Fin n)} (p : Plan Δ X) :
    (encInfo (colorWidth n) p.info).length ≤ 112 * n := by
  rw [length_encInfo]
  simp only [Plan.info]
  have hsum : ∑ v, (p.lvl v + 1) ≤ 3 * n := by
    rw [Finset.sum_add_distrib]
    have := p.lvl_sum
    simp only [Fintype.card_fin, sum_const, card_univ, smul_eq_mul, mul_one] at this ⊢
    omega
  have hcov : (p.cs.length + 1) * (colorWidth n + 1) ≤ 100 * n := by
    rcases p.cs_len with h | h
    · rw [h]
      have : colorWidth n + 1 ≤ 2 ^ colorWidth n := Nat.lt_two_pow_self
      have := two_pow_colorWidth_le hn
      simp; omega
    · rw [Fintype.card_fin] at h
      exact cover_bits_le h (two_pow_colorWidth_le hn)
  nlinarith

/-- The protocol of Algorithm 2 (for `8 ≤ Δ`). Alice's own palette is `[0, Δ - 1)`, Bob's is
`[Δ - 1, 2Δ - 2)`. On inputs violating the degree bound the parties send nothing and output `0`. -/
noncomputable def alg2Protocol (hΔ : 8 ≤ Δ) :
    OneRoundProtocol (SimpleGraph (Fin n)) (SimpleGraph (Fin n)) (Sym2 (Fin n) → ℕ)
      (Sym2 (Fin n) → ℕ) := by
  classical
  exact
  { msgA := fun A => if h : ∀ v, (A.neighborSet v).ncard ≤ Δ then
      encInfo (colorWidth n) (Classical.choice (exists_plan hΔ h)).info else []
    msgB := fun B => if h : ∀ v, (B.neighborSet v).ncard ≤ Δ then
      encInfo (colorWidth n) (Classical.choice (exists_plan hΔ h)).info else []
    outA := fun A m => if h : ∀ v, (A.neighborSet v).ncard ≤ Δ then
      (Classical.choice (exists_plan hΔ h)).color 0 (Δ - 1) (decInfo (colorWidth n) m)
      else fun _ => 0
    outB := fun B m => if h : ∀ v, (B.neighborSet v).ncard ≤ Δ then
      (Classical.choice (exists_plan hΔ h)).color (Δ - 1) 0 (decInfo (colorWidth n) m)
      else fun _ => 0 }

lemma alg2Protocol_costLE (hn : 1 ≤ n) (hΔ : 8 ≤ Δ) : (alg2Protocol (n := n) hΔ).CostLE (224 * n) := by
  intro A B
  simp only [alg2Protocol]
  have hA : (if h : ∀ v, (A.neighborSet v).ncard ≤ Δ then
      encInfo (colorWidth n) (Classical.choice (exists_plan hΔ h)).info else []).length ≤ 112 * n := by
    split_ifs
    · exact length_encInfo_le hn _
    · simp
  have hB : (if h : ∀ v, (B.neighborSet v).ncard ≤ Δ then
      encInfo (colorWidth n) (Classical.choice (exists_plan hΔ h)).info else []).length ≤ 112 * n := by
    split_ifs
    · exact length_encInfo_le hn _
    · simp
  omega

lemma alg2Protocol_correct (hΔ : 8 ≤ Δ) (hΔn : Δ ≤ n) {A B : SimpleGraph (Fin n)}
    (hv : ValidInput Δ A B) :
    SolvesEdgeColoring (2 * Δ - 1) A B ((alg2Protocol hΔ).outputA A B)
      ((alg2Protocol hΔ).outputB A B) := by
  obtain ⟨hAB, hdeg⟩ := hv
  have hA := deg_left_le hAB hdeg
  have hB := deg_right_le hAB hdeg
  have hdeg' : ∀ x, ((B ⊔ A).neighborSet x).ncard ≤ Δ := fun x => by rw [sup_comm]; exact hdeg x
  set pA := Classical.choice (exists_plan hΔ hA)
  set pB := Classical.choice (exists_plan hΔ hB)
  have eA : (alg2Protocol hΔ).outputA A B = pA.color 0 (Δ - 1) pB.info := by
    simp only [OneRoundProtocol.outputA, alg2Protocol, dite_eq_left hA, dite_eq_left hB]
    rw [decInfo_encInfo (plan_wf _ hΔn)]
  have eB : (alg2Protocol hΔ).outputB A B = pB.color (Δ - 1) 0 pA.info := by
    simp only [OneRoundProtocol.outputB, alg2Protocol, dite_eq_left hA, dite_eq_left hB]
    rw [decInfo_encInfo (plan_wf _ hΔn)]
  have hoo : Offsets Δ 0 (Δ - 1) := Or.inl ⟨rfl, rfl⟩
  rw [eA, eB]
  exact solvesEdgeColoring_of hAB (color_proper hAB hdeg pA pB hoo hΔ)
    (color_proper hAB.symm hdeg' pB pA hoo.symm hΔ)
    (fun v w w' h1 h2 => cross hAB hdeg pA pB hoo hΔ h1 h2)

/-! ### Lemma 5.1: small `Δ` -/

/-- Alice's greedy colouring with `2Δ - 1` colours. -/
lemma exists_greedy_alice {A : SimpleGraph (Fin n)} (hA : ∀ v, (A.neighborSet v).ncard ≤ Δ) :
    ∃ c : Sym2 (Fin n) → ℕ, (∀ ⦃u v⦄, A.Adj u v → c s(u, v) ∈ range (2 * Δ - 1)) ∧
      A.IsEdgeColoring c :=
  exists_listEdgeColoring A (fun _ => range (2 * Δ - 1)) fun u v huv => by
    have := hA u; have := hA v
    have : 0 < (A.neighborSet u).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, huv⟩
    simp only [card_range]; omega

/-- Alice's colouring in Lemma 5.1 (`0` on inputs violating the degree bound). -/
noncomputable def greedyAlice (Δ : ℕ) (A : SimpleGraph (Fin n)) : Sym2 (Fin n) → ℕ := by
  classical
  exact if h : ∀ v, (A.neighborSet v).ncard ≤ Δ then (exists_greedy_alice h).choose else fun _ => 0

open Classical in
/-- Colours used by `c` at `v`, as a `13`-bit array per vertex. -/
noncomputable def usedArray (A : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℕ) :
    Fin n → Fin 13 → Bool :=
  fun v j => decide (∃ w, A.Adj v w ∧ c s(v, w) = j)

open Classical in
/-- Bob's lists in Lemma 5.1: colours `< 2Δ - 1` not used by Alice at the endpoints. -/
noncomputable def bobList (Δ : ℕ) (used : Fin n → Fin 13 → Bool) (e : Sym2 (Fin n)) : Finset ℕ :=
  (range (2 * Δ - 1)).filter fun j => ∀ x ∈ e, ∀ hj : j < 13, used x ⟨j, hj⟩ = false

/-- Bob's greedy colouring in Lemma 5.1. -/
noncomputable def greedyBob (Δ : ℕ) (B : SimpleGraph (Fin n)) (used : Fin n → Fin 13 → Bool) :
    Sym2 (Fin n) → ℕ := by
  classical
  exact if h : ∃ c : Sym2 (Fin n) → ℕ, (∀ ⦃u v⦄, B.Adj u v → c s(u, v) ∈ bobList Δ used s(u, v)) ∧
    B.IsEdgeColoring c then h.choose else fun _ => 0

open Classical in
/-- Decoding of Alice's message in Lemma 5.1. -/
noncomputable def decUsed (l : List Bool) : Fin n → Fin 13 → Bool :=
  if h : ∃ u : Fin n → Fin 13 → Bool, (List.ofFn u).flatMap bitArray = l then h.choose
  else fun _ _ => false

lemma decUsed_enc (u : Fin n → Fin 13 → Bool) : decUsed ((List.ofFn u).flatMap bitArray) = u := by
  have hex : ∃ u' : Fin n → Fin 13 → Bool, (List.ofFn u').flatMap bitArray =
      (List.ofFn u).flatMap bitArray := ⟨u, rfl⟩
  rw [decUsed, dite_eq_left hex]
  exact (prefixInj_bitArray.ofFn (l := []) (l' := []) (by simpa using hex.choose_spec)).1

/-- **Lemma 5.1** as a one-round protocol (Alice sends `13 n` bits, Bob nothing). -/
noncomputable def lemma51Protocol (Δ : ℕ) :
    OneRoundProtocol (SimpleGraph (Fin n)) (SimpleGraph (Fin n)) (Sym2 (Fin n) → ℕ)
      (Sym2 (Fin n) → ℕ) where
  msgA A := (List.ofFn (usedArray A (greedyAlice Δ A))).flatMap bitArray
  msgB _ := []
  outA A _ := greedyAlice Δ A
  outB B m := greedyBob Δ B (decUsed m)

lemma lemma51Protocol_costLE (Δ : ℕ) : (lemma51Protocol (n := n) Δ).CostLE (13 * n) := by
  intro A B
  simp [lemma51Protocol, length_flatMap_const (m := 13) (fun _ => by simp [bitArray] :
    ∀ f : Fin 13 → Bool, (bitArray f).length = 13), mul_comm]

/-- **Lemma 5.1** of [CMNS25]: for `Δ ≤ 7` the protocol `lemma51Protocol` (one round, `13 n`
bits) solves `(2Δ - 1)`-edge colouring. -/
theorem lemma_5_1 (hΔ : Δ ≤ 7) {A B : SimpleGraph (Fin n)} (hv : ValidInput Δ A B) :
    SolvesEdgeColoring (2 * Δ - 1) A B ((lemma51Protocol Δ).outputA A B)
      ((lemma51Protocol Δ).outputB A B) := by
  classical
  obtain ⟨hAB, hdeg⟩ := hv
  have hA := deg_left_le hAB hdeg
  have hB := deg_right_le hAB hdeg
  set gA := greedyAlice Δ A
  have hgA : (∀ ⦃u v⦄, A.Adj u v → gA s(u, v) ∈ range (2 * Δ - 1)) ∧ A.IsEdgeColoring gA := by
    simp only [gA, greedyAlice, dite_eq_left hA]; exact (exists_greedy_alice hA).choose_spec
  set used := usedArray A gA
  have hused : ∀ x, #((range (2 * Δ - 1)).filter fun j => ∃ hj : j < 13, used x ⟨j, hj⟩ = true) ≤
      (A.neighborSet x).ncard := fun x => by
    have hsub : (range (2 * Δ - 1)).filter (fun j => ∃ hj : j < 13, used x ⟨j, hj⟩ = true) ⊆
        (Set.toFinite (A.neighborSet x)).toFinset.image fun w => gA s(x, w) := by
      intro j hj
      simp only [mem_filter, used, usedArray, decide_eq_true_eq] at hj
      obtain ⟨-, -, w, hw, hwj⟩ := hj
      exact mem_image.mpr ⟨w, by simpa using hw, hwj⟩
    calc _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_image_le
      _ = _ := (Set.ncard_eq_toFinset_card _ _).symm
  have hex : ∃ c : Sym2 (Fin n) → ℕ, (∀ ⦃u v⦄, B.Adj u v → c s(u, v) ∈ bobList Δ used s(u, v)) ∧
      B.IsEdgeColoring c := by
    refine exists_listEdgeColoring B _ fun u v huv => ?_
    have hsub : range (2 * Δ - 1) \
        ((range (2 * Δ - 1)).filter (fun j => ∃ hj : j < 13, used u ⟨j, hj⟩ = true) ∪
          (range (2 * Δ - 1)).filter (fun j => ∃ hj : j < 13, used v ⟨j, hj⟩ = true)) ⊆
        bobList Δ used s(u, v) := by
      intro j hj
      simp only [mem_sdiff, mem_union, mem_filter, not_or, not_and, not_exists] at hj
      refine mem_filter.mpr ⟨hj.1, fun x hx hj13 => ?_⟩
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · simpa using hj.2.1 hj.1 hj13
      · simpa using hj.2.2 hj.1 hj13
    have h1 := card_le_card hsub
    have h2 := le_card_sdiff ((range (2 * Δ - 1)).filter (fun j => ∃ hj : j < 13, used u ⟨j, hj⟩ = true) ∪
          (range (2 * Δ - 1)).filter (fun j => ∃ hj : j < 13, used v ⟨j, hj⟩ = true)) (range (2 * Δ - 1))
    have h3 := card_union_le ((range (2 * Δ - 1)).filter (fun j => ∃ hj : j < 13, used u ⟨j, hj⟩ = true))
          ((range (2 * Δ - 1)).filter (fun j => ∃ hj : j < 13, used v ⟨j, hj⟩ = true))
    have := hused u; have := hused v
    have := deg_add_le hAB hdeg u; have := deg_add_le hAB hdeg v
    have : 0 < (B.neighborSet u).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨v, huv⟩
    simp only [card_range] at h2
    omega
  set gB := greedyBob Δ B used
  have hgB : (∀ ⦃u v⦄, B.Adj u v → gB s(u, v) ∈ bobList Δ used s(u, v)) ∧ B.IsEdgeColoring gB := by
    simp only [gB, greedyBob, dite_eq_left hex]; exact hex.choose_spec
  have eA : (lemma51Protocol Δ).outputA A B = gA := rfl
  have eB : (lemma51Protocol Δ).outputB A B = gB := by
    simp only [OneRoundProtocol.outputB, lemma51Protocol]; rw [decUsed_enc]
  rw [eA, eB]
  refine solvesEdgeColoring_of hAB ⟨fun u v h => mem_range.mp (hgA.1 h), hgA.2⟩
    ⟨fun u v h => mem_range.mp (mem_filter.mp (hgB.1 h)).1, hgB.2⟩ fun v w w' h1 h2 he => ?_
  have hj := mem_filter.mp (hgB.1 h2)
  have h13 : gB s(v, w') < 13 := by have := mem_range.mp hj.1; omega
  have := hj.2 v (Sym2.mem_mk_left _ _) h13
  simp only [used, usedArray, decide_eq_false_iff_not, not_exists, not_and] at this
  exact this w h1 he

/-! ### Theorem 2 -/

/-- On `n` vertices every degree is `< n`. -/
lemma ncard_neighborSet_lt (G : SimpleGraph (Fin n)) (v : Fin n) : (G.neighborSet v).ncard < n := by
  have hsub : G.neighborSet v ⊆ (Set.univ : Set (Fin n)) \ {v} := fun w hw =>
    ⟨trivial, fun h => G.irrefl (Set.mem_singleton_iff.mp h ▸ hw)⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_sdiff_singleton_of_mem (Set.mem_univ v), Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at this
  have : 0 < n := Fin.pos v
  omega

/-- The protocol of Theorem 2: Lemma 5.1 if the effective degree bound `min Δ n` is `≤ 7`,
Algorithm 2 otherwise. -/
noncomputable def theorem2Protocol (n Δ : ℕ) :
    OneRoundProtocol (SimpleGraph (Fin n)) (SimpleGraph (Fin n)) (Sym2 (Fin n) → ℕ)
      (Sym2 (Fin n) → ℕ) :=
  if h : 8 ≤ min Δ n then alg2Protocol h else lemma51Protocol (min Δ n)

lemma theorem2Protocol_correct {A B : SimpleGraph (Fin n)} (hv : ValidInput Δ A B) :
    SolvesEdgeColoring (2 * Δ - 1) A B ((theorem2Protocol n Δ).outputA A B)
      ((theorem2Protocol n Δ).outputB A B) := by
  have hv' : ValidInput (min Δ n) A B :=
    ⟨hv.1, fun v => le_min (hv.2 v) (ncard_neighborSet_lt _ v).le⟩
  have hmono : ∀ {cA cB}, SolvesEdgeColoring (2 * min Δ n - 1) A B cA cB →
      SolvesEdgeColoring (2 * Δ - 1) A B cA cB := fun h =>
    h.mono le_rfl (by have := min_le_left Δ n; omega)
  unfold theorem2Protocol
  split_ifs with h
  · exact hmono (alg2Protocol_correct h (min_le_right _ _) hv')
  · exact hmono (lemma_5_1 (by omega) hv')

/-- **Theorem 2** of [CMNS25]: there is a deterministic protocol that finds a `(2Δ - 1)`-edge
colouring of every `n`-vertex graph of maximum degree `≤ Δ` (edges partitioned between Alice and
Bob, each party colouring its own edges), using `O(n)` bits (here `≤ 224 n`) and `O(1)` rounds
(here one round of simultaneous messages). -/
theorem theorem_2 : ∃ C : ℕ, ∀ n Δ : ℕ, ∃ P : OneRoundProtocol (SimpleGraph (Fin n))
    (SimpleGraph (Fin n)) (Sym2 (Fin n) → ℕ) (Sym2 (Fin n) → ℕ),
    P.CostLE (C * n) ∧ ∀ A B, ValidInput Δ A B →
      SolvesEdgeColoring (2 * Δ - 1) A B (P.outputA A B) (P.outputB A B) := by
  refine ⟨224, fun n Δ => ⟨theorem2Protocol n Δ, ?_, fun A B hv => theorem2Protocol_correct hv⟩⟩
  unfold theorem2Protocol
  split_ifs with h
  · exact alg2Protocol_costLE (by omega) h
  · intro A B; have := lemma51Protocol_costLE (n := n) (min Δ n) A B; omega

/-- Theorem 2 with the protocol written as a protocol tree of
`Cslib.CommunicationComplexity.Protocol` (messages of length `≤ L` sent as one symbol of an
alphabet of size `2 ^ (L + 1)`): cost `≤ 224 n + 2`, and the leaf reached on `(A, B)` gives
Alice's and Bob's correct outputs. -/
theorem theorem_2_tree (n Δ : ℕ) : ∃ T : Protocol (SimpleGraph (Fin n)) (SimpleGraph (Fin n))
    ((SimpleGraph (Fin n) → Sym2 (Fin n) → ℕ) × (SimpleGraph (Fin n) → Sym2 (Fin n) → ℕ)),
    T.CostLE (224 * n + 2) ∧ ∀ A B, ValidInput Δ A B →
      SolvesEdgeColoring (2 * Δ - 1) A B ((T.eval A B).1 A) ((T.eval A B).2 B) := by
  have hmsg : (∀ A, ((theorem2Protocol n Δ).msgA A).length ≤ 112 * n) ∧
      ∀ B, ((theorem2Protocol n Δ).msgB B).length ≤ 112 * n := by
    unfold theorem2Protocol
    split_ifs with h
    · refine ⟨fun A => ?_, fun B => ?_⟩ <;> simp only [alg2Protocol] <;> split_ifs
      · exact length_encInfo_le (by omega) _
      · simp
      · exact length_encInfo_le (by omega) _
      · simp
    · refine ⟨fun A => ?_, fun B => by simp [lemma51Protocol]⟩
      have := lemma51Protocol_costLE (n := n) (min Δ n) A ⊥
      simp only [lemma51Protocol, List.length_nil, add_zero] at this ⊢
      omega
  refine ⟨(theorem2Protocol n Δ).toProtocol (112 * n) (112 * n), ?_, fun A B hv => ?_⟩
  · have := (theorem2Protocol n Δ).toProtocol_costLE (112 * n) (112 * n)
    exact this.mono (by omega)
  · rw [OneRoundProtocol.toProtocol_eval_fst _ hmsg.2,
      OneRoundProtocol.toProtocol_eval_snd _ hmsg.1]
    exact theorem2Protocol_correct hv

end Podc.RoundEfficientColoring
