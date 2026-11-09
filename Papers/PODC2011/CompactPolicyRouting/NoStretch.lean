import Papers.PODC2011.CompactPolicyRouting.Routing

/-!
# No compact stretch-`k` routing when isotonicity fails badly (Theorem 4.17)

Theorem 4.17: let `A` be monotone and suppose that for every `p ≥ 2` there are weights `w₁, …, w_p` with
`wᵢ ⊕ wⱼ ≻ wᵢ^{2k}` and `wᵢ ⊕ wⱼ ≻ wⱼ^{2k}` for `i ≠ j` (condition (4.2)). Then no stretch-`k` routing scheme has
sublinear local memory.

The graph family (Fig. 4.2): centres `cᵢ` (`i < p`), middle nodes `z_{ij}` (`j < δ`) adjacent to `cᵢ`, and targets
`t`, each with a word `word t : Fin p → Fin δ`; `t` is adjacent to `z_{i, word t i}`. Every edge at `z_{ij}` has
weight `wᵢ`.

* `Family.weight_gt_of_two_lt_length`: every `cᵢ – t` path other than the two-hop path `cᵢ z_{i,word t i} t` weighs
  more than `wᵢ^{2k}` (it contains two `wᵢ`-edges and two `wⱼ`-edges for some `j ≠ i`).
* `Family.route_eq_of_implementsStretch`: hence every stretch-`k` routing function forwards a packet from `cᵢ`
  for `t` on the port towards `z_{i, word t i}`, i.e. the local routing functions of the centres determine the words.
* `theorem_4_17`: counting (here over a family with `p ≈ n/4` centres, `δ = 2` and `q ≈ n/4` targets with arbitrary
  words) gives local memory `≥ n/8` at some centre for large `n`, for every memory measure in which fewer than `2^b`
  functions have code length `< b`.

The thesis' family has exactly `δ^p` targets carrying pairwise distinct words; then the graph is unique up to
isomorphism and node labels of `O(log n)` bits can carry the word of each target, so it cannot by itself force
`Ω(n)` bits in the model of Section 4.2 (labels are chosen by the scheme). With `p, q = Θ(n)` the counting works.
-/

namespace Podc.CompactPolicyRouting

open SimpleGraph RoutingAlgebra Filter

universe u

variable {W : Type u} [LinearOrder W]

/-- A routing function of stretch `k` (Definition 4.13): for every `s ≠ t` joined by a traversable path, the
generated route is a path `p` with `w(p) ⪯ w(p*_{st})^k`. -/
def ImplementsStretch (A : RoutingAlgebra W) {V : Type} [Finite V] {G : SimpleGraph V}
    (wt : Sym2 V → W) (k : ℕ) (R : RoutingFunction G) : Prop :=
  ∀ s t, s ≠ t → Traversable A (G := G) wt s t →
    ∃ p : G.Walk s t, p.IsPath ∧ IsWithinStretch A wt k p ∧ R.Generates (R.label t) p

/-- Local memory requirement of stretch-`k` routing (Definition 4.5 with stretch-`k` routing functions). -/
noncomputable def memReqStretch (A : RoutingAlgebra W) (mem : MemoryMeasure) (c k n : ℕ) : ℕ∞ :=
  ⨆ (V : Type) (_ : Finite V) (_ : Nat.card V = n) (G : SimpleGraph V) (_ : G.Connected)
    (wt : Sym2 V → W), minMem G mem (fun R => ImplementsStretch A wt k R ∧ R.LabelsBounded c n)

theorem le_memReqStretch {A : RoutingAlgebra W} {mem : MemoryMeasure} {c k n : ℕ} {V : Type} [Finite V]
    (hV : Nat.card V = n) (G : SimpleGraph V) (hG : G.Connected) (wt : Sym2 V → W) :
    minMem G mem (fun R => ImplementsStretch A wt k R ∧ R.LabelsBounded c n) ≤
      memReqStretch A mem c k n :=
  le_iSup_of_le V <| le_iSup_of_le inferInstance <| le_iSup_of_le hV <| le_iSup_of_le G <|
    le_iSup_of_le hG <| le_iSup_of_le wt le_rfl

namespace Family

variable (p δ q : ℕ)

/-- Nodes of the family graph: centres `c i`, middle nodes `z i j`, targets `tgt t`. -/
abbrev Node := Fin p ⊕ (Fin p × Fin δ) ⊕ Fin q

variable {p δ q}

/-- Adjacency of the family graph. -/
def Rel (word : Fin q → Fin p → Fin δ) : Node p δ q → Node p δ q → Prop
  | .inl i, .inr (.inl (i', _)) => i = i'
  | .inr (.inl (i', _)), .inl i => i = i'
  | .inr (.inl (i, j)), .inr (.inr t) => word t i = j
  | .inr (.inr t), .inr (.inl (i, j)) => word t i = j
  | _, _ => False

/-- The graph of Fig. 4.2 for the words `word`. -/
def graph (word : Fin q → Fin p → Fin δ) : SimpleGraph (Node p δ q) where
  Adj := Rel word
  symm := ⟨by
    intro a b h
    rcases a with i | ⟨i, j⟩ | t <;> rcases b with i' | ⟨i', j'⟩ | t' <;> simp_all [Rel]⟩
  loopless := ⟨by
    intro a h
    rcases a with i | ⟨i, j⟩ | t <;> simp_all [Rel]⟩

/-- The index `i` of a middle node `z i j`. -/
def zIdx : Node p δ q → Option (Fin p)
  | .inr (.inl (i, _)) => some i
  | _ => none

/-- The edge weights: an edge at `z i j` has weight `w i`. -/
def wts (A : RoutingAlgebra W) (w : Fin p → W) : Sym2 (Node p δ q) → W :=
  Sym2.lift ⟨fun a b => match zIdx a, zIdx b with
    | some i, none => w i
    | none, some i => w i
    | _, _ => A.phi, by
    intro a b
    rcases a with i | ⟨i, j⟩ | t <;> rcases b with i' | ⟨i', j'⟩ | t' <;> rfl⟩

@[simp] theorem wts_cz (A : RoutingAlgebra W) (w : Fin p → W) (i i' : Fin p) (j : Fin δ) :
    wts (q := q) A w s(.inl i, .inr (.inl (i', j))) = w i' := rfl

@[simp] theorem wts_zt (A : RoutingAlgebra W) (w : Fin p → W) (i : Fin p) (j : Fin δ) (t : Fin q) :
    wts A w s(.inr (.inl (i, j)), .inr (.inr t)) = w i := rfl

@[simp] theorem wts_tz (A : RoutingAlgebra W) (w : Fin p → W) (i : Fin p) (j : Fin δ) (t : Fin q) :
    wts A w s(.inr (.inr t), .inr (.inl (i, j))) = w i := rfl

@[simp] theorem wts_zc (A : RoutingAlgebra W) (w : Fin p → W) (i i' : Fin p) (j : Fin δ) :
    wts (q := q) A w s(.inr (.inl (i', j)), .inl i) = w i' := rfl

variable (word : Fin q → Fin p → Fin δ)

theorem adj_cz (i : Fin p) (j : Fin δ) : (graph word).Adj (.inl i) (.inr (.inl (i, j))) := rfl

theorem adj_zt (t : Fin q) (i : Fin p) : (graph word).Adj (.inr (.inl (i, word t i))) (.inr (.inr t)) := rfl

/-- The two-hop path `cᵢ z_{i, word t i} t`. -/
def twoHop (i : Fin p) (t : Fin q) : (graph word).Walk (.inl i) (.inr (.inr t)) :=
  .cons (adj_cz word i (word t i)) (.cons (adj_zt word t i) .nil)

theorem twoHop_isPath (i : Fin p) (t : Fin q) : (twoHop word i t).IsPath := by
  simp [twoHop, Walk.isPath_def]

theorem weight_twoHop (A : RoutingAlgebra W) (w : Fin p → W) (i : Fin p) (t : Fin q) :
    weight A (wts A w) (twoHop word i t) = A.emb (w i) ^ 2 := by
  simp [twoHop, pow_two]

/-- A `cᵢ – t` path of length `2` is the two-hop path. -/
theorem eq_twoHop_of_length (i : Fin p) (t : Fin q) (P : (graph word).Walk (.inl i) (.inr (.inr t)))
    (hP : P.length = 2) : P = twoHop word i t := by
  cases P with
  | cons h₁ P₁ =>
    cases P₁ with
    | nil => simp at hP
    | cons h₂ P₂ =>
      cases P₂ with
      | cons => simp at hP
      | nil =>
        rename_i v₁
        rcases v₁ with i' | ⟨i', j⟩ | t'
        · exact absurd h₁ (by simp [graph, Rel])
        · have hi : i = i' := h₁
          subst hi
          have hj : word t i = j := h₂
          subst hj
          rfl
        · exact absurd h₁ (by simp [graph, Rel])

/-- The core of Theorem 4.17: under monotonicity and (4.2), every `cᵢ – t` path other than the two-hop one
weighs more than `wᵢ^{2k}`. -/
theorem weight_gt_of_two_lt_length {A : RoutingAlgebra W} (hM : A.IsMonotone) {k : ℕ} {w : Fin p → W}
    (h42 : ∀ i j, i ≠ j → A.emb (w i) ^ (2 * k) < A.emb (A.op (w i) (w j))) (i : Fin p) (t : Fin q)
    (P : (graph word).Walk (.inl i) (.inr (.inr t))) (hP : P.IsPath) (hlen : 2 < P.length) :
    A.emb (w i) ^ (2 * k) < weight A (wts A w) P := by
  cases P with
  | cons h₁ P₁ =>
  cases P₁ with
  | nil => simp at hlen
  | cons h₂ P₂ =>
  cases P₂ with
  | nil => simp at hlen
  | cons h₃ P₃ =>
  rename_i v₁ v₂ v₃
  cases P₃ with
  | nil =>
    rcases v₁ with i₁ | ⟨i₁, j₁⟩ | t₁ <;> rcases v₂ with i₂ | ⟨i₂, j₂⟩ | t₂ <;>
      simp [graph, Rel] at h₁ h₂ h₃
  | cons h₄ P₄ =>
    rename_i v₄
    rcases v₁ with i₁ | ⟨i₁, j₁⟩ | t₁
    · exact absurd h₁ (by simp [graph, Rel])
    swap
    · exact absurd h₁ (by simp [graph, Rel])
    have hi₁ : i = i₁ := h₁
    subst hi₁
    rcases v₂ with i₂ | ⟨i₂, j₂⟩ | t₂
    · -- back at a centre: it must be `cᵢ` itself, contradicting the path property
      have : i₂ = i := h₂
      subst this
      simp [Walk.isPath_def] at hP
    · exact absurd h₂ (by simp [graph, Rel])
    rcases v₃ with i₃ | ⟨i₃, j₃⟩ | t₃
    · exact absurd h₃ (by simp [graph, Rel])
    swap
    · exact absurd h₃ (by simp [graph, Rel])
    have hw₂ : word t₂ i = j₁ := h₂
    have hw₃ : word t₂ i₃ = j₃ := h₃
    have hi₃ : i₃ ≠ i := by
      rintro rfl
      have : j₃ = j₁ := hw₃.symm.trans hw₂
      subst this
      simp [Walk.isPath_def] at hP
    have hw₄ : wts A w s(.inr (.inl (i₃, j₃)), v₄) = w i₃ := by
      rcases v₄ with i₄ | ⟨i₄, j₄⟩ | t₄
      · rfl
      · exact absurd h₄ (by simp [graph, Rel])
      · rfl
    simp only [weight_cons, wts_cz, wts_zt, wts_tz, hw₄]
    calc A.emb (w i) ^ (2 * k) < A.emb (A.op (w i) (w i₃)) := h42 i i₃ hi₃.symm
      _ ≤ A.emb (A.op (w i) (w i₃)) * A.emb (A.op (w i) (w i₃)) := hM.le_mul' _ _
      _ = A.emb (w i) * (A.emb (w i) * (A.emb (w i₃) * A.emb (w i₃))) := by
        rw [← emb_mul_emb]; ac_rfl
      _ ≤ A.emb (w i) * (A.emb (w i) * (A.emb (w i₃) * (A.emb (w i₃) *
            weight A (wts A w) P₄))) := by
        have := hM.le_mul' (A.emb (w i) * A.emb (w i) * A.emb (w i₃) * A.emb (w i₃))
          (weight A (wts A w) P₄)
        simpa only [mul_assoc] using this

theorem eq_twoHop_or_two_lt (i : Fin p) (t : Fin q) (P : (graph word).Walk (.inl i) (.inr (.inr t))) :
    P = twoHop word i t ∨ 2 < P.length := by
  rcases Nat.lt_or_ge 2 P.length with h | h
  · exact Or.inr h
  left
  apply eq_twoHop_of_length
  cases P with
  | cons h₁ P₁ =>
    cases P₁ with
    | nil => exact absurd h₁ (by simp [graph, Rel])
    | cons h₂ P₂ =>
      cases P₂ with
      | nil => rfl
      | cons => simp at h

/-- Condition (4.2) of Theorem 4.17 for the weights `w : Fin p → W` (the second inequality
`wᵢ ⊕ wⱼ ≻ wⱼ^{2k}` is the first one with `i, j` swapped). -/
def Condition42 (A : RoutingAlgebra W) (k : ℕ) {p : ℕ} (w : Fin p → W) : Prop :=
  ∀ i j, i ≠ j → A.emb (w i) ^ (2 * k) < A.emb (A.op (w i) (w j))

theorem pow_le_pow_of_le {A : RoutingAlgebra W} (hM : A.IsMonotone) (x : A.Ext) {m n : ℕ}
    (h : m ≤ n) : x ^ m ≤ x ^ n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add]; exact hM.le_mul' _ _

/-- The two-hop path is the preferred `cᵢ – t` path: `w(p*_{cᵢ t}) = wᵢ²`. -/
theorem pw_eq {A : RoutingAlgebra W} (hM : A.IsMonotone) {k : ℕ} (hk : 1 ≤ k) {w : Fin p → W}
    (h42 : Condition42 A k w) (i : Fin p) (t : Fin q) :
    pw A (wts A w) (graph word) (.inl i) (.inr (.inr t)) = A.emb (w i) ^ 2 := by
  apply le_antisymm
  · rw [← weight_twoHop word A w i t]; exact pw_le_weight_of_isPath _ (twoHop_isPath word i t)
  · obtain ⟨P, hP, hPw⟩ := exists_isPreferred_weight (A := A) (wt := wts A w)
      (⟨twoHop word i t⟩ : (graph word).Reachable (.inl i) (.inr (.inr t)))
    rw [← hPw]
    rcases eq_twoHop_or_two_lt word i t P with rfl | hlen
    · rw [weight_twoHop]
    · exact ((pow_le_pow_of_le hM _ (by omega : 2 ≤ 2 * k)).trans_lt
        (weight_gt_of_two_lt_length word hM h42 i t P hP.1 hlen)).le

theorem traversable_twoHop {A : RoutingAlgebra W} (hM : A.IsMonotone) {k : ℕ} (hk : 1 ≤ k)
    {w : Fin p → W} (h42 : Condition42 A k w) (hp : 2 ≤ p) (i : Fin p) (t : Fin q) :
    Traversable A (G := graph word) (wts A w) (.inl i) (.inr (.inr t)) := by
  refine ⟨twoHop word i t, twoHop_isPath word i t, ?_⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin p, i ≠ j := by
    by_cases h : i = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, h⟩
  rw [weight_twoHop]
  exact ne_of_lt (((pow_le_pow_of_le hM _ (by omega : 2 ≤ 2 * k))).trans_lt
    ((h42 i j hj).trans_le (emb_le_emb.2 (A.le_phi _))))

/-- Every stretch-`k` routing function on the family graph sends a packet from `cᵢ` to `t` towards
`z_{i, word t i}`: the local routing function of `cᵢ` (with the labels and ports) determines row `i` of the
words. -/
theorem route_eq_of_implementsStretch {A : RoutingAlgebra W} (hM : A.IsMonotone) {k : ℕ} (hk : 1 ≤ k)
    {w : Fin p → W} (h42 : Condition42 A k w) (hp : 2 ≤ p) (R : RoutingFunction (graph word))
    (hR : ImplementsStretch A (wts A w) k R) (i : Fin p) (t : Fin q) :
    (R.route (.inl i) (R.label (.inr (.inr t)))).2 = R.port (.inl i) (.inr (.inl (i, word t i))) := by
  obtain ⟨P, hP, hPk, hgen⟩ := hR (.inl i) (.inr (.inr t)) (by simp)
    (traversable_twoHop word hM hk h42 hp i t)
  rcases eq_twoHop_or_two_lt word i t P with rfl | hlen
  · exact hgen.1
  · exfalso
    have h1 := weight_gt_of_two_lt_length word hM h42 i t P hP hlen
    have h2 : weight A (wts A w) P ≤ A.emb (w i) ^ (2 * k) := by
      have := hPk
      rw [IsWithinStretch, pw_eq word hM hk h42, ← pow_mul] at this
      exact this
    exact absurd (h1.trans_le h2) (lt_irrefl _)

theorem neighborSet_c (i : Fin p) :
    (graph word).neighborSet (.inl i) = Set.range fun j : Fin δ => (.inr (.inl (i, j)) : Node p δ q) := by
  ext v
  rcases v with i' | ⟨i', j⟩ | t <;> simp [graph, Rel, eq_comm]

theorem ncard_neighborSet_c (i : Fin p) : ((graph word).neighborSet (.inl i)).ncard = δ := by
  rw [neighborSet_c, Set.ncard_range_of_injective (fun j j' h => by simpa using h), Nat.card_fin]

theorem card_node : Nat.card (Node p δ q) = p + p * δ + q := by
  simp; ring

theorem connected (hp : 1 ≤ p) (hδ : 1 ≤ δ) (hq : 1 ≤ q) : (graph word).Connected := by
  have := hδ
  set t₀ : Fin q := ⟨0, by omega⟩
  set i₀ : Fin p := ⟨0, by omega⟩
  have hc : ∀ i : Fin p, (graph word).Reachable (.inl i) (.inr (.inr t₀)) := fun i =>
    (adj_cz word i (word t₀ i)).reachable.trans (adj_zt word t₀ i).reachable
  have hall : ∀ v : Node p δ q, (graph word).Reachable v (.inl i₀) := by
    intro v
    rcases v with i | ⟨i, j⟩ | t
    · exact (hc i).trans (hc i₀).symm
    · exact (adj_cz word i j).reachable.symm.trans ((hc i).trans (hc i₀).symm)
    · exact ((adj_zt word t i₀).reachable.symm).trans (adj_cz word i₀ (word t i₀)).reachable.symm
  have : Nonempty (Node p δ q) := ⟨.inl i₀⟩
  exact ⟨fun u v => (hall u).trans (hall v).symm⟩

end Family

/-- `mem` behaves like a code length: fewer than `2 ^ b` local routing functions have code length `< b`
(true e.g. for the length of the shortest description w.r.t. any fixed decoder of binary strings, with `⊤` for
functions that have no description). -/
def CodeLength (mem : MemoryMeasure) : Prop :=
  ∀ b : ℕ, {f | mem f < b}.Finite ∧ {f | mem f < b}.ncard ≤ 2 ^ b

/-- `CodeLength` is satisfiable, e.g. by the measure that assigns `⊤` to every function. -/
theorem codeLength_top : CodeLength (fun _ => ⊤) := fun b => by simp

/-- A code-length measure must give `⊤` to some functions: there are uncountably many local routing functions
`ℕ → ℕ × ℕ`, so a finite-valued measure cannot have only finitely many functions below each bound. (This is why
`MemoryMeasure` takes values in `ℕ∞`.) -/
theorem not_codeLength_of_ne_top {mem : MemoryMeasure} (hmem : ∀ f, mem f ≠ ⊤) : ¬ CodeLength mem := by
  intro h
  have hc : (Set.univ : Set (ℕ → ℕ × ℕ)).Countable := by
    have : (Set.univ : Set (ℕ → ℕ × ℕ)) = ⋃ b : ℕ, {f | mem f < b} := by
      ext f
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 (hmem f)
      exact ⟨m + 1, show mem f < ((m + 1 : ℕ) : ℕ∞) by rw [← hm]; exact_mod_cast Nat.lt_succ_self m⟩
    rw [this]
    exact Set.countable_iUnion fun b => (h b).1.countable
  rw [Set.countable_univ_iff] at hc
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ → ℕ × ℕ)
  obtain ⟨m, hm⟩ := he (fun n => ((e n n).1 + 1, 0))
  have h1 := congrArg Prod.fst (congrFun hm m)
  dsimp only at h1
  omega

open Family in
/-- The counting step of Theorem 4.17 (after Fraigniaud–Gavoille): if for every choice of the words (`δ = 2`) some
stretch-`k` routing function has labels below `n ^ c` and local memory `< b` at every centre, then
`2^{pq} ≤ (n^c)^q · 3^{2p} · (2^b)^p`. -/
theorem card_bound {A : RoutingAlgebra W} (hM : A.IsMonotone) {k : ℕ} (hk : 1 ≤ k) {p q : ℕ}
    {w : Fin p → W} (h42 : Condition42 A k w) (hp : 2 ≤ p) {mem : MemoryMeasure} (hmem : CodeLength mem)
    {c n b : ℕ}
    (h : ∀ word : Fin q → Fin p → Fin 2, ∃ R : RoutingFunction (graph word),
      ImplementsStretch A (wts A w) k R ∧ R.LabelsBounded c n ∧ ∀ i, mem (R.route (.inl i)) < b) :
    2 ^ (p * q) ≤ (n ^ c) ^ q * 3 ^ (2 * p) * (2 ^ b) ^ p := by
  choose R hR using h
  let T := {f : ℕ → ℕ × ℕ // mem f < b}
  have hTfin : Finite T := (hmem b).1.to_subtype
  have hTcard : Nat.card T ≤ 2 ^ b := by
    have := (hmem b).2
    rwa [← Nat.card_coe_set_eq] at this
  have hport : ∀ (word : Fin q → Fin p → Fin 2) (i : Fin p) (j : Fin 2),
      (R word).port (.inl i) (.inr (.inl (i, j))) < 3 := by
    intro word i j
    have := ((R word).port_mem _ _ (adj_cz word i j)).2
    rw [ncard_neighborSet_c] at this
    omega
  let Φ : (Fin q → Fin p → Fin 2) → (Fin q → Fin (n ^ c)) × (Fin p → Fin 2 → Fin 3) × (Fin p → T) :=
    fun word => (fun t => ⟨(R word).label (.inr (.inr t)), (hR word).2.1 _⟩,
      fun i j => ⟨(R word).port (.inl i) (.inr (.inl (i, j))), hport word i j⟩,
      fun i => ⟨(R word).route (.inl i), (hR word).2.2 i⟩)
  have hΦ : Function.Injective Φ := by
    intro w₁ w₂ heq
    simp only [Φ, Prod.mk.injEq, funext_iff, Fin.ext_iff, Subtype.ext_iff] at heq
    obtain ⟨hl, hpo, hro⟩ := heq
    funext t i
    have e₁ := route_eq_of_implementsStretch w₁ hM hk h42 hp (R w₁) (hR w₁).1 i t
    have e₂ := route_eq_of_implementsStretch w₂ hM hk h42 hp (R w₂) (hR w₂).1 i t
    rw [hl t, hro i, e₂, ← hpo i (w₂ t i)] at e₁
    have := (R w₁).port_injOn (.inl i) (adj_cz w₁ i (w₁ t i)) (adj_cz w₁ i (w₂ t i)) e₁.symm
    simpa using this
  have := Nat.card_le_card_of_injective Φ hΦ
  simp only [Nat.card_prod, Nat.card_fun, Nat.card_fin] at this
  calc 2 ^ (p * q) = (2 ^ p) ^ q := by rw [pow_mul]
    _ ≤ (n ^ c) ^ q * ((3 ^ 2) ^ p * Nat.card T ^ p) := this
    _ ≤ (n ^ c) ^ q * ((3 ^ 2) ^ p * (2 ^ b) ^ p) := by gcongr
    _ = (n ^ c) ^ q * 3 ^ (2 * p) * (2 ^ b) ^ p := by rw [← pow_mul, mul_assoc, ← pow_mul]

theorem arith_contra (n p q b X : ℕ) (hp : p = n / 4) (hq : q = n - 3 * p) (hb : b = n / 8 + 1)
    (hn : 8 * X + 64 ≤ n) (h : p * q ≤ X * q + 4 * p + b * p) : False := by
  have h1 : 2 * X + 16 ≤ p := by omega
  have h2 : p ≤ q := by omega
  have h3 : 2 * b ≤ p + 2 := by omega
  have h4 : 2 * (p * q) ≤ 2 * (X * q) + 8 * p + (p + 2) * p := by nlinarith
  have h5 : p * q ≤ 2 * (X * q) + 10 * q := by nlinarith
  have h6 : (2 * X + 16) * q ≤ p * q := Nat.mul_le_mul_right q h1
  have hq0 : 0 < q := by omega
  nlinarith

theorem linear_le_two_pow (K L : ℕ) (hL : 2 * (2 * K + 64) ≤ L) : K * (L + 1) + 64 ≤ 2 ^ L := by
  obtain ⟨m, hm⟩ : ∃ m, m = 2 * K + 64 := ⟨_, rfl⟩
  rw [← hm] at hL
  have hm2 : m < 2 ^ m := Nat.lt_two_pow_self
  induction L, hL using Nat.le_induction with
  | base =>
    have : (m + 1) ^ 2 ≤ 2 ^ (2 * m) := by
      rw [mul_comm, pow_mul]; exact Nat.pow_le_pow_left hm2 2
    subst hm
    nlinarith
  | succ L hL ih =>
    have : K ≤ 2 ^ L := by
      have : 2 ^ m ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [pow_succ]; nlinarith

theorem eventually_log_le (c : ℕ) : ∀ᶠ n : ℕ in atTop, 8 * (c * (Nat.log 2 n + 1)) + 64 ≤ n := by
  filter_upwards [eventually_ge_atTop (2 ^ (2 * (2 * (8 * c) + 64)))] with n hn
  have hn0 : n ≠ 0 := by have := Nat.one_le_two_pow.trans hn; omega
  have hL := Nat.le_log_of_pow_le (by norm_num) hn
  have h1 := linear_le_two_pow (8 * c) _ hL
  have h2 := Nat.pow_log_le_self 2 hn0
  have : 8 * (c * (Nat.log 2 n + 1)) = 8 * c * (Nat.log 2 n + 1) := by ring
  omega

/-- **Theorem 4.17** of [paper]: if `A` is monotone and for every `p` there are weights `w₁, …, w_p` with
`wᵢ ⊕ wⱼ ≻ wᵢ^{2k}` for `i ≠ j` (condition (4.2)), then stretch-`k` routing in `A` is incompressible: some graph on
`n` nodes needs `Ω(n)` bits of local memory at some node (here `≥ n/8` for large `n`), for every code-length
memory measure and every label size `c log n`. -/
theorem theorem_4_17 {A : RoutingAlgebra W} (hM : A.IsMonotone) {k : ℕ} (hk : 1 ≤ k)
    (h42 : ∀ p : ℕ, ∃ w : Fin p → W, Family.Condition42 A k w) {mem : MemoryMeasure} (hmem : CodeLength mem)
    (c : ℕ) : Incompressible (memReqStretch A mem c k) := by
  refine ⟨8, by norm_num, ?_⟩
  filter_upwards [eventually_log_le c] with n hn
  set p := n / 4 with hp
  set q := n - 3 * p with hq
  set b := n / 8 + 1 with hb
  by_contra hlt
  push_neg at hlt
  set M := memReqStretch A mem c k n
  have hMb : M < b := by
    rcases (ENat.ne_top_iff_exists.1 (ne_top_of_lt (lt_of_le_of_lt (le_mul_of_one_le_left'
      (by norm_num : (1 : ℕ∞) ≤ 8)) hlt))) with ⟨m, hm⟩
    rw [← hm] at hlt ⊢
    have : ((8 * m : ℕ) : ℕ∞) < n := by push_cast; exact hlt
    have : 8 * m < n := by exact_mod_cast this
    exact_mod_cast (by omega : m < b)
  obtain ⟨w, hw⟩ := h42 p
  have hp2 : 2 ≤ p := by omega
  have hcard : Nat.card (Family.Node p 2 q) = n := by rw [Family.card_node]; omega
  have hR : ∀ word : Fin q → Fin p → Fin 2, ∃ R : RoutingFunction (Family.graph word),
      ImplementsStretch A (Family.wts A w) k R ∧ R.LabelsBounded c n ∧
        ∀ i, mem (R.route (.inl i)) < b := by
    intro word
    have hle := le_memReqStretch (A := A) (mem := mem) (c := c) (k := k) hcard (Family.graph word)
      (Family.connected word (by omega) (by norm_num) (by omega)) (Family.wts A w)
    obtain ⟨R, hR, hRm⟩ : ∃ R : RoutingFunction (Family.graph word),
        (ImplementsStretch A (Family.wts A w) k R ∧ R.LabelsBounded c n) ∧ R.maxMem mem < b := by
      have := hle.trans_lt hMb
      simp only [minMem, iInf_lt_iff] at this
      obtain ⟨R, hR, h⟩ := this
      exact ⟨R, hR, h⟩
    refine ⟨R, hR.1, hR.2, fun i => ?_⟩
    have : (mem (R.route (.inl i)) : ℕ∞) < b :=
      (le_iSup (fun u => (mem (R.route u) : ℕ∞)) (.inl i)).trans_lt hRm
    exact_mod_cast this
  have hcount := card_bound hM hk hw hp2 hmem hR
  -- `n < 2 ^ (L + 1)`
  set L := Nat.log 2 n
  have hnL : n < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have e1 : (n ^ c) ^ q ≤ 2 ^ (c * (L + 1) * q) := by
    rw [mul_comm c, pow_mul, pow_mul]
    exact Nat.pow_le_pow_left (Nat.pow_le_pow_left hnL.le c) q
  have e2 : 3 ^ (2 * p) ≤ 2 ^ (4 * p) := by
    rw [pow_mul, pow_mul]; exact Nat.pow_le_pow_left (by norm_num) p
  have e3 : 2 ^ (p * q) ≤ 2 ^ (c * (L + 1) * q + 4 * p + b * p) := by
    calc 2 ^ (p * q) ≤ (n ^ c) ^ q * 3 ^ (2 * p) * (2 ^ b) ^ p := hcount
      _ ≤ 2 ^ (c * (L + 1) * q) * 2 ^ (4 * p) * 2 ^ (b * p) := by
        rw [← pow_mul 2 b p]; exact Nat.mul_le_mul (Nat.mul_le_mul e1 e2) le_rfl
      _ = _ := by rw [← pow_add, ← pow_add]
  have e4 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 e3
  exact arith_contra n p q b (c * (L + 1)) hp hq hb hn e4

end Podc.CompactPolicyRouting
