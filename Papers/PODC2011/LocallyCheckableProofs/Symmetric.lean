import Papers.PODC2011.LocallyCheckableProofs.Star
import Papers.PODC2011.LocallyCheckableProofs.AsymCount

/-!
# Theorem 6.1: symmetry of connected graphs requires proofs of size `Ω(n²)`

A graph is *symmetric* if it has a non-trivial automorphism (`IsSymmetric`). Following the paper,
we glue two graphs `H₁`, `H₂` on `Fin k` by a path (`StarCons.star`). We restrict `H₁`, `H₂` to
*good*
graphs: asymmetric (`Asymm`) and such that any two distinct vertices have at least three common
neighbours (`ThreeCommon`). Then

* `H ⊛ H` is symmetric (`isSymmetric_star_self`);
* if `H₁`, `H₂` are good and non-isomorphic, `H₁ ⊛ H₂` is asymmetric (`not_isSymmetric_star`).

The paper says only "by the construction of `G`, `ϕ` must swap `G₁` and `G₂`". With the
three-common-neighbours property this is easy: the path nodes are exactly the nodes without three
distinct neighbours, so an automorphism maps the path onto itself (identity or reversal,
`StarCons.PathEnum`), and then each copy onto a copy (two copy vertices are joined by a path of
length two inside the copy).

Since almost all graphs are good (`exists_many_good`), there are `≥ 2^(k choose 2)/2` good graphs
on `Fin k`, i.e. at least `2^(k choose 2)/(2 k!)` isomorphism classes; the gluing/pigeonhole
argument
(`StarCons.card_le_of_glue`) bounds this number by `2^((s(n)+1)(2r+1))`, which gives Theorem 6.1.
-/

namespace Podc.LocallyCheckableProofs

open SimpleGraph Finset StarCons

/-- The graph of `I` (induced on its nodes) has a non-trivial automorphism. -/
def IsSymmetric {L : Type*} (I : Inst L) : Prop :=
  ∃ φ : I.G.induce (I.V : Set ℕ) ≃g I.G.induce (I.V : Set ℕ), ∃ v, φ v ≠ v

namespace SymStar

variable {p k : ℕ} {H₁ H₂ : SimpleGraph (Fin k)}

/-- `x` has three distinct neighbours. -/
def Three (G : SimpleGraph ℕ) (x : ℕ) : Prop :=
  ∃ y₁ y₂ y₃, y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ ∧ G.Adj x y₁ ∧ G.Adj x y₂ ∧ G.Adj x y₃

lemma three_of_isAut {L : Type*} {I : Inst L} {ψ : Equiv.Perm ℕ} (h : IsAut I ψ) {x : ℕ}
    (hx : Three I.G x) : Three I.G (ψ x) := by
  obtain ⟨y₁, y₂, y₃, h12, h13, h23, a1, a2, a3⟩ := hx
  exact ⟨ψ y₁, ψ y₂, ψ y₃, ψ.injective.ne h12, ψ.injective.ne h13, ψ.injective.ne h23,
    (h.adj _ _).2 a1, (h.adj _ _).2 a2, (h.adj _ _).2 a3⟩

lemma three_isAut_iff {L : Type*} {I : Inst L} {ψ : Equiv.Perm ℕ} (h : IsAut I ψ) {x : ℕ} :
    Three I.G (ψ x) ↔ Three I.G x :=
  ⟨fun hx => by simpa using three_of_isAut h.symm hx, three_of_isAut h⟩

lemma not_three_path {x : ℕ} (hx1 : 1 ≤ x) (hxp : x ≤ p) : ¬ Three (graph p k H₁ H₂) x := by
  rintro ⟨y₁, y₂, y₃, h12, h13, h23, a1, a2, a3⟩
  have := path_nbr hx1 hxp a1
  have := path_nbr hx1 hxp a2
  have := path_nbr hx1 hxp a3
  omega

lemma three_copy (hp : 1 ≤ p) (hk : 2 ≤ k) (h₁ : ThreeCommon H₁) (h₂ : ThreeCommon H₂) (b : Bool)
    (a : Fin k) :
    Three (graph p k H₁ H₂) (off p k b + a) := by
  obtain ⟨a', ha'⟩ : ∃ a' : Fin k, a' ≠ a := by
    by_cases h0 : (a : ℕ) = 0
    · exact ⟨⟨1, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
    · exact ⟨⟨0, by omega⟩, fun e => by rw [← e] at h0; simp at h0⟩
  have hb : ThreeCommon (hc H₁ H₂ b) := by cases b <;> assumption
  obtain ⟨c₁, c₂, c₃, h12, h13, h23, ⟨a1, -⟩, ⟨a2, -⟩, ⟨a3, -⟩⟩ := hb a a' ha'.symm
  have hne : ∀ c c' : Fin k, c ≠ c' → off p k b + (c : ℕ) ≠ off p k b + c' := by
    intro c c' h e; exact h (Fin.ext (by omega))
  exact ⟨_, _, _, hne _ _ h12, hne _ _ h13, hne _ _ h23, (copy_adj hp b a c₁).2 a1,
    (copy_adj hp b a c₂).2 a2, (copy_adj hp b a c₃).2 a3⟩

/-- With three common neighbours, the path nodes are exactly the nodes without three distinct
neighbours. -/
lemma three_iff (hp : 1 ≤ p) (hk : 2 ≤ k) (h₁ : ThreeCommon H₁) (h₂ : ThreeCommon H₂) {x : ℕ}
    (hx : x ∈ (star p k H₁ H₂).V) : ¬ Three (graph p k H₁ H₂) x ↔ 1 ≤ x ∧ x ≤ p := by
  refine ⟨fun h => ?_, fun h => not_three_path h.1 h.2⟩
  simp only [star_V, mem_Icc] at hx
  by_contra hxp
  apply h
  by_cases hx1 : x ≤ p + k
  · have := three_copy (H₁ := H₁) (H₂ := H₂) hp hk h₁ h₂ false ⟨x - p - 1, by omega⟩
    simp only [off] at this
    convert this using 1; omega
  · have := three_copy (H₁ := H₁) (H₂ := H₂) hp hk h₁ h₂ true ⟨x - p - k - 1, by omega⟩
    simp only [off] at this
    convert this using 1; omega

/-- The path nodes, enumerated. -/
lemma pathEnum (hp : 1 ≤ p) (hk : 2 ≤ k) (h₁ : ThreeCommon H₁) (h₂ : ThreeCommon H₂) :
    PathEnum (graph p k H₁ H₂) (fun x => x ∈ (star p k H₁ H₂).V ∧ ¬ Three (graph p k H₁ H₂) x)
      (p - 1) (fun i => i + 1) where
  mem v := by
    constructor
    · rintro ⟨hv, h⟩
      have := (three_iff hp hk h₁ h₂ hv).1 h
      exact ⟨v - 1, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      have hv : i + 1 ∈ (star p k H₁ H₂).V := by simp; omega
      exact ⟨hv, (three_iff hp hk h₁ h₂ hv).2 (by omega)⟩
  inj i _ j _ e := by omega
  adj i hi j hj := by
    rw [graph_adj]
    unfold pathRel
    constructor
    · rintro (h | h | ⟨a, b, -, e1, e2⟩ | ⟨a, b, -, e1, e2⟩) <;> omega
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))

/-- **Transfer of copies.** An automorphism mapping the root of copy `b` to the root of copy `b'`
maps copy `b` onto copy `b'` and induces an isomorphism of the corresponding graphs. -/
lemma transfer (hp : 1 ≤ p) (hk : 2 ≤ k) (h₁ : ThreeCommon H₁) (h₂ : ThreeCommon H₂)
    {ψ : Equiv.Perm ℕ} (hψ : IsAut (star p k H₁ H₂) ψ) (b b' : Bool)
    (h0 : ψ (off p k b) = off p k b') :
    ∃ σ : Equiv.Perm (Fin k), (∀ a : Fin k, ψ (off p k b + a) = off p k b' + σ a) ∧
      ∀ a c, (hc H₁ H₂ b').Adj (σ a) (σ c) ↔ (hc H₁ H₂ b).Adj a c := by
  have hb : ThreeCommon (hc H₁ H₂ b) := by cases b <;> assumption
  have nonpath : ∀ a : Fin k, ¬ (1 ≤ ψ (off p k b + a) ∧ ψ (off p k b + a) ≤ p) := by
    intro a h
    have := (three_isAut_iff hψ).2 (three_copy hp hk h₁ h₂ b a)
    exact not_three_path h.1 h.2 this
  have img : ∀ a : Fin k, ∃ c : Fin k, ψ (off p k b + a) = off p k b' + c := by
    intro a
    by_cases ha : (a : ℕ) = 0
    · exact ⟨⟨0, by omega⟩, by simp [ha, h0]⟩
    obtain ⟨c₁, -, -, -, -, -, ⟨a1, a2⟩, -, -⟩ := hb ⟨0, by omega⟩ a (fun e => ha (by rw [← e]))
    have e0 : ψ (off p k b + ((⟨0, by omega⟩ : Fin k) : ℕ)) =
        off p k b' + ((⟨0, by omega⟩ : Fin k) : ℕ) := by
      simp [h0]
    have s1 := (hψ.adj _ _).2 ((copy_adj hp b _ _).2 a1)
    rw [e0] at s1
    obtain ⟨d, hd⟩ := copy_nbr (H₁ := H₁) (H₂ := H₂) b' _ s1 (nonpath c₁)
    have s2 := (hψ.adj _ _).2 ((copy_adj hp b _ _).2 a2.symm)
    rw [hd] at s2
    exact copy_nbr (H₁ := H₁) (H₂ := H₂) b' d s2 (nonpath a)
  choose f hf using img
  have finj : Function.Injective f := by
    intro a c e
    have := ψ.injective ((hf a).trans (e ▸ (hf c).symm))
    exact Fin.ext (by omega)
  let σ := Equiv.ofBijective f (Finite.injective_iff_bijective.1 finj)
  refine ⟨σ, fun a => hf a, fun a c => ?_⟩
  change (hc H₁ H₂ b').Adj (f a) (f c) ↔ _
  rw [← copy_adj hp b', ← hf, ← hf]
  exact (hψ.adj _ _).trans (copy_adj hp b a c)

/-- **Good, non-isomorphic `H₁`, `H₂` give an asymmetric `H₁ ⊛ H₂`.** Every automorphism of
`H₁ ⊛ H₂` (as a permutation of `ℕ`) fixes all nodes. -/
theorem isAut_star_fix (hp : 2 ≤ p) (hk : 2 ≤ k) (g₁ : Asymm H₁ ∧ ThreeCommon H₁)
    (g₂ : Asymm H₂ ∧ ThreeCommon H₂) (hni : ∀ σ : Equiv.Perm (Fin k), H₂.comap σ ≠ H₁)
    {ψ : Equiv.Perm ℕ} (hψ : IsAut (star p k H₁ H₂) ψ) : ∀ v ∈ (star p k H₁ H₂).V, ψ v = v := by
  have hp1 : 1 ≤ p := by omega
  have hPE := pathEnum hp1 hk g₁.2 g₂.2
  have hQ : ∀ x, (ψ x ∈ (star p k H₁ H₂).V ∧ ¬ Three (graph p k H₁ H₂) (ψ x)) ↔
      (x ∈ (star p k H₁ H₂).V ∧ ¬ Three (graph p k H₁ H₂) x) := by
    intro x
    rw [hψ.mem, show Three (graph p k H₁ H₂) (ψ x) ↔ Three (graph p k H₁ H₂) x from
      three_isAut_iff hψ]
  have hadj : ∀ x y, (graph p k H₁ H₂).Adj (ψ x) (ψ y) ↔ (graph p k H₁ H₂).Adj x y := hψ.adj
  -- nodes of the copies are not mapped to path nodes
  have nonpath : ∀ b (a : Fin k), ¬ (1 ≤ ψ (off p k b + a) ∧ ψ (off p k b + a) ≤ p) := by
    intro b a h
    have := (three_isAut_iff hψ).2 (three_copy hp1 hk g₁.2 g₂.2 b a)
    exact not_three_path h.1 h.2 this
  have nonpath0 : ∀ b, ¬ (1 ≤ ψ (off p k b) ∧ ψ (off p k b) ≤ p) := by
    intro b; simpa using nonpath b ⟨0, by omega⟩
  have adj1 : (graph p k H₁ H₂).Adj 1 (off p k false) :=
    graph_adj.2 (Or.inl (Or.inr (Or.inl ⟨rfl, hp1, by omega, rfl⟩)))
  have adjp : (graph p k H₁ H₂).Adj p (off p k true) :=
    graph_adj.2 (Or.inl (Or.inr (Or.inr ⟨rfl, hp1, by omega, rfl⟩)))
  rcases hPE.end_cases hadj hQ with h1 | h1 <;> simp only [zero_add] at h1
  · -- `ψ` fixes the path, hence the roots, hence (by asymmetry) the copies
    have hpath := hPE.rigid hPE hadj hQ (by simpa using h1)
    have hpath' : ∀ x, 1 ≤ x → x ≤ p → ψ x = x := fun x h1 h2 => by
      simpa [Nat.sub_add_cancel h1] using hpath (x - 1) (by omega)
    have r1 : ψ (off p k false) = off p k false := by
      have := (hadj _ _).2 adj1
      rw [h1] at this
      have := path_nbr le_rfl hp1 this
      have := nonpath0 false
      simp only [off] at *; split_ifs at * <;> omega
    have r2 : ψ (off p k true) = off p k true := by
      have := (hadj _ _).2 adjp
      rw [hpath' p hp1 le_rfl] at this
      have := path_nbr hp1 le_rfl this
      have := nonpath0 true
      simp only [off] at *; split_ifs at * <;> omega
    obtain ⟨σ₁, hσ₁, ha₁⟩ := transfer hp1 hk g₁.2 g₂.2 hψ false false r1
    obtain ⟨σ₂, hσ₂, ha₂⟩ := transfer hp1 hk g₁.2 g₂.2 hψ true true r2
    have e₁ := g₁.1 σ₁ ha₁
    have e₂ := g₂.1 σ₂ ha₂
    intro v hv
    simp only [star_V, mem_Icc] at hv
    by_cases hvp : v ≤ p
    · exact hpath' v hv.1 hvp
    by_cases hvk : v ≤ p + k
    · have := hσ₁ ⟨v - p - 1, by omega⟩
      simp only [e₁, Equiv.Perm.coe_one, id, off] at this
      convert this using 2 <;> omega
    · have := hσ₂ ⟨v - p - k - 1, by omega⟩
      simp only [e₂, Equiv.Perm.coe_one, id, off] at this
      convert this using 2 <;> omega
  · -- `ψ` reverses the path, hence swaps the copies: `H₁ ≅ H₂`, a contradiction
    have r1 : ψ (off p k false) = off p k true := by
      have := (hadj _ _).2 adj1
      rw [show p - 1 + 1 = p by omega] at h1
      rw [h1] at this
      have := path_nbr hp1 le_rfl this
      have := nonpath0 false
      simp only [off] at *; split_ifs at * <;> omega
    obtain ⟨σ, -, hσ⟩ := transfer hp1 hk g₁.2 g₂.2 hψ false true r1
    exact absurd (by ext a c; exact hσ a c) (hni σ)

lemma connected_of_threeCommon {H : SimpleGraph (Fin k)} (hk : 0 < k) (h : ThreeCommon H) :
    H.Connected := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  refine ⟨fun a b => ?_⟩
  by_cases hab : a = b
  · subst hab; rfl
  obtain ⟨c, -, -, -, -, -, ⟨h1, h2⟩, -, -⟩ := h a b hab
  exact h1.reachable.trans h2.symm.reachable

/-- `H ⊛ H` is symmetric: the swap is a non-trivial automorphism. -/
theorem isSymmetric_star_self (hk : 0 < k) (H : SimpleGraph (Fin k)) :
    IsSymmetric (star p k H H) := by
  obtain ⟨φ, hφ⟩ := exists_iso_of_perm (swap_isAut (p := p) H)
  refine ⟨φ, ⟨p + 1, by simp; omega⟩, fun e => ?_⟩
  have := congrArg Subtype.val e
  have h' : swapFun p k (p + 1) = p + 1 := by rw [hφ] at this; simpa using this
  rw [swapFun_c1 (by omega) (by omega)] at h'
  omega

/-- If `H₁`, `H₂` are good and not isomorphic, `H₁ ⊛ H₂` is asymmetric. -/
theorem not_isSymmetric_star (hp : 2 ≤ p) (hk : 2 ≤ k) (g₁ : Asymm H₁ ∧ ThreeCommon H₁)
    (g₂ : Asymm H₂ ∧ ThreeCommon H₂) (hni : ∀ σ : Equiv.Perm (Fin k), H₂.comap σ ≠ H₁) :
    ¬ IsSymmetric (star p k H₁ H₂) := by
  rintro ⟨φ, v, hv⟩
  obtain ⟨ψ, hψ, hψφ⟩ := exists_perm_of_iso _ φ
  apply hv
  apply Subtype.ext
  rw [← hψφ]
  exact isAut_star_fix hp hk g₁ g₂ hni hψ v v.2

lemma four_mul_add_three_le_two_pow : ∀ m, 5 ≤ m → 4 * m + 3 ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge m 5 with h | h
    · interval_cases m <;> omega
    · have := ih h; rw [pow_succ]; omega

lemma two_mul_choose_two (k : ℕ) : 2 * k.choose 2 + k = k * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith

end SymStar

open SymStar

/-- **Theorem 6.1** of [GS16]: symmetry of connected graphs requires locally checkable proofs of
size `Ω(n²)`. Here `F` is any family containing all connected unlabelled graphs with identifiers in
`{1, …, n}`, and `IsSymmetric` is the property of having a non-trivial automorphism. The constant
`c` depends on the local horizon `r` of the verifier (`c = 1/(256 (2r+1))`). -/
theorem symmetric_lcp_lower_bound (F : Set (Inst Unit))
    (hF : ∀ I : Inst Unit, I.Plain → I.Conn → I.IdBound 1 → I ∈ F) {s : ℕ → ℕ}
    (h : AdmitsLCP F {I | IsSymmetric I} s) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → c * (n : ℝ) ^ 2 ≤ s n := by
  classical
  obtain ⟨r, A, hA, hc, hs⟩ := h
  obtain ⟨K, hK⟩ := exists_many_good
  refine ⟨1 / (256 * (2 * r + 1)), by positivity, 3 * (K + 16 * r + 20), fun n hn => ?_⟩
  set k := n / 3 with hkdef
  set p := n - 2 * k with hpdef
  have hk : K + 16 * r + 20 ≤ k := by omega
  have hpk : k ≤ p := by omega
  have hn' : p + 2 * k = n := by omega
  obtain ⟨𝒢, hgood, hcard⟩ := hK k (by omega)
  let R : SimpleGraph (Fin k) → SimpleGraph (Fin k) → Prop :=
    fun H₁ H₂ => ∀ σ : Equiv.Perm (Fin k), H₂.comap σ ≠ H₁
  have key := card_le_of_glue (p := p) 𝒢 id R k.factorial ?_ hA (by omega) (s n) ?_ ?_
  rotate_left
  · intro i _
    calc (𝒢.filter fun j => ¬ R j i).card
        ≤ ((univ : Finset (Equiv.Perm (Fin k))).image
            fun σ : Equiv.Perm (Fin k) => i.comap σ).card := by
          refine card_le_card (fun j hj => ?_)
          simp only [mem_filter, R, not_forall, not_not] at hj
          obtain ⟨σ, hσ⟩ := hj.2
          exact mem_image.2 ⟨σ, mem_univ _, hσ⟩
      _ ≤ (univ : Finset (Equiv.Perm (Fin k))).card := card_image_le
      _ = k.factorial := by simp [Fintype.card_perm]
  · intro i hi
    have hI : star p k i i ∈ F := hF _ star_plain
      (star_conn (by omega) (by omega) (connected_of_threeCommon (by omega) (hgood i hi).2)
        (connected_of_threeCommon (by omega) (hgood i hi).2)) star_idBound
    obtain ⟨P, hP, hacc⟩ := hc _ hI (isSymmetric_star_self (by omega) i)
    rw [star_n, hn'] at hP
    exact ⟨P, hP, hacc⟩
  · intro i hi j hj hij P
    have hI : star p k i j ∈ F := hF _ star_plain
      (star_conn (by omega) (by omega) (connected_of_threeCommon (by omega) (hgood i hi).2)
        (connected_of_threeCommon (by omega) (hgood j hj).2)) star_idBound
    exact hs _ hI (not_isSymmetric_star (by omega) (by omega) (hgood i hi) (hgood j hj) hij) P
  -- arithmetic
  set X := (s n + 1) * (2 * r + 1) with hX
  have hfac : k.factorial ≤ 2 ^ (k / 4 * k) := by
    calc k.factorial ≤ k ^ k := Nat.factorial_le_pow k
      _ ≤ (2 ^ (k / 4)) ^ k := by
          gcongr
          have := four_mul_add_three_le_two_pow (k / 4) (by omega)
          omega
      _ = 2 ^ (k / 4 * k) := by rw [pow_mul]
  have h2 : 2 ^ k.choose 2 ≤ 2 ^ (1 + k / 4 * k + X) := by
    calc 2 ^ k.choose 2 ≤ 2 * 𝒢.card := hcard
      _ ≤ 2 * (k.factorial * 2 ^ X) := by gcongr
      _ ≤ 2 * (2 ^ (k / 4 * k) * 2 ^ X) := by gcongr
      _ = 2 ^ (1 + k / 4 * k + X) := by rw [pow_add, pow_add, pow_one]; ring
  have h3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have h4 := two_mul_choose_two k
  have h5 : 4 * (k / 4) ≤ k := Nat.mul_div_le k 4
  have h6 : k * k ≤ 8 * X := by nlinarith
  have h7 : 2 * (2 * r + 1) ≤ X := by nlinarith
  have hs1 : 1 ≤ s n := by
    by_contra h0
    have : s n = 0 := by omega
    rw [this] at hX
    omega
  have h8 : n * n ≤ 256 * (2 * r + 1) * s n := by
    have : n ≤ 4 * k := by omega
    nlinarith
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  have : ((n * n : ℕ) : ℝ) ≤ ((256 * (2 * r + 1) * s n : ℕ) : ℝ) := by exact_mod_cast h8
  push_cast at this
  nlinarith

/-- **Theorem 6.1** of [GS16], `o`-notation form: proofs of size `o(n²)` do not suffice. -/
theorem symmetric_not_isLittleO (F : Set (Inst Unit))
    (hF : ∀ I : Inst Unit, I.Plain → I.Conn → I.IdBound 1 → I ∈ F) {s : ℕ → ℕ}
    (h : AdmitsLCP F {I | IsSymmetric I} s) :
    ¬ (fun n => (s n : ℝ)) =o[Filter.atTop] (fun n => (n : ℝ) ^ 2) := by
  intro ho
  obtain ⟨c, hc, N, hN⟩ := symmetric_lcp_lower_bound F hF h
  have hb := ho.bound (half_pos hc)
  rw [Filter.eventually_atTop] at hb
  obtain ⟨M, hM⟩ := hb
  have h1 := hN (max (max N M) 1) (by omega)
  have h2 := hM (max (max N M) 1) (by omega)
  set m := max (max N M) 1
  have hm : (1 : ℝ) ≤ m := by exact_mod_cast (le_max_right _ _)
  simp only [Real.norm_eq_abs, Nat.abs_cast, abs_pow] at h2
  have : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  nlinarith [mul_pos hc this]

end Podc.LocallyCheckableProofs
