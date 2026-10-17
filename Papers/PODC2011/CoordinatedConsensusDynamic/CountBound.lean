import Papers.PODC2011.CoordinatedConsensusDynamic.Simultaneous

/-!
# Theorem 4.1: eventual consensus with a factor-2 upper bound on the count

System `BoundN`: every node receives the same number `N ≥ n` (an upper bound on the count).
For `i ∈ {0,1}` the signature `σ_{V,i}` gives input `i` to everybody and the bound `N = 2n`.

**Theorem 4.1 (as stated).** For any comparison-based algorithm there is an `i ∈ {0,1}` such that
in *any* execution `(V, E, σ_{V,i})`, no node `u` decides at time `t` unless `past(u,t)(0) = V`.

The quantifier order makes this false: the bit `i` may have to depend on `n`. The algorithm
`cexRule` ignores UIDs; with bound `N` it is biased towards `bias N` (= `0` iff `⌊N/2⌋` is even):
decide `bias N` as soon as an input `bias N` has been heard, otherwise decide `¬ bias N` at time
`N - 1`. It solves consensus in `BoundN` (`cexRule_consensus`), is comparison-based
(`cexRule_comparisonBased`), and violates the literal statement for both `i`
(`theorem_4_1_literal_false`: `n = 2` all zeros, `n = 3` all ones, decision at time `0`).

The paper's proof (stitching two executions with disjoint UIDs and giving everybody the bound
`2n`) works when both executions have the same size `n`, i.e. for the corrected statement
"for every `n` there is an `i` …", which we prove as `theorem_4_1`.
-/

namespace CoordCons

open DGraph Relation Function

variable {α : Type*}

/-! ### Renaming nodes along an injection -/

namespace DGraph

open Classical in
/-- Rename the nodes along an injection `f` (inputs outside the image are irrelevant). -/
noncomputable def embed (G : DGraph α) (f : ℕ → ℕ) : DGraph α where
  V := G.V.image f
  input x := if h : ∃ y, f y = x then G.input h.choose else G.input x
  N := G.N
  adj r x y := ∃ a b, f a = x ∧ f b = y ∧ G.adj r a b

variable {G : DGraph α} {f : ℕ → ℕ}

theorem embed_input (hf : Injective f) (w : ℕ) : (G.embed f).input (f w) = G.input w := by
  have h : ∃ y, f y = f w := ⟨w, rfl⟩
  simp only [embed, dif_pos h]
  rw [hf h.choose_spec]

theorem embed_adj (hf : Injective f) (r a b : ℕ) :
    (G.embed f).adj r (f a) (f b) ↔ G.adj r a b := by
  simp only [embed]
  constructor
  · rintro ⟨a', b', ha, hb, h⟩; rw [← hf ha, ← hf hb]; exact h
  · intro h; exact ⟨a, b, rfl, rfl, h⟩

theorem reach_embed (hf : Injective f) {w s u t : ℕ} (h : G.Reach w s u t) :
    (G.embed f).Reach (f w) s (f u) t := by
  induction h with
  | refl => exact .refl
  | step _ hs ih =>
    rcases hs with rfl | hs
    · exact ih.stay
    · exact .step ih (Or.inr ((embed_adj hf _ _ _).2 hs))

theorem reach_of_embed (hf : Injective f) {x s y t : ℕ} (h : (G.embed f).Reach x s y t) :
    ∀ u, y = f u → ∃ w, x = f w ∧ G.Reach w s u t := by
  induction h with
  | refl => intro u hu; exact ⟨u, hu, .refl⟩
  | @step z y t _ hs ih =>
    intro u hu
    rcases hs with rfl | ⟨a, b, ha, hb, hab⟩
    · obtain ⟨w, hw, hr⟩ := ih u hu
      exact ⟨w, hw, hr.stay⟩
    · obtain ⟨w, hw, hr⟩ := ih a ha.symm
      rw [hu] at hb
      exact ⟨w, hw, .step hr (Or.inr (hf hb ▸ hab))⟩

theorem Valid.embed (hG : G.Valid) (hf : Injective f) : (G.embed f).Valid := by
  refine ⟨hG.nonempty.image f, fun r x y h => ?_, fun r x y h => ?_, fun r x h => ?_,
    fun r hr x hx y hy => ?_⟩
  · obtain ⟨a, b, rfl, rfl, h⟩ := h
    exact ⟨Finset.mem_image_of_mem f (hG.mem _ _ _ h).1,
      Finset.mem_image_of_mem f (hG.mem _ _ _ h).2⟩
  · obtain ⟨a, b, rfl, rfl, h⟩ := h
    exact ⟨b, a, rfl, rfl, hG.symm _ _ _ h⟩
  · obtain ⟨a, b, ha, hb, h⟩ := h
    exact hG.irrefl r a (hf (ha.trans hb.symm) ▸ h)
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
    have key : ∀ c d, ReflTransGen (G.adj r) c d →
        ReflTransGen ((G.embed f).adj r) (f c) (f d) := by
      intro c d h
      induction h with
      | refl => exact .refl
      | tail _ h ih => exact ih.tail ((embed_adj hf _ _ _).2 h)
    exact key a b (hG.conn r hr a ha b hb)

end DGraph

/-- Comparison-based decision rules: invariant under order-preserving renaming of the UIDs. -/
def ComparisonBased (D : Decision Bool) : Prop :=
  ∀ f : ℕ → ℕ, StrictMono f → ∀ G u t, D (G.embed f) (f u) t = D G u t

/-- The signature `σ_{V,i}`: all inputs `i`, bound `2n`. -/
def SigmaI (i : Bool) (G : DGraph Bool) : Prop :=
  G.Valid ∧ G.N = 2 * G.V.card ∧ ∀ w ∈ G.V, G.input w = i

/-- Theorem 4.1 exactly as stated (one `i` for executions of all sizes). -/
def Theorem41Literal (D : Decision Bool) : Prop :=
  ∃ i : Bool, ∀ G, SigmaI i G → ∀ u ∈ G.V, ∀ t, (D G u t).isSome → G.past u t 0 = G.V

/-! ### The counterexample algorithm -/

/-- The value the counterexample algorithm is biased towards, given the bound `N`. -/
def bias (N : ℕ) : Bool := decide (N / 2 % 2 = 1)

open Classical in
/-- Decide `bias N` once an input `bias N` has been heard; otherwise decide `¬ bias N` at time
`N - 1` (when everybody has been heard from, since `n ≤ N`). -/
noncomputable def cexRule : Decision Bool := fun G u t =>
  if ∃ w, G.Reach w 0 u t ∧ G.input w = bias G.N then some (bias G.N)
  else if G.N ≤ t + 1 then some (!bias G.N) else none

theorem cexRule_local : Local cexRule := by
  intro G H u t h
  have hex : (∃ w, G.Reach w 0 u t ∧ G.input w = bias G.N) ↔
      (∃ w, H.Reach w 0 u t ∧ H.input w = bias H.N) := by
    rw [h.N_eq]
    constructor
    · rintro ⟨w, hw, hi⟩; exact ⟨w, h.reach_iff.1 hw, h.input_eq hw ▸ hi⟩
    · rintro ⟨w, hw, hi⟩
      exact ⟨w, h.reach_iff.2 hw, (h.input_eq (h.reach_iff.2 hw)).symm ▸ hi⟩
  simp only [cexRule]
  by_cases hc : ∃ w, G.Reach w 0 u t ∧ G.input w = bias G.N
  · rw [if_pos hc, if_pos (hex.1 hc), h.N_eq]
  · rw [if_neg hc, if_neg (fun h' => hc (hex.2 h')), h.N_eq]

theorem cexRule_comparisonBased : ComparisonBased cexRule := by
  intro f hf G u t
  have hinj := hf.injective
  have hex : (∃ x, (G.embed f).Reach x 0 (f u) t ∧ (G.embed f).input x = bias (G.embed f).N) ↔
      (∃ w, G.Reach w 0 u t ∧ G.input w = bias G.N) := by
    constructor
    · rintro ⟨x, hx, hi⟩
      obtain ⟨w, rfl, hw⟩ := reach_of_embed hinj hx u rfl
      exact ⟨w, hw, (embed_input hinj w) ▸ hi⟩
    · rintro ⟨w, hw, hi⟩
      exact ⟨f w, reach_embed hinj hw, (embed_input hinj w).symm ▸ hi⟩
  simp only [cexRule, show (G.embed f).N = G.N from rfl]
  by_cases hc : ∃ w, G.Reach w 0 u t ∧ G.input w = bias G.N
  · rw [if_pos (hex.2 hc), if_pos hc]
  · rw [if_neg (fun h => hc (hex.1 h)), if_neg hc]

/-- After time `N - 1` the past is everything. -/
theorem reach_all_of_bound {G : DGraph Bool} (hG : BoundN G) {u t : ℕ} (hu : u ∈ G.V)
    (ht : G.N ≤ t + 1) : ∀ w ∈ G.V, G.Reach w 0 u t := by
  have hp := past_eq_V hG.1 hu (t := t) (s := 0) (by have := hG.2; omega)
  intro w hw
  exact (mem_past.1 (hp ▸ hw)).2

theorem cexRule_consensus : Consensus BoundN cexRule := by
  -- the value decided is always "is there an input `bias N`?"
  have hval : ∀ G, BoundN G → ∀ u ∈ G.V, ∀ t v, cexRule G u t = some v →
      v = if ∃ w ∈ G.V, G.input w = bias G.N then bias G.N else !bias G.N := by
    intro G hG u hu t v h
    simp only [cexRule] at h
    split_ifs at h with h1 h2
    · obtain ⟨w, hw, hi⟩ := h1
      rw [if_pos ⟨w, (hw.mem_iff hG.1).2 hu, hi⟩]; exact (Option.some.inj h).symm
    · rw [if_neg]
      · exact (Option.some.inj h).symm
      · rintro ⟨w, hw, hi⟩
        exact h1 ⟨w, reach_all_of_bound hG hu h2 w hw, hi⟩
  refine ⟨cexRule_local, ?_, ?_, ?_, ?_⟩
  · intro G hG u hu t v h
    have hv := hval G hG u hu t v h
    simp only [cexRule] at h ⊢
    split_ifs at h with h1 h2
    · rw [if_pos (by obtain ⟨w, hw, hi⟩ := h1; exact ⟨w, hw.stay, hi⟩)]; exact h
    · by_cases h3 : ∃ w, G.Reach w 0 u (t + 1) ∧ G.input w = bias G.N
      · exfalso
        obtain ⟨w, hw, hi⟩ := h3
        exact h1 ⟨w, reach_all_of_bound hG hu h2 w ((hw.mem_iff hG.1).2 hu), hi⟩
      · rw [if_neg h3, if_pos (by omega)]; exact h
  · intro G hG u hu w hw t t' a b ha hb
    rw [hval G hG u hu t a ha, hval G hG w hw t' b hb]
  · intro G hG u hu t v h
    rw [hval G hG u hu t v h]
    split_ifs with h1
    · obtain ⟨w, hw, hi⟩ := h1; exact ⟨w, hw, hi⟩
    · push Not at h1
      obtain ⟨w, hw⟩ := hG.1.nonempty
      refine ⟨w, hw, ?_⟩
      have := h1 w hw
      cases hb : bias G.N <;> cases hi : G.input w <;> simp_all
  · intro G hG u hu
    refine ⟨G.N, ?_⟩
    simp only [cexRule]
    split_ifs <;> simp_all

/-- **Theorem 4.1, as literally stated, is false**: the comparison-based consensus rule
`cexRule` (correct for every valid upper bound `N ≥ n`) decides at time `0`, before hearing from
everybody, in an all-`0` execution with `n = 2` and in an all-`1` execution with `n = 3`. -/
theorem theorem_4_1_literal_false : ¬ Theorem41Literal cexRule := by
  rintro ⟨i, hi⟩
  -- a complete graph with `n ≥ 2` nodes and bound `2n`: node `0` decides at time `0`
  have key : ∀ n : ℕ, 2 ≤ n → bias (2 * n) = i → False := by
    intro n hn hb
    have hS : SigmaI i (complete n i (2 * n)) :=
      ⟨complete_valid (by omega) i _, by simp [complete], fun w _ => rfl⟩
    have h0 : (0 : ℕ) ∈ (complete n i (2 * n)).V := by simp [complete]; omega
    have hdec : cexRule (complete n i (2 * n)) 0 0 = some i := by
      simp only [cexRule]
      rw [if_pos ⟨0, .refl, by simp [complete, hb]⟩]
      simp [complete, hb]
    have hp := hi _ hS 0 h0 0 (by simp [hdec])
    have h1 : (1 : ℕ) ∈ (complete n i (2 * n)).past 0 0 0 := by
      rw [hp]; simp [complete]; omega
    exact absurd (mem_past.1 h1).2.same_time (by decide)
  cases i
  · exact key 2 le_rfl (by decide)
  · exact key 3 (by norm_num) (by decide)

/-! ### The corrected Theorem 4.1 -/

namespace DGraph

/-- Stitch two executions with disjoint node sets by an edge `{a, b}` in every round. -/
def stitch (A B : DGraph Bool) (a b N : ℕ) : DGraph Bool where
  V := A.V ∪ B.V
  input x := if x ∈ A.V then A.input x else B.input x
  N := N
  adj r x y := A.adj r x y ∨ B.adj r x y ∨ (1 ≤ r ∧ ((x = a ∧ y = b) ∨ (x = b ∧ y = a)))

variable {A B : DGraph Bool} {a b N : ℕ}

theorem Valid.stitch (hA : A.Valid) (hB : B.Valid) (hdisj : Disjoint A.V B.V) (ha : a ∈ A.V)
    (hb : b ∈ B.V) : (A.stitch B a b N).Valid := by
  have hab : a ≠ b := fun h => Finset.disjoint_left.1 hdisj ha (h ▸ hb)
  have hsymm : ∀ r x y, (A.stitch B a b N).adj r x y → (A.stitch B a b N).adj r y x := by
    intro r x y h
    rcases h with h | h | ⟨h1, h2⟩
    · exact Or.inl (hA.symm _ _ _ h)
    · exact Or.inr (Or.inl (hB.symm _ _ _ h))
    · exact Or.inr (Or.inr ⟨h1, by tauto⟩)
  refine ⟨⟨a, Finset.mem_union_left _ ha⟩, fun r x y h => ?_, hsymm, fun r x h => ?_,
    fun r hr x hx y hy => ?_⟩
  · simp only [DGraph.stitch, Finset.mem_union]
    rcases h with h | h | ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨Or.inl (hA.mem _ _ _ h).1, Or.inl (hA.mem _ _ _ h).2⟩
    · exact ⟨Or.inr (hB.mem _ _ _ h).1, Or.inr (hB.mem _ _ _ h).2⟩
    · exact ⟨Or.inl ha, Or.inr hb⟩
    · exact ⟨Or.inr hb, Or.inl ha⟩
  · rcases h with h | h | ⟨-, ⟨rfl, h⟩ | ⟨rfl, h⟩⟩
    · exact hA.irrefl _ _ h
    · exact hB.irrefl _ _ h
    · exact hab h
    · exact hab h.symm
  · have key : ∀ z ∈ (A.stitch B a b N).V, ReflTransGen ((A.stitch B a b N).adj r) z a := by
      intro z hz
      rcases Finset.mem_union.1 hz with hz | hz
      · exact ReflTransGen.mono (fun p q h => Or.inl h) _ _ (hA.conn r hr z hz a ha)
      · exact (ReflTransGen.mono (fun p q h => Or.inr (Or.inl h)) _ _ (hB.conn r hr z hz b hb)).tail
          (Or.inr (Or.inr ⟨hr, Or.inr ⟨rfl, rfl⟩⟩))
    exact (key x hx).trans ((key y hy).symm_of (hsymm r))

theorem indist_stitch_left (hA : A.Valid) (hB : B.Valid) (hdisj : Disjoint A.V B.V)
    (hb : b ∈ B.V) {u t : ℕ} (hu : u ∈ A.V) (ha : ¬ A.Reach a 0 u t) (hN : A.N = N) :
    Indist A (A.stitch B a b N) u t := by
  refine indist_of_agree hA hu hN (fun w hw => ?_) (fun y s hy x => ?_)
  · have hwA := (hw.mem_iff hA).2 hu
    exact ⟨Finset.mem_union_left _ hwA, by simp [DGraph.stitch, hwA]⟩
  · have hyA := (hy.mem_iff hA).2 hu
    have hyB : y ∉ B.V := fun h => Finset.disjoint_left.1 hdisj hyA h
    have hya : y ≠ a := fun h => ha (h ▸ hy.mono_left (Nat.zero_le _))
    have hyb : y ≠ b := fun h => hyB (h ▸ hb)
    have hBxy : ¬ B.adj (s + 1) x y := fun h => hyB (hB.mem _ _ _ h).2
    simp [DGraph.stitch, hya, hyb, hBxy]

theorem indist_stitch_right (hA : A.Valid) (hB : B.Valid) (hdisj : Disjoint A.V B.V)
    (ha : a ∈ A.V) {u t : ℕ} (hu : u ∈ B.V) (hb : ¬ B.Reach b 0 u t) (hN : B.N = N) :
    Indist B (A.stitch B a b N) u t := by
  refine indist_of_agree hB hu hN (fun w hw => ?_) (fun y s hy x => ?_)
  · have hwB := (hw.mem_iff hB).2 hu
    have hwA : w ∉ A.V := fun h => Finset.disjoint_left.1 hdisj h hwB
    exact ⟨Finset.mem_union_right _ hwB, by simp [DGraph.stitch, hwA]⟩
  · have hyB := (hy.mem_iff hB).2 hu
    have hyA : y ∉ A.V := fun h => Finset.disjoint_left.1 hdisj h hyB
    have hyb : y ≠ b := fun h => hb (h ▸ hy.mono_left (Nat.zero_le _))
    have hya : y ≠ a := fun h => hyA (h ▸ ha)
    have hAxy : ¬ A.adj (s + 1) x y := fun h => hyA (hA.mem _ _ _ h).2
    simp [DGraph.stitch, hya, hyb, hAxy]

end DGraph

/-- **Theorem 4.1 (corrected quantifier order).** If every node is given the upper bound `2n`,
then for every comparison-based consensus algorithm and every `n` there is an `i ∈ {0,1}` such that
in every execution with `n` nodes and signature `σ_{V,i}`, no node decides before it has heard from
all nodes. -/
theorem theorem_4_1 {D : Decision Bool} (hD : Consensus BoundN D) (hcmp : ComparisonBased D)
    (n : ℕ) : ∃ i : Bool, ∀ G, SigmaI i G → G.V.card = n →
      ∀ u ∈ G.V, ∀ t, (D G u t).isSome → G.past u t 0 = G.V := by
  by_contra hcon
  push Not at hcon
  -- an execution for each input value in which some node decides early
  have hbad : ∀ i : Bool, ∃ G, SigmaI i G ∧ G.V.card = n ∧ ∃ u ∈ G.V, ∃ v ∈ G.V, ∃ t,
      ¬ G.Reach v 0 u t ∧ D G u t = some i := by
    intro i
    obtain ⟨G, hS, hn, u, hu, t, hdec, hp⟩ := hcon i
    obtain ⟨v, hv, hvp⟩ : ∃ v ∈ G.V, v ∉ G.past u t 0 := by
      by_contra h; push Not at h
      exact hp (Finset.Subset.antisymm (past_subset _ _ _) h)
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hdec
    have hB : BoundN G := ⟨hS.1, by rw [hS.2.1]; omega⟩
    obtain ⟨w, hw, hwa⟩ := hD.validity G hB u hu t a ha
    have : a = i := hwa ▸ hS.2.2 w hw
    subst this
    exact ⟨G, hS, hn, u, hu, v, hv, t, fun h => hvp (mem_past.2 ⟨hv, h⟩), ha⟩
  obtain ⟨G₀, hS₀, hn₀, u₀, hu₀, v₀, hv₀, t₀, hr₀, hd₀⟩ := hbad false
  obtain ⟨G₁, hS₁, hn₁, u₁, hu₁, v₁, hv₁, t₁, hr₁, hd₁⟩ := hbad true
  -- shift the UIDs of `G₁` above those of `G₀`
  set M := G₀.V.sup id + 1
  set f : ℕ → ℕ := fun x => x + M
  have hf : StrictMono f := fun x y h => by simp only [f]; omega
  have hinj := hf.injective
  set G₁' := G₁.embed f
  have hV₁' : G₁'.V = G₁.V.image f := rfl
  have hdisj : Disjoint G₀.V G₁'.V := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [hV₁', Finset.mem_image] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    have := Finset.le_sup (f := id) hx
    simp only [id, f, M] at this
    omega
  have hval₁' : G₁'.Valid := hS₁.1.embed hinj
  have hfv : f v₁ ∈ G₁'.V := Finset.mem_image_of_mem f hv₁
  have hfu : f u₁ ∈ G₁'.V := Finset.mem_image_of_mem f hu₁
  have hr₁' : ¬ G₁'.Reach (f v₁) 0 (f u₁) t₁ := by
    intro h
    obtain ⟨w, hw, hr⟩ := reach_of_embed hinj h u₁ rfl
    exact hr₁ (hinj hw ▸ hr)
  have hd₁' : D G₁' (f u₁) t₁ = some true := (hcmp f hf G₁ u₁ t₁).trans hd₁
  -- the stitched execution
  set H := G₀.stitch G₁' v₀ (f v₁) (2 * n)
  have hHv : H.Valid := hS₀.1.stitch hval₁' hdisj hv₀ hfv
  have hHB : BoundN H := by
    refine ⟨hHv, ?_⟩
    show (G₀.V ∪ G₁'.V).card ≤ 2 * n
    rw [Finset.card_union_of_disjoint hdisj, hV₁', Finset.card_image_of_injective _ hinj]
    omega
  have hi₀ : Indist G₀ H u₀ t₀ :=
    indist_stitch_left hS₀.1 hval₁' hdisj hfv hu₀ hr₀ (by rw [hS₀.2.1, hn₀])
  have hi₁ : Indist G₁' H (f u₁) t₁ :=
    indist_stitch_right hS₀.1 hval₁' hdisj hv₀ hfu hr₁' (by
      show G₁.N = 2 * n; rw [hS₁.2.1, hn₁])
  have := hD.agreement H hHB u₀ hi₀.mem_right (f u₁) hi₁.mem_right t₀ t₁ false true
    ((hD.loc _ _ _ _ hi₀).symm.trans hd₀) ((hD.loc _ _ _ _ hi₁).symm.trans hd₁')
  exact absurd this (by decide)

end CoordCons
