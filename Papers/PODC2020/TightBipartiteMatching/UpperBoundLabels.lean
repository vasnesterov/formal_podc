import Papers.PODC2020.TightBipartiteMatching.Problems

/-!
# Upper bound, part 1: recognising configurations of `Φ^W_Δ(x, y)` from label counts

Brandt–Olivetti, *Truly Tight-in-Δ Bounds for Bipartite Maximal Matching and Variants*, PODC 2020,
§5.

The converse direction of `phi_W_counts` / `phi_B_counts`: sufficient conditions, in terms of the
number of occurrences of each label, for a configuration to be allowed by the white or the black
constraint of `Phi d x y`.

* `phiW_matched`:   `1 ≤ #M ≤ y`, no `Z`, no `P` (pattern `[MOX]^{y-1}[M][OX]^{Δ-y}`);
* `phiW_unmatched`: only `P` and `X`, at least `Δ - x` labels `P` (pattern `[PX]^x[P]^{Δ-x}`);
* `phiB_matched`:   `1 ≤ #M ≤ y`, no `Z` (pattern `[MPOX]^{y-1}[M][POX]^{Δ-y}`);
* `phiB_unmatched`: only `O` and `X`, at most `x` labels `X` (pattern `[OX]^x[O]^{Δ-x}`).
-/

namespace TightBipartiteMatching

open Lab

-- CSLib candidate (generic multiset lemma)
/-- Split off `n` elements satisfying `p` from a multiset containing at least `n` of them. -/
theorem exists_split {α : Type*} (p : α → Prop) [DecidablePred p] (m : Multiset α) (n : ℕ)
    (h : n ≤ m.countP p) :
    ∃ m₁ m₂, m = m₁ + m₂ ∧ Multiset.card m₁ = n ∧ ∀ a ∈ m₁, p a := by
  induction m using Multiset.induction_on generalizing n with
  | empty =>
    simp only [Multiset.countP_zero, Nat.le_zero] at h; subst h
    exact ⟨0, 0, by simp, by simp, by simp⟩
  | cons a m ih =>
    by_cases hp : p a
    · rcases n with _ | n
      · exact ⟨0, a ::ₘ m, by simp, by simp, by simp⟩
      · rw [Multiset.countP_cons_of_pos _ hp] at h
        obtain ⟨m₁, m₂, rfl, h1, h2⟩ := ih n (by omega)
        refine ⟨a ::ₘ m₁, m₂, by simp, by simp [h1], ?_⟩
        intro b hb
        rcases Multiset.mem_cons.1 hb with rfl | hb
        exacts [hp, h2 b hb]
    · rw [Multiset.countP_cons_of_neg _ hp] at h
      obtain ⟨m₁, m₂, rfl, h1, h2⟩ := ih n h
      exact ⟨m₁, a ::ₘ m₂, by simp, h1, h2⟩

/-- `countP` of a predicate on labels, in terms of the five label counts. -/
theorem countP_lab (p : Lab → Prop) [DecidablePred p] (m : Multiset Lab) :
    m.countP p = (if p M then m.count M else 0) + (if p Z then m.count Z else 0) +
      (if p P then m.count P else 0) + (if p O then m.count O else 0) +
      (if p X then m.count X else 0) := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.countP_cons, ih]
    cases a <;> simp only [Multiset.count_cons, reduceCtorEq, ite_true, ite_false] <;>
      split_ifs <;> omega

theorem count_eq_zero_of_forall {m : Multiset Lab} {ℓ : Lab} (h : ∀ a ∈ m, a ≠ ℓ) :
    m.count ℓ = 0 :=
  Multiset.count_eq_zero.2 fun hm => h _ hm rfl

theorem gen2_intro {S₁ S₂ : Set Lab} {n₁ n₂ : ℕ} {m₁ m₂ : Multiset Lab}
    (h1 : Multiset.card m₁ = n₁) (h1' : ∀ a ∈ m₁, a ∈ S₁)
    (h2 : Multiset.card m₂ = n₂) (h2' : ∀ a ∈ m₂, a ∈ S₂) :
    m₁ + m₂ ∈ Cond.Gen [(S₁, n₁), (S₂, n₂)] :=
  Cond.gen_cons.2 ⟨m₁, m₂, rfl, h1, h1', Cond.gen_cons.2 ⟨m₂, 0, by simp, h2, h2', by simp⟩⟩

theorem gen3_intro {S₁ S₂ S₃ : Set Lab} {n₁ n₂ n₃ : ℕ} {m₁ m₂ m₃ : Multiset Lab}
    (h1 : Multiset.card m₁ = n₁) (h1' : ∀ a ∈ m₁, a ∈ S₁)
    (h2 : Multiset.card m₂ = n₂) (h2' : ∀ a ∈ m₂, a ∈ S₂)
    (h3 : Multiset.card m₃ = n₃) (h3' : ∀ a ∈ m₃, a ∈ S₃) :
    m₁ + m₂ + m₃ ∈ Cond.Gen [(S₁, n₁), (S₂, n₂), (S₃, n₃)] := by
  rw [add_assoc]
  exact Cond.gen_cons.2 ⟨m₁, m₂ + m₃, rfl, h1, h1', gen2_intro h2 h2' h3 h3'⟩

variable {d : ℕ}

/-- Shared core of `phiW_matched` and `phiB_matched`: split a configuration with
`1 ≤ #M ≤ y` and no `Z` into `y - 1` arbitrary labels, one `M`, and `Δ - y` labels from
`{P, O, X}`. -/
theorem split_matched {y : ℕ} (hy1 : 1 ≤ y) (hyd : y ≤ d + 1) {m : Multiset Lab}
    (hc : Multiset.card m = d + 1) (hM1 : 1 ≤ m.count M) (hMy : m.count M ≤ y)
    (hZ : m.count Z = 0) :
    ∃ m₁ m₂ m₃, m = m₁ + m₂ + m₃ ∧ Multiset.card m₁ = y - 1 ∧ (∀ a ∈ m₁, a ≠ Z ∧ a ∈ m) ∧
      Multiset.card m₂ = 1 ∧ (∀ a ∈ m₂, a = M) ∧ Multiset.card m₃ = d + 1 - y ∧
      (∀ a ∈ m₃, a = P ∨ a = O ∨ a = X) := by
  obtain ⟨a, r, rfl, ha1, ha2⟩ := exists_split (· = M) m 1 (by
    rw [countP_lab]; simpa using hM1)
  have hcM : a.count M = 1 := by
    rw [Multiset.count_eq_card.2 (fun b hb => (ha2 b hb).symm), ha1]
  have hcnt := card_eq_counts r
  have hcnt' := card_eq_counts (a + r)
  simp only [Multiset.count_add, hcM, Multiset.card_add, ha1] at hc hM1 hMy hZ hcnt' ⊢
  obtain ⟨b, c, rfl, hb1, hb2⟩ := exists_split (fun a => a = P ∨ a = O ∨ a = X) r (d + 1 - y)
    (by
      rw [countP_lab]
      have : a.count Z = 0 := count_eq_zero_of_forall fun b hb => by simp [ha2 b hb]
      simp only [reduceCtorEq, or_self, ite_false, or_false, false_or, ite_true]
      omega)
  simp only [Multiset.card_add] at hc
  refine ⟨c, a, b, by abel, by omega, fun e he => ⟨?_, ?_⟩, ha1, ha2, hb1, hb2⟩
  · rintro rfl
    have : 0 < c.count Z := Multiset.count_pos.2 he
    simp only [Multiset.count_add] at hZ
    omega
  · simp [he]

theorem phiW_matched {x y : ℕ} (hy1 : 1 ≤ y) (hyd : y ≤ d + 1) {m : Multiset Lab}
    (hc : Multiset.card m = d + 1) (hM1 : 1 ≤ m.count M) (hMy : m.count M ≤ y)
    (hZ : m.count Z = 0) (hP : m.count P = 0) : m ∈ (Phi d x y).W := by
  obtain ⟨m₁, m₂, m₃, rfl, h1, h1', h2, h2', h3, h3'⟩ := split_matched hy1 hyd hc hM1 hMy hZ
  refine ⟨_, List.mem_cons_self .., gen3_intro h1 ?_ h2 (by simpa using h2') h3 ?_⟩
  · intro a ha
    obtain ⟨haZ, ham⟩ := h1' a ha
    have haP : a ≠ P := by
      rintro rfl; exact (Multiset.count_eq_zero.1 hP) ham
    cases a <;> simp_all
  · intro a ha
    have haP : a ≠ P := by
      rintro rfl
      exact (Multiset.count_eq_zero.1 hP) (Multiset.mem_add.2 (Or.inr ha))
    rcases h3' a ha with rfl | rfl | rfl <;> simp_all

theorem phiB_matched {x y : ℕ} (hy1 : 1 ≤ y) (hyd : y ≤ d + 1) {m : Multiset Lab}
    (hc : Multiset.card m = d + 1) (hM1 : 1 ≤ m.count M) (hMy : m.count M ≤ y)
    (hZ : m.count Z = 0) : m ∈ (Phi d x y).B := by
  obtain ⟨m₁, m₂, m₃, rfl, h1, h1', h2, h2', h3, h3'⟩ := split_matched hy1 hyd hc hM1 hMy hZ
  refine ⟨_, List.mem_cons_self .., gen3_intro h1 ?_ h2 (by simpa using h2') h3
    (by simpa using h3')⟩
  intro a ha
  have := (h1' a ha).1
  cases a <;> simp_all

theorem phiW_unmatched {x y : ℕ} (hx : x ≤ d + 1) {m : Multiset Lab}
    (hc : Multiset.card m = d + 1) (hM : m.count M = 0) (hZ : m.count Z = 0)
    (hO : m.count O = 0) (hP : d + 1 - x ≤ m.count P) : m ∈ (Phi d x y).W := by
  obtain ⟨a, r, rfl, ha1, ha2⟩ := exists_split (· = P) m (d + 1 - x) (by
    rw [countP_lab]; simpa using hP)
  refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
  rw [add_comm a r]
  refine gen2_intro (by simp only [Multiset.card_add] at hc; omega) ?_ ha1 (by simpa using ha2)
  intro e he
  have hm : e ∈ a + r := Multiset.mem_add.2 (Or.inr he)
  have h1 : e ≠ M := by rintro rfl; exact Multiset.count_eq_zero.1 hM hm
  have h2 : e ≠ Z := by rintro rfl; exact Multiset.count_eq_zero.1 hZ hm
  have h3 : e ≠ O := by rintro rfl; exact Multiset.count_eq_zero.1 hO hm
  cases e <;> simp_all

theorem phiB_unmatched {x y : ℕ} (hx : x ≤ d + 1) {m : Multiset Lab}
    (hc : Multiset.card m = d + 1) (hM : m.count M = 0) (hZ : m.count Z = 0)
    (hP : m.count P = 0) (hX : m.count X ≤ x) : m ∈ (Phi d x y).B := by
  have hcnt := card_eq_counts m
  obtain ⟨a, r, rfl, ha1, ha2⟩ := exists_split (· = O) m (d + 1 - x) (by
    rw [countP_lab]; simp only [reduceCtorEq, ite_false, ite_true]; omega)
  refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
  rw [add_comm a r]
  refine gen2_intro (by simp only [Multiset.card_add] at hc; omega) ?_ ha1 (by simpa using ha2)
  intro e he
  have hm : e ∈ a + r := Multiset.mem_add.2 (Or.inr he)
  have h1 : e ≠ M := by rintro rfl; exact Multiset.count_eq_zero.1 hM hm
  have h2 : e ≠ Z := by rintro rfl; exact Multiset.count_eq_zero.1 hZ hm
  have h3 : e ≠ P := by rintro rfl; exact Multiset.count_eq_zero.1 hP hm
  cases e <;> simp_all

end TightBipartiteMatching
