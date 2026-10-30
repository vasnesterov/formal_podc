import Papers.PODC2026.OverwriteLeastFixedPoints.Distributed

/-!
# The transitive-closure example (Sections 2.1, 3.1, 4.1)

State: `R : V × V → Bool` ordered pointwise (`false < true`); `tcF (a, b)` sets `R[a,b]` to
`R[a,b] ∨ ∃ k, R[a,k] ∧ R[k,b]` and leaves the other coordinates unchanged; initial state
`R₀[a,b] = 1 iff (a,b) ∈ E ∨ a = b`.

* `isLeast_rtc`: the least common fixed point above `R₀` is the reflexive–transitive closure of `E`;
* `tc_interleaving`, `tc_parallel` (Algorithm 1), `tc_distributed` (Algorithm 3): each execution
  model computes it;
* `tc_parallel_rounds`: Section 3.1's round bound: if all `n²` threads run in every round, `R_t`
  contains every pair joined by a path of length `≤ 2^t`, so `R_t` is the closure as soon as
  `n - 1 ≤ 2^t`, i.e. after `⌈log₂ (n-1)⌉` rounds.
-/

namespace Podc.OverwriteLeastFixedPoints.TC

open Podc.OverwriteLeastFixedPoints

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The update function `f_{a,b}` of Section 2.1. -/
def tcF (p : V × V) (R : V × V → Bool) : V × V → Bool :=
  Function.update R p (R p || decide (∃ k, R (p.1, k) = true ∧ R (k, p.2) = true))

/-- The initial state `R₀`: edges and the diagonal. -/
def tcInit (E : V → V → Prop) [DecidableRel E] : V × V → Bool :=
  fun p => decide (E p.1 p.2 ∨ p.1 = p.2)

/-- The reflexive–transitive closure of `E` as a state. -/
noncomputable def rtc (E : V → V → Prop) : V × V → Bool :=
  fun p => by classical exact decide (Relation.ReflTransGen E p.1 p.2)

theorem tcF_self (R : V × V → Bool) (p : V × V) :
    tcF p R p = (R p || decide (∃ k, R (p.1, k) = true ∧ R (k, p.2) = true)) := by
  simp [tcF]

theorem tcF_ne (R : V × V → Bool) {p q : V × V} (h : q ≠ p) : tcF p R q = R q := by
  simp [tcF, Function.update_of_ne h]

theorem tcF_monotone (p : V × V) : Monotone (tcF p) := by
  intro R R' h q
  by_cases hq : q = p
  · subst hq
    rw [tcF_self, tcF_self]
    refine sup_le_sup (h q) ?_
    rw [Bool.le_iff_imp]
    simp only [decide_eq_true_eq]
    rintro ⟨k, h1, h2⟩
    exact ⟨k, le_antisymm le_top (h1 ▸ h _), le_antisymm le_top (h2 ▸ h _)⟩
  · rw [tcF_ne _ hq, tcF_ne _ hq]; exact h q

theorem tcF_inflationary (p : V × V) : Inflationary (tcF p) := by
  intro R q
  by_cases hq : q = p
  · subst hq; rw [tcF_self]; exact le_sup_left
  · rw [tcF_ne _ hq]

theorem tcF_local : IsLocal (tcF (V := V)) := fun _ _ _ hj => tcF_ne _ hj

/-- The common fixed points of the `tcF` are exactly the transitive relations. -/
theorem isCommonFixed_tcF_iff (R : V × V → Bool) :
    IsCommonFixed tcF R ↔ ∀ a k b, R (a, k) = true → R (k, b) = true → R (a, b) = true := by
  constructor
  · intro h a k b h1 h2
    have := congrFun (h (a, b)) (a, b)
    rw [tcF_self] at this
    rw [← this]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inr ⟨k, h1, h2⟩
  · intro h p
    funext q
    by_cases hq : q = p
    · subst hq
      rw [tcF_self]
      cases hR : R q
      · simp only [Bool.false_or, decide_eq_false_iff_not]
        rintro ⟨k, h1, h2⟩
        have := h q.1 k q.2 h1 h2
        simp_all
      · rfl
    · rw [tcF_ne _ hq]

/-- Section 2.1: the least common fixed point of the `tcF` above `R₀` is the reflexive–transitive
closure of `E`. -/
theorem isLeast_rtc (E : V → V → Prop) [DecidableRel E] :
    IsLeast {y | IsCommonFixed tcF y ∧ tcInit E ≤ y} (rtc E) := by
  classical
  refine ⟨⟨(isCommonFixed_tcF_iff _).2 ?_, ?_⟩, ?_⟩
  · intro a k b h1 h2
    simp only [rtc, decide_eq_true_eq] at *
    exact h1.trans h2
  · intro p
    simp only [tcInit, rtc]
    rw [Bool.le_iff_imp]
    simp only [decide_eq_true_eq]
    rintro (h | h)
    · exact Relation.ReflTransGen.single h
    · rw [h]
  · rintro y ⟨hy, h0⟩ ⟨a, b⟩
    have htr := (isCommonFixed_tcF_iff y).1 hy
    simp only [rtc]
    rw [Bool.le_iff_imp]
    intro h
    simp only [decide_eq_true_eq] at h
    induction h with
    | refl =>
      have := h0 (a, a)
      simp only [tcInit, or_true, decide_true] at this
      exact le_antisymm le_top this
    | @tail c d _ he ih =>
      refine htr _ _ _ ih ?_
      have := h0 (c, d)
      simp only [tcInit] at this
      exact le_antisymm le_top (le_trans (by simp [he]) this)

/-- Section 2.1: a fair interleaved execution of the `tcF` from `R₀` terminates at the
reflexive–transitive closure of `E`. -/
theorem tc_interleaving (E : V → V → Prop) [DecidableRel E] {σ : ℕ → V × V} (hσ : FairSeq σ)
    {G : ℕ → V × V → Bool} (h0 : G 0 = tcInit E) (hG : IsInterleavedExec tcF σ G) :
    TerminatesAt G (rtc E) := by
  obtain ⟨x, hx, hl⟩ := converges_from tcF_monotone tcF_inflationary hσ hG
  rw [h0] at hl
  rwa [hl.unique (isLeast_rtc E)] at hx

/-- Section 3.1 (Algorithm 1): a fair parallel execution with update-only-on-change from `R₀`
terminates at the reflexive–transitive closure of `E`. -/
theorem tc_parallel (E : V → V → Prop) [DecidableRel E] {S : ℕ → Set (V × V)} (hS : FairSets S)
    {G : ℕ → V × V → Bool} (h0 : G 0 = tcInit E)
    (hG : ∀ t, ParRound uooc tcF (G t) (S t) (G (t + 1))) : TerminatesAt G (rtc E) := by
  obtain ⟨x, hx, hl⟩ := parallel_converges_from tcF_monotone tcF_inflationary hS hG
  rw [h0] at hl
  rwa [hl.unique (isLeast_rtc E)] at hx

/-- Section 4.1 (Algorithm 3): a distributed execution with bounded staleness and a fair (e.g.
strongly fair) scheduler from `R₀` terminates at the reflexive–transitive closure of `E`. -/
theorem tc_distributed (E : V → V → Prop) [DecidableRel E] {S : ℕ → Set (V × V)}
    (hS : FairSets S) {T : ℕ} {W : ℕ → V × V → V × V → Bool} {G : ℕ → V × V → Bool}
    (h0 : G 0 = tcInit E) (hV : ∀ t, ∀ i ∈ S t, BoundedStale T G t i (W t i))
    (hG : IsDistExec tcF S W G) : TerminatesAt G (rtc E) := by
  obtain ⟨x, hx, hl⟩ := distributed_converges_from tcF_monotone tcF_inflationary tcF_local hS hV hG
  rw [h0] at hl
  rwa [hl.unique (isLeast_rtc E)] at hx

/-! ## The `O(log n)` round bound of Section 3.1 -/

/-- `ReachLe E n a b`: there is an `E`-walk from `a` to `b` with at most `n` edges. -/
def ReachLe (E : V → V → Prop) : ℕ → V → V → Prop
  | 0, a, b => a = b
  | n + 1, a, b => ReachLe E n a b ∨ ∃ k, ReachLe E n a k ∧ E k b

omit [Fintype V] [DecidableEq V] in
theorem ReachLe.mono {E : V → V → Prop} {m n : ℕ} (h : m ≤ n) {a b : V} (hr : ReachLe E m a b) :
    ReachLe E n a b := by
  induction h with
  | refl => exact hr
  | step _ ih => exact Or.inl ih

omit [Fintype V] [DecidableEq V] in
/-- A walk of length `≤ m + n` splits into walks of lengths `≤ m` and `≤ n`. -/
theorem ReachLe.split {E : V → V → Prop} (m : ℕ) : ∀ n {a b : V}, ReachLe E (m + n) a b →
    ∃ k, ReachLe E m a k ∧ ReachLe E n k b
  | 0, a, b, h => ⟨b, h, rfl⟩
  | n + 1, a, b, h => by
    rcases h with h | ⟨c, hc, he⟩
    · obtain ⟨k, h1, h2⟩ := ReachLe.split m n h
      exact ⟨k, h1, Or.inl h2⟩
    · obtain ⟨k, h1, h2⟩ := ReachLe.split m n hc
      exact ⟨k, h1, Or.inr ⟨c, h2, he⟩⟩

omit [Fintype V] [DecidableEq V] in
theorem ReachLe.rtc {E : V → V → Prop} : ∀ {n : ℕ} {a b : V}, ReachLe E n a b →
    Relation.ReflTransGen E a b
  | 0, a, b, h => h ▸ Relation.ReflTransGen.refl
  | n + 1, a, b, h => by
    rcases h with h | ⟨c, hc, he⟩
    · exact ReachLe.rtc h
    · exact (ReachLe.rtc hc).tail he

omit [Fintype V] [DecidableEq V] in
theorem exists_reachLe_of_rtc {E : V → V → Prop} {a b : V} (h : Relation.ReflTransGen E a b) :
    ∃ n, ReachLe E n a b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ he ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, Or.inr ⟨_, hn, he⟩⟩

omit [DecidableEq V] in
/-- Every pair in the reflexive–transitive closure is joined by a walk with at most `|V| - 1`
edges. -/
theorem reachLe_card_of_rtc {E : V → V → Prop} {a b : V} (h : Relation.ReflTransGen E a b) :
    ReachLe E (Fintype.card V - 1) a b := by
  classical
  let F : ℕ → Finset V := fun n => Finset.univ.filter (ReachLe E n a)
  have hFmono : ∀ n, F n ⊆ F (n + 1) := fun n x hx => by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact Or.inl hx
  -- once stable, stable forever
  have hstable : ∀ n, F (n + 1) = F n → ∀ m, F (n + m) = F n := by
    intro n hn m
    induction m with
    | zero => rfl
    | succ m ih =>
      apply Finset.Subset.antisymm _ (ih ▸ hFmono _)
      intro x hx
      simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [← add_assoc] at hx
      rcases hx with hx | ⟨c, hc, he⟩
      · rw [← ih]; simpa [F] using hx
      · have hc' : c ∈ F (n + 1) := by
          rw [hn, ← ih]; simpa [F] using hc
        simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hc'
        rcases hc' with hc' | ⟨d, hd, hd'⟩
        · rw [← hn]; simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
          exact Or.inr ⟨c, hc', he⟩
        · rw [← hn]; simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
          right; refine ⟨c, ?_, he⟩
          have : c ∈ F (n + 1) := by
            simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
            exact Or.inr ⟨d, hd, hd'⟩
          rw [hn] at this
          simpa [F] using this
  -- growth until stabilization
  have hgrow : ∀ n, (∃ m, m < n ∧ F (m + 1) = F m) ∨ n + 1 ≤ (F n).card := by
    intro n
    induction n with
    | zero =>
      right
      have : a ∈ F 0 := Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
      exact Finset.card_pos.2 ⟨a, this⟩
    | succ n ih =>
      rcases ih with ⟨m, hm, hm'⟩ | ih
      · exact Or.inl ⟨m, by omega, hm'⟩
      · by_cases hs : F (n + 1) = F n
        · exact Or.inl ⟨n, by omega, hs⟩
        · right
          have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hFmono n, Ne.symm hs⟩)
          omega
  obtain ⟨n, hn⟩ := exists_reachLe_of_rtc h
  rcases hgrow (Fintype.card V) with ⟨m, hm, hm'⟩ | hc
  · have hmem : b ∈ F m := by
      rcases le_total n m with hnm | hmn
      · simpa [F] using hn.mono hnm
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
        rw [← hstable m hm' d]; simpa [F] using hn
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.mono (by omega)
  · exact absurd (hc.trans (Finset.card_le_univ _)) (by omega)

/-- In an update-only-on-change round, if the process owning `p` is active and every vector it may
read yields `true` at `p`, then the committed value at `p` is `true`. -/
theorem commit_true {R R' : V × V → Bool} {S : Set (V × V)}
    (e : RoundExec uooc tcF R S R') {p : V × V} (hp : p ∈ S)
    (hf : ∀ X, R ≤ X → tcF p X p = true) : R' p = true := by
  have hinf := tcF_inflationary (V := V)
  have hle := e.le_commit hinf p
  by_contra hne
  have hR' : R' p = false := by simpa using hne
  have hR : R' p = R p := by
    rw [hR']
    cases h2 : R p
    · rfl
    · rw [h2, hR'] at hle; exact absurd hle (by simp)
  have hnw := (e.commit_eq_iff hinf p).1 hR
  have hX := hf (e.read p) (e.le_read hinf p hp)
  rcases e.read_spec p hp p with h | ⟨j, hj, -, hw, -⟩
  · -- `p` read the committed value: it writes `true` unless that value was already `true`
    by_cases hRp : R p = true
    · exact hne (hR ▸ hRp)
    · exact hnw p hp (by simp only [uooc, hX, h]; simpa using hRp)
  · exact hnw j hj hw

/-- **Section 3.1, round complexity.** If all `n²` threads run in every round (parallel
non-interleaving rounds with update-only-on-change, from `R₀`), then after `t` rounds every pair
joined by a walk of length `≤ 2^t` is set, and the state equals the reflexive–transitive closure
as soon as `|V| - 1 ≤ 2^t`. -/
theorem tc_parallel_rounds (E : V → V → Prop) [DecidableRel E] {G : ℕ → V × V → Bool}
    (h0 : G 0 = tcInit E) (hG : ∀ t, ParRound uooc tcF (G t) Set.univ (G (t + 1))) :
    (∀ t a b, ReachLe E (2 ^ t) a b → G t (a, b) = true) ∧
      (∀ t, Fintype.card V - 1 ≤ 2 ^ t → G t = rtc E) := by
  have hlow : ∀ t a b, ReachLe E (2 ^ t) a b → G t (a, b) = true := by
    intro t
    induction t with
    | zero =>
      intro a b h
      rw [h0]
      simp only [tcInit, decide_eq_true_eq]
      rcases h with h | ⟨k, rfl, he⟩
      · exact Or.inr h
      · exact Or.inl he
    | succ t ih =>
      intro a b h
      rw [pow_succ, mul_two] at h
      obtain ⟨k, h1, h2⟩ := ReachLe.split _ _ h
      have g1 := ih _ _ h1
      have g2 := ih _ _ h2
      refine commit_true (hG t).some (Set.mem_univ (a, b)) fun X hX => ?_
      rw [tcF_self]
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Or.inr ⟨k, le_antisymm le_top (g1 ▸ hX _), le_antisymm le_top (g2 ▸ hX _)⟩
  refine ⟨hlow, fun t ht => le_antisymm ?_ ?_⟩
  · -- upper bound: never above the closure (a common fixed point above `R₀`)
    have hY := (isLeast_rtc E).1
    have : ∀ t, G t ≤ rtc E := by
      intro t
      induction t with
      | zero => rw [h0]; exact hY.2
      | succ t ih => exact (hG t).some.commit_le tcF_monotone hY.1 ih
    exact this t
  · intro p
    classical
    simp only [rtc]
    rw [Bool.le_iff_imp]
    intro h
    simp only [decide_eq_true_eq] at h
    exact hlow t p.1 p.2 ((reachLe_card_of_rtc h).mono ht)

end Podc.OverwriteLeastFixedPoints.TC
