import Papers.PODC2018.FairLeaderElection.TreeModel

/-!
# General facts about fair leader election on graphs (towards Theorem 7.2 of [YM18])

* `goutcome_eq_some_iff`: the outcome is `some o` iff every processor terminates with `some o`.
* `exists_outcome_of_isFLE`: an FLE protocol never fails (finite inputs, uniform distribution).
* `not_resilient_of_assures` (**the bias lemma**, replacing the parity argument of the proof of
  Theorem 7.2, which only covers even `n`): if, for some fair schedule, a coalition of size `≤ k`
  has a deviation forcing the leader into a proper subset `S ⊊ V`, then the protocol is not
  `ε`-`k`-resilient for any `ε < 1/n`: with the utility `1_S` every member gains
  `1 - |S|/n ≥ 1/n`.
* `isResilient_one_sub` (**upper bound**): every FLE protocol is `(1 - 1/n)`-`k`-resilient for every
  `k ≥ 1`, because `E_D[u] ≤ max u` and `E_P[u] = (1/n) Σ_j u(j) ≥ max u / n`.
* `not_isFLE_of_edgeless`: without edges there is no FLE protocol (`n ≥ 2`).
-/

namespace Podc.FairLeaderElection.Trees

variable {V M : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A terminated processor's history no longer changes. -/
theorem grun_frozen (P : V → GProc V M) (σ : ℕ → V × V) {t : ℕ} {v : V}
    (h : (P v).out (grun G P σ t v) ≠ none) : ∀ t', t ≤ t' → grun G P σ t' v = grun G P σ t v := by
  intro t' ht'
  induction t', ht' using Nat.le_induction with
  | base => rfl
  | succ t' _ ih =>
    simp only [grun, gdeliver]
    split_ifs with hd
    · rw [Function.update_apply]
      split_ifs with he
      · subst he; exact absurd hd.2 (by rw [ih]; exact h)
      · exact ih
    · exact ih

theorem out_unique (P : V → GProc V M) (σ : ℕ → V × V) {v : V} {t t' : ℕ} {o o' : Option V}
    (h : (P v).out (grun G P σ t v) = some o) (h' : (P v).out (grun G P σ t' v) = some o') :
    o = o' := by
  rcases le_total t t' with hle | hle
  · rw [grun_frozen G P σ (by simp [h]) t' hle, h] at h'; exact Option.some_injective _ h'
  · rw [grun_frozen G P σ (by simp [h']) t hle, h'] at h; exact (Option.some_injective _ h).symm

theorem goutcome_eq_some_iff (P : V → GProc V M) (σ : ℕ → V × V) [Nonempty V] {o : V} :
    goutcome G P σ = some o ↔ ∀ v, ∃ t, (P v).out (grun G P σ t v) = some (some o) := by
  unfold goutcome
  split_ifs with h
  · constructor
    · rintro hv; cases hv; exact h.choose_spec
    · intro hv
      obtain ⟨v⟩ := ‹Nonempty V›
      obtain ⟨t, ht⟩ := h.choose_spec v
      obtain ⟨t', ht'⟩ := hv v
      have := out_unique G P σ ht ht'
      rw [Option.some_injective _ this]
  · simp only [false_iff]
    intro hv; exact h ⟨o, hv⟩

variable [Fintype V] {I : V → Type*} [∀ v, Fintype (I v)]

theorem sum_prob (P : Protocol V M I) (σ : ℕ → V × V) [∀ v, Nonempty (I v)] :
    ∑ o : Option V, prob G P σ o = 1 := by
  classical
  unfold prob
  rw [← Finset.sum_div, div_eq_one_iff_eq (by positivity)]
  norm_cast
  rw [← Finset.card_biUnion]
  · congr 1
    ext ω; simp
  · intro a _ b _ hab
    simp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro x _ h1 h2; exact hab (h1.symm.trans h2)

/-- **Honest executions of an FLE protocol always elect a leader.** -/
theorem exists_outcome_of_isFLE [Nonempty V] {P : Protocol V M I} (hP : IsFLE G P)
    [∀ v, Nonempty (I v)]
    {σ : ℕ → V × V} (hσ : GFair G σ) (ω : ∀ v, I v) : ∃ o, goutcome G (P.profile ω) σ = some o := by
  classical
  have hn : (Fintype.card V : ℝ) ≠ 0 := by
    have := Fintype.card_pos (α := V); positivity
  have h := sum_prob G P σ
  rw [Fintype.sum_option] at h
  simp only [hP σ hσ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have h0 : prob G P σ none = 0 := by field_simp at h; linarith
  unfold prob at h0
  rw [div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · norm_cast at h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
    have := h0 (Finset.mem_univ ω)
    cases hO : goutcome G (P.profile ω) σ with
    | none => exact absurd hO this
    | some o => exact ⟨o, rfl⟩
  · exfalso; norm_cast at h0; exact Fintype.card_ne_zero h0

theorem expU_eq_sum (P : Protocol V M I) (σ : ℕ → V × V) {u : Option V → ℝ} (hu : u none = 0) :
    expU G P σ u = ∑ j : V, prob G P σ (some j) * u (some j) := by
  classical
  unfold expU prob
  rw [← Finset.sum_fiberwise Finset.univ (fun ω => goutcome G (P.profile ω) σ)
    (fun ω => u (goutcome G (P.profile ω) σ)), Fintype.sum_option]
  have h0 : ∑ ω ∈ Finset.univ with goutcome G (P.profile ω) σ = none,
      u (goutcome G (P.profile ω) σ) = 0 :=
    Finset.sum_eq_zero fun ω hω => by rw [(Finset.mem_filter.mp hω).2, hu]
  rw [h0, zero_add, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => u (some j)) fun ω hω => by
    rw [(Finset.mem_filter.mp hω).2]]
  simp [Finset.sum_const, nsmul_eq_mul]
  ring

theorem expU_le (P : Protocol V M I) (σ : ℕ → V × V) [∀ v, Nonempty (I v)] {u : Option V → ℝ}
    {m : ℝ} (h : ∀ ω, u (goutcome G (P.profile ω) σ) ≤ m) : expU G P σ u ≤ m := by
  unfold expU
  rw [div_le_iff₀ (by positivity)]
  calc ∑ ω, u (goutcome G (P.profile ω) σ) ≤ ∑ _ω : (∀ v, I v), m := Finset.sum_le_sum fun ω _ => h ω
    _ = m * Fintype.card (∀ v, I v) := by simp [mul_comm]

theorem expU_eq_const (P : Protocol V M I) (σ : ℕ → V × V) [∀ v, Nonempty (I v)]
    {u : Option V → ℝ} {m : ℝ} (h : ∀ ω, u (goutcome G (P.profile ω) σ) = m) :
    expU G P σ u = m := by
  unfold expU
  rw [div_eq_iff (by positivity)]
  simp [h, mul_comm]

/-- **The bias lemma.** If for some fair schedule a coalition of at most `k` processors can force
the leader into a proper subset `S` of `V`, then an FLE protocol is not `ε`-`k`-resilient for any
`ε < 1/n`. (The proof of Theorem 7.2 in the paper only treats even `n`, via the parity bit.) -/
theorem not_resilient_of_assures {P : Protocol V M I} (hP : IsFLE G P) [∀ v, Nonempty (I v)]
    {σ : ℕ → V × V} (hσ : GFair G σ) {C : Finset V} {k : ℕ} (hC : C.card ≤ k)
    (hk : k ≤ Fintype.card V) (A : (v : V) → I v → GProc V M) {S : Finset V}
    (hS : S ≠ Finset.univ)
    (hA : ∀ ω, ∃ o ∈ S, goutcome G ((P.deviate C A).profile ω) σ = some o)
    {ε : ℝ} (hε : ε < 1 / Fintype.card V) : ¬ IsResilient G P ε k := by
  classical
  intro hR
  obtain ⟨C', hCC', -, hC'⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ C) hC
    (by simpa using hk)
  let A' : (v : V) → I v → GProc V M := fun v i => if v ∈ C then A v i else P.proc v i
  have hdev : ∀ ω, (P.deviate C' A').profile ω = (P.deviate C A).profile ω := by
    intro ω; funext v
    simp only [Protocol.profile, Protocol.deviate, A']
    by_cases hv : v ∈ C
    · simp [hv, hCC' hv]
    · simp [hv]
  let u : Option V → ℝ := fun o => match o with
    | none => 0
    | some j => if j ∈ S then 1 else 0
  have hu : IsRational u := ⟨rfl, fun o => by
    cases o with
    | none => simp [u]
    | some j => by_cases hj : j ∈ S <;> simp [u, hj]⟩
  obtain ⟨p, -, hp⟩ := hR σ hσ (fun _ => u) (fun _ => hu) C' hC' A'
  have hD : expU G (P.deviate C' A') σ u = 1 := by
    apply expU_eq_const
    intro ω
    obtain ⟨o, hoS, ho⟩ := hA ω
    rw [hdev, ho]; simp [u, hoS]
  have hPu : expU G P σ u = S.card / Fintype.card V := by
    rw [expU_eq_sum G P σ rfl]
    simp only [hP σ hσ, u, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [hD, hPu] at hp
  have hlt : S.card < Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hS⟩)
  have hn : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  have : (S.card : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast hlt
  have : 1 ≤ S.card / (Fintype.card V : ℝ) + ε := hp
  rw [lt_div_iff₀ hn] at hε
  rw [div_add' _ _ _ hn.ne', le_div_iff₀ hn] at this
  linarith

/-- **Upper bound.** Every FLE protocol is `(1 - 1/n)`-`k`-resilient for every `k ≥ 1`. In
particular Theorem 7.2 fails at `ε = 1/n` for `n = 2`. -/
theorem isResilient_one_sub {P : Protocol V M I} (hP : IsFLE G P) [∀ v, Nonempty (I v)]
    [Nonempty V] {k : ℕ} (hk : 1 ≤ k) :
    IsResilient G P (1 - 1 / Fintype.card V) k := by
  classical
  intro σ hσ u hu C hC A
  obtain ⟨p, hp⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨p, hp, ?_⟩
  have hn : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast Fintype.card_pos
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j : V => u p (some j))
    Finset.univ_nonempty
  have hm0 : 0 ≤ u p (some j0) := ((hu p).2 _).1
  have hQ : expU G (P.deviate C A) σ (u p) ≤ u p (some j0) := by
    apply expU_le
    intro ω
    cases goutcome G ((P.deviate C A).profile ω) σ with
    | none => rw [(hu p).1]; exact hm0
    | some j => exact hj0 j (Finset.mem_univ _)
  have hP' : u p (some j0) / Fintype.card V ≤ expU G P σ (u p) := by
    rw [expU_eq_sum G P σ (hu p).1]
    simp only [hP σ hσ]
    calc u p (some j0) / Fintype.card V = 1 / Fintype.card V * u p (some j0) := by ring
      _ ≤ ∑ j : V, 1 / (Fintype.card V : ℝ) * u p (some j) :=
          Finset.single_le_sum (f := fun j : V => 1 / (Fintype.card V : ℝ) * u p (some j))
            (fun j _ => mul_nonneg (by positivity) ((hu p).2 _).1) (Finset.mem_univ j0)
  have h1 := ((hu p).2 (some j0)).2
  have : u p (some j0) - u p (some j0) / Fintype.card V ≤ 1 - 1 / Fintype.card V := by
    have e : u p (some j0) - u p (some j0) / Fintype.card V =
        u p (some j0) * (1 - 1 / Fintype.card V) := by ring
    rw [e]
    have : 0 ≤ 1 - 1 / (Fintype.card V : ℝ) := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hn
    nlinarith
  linarith

end Podc.FairLeaderElection.Trees
