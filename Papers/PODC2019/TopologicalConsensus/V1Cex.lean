import Papers.PODC2019.TopologicalConsensus.CanonicalCex

/-!
# Counterexamples to the broadcast/component characterizations of the PODC'19 version (arXiv v1)

The PODC'19 paper (arXiv:1905.09590v1) claims, for synchronous fault-free dynamic networks under
an arbitrary message adversary (minimum topology = our `d_u`):

* Corollary 5.6: consensus is solvable iff no connected component of `Σ` contains a `v`-valent and
  a `w`-valent execution, `v ≠ w`;
* Theorem 5.11: consensus is solvable iff every connected component is broadcastable;
* Theorem 6.7 (non-compact adversaries): consensus is solvable iff every component of a valent
  execution is broadcastable.

The "if" directions are false. Counterexample (three processes `0, 1, 2`, binary inputs):
`MA = {π_k | k ∈ ℕ} ∪ {σ_∞}` with
* `σ_∞`: `1 → 0` and `1 → 2` in every round;
* `π_k`: no edges before round `k + 1`, `2 → 0` in round `k + 1`, then `0 → 1`, `0 → 2` forever.

Every execution `(x, π_k)` lies in the clopen set `S_{x₀,x₂,k}` (process 1 is never heard of; the
`(k+2)`-round views determine `k`, `x₀`, `x₂`), broadcast by `0`, containing only `x₀`-valent
valent executions. The component of `(x, σ_∞)` is `{(y, σ_∞) | y₁ = x₁}` (broadcast by `1`).
Yet consensus is impossible: `((1,0,1), π_k)` must decide like `((1,1,1), π_k)` (process 0 never
hears of process 1), i.e. `1`, while for large `k` process 1 cannot distinguish it from
`((0,0,0), σ_∞)` before deciding.

We also refute v1 Corollary 6.1 ("finitely many components" for compact adversaries) and
Corollary 6.5 (`ε`-approximations equal components for small `ε`) on the limit-closed adversary
`CanonicalCex.MAex`.
-/

namespace TopoConsensus

namespace V1Cex

open Set Cslib.HeardOf Topology DN

/-- `σ_∞`: `1 → 0`, `1 → 2` in every round. -/
def σI : ℕ → Graph (Fin 3) := fun _ q p => q = 1 ∧ (p = 0 ∨ p = 2)

/-- `π_k`: `2 → 0` in round `k + 1` (index `k`), then `0 → 1`, `0 → 2` forever. -/
def πk (k : ℕ) : ℕ → Graph (Fin 3) := fun t q p =>
  (t = k ∧ q = 2 ∧ p = 0) ∨ (k < t ∧ q = 0 ∧ (p = 1 ∨ p = 2))

/-- The message adversary `{π_k} ∪ {σ_∞}`. -/
def MA : Set (ℕ → Graph (Fin 3)) := insert σI (range πk)

theorem σI_mem : σI ∈ MA := mem_insert _ _
theorem πk_mem (k : ℕ) : πk k ∈ MA := Or.inr ⟨k, rfl⟩

abbrev Adm := (dnModel (V := Bool) MA).adm

theorem not_limitClosed : ¬ LimitClosed MA := by
  intro h
  have hmem := h (fun _ _ _ => False) fun t => ⟨πk t, πk_mem t, fun k hk => by
    funext q p; simp [πk]; omega⟩
  rcases hmem with h1 | ⟨k, hk⟩
  · have := congrFun (congrFun (congrFun h1 0) 1) 0
    simp [σI] at this
  · have := congrFun (congrFun (congrFun hk k) 2) 0
    simp [πk] at this

/-! ### Generic helpers -/

theorem FIIndist_of_deaf {P V : Type*} {x y : P → V} {σ τ : ℕ → Graph P} {p : P} (hx : x p = y p)
    {T : ℕ} (hσ : ∀ t < T, ∀ q, ¬ σ t q p) (hτ : ∀ t < T, ∀ q, ¬ τ t q p) :
    FIIndist x y σ τ T p := by
  induction T with
  | zero => exact hx
  | succ T ih =>
    exact (ih (fun t ht => hσ t (by omega)) (fun t ht => hτ t (by omega))).succ_of_deaf
      (hσ T (by omega)) (hτ T (by omega))

/-- In `π_k`, processes 0 and 2 never hear of process 1. -/
theorem not_heard_one (k t : ℕ) : ∀ q : Fin 3, (q = 0 ∨ q = 2) → ¬ Heard (πk k) t q 1 := by
  induction t with
  | zero => intro q hq h; simp only [Heard] at h; subst h; simp at hq
  | succ t ih =>
    intro q hq h
    rcases h with h | ⟨r, hr, hh⟩
    · exact ih q hq h
    · have : r = 0 ∨ r = 2 := by
        rcases hr with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp
      exact ih r this hh

/-! ### The executions with pattern `π_k` are isolated in groups -/

theorem iso0 {k : ℕ} {x y : Fin 3 → Bool} {τ : ℕ → Graph (Fin 3)} (hτ : τ ∈ MA)
    (h : FIIndist x y (πk k) τ (k + 1) 0) : τ = πk k ∧ y 0 = x 0 ∧ y 2 = x 2 := by
  obtain ⟨h0, hin, hs⟩ := h
  have e : πk k k 2 0 := Or.inl ⟨rfl, rfl, rfl⟩
  have hτk := (hin 2).1 e
  refine ⟨?_, h0.input.symm, (hs 2 e).input.symm⟩
  rcases hτ with rfl | ⟨m, rfl⟩
  · simp [σI] at hτk
  · rcases hτk with ⟨rfl, -, -⟩ | ⟨-, h2, -⟩
    · rfl
    · exact absurd h2 (by decide)

theorem isolated {k : ℕ} {x y : Fin 3 → Bool} {τ : ℕ → Graph (Fin 3)} (hτ : τ ∈ MA) {r : Fin 3}
    (h : FIIndist x y (πk k) τ (k + 2) r) : τ = πk k ∧ y 0 = x 0 ∧ y 2 = x 2 := by
  fin_cases r
  · exact iso0 hτ (h.mono (k + 1) (by omega))
  · obtain ⟨-, -, hs⟩ := h
    exact iso0 hτ (hs 0 (Or.inr ⟨by omega, rfl, Or.inl rfl⟩))
  · obtain ⟨-, -, hs⟩ := h
    exact iso0 hτ (hs 0 (Or.inr ⟨by omega, rfl, Or.inr rfl⟩))

/-- `S_{a,c,k}`: executions with pattern `π_k` and inputs `a` at 0 and `c` at 2. -/
def S (a c : Bool) (k : ℕ) : Set Adm :=
  {δ | patOf (δ : ℕ → Conf (Fin 3) Bool) = πk k ∧ inpOf (δ : ℕ → Conf (Fin 3) Bool) 0 = a ∧
    inpOf (δ : ℕ → Conf (Fin 3) Bool) 2 = c}

theorem mem_S_of {a c : Bool} {k : ℕ} {δ δ' : Adm} (hδ : δ ∈ S a c k) {r : Fin 3}
    (h : FIIndist (inpOf (δ : ℕ → Conf (Fin 3) Bool)) (inpOf (δ' : ℕ → Conf (Fin 3) Bool))
      (patOf (δ : ℕ → Conf (Fin 3) Bool)) (patOf (δ' : ℕ → Conf (Fin 3) Bool)) (k + 2) r) :
    δ' ∈ S a c k := by
  obtain ⟨hp, h0, h2⟩ := hδ
  rw [hp] at h
  obtain ⟨e1, e2, e3⟩ := isolated (eq_exec δ'.2).2 h
  exact ⟨e1, e2.trans h0, e3.trans h2⟩

theorem isClopen_S (a c : Bool) (k : ℕ) : IsClopen[(dnModel (V := Bool) MA).τU] (S a c k) := by
  refine ⟨?_, ?_⟩
  · rw [← @isOpen_compl_iff, Model.isOpen_τU_iff]
    intro δ hδ
    refine ⟨k + 2, fun δ' ⟨p, hp⟩ hδ' => hδ ?_⟩
    rw [(eq_exec δ.2).1, (eq_exec δ'.2).1] at hp
    exact mem_S_of hδ' (okP_upTo_iff.1 hp).symm
  · rw [Model.isOpen_τU_iff]
    intro δ hδ
    refine ⟨k + 2, fun δ' ⟨p, hp⟩ => ?_⟩
    rw [(eq_exec δ.2).1, (eq_exec δ'.2).1] at hp
    exact mem_S_of hδ (okP_upTo_iff.1 hp)

/-! ### The executions with pattern `σ_∞` -/

/-- `W_c`: the `σ_∞`-executions with `x₁ = c`, together with all `π`-executions. -/
def W (c : Bool) : Set Adm :=
  {δ | patOf (δ : ℕ → Conf (Fin 3) Bool) = σI → inpOf (δ : ℕ → Conf (Fin 3) Bool) 1 = c}

theorem isOpen_W (c : Bool) : IsOpen[(dnModel (V := Bool) MA).τU] (W c) := by
  rw [Model.isOpen_τU_iff]
  intro δ hδ
  by_cases hp : patOf (δ : ℕ → Conf (Fin 3) Bool) = σI
  · refine ⟨1, fun δ' ⟨r, hr⟩ hp' => ?_⟩
    rw [(eq_exec δ.2).1, (eq_exec δ'.2).1, hp, hp'] at hr
    have h1 := okP_upTo_iff.1 hr
    rw [← hδ hp]
    fin_cases r
    · exact (h1.2.2 1 ⟨rfl, Or.inl rfl⟩).input.symm
    · exact (h1.mono 0 (by omega)).input.symm
    · exact (h1.2.2 1 ⟨rfl, Or.inr rfl⟩).input.symm
  · obtain ⟨k, hk⟩ : ∃ k, patOf (δ : ℕ → Conf (Fin 3) Bool) = πk k := by
      rcases (eq_exec δ.2).2 with h | ⟨k, hk⟩
      · exact absurd h hp
      · exact ⟨k, hk.symm⟩
    refine ⟨k + 2, fun δ' ⟨r, hr⟩ hp' => ?_⟩
    rw [(eq_exec δ.2).1, (eq_exec δ'.2).1] at hr
    have := mem_S_of (a := inpOf (δ : ℕ → Conf (Fin 3) Bool) 0)
      (c := inpOf (δ : ℕ → Conf (Fin 3) Bool) 2) ⟨hk, rfl, rfl⟩ (okP_upTo_iff.1 hr)
    rw [this.1] at hp'
    have := congrFun (congrFun (congrFun hp' k) 2) 0
    simp [πk, σI] at this

/-! ### Components -/

theorem comp_subset_S {δ : Adm} {k : ℕ} (hk : patOf (δ : ℕ → Conf (Fin 3) Bool) = πk k) :
    comp δ ⊆ S (inpOf (δ : ℕ → Conf (Fin 3) Bool) 0) (inpOf (δ : ℕ → Conf (Fin 3) Bool) 2) k := by
  let _ := (dnModel (V := Bool) MA).τU
  exact (isClopen_S _ _ k).connectedComponent_subset ⟨hk, rfl, rfl⟩

theorem comp_subset_K {δ : Adm} (hσ : patOf (δ : ℕ → Conf (Fin 3) Bool) = σI) :
    ∀ ε ∈ comp δ, patOf (ε : ℕ → Conf (Fin 3) Bool) = σI ∧
      inpOf (ε : ℕ → Conf (Fin 3) Bool) 1 = inpOf (δ : ℕ → Conf (Fin 3) Bool) 1 := by
  let _ := (dnModel (V := Bool) MA).τU
  -- the component only contains `σ_∞`-executions
  have hpat : ∀ ε ∈ comp δ, patOf (ε : ℕ → Conf (Fin 3) Bool) = σI := by
    intro ε hε
    rcases (eq_exec ε.2).2 with h | ⟨k, hk⟩
    · exact h
    · exfalso
      have hc : comp δ = comp ε := connectedComponent_eq hε
      have : δ ∈ comp ε := hc ▸ mem_connectedComponent
      have hS := (comp_subset_S hk.symm) this
      rw [hS.1] at hσ
      have := congrFun (congrFun (congrFun hσ k) 2) 0
      simp [πk, σI] at this
  intro ε hε
  refine ⟨hpat ε hε, ?_⟩
  set c := inpOf (δ : ℕ → Conf (Fin 3) Bool) 1
  by_contra hne
  have hpre := (isPreconnected_connectedComponent (x := δ))
  have hcover : comp δ ⊆ W c ∪ W (!c) := by
    intro ζ _
    by_cases h : inpOf (ζ : ℕ → Conf (Fin 3) Bool) 1 = c
    · exact Or.inl fun _ => h
    · exact Or.inr fun _ => by cases hc : c <;> simp_all
  obtain ⟨ζ, hζ, hu, hv⟩ := hpre (W c) (W (!c)) (isOpen_W c) (isOpen_W (!c)) hcover
    ⟨δ, mem_connectedComponent, fun _ => rfl⟩
    ⟨ε, hε, fun _ => by cases hc : c <;> cases h : inpOf (ε : ℕ → Conf (Fin 3) Bool) 1 <;> simp_all⟩
  have h1 := hu (hpat ζ hζ)
  have h2 := hv (hpat ζ hζ)
  rw [h1] at h2
  cases c <;> simp at h2

/-! ### Main result -/

theorem broadcaster_zero (k : ℕ) : Broadcaster (πk k) 0 := by
  intro q
  fin_cases q
  · exact ⟨0, rfl⟩
  · exact ⟨k + 2, Or.inr ⟨0, Or.inr ⟨by omega, rfl, Or.inl rfl⟩, Heard.mono (t := 0) rfl _ (by omega)⟩⟩
  · exact ⟨k + 2, Or.inr ⟨0, Or.inr ⟨by omega, rfl, Or.inr rfl⟩, Heard.mono (t := 0) rfl _ (by omega)⟩⟩

theorem broadcaster_one_σI : Broadcaster σI 1 := by
  intro q
  fin_cases q
  · exact ⟨1, Or.inr ⟨1, ⟨rfl, Or.inl rfl⟩, rfl⟩⟩
  · exact ⟨0, rfl⟩
  · exact ⟨1, Or.inr ⟨1, ⟨rfl, Or.inr rfl⟩, rfl⟩⟩

/-- Every connected component is broadcastable by some process, and no connected component
contains valent executions of two different values. -/
theorem components_good (γ : Adm) :
    (∃ p, ∀ δ ∈ comp γ, Broadcaster (patOf (δ : ℕ → Conf (Fin 3) Bool)) p) ∧
    ∃ u, ∀ δ ∈ comp γ, ∀ v, (dnModel (V := Bool) MA).Valent (δ : ℕ → Conf (Fin 3) Bool) v →
      v = u := by
  rcases (eq_exec γ.2).2 with h | ⟨k, hk⟩
  · refine ⟨⟨1, fun δ hδ => ?_⟩, ⟨inpOf (γ : ℕ → Conf (Fin 3) Bool) 1, fun δ hδ v hv => ?_⟩⟩
    · rw [(comp_subset_K h δ hδ).1]; exact broadcaster_one_σI
    · rw [← (comp_subset_K h δ hδ).2]; exact (hv 1).symm
  · refine ⟨⟨0, fun δ hδ => ?_⟩, ⟨inpOf (γ : ℕ → Conf (Fin 3) Bool) 0, fun δ hδ v hv => ?_⟩⟩
    · rw [(comp_subset_S hk.symm hδ).1]; exact broadcaster_zero k
    · rw [← (comp_subset_S hk.symm hδ).2.1]; exact (hv 0).symm

/-- Consensus is impossible under `MA`. -/
theorem not_solvable : ¬ UniformSolvable (dnModel (V := Bool) MA) := by
  rw [dn_solvable_iff]
  rintro ⟨L, hV, hL⟩
  let x101 : Fin 3 → Bool := fun q => q ≠ 1
  -- `((1,0,1), π_k)` decides like `((1,1,1), π_k)`
  have h1 : ∀ k, L x101 (πk k) = true := by
    intro k
    obtain ⟨T, hT⟩ := hL (fun _ => true) (πk k) (πk_mem k)
    rw [hT x101 (πk k) (πk_mem k) ⟨0, FIIndist_of_not_heard (p := 1)
      (fun r hr => by simp [x101, hr]) (not_heard_one k T 0 (Or.inl rfl))⟩]
    exact hV true _ _ (πk_mem k) fun _ => rfl
  obtain ⟨T, hT⟩ := hL (fun _ => false) σI σI_mem
  have := hT x101 (πk T) (πk_mem T) ⟨1, FIIndist_of_deaf (by simp [x101])
    (fun t _ q h => by simp [σI] at h) (fun t ht q h => by simp [πk] at h; omega)⟩
  rw [h1 T, hV false _ _ σI_mem (fun _ => rfl)] at this
  exact Bool.noConfusion this

/-- **v1 Corollary 5.6, Theorem 5.11 and Theorem 6.7 ("if" directions) are false**: for the
non-limit-closed message adversary `MA`, every connected component of `Σ` (minimum topology) is
broadcastable and contains valent executions of at most one value, but consensus is impossible. -/
theorem v1_theorem_5_11_false :
    ¬ LimitClosed MA ∧
    (∀ γ : Adm, ∃ p, ∀ δ ∈ comp γ, Broadcaster (patOf (δ : ℕ → Conf (Fin 3) Bool)) p) ∧
    (∀ γ : Adm, ∀ δ ∈ comp γ, ∀ δ' ∈ comp γ, ∀ v w,
      (dnModel (V := Bool) MA).Valent (δ : ℕ → Conf (Fin 3) Bool) v →
      (dnModel (V := Bool) MA).Valent (δ' : ℕ → Conf (Fin 3) Bool) w → v = w) ∧
    ¬ UniformSolvable (dnModel (V := Bool) MA) := by
  refine ⟨not_limitClosed, fun γ => (components_good γ).1, fun γ δ hδ δ' hδ' v w hv hw => ?_,
    not_solvable⟩
  obtain ⟨u, hu⟩ := (components_good γ).2
  rw [hu δ hδ v hv, hu δ' hδ' w hw]

end V1Cex

/-! ### v1 Corollaries 6.1 and 6.5 on the limit-closed adversary `CanonicalCex.MAex` -/

namespace CanonicalCex

open Set DN

/-- **v1 Corollary 6.1 is false**: for the limit-closed adversary `MAex`, where consensus is
solvable, the connected components `{(x, σ_n)}` are pairwise distinct for different `n`
(infinitely many components). -/
theorem v1_corollary_6_1_false :
    LimitClosed MAex ∧ UniformSolvable (dnModel (V := Bool) MAex) ∧
      ∀ x : Fin 2 → Bool, Function.Injective fun n => comp (γn x n) := by
  refine ⟨limitClosed, solvable, fun x n m h => ?_⟩
  simp only [comp_γn, singleton_eq_singleton_iff] at h
  have := congrArg (fun γ : (dnModel (V := Bool) MAex).adm => patOf (γ : ℕ → Conf (Fin 2) Bool) n) h
  simp only [γn, patOf_exec, σn, ite_true] at this
  by_contra hnm
  simp only [hnm, ite_false] at this
  exact both_ne_toL this

/-- **v1 Corollary 6.5 is false**: for every `ε > 0` there is an execution whose
`ε`-approximation is strictly larger than its connected component. -/
theorem v1_corollary_6_5_false (ε : ℝ) (hε : 0 < ε) :
    ∃ z, ¬ approx (MA := MAex) ε z ⊆ comp z := by
  let _ := (dnModel (V := Bool) MAex).τU
  let y : Fin 2 → Bool := fun _ => true
  let x : Fin 2 → Bool := fun q => if q = 0 then false else true
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨γinf y, fun hsub => ?_⟩
  have hmem : γn x T ∈ approx (MA := MAex) ε (γinf y) := by
    refine Relation.ReflTransGen.single ?_
    refine lt_trans ((Model.dU_lt_pow_iff _ _ _ T).2 ⟨1, ?_⟩) hT
    simp only [γinf, γn]
    exact okP_upTo_iff.2 (indist_γinf_γn (x := x) (y := y) (by simp [x, y]) T T le_rfl)
  have hc := hsub hmem
  have : comp (γinf y) = comp (γn x T) := connectedComponent_eq hc
  have hy : γinf y ∈ comp (γn x T) := this ▸ mem_connectedComponent
  rw [comp_γn, mem_singleton_iff] at hy
  have := congrArg (fun γ : (dnModel (V := Bool) MAex).adm => patOf (γ : ℕ → Conf (Fin 2) Bool) T) hy
  simp only [γinf, γn, patOf_exec, σinf, σn, ite_true] at this
  exact both_ne_toL this.symm

end CanonicalCex

end TopoConsensus
