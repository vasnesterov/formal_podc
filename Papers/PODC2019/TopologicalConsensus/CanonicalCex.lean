import Papers.PODC2019.TopologicalConsensus.Broadcast
import Papers.PODC2019.TopologicalConsensus.LossyLink

/-!
# Canonical strong broadcaster decision sets need not be closed (Theorem 7.9, Corollaries 8.2,
# 8.3, Lemma 8.6, Corollary 8.7)

Definition 7.8 assigns every connected component `Σ_γ` of `Σ` its *canonical* broadcaster
`b(Σ_γ)`: the smallest process that is a broadcaster in every execution of the component. The
strong broadcaster decision sets are `Σ^p_v = ⋃ {Σ_γ | b(Σ_γ) = p, I_p(γ) = v}`. Theorem 7.9 and
Corollary 8.2 claim that consensus is solvable iff (i) every component is broadcastable and
(ii) the sets `Σ^p_v` are clopen (closed); Corollary 8.3 claims that for limit-closed message
adversaries they are clopen and pairwise at positive distance, and Lemma 8.6 / Corollary 8.7
claim that their `ε`-approximations coincide with them for small `ε`.

Counterexample (two processes, a limit-closed message adversary):
`MAex = {σ_n | n ∈ ℕ} ∪ {σ_∞}`, where `σ_∞ = (1 → 0)^ω` and `σ_n` is `σ_∞` with round `n + 1`
replaced by `0 ↔ 1`.
* Consensus is solvable: everybody knows the input of process `1` after round 1 (`solvable`).
* Every execution `(x, σ_n)` is isolated, so `{(x, σ_n)}` is a connected component; both processes
  broadcast in `σ_n`, so its canonical broadcaster is `0`.
* In `(y, σ_∞)` process `0` is not a broadcaster, so the canonical broadcaster of its component
  is `1`.
* `(y, σ_∞)` is the limit of `(x, σ_n)` with `x = (0, y₁)` (process 1 hears nothing up to round
  `n`), so `(y, σ_∞) ∈ closure Σ^0_0 \ Σ^0_0`: `Σ^0_0` is not closed (`theorem_7_9_canonical_false`).
* For every `ε > 0`, `(y, σ_∞)` lies in both `ε`-approximations `Σ^{0,ε}_0` and `Σ^{1,ε}_{y₁}`
  (`corollary_8_7_false`).

With an existentially chosen broadcaster (here: always `1`) the decision sets are clopen
(`Broadcast.dn_theorem_7_9_exists`), so only the canonical choice is at fault.
-/

namespace TopoConsensus

namespace DN

open Set Cslib.HeardOf Topology

set_option linter.unusedSectionVars false

variable {n : ℕ} [NeZero n] {MA : Set (ℕ → Graph (Fin n))}

/-! ### Definitions 7.8 and 8.4 (dynamic networks) -/

/-- The connected component of `γ` in the uniform topology. -/
def comp (γ : (dnModel (V := Bool) MA).adm) : Set (dnModel (V := Bool) MA).adm :=
  @connectedComponent _ (dnModel (V := Bool) MA).τU γ

/-- `p` is a broadcaster in every execution of `K`. -/
def CommonBroadcaster (K : Set (dnModel (V := Bool) MA).adm) (p : Fin n) : Prop :=
  ∀ δ ∈ K, Broadcaster (patOf (δ : ℕ → Conf (Fin n) Bool)) p

/-- `p` is the canonical (smallest common) broadcaster of the component of `γ`. -/
def IsCanonical (γ : (dnModel (V := Bool) MA).adm) (p : Fin n) : Prop :=
  CommonBroadcaster (comp γ) p ∧ ∀ q < p, ¬ CommonBroadcaster (comp γ) q

/-- The canonical strong broadcaster decision set `Σ^p_v` (Definition 7.8). -/
def strongBroadcasterSet (p : Fin n) (v : Bool) : Set (dnModel (V := Bool) MA).adm :=
  {γ | IsCanonical γ p ∧ inpOf (γ : ℕ → Conf (Fin n) Bool) p = v}

/-- The `ε`-approximation `Σ^ε_γ` (Definition 8.4): executions reachable from `γ` by finitely
many steps of `d_u`-distance `< ε`. -/
def approx (ε : ℝ) (γ : (dnModel (V := Bool) MA).adm) : Set (dnModel (V := Bool) MA).adm :=
  {δ | Relation.ReflTransGen (fun α β : (dnModel (V := Bool) MA).adm =>
    (dnModel (V := Bool) MA).dU α β < ε) γ δ}

/-- The `ε`-approximation `Σ^{p,ε}_v` of the strong broadcaster decision set. -/
def approxSet (p : Fin n) (v : Bool) (ε : ℝ) : Set (dnModel (V := Bool) MA).adm :=
  ⋃ γ ∈ strongBroadcasterSet (MA := MA) p v, approx ε γ

end DN

/-- A message adversary is limit-closed if every pattern all of whose finite prefixes extend to
patterns of `MA` is in `MA` (compactness of `MA` in the product topology). -/
def LimitClosed {P : Type*} (MA : Set (ℕ → Cslib.HeardOf.Graph P)) : Prop :=
  ∀ σ, (∀ t, ∃ τ ∈ MA, ∀ k < t, τ k = σ k) → σ ∈ MA

namespace CanonicalCex

open Set Cslib.HeardOf Topology DN LossyLink

/-- `σ_∞ = (1 → 0)^ω`. -/
def σinf : ℕ → Graph (Fin 2) := fun _ => toL

/-- `σ_n`: `σ_∞` with round `n + 1` replaced by `0 ↔ 1`. -/
def σn (n : ℕ) : ℕ → Graph (Fin 2) := fun k => if k = n then both else toL

/-- The message adversary `{σ_n} ∪ {σ_∞}`. -/
def MAex : Set (ℕ → Graph (Fin 2)) := insert σinf (range σn)

theorem σinf_mem : σinf ∈ MAex := mem_insert _ _
theorem σn_mem (n : ℕ) : σn n ∈ MAex := Or.inr ⟨n, rfl⟩

theorem both_ne_toL : both ≠ toL := by
  intro h
  have := congrFun (congrFun h 0) 1
  simp [both, toL] at this

theorem limitClosed : LimitClosed MAex := by
  intro σ hσ
  by_cases hb : ∃ n, σ n = both
  · obtain ⟨n, hn⟩ := hb
    have key : ∀ k, σ k = σn n k := by
      intro k
      obtain ⟨τ, hτ, hτσ⟩ := hσ (max n k + 1)
      have hτn : τ n = both := (hτσ n (by omega)).trans hn
      rcases hτ with rfl | ⟨m, rfl⟩
      · exact absurd hτn.symm (by simpa [σinf] using both_ne_toL)
      · have hm : m = n := by
          by_contra hmn
          simp [σn, Ne.symm hmn] at hτn
          exact both_ne_toL hτn.symm
        subst hm
        exact (hτσ k (by omega)).symm
    exact (funext key : σ = σn n) ▸ σn_mem n
  · push Not at hb
    have : σ = σinf := by
      funext k
      obtain ⟨τ, hτ, hτσ⟩ := hσ (k + 1)
      have := hτσ k (Nat.lt_succ_self k)
      rcases hτ with rfl | ⟨m, rfl⟩
      · exact this.symm
      · simp only [σn] at this
        split_ifs at this
        · exact absurd this.symm (hb k)
        · exact this.symm
    exact this ▸ σinf_mem

theorem toL_or_both {σ : ℕ → Graph (Fin 2)} (hσ : σ ∈ MAex) (k : ℕ) :
    σ k = toL ∨ σ k = both := by
  rcases hσ with rfl | ⟨m, rfl⟩
  · exact Or.inl rfl
  · simp only [σn]; split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

theorem edge10 {σ : ℕ → Graph (Fin 2)} (hσ : σ ∈ MAex) (k : ℕ) : σ k 1 0 := by
  rcases toL_or_both hσ k with h | h <;> rw [h] <;> simp [toL, both]

/-! ### Consensus is solvable -/

theorem solvable : UniformSolvable (dnModel (V := Bool) MAex) := by
  refine dn_solvable_iff.2 ⟨fun x _ => x 1, fun v x σ _ hx => hx 1, ?_⟩
  intro x σ hσ
  refine ⟨1, fun y τ _ ⟨r, hr⟩ => ?_⟩
  obtain ⟨h0, -, hs⟩ := hr
  fin_cases r
  · exact (show x 1 = y 1 from hs 1 (edge10 hσ 0)).symm
  · exact (show x 1 = y 1 from h0).symm

/-! ### Broadcasters -/

theorem broadcaster_one {σ : ℕ → Graph (Fin 2)} (hσ : σ ∈ MAex) : Broadcaster σ 1 := by
  intro q
  fin_cases q
  · exact ⟨1, heard_succ_iff.2 (Or.inr ⟨1, edge10 hσ 0, heard_zero_iff.2 rfl⟩)⟩
  · exact ⟨0, heard_zero_iff.2 rfl⟩

theorem broadcaster_zero_σn (n : ℕ) : Broadcaster (σn n) 0 := by
  intro q
  fin_cases q
  · exact ⟨0, heard_zero_iff.2 rfl⟩
  · refine ⟨n + 1, heard_succ_iff.2 (Or.inr ⟨0, by simp [σn, both],
      Heard.mono (t := 0) (heard_zero_iff.2 rfl) n (Nat.zero_le n)⟩)⟩

theorem not_heard_σinf : ∀ t, ¬ Heard σinf t 1 0
  | 0 => fun h => absurd (heard_zero_iff.1 h) (by decide)
  | t + 1 => fun h => by
    rcases heard_succ_iff.1 h with h | ⟨r, hr, -⟩
    · exact not_heard_σinf t h
    · exact toL_deaf r hr

theorem not_broadcaster_zero_σinf : ¬ Broadcaster σinf 0 := fun h => by
  obtain ⟨T, hT⟩ := h 1
  exact not_heard_σinf T hT

/-! ### Isolation of the executions `(x, σ_n)` -/

theorem isolated {n : ℕ} {x y : Fin 2 → Bool} {τ : ℕ → Graph (Fin 2)} (hτ : τ ∈ MAex) {r : Fin 2}
    (h : FIIndist x y (σn n) τ (n + 2) r) : y = x ∧ τ = σn n := by
  have h1 : FIIndist x y (σn n) τ (n + 1) 1 := by
    fin_cases r
    · obtain ⟨-, -, hs⟩ := h
      exact hs 1 (by simp [σn, toL])
    · exact h.1
  obtain ⟨hn1, hin, hs⟩ := h1
  have hτn : τ n 0 1 := (hin 0).1 (by simp [σn, both])
  have hτeq : τ = σn n := by
    rcases hτ with rfl | ⟨m, rfl⟩
    · simp [σinf, toL] at hτn
    · by_cases hm : n = m
      · rw [hm]
      · simp [σn, hm, toL] at hτn
  refine ⟨funext fun q => ?_, hτeq⟩
  fin_cases q
  · exact (DN.FIIndist.input (hs 0 (by simp [σn, both]))).symm
  · exact (DN.FIIndist.input hn1).symm

/-- The execution `(x, σ_n)` as an element of `Σ`. -/
def γn (x : Fin 2 → Bool) (n : ℕ) : (dnModel (V := Bool) MAex).adm :=
  ⟨exec x (σn n), exec_mem_adm x (σn_mem n)⟩

/-- The execution `(y, σ_∞)` as an element of `Σ`. -/
def γinf (y : Fin 2 → Bool) : (dnModel (V := Bool) MAex).adm :=
  ⟨exec y σinf, exec_mem_adm y σinf_mem⟩

theorem eq_γn_of {x : Fin 2 → Bool} {n : ℕ} (δ : (dnModel (V := Bool) MAex).adm) {r : Fin 2}
    (h : FIIndist x (inpOf (δ : ℕ → Conf (Fin 2) Bool)) (σn n) (patOf (δ : ℕ → Conf (Fin 2) Bool))
      (n + 2) r) : δ = γn x n := by
  obtain ⟨he, hm⟩ := eq_exec δ.2
  obtain ⟨hy, hτ⟩ := isolated hm h
  apply Subtype.ext
  rw [he, hy, hτ]
  rfl

theorem isClopen_singleton_γn (x : Fin 2 → Bool) (n : ℕ) :
    IsClopen[(dnModel (V := Bool) MAex).τU] {γn x n} := by
  refine ⟨?_, ?_⟩
  · rw [← @isOpen_compl_iff, Model.isOpen_τU_iff]
    intro δ hδ
    refine ⟨n + 2, fun δ' ⟨p, hp⟩ hδ' => ?_⟩
    rw [mem_singleton_iff] at hδ'
    subst hδ'
    obtain ⟨he, -⟩ := eq_exec δ.2
    rw [he] at hp
    exact hδ (mem_singleton_iff.2 (eq_γn_of δ (okP_upTo_iff.1 hp).symm))
  · rw [Model.isOpen_τU_iff]
    intro γ hγ
    rw [mem_singleton_iff] at hγ
    subst hγ
    refine ⟨n + 2, fun δ ⟨p, hp⟩ => ?_⟩
    obtain ⟨he, -⟩ := eq_exec δ.2
    rw [he] at hp
    exact mem_singleton_iff.2 (eq_γn_of δ (okP_upTo_iff.1 hp))

theorem comp_γn (x : Fin 2 → Bool) (n : ℕ) : comp (γn x n) = {γn x n} := by
  let _ := (dnModel (V := Bool) MAex).τU
  apply Subset.antisymm
  · exact (isClopen_singleton_γn x n).connectedComponent_subset (mem_singleton _)
  · exact singleton_subset_iff.2 mem_connectedComponent

theorem isCanonical_γn (x : Fin 2 → Bool) (n : ℕ) : IsCanonical (γn x n) 0 := by
  refine ⟨?_, fun q hq => absurd hq (Fin.not_lt_zero q)⟩
  rw [comp_γn]
  intro δ hδ
  rw [mem_singleton_iff] at hδ
  subst hδ
  simp only [γn, patOf_exec]
  exact broadcaster_zero_σn n

theorem isCanonical_γinf (y : Fin 2 → Bool) : IsCanonical (γinf y) 1 := by
  let _ := (dnModel (V := Bool) MAex).τU
  refine ⟨fun δ _ => broadcaster_one (eq_exec δ.2).2, fun q hq h => ?_⟩
  have hq0 : q = 0 := by
    fin_cases q
    · rfl
    · exact absurd hq (lt_irrefl _)
  subst hq0
  have := h (γinf y) mem_connectedComponent
  simp only [γinf, patOf_exec] at this
  exact not_broadcaster_zero_σinf this

theorem not_isCanonical_zero_γinf (y : Fin 2 → Bool) : ¬ IsCanonical (γinf y) 0 := fun h =>
  (isCanonical_γinf y).2 0 (by decide) h.1

/-- Process 1 cannot distinguish `(y, σ_∞)` from `(x, σ_T)` during the first `T` rounds if
`x₁ = y₁`. -/
theorem indist_γinf_γn {x y : Fin 2 → Bool} (hxy : y 1 = x 1) (T : ℕ) :
    ∀ t ≤ T, FIIndist y x σinf (σn T) t 1 := by
  intro t ht
  induction t with
  | zero => exact hxy
  | succ t ih =>
    refine (ih (by omega)).succ_of_deaf (fun q => toL_deaf q) (fun q => ?_)
    simp only [σn, show t ≠ T by omega, ite_false]
    exact toL_deaf q

/-! ### Main counterexamples -/

/-- **Theorem 7.9 / Corollaries 8.2 and 8.3 are false with canonical broadcasters**: for the
limit-closed message adversary `MAex`, consensus is solvable, but the canonical strong broadcaster
decision set `Σ^0_0` is not closed in the uniform topology. -/
theorem theorem_7_9_canonical_false :
    LimitClosed MAex ∧ UniformSolvable (dnModel (V := Bool) MAex) ∧
      ¬ IsClosed[(dnModel (V := Bool) MAex).τU] (strongBroadcasterSet (MA := MAex) 0 false) := by
  refine ⟨limitClosed, solvable, fun hcl => ?_⟩
  let _ := (dnModel (V := Bool) MAex).τU
  -- `(1, σ_∞)` is in the closure but not in the set
  let y : Fin 2 → Bool := fun _ => true
  have hnot : γinf y ∉ strongBroadcasterSet (MA := MAex) 0 false :=
    fun h => not_isCanonical_zero_γinf y h.1
  apply hnot
  rw [← hcl.closure_eq, mem_closure_iff]
  intro U hU hyU
  obtain ⟨T, hT⟩ := (Model.isOpen_τU_iff _ U).1 hU _ hyU
  let x : Fin 2 → Bool := fun q => if q = 0 then false else true
  refine ⟨γn x T, hT _ ⟨1, ?_⟩, isCanonical_γn x T, rfl⟩
  simp only [γinf, γn]
  exact okP_upTo_iff.2 (indist_γinf_γn (x := x) (y := y) (by simp [x, y]) T T le_rfl)

/-- **Lemma 8.6 and Corollary 8.7 are false**: for every `ε > 0` the `ε`-approximations of
`Σ^0_0` and `Σ^1_1` intersect, and the `ε`-approximation of `Σ^0_0` is strictly larger than
`Σ^0_0`. -/
theorem corollary_8_7_false (ε : ℝ) (hε : 0 < ε) :
    ∃ γ, γ ∈ approxSet (MA := MAex) 0 false ε ∧ γ ∈ approxSet (MA := MAex) 1 true ε ∧
      γ ∉ strongBroadcasterSet (MA := MAex) 0 false := by
  let y : Fin 2 → Bool := fun _ => true
  let x : Fin 2 → Bool := fun q => if q = 0 then false else true
  obtain ⟨T, hT⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2⁻¹ : ℝ) < 1)
  refine ⟨γinf y, ?_, ?_, fun h => not_isCanonical_zero_γinf y h.1⟩
  · refine mem_iUnion₂.2 ⟨γn x T, ⟨isCanonical_γn x T, rfl⟩, Relation.ReflTransGen.single ?_⟩
    refine lt_trans ((Model.dU_lt_pow_iff _ _ _ T).2 ⟨1, ?_⟩) hT
    simp only [γinf, γn]
    exact okP_upTo_iff.2 (indist_γinf_γn (x := x) (y := y) (by simp [x, y]) T T le_rfl).symm
  · exact mem_iUnion₂.2 ⟨γinf y, ⟨isCanonical_γinf y, rfl⟩, Relation.ReflTransGen.refl⟩

end CanonicalCex

end TopoConsensus
