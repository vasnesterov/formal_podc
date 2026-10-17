import Papers.PODC2019.TopologicalConsensus.Characterization
import Cslib.Computability.Distributed.DynamicNetworks.FullInfo

/-!
# Dynamic networks under general message adversaries (the PODC'19 setting, Sections 8.4/8.5)

`n` lock-step synchronous, fault-free processes run a full-information protocol; in round `t + 1`
the message adversary chooses the directed communication graph `σ t`
(`Cslib.HeardOf.Graph`: `σ t q p` means that `p` receives `q`'s message). A message adversary is
an arbitrary set `MA` of communication patterns `σ : ℕ → Graph P` (no compactness/limit-closure
assumed). Inputs are arbitrary: `Σ = {(x, σ) | x : P → V, σ ∈ MA}`.

* `FIIndist x y σ τ t p`: process `p` has the same full-information view after `t` rounds in
  the executions `(x, σ)` and `(y, τ)` (defined by recursion on `t`, no view type needed): the
  library notion `Cslib.HeardOf.FIIndist` with initial views given by the inputs.
* `dnModel MA`: the instance of the generic model; it is fault-free and satisfies
  `LockstepRecall`, so the characterization of Theorem 5.2/5.3 applies with the paper's `d_u`
  (`dn_theorem_5_2`, `dn_theorem_5_3`).
* `dn_solvable_iff`: the same characterization without topology: consensus is solvable under `MA`
  iff there is a labelling `L` of the executions that respects validity and is *locally constant*:
  for every admissible `(x, σ)` there is a round `T` such that every admissible `(y, τ)` in which
  some process has the same `T`-round view gets the same label.
-/

namespace TopoConsensus

open Set Filter Topology Cslib.HeardOf

namespace DN

variable {P V : Type*}

/-- `p` cannot distinguish `(x, σ)` from `(y, τ)` after `t` rounds (full-information view):
`p` has the same input in both, and for `t + 1` it has the same view after `t` rounds, the same
in-neighbours in round `t + 1`, and these have the same views after `t` rounds
(`FIIndist.zero_iff`, `FIIndist.succ_iff`). -/
abbrev FIIndist (x y : P → V) (σ τ : ℕ → Graph P) : ℕ → P → Prop :=
  Cslib.HeardOf.FIIndist (fun p => x p = y p) σ τ

variable {x y z : P → V} {σ τ ρ : ℕ → Graph P}

theorem FIIndist.zero_iff {p : P} : FIIndist x y σ τ 0 p ↔ x p = y p := Iff.rfl

theorem FIIndist.succ_iff {t : ℕ} {p : P} : FIIndist x y σ τ (t + 1) p ↔
    FIIndist x y σ τ t p ∧ (∀ q, σ t q p ↔ τ t q p) ∧ ∀ q, σ t q p → FIIndist x y σ τ t q :=
  Iff.rfl

theorem FIIndist.refl (x : P → V) (σ : ℕ → Graph P) (t : ℕ) (p : P) : FIIndist x x σ σ t p :=
  Cslib.HeardOf.FIIndist.refl (fun _ => rfl) t p

theorem FIIndist.symm {t : ℕ} {p : P} (h : FIIndist x y σ τ t p) : FIIndist y x τ σ t p :=
  Cslib.HeardOf.FIIndist.symm (fun _ => Eq.symm) h

theorem FIIndist.trans {t : ℕ} {p : P} (h₁ : FIIndist x y σ τ t p) (h₂ : FIIndist y z τ ρ t p) :
    FIIndist x z σ ρ t p :=
  Cslib.HeardOf.FIIndist.trans (fun _ => Eq.trans) h₁ h₂

theorem FIIndist.mono {t : ℕ} {p : P} (h : FIIndist x y σ τ t p) : ∀ u ≤ t, FIIndist x y σ τ u p :=
  fun _ hu => Cslib.HeardOf.FIIndist.mono h hu

theorem FIIndist.input {t : ℕ} {p : P} (h : FIIndist x y σ τ t p) : x p = y p :=
  Cslib.HeardOf.FIIndist.zero (I := fun p => x p = y p) h

/-- Executions that agree before round `t` are indistinguishable for everybody up to `t`. -/
theorem FIIndist_of_prefix {t : ℕ} (hστ : ∀ k < t, σ k = τ k) (p : P) : FIIndist x x σ τ t p :=
  (fiIndist_congr (fun _ _ => rfl) hστ p).1 (FIIndist.refl x σ t p)

/-- Configurations: the time, the inputs and the pattern truncated to the rounds played so far. -/
structure Conf (P V : Type*) where
  time : ℕ
  inp : P → V
  pat : ℕ → Graph P

/-- The pattern `σ` truncated to its first `t` rounds. -/
def trunc (σ : ℕ → Graph P) (t : ℕ) : ℕ → Graph P := fun k => if k < t then σ k else fun _ _ => False

/-- The execution with inputs `x` and communication pattern `σ`. -/
def exec (x : P → V) (σ : ℕ → Graph P) : ℕ → Conf P V := fun t => ⟨t, x, trunc σ t⟩

theorem FIIndist_trunc {t : ℕ} {p : P} :
    FIIndist x y (trunc σ t) (trunc τ t) t p ↔ FIIndist x y σ τ t p :=
  fiIndist_congr (fun k hk => by simp [trunc, hk]) (fun k hk => by simp [trunc, hk]) p

variable [Nonempty P]

/-- The dynamic-network model under the message adversary `MA`. -/
def dnModel (MA : Set (ℕ → Graph P)) : Model P (Conf P V) V where
  indist p c d := c.time = d.time ∧ FIIndist c.inp d.inp c.pat d.pat c.time p
  equiv p := ⟨fun c => ⟨rfl, FIIndist.refl _ _ _ _⟩,
    fun {c d} h => ⟨h.1.symm, by rw [← h.1]; exact h.2.symm⟩,
    fun {c d e} h₁ h₂ => ⟨h₁.1.trans h₂.1, h₁.2.trans (by rw [h₁.1]; exact h₂.2)⟩⟩
  Ob _ := univ
  clock _ c := c.time
  input c := c.inp
  adm := {γ | ∃ x, ∃ σ ∈ MA, γ = exec x σ}
  ob_anti := fun _ _ _ _ _ => le_rfl
  ob_init := fun _ _ => rfl
  ob_nonempty := fun _ _ => ⟨Classical.arbitrary P, mem_iInter.2 fun _ => trivial⟩
  clock_le := by
    rintro p γ ⟨x, σ, -, rfl⟩ c t h
    exact le_of_eq h.1
  clock_tendsto := by
    rintro γ ⟨x, σ, -, rfl⟩ p -
    exact tendsto_id
  input_local := by
    rintro p γ ⟨x, σ, -, rfl⟩ δ ⟨y, τ, -, rfl⟩ s t h
    exact h.2.input
  init_unique := by
    rintro γ ⟨x, σ, -, rfl⟩ δ ⟨y, τ, -, rfl⟩ h
    change x = y at h
    subst h
    simp only [exec, Conf.mk.injEq, true_and]
    funext k
    simp [trunc]

variable {MA : Set (ℕ → Graph P)}

theorem mem_adm {γ : ℕ → Conf P V} : γ ∈ (dnModel MA).adm ↔ ∃ x, ∃ σ ∈ MA, γ = exec x σ :=
  Iff.rfl

theorem exec_mem_adm (x : P → V) (hσ : σ ∈ MA) : exec x σ ∈ (dnModel (V := V) MA).adm :=
  ⟨x, σ, hσ, rfl⟩

theorem indist_exec {p : P} {s t : ℕ} :
    (dnModel (V := V) MA).indist p (exec x σ s) (exec y τ t) ↔ s = t ∧ FIIndist x y σ τ s p := by
  change s = t ∧ FIIndist x y (trunc σ s) (trunc τ t) s p ↔ _
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, FIIndist_trunc.1 h⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, FIIndist_trunc.2 h⟩

theorem lockstepRecall : (dnModel (V := V) MA).LockstepRecall := by
  rintro p γ ⟨x, σ, -, rfl⟩ δ ⟨y, τ, -, rfl⟩ s t h
  have h2 := indist_exec.1 h
  obtain ⟨rfl, h3⟩ := h2
  exact ⟨rfl, fun u hu => indist_exec.2 ⟨rfl, h3.mono u hu⟩⟩

theorem faultFree : (dnModel (V := V) MA).FaultFree := fun _ => rfl

variable [Fintype P]

/-- **Theorem 5.2 for message adversaries** (uniform consensus = consensus here, all processes are
correct): consensus is solvable under an arbitrary message adversary iff `Σ` can be partitioned into
`d_u`-clopen decision sets containing the `v`-valent executions. -/
theorem dn_theorem_5_2 :
    UniformSolvable (dnModel (V := V) MA) ↔
      ∃ lab : (dnModel (V := V) MA).adm → V,
        (∀ v, IsClopen[(dnModel (V := V) MA).τU] (lab ⁻¹' {v})) ∧
        ∀ γ : (dnModel (V := V) MA).adm, ∀ v, (dnModel MA).Valent γ v → lab γ = v :=
  Model.theorem_5_2_faultFree _ lockstepRecall faultFree

/-- Theorem 5.3 for message adversaries. -/
theorem dn_theorem_5_3 :
    NonUniformSolvable (dnModel (V := V) MA) ↔
      ∃ lab : (dnModel (V := V) MA).adm → V,
        (∀ v, IsClopen[(dnModel (V := V) MA).τNU] (lab ⁻¹' {v})) ∧
        ∀ γ : (dnModel (V := V) MA).adm, ∀ v, (dnModel MA).Valent γ v → lab γ = v :=
  Model.theorem_5_3 _ lockstepRecall

omit [Fintype P] in
/-- In the dynamic-network model, a `d_u`-ball of radius `2^{-T}` around `(x, σ)` consists of the
executions in which some process has the same view after `T` rounds. -/
theorem okP_upTo_iff {p : P} {T : ℕ} :
    (∀ t ≤ T, (dnModel (V := V) MA).okP p (exec x σ t) (exec y τ t)) ↔ FIIndist x y σ τ T p := by
  constructor
  · intro h
    rcases h T le_rfl with ⟨h', -⟩ | h'
    · exact (indist_exec.1 h').2
    · have e : (dnModel (V := V) MA).indist p (exec x σ T) (exec y τ T) := by
        rw [← h']; exact (dnModel (V := V) MA).indist_refl p _
      exact (indist_exec.1 e).2
  · intro h t ht
    exact Or.inl ⟨indist_exec.2 ⟨rfl, h.mono t ht⟩, trivial, trivial⟩

/-- **Consensus under a general message adversary, without topology.** Consensus is solvable iff
there is a labelling `L` of executions (inputs, pattern) such that (i) executions in which all
inputs are `v` get label `v`, and (ii) `L` is locally constant: for every admissible `(x, σ)`
there is a round `T` such that every admissible `(y, τ)` in which some process has the same view
after `T` rounds as in `(x, σ)` has the same label. -/
theorem dn_solvable_iff [Nonempty V] :
    UniformSolvable (dnModel (V := V) MA) ↔
      ∃ L : (P → V) → (ℕ → Graph P) → V,
        (∀ v x, ∀ σ ∈ MA, (∀ p, x p = v) → L x σ = v) ∧
        ∀ x, ∀ σ ∈ MA, ∃ T, ∀ y, ∀ τ ∈ MA, (∃ p, FIIndist x y σ τ T p) → L y τ = L x σ := by
  classical
  rw [dn_theorem_5_2]
  constructor
  · rintro ⟨lab, hcl, hval⟩
    refine ⟨fun x σ => if h : σ ∈ MA then lab ⟨exec x σ, exec_mem_adm x h⟩
      else Classical.arbitrary V, ?_, ?_⟩
    · intro v x σ hσ hx
      simp only [dite_eq_left hσ]
      exact hval _ v hx
    · intro x σ hσ
      have hopen := (Model.isOpen_τU_iff _ _).1 (hcl (lab ⟨exec x σ, exec_mem_adm x hσ⟩)).2
        ⟨exec x σ, exec_mem_adm x hσ⟩ rfl
      obtain ⟨T, hT⟩ := hopen
      refine ⟨T, fun y τ hτ ⟨p, hp⟩ => ?_⟩
      simp only [dite_eq_left hτ, dite_eq_left hσ]
      exact hT ⟨exec y τ, exec_mem_adm y hτ⟩ ⟨p, okP_upTo_iff.2 hp⟩
  · rintro ⟨L, hval, hloc⟩
    have hL : ∀ γ : (dnModel (V := V) MA).adm, ∃ x, ∃ σ ∈ MA, (γ : ℕ → Conf P V) = exec x σ :=
      fun γ => γ.2
    choose fx fσ hfσ hfeq using hL
    let lab : (dnModel (V := V) MA).adm → V := fun γ => L (fx γ) (fσ γ)
    refine ⟨lab, fun v => @isClopen_fibers _ _ (dnModel (V := V) MA).τU lab ?_ v, ?_⟩
    · intro w
      rw [Model.isOpen_τU_iff]
      intro γ hγ
      obtain ⟨T, hT⟩ := hloc (fx γ) (fσ γ) (hfσ γ)
      refine ⟨T, fun δ ⟨p, hp⟩ => ?_⟩
      simp only [mem_preimage, mem_singleton_iff] at hγ ⊢
      rw [← hγ]
      rw [hfeq γ, hfeq δ] at hp
      exact hT (fx δ) (fσ δ) (hfσ δ) ⟨p, okP_upTo_iff.1 hp⟩
    · intro γ v hv
      apply hval v (fx γ) (fσ γ) (hfσ γ)
      intro p
      have := hv p
      rw [hfeq γ] at this
      exact this

end DN

end TopoConsensus
