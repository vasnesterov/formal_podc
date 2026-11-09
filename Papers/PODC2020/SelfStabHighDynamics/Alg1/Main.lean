import Papers.PODC2020.SelfStabHighDynamics.Alg1.Exec

/-!
# Algorithm 1: the results of Section 4.2

Paper-facing statements for Algorithm 1 (self-stabilizing leader election for `TC_B(Δ)`, `Δ ≥ 1`
known, `n` unknown). `exec G γ t` is the configuration at the end of the paper's Round `t`.
The leader `ℓ` is the least identifier of `V` (`IsLeast (V : Set ι) ℓ`, i.e. `ℓ = V.min' hV`,
see `qLegit_iff`, `legit_iff`). The proofs are in `Alg1/Exec.lean`.

Deviations from the paper's proofs: Claim (*) of Lemma 3 is proved by induction on the length
`J` of a journey from `ℓ` (`claim`), which avoids the paper's double indexing; several
hypotheses are dropped where unused (see the docstrings).
-/

namespace Podc.SelfStabHighDynamics.Alg1

open StabilizingLEDynamic (IsDG JssB DG)

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ} (hΔ : 0 < Δ) {V : Finset ι} {G : DG ι}
  {γ : ι → St ι}

/-- Line 7: the lexicographic minimum of a nonempty mailbox is one of its messages and is
lexicographically below every message. -/
theorem lexMin_spec (mb : Finset (ι × ℕ)) (h : mb.Nonempty) :
    lexMin mb h ∈ mb ∧ ∀ y ∈ mb,
      (lexMin mb h).1 < y.1 ∨ ((lexMin mb h).1 = y.1 ∧ (lexMin mb h).2 ≤ y.2) :=
  ⟨lexMin_mem mb h, fun _ hy => lexMin_le mb h hy⟩

/-- **Remark 6** of [Altisen et al.]. Since the end of the first round, every process satisfies
`lid(p) ≤ id(p)` and `lid(p) = id(p) ⇒ ttl(p) = 0` (in every dynamic graph, from every
configuration). -/
theorem remark_6 (G : DG ι) (γ : ι → St ι) (t : ℕ) (p : ι) :
    ((alg Δ hΔ).exec G γ (t + 1) p).lid ≤ p ∧
      (((alg Δ hΔ).exec G γ (t + 1) p).lid = p → ((alg Δ hΔ).exec G γ (t + 1) p).ttl = 0) :=
  remark6 G γ t p

/-- The configurations of Algorithm 1 for `V` (`ttl(p) ∈ {0, …, 2Δ - 1}`) are closed under the
execution, in every dynamic graph. -/
theorem exec_mem_Cfg (G : DG ι) (hγ : γ ∈ (alg Δ hΔ).Cfg V) (t : ℕ) :
    (alg Δ hΔ).exec G γ t ∈ (alg Δ hΔ).Cfg V :=
  exec_mem_cfg G hγ t

/-- **Lemma 1** of [Altisen et al.]. Let `f` be a fake ID. At the end of Round `t` (= beginning
of Round `t + 1`), every process `p` with `lid(p) = f` has `ttl(p) ≥ t`. (No assumption on the
initial configuration is needed.) -/
theorem lemma_1 (hG : IsDG V G) (γ : ι → St ι) {f : ι} (hf : f ∉ V) :
    ∀ t, ∀ p ∈ V, ((alg Δ hΔ).exec G γ t p).lid = f → t ≤ ((alg Δ hΔ).exec G γ t p).ttl :=
  lemma1 hG γ hf

/-- **Corollary 4** of [Altisen et al.]. At the end of Round `2Δ`, the configuration is
quasi-legitimate. -/
theorem corollary_4 (hG : IsDG V G) (hγ : γ ∈ (alg Δ hΔ).Cfg V) :
    QLegit V ((alg Δ hΔ).exec G γ (2 * Δ)) :=
  cor4 hG hγ

/-- **Lemma 2** of [Altisen et al.]. In every dynamic graph with vertex set `V`, an execution
from a quasi-legitimate configuration is quasi-legitimate at the end of every round. -/
theorem lemma_2 (hG : IsDG V G) (hQ : QLegit V γ) :
    ∀ t, QLegit V ((alg Δ hΔ).exec G γ t) :=
  qLegit_exec hG hQ

/-- **Lemma 3** of [Altisen et al.]. In a dynamic graph of `TC_B(Δ)`, an execution from a
quasi-legitimate configuration is legitimate at the end of every Round `r ≥ Δ`. (The paper's
`G_{[t, +∞)}` is covered since `TC_B(Δ)` is suffix-closed, `J_shift`.) -/
theorem lemma_3 (hG : G ∈ JssB Δ V) (hQ : QLegit V γ) :
    ∀ r ≥ Δ, Legit Δ V ((alg Δ hΔ).exec G γ r) :=
  lemma3 hG hQ

/-- **Corollary 5** of [Altisen et al.]. In a dynamic graph of `TC_B(Δ)`, at the end of every
Round `i ≥ 3Δ` of every execution, the configuration is legitimate. -/
theorem corollary_5 (hG : G ∈ JssB Δ V) (hγ : γ ∈ (alg Δ hΔ).Cfg V) :
    ∀ i ≥ 3 * Δ, Legit Δ V ((alg Δ hΔ).exec G γ i) :=
  cor5 hG hγ

/-- **Lemma 4** of [Altisen et al.] (stated also for `r = 0`). In every dynamic graph with
vertex set `V`, from a legitimate configuration, at the end of every Round `r < Δ`, every
process has `lid = id(ℓ)` and `ttl ≤ Δ + r`. -/
theorem lemma_4 (hG : IsDG V G) (hL : Legit Δ V γ) (hV : V.Nonempty) :
    ∀ r < Δ, ∀ p ∈ V,
      ((alg Δ hΔ).exec G γ r p).lid = V.min' hV ∧ ((alg Δ hΔ).exec G γ r p).ttl ≤ Δ + r :=
  lemma4 hG hL (Finset.isLeast_min' V hV)

/-- **Theorem 4** of [Altisen et al.]. In a dynamic graph of `TC_B(Δ)`, the execution from a
legitimate configuration satisfies `SP_LE`. -/
theorem theorem_4 (hV : V.Nonempty) (hG : G ∈ JssB Δ V) (hL : Legit Δ V γ) :
    spLE (alg Δ hΔ) V ((alg Δ hΔ).exec G γ) :=
  thm4 hV hG hL

/-- The legitimate configurations of Algorithm 1 for `V`. -/
def legitSet (Δ : ℕ) (hΔ : 0 < Δ) (V : Finset ι) : Set (ι → St ι) :=
  {γ | γ ∈ (alg Δ hΔ).Cfg V ∧ Legit Δ V γ}

/-- **Corollary 6** of [Altisen et al.]. The legitimate configurations form a set of legitimate
configurations of Algorithm 1 for `SP_LE` in `TC_B(Δ)` (Definition 1), reached from every
configuration within `3Δ` rounds and from then on forever. -/
theorem corollary_6 (hV : V.Nonempty) :
    IsLegit (alg Δ hΔ) (JssB Δ) (spLE (alg Δ hΔ)) V (legitSet Δ hΔ V) ∧
      ∀ G ∈ JssB Δ V, ∀ γ ∈ (alg Δ hΔ).Cfg V, ∀ i ≥ 3 * Δ,
        (alg Δ hΔ).exec G γ i ∈ legitSet Δ hΔ V := by
  have hconv : ∀ G ∈ JssB Δ V, ∀ γ ∈ (alg Δ hΔ).Cfg V, ∀ i ≥ 3 * Δ,
      (alg Δ hΔ).exec G γ i ∈ legitSet Δ hΔ V :=
    fun G hG γ hγ i hi => ⟨exec_mem_cfg G hγ i, cor5 hG hγ i hi⟩
  exact ⟨⟨fun _ h => h.1, fun G hG γ hγ => ⟨3 * Δ, hconv G hG γ hγ _ le_rfl⟩,
    fun G hG γ hγ => thm4 hV hG hγ.2⟩, hconv⟩

/-- **Corollary 6** of [Altisen et al.]. Algorithm 1 is a self-stabilizing leader election
algorithm for `TC_B(Δ)`. -/
theorem selfStab : SelfStab (alg (ι := ι) Δ hΔ) (JssB Δ) (spLE (alg Δ hΔ)) :=
  fun V hV => ⟨legitSet Δ hΔ V, (corollary_6 hΔ hV).1⟩

/-- Algorithm 1 is `(1, V)`-ambiguous for every `V` with at least two processes (Section 3.3;
its possible local states do not depend on the system). -/
theorem ambiguous (hV : 2 ≤ V.card) : Ambiguous (alg Δ hΔ) 1 V :=
  ⟨Nat.one_pos, by omega, fun _ _ _ _ _ => rfl⟩

/-- Algorithm 1 is size-ambiguous (as soon as there are two identifiers). -/
theorem sizeAmbiguous [Nontrivial ι] : SizeAmbiguous (alg (ι := ι) Δ hΔ) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne ι
  exact ⟨1, {a, b}, ambiguous hΔ (by rw [Finset.card_pair hab])⟩

end Podc.SelfStabHighDynamics.Alg1
