import Mathlib
import Cslib.Computability.Distributed.DynamicNetworks.HeardOf
import Cslib.Computability.Distributed.DynamicNetworks.Journey

/-!
# The model of Biely–Robinson–Schmid–Schwarz–Winkler (Section 3)

A fixed finite set `P` of processes with unique identifiers runs in synchronous lock-step rounds.
In round `t + 1` an omniscient message adversary chooses the directed communication graph `ρ t`
(`Cslib.HeardOf.Graph`: `ρ t q p` means that `p` receives the round-`t+1` message of `q`; every
process always "hears" itself). A message adversary (Definition 2) is a set of communication
patterns `ρ : ℕ → Graph P`; inputs are arbitrary and independent of the pattern.

**Algorithms.** We use the full-information form: every process broadcasts its whole state and
applies a deterministic transition function (`Cslib.HeardOf.StepFn`) to the vector of received
states. The paper's algorithms (a sending function `M_p` and a transition function `T_p`) are the
special case where the state is post-processed by `M_p`; impossibility results for full-information
algorithms therefore cover every algorithm of the paper's model. A process' identifier is an
argument of `init` and `step`, and the algorithm may depend on `P` (it knows `n`) and on any
parameter of the adversary. Decisions are irrevocable (`dec_stable`, the paper's "decided states
are closed under the transition function").

**Problems** (Definitions 3 and 4). `SolvesKSet A k Adv`: for every input vector and every pattern
of `Adv`, at most `k` different values are decided, every decision is some input, and every process
decides. Consensus is `k = 1`.

**Graph notions** (Definitions 5–10, 12, 15, 16), with round indices starting at `0` (the paper's
round `t + 1` is our index `t`; the paper's interval `I = [a, b]` of rounds has the same length
`b − a + 1`):
* `IsRootComp G R`: `R` is a root component (= source component, CSLib's
  `Digraph.IsSourceComponent`) of `G`.
* `IsVSRC ρ R a b`: `R` is a vertex-stable root component in the rounds `a..b`.
* The causal distance bound `cd_x(p, q) ≤ k` (Definition 7, `k ≥ 1`) is the journey
  `Journey ρ x p (x + k) q` (CSLib `Cslib.DynNet.Journey`, from time `x` to time `x + k`).
* `DBounded`, `HNetBounded` (Definitions 9 and 10), the message adversaries `VSRCd` (Def. 12),
  `VSRCk`, `VSRCkInf` (Def. 15, finite and infinite stability window) and `SigmaMaj` (Def. 16).
-/

namespace Podc.GracefulKSetAgreement

open Cslib.HeardOf Cslib.DynNet

/-- A deterministic full-information algorithm with inputs in `V`, states `σ`, and irrevocable
decisions `dec`. -/
structure Alg (P V σ : Type) where
  /-- Initial state of a process with a given input. -/
  init : P → V → σ
  /-- Transition function (receives its own state and the states of the processes it hears). -/
  step : StepFn P σ
  /-- Decision of a state (`none` = undecided). -/
  dec : σ → Option V
  /-- Decisions are irrevocable. -/
  dec_stable : ∀ i (m : P → Option σ) s v, m i = some s → dec s = some v → dec (step i m) = some v

namespace Alg

variable {P V σ : Type} (A : Alg P V σ)

/-- The initial configuration for the input vector `x`. -/
def initC (x : P → V) : P → σ := fun i => A.init i (x i)

/-- The configuration after `t` rounds of the pattern `ρ`. -/
noncomputable def run (x : P → V) (ρ : ℕ → Graph P) (t : ℕ) : P → σ :=
  conf A.step (A.initC x) ρ t

/-- `i` decides `v` in the run `(x, ρ)`. -/
def Decides (x : P → V) (ρ : ℕ → Graph P) (i : P) (v : V) : Prop :=
  ∃ t, A.dec (A.run x ρ t i) = some v

/-- `A` solves `k`-set agreement under the message adversary `Adv` (Definition 4). -/
def SolvesKSet (k : ℕ) (Adv : Set (ℕ → Graph P)) : Prop :=
  ∀ x : P → V, ∀ ρ ∈ Adv,
    (∀ S : Finset V, (∀ v ∈ S, ∃ i, A.Decides x ρ i v) → S.card ≤ k) ∧
    (∀ i v, A.Decides x ρ i v → ∃ j, x j = v) ∧
    (∀ i, ∃ v, A.Decides x ρ i v)

/-- `A` solves consensus under `Adv` (Definition 3). -/
abbrev SolvesConsensus (Adv : Set (ℕ → Graph P)) : Prop := A.SolvesKSet 1 Adv

theorem SolvesKSet.mono {A : Alg P V σ} {k : ℕ} {Adv Adv' : Set (ℕ → Graph P)}
    (h : A.SolvesKSet k Adv) (hsub : Adv' ⊆ Adv) : A.SolvesKSet k Adv' :=
  fun x ρ hρ => h x ρ (hsub hρ)

/-- Decisions persist along configurations. -/
theorem dec_conf_mono {C : P → σ} {ρ : ℕ → Graph P} {i : P} {v : V} {t t' : ℕ}
    (h : A.dec (conf A.step C ρ t i) = some v) (htt : t ≤ t') :
    A.dec (conf A.step C ρ t' i) = some v := by
  induction htt with
  | refl => exact h
  | step _ ih =>
    rw [conf_succ]
    exact A.dec_stable i _ _ v (by simp [msgs, hears_self]) ih

/-- A process decides at most one value. -/
theorem Decides.unique {x : P → V} {ρ : ℕ → Graph P} {i : P} {v w : V}
    (hv : A.Decides x ρ i v) (hw : A.Decides x ρ i w) : v = w := by
  obtain ⟨t, ht⟩ := hv
  obtain ⟨t', ht'⟩ := hw
  have h1 := A.dec_conf_mono ht (le_max_left t t')
  have h2 := A.dec_conf_mono ht' (le_max_right t t')
  rw [run, h1] at *
  exact Option.some_injective _ (h1.symm.trans h2)

end Alg

/-! ### Locality -/

section Locality

variable {P σ : Type}

/-- If two configurations agree outside `S`, then at time `t` they agree on every process that
no process of `S` (at time `0`) reaches by a journey. -/
theorem conf_eq_of_not_journey (step : StepFn P σ) {C₁ C₂ : P → σ} (ρ : ℕ → Graph P)
    (S : Set P) (hC : ∀ i, i ∉ S → C₁ i = C₂ i) :
    ∀ t q, (∀ p ∈ S, ¬ Journey ρ 0 p t q) → conf step C₁ ρ t q = conf step C₂ ρ t q := by
  intro t
  induction t with
  | zero =>
    intro q hq
    refine hC q fun hqS => hq q hqS .refl
  | succ t ih =>
    intro q hq
    rw [conf_succ, conf_succ]
    refine next_eq_of_agree (SameIn.refl _ _) fun j hj => ih j fun p hp hpj => ?_
    refine hq p hp (.step hpj ?_)
    rcases hj with rfl | hj
    · exact Or.inl rfl
    · exact Or.inr hj

/-- **Validity forces isolated groups to decide their own input.** If the processes of `S` hear
only processes of `S` in every round of `ρ ∈ Adv`, all of them have input `c`, and `A` solves
`k`-set agreement under `Adv`, then every decision in `S` is `c`. -/
theorem Alg.decides_of_closed {V : Type} {A : Alg P V σ} {k : ℕ} {Adv : Set (ℕ → Graph P)}
    (hA : A.SolvesKSet k Adv) {x : P → V} {ρ : ℕ → Graph P} (hρ : ρ ∈ Adv) (S : Set P)
    (hS : ∀ t, ∀ i ∈ S, ∀ j, Hears (ρ t) i j → j ∈ S) {c : V} (hc : ∀ i ∈ S, x i = c)
    {i : P} (hi : i ∈ S) {v : V} (hv : A.Decides x ρ i v) : v = c := by
  obtain ⟨t, ht⟩ := hv
  have heq : A.run x ρ t i = A.run (fun _ => c) ρ t i :=
    conf_agree S (fun _ _ _ => SameIn.refl _ _) hS
      (fun j hj => by simp [Alg.initC, hc j hj]) t i hi
  obtain ⟨j, hj⟩ := (hA (fun _ => c) ρ hρ).2.1 i v ⟨t, heq ▸ ht⟩
  exact hj.symm

/-- A process that is deaf in every round decides its own input. -/
theorem Alg.decides_own_of_deaf {V : Type} {A : Alg P V σ} {k : ℕ} {Adv : Set (ℕ → Graph P)}
    (hA : A.SolvesKSet k Adv) (x : P → V) {ρ : ℕ → Graph P} (hρ : ρ ∈ Adv) {i : P}
    (hi : ∀ t, Deaf (ρ t) i) : A.Decides x ρ i (x i) := by
  obtain ⟨v, hv⟩ := (hA x ρ hρ).2.2 i
  have := A.decides_of_closed hA hρ {i}
    (fun t j hj l hl => by rw [Set.mem_singleton_iff] at hj ⊢; subst hj; exact (hi t).eq hl)
    (c := x i) (fun j hj => by rw [Set.mem_singleton_iff] at hj; rw [hj]) rfl hv
  exact this ▸ hv

end Locality

/-! ### Root components and vertex-stable root components -/

section Graphs

variable {P : Type}

/-- `R` is a root component of `G` (Definition 5): a strongly connected component without
incoming edges from outside (CSLib's source components). -/
def IsRootComp (G : Graph P) (R : Set P) : Prop :=
  (Digraph.mk G).IsSourceComponent R

/-- Elementary characterization of root components: non-empty, closed under in-neighbours,
and strongly connected. -/
theorem isRootComp_iff {G : Graph P} {R : Set P} :
    IsRootComp G R ↔ R.Nonempty ∧ (∀ v ∈ R, ∀ u, G u v → u ∈ R) ∧
      ∀ u ∈ R, ∀ v ∈ R, (Digraph.mk G).Reachable u v := by
  constructor
  · intro h
    exact ⟨h.nonempty, h.closed, fun u hu v hv => h.reachable hu hv⟩
  · rintro ⟨⟨r, hr⟩, hcl, hsc⟩
    refine Digraph.isSourceComponent_iff.mpr ⟨r, ?_, fun x hx => ?_⟩
    · ext x
      exact ⟨fun hx => hsc x hx r hr,
        fun hx => Digraph.mem_of_reachable_of_closed (G := Digraph.mk G) hcl hx hr⟩
    · exact hsc r hr x (Digraph.mem_of_reachable_of_closed (G := Digraph.mk G) hcl hx hr)

/-- A singleton is a root component iff the process is deaf. -/
theorem isRootComp_singleton_iff {G : Graph P} {i : P} : IsRootComp G {i} ↔ Deaf G i := by
  rw [isRootComp_iff]
  constructor
  · rintro ⟨-, hcl, -⟩ j hj
    exact hcl i rfl j hj
  · intro h
    refine ⟨⟨i, rfl⟩, fun v hv u huv => ?_, fun u hu v hv => ?_⟩
    · rw [Set.mem_singleton_iff] at hv ⊢; subst hv; exact h u huv
    · rw [Set.mem_singleton_iff] at hu hv; subst hu hv; exact Digraph.Reachable.rfl

/-- A pair `{u, v}` linked in both directions without other in-neighbours is a root component. -/
theorem isRootComp_pair {G : Graph P} {u v : P} (huv : G u v) (hvu : G v u)
    (hcl : ∀ w, ∀ z, (z = u ∨ z = v) → G w z → w = u ∨ w = v) : IsRootComp G {u, v} := by
  rw [isRootComp_iff]
  refine ⟨⟨u, by simp⟩, fun z hz w hw => ?_, fun a ha b hb => ?_⟩
  · simpa using hcl w z (by simpa using hz) hw
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact .rfl
    · exact Digraph.Adj.reachable (G := Digraph.mk G) huv
    · exact Digraph.Adj.reachable (G := Digraph.mk G) hvu
    · exact .rfl

/-- **Counting root components.** If `𝓡` consists of root components of `G` and every process is
reachable from one of them, then every root component of `G` belongs to `𝓡`. -/
theorem isRootComp_mem_of_reach {G : Graph P} {𝓡 : Set (Set P)}
    (h𝓡 : ∀ R ∈ 𝓡, IsRootComp G R)
    (hreach : ∀ v, ∃ R ∈ 𝓡, ∃ u ∈ R, (Digraph.mk G).Reachable u v)
    {S : Set P} (hS : IsRootComp G S) : S ∈ 𝓡 := by
  obtain ⟨v, hv⟩ := hS.nonempty
  obtain ⟨R, hR, u, hu, huv⟩ := hreach v
  have huS : u ∈ S := Digraph.mem_of_reachable_of_closed hS.closed huv hv
  have : R = S := (h𝓡 R hR).eq_of_mem hS hu huS
  exact this ▸ hR

/-- `R` is a vertex-stable root component in the rounds `a, …, b` (Definition 6). -/
def IsVSRC (ρ : ℕ → Graph P) (R : Set P) (a b : ℕ) : Prop :=
  ∀ t, a ≤ t → t ≤ b → IsRootComp (ρ t) R

/-- `R` is a vertex-stable root component in all rounds from `a` on. -/
def IsVSRCFrom (ρ : ℕ → Graph P) (R : Set P) (a : ℕ) : Prop :=
  ∀ t, a ≤ t → IsRootComp (ρ t) R

/-- Definition 9: the `[a, b]`-VSRC `R` is `D`-bounded: either `|I| < D`, or the dynamic causal
diameter of `R` is at most `D` for every starting round `x ∈ [a, b − D + 1]`. -/
def DBounded (D : ℕ) (ρ : ℕ → Graph P) (R : Set P) (a b : ℕ) : Prop :=
  b + 1 < a + D ∨ ∀ x, a ≤ x → x + D ≤ b + 1 → ∀ p ∈ R, ∀ q ∈ R, Journey ρ x p (x + D) q

/-- Definition 10: the set `S` of `[a, b]`-VSRCs is `H`-network-bounded: either `|I| < H`, or for
every starting round `x ∈ [a, b − H + 1]` every process is reached within `H` rounds from some
member of some `R ∈ S`. -/
def HNetBounded (H : ℕ) (ρ : ℕ → Graph P) (S : Set (Set P)) (a b : ℕ) : Prop :=
  b + 1 < a + H ∨ ∀ x, a ≤ x → x + H ≤ b + 1 → ∀ q, ∃ R ∈ S, ∃ p ∈ R, Journey ρ x p (x + H) q

/-- Definition 10 for an infinite interval `[a, ∞)`. -/
def HNetBoundedFrom (H : ℕ) (ρ : ℕ → Graph P) (S : Set (Set P)) (a : ℕ) : Prop :=
  ∀ x, a ≤ x → ∀ q, ∃ R ∈ S, ∃ p ∈ R, Journey ρ x p (x + H) q

/-- **Definition 12**, the consensus message adversary `VSRC(d)` (with network causal diameter
`H`): (i) exactly one root component per round, (ii) every vertex-stable root component is
`H`-network-bounded, (iii) some `d`-round window with an `H`-network-bounded VSRC. -/
def VSRCd (H d : ℕ) : Set (ℕ → Graph P) := {ρ |
  (∀ t, ∃! R, IsRootComp (ρ t) R) ∧
  (∀ R a b, IsVSRC ρ R a b → HNetBounded H ρ {R} a b) ∧
  ∃ a R, IsVSRC ρ R a (a + d - 1) ∧ HNetBounded H ρ {R} a (a + d - 1)}

/-- **Definition 15**, the message adversary `VSRC(k, d)` (with parameters `D`, `H`), literal
reading: (i) at most `k` root components per round, (ii) every VSRC is `D`-bounded, (iii) a
`d`-round window `J` in which `1 ≤ ℓ ≤ k` `H`-network-bounded VSRCs exist simultaneously. -/
def VSRCk (D H k d : ℕ) : Set (ℕ → Graph P) := {ρ |
  (∀ t, {R | IsRootComp (ρ t) R}.ncard ≤ k) ∧
  (∀ R a b, IsVSRC ρ R a b → DBounded D ρ R a b) ∧
  ∃ a, ∃ S : Set (Set P), 1 ≤ S.ncard ∧ S.ncard ≤ k ∧
    (∀ R ∈ S, IsVSRC ρ R a (a + d - 1)) ∧ HNetBounded H ρ S a (a + d - 1)}

/-- Definition 15, strong reading of (iii): *all* root components of the rounds of `J` are among
the `ℓ` stable ones. Smaller than `VSRCk`, so impossibility results for it are stronger. -/
def VSRCkAll (D H k d : ℕ) : Set (ℕ → Graph P) := {ρ |
  (∀ t, {R | IsRootComp (ρ t) R}.ncard ≤ k) ∧
  (∀ R a b, IsVSRC ρ R a b → DBounded D ρ R a b) ∧
  ∃ a, ∃ S : Set (Set P), 1 ≤ S.ncard ∧ S.ncard ≤ k ∧
    (∀ R ∈ S, IsVSRC ρ R a (a + d - 1)) ∧ HNetBounded H ρ S a (a + d - 1) ∧
    ∀ t, a ≤ t → t ≤ a + d - 1 → ∀ R, IsRootComp (ρ t) R → R ∈ S}

theorem VSRCkAll_subset (D H k d : ℕ) : (VSRCkAll D H k d : Set (ℕ → Graph P)) ⊆ VSRCk D H k d :=
  fun _ ⟨h1, h2, a, S, h3, h4, h5, h6, _⟩ => ⟨h1, h2, a, S, h3, h4, h5, h6⟩

/-- **Definition 15 with `d = ∞`**, `VSRC(k, ∞)`: the window `J = [a, ∞)` is infinite (strong
reading of (iii), as in `VSRCkAll`). -/
def VSRCkInf (D H k : ℕ) : Set (ℕ → Graph P) := {ρ |
  (∀ t, {R | IsRootComp (ρ t) R}.ncard ≤ k) ∧
  (∀ R a b, IsVSRC ρ R a b → DBounded D ρ R a b) ∧
  ∃ a, ∃ S : Set (Set P), 1 ≤ S.ncard ∧ S.ncard ≤ k ∧
    (∀ R ∈ S, IsVSRCFrom ρ R a) ∧ HNetBoundedFrom H ρ S a ∧
    ∀ t, a ≤ t → ∀ R, IsRootComp (ρ t) R → R ∈ S}

/-- `VSRC(k, ∞)` grows with `k`. -/
theorem VSRCkInf_mono {D H k k' : ℕ} (hk : k ≤ k') :
    (VSRCkInf D H k : Set (ℕ → Graph P)) ⊆ VSRCkInf D H k' :=
  fun _ ⟨h1, h2, a, S, h3, h4, h5⟩ =>
    ⟨fun t => (h1 t).trans hk, h2, a, S, h3, h4.trans hk, h5⟩

/-- **Definition 16**, the `Σ_{n−1}`-influence message adversary `Σ_{n−1}-MAJ`: for every choice
of intervals `I_i = [a i, b i]` during which `{i}` is a root component (i.e. `i` is deaf), for
every process `i`, some `{i}^{I_i}` influences some `{j}^{I_j}`, `j ≠ i`: a causal chain from `i`
starting after `I_i` reaches `j` by the beginning of `I_j`. -/
def SigmaMaj : Set (ℕ → Graph P) := {ρ |
  ∀ a b : P → ℕ, (∀ i, a i ≤ b i) → (∀ i, IsVSRC ρ {i} (a i) (b i)) →
    ∃ i j, i ≠ j ∧ Journey ρ (b i + 1) i (a j) j}

end Graphs

end Podc.GracefulKSetAgreement
