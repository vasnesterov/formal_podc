import Mathlib

/-!
# Theorem 1 in the paper's model-agnostic form

Theorem 1 of [BRS11] is stated for an arbitrary "system model" `M` (any set of admissible runs for
each algorithm) and a restricted model `M' = ⟨D̄⟩`. We formalize this generic setting abstractly:
a model gives, for every algorithm, a set of runs; a run gives every process a *view* (its sequence
of local states until it decides, Definition 2), from which the process' input and decision are
read off; a run says which processes are correct; and the model says, for every run, whether the
processes of `D̄` receive no message from `D` before all of `D̄` have decided (property
`(dec-D̄)`).

* `Theorem1Statement` is Theorem 1 exactly as stated (conditions (A)–(D)).
* `theorem1_statement_false`: read literally, it fails in a model that fixes an input value (outside
  the paper's problem definition, where inputs are arbitrary and admissibility does not depend on
  them; there the missing hypothesis (E) holds, so this is an under-specified statement). In the paper's proof, Fact 1 ("in each run of
  `R(D̄)` all processes of `D̄` decide on a common value") is derived from (B) and `k`-agreement
  alone, and the consensus algorithm `A|D̄` is claimed to satisfy validity in `M'`; both silently
  assume that the processes of `D̄` can only decide values proposed in `D̄`. Counterexample:
  `n = 3`, `k = 2`, `D = D₁ = {0}`, `D̄ = {1, 2}`, `V = Fin 4`; in `M` the processes never
  communicate and process `0`'s input is always `0`; `A` = "decide `0`" solves (even) consensus in
  `M`, while all of (A)–(D) hold with `M'` = `D̄` without communication, inputs in `{1, 2, 3}`.
* `condB_fails`: with the values `v₁, …, v_{k-1}` fixed in advance, condition (B) fails as soon
  as a run of `R(D̄)` has a process of `D̄` proposing some `v i` — which is always the case in the
  paper's applications, where the inputs are arbitrary distinct values.
* `theorem1_corrected`: Theorem 1 holds with the missing hypothesis (E) (processes of `D̄` decide
  only values proposed in `D̄` in the runs of `R(D̄)`), with run-dependent values in (B), with (D)
  strengthened to provide runs in `R(D̄)` (the paper's "clearly `ρ ∈ R(D̄)`" does not follow from
  indistinguishability *until decision*, which says nothing about a process of `D̄` after it has
  decided while another one has not) that preserve correctness of the processes of `D̄` (needed
  for termination of `A|D̄`, which the paper's proof does not address), and with (C) only for the
  algorithm `A|D̄`. Condition (A) is not needed.

In the paper's applications (Theorem 2 / Corollary 5) all extra hypotheses hold; see
`KSetAgreement.theorem1_async` for the concrete asynchronous version, proved from CSLib's FLP.
-/

namespace KSetAgreement.Abstract

/-- An abstract system model with processes `P`, values `V` and local views `W`. -/
structure SysModel (P V W : Type) where
  /-- Algorithms. -/
  Alg : Type
  /-- Runs. -/
  Run : Type
  /-- The admissible runs of an algorithm. -/
  runs : Alg → Set Run
  /-- The view (local state sequence until decision) of a process in a run. -/
  view : Run → P → W
  /-- Correct (non-faulty) processes. -/
  correct : Run → P → Prop
  /-- `isolated D Dbar r`: in `r`, no process of `Dbar` receives a message from a process of `D`
  until every process of `Dbar` has decided (property `(dec-D̄)`). -/
  isolated : Set P → Set P → Run → Prop

variable {P V W : Type} (inOf : W → V) (decOf : W → Option V)

namespace SysModel

variable (M : SysModel P V W)

/-- Input of `p` in run `r`. -/
def input (r : M.Run) (p : P) : V := inOf (M.view r p)

/-- Decision of `p` in run `r`. -/
def dec (r : M.Run) (p : P) : Option V := decOf (M.view r p)

/-- `A` solves `k`-set agreement in `M`. -/
def SolvesKSA (A : M.Alg) (k : ℕ) : Prop :=
  ∀ r ∈ M.runs A, {v | ∃ p, M.dec decOf r p = some v}.ncard ≤ k ∧
    (∀ p v, M.dec decOf r p = some v → ∃ q, M.input inOf r q = v) ∧
    ∀ p, M.correct r p → (M.dec decOf r p).isSome

/-- `B` solves consensus among the processes of `Dbar` in `M`. -/
def SolvesConsensus (Dbar : Set P) (B : M.Alg) : Prop :=
  ∀ r ∈ M.runs B,
    (∀ p ∈ Dbar, ∀ q ∈ Dbar, ∀ v v', M.dec decOf r p = some v → M.dec decOf r q = some v' →
      v = v') ∧
    (∀ p ∈ Dbar, ∀ v, M.dec decOf r p = some v → ∃ q ∈ Dbar, M.input inOf r q = v) ∧
    ∀ p ∈ Dbar, M.correct r p → (M.dec decOf r p).isSome

end SysModel

/-- Definition 2: runs `r` (of `M`) and `r'` (of `M'`) are indistinguishable for the processes
of `Dbar`. -/
def Indist {M M' : SysModel P V W} (Dbar : Set P) (r : M.Run) (r' : M'.Run) : Prop :=
  ∀ p ∈ Dbar, M.view r p = M'.view r' p

/-- The runs `M_A` of Theorem 1: admissible runs in which all inputs are distinct. -/
def MA (M : SysModel P V W) (A : M.Alg) : Set M.Run :=
  {r | r ∈ M.runs A ∧ Function.Injective (M.input inOf r)}

/-- `(dec-D)` for the groups `Dg i` (whose union is `D`) and values `v i`. -/
def DecD (M : SysModel P V W) {j : ℕ} (Dg : Fin j → Set P) (v : Fin j → V) (r : M.Run) : Prop :=
  ∀ i, (∃ q ∈ ⋃ i, Dg i, M.input inOf r q = v i) ∧ ∃ p ∈ Dg i, M.dec decOf r p = some (v i)

/-- **Theorem 1** of [BRS11], exactly as stated (for `k = j + 1`, groups `D₁, …, D_j`). -/
def Theorem1Statement : Prop :=
  ∀ (P V W : Type) [Finite P] (inOf : W → V) (decOf : W → Option V) (M M' : SysModel P V W)
    (restrict : M.Alg → M'.Alg) (A : M.Alg) (j : ℕ) (Dg : Fin j → Set P) (v : Fin j → V),
    (∀ i, (Dg i).Nonempty) → (∀ i i', i ≠ i' → Disjoint (Dg i) (Dg i')) →
    Function.Injective v →
    let D := ⋃ i, Dg i
    let Dbar := Dᶜ
    let RDbar := {r | r ∈ MA inOf M A ∧ M.isolated D Dbar r}
    let RDDbar := {r | r ∈ RDbar ∧ DecD inOf decOf M Dg v r}
    -- (A)
    RDbar.Nonempty →
    -- (B)
    (∀ α ∈ RDbar, ∃ β ∈ RDDbar, Indist (M := M) (M' := M) Dbar β α) →
    -- (C)
    (∀ B : M'.Alg, ¬ M'.SolvesConsensus inOf decOf Dbar B) →
    -- (D)
    (∀ ρ' ∈ M'.runs (restrict A), ∃ ρ ∈ MA inOf M A, Indist Dbar ρ ρ') →
    ¬ M.SolvesKSA inOf decOf A (j + 1)

/-! ### The counterexample -/

namespace Counterexample

/-- Views: input and decision. -/
abbrev View := Fin 4 × Option (Fin 4)

/-- Without communication an algorithm is a decision function (each process decides in its first
step, as a function of its input) and a run is an algorithm together with an input vector. -/
abbrev Alg := Fin 3 → Fin 4 → Fin 4

/-- The view of `p`: its input and its decision. -/
def view (r : Alg × (Fin 3 → Fin 4)) (p : Fin 3) : View := (r.2 p, some (r.1 p (r.2 p)))

/-- The model `M`: no communication, all processes correct, process `0` always has input `0`. -/
def M : SysModel (Fin 3) (Fin 4) View where
  Alg := Alg
  Run := Alg × (Fin 3 → Fin 4)
  runs δ := {r | r.1 = δ ∧ r.2 0 = 0}
  view := view
  correct _ _ := True
  isolated _ _ _ := True

/-- The restricted model `M' = ⟨{1, 2}⟩`: no communication, inputs in `{1, 2, 3}`, distinct. -/
def M' : SysModel (Fin 3) (Fin 4) View where
  Alg := Alg
  Run := Alg × (Fin 3 → Fin 4)
  runs δ := {r | r.1 = δ ∧ r.2 1 ≠ 0 ∧ r.2 2 ≠ 0 ∧ r.2 1 ≠ r.2 2}
  view := view
  correct _ _ := True
  isolated _ _ _ := True

/-- The algorithm: everybody decides `0`. -/
def A : Alg := fun _ _ => 0

theorem A_solves : M.SolvesKSA Prod.fst Prod.snd A 2 := by
  rintro ⟨δ, x⟩ ⟨rfl, hx0⟩
  refine ⟨?_, ?_, ?_⟩
  · have : {v | ∃ p, M.dec Prod.snd (A, x) p = some v} ⊆ {0} := by
      rintro v ⟨p, hp⟩
      simp [SysModel.dec, M, view, A] at hp
      simp [hp]
    exact le_trans (Set.ncard_le_ncard this (Set.toFinite _)) (by simp)
  · intro p v hv
    refine ⟨0, ?_⟩
    simp [SysModel.dec, M, view, A] at hv
    simpa [SysModel.input, M, view, ← hv] using hx0
  · intro p _
    simp [SysModel.dec, M, view]

/-- (C): consensus among `{1, 2}` is impossible in `M'`. -/
theorem no_consensus (B : Alg) : ¬ M'.SolvesConsensus Prod.fst Prod.snd {1, 2} B := by
  intro h
  -- decisions of process `p` with input `a`
  have run : ∀ a b : Fin 4, a ≠ 0 → b ≠ 0 → a ≠ b →
      B 1 a = B 2 b ∧ (B 1 a = a ∨ B 1 a = b) := by
    intro a b ha hb hab
    let x : Fin 3 → Fin 4 := ![0, a, b]
    obtain ⟨hag, hval, -⟩ := h (B, x) ⟨rfl, ha, hb, hab⟩
    have h1 := hag 1 (by simp) 2 (by simp) (B 1 a) (B 2 b)
      (by simp [SysModel.dec, M', view, x]) (by simp [SysModel.dec, M', view, x])
    obtain ⟨q, hq, hqv⟩ := hval 1 (by simp) (B 1 a) (by simp [SysModel.dec, M', view, x])
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · exact ⟨h1, Or.inl (by simpa [SysModel.input, M', view, x] using hqv.symm)⟩
    · exact ⟨h1, Or.inr (by simpa [SysModel.input, M', view, x] using hqv.symm)⟩
  have e1 := run 1 2 (by decide) (by decide) (by decide)
  have e2 := run 1 3 (by decide) (by decide) (by decide)
  have e3 := run 3 2 (by decide) (by decide) (by decide)
  -- `B 1 1 = B 2 2 = B 2 3 ∈ {1, 2} ∩ {1, 3}`, so `B 2 2 = 1`, but `B 3 ... `
  have hB11 : B 1 1 = 1 := by
    rcases e1.2 with h | h <;> rcases e2.2 with h' | h' <;> simp_all
  have : B 2 2 = 1 := by rw [← e1.1, hB11]
  rcases e3.2 with h | h <;> simp_all

/-- **Theorem 1 as stated is false.** -/
theorem theorem1_statement_false : ¬ Theorem1Statement := by
  intro h
  let Dg : Fin 1 → Set (Fin 3) := fun _ => {0}
  have hD : (⋃ i, Dg i) = {0} := by simp [Dg]
  have hDbar : (⋃ i, Dg i)ᶜ = ({1, 2} : Set (Fin 3)) := by
    rw [hD]; ext p; fin_cases p <;> simp
  refine h (Fin 3) (Fin 4) View Prod.fst Prod.snd M M' id A 1 Dg (fun _ => 0)
    (fun _ => ⟨0, rfl⟩) (fun i i' hii => absurd (Subsingleton.elim i i') hii)
    (fun i i' _ => Subsingleton.elim i i') ?_ ?_ ?_ ?_ A_solves
  · -- (A)
    refine ⟨(A, ![0, 1, 2]), ⟨⟨rfl, rfl⟩, ?_⟩, trivial⟩
    intro p q hpq
    fin_cases p <;> fin_cases q <;> simp_all [SysModel.input, M, view]
  · -- (B): every run of `R(D̄)` is in `R(D, D̄)`
    intro α hα
    obtain ⟨⟨⟨hα1, hα0⟩, -⟩, -⟩ := id hα
    refine ⟨α, ⟨hα, ?_⟩, fun _ _ => rfl⟩
    intro i
    refine ⟨⟨0, by simp [Dg], by simp [SysModel.input, M, view, hα0]⟩, 0, rfl, ?_⟩
    simp [SysModel.dec, M, view, hα1, A]
  · -- (C)
    intro B
    rw [hDbar]
    exact no_consensus B
  · -- (D)
    rintro ⟨δ, x⟩ ⟨rfl, h1, h2, h12⟩
    refine ⟨(A, Function.update x 0 0), ⟨⟨rfl, by simp⟩, ?_⟩, ?_⟩
    · intro p q hpq
      simp only [SysModel.input, M, view] at hpq
      fin_cases p <;> fin_cases q <;> simp_all [Function.update]
    · intro p hp
      rw [hDbar] at hp
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl <;> simp [M, M', view, Function.update]

end Counterexample

/-! ### The corrected theorem -/

/-- **Condition (B) with values fixed in advance fails** as soon as some run of `R(D̄)` has a
process of `D̄` proposing `v i`: no run of `R(D, D̄)` can be indistinguishable from it for `D̄`
(views contain the inputs, and in `R(D, D̄)` the value `v i` is proposed in `D`). In the paper's
applications `R(D̄)` contains runs with arbitrary distinct inputs, so (B) as stated is never
satisfied there; the values have to be chosen depending on the run (`theorem1_corrected`). -/
theorem condB_fails (M : SysModel P V W) (A : M.Alg) {j : ℕ} (Dg : Fin j → Set P)
    (v : Fin j → V) (α : M.Run) (i : Fin j) (p : P) (hp : p ∈ (⋃ i, Dg i)ᶜ)
    (hpv : M.input inOf α p = v i) :
    ¬ ∃ β ∈ MA inOf M A, DecD inOf decOf M Dg v β ∧
      Indist (M := M) (M' := M) (⋃ i, Dg i)ᶜ β α := by
  rintro ⟨β, hβ, hdec, hind⟩
  obtain ⟨⟨q, hq, hqv⟩, -⟩ := hdec i
  have : M.input inOf β p = v i := by rw [SysModel.input, hind p hp]; exact hpv
  have hpq : p = q := hβ.2 (this.trans hqv.symm)
  exact hp (hpq ▸ hq)


/-- **Theorem 1** of [BRS11], corrected. Compared with the statement: (A) is dropped (it is not
needed); in (B) the values `v i` may depend on the run (with values fixed in advance, (B) fails in
the paper's own applications, see `condB_fails`); (C) is only required for `A|D̄`; (D) must
provide indistinguishable runs that lie in `R(D̄)` and in which the correct processes of `D̄` are
correct; and (E) is added: in the runs of `R(D̄)` the processes of `D̄` decide only values
proposed in `D̄`. -/
theorem theorem1_corrected [Finite P] (M M' : SysModel P V W) (A : M.Alg) (A' : M'.Alg)
    (j : ℕ) (Dg : Fin j → Set P) (hA : M.SolvesKSA inOf decOf A (j + 1)) :
    let D := ⋃ i, Dg i
    let Dbar := Dᶜ
    let RDbar := {r | r ∈ MA inOf M A ∧ M.isolated D Dbar r}
    -- (B), with run-dependent values
    (∀ α ∈ RDbar, ∃ v : Fin j → V, Function.Injective v ∧
      ∃ β ∈ RDbar, DecD inOf decOf M Dg v β ∧ Indist (M := M) (M' := M) Dbar β α) →
    -- (C) for `A' = A|D̄`
    ¬ M'.SolvesConsensus inOf decOf Dbar A' →
    -- (D), strengthened
    (∀ ρ' ∈ M'.runs A', ∃ ρ ∈ RDbar, Indist Dbar ρ ρ' ∧
      ∀ p ∈ Dbar, M'.correct ρ' p → M.correct ρ p) →
    -- (E)
    (∀ ρ ∈ RDbar, ∀ p ∈ Dbar, ∀ u, M.dec decOf ρ p = some u → ∃ q ∈ Dbar, M.input inOf ρ q = u) →
    False := by
  intro D Dbar RDbar hB hC hD hE
  -- Fact 1: in every run of `R(D̄)` the processes of `D̄` agree
  have fact1 : ∀ α ∈ RDbar, ∀ p ∈ Dbar, ∀ q ∈ Dbar, ∀ u u',
      M.dec decOf α p = some u → M.dec decOf α q = some u' → u = u' := by
    intro α hα p hp q hq u u' hu hu'
    obtain ⟨v, hv, β, hβ, hβv, hind⟩ := hB α hα
    have hpβ : M.dec decOf β p = some u := by rw [SysModel.dec, hind p hp]; exact hu
    have hqβ : M.dec decOf β q = some u' := by rw [SysModel.dec, hind q hq]; exact hu'
    by_contra huu
    -- the values `v i` and `u`, `u'` are `j + 2` distinct decided values in `β`
    have hinj := hβ.1.2
    have hval : ∀ i, v i ≠ u ∧ v i ≠ u' := by
      intro i
      obtain ⟨⟨r, hr, hrv⟩, -⟩ := hβv i
      obtain ⟨a, ha, hau⟩ := hE β hβ p hp u hpβ
      obtain ⟨b, hb, hbu⟩ := hE β hβ q hq u' hqβ
      have hra : r ≠ a := fun h => ha (h ▸ hr)
      have hrb : r ≠ b := fun h => hb (h ▸ hr)
      exact ⟨fun h => hra (hinj (by rw [hrv, hau, h])), fun h => hrb (hinj (by rw [hrv, hbu, h]))⟩
    let W' : Fin (j + 2) → V := Fin.cons u (Fin.cons u' v)
    have hW' : Function.Injective W' := by
      refine Fin.cons_injective_iff.2 ⟨?_, Fin.cons_injective_iff.2 ⟨?_, hv⟩⟩
      · rintro ⟨i, hi⟩
        refine Fin.cases (fun h => huu (by simpa using h.symm)) (fun i h => ?_) i hi
        exact (hval i).1 (by simpa using h)
      · rintro ⟨i, hi⟩; exact (hval i).2 hi
    have hsub : Set.range W' ⊆ {w | ∃ p, M.dec decOf β p = some w} := by
      rintro _ ⟨i, rfl⟩
      refine Fin.cases ⟨p, hpβ⟩ (fun i => ?_) i
      refine Fin.cases ⟨q, hqβ⟩ (fun i => ?_) i
      obtain ⟨-, r, -, hr⟩ := hβv i
      exact ⟨r, hr⟩
    have hfin : {w | ∃ p, M.dec decOf β p = some w}.Finite := by
      refine ((Set.finite_range (fun p => M.dec decOf β p)).preimage
        (Option.some_injective V).injOn).subset ?_
      rintro w ⟨p, hp⟩; exact ⟨p, hp⟩
    have h1 := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_range_of_injective hW', Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    have h2 := (hA β hβ.1.1).1
    omega
  -- hence `A|D̄` solves consensus in `M'`
  apply hC
  intro ρ' hρ'
  obtain ⟨ρ, hρ, hind, hcorr⟩ := hD ρ' hρ'
  have hdec : ∀ p ∈ Dbar, M'.dec decOf ρ' p = M.dec decOf ρ p := by
    intro p hp; rw [SysModel.dec, SysModel.dec, hind p hp]
  refine ⟨?_, ?_, ?_⟩
  · intro p hp q hq u u' hu hu'
    rw [hdec p hp] at hu
    rw [hdec q hq] at hu'
    exact fact1 ρ hρ p hp q hq u u' hu hu'
  · intro p hp u hu
    rw [hdec p hp] at hu
    obtain ⟨q, hq, hqu⟩ := hE ρ hρ p hp u hu
    refine ⟨q, hq, ?_⟩
    rw [SysModel.input, ← hind q hq]
    exact hqu
  · intro p hp hc
    rw [hdec p hp]
    exact (hA ρ hρ.1.1).2.2 p (hcorr p hp hc)

end KSetAgreement.Abstract
