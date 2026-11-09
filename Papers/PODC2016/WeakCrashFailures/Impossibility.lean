import Papers.PODC2016.WeakCrashFailures.Failures
import Podc.Computability.Distributed.SWMR.Restrict
import Podc.Computability.Distributed.SWMR.FLP
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Interval.Finset.Nat

/-!
# Impossibility results for weak crash failures (Section 5)

G. Taubenfeld, *Computing in the presence of weak crash failures*, PODC 2016; full version
*Weak Failures: Definitions, Algorithms and Impossibility Results*, §5: Theorem 7, Corollaries 1
and 2.

Model: the asynchronous read/write SWMR model `Cslib.SWMR` (deterministic processes, atomic
single-writer registers, executions given by schedules). An algorithm *tolerates* a failure
pattern `adm : (ℕ → P) → Prop` (`WSolves A adm T`) if every finite execution satisfies the task
(safety) and, in every infinite execution whose schedule satisfies `adm`, every correct process
decides (termination).

* `kSetConsensus k`: validity (a decided value is the input of some process) and k-agreement (at
  most `k` distinct decided values).
* `WeakInitAdmissible m ℓ k`: "k crash m-failures and ℓ initial failures".
* `WeakAdmissible m f` (from `Failures.lean`): "f crash m-failures".
* `KSetImpossible K Vr V k`: the classical impossibility of k-set consensus tolerating `k` crash
  failures with more than `k` processes (Borowsky–Gafni, Herlihy–Shavit, Saks–Zaharoglou). It is
  **not** formalized here and appears as a hypothesis of Theorem 7 and Corollary 1. For `k = 1`
  it is FLP (Loui–Abu-Amara), which *is* formalized (`Alg.not_solves_binConsensus`), so
  Corollary 2 is unconditional (`kSetImpossible_one`).

## Main statements

* `theorem7`: Theorem 7 (with the hypothesis `KSetImpossible`).
* `corollary1`: Corollary 1, under the weaker bound `n > ℓ + k` (the paper assumes
  `n > 2ℓ + k`).
* `corollary2`, `corollary2_paper`, `no_consensus_two_failures`: Corollary 2 (unconditional), for
  `n > ℓ + 1`, and in the paper's form (`2ℓ < n`) under the extra assumption `n ≥ 2`.
* `corollary2_false_n1`: for `n = 1, ℓ = 0` Corollary 2 as stated is false: a single process
  deciding its own input solves consensus tolerating one crash 1-failure.
* `weakAdmissible_iff_of_card_two`: for `n = 2`, two crash 1-failures are the same failure
  pattern as one crash 1-failure (so the bound `n > 2` of the introduction is needed).
-/

namespace Podc.WeakCrashFailures

open Cslib.SWMR

section Defs

variable {P K : Type} {Vr : K → Type} {In Out V : Type}

/-- The k-set consensus task: every decided value is the input of some process (validity) and at
most `k` distinct values are decided (k-agreement). `kSetConsensus 1` is consensus. -/
def kSetConsensus (k : ℕ) : Task P V V := fun x y =>
  (∀ p v, y p = some v → ∃ q, x q = v) ∧ {v | ∃ p, y p = some v}.encard ≤ k

variable [DecidableEq P] [DecidableEq K]

/-- `A` solves the task `T` tolerating the failure pattern `adm`: every finite execution
satisfies `T` (safety), and in every infinite execution whose schedule satisfies `adm`, every
correct process eventually decides (termination). -/
def WSolves (A : Alg P K Vr In Out) (adm : (ℕ → P) → Prop) (T : Task P In Out) : Prop :=
  (∀ (x : P → In) (σ : List P), T x (A.run (A.initCfg x) σ).out) ∧
  ∀ (x : P → In) (σ : ℕ → P), adm σ → ∀ p, InfOften σ p →
    ∃ T, ((A.run (A.initCfg x) (pre σ T)).out p).isSome

/-- Tolerating more failure patterns is harder. -/
lemma WSolves.mono {A : Alg P K Vr In Out} {adm adm' : (ℕ → P) → Prop} {T : Task P In Out}
    (h : WSolves A adm' T) (hadm : ∀ σ, adm σ → adm' σ) : WSolves A adm T :=
  ⟨h.1, fun x σ hσ => h.2 x σ (hadm σ hσ)⟩

/-- "k crash m-failures and ℓ initial failures": every faulty process either fails initially
(at most `ℓ` of them) or is an m-failure (at most `k` of them). -/
def WeakInitAdmissible (m ℓ k : ℕ) (σ : ℕ → P) : Prop :=
  ∃ I W : Finset P, Faulty σ ⊆ ↑I ∪ ↑W ∧ I.card ≤ ℓ ∧ (∀ p ∈ I, InitialFailure σ p) ∧
    W.card ≤ k ∧ ∀ p ∈ W, WeakFailure m σ p

/-- The classical impossibility of k-set consensus (Borowsky–Gafni, Herlihy–Shavit,
Saks–Zaharoglou; [4, 12, 18] of the paper), for register banks `K`/`Vr` and values `V`: no
algorithm for more than `k` processes solves k-set consensus tolerating `k` crash failures.
Used as a hypothesis (not formalized, except for `k = 1`: `kSetImpossible_one`). It is the classical
theorem when `V` has more than `k` values; for `|V| ≤ k` it is false ("decide your own input"). -/
def KSetImpossible (K : Type) [DecidableEq K] (Vr : K → Type) (V : Type) (k : ℕ) : Prop :=
  ∀ (Q : Type) [Fintype Q] [DecidableEq Q], k < Fintype.card Q →
    ∀ A : Alg Q K Vr V V, ¬ A.Solves k (kSetConsensus k)

end Defs

/-! ### Sanity checks on the failure models -/

section Sanity

variable {P K : Type} {Vr : K → Type} {In Out : Type} [Fintype P] [DecidableEq P] [DecidableEq K]

/-- With `m ≥ n`, "f crash m-failures" are just "at most `f` crash failures". -/
lemma weakAdmissible_iff_of_card_le {m : ℕ} (hm : Fintype.card P ≤ m) (f : ℕ) (σ : ℕ → P) :
    WeakAdmissible m f σ ↔ (Faulty σ).ncard ≤ f :=
  ⟨fun h => h.1, fun h => ⟨h, fun p hp => (weakFailure_iff_faulty hm σ p).2 hp⟩⟩

/-- With `m ≥ n`, tolerating `f` crash m-failures is the usual `f`-resilient solvability. -/
lemma wSolves_weakAdmissible_iff_solves {A : Alg P K Vr In Out} {T : Task P In Out} {m : ℕ}
    (hm : Fintype.card P ≤ m) (f : ℕ) :
    WSolves A (WeakAdmissible m f) T ↔ A.Solves f T := by
  unfold WSolves Alg.Solves
  simp only [weakAdmissible_iff_of_card_le hm]

/-- "k crash m-failures and ℓ initial failures" is a special case of "ℓ + k crash m-failures":
an initial failure is an m-failure for every `m`. -/
lemma WeakInitAdmissible.weakAdmissible {m ℓ k : ℕ} {σ : ℕ → P}
    (h : WeakInitAdmissible m ℓ k σ) : WeakAdmissible m (ℓ + k) σ := by
  obtain ⟨I, W, hF, hI, hIi, hW, hWw⟩ := h
  refine ⟨?_, fun p hp => ?_⟩
  · refine le_trans (Set.ncard_le_ncard hF (Set.toFinite _)) ?_
    refine le_trans (Set.ncard_union_le _ _) ?_
    rw [Set.ncard_coe_finset, Set.ncard_coe_finset]
    omega
  · rcases hF hp with hp | hp
    · exact (hIi p hp).weakFailure m
    · exact hWw p hp

omit [DecidableEq P] [DecidableEq K] in
/-- An infinite schedule over a nonempty finite set of processes has a correct process. -/
lemma exists_infOften [Nonempty P] (σ : ℕ → P) : ∃ p, InfOften σ p := by
  obtain ⟨p, hp⟩ := Finite.exists_infinite_fiber σ
  refine ⟨p, fun N => ?_⟩
  have hinf : (σ ⁻¹' {p}).Infinite := Set.infinite_coe_iff.1 hp
  obtain ⟨m, hm, hmN⟩ := hinf.exists_gt N
  exact ⟨m, le_of_lt hmN, by simpa using hm⟩

omit [DecidableEq P] [DecidableEq K] in
/-- Not every process is faulty: at most `n - 1` faulty processes. -/
lemma ncard_faulty_le (σ : ℕ → P) : (Faulty σ).ncard ≤ Fintype.card P - 1 := by
  rcases isEmpty_or_nonempty P with hP | hP
  · simp [Set.eq_empty_of_isEmpty]
  obtain ⟨p, hp⟩ := exists_infOften σ
  have hlt : (Faulty σ).ncard < (Set.univ : Set P).ncard :=
    Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.2 ⟨Set.subset_univ _,
      fun h => (h ▸ Set.mem_univ p : p ∈ Faulty σ) hp⟩) (Set.toFinite _)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hlt
  omega

/-- Allowing more than `n - 1` failures changes nothing. -/
lemma weakAdmissible_iff_of_le {m f : ℕ} (hf : Fintype.card P - 1 ≤ f) (σ : ℕ → P) :
    WeakAdmissible m f σ ↔ WeakAdmissible m (Fintype.card P - 1) σ :=
  ⟨fun h => ⟨ncard_faulty_le σ, h.2⟩, fun h => ⟨le_trans h.1 hf, h.2⟩⟩

/-- For `n = 2`, "two crash 1-failures" is the same failure pattern as "one crash 1-failure"
(the two processes cannot both be faulty). Hence, by Theorem 1 (one crash (n−1)-failure is
tolerable), the bound `n > 2` in "no consensus algorithm tolerates two crash (n−1)-failures"
(§1.3, after Corollary 2) is necessary. -/
lemma weakAdmissible_iff_of_card_two (hP : Fintype.card P = 2) (σ : ℕ → P) :
    WeakAdmissible 1 2 σ ↔ WeakAdmissible 1 1 σ := by
  have := weakAdmissible_iff_of_le (m := 1) (f := 2) (by omega) σ
  rw [hP] at this
  exact this

end Sanity

/-! ### Restriction to a subset of the processes -/

section Restrict

variable {P K : Type} {Vr : K → Type} {In Out Out' : Type} [DecidableEq P] [DecidableEq K]

/-- Termination transfers to the restriction `A.restrictMap G f` along any schedule of `G` whose
lift to `P` is a tolerated failure pattern. -/
theorem WSolves.restrictMap_termination {A : Alg P K Vr In Out} {adm : (ℕ → P) → Prop}
    {T : Task P In Out} {G : Finset P} {f : Out → Out'} (hA : WSolves A adm T)
    (xG : G → In) (w : P → In) (σ : ℕ → G) (hσ : adm (fun m => (σ m).1)) (p : G)
    (hp : InfOften σ p) :
    ∃ T, (((A.restrictMap G f).run ((A.restrictMap G f).initCfg xG) (pre σ T)).out p).isSome := by
  have hpA : InfOften (fun m => (σ m).1) p.1 := by
    intro N
    obtain ⟨m, hm, hmp⟩ := hp N
    exact ⟨m, hm, by simp [hmp]⟩
  obtain ⟨T, hT⟩ := hA.2 (liftIn xG w) _ hσ p.1 hpA
  refine ⟨T, ?_⟩
  have := ((Alg.run_restrictMap (A := A) (f := f) xG w (pre σ T)).1 p).2.2
  rw [this, ← pre_comp_val]
  simpa using hT

end Restrict

/-! ### Theorem 7 and Corollary 1 -/

section Theorem7

variable {P K : Type} {Vr : K → Type} {V : Type} [Fintype P] [DecidableEq P] [DecidableEq K]

/-- The faulty processes of the lift of a schedule of `G`: those outside `G` and the faulty
processes of `G`. -/
lemma faulty_lift_subset {G : Finset P} (σ : ℕ → G) :
    Faulty (fun m => (σ m).1) ⊆ (↑Gᶜ : Set P) ∪ Subtype.val '' Faulty σ := by
  intro q hq
  by_cases hqG : q ∈ G
  · right
    refine ⟨⟨q, hqG⟩, fun hinf => hq ?_, rfl⟩
    intro N
    obtain ⟨m, hm, hmq⟩ := hinf N
    exact ⟨m, hm, by simp [hmq]⟩
  · left; simpa using hqG

omit [Fintype P] in
/-- In the lift of a schedule of `G`, the point contention never exceeds `|G|`. -/
lemma contention_lift_le {G : Finset P} (σ : ℕ → G) (t : ℕ) :
    contention (fun m => (σ m).1) t ≤ G.card := by
  apply Finset.card_le_card
  intro q hq
  obtain ⟨s, -, rfl⟩ := mem_started.1 hq
  exact (σ s).2

/-- The lift of a schedule of `G` with at most `k` faulty processes, where `|G| = n - ℓ`, has
`ℓ` initial failures (the processes outside `G`) and at most `k` crash `(n - ℓ)`-failures. -/
lemma weakInitAdmissible_lift {ℓ k : ℕ} {G : Finset P} (hG : G.card = Fintype.card P - ℓ)
    (hℓ : ℓ ≤ Fintype.card P) (σ : ℕ → G) (hσ : (Faulty σ).ncard ≤ k) :
    WeakInitAdmissible (Fintype.card P - ℓ) ℓ k (fun m => (σ m).1) := by
  classical
  set W : Finset P := (Set.toFinite (Subtype.val '' Faulty σ)).toFinset
  refine ⟨Gᶜ, W, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    rcases faulty_lift_subset σ hq with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa [W] using h)
  · rw [Finset.card_compl]; omega
  · intro q hq s _ hs
    exact (Finset.mem_compl.1 hq) (hs ▸ (σ s).2)
  · rw [← Set.ncard_eq_toFinset_card, Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hσ
  · intro q hq
    have hqF : q ∈ Faulty (fun m => (σ m).1) := by
      obtain ⟨r, hr, rfl⟩ := (Set.Finite.mem_toFinset _).1 hq
      intro hinf
      apply hr
      intro N
      obtain ⟨m, hm, hmq⟩ := hinf N
      exact ⟨m, hm, Subtype.ext hmq⟩
    obtain ⟨t, ht⟩ := exists_stoppedFrom_of_faulty hqF
    exact ⟨t, ht, hG ▸ contention_lift_le σ t⟩

/-- **Theorem 7** of [Taubenfeld, PODC 2016 / full version §5]: for every `ℓ ≥ 0`, `k` and
`n > ℓ + k`, there is no k-set consensus algorithm for `n` processes using registers that
tolerates `k` crash `(n − ℓ)`-failures and `ℓ` initial failures — assuming the classical
impossibility of k-set consensus tolerating `k` crash failures (`KSetImpossible`).
(The paper's `k ≥ 1` is not needed.) -/
theorem theorem7 {ℓ k : ℕ} (hn : ℓ + k < Fintype.card P) (hKS : KSetImpossible K Vr V k)
    (A : Alg P K Vr V V) :
    ¬ WSolves A (WeakInitAdmissible (Fintype.card P - ℓ) ℓ k) (kSetConsensus k) := by
  intro hA
  obtain ⟨G, -, hG⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset P))
    (n := Fintype.card P - ℓ) (by simp)
  have hGpos : 0 < G.card := by omega
  obtain ⟨g₀, hg₀⟩ := Finset.card_pos.1 hGpos
  set B := A.restrictMap G id
  apply hKS G (by simp only [Fintype.card_coe]; omega) B
  refine ⟨fun xG τ => ?_, fun xG σ hσ p hp => ?_⟩
  · -- safety: an execution of `B` is an execution of `A` where `Gᶜ` takes no step
    set w : P → V := fun _ => xG ⟨g₀, hg₀⟩
    have hrel := (Alg.run_restrictMap (A := A) (f := id) xG w τ).1
    obtain ⟨hval, hagr⟩ := hA.1 (liftIn xG w) (τ.map Subtype.val)
    have hout : ∀ (p : G) v, (B.run (B.initCfg xG) τ).out p = some v →
        (A.run (A.initCfg (liftIn xG w)) (τ.map Subtype.val)).out p.1 = some v := by
      intro p v h
      rw [(hrel p).2.2] at h
      simpa using h
    refine ⟨fun p v hpv => ?_, ?_⟩
    · obtain ⟨q, hq⟩ := hval _ v (hout p v hpv)
      by_cases hqG : q ∈ G
      · exact ⟨⟨q, hqG⟩, by simpa [liftIn, hqG] using hq⟩
      · exact ⟨⟨g₀, hg₀⟩, by simpa [liftIn, hqG, w] using hq⟩
    · refine le_trans (Set.encard_le_encard ?_) hagr
      rintro v ⟨p, hp⟩
      exact ⟨p.1, hout p v hp⟩
  · -- termination: the lifted schedule has `ℓ` initial failures and `≤ k` (n−ℓ)-failures
    exact hA.restrictMap_termination xG (fun _ => xG ⟨g₀, hg₀⟩) σ
      (weakInitAdmissible_lift hG (by omega) σ hσ) p hp

/-- **Corollary 1** of [Taubenfeld, PODC 2016 / full version §5]: for every `ℓ ≥ 0`, `k` and
`n > ℓ + k`, there is no k-set consensus algorithm for `n` processes using registers that
tolerates `ℓ + k` crash `(n − ℓ)`-failures (assuming `KSetImpossible`). The paper assumes
`n > 2ℓ + k`; `n > ℓ + k` suffices. -/
theorem corollary1 {ℓ k : ℕ} (hn : ℓ + k < Fintype.card P) (hKS : KSetImpossible K Vr V k)
    (A : Alg P K Vr V V) :
    ¬ WSolves A (WeakAdmissible (Fintype.card P - ℓ) (ℓ + k)) (kSetConsensus k) :=
  fun hA => theorem7 hn hKS A (hA.mono fun _ h => h.weakAdmissible)

end Theorem7

/-! ### Corollary 2: consensus, via FLP -/

section Relabel

variable {P K : Type} {Vr : K → Type} {In In' Out Out' : Type}

/-- Relabel the inputs (by `g`) and the decisions (by `f`) of an algorithm. -/
@[reducible] def relabel (A : Alg P K Vr In Out) (g : In' → In) (f : Out → Out') : Alg P K Vr In' Out' where
  S := A.S
  v₀ := A.v₀
  init p x := A.init p (g x)
  next p s :=
    match A.next p s with
    | .write i v s' => .write i v s'
    | .read q i k => .read q i k
    | .decide y s' => .decide (f y) s'

variable [DecidableEq P] [DecidableEq K] {A : Alg P K Vr In Out} {g : In' → In} {f : Out → Out'}

/-- The simulation relation for `relabel`. -/
def RelabelRel (A : Alg P K Vr In Out) (g : In' → In) (f : Out → Out')
    (D : Config (relabel A g f)) (C : Config A) : Prop :=
  (∀ p, D.loc p = C.loc p) ∧ D.mem = C.mem ∧ ∀ p, D.out p = (C.out p).map f

lemma RelabelRel.step {D : Config (relabel A g f)} {C : Config A} (h : RelabelRel A g f D C)
    (p : P) : RelabelRel A g f ((relabel A g f).step p D) (A.step p C) := by
  obtain ⟨hl, hm, ho⟩ := h
  rcases hA : A.next p (C.loc p) with ⟨i, v, s'⟩ | ⟨q, i, k⟩ | ⟨y, s'⟩
  · have hB : (relabel A g f).next p (D.loc p) = .write i v s' := by
      simp only [relabel, hl, hA]
    rw [Alg.step_of_write hA, Alg.step_of_write hB]
    refine ⟨fun r => ?_, by simp [hm], ho⟩
    by_cases hr : r = p
    · subst hr; simp
    · simp [Function.update_of_ne hr, hl r]
  · have hB : (relabel A g f).next p (D.loc p) = .read q i k := by
      simp only [relabel, hl, hA]
    rw [Alg.step_of_read hA, Alg.step_of_read hB]
    refine ⟨fun r => ?_, hm, ho⟩
    by_cases hr : r = p
    · subst hr; simp [hm]
    · simp [Function.update_of_ne hr, hl r]
  · have hB : (relabel A g f).next p (D.loc p) = .decide (f y) s' := by
      simp only [relabel, hl, hA]
    rw [Alg.step_of_decide hA, Alg.step_of_decide hB]
    refine ⟨fun r => ?_, hm, fun r => ?_⟩
    · by_cases hr : r = p
      · subst hr; simp
      · simp [Function.update_of_ne hr, hl r]
    · by_cases hr : r = p
      · subst hr; cases hc : C.out r <;> simp [ho, hc]
      · simp [Function.update_of_ne hr, ho r]

lemma RelabelRel.run {D : Config (relabel A g f)} {C : Config A} (h : RelabelRel A g f D C)
    (τ : List P) : RelabelRel A g f ((relabel A g f).run D τ) (A.run C τ) := by
  induction τ generalizing D C with
  | nil => exact h
  | cons p τ ih => exact ih (h.step p)

/-- An execution of the relabelled algorithm is an execution of `A` from the relabelled inputs
(with the same schedule); the decisions are mapped by `f`. -/
lemma out_run_relabel (x : P → In') (τ : List P) (p : P) :
    ((relabel A g f).run ((relabel A g f).initCfg x) τ).out p =
      ((A.run (A.initCfg (g ∘ x)) τ).out p).map f :=
  (RelabelRel.run (A := A) (g := g) (f := f) (D := (relabel A g f).initCfg x)
    (C := A.initCfg (g ∘ x)) ⟨fun _ => rfl, rfl, fun _ => rfl⟩ τ).2.2 p

end Relabel

section Corollary2

variable {P K : Type} {Vr : K → Type} {V : Type} [DecidableEq K]

/-- Consensus (with validity) is at least as hard as binary consensus with weak validity:
relabel the inputs `false, true` as two distinct values `v₀, v₁` and map a decision `y` back to
`y = v₁`. -/
lemma Alg.Solves.binConsensus_relabel {Q : Type} [DecidableEq Q] [DecidableEq V] {v₀ v₁ : V} (hv : v₀ ≠ v₁)
    {t : ℕ} {A : Alg Q K Vr V V} (hA : A.Solves t (kSetConsensus 1)) :
    (relabel A (fun b : Bool => if b then v₁ else v₀) (fun y => decide (y = v₁))).Solves t
      binConsensus := by
  refine ⟨fun x τ => ?_, fun x σ hσ p hp => ?_⟩
  · obtain ⟨hval, hagr⟩ := hA.1 ((fun b : Bool => if b then v₁ else v₀) ∘ x) τ
    rw [Nat.cast_one, Set.encard_le_one_iff] at hagr
    refine ⟨fun b hb p c hc => ?_, fun p q c c' hc hc' => ?_⟩
    · rw [out_run_relabel, Option.map_eq_some_iff] at hc
      obtain ⟨y, hy, rfl⟩ := hc
      obtain ⟨q, hq⟩ := hval p y hy
      rw [← hq]
      cases b <;> simp [hb q, hv]
    · rw [out_run_relabel, Option.map_eq_some_iff] at hc hc'
      obtain ⟨y, hy, rfl⟩ := hc
      obtain ⟨y', hy', rfl⟩ := hc'
      rw [hagr y y' ⟨p, hy⟩ ⟨q, hy'⟩]
  · obtain ⟨T, hT⟩ := hA.2 _ σ hσ p hp
    exact ⟨T, by rw [out_run_relabel]; simpa using hT⟩

/-- `KSetImpossible` for `k = 1` (consensus) holds: it follows from FLP / Loui–Abu-Amara
(`Alg.not_solves_binConsensus`), for any set `V` of at least two values. -/
theorem kSetImpossible_one [Nontrivial V] : KSetImpossible K Vr V 1 := by
  classical
  intro Q _ _ hQ A hA
  obtain ⟨v₀, v₁, hv⟩ := exists_pair_ne V
  exact Alg.not_solves_binConsensus (P := Q) (by omega) _ (Alg.Solves.binConsensus_relabel hv hA)

variable [Fintype P] [DecidableEq P]

/-- **Corollary 2** of [Taubenfeld, PODC 2016 / full version §5], in the strengthened form
`n > ℓ + 1`: there is no consensus algorithm for `n` processes using registers that tolerates
`ℓ + 1` crash `(n − ℓ)`-failures. Unconditional (via FLP). -/
theorem corollary2 [Nontrivial V] {ℓ : ℕ} (hn : ℓ + 1 < Fintype.card P) (A : Alg P K Vr V V) :
    ¬ WSolves A (WeakAdmissible (Fintype.card P - ℓ) (ℓ + 1)) (kSetConsensus 1) :=
  corollary1 hn kSetImpossible_one A

/-- **Corollary 2** of [Taubenfeld, PODC 2016 / full version §5] in the paper's form
("for every `0 ≤ ℓ < n/2`"), with the missing assumption `n ≥ 2` (see `corollary2_false_n1`). -/
theorem corollary2_paper [Nontrivial V] {ℓ : ℕ} (hn2 : 2 ≤ Fintype.card P)
    (hℓ : 2 * ℓ < Fintype.card P) (A : Alg P K Vr V V) :
    ¬ WSolves A (WeakAdmissible (Fintype.card P - ℓ) (ℓ + 1)) (kSetConsensus 1) :=
  corollary2 (by omega) A

/-- [Taubenfeld, PODC 2016], §1.3 and after Corollary 2: for `n > 2` there is no consensus
algorithm for `n` processes using registers that tolerates two crash `(n − 1)`-failures. -/
theorem no_consensus_two_failures [Nontrivial V] (hn : 2 < Fintype.card P) (A : Alg P K Vr V V) :
    ¬ WSolves A (WeakAdmissible (Fintype.card P - 1) 2) (kSetConsensus 1) :=
  corollary2 (ℓ := 1) (by omega) A

end Corollary2

/-! ### The edge case `n = 1` -/

section SelfDecide

variable {P V : Type} [DecidableEq P]

/-- Every process decides its own input (one register bank with a single trivial register). -/
@[reducible] def selfDecide (P V : Type) : Alg P Unit (fun _ => Unit) V V where
  S := V
  v₀ _ := ()
  init _ x := x
  next _ v := .decide v v

lemma selfDecide_run_inv (x : P → V) (τ : List P) :
    (∀ p, ((selfDecide P V).run ((selfDecide P V).initCfg x) τ).loc p = x p) ∧
    ∀ p, ((selfDecide P V).run ((selfDecide P V).initCfg x) τ).out p = none ∨
      ((selfDecide P V).run ((selfDecide P V).initCfg x) τ).out p = some (x p) := by
  induction τ using List.reverseRecOn with
  | nil => exact ⟨fun _ => rfl, fun _ => Or.inl rfl⟩
  | append_singleton τ q ih =>
    obtain ⟨hl, ho⟩ := ih
    rw [Alg.run_concat]
    have hq : (selfDecide P V).next q
        (((selfDecide P V).run ((selfDecide P V).initCfg x) τ).loc q) = .decide (x q) (x q) := by
      rw [hl q]
    rw [Alg.step_of_decide hq]
    refine ⟨fun p => ?_, fun p => ?_⟩
    · by_cases hp : p = q
      · subst hp; simp
      · simp [Function.update_of_ne hp, hl p]
    · by_cases hp : p = q
      · subst hp; rcases ho p with h | h <;> simp [h]
      · simp only [Function.update_of_ne hp]; exact ho p

/-- With a single process (or none), `selfDecide` solves consensus and tolerates every failure
pattern (in particular `ℓ + 1 = 1` crash `(n − ℓ) = 1`-failures). -/
theorem selfDecide_wSolves [Subsingleton P] (adm : (ℕ → P) → Prop) :
    WSolves (selfDecide P V) adm (kSetConsensus 1) := by
  refine ⟨fun x τ => ⟨fun p v hv => ⟨p, ?_⟩, ?_⟩, fun x σ _ p hp => ?_⟩
  · rcases (selfDecide_run_inv x τ).2 p with h | h <;> rw [h] at hv
    · simp at hv
    · exact Option.some_injective _ hv
  · rw [Nat.cast_one, Set.encard_le_one_iff]
    rintro a b ⟨p, hp⟩ ⟨q, hq⟩
    rw [Subsingleton.elim q p] at hq
    rw [hp] at hq
    exact Option.some_injective _ hq
  · obtain ⟨m, -, hm⟩ := hp 0
    refine ⟨m + 1, ?_⟩
    rw [pre_succ, Alg.run_concat, hm]
    have hq : (selfDecide P V).next p
        (((selfDecide P V).run ((selfDecide P V).initCfg x) (pre σ m)).loc p) =
          .decide (x p) (x p) := by
      rw [(selfDecide_run_inv x _).1 p]
    rw [Alg.step_of_decide hq]
    simp

/-- Corollary 2 as stated in the paper ("for every `0 ≤ ℓ < n/2`") is false for `n = 1`,
`ℓ = 0`: with a single process (`P = Unit`) and any values `V`, the algorithm "decide your own
input" is a consensus algorithm tolerating `ℓ + 1 = 1` crash `(n − ℓ) = 1`-failure. -/
theorem corollary2_false_n1 (V : Type) :
    2 * 0 < Fintype.card Unit ∧
      WSolves (selfDecide Unit V) (WeakAdmissible (Fintype.card Unit - 0) (0 + 1))
        (kSetConsensus 1) :=
  ⟨by simp, selfDecide_wSolves _⟩

end SelfDecide

end Podc.WeakCrashFailures
