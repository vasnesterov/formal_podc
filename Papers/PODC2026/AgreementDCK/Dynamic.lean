import Cslib.Computability.Distributed.Knowledge.Basic
import Mathlib

/-!
# Dynamic knowledge and dynamic common knowledge among the nonfaulty processes

Definitions 1.3 and 1.4 of Or David and Yoram Moses, *Brief Announcement: What is Agreement About
if not Common Knowledge?*, PODC 2026, over the interpreted-system semantics of
`Cslib.Computability.Distributed.Knowledge.Basic`.

* `System.DK S i ψ φ` — `K_i^N@ψ (φ)`: the run fact `◇ψ ∧ □(ψ → K_i^N φ)` (Definition 1.3);
* `System.EN S ψ φ` — `E^N@ψ (φ)`: `K_i^N@ψᵢ (φ)` for every `i ∈ N(r)` (Definition 1.4);
* `System.EIter S ψ φ m` — `E^{m+1}^N@ψ (φ)` (the index is shifted by one: `EIter 0 = E^N@ψ`);
* `System.CN S ψ φ` — `C^N@ψ (φ)`: `E^m^N@ψ (φ)` for all `m ≥ 1` (Definition 1.4).

A *local profile* `ψ : ι → Fact R` assigns an `i`-local fact to every process (`IsLocalProfile`).
All dynamic states of knowledge are run facts (`R → Prop`); when they are nested inside another
operator they are lifted to time-independent facts with `RunFact.lift`.

Besides the definitions, this file proves the standard properties of `C^N@ψ` that the paper uses
implicitly: monotonicity, the *fixed-point* property `C φ ↔ E(φ ∧ C φ)` (`CN_iff_EN`), the
*induction rule* "`⊨ θ → E θ` implies `⊨ θ → C θ`" (`CN_of_EN_valid`), and the remark of the
paper that every nonfaulty process eventually knows that a dynamic common knowledge holds
(`CN.eventually_KN`).
-/

namespace Cslib.Knowledge

open RunFact

namespace System

variable {ι R : Type*} {L : ι → Type*} (S : System ι R L)

/-- A local profile `𝛙 = (ψ₁, …, ψₙ)`: `ψᵢ` is `i`-local for every process `i`. -/
def IsLocalProfile (ψ : ι → Fact R) : Prop := ∀ i, S.IsLocal i (ψ i)

/-- **Definition 1.3 (Dynamic knowledge).** `r ⊨ K_i^N@ψ (φ)` iff `r ⊨ ◇ψ ∧ □(ψ → K_i^N φ)`:
the event `ψ` happens at some time of `r`, and whenever it holds, `i` has nonfaulty knowledge of
`φ`. (The paper requires `ψ` to be `i`-local; the definition makes sense for any fact.) -/
def DK (i : ι) (ψ φ : Fact R) (r : R) : Prop :=
  (∃ t, ψ r t) ∧ ∀ t, ψ r t → S.KN i φ r t

/-- **Definition 1.4 (dynamic everyone knows).** `r ⊨ E^N@𝛙 (φ)` iff `r ⊨ K_i^N@ψᵢ (φ)` for every
nonfaulty `i ∈ N(r)`. -/
def EN (ψ : ι → Fact R) (φ : Fact R) (r : R) : Prop :=
  ∀ i ∈ S.nf r, S.DK i (ψ i) φ r

/-- Iterated dynamic everyone knows: `EIter ψ φ m = E^N@𝛙 (E^N@𝛙 (⋯ (φ)))` with `m + 1` nested
occurrences of `E^N@𝛙`, i.e. the paper's `E^{m+1}^N@𝛙 (φ)`. -/
def EIter (ψ : ι → Fact R) (φ : Fact R) : ℕ → R → Prop
  | 0 => S.EN ψ φ
  | m + 1 => S.EN ψ (lift (EIter ψ φ m))

/-- **Definition 1.4 (dynamic common knowledge).** `r ⊨ C^N@𝛙 (φ)` iff `r ⊨ E^m^N@𝛙 (φ)` for all
`m ≥ 1`. -/
def CN (ψ : ι → Fact R) (φ : Fact R) (r : R) : Prop :=
  ∀ m, S.EIter ψ φ m r

variable {S}

@[simp] lemma EIter_zero (ψ : ι → Fact R) (φ : Fact R) : S.EIter ψ φ 0 = S.EN ψ φ := rfl

@[simp] lemma EIter_succ (ψ : ι → Fact R) (φ : Fact R) (m : ℕ) :
    S.EIter ψ φ (m + 1) = S.EN ψ (lift (S.EIter ψ φ m)) := rfl

/-! ### Monotonicity -/

lemma DK.mono {i : ι} {ψ φ φ' : Fact R} {r : R} (h : S.DK i ψ φ r)
    (hφ : ∀ r' t', i ∈ S.nf r' → φ r' t' → φ' r' t') : S.DK i ψ φ' r :=
  ⟨h.1, fun t ht => (h.2 t ht).mono hφ⟩

/-- `E^N@𝛙` is monotone; it is enough that the implication holds in runs where some process is
nonfaulty. -/
lemma EN.mono {ψ : ι → Fact R} {φ φ' : Fact R} {r : R} (h : S.EN ψ φ r)
    (hφ : ∀ r' t', (S.nf r').Nonempty → φ r' t' → φ' r' t') : S.EN ψ φ' r :=
  fun i hi => (h i hi).mono fun r' t' hi' => hφ r' t' ⟨i, hi'⟩

lemma EIter.mono {ψ : ι → Fact R} {φ φ' : Fact R}
    (hφ : ∀ r' t', (S.nf r').Nonempty → φ r' t' → φ' r' t') :
    ∀ m r, S.EIter ψ φ m r → S.EIter ψ φ' m r
  | 0, _, h => EN.mono h hφ
  | m + 1, _, h => EN.mono h fun r' _ _ h' => EIter.mono hφ m r' h'

lemma CN.mono {ψ : ι → Fact R} {φ φ' : Fact R} {r : R} (h : S.CN ψ φ r)
    (hφ : ∀ r' t', (S.nf r').Nonempty → φ r' t' → φ' r' t') : S.CN ψ φ' r :=
  fun m => EIter.mono hφ m r (h m)

/-- In a run without nonfaulty processes every dynamic state of knowledge holds vacuously. -/
lemma CN_of_nf_empty {ψ : ι → Fact R} {φ : Fact R} {r : R} (h : S.nf r = ∅) : S.CN ψ φ r := by
  intro m
  cases m <;> intro i hi <;> simp [h] at hi

/-! ### Fixed point and induction rule -/

lemma CN.EN {ψ : ι → Fact R} {φ : Fact R} {r : R} (h : S.CN ψ φ r) : S.EN ψ φ r := h 0

/-- **Fixed-point property**: `C^N@𝛙 (φ) ↔ E^N@𝛙 (φ ∧ C^N@𝛙 (φ))`. -/
theorem CN_iff_EN {ψ : ι → Fact R} {φ : Fact R} {r : R} :
    S.CN ψ φ r ↔ S.EN ψ (fun r t => φ r t ∧ S.CN ψ φ r) r := by
  constructor
  · intro h i hi
    refine ⟨(h 0 i hi).1, fun t ht => ?_⟩
    refine KN.and ((h 0 i hi).2 t ht) ?_
    exact KN.forall hi fun m => (h (m + 1) i hi).2 t ht
  · intro h m
    cases m with
    | zero => exact EN.mono h fun _ _ _ h' => h'.1
    | succ m => exact EN.mono h fun _ _ _ h' => h'.2 m

/-- **Induction rule**: if `⊨ θ → E^N@𝛙 (φ ∧ θ)` for a run fact `θ`, then
`⊨ θ → C^N@𝛙 (φ)`. -/
theorem CN_of_EN_valid {ψ : ι → Fact R} {φ : Fact R} {θ : R → Prop}
    (h : ∀ r, θ r → S.EN ψ (fun r t => φ r t ∧ θ r) r) : ∀ r, θ r → S.CN ψ φ r := by
  have key : ∀ m r, θ r → S.EIter ψ φ m r ∧ S.EN ψ (lift θ) r := by
    intro m
    induction m with
    | zero => exact fun r hr => ⟨EN.mono (h r hr) fun _ _ _ h' => h'.1,
        EN.mono (h r hr) fun _ _ _ h' => h'.2⟩
    | succ m ih => exact fun r hr => ⟨EN.mono (ih r hr).2 fun r' _ _ h' => (ih r' h').1,
        (ih r hr).2⟩
  exact fun r hr m => (key m r hr).1

/-- Special case of the induction rule: `⊨ θ → E^N@𝛙 (θ)` implies `⊨ θ → C^N@𝛙 (θ)`. Hence in
Theorem 1.7 the hypothesis `⊨ θ_v → C^N@𝛙(v) (θ_v)` is equivalent to
`⊨ θ_v → E^N@𝛙(v) (θ_v)`. -/
theorem CN_self_of_EN_self {ψ : ι → Fact R} {θ : R → Prop}
    (h : ∀ r, θ r → S.EN ψ (lift θ) r) : ∀ r, θ r → S.CN ψ (lift θ) r :=
  CN_of_EN_valid fun r hr => EN.mono (h r hr) fun _ _ _ h' => ⟨h', h'⟩

/-- "If a fact is dynamic common knowledge, then every correct process will, at least at one
point, know that it is" (David–Moses, after Definition 1.4): at the times when `ψᵢ` holds. -/
theorem CN.KN_CN {ψ : ι → Fact R} {φ : Fact R} {r : R} (h : S.CN ψ φ r) {i : ι}
    (hi : i ∈ S.nf r) : ∀ t, ψ i r t → S.KN i (lift (S.CN ψ φ)) r t :=
  fun t ht => ((CN_iff_EN.1 h i hi).2 t ht).mono fun _ _ _ h' => h'.2

theorem CN.eventually_KN {ψ : ι → Fact R} {φ : Fact R} {r : R} (h : S.CN ψ φ r) {i : ι}
    (hi : i ∈ S.nf r) : ∃ t, S.KN i (lift (S.CN ψ φ)) r t :=
  let ⟨t, ht⟩ := (h 0 i hi).1
  ⟨t, h.KN_CN hi t ht⟩

end System

end Cslib.Knowledge
