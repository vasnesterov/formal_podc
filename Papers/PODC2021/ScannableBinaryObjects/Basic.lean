import Papers.PODC2021.ScannableBinaryObjects.Defs

/-!
# Scannable binary objects: basic lemmas

* algebra of `Absent` (`absent_append`, `absent_append_noP0`, …);
* `scan_resp` (Observation 3): by linearizability, a scan by a scanner returns the value after a
  prefix of `p₀`'s operations containing all those completed before the scan was invoked;
* `Lim` lemmas.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Scannable

open Cslib.SharedMemory

variable {k : ℕ} {O : Fin k → BitObj} {P : Type} [DecidableEq P]

/-- All invocations in `α` follow the single-updater discipline. -/
def SUExec (p₀ : P) (α : List (Label P (scannable O))) : Prop :=
  ∀ p o, Label.inv p o ∈ α → SingleUpdater p₀ p o

lemma inv_mem_of_mem_opsOf {α : List (Label P (scannable O))} {p : P} {o : ScanOp O}
    (h : o ∈ opsOf α p) : Label.inv p o ∈ α := by
  simp only [opsOf, List.mem_filterMap] at h
  obtain ⟨ℓ, hℓ, he⟩ := h
  cases ℓ with
  | inv q o' =>
    simp only [Label.invOf_inv] at he
    split_ifs at he with hq
    · cases he; subst hq; exact hℓ
  | ret q r => simp at he
  | tau q => simp at he

/-! ### Values and absence -/

section Absent

variable {p₀ : P}

lemma valAt_congr {ε ε' : List (Label P (scannable O))} (h : opsOf ε p₀ = opsOf ε' p₀) (i : ℕ) :
    valAt p₀ ε i = valAt p₀ ε' i := by
  simp only [valAt, h]

lemma valAt_append_of_le {ε β : List (Label P (scannable O))} {i : ℕ}
    (hi : i ≤ (opsOf ε p₀).length) : valAt p₀ (ε ++ β) i = valAt p₀ ε i := by
  simp only [valAt, opsOf_append, List.take_append_of_le_length hi]

lemma valAt_append_add (ε β : List (Label P (scannable O))) (t : ℕ) :
    valAt p₀ (ε ++ β) ((opsOf ε p₀).length + t) =
      (scannable O).runOps (curVal p₀ ε) ((opsOf β p₀).take t) := by
  simp only [valAt, curVal, opsOf_append, List.take_append]
  rw [List.take_of_length_le (by omega), ObjSpec.runOps_append, List.take_length]
  congr 2
  omega

lemma absent_append {V : Set (Fin k → Bool)} {ε β γ : List (Label P (scannable O))} :
    Absent p₀ V ε (β ++ γ) ↔ Absent p₀ V ε β ∧ Absent p₀ V (ε ++ β) γ := by
  constructor
  · intro h
    refine ⟨fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
    · have := h i h1 (by simp only [opsOf_append, List.length_append] at h2 ⊢; omega)
      rwa [← List.append_assoc, valAt_append_of_le h2] at this
    · have := h i (by simp only [opsOf_append, List.length_append] at h1 ⊢; omega)
        (by simpa using h2)
      simpa using this
  · rintro ⟨h1, h2⟩ i hi1 hi2
    by_cases hle : i ≤ (opsOf (ε ++ β) p₀).length
    · have := h1 i hi1 hle
      rwa [← List.append_assoc, valAt_append_of_le hle]
    · have := h2 i (by omega) (by simpa using hi2)
      simpa using this

lemma absent_append_noP0 {V : Set (Fin k → Bool)} {ε β γ : List (Label P (scannable O))}
    (hγ : opsOf γ p₀ = []) : Absent p₀ V ε (β ++ γ) ↔ Absent p₀ V ε β := by
  have h : opsOf (ε ++ (β ++ γ)) p₀ = opsOf (ε ++ β) p₀ := by simp [hγ]
  unfold Absent
  simp only [h, valAt_congr h]

lemma absent_nil_iff {V : Set (Fin k → Bool)} {ε : List (Label P (scannable O))} :
    Absent p₀ V ε [] ↔ curVal p₀ ε ∉ V := by
  constructor
  · intro h; have := h _ le_rfl (by simp); simpa [curVal] using this
  · intro h i h1 h2
    simp only [List.append_nil] at h2 ⊢
    rwa [show i = (opsOf ε p₀).length by omega]

lemma absent_noP0 {V : Set (Fin k → Bool)} {ε γ : List (Label P (scannable O))}
    (hγ : opsOf γ p₀ = []) : Absent p₀ V ε γ ↔ curVal p₀ ε ∉ V := by
  rw [← absent_nil_iff, ← absent_append_noP0 (β := []) hγ, List.nil_append]

lemma Absent.mono {V V' : Set (Fin k → Bool)} {ε β : List (Label P (scannable O))}
    (h : Absent p₀ V ε β) (hV : V' ⊆ V) : Absent p₀ V' ε β :=
  fun i h1 h2 hm => h i h1 h2 (hV hm)

/-- The current value at the end of `β` is not in `V` if `β` is `V`-absent. -/
lemma Absent.curVal {V : Set (Fin k → Bool)} {ε β : List (Label P (scannable O))}
    (h : Absent p₀ V ε β) : curVal p₀ (ε ++ β) ∉ V :=
  h _ (by simp) le_rfl

end Absent

/-! ### Observation 3: responses of scans -/

section ScanResp

variable {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
  {I : Impl (scannable O) B P L} {p₀ : P}

/-- **Observation 3 (core).** In a single-updater execution `α = ε ++ γ`, a scan `(q, m)` that
was not invoked in `ε` and has returned `r` in `α` returns the value after the first `i`
operations of `p₀`, where `i` is at least the number of operations of `p₀` completed in `ε` and
at most the number of operations of `p₀` invoked in `α`. -/
theorem scan_resp (hlin : I.Linearizable) {ε γ : List (Label P (scannable O))}
    (hv : I.Valid (ε ++ γ)) (hsu : SUExec p₀ (ε ++ γ)) {q : P} (hq : q ≠ p₀) {m : ℕ}
    (hinv : ¬ Invoked ε (q, m)) {r : ScanResp O} (hr : respOf (ε ++ γ) (q, m) = some r) :
    ∃ i, (respsOf ε p₀).length ≤ i ∧ i ≤ (opsOf (ε ++ γ) p₀).length ∧
      r = .view (valAt p₀ (ε ++ γ) i) := by
  obtain ⟨h, hh⟩ := hlin
  have hL := hh _ hv
  have hro : ∀ y ∈ h (ε ++ γ), y.1.1 ≠ p₀ → (scannable O).ReadOnly y.2 := by
    intro y hy hy0
    have := hsu _ _ (inv_mem_of_mem_opsOf (hL.op_mem hy))
    obtain ⟨⟨q', j⟩, o⟩ := y
    cases o with
    | scan => intro v; rfl
    | update i o' => exact absurd this hy0
  obtain ⟨j, hj1, hj2, o, ho, hro'⟩ := hL.resp_eq hv.wellFormed p₀ hro hr
    (respsOf ε p₀).length (fun j hj => ⟨ε, γ, rfl, hj, hinv⟩)
  have hmem : o ∈ opsOf (ε ++ γ) q := by
    simp only [opOf] at ho; exact List.mem_of_getElem? ho
  have hsuo := hsu _ _ (inv_mem_of_mem_opsOf hmem)
  cases o with
  | scan => exact ⟨j, hj1, hj2, hro'⟩
  | update i o' => exact absurd hsuo hq

end ScanResp

/-! ### Restricted executions -/

section Lim

variable {p₀ : P}

lemma lim_append {A : Finset P} {k' : ℕ} {β γ : List (Label P (scannable O))} :
    Lim p₀ A k' (β ++ γ) ↔ Lim p₀ A k' β ∧ Lim p₀ A k' γ := by
  simp only [Lim, List.mem_append]
  constructor
  · intro h; exact ⟨fun ℓ hℓ => h ℓ (Or.inl hℓ), fun ℓ hℓ => h ℓ (Or.inr hℓ)⟩
  · rintro ⟨h1, h2⟩ ℓ (hℓ | hℓ)
    · exact h1 ℓ hℓ
    · exact h2 ℓ hℓ

lemma Lim.mono {A A' : Finset P} {k' k'' : ℕ} {β : List (Label P (scannable O))}
    (h : Lim p₀ A k' β) (hA : A ⊆ A') (hk : k' ≤ k'') : Lim p₀ A' k'' β := by
  intro ℓ hℓ
  obtain ⟨h1, h2⟩ := h ℓ hℓ
  refine ⟨hA h1, ?_⟩
  cases ℓ with
  | inv p o => exact ⟨h2.1, fun i o' ho => (h2.2 i o' ho).trans_le hk⟩
  | _ => trivial

lemma Lim.su {A : Finset P} {k' : ℕ} {β : List (Label P (scannable O))} (h : Lim p₀ A k' β) :
    SUExec p₀ β := fun p o hm => (h _ hm).2.1

lemma suExec_append {α β : List (Label P (scannable O))} :
    SUExec p₀ (α ++ β) ↔ SUExec p₀ α ∧ SUExec p₀ β := by
  simp only [SUExec, List.mem_append]
  constructor
  · intro h; exact ⟨fun p o hm => h p o (Or.inl hm), fun p o hm => h p o (Or.inr hm)⟩
  · rintro ⟨h1, h2⟩ p o (hm | hm)
    · exact h1 p o hm
    · exact h2 p o hm

/-- Labels without invocations. -/
def NoInv (β : List (Label P (scannable O))) : Prop := ∀ p, opsOf β p = []

lemma mem_opsOf_of_inv_mem {β : List (Label P (scannable O))} {p : P} {o : ScanOp O}
    (h : Label.inv p o ∈ β) : o ∈ opsOf β p := by
  simp only [opsOf, List.mem_filterMap]
  exact ⟨_, h, by simp⟩

lemma lim_of_noInv {A : Finset P} {k' : ℕ} {β : List (Label P (scannable O))}
    (h : NoInv β) (hA : ∀ ℓ ∈ β, ℓ.proc ∈ A) : Lim p₀ A k' β := by
  intro ℓ hℓ
  refine ⟨hA ℓ hℓ, ?_⟩
  cases ℓ with
  | inv p o => have := mem_opsOf_of_inv_mem hℓ; rw [h p] at this; simp at this
  | _ => trivial

lemma noInv_append {β γ : List (Label P (scannable O))} (h1 : NoInv β) (h2 : NoInv γ) :
    NoInv (β ++ γ) := fun p => by simp [h1 p, h2 p]

lemma opsOf_eq_nil_of_lim {A : Finset P} {k' : ℕ} {β : List (Label P (scannable O))} {p : P}
    (h : Lim p₀ A k' β) (hp : p ∉ A) : opsOf β p = [] :=
  opsOf_eq_nil_of_proc_ne (fun ℓ hℓ he => hp (he ▸ (h ℓ hℓ).1))

end Lim

end Cslib.SharedMemory.Scannable
