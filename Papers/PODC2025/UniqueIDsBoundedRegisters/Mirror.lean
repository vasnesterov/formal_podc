import Papers.PODC2025.UniqueIDsBoundedRegisters.Defs

/-!
# Anonymity: another process can replay a solo run

If all processes run the same automaton (`Anonymous`), a process `q'` whose local state, pending
operation and memory agree with those of `q` can replay any run of `q` step by step
(`runFrom_mirror`), with the same responses (`respsOf_relabel`). (CSLib candidate.)
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.UniqueIDs

open Cslib.SharedMemory Impl

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι]

-- CSLib candidate
/-- Rename the process of a label. -/
def relabel (q' : P) : Label P A → Label P A
  | .inv _ o => .inv q' o
  | .tau _ => .tau q'
  | .ret _ r => .ret q' r

/-- `C` seen by `q` is `D` seen by `q'`. -/
structure Mirror (q q' : P) (C D : Config A B P L) : Prop where
  mem : C.mem = D.mem
  loc : C.loc q = D.loc q'
  pend : C.pend q = D.pend q'

variable {I : Impl A B P L}

lemma step_mirror (hA : Anonymous I) {q q' : P} (hall : ∀ o, I.allowed q o → I.allowed q' o)
    {C D C' : Config A B P L} (h : Mirror q q' C D) {ℓ : Label P A} (hℓ : ℓ.proc = q)
    (hs : I.step C ℓ = some C') :
    ∃ D', I.step D (relabel q' ℓ) = some D' ∧ Mirror q q' C' D' := by
  classical
  cases ℓ with
  | inv p o =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, h3, h4⟩ := step_inv hs
    have : I.step D (.inv q' o) =
        some { D with pend := Function.update D.pend q' (some o),
                      loc := Function.update D.loc q' (I.invoke q' (D.loc q') o) } := by
      simp [step, ← h.pend, h0, hall o h1]
    refine ⟨_, this, ?_, ?_, ?_⟩
    · rw [h4, h.mem]
    · rw [h3]; simp [h.loc, hA.invoke p q']
    · rw [h2]; simp
  | tau p =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, i, o, k, hact, hm, hl⟩ := step_tau hs
    have hact' : I.act q' (D.loc q') = .access i o k := by rw [← h.loc, hA.act q' p, hact]
    have : I.step D (.tau q') = some { D with
        mem := Function.update D.mem i ((B i).δ (D.mem i) o).1,
        loc := Function.update D.loc q' (k ((B i).δ (D.mem i) o).2) } := by
      simp [step, ← h.pend, h0, hact']
    refine ⟨_, this, ?_, ?_, ?_⟩
    · rw [hm, h.mem]
    · rw [hl]; simp [h.mem]
    · rw [h1]; exact h.pend
  | ret p r =>
    simp only [Label.proc] at hℓ; subst hℓ
    obtain ⟨h0, h1, h2, l, hact, hl⟩ := step_ret hs
    have hact' : I.act q' (D.loc q') = .ret r l := by rw [← h.loc, hA.act q' p, hact]
    have : I.step D (.ret q' r) = some
        { D with pend := Function.update D.pend q' none, loc := Function.update D.loc q' l } := by
      simp [step, ← h.pend, h0, hact']
    refine ⟨_, this, ?_, ?_, ?_⟩
    · rw [h2, h.mem]
    · rw [hl]; simp
    · rw [h1]; simp

lemma runFrom_mirror (hA : Anonymous I) {q q' : P} (hall : ∀ o, I.allowed q o → I.allowed q' o) :
    ∀ (γ : List (Label P A)) {C D C' : Config A B P L}, Mirror q q' C D → (∀ ℓ ∈ γ, ℓ.proc = q) →
      I.runFrom C γ = some C' → ∃ D', I.runFrom D (γ.map (relabel q')) = some D' ∧ Mirror q q' C' D' := by
  intro γ
  induction γ with
  | nil =>
    intro C D C' h _ hr
    simp only [runFrom_nil, Option.some.injEq] at hr; subst hr; exact ⟨D, rfl, h⟩
  | cons ℓ γ ih =>
    intro C D C' h hγ hr
    simp only [runFrom_cons] at hr
    cases hs : I.step C ℓ with
    | none => simp [hs] at hr
    | some C₁ =>
      simp only [hs, Option.bind_some] at hr
      obtain ⟨D₁, hD₁, h₁⟩ := step_mirror hA hall h (hγ ℓ (by simp)) hs
      obtain ⟨D', hD', h'⟩ := ih h₁ (fun ℓ' hℓ' => hγ ℓ' (by simp [hℓ'])) hr
      exact ⟨D', by simp [hD₁, hD'], h'⟩

omit [DecidableEq ι] in
lemma respsOf_relabel {q q' : P} : ∀ γ : List (Label P A), (∀ ℓ ∈ γ, ℓ.proc = q) →
    respsOf (γ.map (relabel q')) q' = respsOf γ q := by
  intro γ
  induction γ with
  | nil => intro _; rfl
  | cons ℓ γ ih =>
    intro h
    have hℓ := h ℓ (by simp)
    rw [List.map_cons, respsOf_cons, respsOf_cons, ih (fun ℓ' hℓ' => h ℓ' (by simp [hℓ']))]
    cases ℓ with
    | inv p o => rfl
    | tau p => rfl
    | ret p r => simp only [Label.proc] at hℓ; subst hℓ; simp [relabel]

omit [DecidableEq ι] in
lemma relabel_proc (q' : P) (ℓ : Label P A) : (relabel q' ℓ).proc = q' := by
  cases ℓ <;> rfl

omit [DecidableEq P] [DecidableEq ι] in
lemma numInv_relabel (q' : P) (γ : List (Label P A)) :
    numInv (γ.map (relabel q')) = numInv γ := by
  induction γ with
  | nil => rfl
  | cons ℓ γ ih => cases ℓ <;> simp [relabel, ih, Label.isInv]

end Cslib.SharedMemory.UniqueIDs
