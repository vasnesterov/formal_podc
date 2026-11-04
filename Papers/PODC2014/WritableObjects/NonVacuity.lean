import Papers.PODC2014.WritableObjects.Counterexample

/-!
# Non-vacuity of Lemma 4.5

A transcript of a register `WT` over `ℕ` (processes `p₀`, `p₁`; both indices owned by `p₀`) that
satisfies all hypotheses of Lemma 4.5, including the "not in use" requirement, with concurrent
operations: `p₀` writes `1` (index `0`), then `Write(2)` on the fresh index `1`; meanwhile `p₁` reads
`1` from `A[0]`; after `Ptr := 1`, `p₁` reads `2` from `A[1]`.
-/

namespace Podc.WritableObjects.Counterexample

open Cslib.SharedMemory List

/-- The transcript. -/
def okα : List (Ev (Fin 2) (Fin 2) R) :=
  [ .winv 0 1, .swinv 0 0 1, .aret 0 0 1, .ptr 0 0, .hret 0 1,
    .winv 0 2, .swinv 0 1 2, .aret 0 1 2,
    .einv 1 .read, .opinv 1 0 .read, .aret 1 0 1, .hret 1 1,
    .ptr 0 1, .hret 0 2,
    .einv 1 .read, .opinv 1 1 .read, .aret 1 1 2, .hret 1 2 ]

/-- Both indices are owned by `p₀`. -/
def own2 : Fin 2 → Fin 2 := fun _ => 0

/-- Control states along `okα`. -/
def ctl2 : Fin 2 → ℕ → PSt (Fin 2) R
  | 0, t => (([.idle, .wBeg 1, .wSW 1 0, .wPtr 1 0, .wEnd 1, .idle, .wBeg 2, .wSW 2 1] :
      List (PSt (Fin 2) R)) ++ replicate 5 (PSt.wPtr 2 1 : PSt (Fin 2) R) ++
      [(PSt.wEnd 2 : PSt (Fin 2) R)] ++ replicate 5 (PSt.idle : PSt (Fin 2) R)).getD t .idle
  | 1, t => (replicate 9 (PSt.idle : PSt (Fin 2) R) ++
      ([.eBeg .read, .eOp 0, .eEnd 1] : List (PSt (Fin 2) R)) ++
      replicate 3 (PSt.idle : PSt (Fin 2) R) ++
      ([.eBeg .read, .eOp 1, .eEnd 2, .idle] : List (PSt (Fin 2) R))).getD t .idle

lemma okα_ctrl : IsCtrl regW own2 okα ctl2 := by
  intro p
  refine ⟨by fin_cases p <;> rfl, fun t ht => ?_⟩
  simp only [okα, List.length_cons, List.length_nil] at ht
  fin_cases p <;> interval_cases t <;>
    simp [okα, ctl2, Ev.proc, own2] <;>
    first
    | exact PStep.winv _
    | exact PStep.einv _ (by intro v h; cases h)
    | exact PStep.swinv _ _ rfl
    | exact PStep.swret _ _ _
    | exact PStep.ptr _ _
    | exact PStep.wret (W := regW) _
    | exact PStep.opinv _ _
    | exact PStep.opret _ _
    | exact PStep.eret _

lemma lt_of_okα {a : ℕ} {ev : Ev (Fin 2) (Fin 2) R} (h : okα[a]? = some ev) : a < 18 := by
  have := (getElem_of_getElem? h).1; simpa [okα] using this

lemma okα_notInUse : NotInUse okα := by
  intro t p f v ht
  have := lt_of_okα ht
  interval_cases t <;> simp [okα] at ht <;> obtain ⟨rfl, rfl, rfl⟩ := ht <;> decide

lemma okα_condC : CondC okα := by
  intro e t q o o' i het he ht hq
  have htl := lt_of_okα ht
  interval_cases t <;> simp [okα] at ht
  · obtain ⟨rfl, rfl, rfl⟩ := ht
    refine ⟨9, het, le_rfl, by decide, fun a p v ha => ?_⟩
    have := lt_of_okα ha
    interval_cases a <;> simp [okα] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact Or.inl ⟨2, 1, by omega, by omega, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := ht
    refine ⟨15, het, le_rfl, by decide, fun a p v ha => ?_⟩
    have := lt_of_okα ha
    interval_cases a <;> simp [okα] at ha
    obtain ⟨rfl, rfl⟩ := ha
    exact Or.inl ⟨7, 2, by omega, by omega, rfl⟩

lemma okα_seqWritable (i : Fin 2) : SeqWritable regW (lowH regW i okα) := by
  intro _
  fin_cases i
  · have h := seq_extend (seq_extend (isLinearization_nil (P := Fin 2) (A := R)) 0 (.write 1) rfl)
      1 .read rfl
    exact ⟨_, by convert h using 1; rfl⟩
  · have h := seq_extend (seq_extend (isLinearization_nil (P := Fin 2) (A := R)) 0 (.write 2) rfl)
      1 .read rfl
    exact ⟨_, by convert h using 1; rfl⟩

/-- **Non-vacuity of Lemma 4.5**: a transcript with concurrent operations satisfying all its
hypotheses (template including "not in use", condition (C), sequentially writable base objects). -/
theorem lemma_4_5_nonvacuous : ∃ (α : List (Ev (Fin 2) (Fin 2) R)),
    Template regW own2 α ∧ CondC α ∧ (∀ i, SeqWritable regW (lowH regW i α)) :=
  ⟨okα, ⟨⟨ctl2, okα_ctrl⟩, okα_notInUse⟩, okα_condC, okα_seqWritable⟩

end Podc.WritableObjects.Counterexample
