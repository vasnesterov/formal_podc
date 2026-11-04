import Papers.PODC2014.EventualLinParadox.Basic

/-!
# Lemma 6 needs total operations

The paper's sequential specifications have a transition *relation* `δ ⊆ Q × OP × RES × Q`, which
may leave an operation without any transition in some state. Lemma 6 ("every prefix of a
`t`-linearizable history is `t`-linearizable") is false for such partial types: its proof
completes the early operations "with the responses they would have if executed in that order",
which needs every operation to be applicable in every state (see `TLinearizable.prefix`, which
proves Lemma 6 for total types).

Counterexample (`lemma6_false_partial`): a one-bit object whose operation `use` (`false`) is only
enabled after `enable` (`true`). Process 0 runs `use` (positions 0, 1), then process 1 runs
`enable` (positions 2, 3). With `t = 2`, the history is `2`-linearizable (`enable` before `use`,
which responded before position `2`), but its prefix of length `2` is not: its only operation
is `use`, which cannot be applied in the initial state.
-/

namespace Podc.EventualLinParadox

/-- A one-bit object: `enable` (`true`) sets the bit, `use` (`false`) requires it. -/
def gateType : ObjType Bool Bool Unit where
  init := {false}
  δ q op _ q' := if op then q' = true else q = true ∧ q' = q

/-- `use` by process 0, then `enable` by process 1. -/
def gateHist : History (Fin 2) Unit Bool Unit := fun n =>
  match n with
  | 0 => some (.inv 0 () false)
  | 1 => some (.res 0 ())
  | 2 => some (.inv 1 () true)
  | 3 => some (.res 2 ())
  | _ => none

/-- `enable` then `use`. -/
def gateLin : SeqHist Unit := fun k =>
  match k with
  | 0 => some (2, ())
  | 1 => some (0, ())
  | _ => none

lemma gateHist_isTLin : IsTLin (fun _ => gateType) gateHist 2 gateLin where
  nodup k k' a r r' hk hk' := by
    match k, k' with
    | 0, 0 => rfl
    | 1, 1 => rfl
    | 0, 1 => simp [gateLin] at hk hk'; omega
    | 1, 0 => simp [gateLin] at hk hk'; omega
    | k + 2, _ => simp [gateLin] at hk
    | _, k' + 2 => simp [gateLin] at hk'
  legal := by
    refine ⟨fun k a r hk => ?_, fun x => ⟨fun k => decide (1 ≤ k), rfl, fun k => ?_⟩⟩
    · match k with
      | 0 => simp [gateLin] at hk; subst hk; exact ⟨1, (), true, rfl⟩
      | 1 => simp [gateLin] at hk; subst hk; exact ⟨0, (), false, rfl⟩
      | k + 2 => simp [gateLin] at hk
    · match k with
      | 0 => exact Or.inl ⟨1, true, rfl, by simp [gateType]⟩
      | 1 => exact Or.inl ⟨0, false, rfl, by simp [gateType]⟩
      | k + 2 => simp [gateLin, SeqStep]
  complete a j r hj := by
    match j with
    | 1 => simp [gateHist] at hj; subst hj; exact ⟨1, (), rfl⟩
    | 3 => simp [gateHist] at hj; subst hj; exact ⟨0, (), rfl⟩
    | 0 => simp [gateHist] at hj
    | 2 => simp [gateHist] at hj
    | j + 4 => simp [gateHist] at hj
  rt a b j r hj htj hjb hb _ := by
    obtain ⟨p, x, op, hb⟩ := hb
    match j with
    | 0 | 1 | 2 => simp [gateHist] at hj <;> omega
    | 3 => match b with
      | b + 4 => simp [gateHist] at hb
      | 0 | 1 | 2 | 3 => omega
    | j + 4 => simp [gateHist] at hj
  resp a j r hj htj := by
    match j with
    | 3 => simp [gateHist] at hj; subst hj; exact ⟨0, rfl⟩
    | 0 | 1 | 2 => simp [gateHist] at hj <;> omega
    | j + 4 => simp [gateHist] at hj

/-- **Lemma 6 is false for types with partial operations.** -/
theorem lemma6_false_partial :
    WellFormed gateHist ∧ TLinearizable (fun _ => gateType) gateHist 2 ∧
      ¬ TLinearizable (fun _ => gateType) (take gateHist 2) 2 := by
  refine ⟨⟨fun a j r hj => ?_, fun a j j' r r' hj hj' => ?_, fun a b p x x' op op' ha hb hab => ?_⟩,
    ⟨gateLin, gateHist_isTLin⟩, ?_⟩
  · match j with
    | 1 => simp [gateHist] at hj; subst hj; exact ⟨by omega, 0, (), false, rfl⟩
    | 3 => simp [gateHist] at hj; subst hj; exact ⟨by omega, 1, (), true, rfl⟩
    | 0 | 2 => simp [gateHist] at hj
    | j + 4 => simp [gateHist] at hj
  · match j, j' with
    | 1, 1 => rfl
    | 3, 3 => rfl
    | 1, 3 => simp [gateHist] at hj hj'; omega
    | 3, 1 => simp [gateHist] at hj hj'; omega
    | 0, _ | 2, _ | _ + 4, _ => simp [gateHist] at hj
    | _, 0 | _, 2 | _, _ + 4 => simp [gateHist] at hj'
  · match a, b with
    | 0, 2 => simp [gateHist] at ha hb; omega
    | 0, 0 | 2, 2 => omega
    | 2, 0 => omega
    | 1, _ | 3, _ | _ + 4, _ => simp [gateHist] at ha
    | _, 1 | _, 3 | _, _ + 4 => simp [gateHist] at hb
  · rintro ⟨S, hS⟩
    -- operation `0` (`use`) completed in the prefix, so it is in `S`
    obtain ⟨k, r, hk⟩ := hS.complete 0 1 () (by simp [take, gateHist])
    -- every entry of `S` is operation `0`, so nothing precedes it
    have hent : ∀ i a r, S i = some (a, r) → a = 0 := by
      intro i a r hi
      obtain ⟨p, x, op, ha⟩ := hS.legal.1 i a r hi
      simp only [take_apply] at ha
      split_ifs at ha with h
      match a with
      | 0 => rfl
      | 1 => simp [gateHist] at ha
    obtain ⟨q, hq0, hqs⟩ := hS.legal.2 ()
    have hconst : ∀ i ≤ k, q i = false := by
      intro i hi
      induction i with
      | zero => simpa [gateType] using hq0
      | succ i ih =>
        have := hqs i
        rcases hSi : S i with _ | ⟨a, r'⟩
        · rw [hSi] at this; simp only [SeqStep] at this; rw [this]; exact ih (by omega)
        · have := hent i a r' hSi; subst this
          have := hS.nodup i k 0 r' r hSi hk; omega
    have := hqs k
    rw [hk] at this
    obtain ⟨p, op, hop, hδ⟩ := this.onObj ⟨0, false, by simp [take, gateHist]⟩
    simp [take, gateHist] at hop
    obtain ⟨-, rfl⟩ := hop
    simp [gateType, hconst k le_rfl] at hδ

end Podc.EventualLinParadox
