import Papers.PODC2015.DAPInvisibleReads.Scenario
import Mathlib.Tactic.FinCases

/-!
# Figure 1: the histories `H_WRTO` and `H_NO-RTO`

Processes `1, …, 4` run `T₁, …, T₄`; objects `x = 0`, `y = 1`; initial values `0`; `T₂` writes
`x₂ = 2`, `T₃` writes `y₃ = 3`.

* `H_WRTO = (T₂, T₃, T₄)`: `T₄` reads `y₀`; then `T₃` writes `y₃` and commits; then `T₂` writes `x₂`
  and commits; then `T₄` reads `x₂` and commits. It preserves WRTO (`hWRTO_preservesWRTO`) but not
  RTO (`hWRTO_not_preservesRTO`): `T₃ ≺RTO T₂ →wr T₄ →rw T₃`.
* `H_NO-RTO = (T₁, T₂, T₃, T₄)`: as `H_WRTO`, with `T₁` running after `c₂` and reading `x₀` and
  `y₃`. It preserves neither WRTO nor RTO (`hNoRTO_not_preservesWRTO`): `T₂ ≺WRTO T₁ →rw T₂`.
-/

namespace Podc.DAPInvisibleReads.Figure1

open Cslib.SharedMemory

/-- Labels of the figure. -/
abbrev L5 := Lbl (Fin 5) (Fin 2) ℕ

/-- Initial values. -/
def v₀ : Fin 2 → ℕ := fun _ => 0

/-- `R₄(y₀)`. -/
def r4y : List L5 := [.inv 4 (.read 1), .ret 4 (some 0)]
/-- `T₃ = W₃(y₃) c₃`. -/
def t3 : List L5 := [.inv 3 (.write 1 3), .ret 3 (some 0), .inv 3 .tryC, .ret 3 (some 0)]
/-- `T₂ = W₂(x₂) c₂`. -/
def t2 : List L5 := [.inv 2 (.write 0 2), .ret 2 (some 0), .inv 2 .tryC, .ret 2 (some 0)]
/-- `T₁ = R₁(x₀) R₁(y₃) c₁`. -/
def t1 : List L5 :=
  [.inv 1 (.read 0), .ret 1 (some 0), .inv 1 (.read 1), .ret 1 (some 3), .inv 1 .tryC,
    .ret 1 (some 0)]
/-- `R₄(x₂) c₄`. -/
def r4x : List L5 := [.inv 4 (.read 0), .ret 4 (some 2), .inv 4 .tryC, .ret 4 (some 0)]

/-- The history `H_WRTO`. -/
def hWRTO : List L5 := r4y ++ t3 ++ t2 ++ r4x

/-- The history `H_NO-RTO`. -/
def hNoRTO : List L5 := r4y ++ t3 ++ t2 ++ t1 ++ r4x

lemma committed_iff (h : List L5) (T : TxId (Fin 5)) :
    Committed h T ↔ (txRec h T).ops.any (fun q => q.1 = .tryC ∧ q.2.isSome) := by
  simp only [Committed, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨v, hv⟩; exact ⟨_, hv, rfl, rfl⟩
  · rintro ⟨⟨o, r⟩, hm, ho, hr⟩
    obtain ⟨v, rfl⟩ := Option.isSome_iff_exists.1 hr
    simp only at ho; subst ho; exact ⟨v, hm⟩

instance (h : List L5) (T : TxId (Fin 5)) : Decidable (Committed h T) :=
  decidable_of_iff _ (committed_iff h T).symm

/-- The records of `H_WRTO`. -/
lemma txRec_hWRTO (p : Fin 5) (k : ℕ) :
    txRec hWRTO (p, k) =
      if k = 0 ∧ p = 4 then ⟨[(.read 1, some 0), (.read 0, some 2), (.tryC, some 0)], none⟩
      else if k = 0 ∧ p = 3 then ⟨[(.write 1 3, some 0), (.tryC, some 0)], none⟩
      else if k = 0 ∧ p = 2 then ⟨[(.write 0 2, some 0), (.tryC, some 0)], none⟩
      else TxRec.empty := by
  rcases k with _ | _ | k
  · fin_cases p <;> decide
  · fin_cases p <;> decide
  · have hl : ((pstate hWRTO p).done ++ [(pstate hWRTO p).cur]).length ≤ k + 2 := by
      have : ((pstate hWRTO p).done ++ [(pstate hWRTO p).cur]).length ≤ 2 := by
        fin_cases p <;> decide
      omega
    simp only [txRec, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none hl]; simp

/-- The records of `H_NO-RTO`. -/
lemma txRec_hNoRTO (p : Fin 5) (k : ℕ) :
    txRec hNoRTO (p, k) =
      if k = 0 ∧ p = 4 then ⟨[(.read 1, some 0), (.read 0, some 2), (.tryC, some 0)], none⟩
      else if k = 0 ∧ p = 3 then ⟨[(.write 1 3, some 0), (.tryC, some 0)], none⟩
      else if k = 0 ∧ p = 2 then ⟨[(.write 0 2, some 0), (.tryC, some 0)], none⟩
      else if k = 0 ∧ p = 1 then
        ⟨[(.read 0, some 0), (.read 1, some 3), (.tryC, some 0)], none⟩
      else TxRec.empty := by
  rcases k with _ | _ | k
  · fin_cases p <;> decide
  · fin_cases p <;> decide
  · have hl : ((pstate hNoRTO p).done ++ [(pstate hNoRTO p).cur]).length ≤ k + 2 := by
      have : ((pstate hNoRTO p).done ++ [(pstate hNoRTO p).cur]).length ≤ 2 := by
        fin_cases p <;> decide
      omega
    simp only [txRec, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none hl]; simp

/-! ### Versions -/

lemma cwriter_hWRTO (z : Fin 2) (T : TxId (Fin 5)) :
    CWriter hWRTO z T ↔ T = (if z = 0 then (2, 0) else (3, 0)) := by
  obtain ⟨p, k⟩ := T
  fin_cases z <;>
  · simp only [CWriter, Committed, wval, txRec_hWRTO]
    split_ifs with h1 h2 h3 <;> simp_all [writesOf, TxRec.empty] <;> tauto

lemma cwriter_hNoRTO (z : Fin 2) (T : TxId (Fin 5)) :
    CWriter hNoRTO z T ↔ T = (if z = 0 then (2, 0) else (3, 0)) := by
  obtain ⟨p, k⟩ := T
  fin_cases z <;>
  · simp only [CWriter, Committed, wval, txRec_hNoRTO]
    split_ifs with h1 h2 h3 h4 <;> simp_all [writesOf, TxRec.empty] <;> tauto

lemma reads_hWRTO {T : TxId (Fin 5)} {z : Fin 2} {v : ℕ} (h : Reads hWRTO T z v) : T = (4, 0) := by
  obtain ⟨p, k⟩ := T
  simp only [Reads, txRec_hWRTO] at h
  split_ifs at h with h1 h2 h3 <;> simp_all [TxRec.empty]

/-- `T₄` begins with the first event of `H_WRTO` and commits with its last event. -/
lemma hWRTO_take :
    (∀ n < 15, 1 ≤ n → Began (hWRTO.take n) (4, 0)) ∧
    (∀ n < 14, ¬ Committed (hWRTO.take n) (4, 0)) := by
  decide

lemma prefix_eq_take {h h₁ h₂ : List L5} (hs : h = h₁ ++ h₂) : h₁ = h.take h₁.length := by
  subst hs; simp

/-! ### The claims of Figure 1 -/

/-- Figure 1: `H_WRTO` does not preserve RTO: `T₃ ≺RTO T₂ →wr T₄ →rw T₃`. -/
theorem hWRTO_not_preservesRTO : ¬ PreservesRTO v₀ hWRTO := by
  intro H
  have hrto : RTO hWRTO (3, 0) (2, 0) :=
    ⟨by decide, r4y ++ t3, t2 ++ r4x, by simp [hWRTO], by decide, by decide⟩
  refine H _ _ hrto (Relation.TransGen.head (b := (4, 0)) (Or.inl (Or.inl ⟨by decide, by decide, 0, 2,
    by simp [Reads, txRec_hWRTO], by decide⟩)) (Relation.TransGen.single (Or.inl ?_)))
  refine Or.inr (Or.inr ⟨by decide, 1, 0, none, by simp [Reads, txRec_hWRTO], rfl, by simp, ?_⟩)
  exact nextV_none (fun T => by simpa using cwriter_hWRTO 1 T)

/-- Figure 1: `H_WRTO` preserves WRTO (its only RTO pair, `T₃ ≺RTO T₂`, is not joined by a
direct edge). -/
theorem hWRTO_preservesWRTO : PreservesWRTO v₀ hWRTO := by
  -- every direct edge has `T₄` as an endpoint
  have hdsg : ∀ T T', DSG v₀ hWRTO T T' → T = (4, 0) ∨ T' = (4, 0) := by
    rintro T T' (⟨-, -, z, v, hr, -⟩ | ⟨z, hn⟩ | ⟨-, z, v, u, hr, -⟩)
    · exact Or.inr (reads_hWRTO hr)
    · have hv : VOrd hWRTO z T T' := by
        cases hn' : (some T : Option (TxId (Fin 5))) with
        | none => simp at hn'
        | some T₀ => exact hn.1
      exact absurd hv (not_vOrd (cwriter_hWRTO z) _ _)
    · exact Or.inl (reads_hWRTO hr)
  have h4 := hWRTO_take
  -- `T₄` is in no RTO pair
  have hrto : ∀ T T', RTO hWRTO T T' → T ≠ (4, 0) ∧ T' ≠ (4, 0) := by
    rintro T T' ⟨hb, h₁, h₂, hs, hc, hnb⟩
    have ht := prefix_eq_take hs
    have hlen : h₁.length ≤ 14 := by
      have := congrArg List.length hs; simp only [List.length_append] at this
      have : hWRTO.length = 14 := rfl; omega
    refine ⟨fun hT => ?_, fun hT' => ?_⟩
    · subst hT
      rcases Nat.lt_or_ge h₁.length 14 with hl | hl
      · rw [ht] at hc; exact h4.2 _ hl hc
      · have : h₂ = [] := by
          have := congrArg List.length hs; simp only [List.length_append] at this
          have : hWRTO.length = 14 := rfl; exact List.eq_nil_of_length_eq_zero (by omega)
        subst this; simp at hs; subst hs; exact hnb hb
    · subst hT'
      rcases Nat.eq_zero_or_pos h₁.length with hl | hl
      · rw [List.length_eq_zero_iff] at hl; subst hl
        exact absurd hc (by
          rcases T with ⟨p, k⟩
          simp [Committed, txRec, pstate, projP, PState.init, TxRec.empty]
          rcases k with _ | k <;> simp)
      · rw [ht] at hnb; exact hnb (h4.1 _ (by omega) hl)
  rintro T T' ⟨hr, hd⟩ -
  obtain ⟨h1, h2⟩ := hrto T T' hr
  rcases hd with hd | hd <;> rcases hdsg _ _ hd with h | h <;> simp_all

/-- Figure 1: `H_NO-RTO` preserves neither WRTO nor RTO: `T₂ ≺WRTO T₁ →rw T₂`. -/
theorem hNoRTO_not_preservesWRTO : ¬ PreservesWRTO v₀ hNoRTO ∧ ¬ PreservesRTO v₀ hNoRTO := by
  have hd : DSG v₀ hNoRTO (1, 0) (2, 0) := by
    refine Or.inr (Or.inr ⟨by decide, 0, 0, none, by simp [Reads, txRec_hNoRTO], rfl, by simp, ?_⟩)
    exact nextV_none (fun T => by simpa using cwriter_hNoRTO 0 T)
  have hrto : RTO hNoRTO (2, 0) (1, 0) :=
    ⟨by decide, r4y ++ t3 ++ t2, t1 ++ r4x, by simp [hNoRTO], by decide, by decide⟩
  have hw : ¬ PreservesWRTO v₀ hNoRTO := fun H =>
    H _ _ ⟨hrto, Or.inr hd⟩ (Relation.TransGen.single (Or.inl hd))
  exact ⟨hw, fun H => hw H.preservesWRTO⟩

/-- Why `EnsuresRTO` only considers histories with unique written values: in the value-based DSG,
the serial history `W₀(x, 0) c₀ · R₁(x) c₁` (whose read returns the value written by `T₀`, equal
to the initial value) would count as a violation of RTO (`T₀ ≺RTO T₁ →rw T₀`, the read being
attributed to the initial version). -/
def hRep : List (Lbl (Fin 2) (Fin 1) ℕ) :=
  [.inv 0 (.write 0 0), .ret 0 (some 0), .inv 0 .tryC, .ret 0 (some 0), .inv 1 (.read 0),
    .ret 1 (some 0)]

lemma txRec_hRep (p : Fin 2) (k : ℕ) : txRec hRep (p, k) =
    if k = 0 ∧ p = 0 then ⟨[(.write 0 0, some 0), (.tryC, some 0)], none⟩
    else if k = 0 ∧ p = 1 then ⟨[(.read 0, some 0)], none⟩ else TxRec.empty := by
  rcases k with _ | _ | k
  · fin_cases p <;> decide
  · fin_cases p <;> decide
  · have hl : ((pstate hRep p).done ++ [(pstate hRep p).cur]).length ≤ k + 2 := by
      have : ((pstate hRep p).done ++ [(pstate hRep p).cur]).length ≤ 2 := by
        fin_cases p <;> decide
      omega
    simp only [txRec, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none hl]; simp

/-- The serial history `hRep` (a transaction rewrites the initial value, a later one reads it)
does not preserve RTO in the value-based DSG, so `EnsuresRTO` must exclude repeated values
(`UniqueWrites`). -/
theorem serial_repeated_value_not_preservesRTO : ¬ PreservesRTO (fun _ => (0 : ℕ)) hRep := by
  intro H
  have hc : ∀ T, CWriter hRep 0 T ↔ T = (0, 0) := by
    rintro ⟨p, k⟩
    simp only [CWriter, Committed, wval, txRec_hRep]
    split_ifs with h1 h2 <;> simp_all [writesOf, TxRec.empty] <;> tauto
  have h4 : txRec (hRep.take 4) (0, 0) = ⟨[(.write 0 0, some 0), (.tryC, some 0)], none⟩ := by
    decide
  have h4' : txRec (hRep.take 4) (1, 0) = TxRec.empty := by decide
  have hrto : RTO hRep (0, 0) (1, 0) :=
    ⟨by simp [Began, txRec_hRep], hRep.take 4, hRep.drop 4, rfl, ⟨0, by simp [h4]⟩,
      by simp [Began, h4', TxRec.empty]⟩
  refine H _ _ hrto (Relation.TransGen.single (Or.inl (Or.inr (Or.inr
    ⟨by decide, 0, 0, none, by simp [Reads, txRec_hRep], rfl, by simp, nextV_none hc⟩))))

/-- WRTO is strictly weaker than RTO: preserving RTO implies preserving WRTO
(`PreservesRTO.preservesWRTO`), and `H_WRTO` preserves WRTO but not RTO. -/
theorem wrto_strictly_weaker :
    (∀ h : List L5, PreservesRTO v₀ h → PreservesWRTO v₀ h) ∧
      ∃ h : List L5, PreservesWRTO v₀ h ∧ ¬ PreservesRTO v₀ h :=
  ⟨fun _ H => H.preservesWRTO, hWRTO, hWRTO_preservesWRTO, hWRTO_not_preservesRTO⟩

end Podc.DAPInvisibleReads.Figure1
