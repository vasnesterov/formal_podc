import Papers.PODC2018.CausalRecordReplay.Model2

/-!
# Counterexample to Definition 6.4 read literally; the `SWO(V)` typo in the proof of Lemma C.1

The smallest instance: two processes `0, 1`, each performing one write to the same variable
(`w₀`, `w₁`, the operations `0` and `1`). Both views order `w₁` before `w₀`.

* `theorem_6_6_literal_false`: with Definition 6.4 taken literally (no `w₃ ≠ w₄`, flag `d = false`),
  `C₀(V, w₁, w₀)` contains the self-loop `(w₀, w₀)`, so `(w₁, w₀) ∈ B₀(V)` and the record of
  Theorem 6.6 is empty; but swapping both views is a strongly causal replay with different data-race
  orders, so the record is not good.
* `lemma_C_1_SWO_record_false`: Case 1 of the proof of Lemma C.1 writes the record as
  `Â_i \ (SWO(V) ∪ PO ∪ B_i)` (`SWO` instead of `SWO_i`, which the statement of Lemma C.1 and
  Theorem 6.6 use). That record is empty here (for either reading of Definition 6.4), and the
  swapped replay loses the `SWO(V)` pair `(w₁, w₀)`: Lemma C.1(a) would fail for it. This refutes
  only the typo inside the proof, not a statement of the paper.
-/

namespace Podc.CausalRecordReplay

open Relation

namespace Counterexample

/-- Two processes, one write each, to the same variable. -/
def prog : Program (Fin 2) (Fin 2) Unit where
  proc := id
  IsWrite := fun _ => True
  var := fun _ => ()
  po := fun _ _ => False
  po_irrefl := fun _ h => h
  po_trans := fun h _ => h
  po_proc := fun h => h.elim
  po_total := fun h hne => absurd h hne

/-- Original views: `w₁ < w₀` at both processes. -/
def V : Fin 2 → Fin 2 → Fin 2 → Prop := fun _ a b => a = 1 ∧ b = 0

/-- Replay views: `w₀ < w₁` at both processes. -/
def V' : Fin 2 → Fin 2 → Fin 2 → Prop := fun _ a b => a = 0 ∧ b = 1

theorem total_V (i : Fin 2) : IsStrictTotalOn (prog.Obs i) (V i) := by
  refine ⟨fun _ => ⟨Or.inr trivial, Or.inr trivial⟩, fun a h => ?_, fun h1 h2 => ?_,
    fun {a b} _ _ hne => ?_⟩
  · obtain ⟨rfl, h⟩ := h; exact absurd h (by decide)
  · obtain ⟨rfl, rfl⟩ := h1; obtain ⟨h, -⟩ := h2; exact absurd h (by decide)
  · fin_cases a <;> fin_cases b <;> simp_all [V]

theorem total_V' (i : Fin 2) : IsStrictTotalOn (prog.Obs i) (V' i) := by
  refine ⟨fun _ => ⟨Or.inr trivial, Or.inr trivial⟩, fun a h => ?_, fun h1 h2 => ?_,
    fun {a b} _ _ hne => ?_⟩
  · obtain ⟨rfl, h⟩ := h; exact absurd h (by decide)
  · obtain ⟨rfl, rfl⟩ := h1; obtain ⟨h, -⟩ := h2; exact absurd h (by decide)
  · fin_cases a <;> fin_cases b <;> simp_all [V']

theorem sc_V : prog.StronglyCausal V :=
  Program.stronglyCausal_iff.2 fun i =>
    ⟨total_V i, fun _ _ h => h.2.2, fun _ _ h => h.1.elim⟩

theorem sc_V' : prog.StronglyCausal V' :=
  Program.stronglyCausal_iff.2 fun i =>
    ⟨total_V' i, fun _ _ h => h.2.2, fun _ _ h => h.1.elim⟩

/-- `(w₁, w₀)` is in the strong write order of `V` (a data race ordered by the view of `0`). -/
theorem swo_10 : prog.SWO V 1 0 :=
  ⟨1, trivial, trivial, TransGen.single (Or.inl ⟨⟨rfl, rfl⟩, rfl⟩)⟩

/-- The only cover of `A_i(V)` is `(w₁, w₀)`. -/
theorem cov_eq {i : Fin 2} {a b : Fin 2} (h : Cov (prog.Arel V i) a b) : a = 1 ∧ b = 0 :=
  Program.Arel_view sc_V h.1

/-- The replay certified by `V'` (there is an execution explained by `V'`). -/
theorem replay : ∃ ex, prog.SCCExplains ex V' :=
  let ⟨ex, h⟩ := prog.exists_explains V' total_V'
  ⟨ex, h, sc_V'⟩

theorem dro_ne : prog.DRO (V' 0) ≠ prog.DRO (V 0) := by
  intro h
  have : prog.DRO (V 0) 0 1 := h ▸ (⟨⟨rfl, rfl⟩, rfl⟩ : prog.DRO (V' 0) 0 1)
  exact absurd this.1.1 (by decide)

/-- With Definition 6.4 read literally (`d = false`, self-loops allowed), Theorem 6.6 fails: the
record `Â_i(V) \ (SWO_i(V) ∪ PO ∪ B_i(V))` of this strongly causal `V` is empty but not good. -/
theorem theorem_6_6_literal_false :
    ∃ ex, prog.SCCExplains ex V ∧ (∀ i a b, ¬ prog.rec2 false V i a b) ∧
      ¬ prog.Good2 V (prog.rec2 false V) := by
  obtain ⟨ex, hex⟩ := prog.exists_explains V total_V
  have hempty : ∀ i a b, ¬ prog.rec2 false V i a b := by
    rintro i a b ⟨hc, hs, -, hb⟩
    obtain ⟨rfl, rfl⟩ := cov_eq hc
    fin_cases i
    · -- `(w₁, w₀) ∈ B₀(V)`: `C₀(V, w₁, w₀)` contains the self-loop `(w₀, w₀)`
      refine hb ⟨rfl, trivial, ⟨⟨rfl, rfl⟩, rfl⟩, 0, Or.inr ⟨rfl, 0, TransGen.single
        (Or.inr ⟨0, trivial, trivial, rfl, fun h => absurd h (by decide), ReflGen.single hc.1,
          ReflGen.refl⟩)⟩⟩
    · exact hs ⟨swo_10, by decide⟩
  refine ⟨ex, ⟨hex, sc_V⟩, hempty, fun hg => ?_⟩
  obtain ⟨ex', h'⟩ := replay
  exact dro_ne (hg ex' V' h' (fun i a b h => absurd h (hempty i a b)) 0)

/-- Lemma C.1 with the record as written in Case 1 of its proof (`Â_i(V) \ (SWO(V) ∪ PO ∪ B_i(V))`,
`SWO` instead of the statement's `SWO_i`; any reading `d` of Definition 6.4): the record is empty,
and the certified replay `V'` does not contain the `SWO(V)` pair `(w₁, w₀)`, so Lemma C.1(a)
`SWO(V') ⊇ SWO(V)` would fail. The lemma as stated (with `SWO_i`) holds: `lemma_C_1_a`. -/
theorem lemma_C_1_SWO_record_false (d : Bool) :
    (∀ i a b, ¬ (Cov (prog.Arel V i) a b ∧ ¬ prog.SWO V a b ∧ ¬ prog.po a b ∧
      ¬ prog.B2 d V i a b)) ∧
    prog.StronglyCausal V ∧ prog.StronglyCausal V' ∧ prog.SWO V 1 0 ∧ ¬ prog.SWO V' 1 0 := by
  refine ⟨?_, sc_V, sc_V', swo_10, fun h => ?_⟩
  · rintro i a b ⟨hc, hs, -, -⟩
    obtain ⟨rfl, rfl⟩ := cov_eq hc
    exact hs swo_10
  · exact absurd (Program.SWO_view sc_V' 0 h).1 (by decide)

end Counterexample

end Podc.CausalRecordReplay
