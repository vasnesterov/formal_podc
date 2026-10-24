import Papers.PODC2015.AlmostStableMatchings.Main

/-!
# A run in which a man becomes bad while inactive

The proof of Lemma 4.4 in the paper charges every man who is bad at the end of `ASM` to the
iteration `i` in which he became bad, and bounds those men with Lemma 4.5 applied to the active
men of iteration `i`. But a man can become bad while he is *inactive*: he is matched when he
leaves the active set and is later displaced by an active man. Lemma 4.5 says nothing about such
men. (Lemma 4.4 itself is true; see `BadMen.lean`.)

Instance (`P5`): 5 men, 5 women, 16 edges; `k = 2` quantiles, `ℓ = 1`, iterations `0, 1, 2`,
and the greedy maximal matching (edges scanned in lexicographic order). In iteration 1 man 3
displaces man 0, who ends iteration 1 unmatched with `|Q| = 4`. In iteration 2 only man 0 is
active; he proposes to woman 3 and displaces man 2, who is inactive (`|Q| = 3 < 4`) and remains
unmatched with `Q = {1, 2}` forever. So man 2 is bad at the end, although he was matched when he
left the active set and was never active again (`bad_while_inactive`).
-/

namespace Papers.PODC2015.AlmostStableMatchings.Example

open Prefs

/-- The preferences of the example (lists favourite first). -/
def P5 : Prefs (Fin 5) (Fin 5) where
  man := ![[0, 3, 4, 1, 2], [2, 4, 1, 0], [3, 1, 2], [2, 3, 4, 0], []]
  woman := ![[3, 0, 1], [2, 0, 1], [2, 0, 1, 3], [0, 2, 3], [0, 3, 1]]
  nodup_man := by decide
  nodup_woman := by decide
  mem_iff := by decide

/-- Greedy maximal matching: scan the edges in lexicographic order. -/
def greedyList (G : Fin 5 → Fin 5 → Bool) : List (Fin 5 × Fin 5) :=
  ((List.finRange 5).flatMap fun m => (List.finRange 5).map fun w => (m, w)).foldl
    (fun acc e => if G e.1 e.2 && acc.all (fun e' => e'.1 != e.1 && e'.2 != e.2)
      then acc ++ [e] else acc) []

/-- The greedy matching in partner form. -/
def greedy (G : Fin 5 → Fin 5 → Bool) : BMatching (Fin 5) (Fin 5) :=
  ⟨fun m => ((greedyList G).find? (·.1 == m)).map Prod.snd,
    fun w => ((greedyList G).find? (·.2 == w)).map Prod.fst⟩

instance (μ : BMatching (Fin 5) (Fin 5)) (G : Fin 5 → Fin 5 → Bool) :
    Decidable (μ.IsMaximalIn G) := by unfold BMatching.IsMaximalIn; infer_instance

/-- The greedy subroutine (it is maximal on every graph; we only use that it is when the check
succeeds, which `decide` confirms on all graphs met in the run). -/
noncomputable def mm5 : MMOracle (Fin 5) (Fin 5) where
  run G := if (greedy G).IsMaximalIn G then greedy G else (exists_maximal G).choose
  isMaximal G := by
    by_cases h : (greedy G).IsMaximalIn G
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]; exact (exists_maximal G).choose_spec
  rounds := 0

instance : DecidableEq (ManSt (Fin 5)) := fun a b =>
  decidable_of_iff (a.Q = b.Q ∧ a.p = b.p ∧ a.A = b.A) (by cases a; cases b; simp)

instance : DecidableEq (St (Fin 5) (Fin 5)) := fun a b =>
  decidable_of_iff (a.man = b.man ∧ a.pw = b.pw) (by cases a; cases b; simp)

def S0 : St (Fin 5) (Fin 5) := ⟨![⟨{0, 1, 2, 3, 4}, none, ∅⟩, ⟨{0, 1, 2, 4}, none, ∅⟩, ⟨{1, 2, 3}, none, ∅⟩, ⟨{0, 2, 3, 4}, none, ∅⟩, ⟨∅, none, ∅⟩], ![none, none, none, none, none]⟩
def S1 : St (Fin 5) (Fin 5) := ⟨![⟨{0, 1, 2, 3, 4}, none, {0, 3}⟩, ⟨{0, 1, 2, 4}, none, {2, 4}⟩, ⟨{1, 2, 3}, none, {3}⟩, ⟨{0, 2, 3, 4}, none, {2, 3}⟩, ⟨∅, none, ∅⟩], ![none, none, none, none, none]⟩
def S2 : St (Fin 5) (Fin 5) := ⟨![⟨{0, 1, 2, 3, 4}, some 0, ∅⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2, 3}, none, {3}⟩, ⟨{0, 3, 4}, none, {3}⟩, ⟨∅, none, ∅⟩], ![some 0, none, some 1, none, none]⟩
def S3 : St (Fin 5) (Fin 5) := ⟨![⟨{0, 1, 2, 3, 4}, some 0, ∅⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2, 3}, some 3, ∅⟩, ⟨{0, 4}, none, ∅⟩, ⟨∅, none, ∅⟩], ![some 0, none, some 1, some 2, none]⟩
def S4 : St (Fin 5) (Fin 5) := ⟨![⟨{0, 1, 2, 3, 4}, some 0, ∅⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2, 3}, some 3, ∅⟩, ⟨{0, 4}, none, {0, 4}⟩, ⟨∅, none, ∅⟩], ![some 0, none, some 1, some 2, none]⟩
def S5 : St (Fin 5) (Fin 5) := ⟨![⟨{1, 2, 3, 4}, none, ∅⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2, 3}, some 3, ∅⟩, ⟨{0, 4}, some 0, ∅⟩, ⟨∅, none, ∅⟩], ![some 3, none, some 1, some 2, none]⟩
def S6 : St (Fin 5) (Fin 5) := ⟨![⟨{1, 2, 3, 4}, none, ∅⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2, 3}, some 3, ∅⟩, ⟨{0, 4}, some 0, ∅⟩, ⟨∅, none, ∅⟩], ![some 3, none, some 1, some 2, none]⟩
def S7 : St (Fin 5) (Fin 5) := ⟨![⟨{1, 2, 3, 4}, none, {3}⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2, 3}, some 3, ∅⟩, ⟨{0, 4}, some 0, ∅⟩, ⟨∅, none, ∅⟩], ![some 3, none, some 1, some 2, none]⟩
def S8 : St (Fin 5) (Fin 5) := ⟨![⟨{1, 2, 3, 4}, some 3, ∅⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2}, none, ∅⟩, ⟨{0, 4}, some 0, ∅⟩, ⟨∅, none, ∅⟩], ![some 3, none, some 1, some 0, none]⟩
def S9 : St (Fin 5) (Fin 5) := ⟨![⟨{1, 2, 3, 4}, some 3, ∅⟩, ⟨{1, 2, 4}, some 2, ∅⟩, ⟨{1, 2}, none, ∅⟩, ⟨{0, 4}, some 0, ∅⟩, ⟨∅, none, ∅⟩], ![some 3, none, some 1, some 0, none]⟩

lemma e0 : P5.init = S0 := by decide +kernel
lemma e1 : P5.initQM 2 (P5.active 0 S0) S0 = S1 := by decide +kernel
lemma e2 : P5.prStep 2 mm5 S1 = S2 := by decide +kernel
lemma e3 : P5.prStep 2 mm5 S2 = S3 := by decide +kernel
lemma e4 : P5.initQM 2 (P5.active 1 S3) S3 = S4 := by decide +kernel
lemma e5 : P5.prStep 2 mm5 S4 = S5 := by decide +kernel
lemma e6 : P5.prStep 2 mm5 S5 = S6 := by decide +kernel
lemma e7 : P5.initQM 2 (P5.active 2 S6) S6 = S7 := by decide +kernel
lemma e8 : P5.prStep 2 mm5 S7 = S8 := by decide +kernel
lemma e9 : P5.prStep 2 mm5 S8 = S9 := by decide +kernel

lemma stage1 : P5.stage 2 mm5 1 1 = S3 := by
  show P5.prStep 2 mm5 (P5.prStep 2 mm5 (P5.initQM 2 (P5.active 0 P5.init) P5.init)) = S3
  rw [e0, e1, e2, e3]

lemma stage2 : P5.stage 2 mm5 1 2 = S6 := by
  show P5.prStep 2 mm5 (P5.prStep 2 mm5 (P5.initQM 2 (P5.active 1 (P5.stage 2 mm5 1 1))
    (P5.stage 2 mm5 1 1))) = S6
  rw [stage1, e4, e5, e6]

lemma stage3 : P5.asm 2 mm5 1 2 = S9 := by
  show P5.prStep 2 mm5 (P5.prStep 2 mm5 (P5.initQM 2 (P5.active 2 (P5.stage 2 mm5 1 2))
    (P5.stage 2 mm5 1 2))) = S9
  rw [stage2, e7, e8, e9]

/-- **A bad man who became bad while inactive.** In the run of `ASM` (`k = 2`, `ℓ = 1`, `L = 2`)
on `P5`, man 2 is active in iteration 1, matched at its end, inactive in iteration 2, and bad at
the end of `ASM`. -/
theorem bad_while_inactive :
    (2 : Fin 5) ∈ P5.active 1 (P5.stage 2 mm5 1 1) ∧
    (P5.stage 2 mm5 1 2).pm 2 ≠ none ∧
    (2 : Fin 5) ∉ P5.active 2 (P5.stage 2 mm5 1 2) ∧
    (2 : Fin 5) ∈ badSet (P5.asm 2 mm5 1 2) := by
  rw [stage1, stage2, stage3]; decide +kernel

end Papers.PODC2015.AlmostStableMatchings.Example
