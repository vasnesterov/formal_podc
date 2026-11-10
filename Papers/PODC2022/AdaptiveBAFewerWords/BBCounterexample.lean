import Papers.PODC2022.AdaptiveBAFewerWords.BBModel

/-!
# Lemmas 9 and 11 of [CKS22] fail for the printed Algorithm 2

The leader of a phase relays at line 23 only a value signed by the sender, and otherwise needs
`t + 1` idk shares. But a correct process may hold an idk certificate `QC_idk(j')` from an earlier
phase as its value; it answers a help request with `⟨QC_idk(j'), j⟩` (line 19), which is neither
sender-signed nor an idk share, so its answer is lost.

The run: `n = 3`, `t = 1`, Byzantine `F = {1}`, which is also the sender. Phases `1, 2, 3` are led
by `p₁, p₂, p₀`.
* Round 1: the Byzantine sender sends nothing.
* Phase 1 (leader `p₁`, Byzantine): `p₁` sends `help_req` to `p₂` only; `p₂` answers `⟨idk, 1⟩_{p₂}`;
  with its own share this makes `t + 1 = 2` shares, and `p₁` sends `QC_idk(1)` to `p₂` only, who adopts
  it.
* Phase 2 (leader `p₂`, correct): `p₂` holds a value, the phase is silent.
* Phase 3 (leader `p₀`, correct, `v = ⊥`): `p₀` broadcasts `help_req`; `p₂` answers `⟨QC_idk(1), 3⟩`,
  `p₀` answers `⟨idk, 3⟩_{p₀}`, `p₁` is silent. One idk share `< t + 1` and no sender-signed value:
  `p₀` relays nothing and returns `⊥`.

So `p₀` enters the weak BA (line 9) with `⊥`.

* `lemma9_false`: phase 3 is non-silent with a correct leader, but the correct `p₀` returns `⊥`.
* `lemma11_false`: the correct `p₀` executes line 9 with `⊥`.
* `scX_valid`, `scX_card`: the run respects unforgeability and `|F| ≤ t`, `n = 2t + 1`.
* `keyFact_false` (`n = 5`, `t = 2`, `f = 1`): two non-silent phases with correct leaders, both
  failing; contradicts "after the first non-silent phase by a correct leader, all following phases
  with correct leaders are silent" (Section 5.1).
* `fixed_ok`: with the repaired rule (relay any `BB_valid` value) every correct process ends with a
  value in this run.
-/

namespace Podc.AdaptiveBAFewerWords.BB.Counterexample

open Podc.AdaptiveBAFewerWords.BB

/-- The Byzantine messages: in phase 1, `p₁` sends `help_req` (round `1`) and then `QC_idk(1)`
(round `3`) to `p₂` only. -/
def advX (r : ℕ) (b w : Fin 3) : List (Msg 3 Bool) :=
  if r = 1 ∧ b = 1 ∧ w = 2 then [.helpReq 1]
  else if r = 3 ∧ b = 1 ∧ w = 2 then [.relay (.qc 1) 1]
  else []

/-- The scenario: Byzantine `{1}`, sender `p₁`, input `true`. -/
def scX : Scenario 3 Bool where
  F := {1}
  sender := 1
  inp := true
  adv := advX

/-- `n = 2t + 1` and `|F| ≤ t` for `t = 1`. -/
theorem scX_card : 3 = 2 * 1 + 1 ∧ scX.F.card ≤ 1 := by decide

/-- The run respects unforgeability (`QC_idk(1)` is built from the shares of `p₁` and `p₂`; `p₂` sent
its share in round `2`). -/
theorem scX_valid : AdvValid 1 .printed scX := by
  intro r b w m hb hw hm
  simp only [scX, advX] at hb hm
  split_ifs at hm with h1 h2
  · simp at hm; subst hm; trivial
  · simp only [List.mem_singleton] at hm
    subst hm
    obtain ⟨rfl, rfl, rfl⟩ := h2
    refine ⟨{1, 2}, by decide, ?_⟩
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr ⟨2, by omega, 2, 1, by decide, by decide +kernel⟩
  · simp at hm

/-- `p₀` returns `⊥` from phase 3 although phase 3 is non-silent with a correct leader
(contradicts Lemma 9 of [CKS22]). -/
theorem lemma9_false :
    NonSilent 1 .printed scX 3 ∧ (0 : Fin 3) ∉ scX.F ∧
      ret 1 .printed scX 3 (vPh 1 .printed scX 2) 0 = none := by
  unfold NonSilent; decide +kernel

/-- The correct `p₀` executes line 9 with `⊥` (contradicts Lemma 11 of [CKS22]). -/
theorem lemma11_false : (0 : Fin 3) ∉ scX.F ∧ vEnd 1 .printed scX 0 = none := by
  decide +kernel

/-- With the repaired rule all correct processes end with a `BB_valid` value in this run. -/
theorem fixed_ok : vEnd 1 .fixed scX 0 = some (.qc 1) ∧ vEnd 1 .fixed scX 2 = some (.qc 1) := by
  decide +kernel

/-! ### `f = 1 < t`: two failing non-silent phases (the key fact of Section 5.1 fails)

`n = 5`, `t = 2`, Byzantine `F = {1}` = sender. Phase 1: `p₁` asks `p₂, p₃` for help, builds
`QC_idk(1)` from the shares of `p₁, p₂, p₃` and sends it to `p₂, p₃` only. Phases 2, 3 are silent;
in phases 4 and 5 the correct leaders `p₄`, `p₀` receive two `⟨QC_idk(1), j⟩` answers and only two
idk shares (`< t + 1 = 3`): both phases are non-silent and both fail. With `t` processes holding a
certificate the same happens in `t` phases, i.e. `Θ(n²)` words with `f = 1` for the printed rule
(this generalization is not formalized). -/

/-- The Byzantine messages of the `n = 5` run. -/
def advY (r : ℕ) (b w : Fin 5) : List (Msg 5 Bool) :=
  if r = 1 ∧ b = 1 ∧ (w = 2 ∨ w = 3) then [.helpReq 1]
  else if r = 3 ∧ b = 1 ∧ (w = 2 ∨ w = 3) then [.relay (.qc 1) 1]
  else []

/-- The `n = 5` scenario: Byzantine `{1}`, sender `p₁`. -/
def scY : Scenario 5 Bool where
  F := {1}
  sender := 1
  inp := true
  adv := advY

theorem scY_card : 5 = 2 * 2 + 1 ∧ scY.F.card ≤ 1 := by decide

theorem scY_valid : AdvValid 2 .printed scY := by
  intro r b w m hb hw hm
  simp only [scY, advY] at hb hm
  split_ifs at hm with h1 h2
  · simp at hm; subst hm; trivial
  · simp only [List.mem_singleton] at hm
    subst hm
    obtain ⟨rfl, -, -⟩ := h2
    refine ⟨{1, 2, 3}, by decide, ?_⟩
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact Or.inl (by decide)
    · exact Or.inr ⟨2, by omega, 2, 1, by decide, by decide +kernel⟩
    · exact Or.inr ⟨2, by omega, 3, 1, by decide, by decide +kernel⟩
  · simp at hm

/-- Phases 4 and 5 both have correct leaders and are non-silent (contradicts the key fact of
Section 5.1), and `p₄`, `p₀` enter the weak BA with `⊥` although only one process is faulty. -/
theorem keyFact_false :
    NonSilent 2 .printed scY 4 ∧ NonSilent 2 .printed scY 5 ∧
      vEnd 2 .printed scY 4 = none ∧ vEnd 2 .printed scY 0 = none := by
  unfold NonSilent; decide +kernel

end Podc.AdaptiveBAFewerWords.BB.Counterexample
