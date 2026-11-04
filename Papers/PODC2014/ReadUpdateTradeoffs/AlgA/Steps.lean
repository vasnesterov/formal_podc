import Papers.PODC2014.ReadUpdateTradeoffs.AlgA.Layout
import Papers.PODC2014.ReadUpdateTradeoffs.AlgA.MemInv

/-!
# Algorithm A: wait-freedom and step complexity (Theorem 6)

A potential `μ` on local states that drops at every base-object access of a process:
`ReadMax` costs `1` access, `WriteMax(v)` at most `2 + 8 · log₂(leaf position)` accesses
(one read of the own `T_R` leaf, one leaf write, and `4` accesses per refresh, `2` refreshes per
ancestor; the leaf at heap position `x` has `⌊log₂ x⌋` ancestors). With the concrete layout
`stdLayout N` (`AlgA/Layout.lean`) this is `≤ 16 · ⌊log₂ min(N, v+1)⌋ + 18`, i.e.
`O(min(log N, log v))` (for `v ≥ 1`).
-/

namespace Podc.ReadUpdateTradeoffs.AlgA

open Cslib.SharedMemory

variable {N : ℕ}

/-- The remaining number of base-object accesses of a process in local state `l`. -/
def μ (lay : Layout N) (p : Fin N) : Loc → ℕ
  | .idle | .rDone _ | .wDone => 0
  | .rRoot => 1
  | .wRead _ => 2 + 8 * Nat.log 2 (lay.leaf (.inr p))
  | .wLeaf _ x => 1 + 8 * Nat.log 2 x
  | .pOld _ c j => 8 * (Nat.log 2 c - 1) + if j then 4 else 8
  | .pL _ c j _ => 8 * (Nat.log 2 c - 1) + if j then 3 else 7
  | .pR _ c j _ _ => 8 * (Nat.log 2 c - 1) + if j then 2 else 6
  | .pCas _ c j _ _ _ => 8 * (Nat.log 2 c - 1) + if j then 1 else 5

lemma μ_up (lay : Layout N) (p : Fin N) (v x : ℕ) : μ lay p (up v x) ≤ 8 * Nat.log 2 x := by
  unfold up
  split_ifs with h
  · simp [μ]
  · have : 1 ≤ Nat.log 2 x := Nat.le_log_of_pow_le (by norm_num) (by omega)
    simp only [μ, Bool.false_eq_true, ite_false]
    omega

/-- Every access strictly decreases the potential. -/
lemma μ_decreases (lay : Layout N) :
    ∀ p l i o k, (impl lay).act p l = .access i o k → ∀ x, μ lay p (k x) < μ lay p l := by
  intro p l i o k h x
  cases l <;> simp only [impl] at h <;> cases h
  · simp [μ]
  · dsimp only
    split_ifs <;> simp [μ]
  · rename_i v
    have := μ_up lay p v i
    have h2 : μ lay p (.wLeaf v i) = 1 + 8 * Nat.log 2 i := rfl
    dsimp only
    omega
  · simp only [μ]; split_ifs <;> omega
  · simp only [μ]; split_ifs <;> omega
  · simp only [μ]; split_ifs <;> omega
  · rename_i v c j old l r
    cases j with
    | false => simp [μ]
    | true =>
      simp only [ite_true]
      have h0 : μ lay p (.pCas v c true old l r) = 8 * (Nat.log 2 c - 1) + 1 := rfl
      rw [h0]
      by_cases hc : c / 2 ≤ 1
      · simp [up, hc, μ]
      · have h1 := μ_up lay p v (c / 2)
        have h2 : Nat.log 2 (c / 2) = Nat.log 2 c - 1 := by
          rw [Nat.log_div_base]
        omega

/-- **Theorem 6** of [Hendler–Khait, PODC'14], wait-freedom: Algorithm A is wait-free. -/
theorem waitFree (lay : Layout N) : (impl lay).WaitFree :=
  (impl lay).waitFree_of_potential (μ lay) (μ_decreases lay)

/-- **Theorem 6**, `ReadMax`: a `ReadMax` takes at most one access (a read of the root) before it
returns. -/
theorem readMax_steps_le (lay : Layout N) {α γ : List (Label (Fin N) maxRegObj)} {p : Fin N}
    (hv : (impl lay).Valid (α ++ .inv p .readMax :: γ)) (hret : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ 1 := by
  obtain ⟨l, h⟩ := (impl lay).tauSteps_le_potential_invoke (μ lay) (μ_decreases lay) hv hret
  simpa [impl, μ] using h

-- CSLib candidate
/-- A pending process that takes no step (no internal step, no response) along an execution
fragment keeps its local state. -/
lemma _root_.Cslib.SharedMemory.Impl.runFrom_loc_of_no_step {A : ObjSpec} {ι : Type}
    {B : ι → ObjSpec} {P L : Type} [DecidableEq P] [DecidableEq ι] (I : Impl A B P L) {p : P} :
    ∀ {γ : List (Label P A)} {C C' : Config A B P L}, I.runFrom C γ = some C' →
      C.pend p ≠ none → γ.countP (Label.isTauOf p) = 0 → (∀ r, .ret p r ∉ γ) →
      C'.loc p = C.loc p ∧ C'.pend p ≠ none
  | [], C, C', h, hp, _, _ => by
    simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; exact ⟨rfl, hp⟩
  | ℓ :: γ, C, C', h, hp, ht, hr => by
    simp only [Impl.runFrom_cons] at h
    cases hs : I.step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      simp only [hs, Option.bind_some] at h
      have hne : ℓ.proc ≠ p := by
        intro hq
        cases ℓ with
        | inv q o => simp only [Label.proc] at hq; subst hq; exact hp (Impl.step_inv hs).1
        | tau q => simp only [Label.proc] at hq; subst hq; simp at ht
        | ret q r => simp only [Label.proc] at hq; subst hq; exact hr r (by simp)
      have h1 := I.step_other hs hne
      have ht' : γ.countP (Label.isTauOf p) = 0 := by
        cases ℓ <;> simp_all [List.countP_cons]
      have := I.runFrom_loc_of_no_step h (by rw [h1.2]; exact hp) ht'
        (fun r hm => hr r (by simp [hm]))
      exact ⟨this.1.trans h1.1, this.2⟩

/-- **Theorem 6**, `ReadMax`: a complete `ReadMax` takes **exactly one** access. -/
theorem readMax_steps_eq (lay : Layout N) {α γ : List (Label (Fin N) maxRegObj)} {p : Fin N}
    {r : ℕ} (hv : (impl lay).Valid (α ++ .inv p .readMax :: γ ++ [.ret p r]))
    (hret : ∀ r, .ret p r ∉ γ) : γ.countP (Label.isTauOf p) = 1 := by
  have hv' : (impl lay).Valid (α ++ .inv p .readMax :: γ) :=
    Impl.Valid.of_append (impl lay) (β := [.ret p (r : ℕ)]) (by simpa using hv)
  have hle := readMax_steps_le lay hv' hret
  refine le_antisymm hle (Nat.one_le_iff_ne_zero.2 fun h0 => ?_)
  obtain ⟨C, hC⟩ := hv
  rw [Impl.run, List.append_assoc, Impl.runFrom_append] at hC
  cases hα : (impl lay).runFrom (impl lay).initCfg α with
  | none => simp [hα] at hC
  | some C₀ =>
    simp only [hα, Option.bind_some, List.cons_append, Impl.runFrom_cons] at hC
    cases hi : (impl lay).step C₀ (.inv p .readMax) with
    | none => simp [hi] at hC
    | some C₁ =>
      simp only [hi, Option.bind_some, Impl.runFrom_append] at hC
      obtain ⟨-, -, hpend, hloc, -⟩ := Impl.step_inv hi
      have hp1 : C₁.pend p ≠ none := by simp [hpend]
      have hl1 : C₁.loc p = .rRoot := by simp [hloc, impl]
      cases hg : (impl lay).runFrom C₁ γ with
      | none => simp [hg] at hC
      | some C₂ =>
        simp only [hg, Option.bind_some, Impl.runFrom_singleton] at hC
        obtain ⟨hl2, -⟩ := (impl lay).runFrom_loc_of_no_step hg hp1 h0 hret
        obtain ⟨-, -, -, l, hact, -⟩ := Impl.step_ret hC
        rw [hl2, hl1] at hact
        simp [impl] at hact

/-- **Theorem 6**, `WriteMax` (any layout): a `WriteMax(v)` of process `p` takes at most
`2 + 8 · ⌊log₂ x⌋` accesses, where `x` is the position of the leaf it writes. -/
theorem writeMax_steps_le' (lay : Layout N) {α γ : List (Label (Fin N) maxRegObj)} {p : Fin N}
    {v : ℕ} (hv : (impl lay).Valid (α ++ .inv p (.writeMax v) :: γ))
    (hret : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ 2 + 8 * Nat.log 2 (lay.leafOf p v) := by
  obtain ⟨l, h⟩ := (impl lay).tauSteps_le_potential_invoke (μ lay) (μ_decreases lay) hv hret
  refine h.trans ?_
  simp only [impl]
  split_ifs with hvN
  · simp [μ]
  · simp [μ, lay.leafOf_of_le p (not_lt.1 hvN)]

/-- **Theorem 6**, `WriteMax` (concrete `B₁`-like layout): a `WriteMax(v)` takes at most
`16 · ⌊log₂ min(N, v+1)⌋ + 18 = O(min(log N, log v))` accesses. -/
theorem writeMax_steps_le {α γ : List (Label (Fin N) maxRegObj)} {p : Fin N} {v : ℕ}
    (hv : (impl (stdLayout N)).Valid (α ++ .inv p (.writeMax v) :: γ))
    (hret : ∀ r, .ret p r ∉ γ) :
    γ.countP (Label.isTauOf p) ≤ 16 * Nat.log 2 (min N (v + 1)) + 18 := by
  have h1 := writeMax_steps_le' (stdLayout N) hv hret
  have h2 := log_leafOf_le N p v
  omega

end Podc.ReadUpdateTradeoffs.AlgA
