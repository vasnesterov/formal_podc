import Papers.PODC2017.ZigzagCausality.Coordination

/-!
# Non-vacuity of Theorem 3: a flooding full-information protocol implementing `Late`

The fork of Figure 1: `C = 0` sends to `A = 1` and `B = 2`, with `U_CA = 1` and `L_CB = U_CB = 2`,
so `L_CB ≥ U_CA + 1`. All processes flood their full local state (an FFIP). `B` performs `b` when
it receives from `C` a state in which `C` has just received `μ_go`. This implements
`Late⟨a --1--> b⟩` (`implementsLate`), and in a concrete run `C` receives `μ_go` and `B` performs
`b` (`performs_exists`), so the hypotheses of `thm3_late` are satisfiable.
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

namespace NonVacuity

open Sys

/-- Channels `0 → 1`, `0 → 2`. -/
def ch : Fin 3 → Fin 3 → Bool
  | 0, 1 => true
  | 0, 2 => true
  | _, _ => false

/-- Bounds: `L₀₁ = U₀₁ = 1`, `L₀₂ = U₀₂ = 2`. -/
def lu : Fin 3 → Fin 3 → ℕ
  | 0, 2 => 2
  | _, _ => 1

def net : Net (Fin 3) where
  Chan i j := ch i j = true
  L := lu
  U := lu
  one_le_L i j _ := by fin_cases i <;> fin_cases j <;> decide
  L_le_U _ _ _ := le_rfl

abbrev LS := LState (Fin 3) Unit ℕ Unit
abbrev BN := BNode (Fin 3) Unit ℕ Unit

instance : Countable LS := by
  refine Function.Injective.countable
    (f := fun ℓ : LS => (ℓ.init, ℓ.hist.map fun b => (b.msgs, b.ext))) ?_
  rintro ⟨a, h⟩ ⟨a', h'⟩ he
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, he⟩ := he
  have ha : a = a' := Subsingleton.elim _ _
  subst ha
  have : h = h' := by
    refine List.map_injective_iff.2 ?_ he
    rintro ⟨m, e⟩ ⟨m', e'⟩ hh
    simp only [Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    rfl
  rw [this]

noncomputable def enc : LS → ℕ := Classical.choose (Countable.exists_injective_nat LS)

theorem enc_injective : Function.Injective enc :=
  Classical.choose_spec (Countable.exists_injective_nat LS)

/-- The flooding full-information protocol. -/
noncomputable def γ : Sys (Fin 3) Unit ℕ Unit where
  net := net
  send i ℓ j := if ch i j = true then some (enc ℓ) else none
  G0 := Set.univ

theorem isFFIP : γ.IsFFIP := by
  refine ⟨?_, ?_⟩
  · intro i j j' ℓ ℓ' m h h'
    simp only [γ] at h h'
    split_ifs at h h'
    cases h; exact enc_injective (Option.some.inj h'.symm)
  · intro i ℓ j hc
    simp only [γ]
    rw [if_pos (show ch i j = true from hc)]; rfl

/-- `C` has just received `μ_go`. -/
def goState (ℓ : LS) : Prop := ∃ b, ℓ.hist.getLast? = some b ∧ () ∈ b.ext

/-- `B` performs `b` when its last batch contains a message from `C` whose content is a state of
`C` that has just received `μ_go`. -/
def doB (ℓ : LS) : Prop :=
  ∃ b, ℓ.hist.getLast? = some b ∧ ∃ ℓC, ((0 : Fin 3), enc ℓC) ∈ b.msgs ∧ goState ℓC

/-- The coordination task: `A = 1`, `B = 2`, `C = 0`. -/
def T : CoordTask (Fin 3) Unit ℕ Unit := ⟨1, 2, 0, (), doB⟩

theorem exists_recv {r : Sched (Fin 3) Unit Unit} (hr : γ.Valid r) {σ : BN}
    (ha : γ.appears r σ) (h0 : 0 < γ.timer r σ) {j : Fin 3} (hc : ch σ.1 j = true) :
    ∃ σ', γ.recv r σ j = some σ' ∧ σ'.1 = j ∧ γ.appears r σ' ∧
      γ.timer r σ' = γ.timer r σ + lu σ.1 j := by
  obtain ⟨σ', h⟩ := Option.isSome_iff_exists.1 (recv_isSome_of_FFIP isFFIP ha h0 hc)
  have sp := recv_spec hr h
  exact ⟨σ', h, sp.1, sp.2.1, le_antisymm sp.2.2.2.2.2 sp.2.2.2.2.1⟩

/-- **The protocol implements `Late⟨a --1--> b⟩`.** -/
theorem implementsLate : γ.ImplementsLate T 1 := by
  intro r hr σ ⟨ha, hB, b, hlast, ℓC, hm, hgo⟩
  obtain ⟨σC, hC0, hrecv, hsend⟩ := exists_recv_of_mem_last hr ha hlast hm
  have hσC : σC.2 = ℓC := by
    simp only [γ, hB, T] at hsend
    split_ifs at hsend
    exact enc_injective (Option.some.inj hsend)
  have sB := recv_spec hr hrecv
  obtain ⟨haC, h0C⟩ := recv_appears_left hrecv
  obtain ⟨α, hA, pA, aA, tA⟩ := exists_recv hr haC h0C (j := 1) (by rw [hC0]; rfl)
  refine ⟨σC, ⟨haC, hC0, ?_⟩, α, σ, by simp [CoordTask.aNode, T, basic, hA, aA],
    γ.basic_ofB r ha, ?_⟩
  · rw [hσC]; exact hgo
  · rw [hC0] at tA sB
    rw [hB] at sB
    have h1 := sB.2.2.2.2.1
    change γ.timer r σC + lu 0 2 ≤ γ.timer r σ at h1
    simp only [lu] at tA h1
    omega

/-- A run: `C` receives `μ_go` at time 1, messages take their exact delays. -/
def r₀ : Sched (Fin 3) Unit Unit where
  g _ := ()
  dlv i s j := s + lu i j
  ext t p := if t = 1 ∧ p = 0 then {()} else ∅

theorem valid_r₀ : γ.Valid r₀ where
  init := Set.mem_univ _
  bounds _ _ _ _ := ⟨le_rfl, le_rfl⟩
  ext_unique e t j t' j' h h' := by
    simp only [r₀] at h h'
    split_ifs at h h' <;> simp_all

/-- **Non-vacuity**: in `r₀`, `C` receives `μ_go` (at `σC`) and `B` performs `b`. So all
hypotheses of `thm3_late` hold for this system. -/
theorem performs_exists : ∃ σC σ, γ.GoNode r₀ T σC ∧ γ.Performs r₀ T σ := by
  have ha : γ.Active r₀ 0 (0 + 1) := by
    rw [active_succ_iff]
    rintro ⟨-, he⟩
    rw [batch_ext] at he
    simp [r₀] at he
  set σC : BN := (0, γ.st r₀ 1 0)
  have hap : γ.appears r₀ σC := γ.appears_st _ _ _
  have ht : γ.timer r₀ σC = 1 := γ.timer_eq_of_active r₀ ha
  have hgo : goState σC.2 := by
    refine ⟨γ.batch r₀ 0 0, ?_, ?_⟩
    · simp [σC, γ.st_succ_of_active r₀ ha]
    · rw [batch_ext]; simp [r₀]
  obtain ⟨β, hβ, pβ, aβ, -⟩ := exists_recv valid_r₀ hap (by omega) (j := 2) rfl
  obtain ⟨m, hm, b, hb, hmem⟩ := recv_mem_last valid_r₀ hβ
  have hm' : m = enc σC.2 := by
    simp only [γ] at hm; split_ifs at hm; exact (Option.some.inj hm).symm
  refine ⟨σC, β, ⟨hap, rfl, hgo⟩, aβ, pβ, b, hb, σC.2, ?_, hgo⟩
  rw [← hm']; exact hmem

end NonVacuity

end Podc.ZigzagCausality
