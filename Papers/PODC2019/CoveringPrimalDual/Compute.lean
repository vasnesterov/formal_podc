import Papers.PODC2019.CoveringPrimalDual.Invariants

/-!
# A computable rational mirror of Algorithm MWHVC

To exhibit concrete executions (counterexamples) we re-implement one iteration over `ℚ`
(`stepQ`), with the `while` loop of step 3d run with a fuel bound, and prove that it agrees with the
real-valued model `step` whenever the fuel sufficed (`step_castS`), a condition checked by
`decide` (`FuelOK`). Concrete runs are then evaluated by `decide` in the kernel.
-/

set_option linter.unusedSectionVars false

namespace Podc.CoveringPrimalDual

open Finset Cslib.Hypergraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

instance Inst.decActive (I : Inst V E) (C : Finset V) (v : V) : Decidable (I.Active C v) := by
  unfold Inst.Active; infer_instance

/-- A rational instance. -/
structure InstQ (V E : Type*) where
  inc : E → Finset V
  w : V → ℚ
  inc_nonempty : ∀ e, (inc e).Nonempty
  w_pos : ∀ v, 0 < w v

/-- Rational parameters. -/
structure ParamsQ where
  f : ℕ
  ε : ℚ
  α : ℚ
  κ : ℚ
  c₀ : ℚ

/-- A rational state. -/
structure StateQ (V E : Type*) where
  C : Finset V
  level : V → ℕ
  deal : E → ℚ
  δ : E → ℚ

/-- The real instance of a rational one. -/
def InstQ.toReal (I : InstQ V E) : Inst V E :=
  ⟨I.inc, fun v => (I.w v : ℝ), I.inc_nonempty, fun v => by exact_mod_cast I.w_pos v⟩

@[simp] theorem InstQ.toReal_inc (I : InstQ V E) : I.toReal.inc = I.inc := rfl

@[simp] theorem InstQ.toReal_w (I : InstQ V E) (v : V) : I.toReal.w v = (I.w v : ℝ) := rfl

/-- The real parameters of rational ones. -/
def ParamsQ.toReal (P : ParamsQ) : Params := ⟨P.f, P.ε, P.α, P.κ, P.c₀⟩

/-- The real state of a rational one. -/
def StateQ.toReal (s : StateQ V E) : State V E :=
  ⟨s.C, s.level, fun e => (s.deal e : ℝ), fun e => (s.δ e : ℝ)⟩

/-- The `while` loop of step 3d with fuel. -/
def lvlUpQ : ℕ → ℕ → ℚ → ℚ → ℕ
  | 0, ℓ, _, _ => ℓ
  | n + 1, ℓ, s, w => if s ≤ w * (1 - (1 / 2) ^ (ℓ + 1)) then ℓ else lvlUpQ n (ℓ + 1) s w

variable (I : InstQ V E) (P : ParamsQ)

/-- The fuel used for the loop of step 3d. -/
def fuel : ℕ := 64

def loadQ (δ : E → ℚ) (v : V) : ℚ := ∑ e ∈ edgesAt I.inc v, δ e

def betaQ : ℚ := P.ε / (P.f + P.ε)

def deal0Q (e : E) : ℚ :=
  P.c₀ * (I.inc e).inf' (I.inc_nonempty e) fun v => I.w v / (edgesAt I.inc v).card

def initQ : StateQ V E := ⟨∅, fun _ => 0, deal0Q I P, deal0Q I P⟩

def joinCQ (s : StateQ V E) : Finset V :=
  s.C ∪ univ.filter fun v => v ∉ s.C ∧ (1 - betaQ P) * I.w v ≤ loadQ I s.δ v

def lvl1Q (s : StateQ V E) (v : V) : ℕ :=
  if I.toReal.Active (joinCQ I P s) v then lvlUpQ fuel (s.level v) (loadQ I s.δ v) (I.w v)
  else s.level v

def deal1Q (s : StateQ V E) (e : E) : ℚ :=
  if I.toReal.Covered (joinCQ I P s) e then s.deal e
  else s.deal e * (1 / 2) ^ (∑ v ∈ I.inc e, (lvl1Q I P s v - s.level v))

def RaiseQ (s : StateQ V E) (v : V) : Prop :=
  ∑ e ∈ I.toReal.uncov (joinCQ I P s) v, deal1Q I P s e ≤
    P.α⁻¹ * (1 / 2) ^ (lvl1Q I P s v + 1) * I.w v

instance (s : StateQ V E) (v : V) : Decidable (RaiseQ I P s v) := by
  unfold RaiseQ; infer_instance

def deal2Q (s : StateQ V E) (e : E) : ℚ :=
  if ¬ I.toReal.Covered (joinCQ I P s) e ∧ ∀ v ∈ I.inc e, RaiseQ I P s v then
    P.α * deal1Q I P s e else deal1Q I P s e

def stepQ (s : StateQ V E) : StateQ V E :=
  ⟨joinCQ I P s, lvl1Q I P s, deal2Q I P s, fun e =>
    if I.toReal.Covered (joinCQ I P s) e then s.δ e else s.δ e + P.κ * deal2Q I P s e⟩

def runQ : ℕ → StateQ V E
  | 0 => initQ I P
  | n + 1 => stepQ I P (runQ n)

/-- The fuel of the loop sufficed in the next iteration from `s`. -/
def FuelOK (s : StateQ V E) : Prop :=
  ∀ v, I.toReal.Active (joinCQ I P s) v →
    loadQ I s.δ v ≤ I.w v * (1 - (1 / 2) ^ (lvlUpQ fuel (s.level v) (loadQ I s.δ v) (I.w v) + 1))

instance (s : StateQ V E) : Decidable (FuelOK I P s) := by unfold FuelOK; infer_instance

/-! ### Soundness -/

theorem le_lvlUpQ : ∀ (n ℓ : ℕ) (s w : ℚ), ℓ ≤ lvlUpQ n ℓ s w
  | 0, _, _, _ => le_rfl
  | n + 1, ℓ, s, w => by
    unfold lvlUpQ; split_ifs
    · exact le_rfl
    · exact (Nat.le_succ ℓ).trans (le_lvlUpQ n (ℓ + 1) s w)

theorem lvlUpQ_min : ∀ (n ℓ : ℕ) (s w : ℚ) (k : ℕ), ℓ ≤ k → k < lvlUpQ n ℓ s w →
    ¬ s ≤ w * (1 - (1 / 2) ^ (k + 1))
  | 0, ℓ, _, _, k, h1, h2 => by simp [lvlUpQ] at h2; omega
  | n + 1, ℓ, s, w, k, h1, h2 => by
    unfold lvlUpQ at h2
    split_ifs at h2 with h
    · omega
    · rcases h1.lt_or_eq with h1 | rfl
      · exact lvlUpQ_min n (ℓ + 1) s w k h1 h2
      · exact h

/-- Characterization of the real loop: the least admissible level. -/
theorem lvlUp_eq {ℓ r : ℕ} {s w : ℝ} (h1 : ℓ ≤ r) (h2 : s ≤ w * (1 - (1 / 2 : ℝ) ^ (r + 1)))
    (h3 : ∀ k, ℓ ≤ k → k < r → ¬ s ≤ w * (1 - (1 / 2 : ℝ) ^ (k + 1))) : lvlUp ℓ s w = r := by
  apply le_antisymm (lvlUp_le h1 h2)
  have hex : ∃ k : ℕ, s ≤ w * (1 - (1 / 2 : ℝ) ^ (ℓ + k + 1)) :=
    ⟨r - ℓ, by rwa [show ℓ + (r - ℓ) + 1 = r + 1 by omega]⟩
  unfold lvlUp
  split_ifs with hh
  · by_contra hlt
    push Not at hlt
    exact h3 (ℓ + Nat.find hh) (by omega) hlt (Nat.find_spec hh)
  · exact absurd hex hh

theorem loadQ_cast (δ : E → ℚ) (v : V) :
    I.toReal.load (fun e => (δ e : ℝ)) v = (loadQ I δ v : ℝ) := by
  simp [Inst.load, Cslib.Hypergraph.load, loadQ, InstQ.toReal]

theorem joinC_castS (s : StateQ V E) :
    joinC I.toReal P.toReal s.toReal = joinCQ I P s := by
  unfold joinC joinCQ
  congr 1
  ext v
  simp only [mem_filter, mem_univ, true_and]
  have : (1 - P.toReal.β) * I.toReal.w v = (((1 - betaQ P) * I.w v : ℚ) : ℝ) := by
    simp [Params.β, betaQ, ParamsQ.toReal, InstQ.toReal]
  rw [this, show s.toReal.δ = fun e => (s.δ e : ℝ) from rfl, loadQ_cast, Rat.cast_le]
  rfl

theorem lvl1_castS (s : StateQ V E) (hok : FuelOK I P s) (v : V) :
    lvl1 I.toReal P.toReal s.toReal v = lvl1Q I P s v := by
  unfold lvl1 lvl1Q
  rw [joinC_castS]
  split_ifs with hact
  · show lvlUp (s.level v) (I.toReal.load (fun e => (s.δ e : ℝ)) v) (I.w v : ℝ) = _
    rw [loadQ_cast]
    apply lvlUp_eq (le_lvlUpQ _ _ _ _)
    · have h := Rat.cast_le (K := ℝ).2 (hok v hact)
      push_cast at h
      exact h
    · intro k hk1 hk2 hle
      apply lvlUpQ_min _ _ _ _ k hk1 hk2
      have h : ((loadQ I s.δ v : ℚ) : ℝ) ≤ ((I.w v * (1 - (1 / 2) ^ (k + 1)) : ℚ) : ℝ) := by
        push_cast; exact hle
      exact_mod_cast h
  · rfl

theorem deal1_castS (s : StateQ V E) (hok : FuelOK I P s) (e : E) :
    deal1 I.toReal P.toReal s.toReal e = (deal1Q I P s e : ℝ) := by
  unfold deal1 deal1Q
  rw [joinC_castS]
  simp only [lvl1_castS I P s hok, InstQ.toReal_inc]
  split_ifs <;> simp [StateQ.toReal]

theorem raise_castS (s : StateQ V E) (hok : FuelOK I P s) (v : V) :
    Raise I.toReal P.toReal s.toReal v ↔ RaiseQ I P s v := by
  unfold Raise RaiseQ
  rw [joinC_castS]
  simp only [deal1_castS I P s hok, lvl1_castS I P s hok]
  rw [← Rat.cast_le (K := ℝ)]
  push_cast
  rfl

theorem deal2_castS (s : StateQ V E) (hok : FuelOK I P s) (e : E) :
    deal2 I.toReal P.toReal s.toReal e = (deal2Q I P s e : ℝ) := by
  unfold deal2 deal2Q RaiseEdge
  rw [joinC_castS]
  simp only [raise_castS I P s hok, deal1_castS I P s hok, InstQ.toReal_inc]
  split_ifs <;> simp [ParamsQ.toReal]

theorem step_castS (s : StateQ V E) (hok : FuelOK I P s) :
    step I.toReal P.toReal s.toReal = (stepQ I P s).toReal := by
  have hj := joinC_castS I P s
  have hl : lvl1 I.toReal P.toReal s.toReal = lvl1Q I P s := funext (lvl1_castS I P s hok)
  have hd : deal2 I.toReal P.toReal s.toReal = fun e => (deal2Q I P s e : ℝ) :=
    funext (deal2_castS I P s hok)
  rw [show step I.toReal P.toReal s.toReal = ⟨joinC I.toReal P.toReal s.toReal,
    lvl1 I.toReal P.toReal s.toReal, deal2 I.toReal P.toReal s.toReal, fun e =>
      if I.toReal.Covered (joinC I.toReal P.toReal s.toReal) e then (s.δ e : ℝ)
      else (s.δ e : ℝ) + P.toReal.κ * deal2 I.toReal P.toReal s.toReal e⟩ from rfl, hj, hl, hd]
  simp only [stepQ, StateQ.toReal, State.mk.injEq, true_and]
  funext e
  split_ifs <;> simp [ParamsQ.toReal]

theorem init_castS : init I.toReal P.toReal = (initQ I P).toReal := by
  have h0 : deal0 I.toReal P.toReal = fun e => (deal0Q I P e : ℝ) := by
    funext e
    unfold deal0 deal0Q
    push_cast
    congr 1
    rw [Finset.apply_inf'_eq_inf'_comp (I.inc_nonempty e) (fun x : ℚ => (x : ℝ))
      (fun x y => Rat.cast_min x y)]
    simp [InstQ.toReal]
  simp [init, initQ, StateQ.toReal, h0]

/-- The real run equals the rational run as long as the fuel suffices. -/
theorem run_castS {n : ℕ} (hok : ∀ i < n, FuelOK I P (runQ I P i)) :
    run I.toReal P.toReal n = (runQ I P n).toReal := by
  induction n with
  | zero => exact init_castS I P
  | succ n ih =>
    show step _ _ (run _ _ n) = _
    rw [ih (fun i hi => hok i (by omega)), step_castS I P _ (hok n (by omega))]
    rfl

end Podc.CoveringPrimalDual
