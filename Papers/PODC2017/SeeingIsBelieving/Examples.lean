import Papers.PODC2017.SeeingIsBelieving.Hierarchy
import Papers.PODC2017.SeeingIsBelieving.SnapshotIsolation

/-!
# Examples

* **Write skew** (Section 1, Figure 1(r), and Section 5.1, Figure 3): two transactions read both
  keys `x`, `y` from the initial state and write different keys. They satisfy the state-based
  definition of snapshot isolation but not of serializability (`writeSkew_SI`,
  `writeSkew_not_Ser`); this also shows that the hypotheses of the theorems are satisfiable.
* **The version order must be quantified** (`blindWrites_*`): two blind-writing transactions
  satisfy `CT_SER` (hence `CT_RU`), yet for the version order `x₀ ≪ x₁`, `y₁ ≪ y₀` the history
  exhibits G0 (and G1c). So Theorems 1–4 are false if "¬G1 ∧ ¬G2" (etc.) refers to a fixed
  history with its own version order; the right-hand sides must read "for some version order".
-/

namespace Podc.SeeingIsBelieving

open Relation

/-! ### Write skew -/

/-- Keys: `false` is `x`, `true` is `y`. Transaction `0` reads `x, y` and writes `x`;
transaction `1` reads `x, y` and writes `y`. -/
def writeSkew : TxnSet Bool (Fin 2) where
  ops T := [.read false none, .read true none, .write (T = 1 : Bool)]
  committed := Finset.univ

lemma writeSkew_wellFormed : writeSkew.WellFormed where
  read_other T _ k X h hX := by simp [writeSkew] at h
  read_own T _ m k h := by
    rcases m with _ | _ | _ | m <;> simp [writeSkew] at h

/-- The execution `T₀ T₁`. -/
def writeSkewExec : Execution writeSkew where
  order := [0, 1]
  nodup := by decide
  mem_iff T := by fin_cases T <;> simp [writeSkew]

/-- Write skew satisfies (state-based) snapshot isolation: both transactions read from the
initial state `s₀`. -/
theorem writeSkew_SI : writeSkew.Satisfies Execution.CTSI := by
  refine ⟨writeSkewExec, fun T _ => ⟨0, Nat.zero_le _, fun m hm => ?_, fun k hk => ?_⟩⟩
  · simp only [writeSkew, List.length_cons, List.length_nil] at hm
    refine ⟨Nat.zero_le _, ?_⟩
    rcases m with _ | _ | _ | m
    · simp [writeSkew, Execution.state]
    · simp [writeSkew, Execution.state]
    · simp [writeSkew]
    · omega
  · fin_cases T
    · simp [Execution.idx, writeSkewExec]
    · simp only [TxnSet.Writes, writeSkew] at hk
      have hk' : k = true := by simpa using hk
      subst hk'
      simp [Execution.idx, writeSkewExec, Execution.state, TxnSet.Writes, writeSkew]

/-- Write skew is not serializable (by Theorem 1: every version order yields an anti-dependency
cycle `T₀ →rw T₁ →rw T₀`). -/
theorem writeSkew_not_Ser : ¬ writeSkew.Satisfies Execution.CTSer := by
  rw [theorem1 writeSkew_wellFormed]
  rintro ⟨vo, -, hG2⟩
  -- the only writer of `k` is the first one
  have hfirst : ∀ (T : Fin 2), vo.IsFirst (T = 1 : Bool) T := by
    intro T
    refine ⟨Finset.mem_univ _, by simp [TxnSet.Writes, writeSkew], fun Z hZ => ?_⟩
    obtain ⟨-, -, hwZ, -⟩ := vo.dom hZ
    have : Z = T := by
      fin_cases Z <;> fin_cases T <;> simp_all [TxnSet.Writes, writeSkew]
    subst this
    exact vo.irrefl _ _ hZ
  have hrw : ∀ T : Fin 2, vo.RW (1 - T) T := by
    intro T
    refine ⟨Finset.mem_univ _, by fin_cases T <;> decide, (T = 1 : Bool), none, ?_, hfirst T⟩
    fin_cases T <;> simp [writeSkew]
  exact hG2 ⟨0, 1, hrw 1, ReflTransGen.single (Or.inr (hrw 0))⟩

/-- Snapshot isolation is strictly weaker than serializability. -/
theorem SI_not_imp_Ser :
    ∃ H : TxnSet Bool (Fin 2), H.WellFormed ∧ H.Satisfies Execution.CTSI ∧
      ¬ H.Satisfies Execution.CTSer :=
  ⟨writeSkew, writeSkew_wellFormed, writeSkew_SI, writeSkew_not_Ser⟩

/-! ### Blind writes: the version order is not determined by the observations -/

/-- Both transactions blindly write `x` and `y`. -/
def blindWrites : TxnSet Bool (Fin 2) where
  ops _ := [.write false, .write true]
  committed := Finset.univ

lemma blindWrites_wellFormed : blindWrites.WellFormed where
  read_other T _ k X h hX := by simp [blindWrites] at h
  read_own T _ m k h := by rcases m with _ | _ | m <;> simp [blindWrites] at h

/-- The version order `x₀ ≪ x₁`, `y₁ ≪ y₀`. -/
def blindWritesVO : VersionOrder blindWrites where
  lt k X Y := (k = false ∧ X = 0 ∧ Y = 1) ∨ (k = true ∧ X = 1 ∧ Y = 0)
  dom {k X Y} h := by
    refine ⟨Finset.mem_univ _, Finset.mem_univ _, ?_, ?_⟩ <;>
      cases k <;> simp [TxnSet.Writes, blindWrites]
  irrefl k X h := by rcases h with ⟨-, rfl, h⟩ | ⟨-, rfl, h⟩ <;> exact absurd h (by decide)
  trans {k X Y Z} h₁ h₂ := by
    rcases h₁ with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> revert h₂ <;> revert Z <;> decide
  total {k X Y} _ _ _ _ hne := by
    fin_cases X <;> fin_cases Y <;> cases k <;> simp_all

/-- The observations of `blindWrites` are serializable (no reads at all). -/
theorem blindWrites_Ser : blindWrites.Satisfies Execution.CTSer := by
  obtain ⟨e⟩ := blindWrites.nonempty_execution
  refine ⟨e, fun T _ m hm => ⟨le_rfl, ?_⟩⟩
  rcases m with _ | _ | m
  · simp [blindWrites]
  · simp [blindWrites]
  · simp [blindWrites] at hm

/-- ... but with the version order `blindWritesVO` the history exhibits G0 (a write cycle),
hence G1. -/
theorem blindWrites_G0 : blindWritesVO.G0 ∧ blindWritesVO.G1 := by
  have h01 : blindWritesVO.WW 0 1 :=
    ⟨false, Or.inl ⟨rfl, rfl, rfl⟩, fun Z ⟨h₁, h₂⟩ => by
      simp only [blindWritesVO] at h₁ h₂; omega⟩
  have h10 : blindWritesVO.WW 1 0 :=
    ⟨true, Or.inr ⟨rfl, rfl, rfl⟩, fun Z ⟨h₁, h₂⟩ => by
      simp only [blindWritesVO] at h₁ h₂; omega⟩
  have hc : TransGen blindWritesVO.WW 0 0 := TransGen.head h01 (TransGen.single h10)
  exact ⟨⟨0, hc⟩, Or.inr ⟨0, transGen_mono (fun a b h => Or.inl h) hc⟩⟩

/-- Theorems 1 and 4 are false if their right-hand side refers to a *given* version order:
here `∃ e, ∀ T, CT_SER(T, e)` (and `CT_RU`) hold, but G1 and G0 occur for `blindWritesVO`. -/
theorem fixed_versionOrder_counterexample :
    blindWrites.Satisfies Execution.CTSer ∧ blindWrites.Satisfies Execution.CTRU ∧
      blindWritesVO.G1 ∧ blindWritesVO.G0 :=
  ⟨blindWrites_Ser, (theorem4 (H := blindWrites)).2 ⟨blindWrites.nonempty_execution.some.vo,
    fun ⟨_, hX⟩ => lt_irrefl _ (lt_of_transGen _ (fun _ _ h => Execution.vo_ww_idx _ h) hX)⟩,
    blindWrites_G0.2, blindWrites_G0.1⟩

end Podc.SeeingIsBelieving
