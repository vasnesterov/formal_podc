import Papers.PODC2020.SSLERegular.EulerCycle
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# State complexity (Sections 3.4 and 4.4)

Exact numbers of states of our transcriptions, with `c` the number of states of the ring
protocol (`Nat.card RS`):

* SS-EulerCycle on `2k`-regular graphs: a virtual node has `c · (4k²)² · 2 · 2 = 64 c k⁴` states
  and a node `(64 c k⁴)^k · (4k²)² · 2 · 2 = (64c)^k · k^(4k) · 64 k⁴` states, which is the paper's
  `O((64c)^k · k^(4k+4))` (`card_vnode`, `card_estate`).
* SS-Tree on `k`-regular graphs: `320 c² k⁶ (k²+1)² (k+1)²` states, i.e. the paper's `O(k¹²)`
  (`card_tstate`).
-/

namespace SSLERegular

variable {RS : Type*} {k : ℕ}

/-- `VNode` as a product. -/
def VNode.equiv : VNode k RS ≃ RS × Fin (4 * k ^ 2) × Fin (4 * k ^ 2) × Bool × Bool where
  toFun s := (s.ringState, s.pred, s.succ, s.token, s.bit)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `EState` as a product. -/
def EState.equiv : EState k RS ≃ (Fin k → VNode k RS) × Fin (4 * k ^ 2) × Fin (4 * k ^ 2) ×
    Bool × Bool where
  toFun s := (s.node, s.color, s.prevColor, s.colorBit, s.errFlag)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- `TState` as a product. -/
def TState.equiv : TState k RS ≃ Fin (k ^ 2) × Fin (k ^ 2) × Fin (k ^ 2) × Bool ×
    Fin (k ^ 2 + 1) × Fin (k + 1) × Bool × Bool × RS × RS × Bool × Bool × Bool ×
    Fin (k ^ 2 + 1) × Fin (k + 1) × Coin where
  toFun s := (s.color, s.parentColor, s.prevColor, s.colorBit, s.counterColor, s.counter,
    s.errFlag, s.root, s.ringState, s.ringStateCopy, s.loopMarker, s.loopChild, s.loopParent,
    s.loopColor, s.loopCounter, s.coin)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma card_coin : Nat.card Coin = 5 := by
  rw [Nat.card_eq_fintype_card]; rfl

/-- Virtual node of SS-EulerCycle: `64 c k⁴` states. -/
theorem card_vnode : Nat.card (VNode k RS) = 64 * Nat.card RS * k ^ 4 := by
  rw [Nat.card_congr VNode.equiv]
  simp only [Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  ring

/-- Node of SS-EulerCycle: `(64 c k⁴)^k · 64 k⁴` states, i.e. `O((64c)^k · k^(4k+4))`. -/
theorem card_estate :
    Nat.card (EState k RS) = (64 * Nat.card RS * k ^ 4) ^ k * (64 * k ^ 4) := by
  rw [Nat.card_congr EState.equiv]
  simp only [Nat.card_prod, Nat.card_fun, card_vnode]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  ring

/-- Node of SS-Tree: `320 c² k⁶ (k²+1)² (k+1)²` states, i.e. `O(k¹²)`. -/
theorem card_tstate :
    Nat.card (TState k RS) =
      320 * Nat.card RS ^ 2 * k ^ 6 * (k ^ 2 + 1) ^ 2 * (k + 1) ^ 2 := by
  rw [Nat.card_congr TState.equiv]
  simp only [Nat.card_prod, card_coin]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_bool]
  ring

end SSLERegular
