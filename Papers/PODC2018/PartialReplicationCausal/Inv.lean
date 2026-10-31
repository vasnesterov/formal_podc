import Papers.PODC2018.PartialReplicationCausal.Basic

/-!
# The inductive invariant of the algorithm

`Inv X s` collects the facts about reachable states used in the proofs of Lemma 3, Lemma 5 and
Theorem 3. Its preservation is proved in `Preservation.lean`; the hard field is `safe`, whose
preservation is the chain argument of `Chain.lean`.
-/

namespace Podc.PartialReplicationCausal

open Classical

variable {ι Reg : Type*} (X : ι → Set Reg)

/-- The inductive invariant. -/
structure Inv (s : State ι Reg) : Prop where
  /-- Applied updates have been issued. -/
  app_lt : ∀ i, ∀ c ∈ s.app i, c < s.n
  /-- Replicas only apply updates of their own registers. -/
  app_reg : ∀ i, ∀ c ∈ s.app i, (s.log c).reg ∈ X i
  /-- An update is applied at its issuer. -/
  own : ∀ a < s.n, a ∈ s.app (s.log a).src
  /-- `pre` only contains earlier updates. -/
  pre_lt : ∀ a < s.n, ∀ c ∈ (s.log a).pre, c < a
  /-- `pre` was applied at the issuer. -/
  pre_app : ∀ a < s.n, (s.log a).pre ⊆ s.app (s.log a).src
  /-- Earlier updates of the same replica precede an update. -/
  pre_own : ∀ a < s.n, ∀ c < a, (s.log c).src = (s.log a).src → c ∈ (s.log a).pre
  /-- `pre` grows along the updates of one replica. -/
  pre_mono : ∀ a < s.n, ∀ c < a, (s.log c).src = (s.log a).src → (s.log c).pre ⊆ (s.log a).pre
  /-- Safety at the moment an update was issued. -/
  pre_safe : ∀ a < s.n, ∀ c ∈ (s.log a).pre, ∀ b, (s.log b).reg ∈ X (s.log a).src →
    HB s b c → b ∈ (s.log a).pre
  /-- Safety (Definition 5). -/
  safe : Safe X s
  /-- A replica's timestamp dominates the timestamps it has merged (on common edges). -/
  τ_app : ∀ i, ∀ c ∈ s.app i, ∀ e₁ e₂, TsEdge X i e₁ e₂ → TsEdge X (s.log c).src e₁ e₂ →
    (s.log c).ts e₁ e₂ ≤ s.τ i e₁ e₂
  /-- The timestamp of an update dominates the timestamps its issuer had merged before. -/
  ts_pre : ∀ a < s.n, ∀ c ∈ (s.log a).pre, ∀ e₁ e₂, TsEdge X (s.log a).src e₁ e₂ →
    TsEdge X (s.log c).src e₁ e₂ → (s.log c).ts e₁ e₂ ≤ (s.log a).ts e₁ e₂
  /-- `τ_i[e_ik]` counts the updates issued by `i` on `e_ik`. -/
  τ_own : ∀ i k, Adj X i k → s.τ i i k = cnt X s i k s.n
  /-- The own entry of an update's timestamp is its position on the edge. -/
  ts_own : ∀ a < s.n, ∀ k, Adj X (s.log a).src k → (s.log a).reg ∈ X k →
    (s.log a).ts (s.log a).src k = cnt X s (s.log a).src k (a + 1)
  /-- Lemma 3, strengthened: replica `i` has applied exactly the first `τ_i[e_ji]` updates of `e_ji`. -/
  count : ∀ i j, j ≠ i → Adj X j i → ∀ c < s.n, (s.log c).src = j → (s.log c).reg ∈ X i →
    (c ∈ s.app i ↔ cnt X s j i (c + 1) ≤ s.τ i j i)
  /-- A positive entry `τ_r[e]` is witnessed by an update on `e` in the causal past of `r`. -/
  τ_wit : ∀ r e₁ e₂, TsEdge X r e₁ e₂ → 0 < s.τ r e₁ e₂ → ∃ c < s.n, (s.log c).src = e₁ ∧
    (s.log c).reg ∈ X e₂ ∧ cnt X s e₁ e₂ (c + 1) = s.τ r e₁ e₂ ∧
    (c ∈ s.app r ∨ ∃ d ∈ s.app r, HB s c d)
  /-- A positive entry of an update's timestamp is witnessed by an update on that edge that is the
  update itself or happened before it. -/
  ts_wit : ∀ a < s.n, ∀ e₁ e₂, TsEdge X (s.log a).src e₁ e₂ → 0 < (s.log a).ts e₁ e₂ →
    ∃ c < s.n, (s.log c).src = e₁ ∧ (s.log c).reg ∈ X e₂ ∧
      cnt X s e₁ e₂ (c + 1) = (s.log a).ts e₁ e₂ ∧ (c = a ∨ HB s c a)

variable {X}

lemma tsEdge_self_iff {i k : ι} : TsEdge X i i k ↔ Adj X i k :=
  ⟨fun h => h.1, fun h => ⟨h, Or.inl rfl⟩⟩

lemma tsEdge_in_iff {i j : ι} : TsEdge X i j i ↔ Adj X j i :=
  ⟨fun h => h.1, fun h => ⟨h, Or.inr (Or.inl rfl)⟩⟩

lemma adj_symm {j k : ι} (h : Adj X j k) : Adj X k j :=
  ⟨h.1.symm, by rw [Set.inter_comm]; exact h.2⟩

lemma adj_of_mem {j k : ι} {x : Reg} (hjk : j ≠ k) (hj : x ∈ X j) (hk : x ∈ X k) : Adj X j k :=
  ⟨hjk, x, hj, hk⟩

namespace Inv

variable {s : State ι Reg} (h : Inv X s)
include h

lemma reg_src {a : ℕ} (ha : a < s.n) : (s.log a).reg ∈ X (s.log a).src :=
  h.app_reg _ _ (h.own a ha)

lemma pre_lt_n {a : ℕ} (ha : a < s.n) {c : ℕ} (hc : c ∈ (s.log a).pre) : c < s.n :=
  (h.pre_lt a ha c hc).trans ha

lemma hb_lt {a b : ℕ} (hab : HB s a b) : a < b := by
  induction hab with
  | single h' => exact h.pre_lt _ h'.1 _ h'.2
  | tail _ h' ih => exact ih.trans (h.pre_lt _ h'.1 _ h'.2)

omit h in
lemma hb_of_pre {a b : ℕ} (hb : b < s.n) (ha : a ∈ (s.log b).pre) : HB s a b :=
  .single ⟨hb, ha⟩

lemma pre_reg {a : ℕ} (ha : a < s.n) {c : ℕ} (hc : c ∈ (s.log a).pre) :
    (s.log c).reg ∈ X (s.log a).src :=
  h.app_reg _ _ (h.pre_app a ha hc)

end Inv

end Podc.PartialReplicationCausal
