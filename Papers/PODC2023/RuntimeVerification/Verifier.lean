import Mathlib
import Papers.PODC2023.RuntimeVerification.Sketch

/-!
# The predictive verifier `V_O` (Figure 10)

`V_O` runs `A*` (8 steps per operation, see `Exec.lean`): after the response `(y, λ)` of `A*`
(step 5), process `p` adds the 4-tuple `(p, op, y, λ)` to its entry of the snapshot object `M`
(step 6, `M.Write`), takes `M.Snapshot()` (step 7), forms the union `τ` of the entries and reports
`(ERROR, X(τ))` iff `X(τ) ∉ O` (lines 10–11).

* `tauAt E s` — the union of `M`'s entries at time `s` (the tuples written before `s`);
  `tau E p k` — what the `k`-th iteration of `p` reads (`M.Snapshot` at step `8k + 7`).
* `Reports O E p k` — the `k`-th iteration of `p` reports `ERROR`.
* `valid_tauAt` — the snapshot contents satisfy Remark 7.2 (`Sketch.Valid`).
* `sketch_mem_of_tight` (Lemma 8.1 (2)), `cut_mem_of_sketch` (Lemma 8.2),
  `sketch_mono` (stability).
-/

namespace Podc2023.RuntimeVerification

open Cslib.SharedMemory.HerlihyWing Sketch

set_option linter.unusedSectionVars false

variable {n : ℕ} {Op Y : Type} [DecidableEq Op] [DecidableEq Y] [Inhabited Op] [Inhabited Y]

namespace Exec

variable (E : Exec n Op Y ℕ)

/-- The 4-tuple of the `k`-th operation of `p`. -/
noncomputable def tup (p : Fin n) (k : ℕ) : Tup n Op Y := ⟨p, k, E.op p k, E.y p k, E.view 8 p k⟩

/-- The contents of `M` (union of its entries) at time `s`: the tuples whose `M.Write`
(step 6) happened before `s`. -/
noncomputable def tauAt (s : ℕ) : Finset (Tup n Op Y) :=
  (Finset.univ : Finset (Fin n)).biUnion fun q =>
    ((Finset.range (cnt 8 6 (E.len q))).filter fun j => E.T q (8 * j + 6) < s).image (E.tup q)

/-- What the `k`-th iteration of `p` reads with `M.Snapshot()` (step 7, line 08). -/
noncomputable def tau (p : Fin n) (k : ℕ) : Finset (Tup n Op Y) := E.tauAt (E.T p (8 * k + 7))

/-- The `k`-th iteration of `p` (whose step 7 happened) reports `(ERROR, X(τ))` (lines 10–11). -/
def Reports (O : Set (Hist (Fin n) Op Y)) (p : Fin n) (k : ℕ) : Prop :=
  8 * k + 7 < E.len p ∧ (XTHy (E.tau p k)).toList ∉ O

/-- History of `V_O` viewed as an implementation (Figure 11): invocation at step 0, response
(`y`, or `ERROR`) after the test at step 7. Here with the responses `y`. -/
def hVy : TH (Fin n) Op Y ℕ := E.proj 8 0 7 E.y

variable {E}

theorem mem_tauAt {s : ℕ} {t : Tup n Op Y} :
    t ∈ E.tauAt s ↔ ∃ q j, 8 * j + 6 < E.len q ∧ E.T q (8 * j + 6) < s ∧ t = E.tup q j := by
  simp only [tauAt, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨q, j, ⟨h1, h2⟩, rfl⟩
    exact ⟨q, j, (lt_cnt (by norm_num)).1 h1, h2, rfl⟩
  · rintro ⟨q, j, h1, h2, rfl⟩
    exact ⟨q, j, ⟨(lt_cnt (by norm_num)).2 h1, h2⟩, rfl⟩

theorem mem_view8 {p : Fin n} {k : ℕ} {x : IRec n Op} :
    x ∈ E.view 8 p k ↔
      8 * x.2.1 + 1 < E.len x.1 ∧ E.T x.1 (8 * x.2.1 + 1) < E.T p (8 * k + 4) ∧
        x.2.2 = E.op x.1 x.2.1 :=
  mem_view (by norm_num)

theorem view_mono {p p' : Fin n} {k k' : ℕ} (h : E.T p (8 * k + 4) ≤ E.T p' (8 * k' + 4)) :
    E.view 8 p k ⊆ E.view 8 p' k' := by
  intro x hx
  rw [mem_view8] at hx ⊢
  exact ⟨hx.1, lt_of_lt_of_le hx.2.1 h, hx.2.2⟩

/-- Steps `8k + i` and `8j + i'` with `i ≠ i'` (both `< 8`) happen at different times. -/
theorem T_ne (hw : E.WF) {p q : Fin n} {k j i i' : ℕ} (hi : i < 8) (hi' : i' < 8) (hii : i ≠ i')
    (h1 : 8 * k + i < E.len p) (h2 : 8 * j + i' < E.len q) :
    E.T p (8 * k + i) ≠ E.T q (8 * j + i') := by
  intro h
  obtain ⟨-, h⟩ := hw.inj p q _ _ h1 h2 h
  omega

theorem op_of_mem_allInv {s : ℕ} {x : IRec n Op} (hx : x ∈ allInv (E.tauAt s)) :
    x.2.2 = E.op x.1 x.2.1 := by
  obtain ⟨t, ht, hxt⟩ := mem_allInv.1 hx
  obtain ⟨q, j, -, -, rfl⟩ := mem_tauAt.1 ht
  exact (mem_view8.1 hxt).2.2

theorem mem_allInv_tauAt {s : ℕ} {x : IRec n Op} :
    x ∈ allInv (E.tauAt s) ↔ ∃ q j, 8 * j + 6 < E.len q ∧ E.T q (8 * j + 6) < s ∧
      8 * x.2.1 + 1 < E.len x.1 ∧ E.T x.1 (8 * x.2.1 + 1) < E.T q (8 * j + 4) ∧
        x.2.2 = E.op x.1 x.2.1 := by
  rw [mem_allInv]
  constructor
  · rintro ⟨t, ht, hxt⟩
    obtain ⟨q, j, h1, h2, rfl⟩ := mem_tauAt.1 ht
    exact ⟨q, j, h1, h2, mem_view8.1 hxt⟩
  · rintro ⟨q, j, h1, h2, h3⟩
    exact ⟨_, mem_tauAt.2 ⟨q, j, h1, h2, rfl⟩, mem_view8.2 h3⟩

/-- Remark 7.2: the contents of `M` are a valid set of tuples. -/
theorem valid_tauAt (hw : E.WF) (s : ℕ) : Valid (E.tauAt s) where
  uniq t ht t' ht' hp hk := by
    obtain ⟨q, j, -, -, rfl⟩ := mem_tauAt.1 ht
    obtain ⟨q', j', -, -, rfl⟩ := mem_tauAt.1 ht'
    simp only [tup] at hp hk
    subst hp hk; rfl
  self t ht := by
    obtain ⟨q, j, h1, -, rfl⟩ := mem_tauAt.1 ht
    simp only [tup]
    rw [mem_view8]
    dsimp only
    exact ⟨by omega, hw.mono _ _ _ (by omega) (by omega), rfl⟩
  cons x hx x' hx' h1 h2 := by
    have e1 := op_of_mem_allInv hx
    have e2 := op_of_mem_allInv hx'
    obtain ⟨p, k, o⟩ := x
    obtain ⟨p', k', o'⟩ := x'
    simp only at h1 h2 e1 e2
    subst h1 h2 e1 e2
    rfl
  chain t ht t' ht' := by
    obtain ⟨q, j, -, -, rfl⟩ := mem_tauAt.1 ht
    obtain ⟨q', j', -, -, rfl⟩ := mem_tauAt.1 ht'
    rcases le_total (E.T q (8 * j + 4)) (E.T q' (8 * j' + 4)) with h | h
    · exact Or.inl (view_mono h)
    · exact Or.inr (view_mono h)
  down x hx j hj := by
    obtain ⟨u, hu, hxu⟩ := mem_allInv.1 hx
    obtain ⟨q', j', h1', h2', rfl⟩ := mem_tauAt.1 hu
    obtain ⟨p, k, o⟩ := x
    simp only [tup] at hxu
    rw [mem_view8] at hxu
    obtain ⟨h1, h2, -⟩ := hxu
    simp only at h1 h2 hj ⊢
    refine ⟨E.tup p j, mem_tauAt.2 ⟨p, j, by omega, ?_, rfl⟩, rfl, rfl, ?_⟩
    · calc E.T p (8 * j + 6) < E.T p (8 * k + 1) := hw.mono _ _ _ (by omega) h1
        _ < E.T q' (8 * j' + 4) := h2
        _ < E.T q' (8 * j' + 6) := hw.mono _ _ _ (by omega) h1'
        _ < s := h2'
    · intro hx
      simp only [tup] at hx
      rw [mem_view8] at hx
      have := hw.mono p (8 * j + 4) (8 * k + 1) (by omega) h1
      exact absurd hx.2.1 (by simp only at this ⊢; omega)

end Exec

end Podc2023.RuntimeVerification
