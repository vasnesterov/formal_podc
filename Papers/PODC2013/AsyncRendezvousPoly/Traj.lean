import Papers.PODC2013.AsyncRendezvousPoly.Model

/-!
# Operations on trajectories

Concatenation `T₁ T₂` (the paper's juxtaposition; the last node of `T₁` is the first node of `T₂`),
reversal `T̄`, `T T̄` (`dbl`), `T^c` (`pow`), indexed concatenations (`concatFn`), and the
"woven" trajectory `F(v₁)(v₁,v₂)F(v₂)…(v_{s-1},v_s)F(v_s)` along `R = (v₁, …, v_s)` (`weave`,
used for `Y'` and `A'`). Occurrences of a trajectory inside another (`OccIn`) and inside a route
(`Occ`) compose (`OccIn.trans`, `OccIn.occ`).
-/

namespace Podc.AsyncRendezvousPoly

variable {V : Type*}

namespace Traj

/-- Concatenation `T S` (meant for `T`'s last node equal to `S`'s first node). -/
def append (T S : Traj V) : Traj V :=
  ⟨T.len + S.len, fun i => if i ≤ T.len then T.f i else S.f (i - T.len)⟩

/-- The reverse trajectory `T̄`. -/
def rev (T : Traj V) : Traj V := ⟨T.len, fun i => T.f (T.len - i)⟩

/-- `T T̄`: follow `T`, then backtrack along it. -/
def dbl (T : Traj V) : Traj V := T.append T.rev

/-- The trajectory consisting of the single node `v`. -/
def nil (v : V) : Traj V := ⟨0, fun _ => v⟩

/-- The one-edge trajectory `(u, w)`. -/
def edge (u w : V) : Traj V := ⟨1, fun i => if i = 0 then u else w⟩

/-- `F 0 F 1 … F (n-1)` (the single node `v` if `n = 0`). -/
def concatFn (v : V) (F : ℕ → Traj V) : ℕ → Traj V
  | 0 => nil v
  | n + 1 => (concatFn v F n).append (F n)

/-- `T^c` for a closed trajectory `T`. -/
def pow (T : Traj V) (c : ℕ) : Traj V := concatFn (T.f 0) (fun _ => T) c

/-- `F(v₁)(v₁,v₂)F(v₂)…(v_{s-1},v_s)F(v_s)` for `R = (v₁, …, v_s)`. -/
def weave (R : Traj V) (F : V → Traj V) : Traj V :=
  (concatFn (R.f 0) (fun i => (F (R.f i)).append (edge (R.f i) (R.f (i + 1)))) R.len).append
    (F (R.f R.len))

/-- `T` is a closed trajectory at `v`. -/
def ClosedAt (T : Traj V) (v : V) : Prop := T.f 0 = v ∧ T.f T.len = v

@[simp] theorem append_len (T S : Traj V) : (T.append S).len = T.len + S.len := rfl
@[simp] theorem rev_len (T : Traj V) : T.rev.len = T.len := rfl
@[simp] theorem dbl_len (T : Traj V) : T.dbl.len = 2 * T.len := by simp [dbl]; ring
@[simp] theorem nil_len (v : V) : (nil v).len = 0 := rfl
@[simp] theorem edge_len (u w : V) : (edge u w).len = 1 := rfl

theorem append_f_of_le (T S : Traj V) {i : ℕ} (h : i ≤ T.len) : (T.append S).f i = T.f i := by
  simp [append, h]

theorem append_f_add (T S : Traj V) (hj : S.f 0 = T.f T.len) (i : ℕ) :
    (T.append S).f (T.len + i) = S.f i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [append, hj]
  · simp [append, show ¬ T.len + i ≤ T.len by omega]

@[simp] theorem append_f_zero (T S : Traj V) : (T.append S).f 0 = T.f 0 := by simp [append]

theorem append_f_len (T S : Traj V) (hj : S.f 0 = T.f T.len) :
    (T.append S).f (T.append S).len = S.f S.len := by
  simpa using append_f_add T S hj S.len

@[simp] theorem dbl_f_zero (T : Traj V) : T.dbl.f 0 = T.f 0 := by simp [dbl]

theorem dbl_f_len (T : Traj V) : T.dbl.f T.dbl.len = T.f 0 := by
  rw [dbl, append_f_len _ _ (by simp [rev])]; simp [rev]

theorem dbl_closed (T : Traj V) : T.dbl.ClosedAt (T.f 0) := ⟨dbl_f_zero T, dbl_f_len T⟩

theorem concatFn_len (v : V) (F : ℕ → Traj V) (n : ℕ) :
    (concatFn v F n).len = ∑ i ∈ Finset.range n, (F i).len := by
  induction n with
  | zero => rfl
  | succ n ih => simp [concatFn, ih, Finset.sum_range_succ]

theorem concatFn_f_zero (v : V) (F : ℕ → Traj V) (n : ℕ) : (concatFn v F n).f 0 = v := by
  induction n with
  | zero => rfl
  | succ n ih => simp [concatFn, ih]

/-- The last node of a chained concatenation. -/
theorem concatFn_f_len (s : ℕ → V) (F : ℕ → Traj V) (h0 : ∀ i, (F i).f 0 = s i)
    (h1 : ∀ i, (F i).f (F i).len = s (i + 1)) (n : ℕ) :
    (concatFn (s 0) F n).f (concatFn (s 0) F n).len = s n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [concatFn]; rw [append_f_len _ _ (by rw [h0, ih])]; exact h1 n

end Traj

open Traj

/-- `T` occurs inside `S` starting at index `α`. -/
def OccIn (T S : Traj V) (α : ℕ) : Prop := α + T.len ≤ S.len ∧ ∀ i ≤ T.len, S.f (α + i) = T.f i

theorem OccIn.refl (T : Traj V) : OccIn T T 0 := ⟨by simp, fun i _ => by simp⟩

theorem OccIn.trans {T S U : Traj V} {α β : ℕ} (h1 : OccIn T S α) (h2 : OccIn S U β) :
    OccIn T U (β + α) :=
  ⟨by have := h1.1; have := h2.1; omega, fun i hi => by
    rw [add_assoc, h2.2 _ (by have := h1.1; omega), h1.2 i hi]⟩

theorem OccIn.occ {T S : Traj V} {α β : ℕ} {r : ℕ → V} (h1 : OccIn T S α) (h2 : Occ S r β) :
    Occ T r (β + α) := fun i hi => by
  rw [add_assoc, h2 _ (by have := h1.1; omega), h1.2 i hi]

theorem occIn_append_left (T S : Traj V) : OccIn T (T.append S) 0 :=
  ⟨by simp, fun i hi => by simp [append_f_of_le _ _ hi]⟩

theorem occIn_append_right (T S : Traj V) (hj : S.f 0 = T.f T.len) :
    OccIn S (T.append S) T.len := ⟨by simp, fun i _ => append_f_add T S hj i⟩

theorem occIn_concatFn (s : ℕ → V) (F : ℕ → Traj V) (h0 : ∀ i, (F i).f 0 = s i)
    (h1 : ∀ i, (F i).f (F i).len = s (i + 1)) {i n : ℕ} (hi : i < n) :
    OccIn (F i) (concatFn (s 0) F n) (concatFn (s 0) F i).len := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · have := (ih hi).trans (occIn_append_left _ (F n)); rwa [zero_add] at this
    · exact occIn_append_right _ _ (by rw [h0, concatFn_f_len s F h0 h1])

/-- Closed-at-`v` version of `occIn_concatFn`. -/
theorem occIn_concatFn_closed {v : V} (F : ℕ → Traj V) (hF : ∀ i, (F i).ClosedAt v) {i n : ℕ}
    (hi : i < n) : OccIn (F i) (concatFn v F n) (∑ j ∈ Finset.range i, (F j).len) := by
  have := occIn_concatFn (fun _ => v) F (fun i => (hF i).1) (fun i => (hF i).2) hi
  rwa [concatFn_len] at this

theorem concatFn_closed {v : V} (F : ℕ → Traj V) (hF : ∀ i, (F i).ClosedAt v) (n : ℕ) :
    (concatFn v F n).ClosedAt v :=
  ⟨concatFn_f_zero v F n, concatFn_f_len (fun _ => v) F (fun i => (hF i).1) (fun i => (hF i).2) n⟩

/-! ### Powers -/

theorem pow_len (T : Traj V) (c : ℕ) : (pow T c).len = c * T.len := by
  simp [pow, concatFn_len]

theorem pow_closed {T : Traj V} {v : V} (hT : T.ClosedAt v) (c : ℕ) : (pow T c).ClosedAt v := by
  have := concatFn_closed (v := v) (fun _ => T) (fun _ => hT) c
  rwa [pow, hT.1]

theorem occIn_pow {T : Traj V} {v : V} (hT : T.ClosedAt v) {c : ℕ} (hc : 1 ≤ c) :
    OccIn T (pow T c) 0 := by
  have := occIn_concatFn_closed (v := v) (fun _ => T) (fun _ => hT) hc
  simpa [pow, hT.1] using this

theorem dbl_f (T : Traj V) {i : ℕ} (hi : i ≤ 2 * T.len) :
    T.dbl.f i = T.f (if i ≤ T.len then i else 2 * T.len - i) := by
  simp only [dbl, append, rev]; split_ifs with h
  · rfl
  · congr 1; omega

/-- `(T T̄)^c` read at position `i` is `T` at the folded index. -/
theorem pow_dbl_f (T : Traj V) (c : ℕ) {i : ℕ} (hi : i ≤ c * (2 * T.len)) :
    (pow T.dbl c).f i = T.f (foldN T.len i) := by
  induction c generalizing i with
  | zero =>
    simp at hi; subst hi; simp [pow, concatFn, nil, foldN]
  | succ c ih =>
    have hcl := dbl_closed T
    simp only [pow, concatFn]
    by_cases h : i ≤ c * (2 * T.len)
    · rw [append_f_of_le _ _ (by rw [concatFn_len]; simpa using h)]
      exact ih h
    · obtain ⟨j, rfl⟩ : ∃ j, i = c * (2 * T.len) + j := ⟨i - c * (2 * T.len), by omega⟩
      have hl : (concatFn (T.dbl.f 0) (fun _ => T.dbl) c).len = c * (2 * T.len) := by
        rw [concatFn_len]; simp
      have hj : j ≤ 2 * T.len := by nlinarith
      rw [← hl, append_f_add _ _ (by
          rw [concatFn_f_len (fun _ => T.dbl.f 0) _ (fun _ => rfl) (fun _ => hcl.2)]), hl,
        dbl_f T hj, foldN_add_mul]
      congr 1
      unfold foldN
      rcases Nat.eq_zero_or_pos T.len with h0 | h0
      · rw [h0] at hj ⊢; simp at hj; subst hj; simp
      rcases hj.lt_or_eq with hj | hj
      · rw [Nat.mod_eq_of_lt hj]
      · subst hj; simp only [Nat.mod_self]; split_ifs <;> omega

/-- An occurrence of `(T T̄)^c` in a route is a repetition of `T T̄`. -/
theorem RepOcc.of_occ {T : Traj V} {c β : ℕ} {r : ℕ → V} (h : Occ (pow T.dbl c) r β) :
    RepOcc T c β r := fun i hi => by
  rw [h i (by rw [pow_len]; simpa using hi), pow_dbl_f T c hi]

theorem RepOcc.of_occIn {T S : Traj V} {c α β : ℕ} {r : ℕ → V} (h1 : OccIn (pow T.dbl c) S α)
    (h2 : Occ S r β) : RepOcc T c (β + α) r := RepOcc.of_occ (h1.occ h2)

/-! ### Woven trajectories -/

theorem weave_len (R : Traj V) (F : V → Traj V) (ℓ : ℕ) (hF : ∀ w, (F w).len = ℓ) :
    (weave R F).len = (R.len + 1) * ℓ + R.len := by
  simp [weave, concatFn_len, hF]; ring

theorem weave_f_zero (R : Traj V) (F : V → Traj V) :
    (weave R F).f 0 = R.f 0 := by
  simp [weave, concatFn_f_zero]

section weave

variable (R : Traj V) (F : V → Traj V) (hF : ∀ w, (F w).ClosedAt w)
include hF

private theorem wv_h0 (i : ℕ) :
    ((fun i => (F (R.f i)).append (edge (R.f i) (R.f (i + 1)))) i).f 0 = R.f i := by
  simp [(hF _).1]

private theorem wv_h1 (i : ℕ) :
    ((fun i => (F (R.f i)).append (edge (R.f i) (R.f (i + 1)))) i).f
      ((fun i => (F (R.f i)).append (edge (R.f i) (R.f (i + 1)))) i).len = R.f (i + 1) := by
  simp only; rw [append_f_len _ _ (by simp [edge, (hF _).2])]; simp [edge]

theorem weave_f_len : (weave R F).f (weave R F).len = R.f R.len := by
  unfold weave
  rw [append_f_len _ _ (by rw [(hF _).1, concatFn_f_len R.f _ (wv_h0 R F hF) (wv_h1 R F hF)])]
  exact (hF _).2

theorem occIn_weave_F {i : ℕ} (hi : i ≤ R.len) : ∃ δ, OccIn (F (R.f i)) (weave R F) δ := by
  rcases hi.lt_or_eq with hi | rfl
  · refine ⟨_, ((occIn_append_left _ _).trans
      (occIn_concatFn R.f _ (wv_h0 R F hF) (wv_h1 R F hF) hi)).trans (occIn_append_left _ _)⟩
  · exact ⟨_, occIn_append_right _ _
      (by rw [(hF _).1, concatFn_f_len R.f _ (wv_h0 R F hF) (wv_h1 R F hF)])⟩

theorem occIn_weave_edge {i : ℕ} (hi : i < R.len) :
    ∃ δ, OccIn (edge (R.f i) (R.f (i + 1))) (weave R F) δ :=
  ⟨_, ((occIn_append_right _ _ (by simp [edge, (hF _).2])).trans
      (occIn_concatFn R.f _ (wv_h0 R F hF) (wv_h1 R F hF) hi)).trans (occIn_append_left _ _)⟩

end weave

/-! ### Covering all edges -/

theorem Covers.of_occIn {G : SimpleGraph V} {T S : Traj V} {α : ℕ} (h : Covers G T)
    (hT : OccIn T S α) : Covers G S := fun u w huw => by
  obtain ⟨i, hi, h'⟩ := h u w huw
  refine ⟨α + i, by have := hT.1; omega, ?_⟩
  rw [hT.2 i hi.le, show α + i + 1 = α + (i + 1) by ring, hT.2 (i + 1) hi]; exact h'

theorem Covers.weave {G : SimpleGraph V} {R : Traj V} (h : Covers G R) (F : V → Traj V)
    (hF : ∀ w, (F w).ClosedAt w) : Covers G (weave R F) := fun u w huw => by
  obtain ⟨i, hi, h'⟩ := h u w huw
  obtain ⟨δ, hδ⟩ := occIn_weave_edge R F hF hi
  refine ⟨δ, by have := hδ.1; simp at this; omega, ?_⟩
  have e0 := hδ.2 0 (by simp); have e1 := hδ.2 1 (by simp)
  rw [add_zero] at e0; rw [e0, e1]; simpa [edge] using h'

/-! ### Walks -/

namespace Traj

theorem IsWalk.append {G : SimpleGraph V} {T S : Traj V} (hT : T.IsWalk G) (hS : S.IsWalk G)
    (hj : S.f 0 = T.f T.len) : (T.append S).IsWalk G := fun i hi => by
  by_cases h : i < T.len
  · rw [append_f_of_le _ _ h.le, append_f_of_le _ _ h]; exact hT i h
  · obtain ⟨j, rfl⟩ : ∃ j, i = T.len + j := ⟨i - T.len, by omega⟩
    rw [append_f_add _ _ hj, show T.len + j + 1 = T.len + (j + 1) by ring, append_f_add _ _ hj]
    exact hS j (by simp at hi; omega)

theorem IsWalk.rev {G : SimpleGraph V} {T : Traj V} (hT : T.IsWalk G) : T.rev.IsWalk G :=
  fun i hi => by
    simp only [Traj.rev] at hi ⊢
    have := hT (T.len - (i + 1)) (by omega)
    rw [show T.len - (i + 1) + 1 = T.len - i by omega] at this
    exact this.symm

theorem IsWalk.dbl {G : SimpleGraph V} {T : Traj V} (hT : T.IsWalk G) : T.dbl.IsWalk G :=
  hT.append hT.rev (by simp [Traj.rev])

theorem IsWalk.nil (G : SimpleGraph V) (v : V) : (nil v).IsWalk G := fun i hi => by simp at hi

theorem IsWalk.edge {G : SimpleGraph V} {u w : V} (h : G.Adj u w) : (edge u w).IsWalk G :=
  fun i hi => by simp at hi; subst hi; simpa [Traj.edge] using h

theorem IsWalk.concatFn {G : SimpleGraph V} (s : ℕ → V) (F : ℕ → Traj V)
    (h0 : ∀ i, (F i).f 0 = s i) (h1 : ∀ i, (F i).f (F i).len = s (i + 1)) (n : ℕ)
    (hw : ∀ i < n, (F i).IsWalk G) : (concatFn (s 0) F n).IsWalk G := by
  induction n with
  | zero => exact IsWalk.nil G _
  | succ n ih =>
    exact (ih fun i hi => hw i (by omega)).append (hw n (by omega))
      (by rw [h0, concatFn_f_len s F h0 h1])

theorem IsWalk.pow {G : SimpleGraph V} {T : Traj V} {v : V} (hT : T.ClosedAt v)
    (hw : T.IsWalk G) (c : ℕ) : (Traj.pow T c).IsWalk G :=
  IsWalk.concatFn (fun _ => T.f 0) (fun _ => T) (fun _ => rfl)
    (fun _ => by rw [hT.1, hT.2]) c (fun _ _ => hw)

theorem IsWalk.weave {G : SimpleGraph V} {R : Traj V} (hR : R.IsWalk G) (F : V → Traj V)
    (hF : ∀ w, (F w).ClosedAt w) (hw : ∀ w, (F w).IsWalk G) : (Traj.weave R F).IsWalk G := by
  unfold Traj.weave
  exact IsWalk.append (IsWalk.concatFn R.f _ (wv_h0 R F hF) (wv_h1 R F hF) _
    (fun i hi => (hw _).append (IsWalk.edge (hR i hi)) (by simp [Traj.edge, (hF _).2])))
    (hw _) (by rw [(hF _).1, concatFn_f_len R.f _ (wv_h0 R F hF) (wv_h1 R F hF)])

end Traj

end Podc.AsyncRendezvousPoly
