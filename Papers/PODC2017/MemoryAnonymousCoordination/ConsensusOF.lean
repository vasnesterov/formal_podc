import Papers.PODC2017.MemoryAnonymousCoordination.ConsensusSafety

/-!
# Figure 2: obstruction-freedom (Theorem 4.1, termination part)

A process running solo finishes its current collect and write; after one more complete (now
accurate) iteration its preference `x` is *stable* (`adopt n view x = x`, `adopt_stable`), and from
then on every iteration turns one more register into `(p, x)` (by the hypothesis `SelOK` on line 6)
until all registers hold `(p, x)`, at which point it decides.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Consensus

open Cslib.SharedMemory

variable {P V : Type} {m : ℕ} [DecidableEq V] [DecidableEq P] [Inhabited V]
  {n : ℕ} {sel : P → V → (Fin m → Option (P × V)) → Fin m} {π : P → Equiv.Perm (Fin m)}

variable (n sel π) in
/-- `p` running solo from `C` eventually returns. -/
def Term (p : P) (C : Cfg P V m) : Prop :=
  ∃ k, (((I n sel π).soloStep p)^[k] C).pend p = none

lemma Term.of_iter {p : P} {C : Cfg P V m} (t : ℕ)
    (h : Term n sel π p (((I n sel π).soloStep p)^[t] C)) : Term n sel π p C := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k + t, by rw [Function.iterate_add_apply]; exact hk⟩

lemma term_done {p : P} {C : Cfg P V m} (hp : C.pend p ≠ none) {v : V}
    (hl : C.loc p = .done v) : Term n sel π p C :=
  ⟨1, solo_done hp hl⟩

lemma term_write_true {p : P} {C : Cfg P V m} (hp : C.pend p ≠ none) {x : V} {j : Fin m}
    (hl : C.loc p = .write x j true) : Term n sel π p C := by
  refine Term.of_iter 1 (term_done (v := x) ?_ ?_)
  · simp only [Function.iterate_one, solo_write hp hl]; exact hp
  · simp [solo_write hp hl, afterWrite]

/-- Finishing a collect solo: after the remaining reads, `p` is about to write, having seen its
virtual view. -/
lemma collect_run {p : P} (d : ℕ) : ∀ (C : Cfg P V m) (x : V) (k : Fin m)
    (view : Fin m → Option (P × V)), k.val + d + 1 = m → C.pend p ≠ none →
    C.loc p = .collect x k view →
    ∃ D, ((I n sel π).soloStep p)^[d + 1] C = D ∧ D.pend = C.pend ∧ D.mem = C.mem ∧
      D.loc p = finish n sel p x (mixed (π p) k view C.mem) := by
  induction d with
  | zero =>
    intro C x k view hk hp hl
    refine ⟨_, rfl, ?_, ?_, ?_⟩
    · simp [solo_collect hp hl]
    · simp [solo_collect hp hl]
    · have hk' : ¬ k.val + 1 < m := by omega
      simp [solo_collect hp hl, afterRead, hk', mixed_last _ _ _ _ hk']
  | succ d ih =>
    intro C x k view hk hp hl
    have hk' : k.val + 1 < m := by omega
    set C₁ := (I n sel π).soloStep p C with hC₁
    have h1 : C₁.loc p = .collect x ⟨k.val + 1, hk'⟩
        (Function.update view k (C.mem (π p k))) := by
      simp [hC₁, solo_collect hp hl, afterRead, hk']
    have hp1 : C₁.pend = C.pend := by simp [hC₁, solo_collect hp hl]
    have hm1 : C₁.mem = C.mem := by simp [hC₁, solo_collect hp hl]
    obtain ⟨D, hD, hDp, hDm, hDl⟩ :=
      ih C₁ x ⟨k.val + 1, hk'⟩ _ (by simp only; omega) (by rw [hp1]; exact hp) h1
    refine ⟨D, ?_, by rw [hDp, hp1], by rw [hDm, hm1], ?_⟩
    · rw [Function.iterate_succ_apply]; exact hD
    · rw [hDl, hm1, mixed_read _ _ _ _ hk']

/-- The registers as seen by `p` (in its own numbering). -/
def localMem (σ : Equiv.Perm (Fin m)) (C : Cfg P V m) : Fin m → Option (P × V) :=
  fun j => C.mem (σ j)

/-- Number of registers not holding `(p, x)`. -/
def miss (p : P) (x : V) (v : Fin m → Option (P × V)) : ℕ :=
  (Finset.univ.filter fun j => v j ≠ some (p, x)).card

lemma miss_update_lt {p : P} {x : V} {v : Fin m → Option (P × V)} {j : Fin m}
    (hj : v j ≠ some (p, x)) : miss p x (Function.update v j (some (p, x))) < miss p x v := by
  unfold miss
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.update_apply]
    split_ifs <;> simp_all
  · intro hsub
    have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ j, hj⟩)
    simp at this

/-- One full solo iteration from the start of a collect: either `p` decides, or it starts a new
collect with preference `x' = adopt n v x` after writing `(p, x')` into local register
`sel p x' v`. -/
lemma round (hm : m + 1 = 2 * n) {p : P} {C : Cfg P V m} (hp : C.pend p ≠ none) {x : V}
    {k : Fin m} {view : Fin m → Option (P × V)} (hl : C.loc p = .collect x k view)
    (hk : k.val = 0) :
    Term n sel π p C ∨
      ∃ t E, ((I n sel π).soloStep p)^[t] C = E ∧ E.pend = C.pend ∧
        E.loc p = .collect (adopt n (localMem (π p) C) x) k (fun _ => none) ∧
        localMem (π p) E = Function.update (localMem (π p) C)
          (sel p (adopt n (localMem (π p) C) x) (localMem (π p) C))
          (some (p, adopt n (localMem (π p) C) x)) ∧
        (∃ i, localMem (π p) C i ≠ some (p, adopt n (localMem (π p) C) x)) := by
  have hm0 := pos_of_hm hm
  obtain ⟨D, hD, hDp, hDm, hDl⟩ := collect_run (n := n) (sel := sel) (π := π) (m - 1) C x k view
    (by omega) hp hl
  rw [mixed_zero _ _ _ _ hk] at hDl
  set v := localMem (π p) C with hv
  change D.loc p = finish n sel p x v at hDl
  simp only [finish] at hDl
  have hpD : D.pend p ≠ none := by rw [hDp]; exact hp
  by_cases hb : ∀ i, v i = some (p, adopt n v x)
  · left
    refine Term.of_iter (m - 1 + 1) ?_
    rw [hD]
    exact term_write_true (x := adopt n v x) (j := sel p (adopt n v x) v) hpD (by rw [hDl]; simp [hb])
  · right
    push Not at hb
    have hDl' : D.loc p = .write (adopt n v x) (sel p (adopt n v x) v) false := by
      rw [hDl]; simp only [Loc.write.injEq, true_and, decide_eq_false_iff_not]; push Not; exact hb
    refine ⟨m - 1 + 1 + 1, (I n sel π).soloStep p D, ?_, ?_, ?_, ?_, hb⟩
    · rw [Function.iterate_succ_apply', hD]
    · rw [solo_write hpD hDl']; exact hDp
    · rw [solo_write hpD hDl']
      simp only [Function.update_self, afterWrite, Bool.false_eq_true, ↓reduceIte, startCollect,
        hm0, ↓reduceDIte]
      congr 1; ext; simp [hk]
    · rw [solo_write hpD hDl']
      funext i
      simp only [localMem, hDm, hv, Function.update_apply, (π p).injective.eq_iff]

/-- Once the preference is stable, the solo run decides (induction on `miss`). -/
lemma term_stable (hm : m + 1 = 2 * n) (hsel : SelOK sel) {p : P} :
    ∀ N (C : Cfg P V m) x k view, miss p x (localMem (π p) C) ≤ N → C.pend p ≠ none →
      C.loc p = .collect x k view → k.val = 0 → adopt n (localMem (π p) C) x = x →
      Term n sel π p C := by
  intro N
  induction N with
  | zero =>
    intro C x k view hN hp hl hk hst
    rcases round (sel := sel) hm hp hl hk with h | ⟨t, E, -, -, -, -, i, hi⟩
    · exact h
    · exfalso
      rw [hst] at hi
      have : 0 < miss p x (localMem (π p) C) :=
        Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
      omega
  | succ N ih =>
    intro C x k view hN hp hl hk hst
    rcases round (sel := sel) hm hp hl hk with h | ⟨t, E, hE, hEp, hEl, hEm, hex⟩
    · exact h
    · rw [hst] at hEl hEm hex
      refine Term.of_iter t ?_
      rw [hE]
      have hsel' := hsel p x _ hex
      refine ih E x k _ ?_ (by rw [hEp]; exact hp) hEl hk ?_
      · rw [hEm]; have := miss_update_lt hsel'; omega
      · rw [hEm]
        have := adopt_stable hm (localMem (π p) C) x (sel p x (localMem (π p) C)) p
        rwa [hst] at this

/-- From the start of a collect, the solo run decides. -/
lemma term_collect0 (hm : m + 1 = 2 * n) (hsel : SelOK sel) {p : P} {C : Cfg P V m}
    (hp : C.pend p ≠ none) {x : V} {k : Fin m} {view : Fin m → Option (P × V)}
    (hl : C.loc p = .collect x k view) (hk : k.val = 0) : Term n sel π p C := by
  rcases round (sel := sel) hm hp hl hk with h | ⟨t, E, hE, hEp, hEl, hEm, -⟩
  · exact h
  · refine Term.of_iter t ?_
    rw [hE]
    refine term_stable hm hsel _ E _ k _ le_rfl (by rw [hEp]; exact hp) hEl hk ?_
    rw [hEm]
    exact adopt_stable hm _ _ _ p

lemma term_write (hm : m + 1 = 2 * n) (hsel : SelOK sel) {p : P} {C : Cfg P V m}
    (hp : C.pend p ≠ none) {x : V} {j : Fin m} {b : Bool} (hl : C.loc p = .write x j b) :
    Term n sel π p C := by
  cases b with
  | true => exact term_write_true hp hl
  | false =>
    have hm0 := pos_of_hm hm
    refine Term.of_iter 1 (term_collect0 (x := x) (k := ⟨0, hm0⟩) (view := fun _ => none)
      hm hsel ?_ ?_ rfl)
    · simp only [Function.iterate_one, solo_write hp hl]; exact hp
    · simp [solo_write hp hl, afterWrite, startCollect, hm0]

lemma term_collect (hm : m + 1 = 2 * n) (hsel : SelOK sel) {p : P} {C : Cfg P V m}
    (hp : C.pend p ≠ none) {x : V} {k : Fin m} {view : Fin m → Option (P × V)}
    (hl : C.loc p = .collect x k view) : Term n sel π p C := by
  obtain ⟨D, hD, hDp, -, hDl⟩ := collect_run (n := n) (sel := sel) (π := π) (m - 1 - k.val) C x k
    view (by omega) hp hl
  refine Term.of_iter (m - 1 - k.val + 1) ?_
  rw [hD]
  exact term_write hm hsel (by rw [hDp]; exact hp) hDl

/-- Obstruction-freedom for `m + 1 = 2n` registers. -/
theorem obstructionFree_of_hm [Fintype P] (hm : m + 1 = 2 * n) (hcard : Fintype.card P ≤ n)
    (hsel : SelOK sel) : ((alg n sel).unnamed π).ObstructionFree := by
  intro C p ⟨α, hα⟩ hp
  have hI : Inv n π α C := inv_of_run (sel := sel) hm hcard hα
  change Term n sel π p C
  cases hl : C.loc p with
  | idle => exact absurd (hI.idle p hl) hp
  | collect x k view => exact term_collect hm hsel hp hl
  | write x j b => exact term_write hm hsel hp hl
  | done v => exact term_done hp hl

end Podc.MemoryAnonymousCoordination.Consensus
