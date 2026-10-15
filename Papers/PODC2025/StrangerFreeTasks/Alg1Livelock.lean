import Papers.PODC2025.StrangerFreeTasks.Alg1SafetyBasic
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic

/-!
# Algorithm 1 is not wait-free (counterexample to Theorem 3.1)

The paper claims (Theorem 3.1, §3.1) that Algorithm 1 solves `k`-bounded lattice agreement
wait-free. For every `k ≥ 2` this fails already with two processes `a ≠ b`: their seen sets
never exceed `{a, b}` (so the exit `|seen| > k` never fires), and the two processes can
alternate so that each second collect observes a fresh write of the other process:

* period (from `Good`): `a` collects; `b` writes; `a` collects again — `b`'s new triple
  `⟨b, seq_b, ·⟩` differs from the one `a` collected, so no output; `b` collects; `a` writes;
  `b` collects again — fails likewise. Freshness (`Good.fresh`: every stored triple of writer
  `w` has a sequence number `< w`'s current `seq`) makes every new write detectable.
* prefix (`prefixExec`): brings both processes to seen set `{a, b}`.

## Main results

* `good_period`, `good_prefix`: the invariant `Good` is reachable and preserved by a period.
* `exists_livelock`: an infinite one-shot execution in which `a` and `b` invoke once, stay
  pending forever and both take infinitely many steps.
* `alg1_not_waitFree`: `¬ (alg1 k).WaitFree` for `k ≥ 2` whenever there are two processes.

Generic run lemmas: `run_col1` / `run_col1_full` (a whole first collect), `run_col2` /
`run_col2_fail` (a whole second collect and the decision).
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {k : ℕ}

/-- Local state after the write of line 9 (and lines 10–11). -/
def afterWrite (l : Loc P k) : Loc P k :=
  { l with phase := .col1, j := 0, i := l.i + 1, seq := l.seq + 1 }

lemma step_write {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .wr) :
    (alg1 k).step C (.tau p) = some { C with
      mem := Function.update C.mem (C.loc p).i ⟨some p, (C.loc p).seq, (C.loc p).seen⟩,
      loc := Function.update C.loc p (afterWrite (C.loc p)) } := by
  simp [Impl.step, hp, alg1, hph, afterWrite]

lemma step_col1 {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .col1) :
    (alg1 k).step C (.tau p) = some { C with
      loc := Function.update C.loc p (afterCol1 k (C.loc p) (C.mem (C.loc p).j)) } := by
  simp [Impl.step, hp, alg1, hph]

lemma step_col2 {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .col2) :
    (alg1 k).step C (.tau p) = some { C with
      loc := Function.update C.loc p (afterCol2 k (C.loc p) (C.mem (C.loc p).j)) } := by
  simp [Impl.step, hp, alg1, hph]

lemma runFrom_tau_cons {C C1 : Cfg P k} {p : P} (h : (alg1 k).step C (.tau p) = some C1)
    (β : List (Label P (laObj P))) :
    (alg1 k).runFrom C (.tau p :: β) = (alg1 k).runFrom C1 β := by
  simp [Impl.runFrom_cons, h]

/-- Local state at the end of a first collect started at the loop index of `l`. -/
def endCol1 (l : Loc P k) (M : Fin (k + 1) → Triple P) (seen' : Finset P) : Loc P k :=
  { l with phase := .col2, j := 0, snap := true, seen := seen',
           collect := fun r => if r < l.j then l.collect r else M r }

lemma step_col1' {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .col1) :
    ∃ C', (alg1 k).step C (.tau p) = some C' ∧ C'.mem = C.mem ∧ C'.pend = C.pend ∧
      C'.loc = Function.update C.loc p (afterCol1 k (C.loc p) (C.mem (C.loc p).j)) :=
  ⟨_, step_col1 hp hph, rfl, rfl, rfl⟩

lemma step_col2' {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .col2) :
    ∃ C', (alg1 k).step C (.tau p) = some C' ∧ C'.mem = C.mem ∧ C'.pend = C.pend ∧
      C'.loc = Function.update C.loc p (afterCol2 k (C.loc p) (C.mem (C.loc p).j)) :=
  ⟨_, step_col2 hp hph, rfl, rfl, rfl⟩

/-- Running the rest of a first collect (lines 12–15). -/
lemma run_col1 (p : P) : ∀ (n : ℕ) (C : Cfg P k), C.pend p ≠ none → (C.loc p).phase = .col1 →
    (C.loc p).j.val + n = k + 1 →
    ∃ C' seen', (alg1 k).runFrom C (List.replicate n (.tau p)) = some C' ∧ C'.mem = C.mem ∧
      C'.pend = C.pend ∧ C'.loc = Function.update C.loc p (endCol1 (C.loc p) C.mem seen') ∧
      ∀ x, x ∈ seen' ↔ x ∈ (C.loc p).seen ∨ ∃ r, (C.loc p).j ≤ r ∧ x ∈ (C.mem r).seen := by
  intro n
  induction n with
  | zero => intro C _ _ h; have := (C.loc p).j.isLt; omega
  | succ m ih =>
    intro C hp hph hj
    obtain ⟨C1, hs, hm, hpd, hlc⟩ := step_col1' hp hph
    generalize hl : C.loc p = l at hlc hph hj ⊢
    obtain ⟨ph, j, i, seq, seen, col, snap, out⟩ := l
    simp only at hph hj; subst hph
    by_cases hjk : j.val = k
    · obtain rfl : m = 0 := by omega
      simp only [afterCol1, hjk, ↓reduceIte] at hlc
      refine ⟨C1, seen ∪ (C.mem j).seen, ?_, hm, hpd, ?_, ?_⟩
      · rw [List.replicate_one, Impl.runFrom_singleton, hs]
      · rw [hlc]; congr 1
        simp only [endCol1, Loc.mk.injEq, true_and, and_true]
        funext r
        by_cases h : r = j
        · subst h; simp
        · have : r < j := by
            rw [Fin.lt_def]; have := r.isLt; have := Fin.val_ne_of_ne h; omega
          simp [h, this]
      · have hle : ∀ r : Fin (k + 1), j ≤ r ↔ r = j := fun r =>
          ⟨fun h => Fin.ext (by have := r.isLt; rw [Fin.le_def] at h; omega),
           fun h => h ▸ le_refl _⟩
        intro x; simp [hle]
    · simp only [afterCol1, hjk, ↓reduceIte] at hlc
      have hj1 : (j + 1).val = j.val + 1 :=
        Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; omega)
      have hC1p := congrFun hlc p
      rw [Function.update_self] at hC1p
      obtain ⟨C', seen', hrun, hm', hpd', hlc', hseen'⟩ :=
        ih C1 (by rw [hpd]; exact hp) (by rw [hC1p]) (by rw [hC1p]; simp only; omega)
      refine ⟨C', seen', ?_, by rw [hm', hm], by rw [hpd', hpd], ?_, ?_⟩
      · rw [List.replicate_succ, runFrom_tau_cons hs]; exact hrun
      · rw [hlc', hC1p, hlc, Function.update_idem, hm]; congr 1
        simp only [endCol1, Loc.mk.injEq, true_and, and_true]
        funext r
        split_ifs with h1 h2 h2
        · exact Function.update_of_ne (ne_of_lt h2) _ _
        · obtain rfl : r = j := Fin.ext (by rw [Fin.lt_def, hj1] at h1; rw [Fin.lt_def] at h2; omega)
          simp
        · rw [Fin.lt_def, hj1] at h1; rw [Fin.lt_def] at h2; omega
        · rfl
      · intro x
        rw [hseen', hC1p, hm]
        simp only [Finset.mem_union]
        constructor
        · rintro ((h | h) | ⟨r, hr, h⟩)
          · exact Or.inl h
          · exact Or.inr ⟨j, le_refl _, h⟩
          · exact Or.inr ⟨r, by rw [Fin.le_def, hj1] at hr; rw [Fin.le_def]; omega, h⟩
        · rintro (h | ⟨r, hr, h⟩)
          · exact Or.inl (Or.inl h)
          · by_cases hrj : r = j
            · subst hrj; exact Or.inl (Or.inr h)
            · refine Or.inr ⟨r, ?_, h⟩
              rw [Fin.le_def, hj1]; rw [Fin.le_def] at hr
              have := Fin.val_ne_of_ne hrj; omega

/-- Running the rest of a second collect (lines 17–22) and the decision (lines 23–27). The
snapshot flag `s` of the decision can only be `true` if no register read differs from the
collected value. -/
lemma run_col2 (p : P) : ∀ (n : ℕ) (C : Cfg P k), C.pend p ≠ none → (C.loc p).phase = .col2 →
    (C.loc p).j.val + n = k + 1 → (∀ r, ((C.loc p).collect r).seen ⊆ (C.loc p).seen) →
    ∃ C' s, (alg1 k).runFrom C (List.replicate n (.tau p)) = some C' ∧ C'.mem = C.mem ∧
      C'.pend = C.pend ∧
      C'.loc = Function.update C.loc p (decision k { C.loc p with j := Fin.last k, snap := s }) ∧
      (s = true → (C.loc p).snap = true ∧ ∀ r, (C.loc p).j ≤ r → C.mem r = (C.loc p).collect r) := by
  intro n
  induction n with
  | zero => intro C _ _ h; have := (C.loc p).j.isLt; omega
  | succ m ih =>
    intro C hp hph hj hsub
    obtain ⟨C1, hs, hm, hpd, hlc⟩ := step_col2' hp hph
    generalize hl : C.loc p = l at hlc hph hj hsub ⊢
    obtain ⟨ph, j, i, seq, seen, col, snap, out⟩ := l
    simp only at hph hj hsub; subst hph
    have hu : seen ∪ (col j).seen = seen := Finset.union_eq_left.2 (hsub j)
    by_cases hjk : j.val = k
    · obtain rfl : m = 0 := by omega
      obtain rfl : j = Fin.last k := Fin.ext hjk
      simp only [afterCol2, hjk, ↓reduceIte, hu] at hlc
      refine ⟨C1, snap && decide (C.mem (Fin.last k) = col (Fin.last k)), ?_, hm, hpd, hlc, ?_⟩
      · rw [List.replicate_one, Impl.runFrom_singleton, hs]
      · intro h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        refine ⟨h.1, fun r hr => ?_⟩
        obtain rfl : r = Fin.last k := Fin.last_le_iff.1 hr
        exact h.2
    · simp only [afterCol2, hjk, ↓reduceIte, hu] at hlc
      have hj1 : (j + 1).val = j.val + 1 :=
        Fin.val_add_one_of_lt (by rw [Fin.lt_def, Fin.val_last]; omega)
      have hC1p := congrFun hlc p
      rw [Function.update_self] at hC1p
      obtain ⟨C', s, hrun, hm', hpd', hlc', hs'⟩ :=
        ih C1 (by rw [hpd]; exact hp) (by rw [hC1p]) (by rw [hC1p]; simp only; omega)
          (by rw [hC1p]; exact hsub)
      refine ⟨C', s, ?_, by rw [hm', hm], by rw [hpd', hpd], ?_, ?_⟩
      · rw [List.replicate_succ, runFrom_tau_cons hs]; exact hrun
      · rw [hlc', hC1p, hlc, Function.update_idem]
      · intro h
        obtain ⟨h1, h2⟩ := hs' h
        rw [hC1p] at h1 h2
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
        refine ⟨h1.1, fun r hr => ?_⟩
        simp only at hr
        by_cases hrj : r = j
        · subst hrj; exact h1.2
        · rw [← hm]; apply h2
          rw [Fin.le_def, hj1]; rw [Fin.le_def] at hr
          have := Fin.val_ne_of_ne hrj; omega

lemma step_write' {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .wr) :
    ∃ C', (alg1 k).runFrom C [.tau p] = some C' ∧
      C'.mem = Function.update C.mem (C.loc p).i ⟨some p, (C.loc p).seq, (C.loc p).seen⟩ ∧
      C'.pend = C.pend ∧ C'.loc = Function.update C.loc p (afterWrite (C.loc p)) :=
  ⟨_, (Impl.runFrom_singleton _ _ _).trans (step_write hp hph), rfl, rfl, rfl⟩

/-- Local state after the invocation of an idle process. -/
def invoked (l : Loc P k) : Loc P k := { l with phase := .wr }

lemma step_invoke {C : Cfg P k} {p : P} (hp : C.pend p = none) (hph : (C.loc p).phase = .idle) :
    (alg1 k).step C (.inv p ()) = some { C with
      pend := Function.update C.pend p (some ()),
      loc := Function.update C.loc p (invoked (C.loc p)) } := by
  simp [Impl.step, hp, alg1, hph, invoked]

lemma step_inv' {C : Cfg P k} {p : P} (hp : C.pend p = none) (hph : (C.loc p).phase = .idle) :
    ∃ C', (alg1 k).runFrom C [.inv p ()] = some C' ∧ C'.mem = C.mem ∧
      C'.pend = Function.update C.pend p (some ()) ∧
      C'.loc = Function.update C.loc p (invoked (C.loc p)) :=
  ⟨_, (Impl.runFrom_singleton _ _ _).trans (step_invoke hp hph), rfl, rfl, rfl⟩

/-- Local state after a complete first collect (from `j = 0`) on memory `M`. -/
def endCol1Full (l : Loc P k) (M : Fin (k + 1) → Triple P) : Loc P k :=
  { l with phase := .col2, j := 0, snap := true, collect := M,
           seen := l.seen ∪ Finset.univ.biUnion fun r => (M r).seen }

/-- A complete first collect. -/
lemma run_col1_full {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .col1)
    (hj : (C.loc p).j = 0) :
    ∃ C', (alg1 k).runFrom C (List.replicate (k + 1) (.tau p)) = some C' ∧ C'.mem = C.mem ∧
      C'.pend = C.pend ∧ C'.loc = Function.update C.loc p (endCol1Full (C.loc p) C.mem) := by
  obtain ⟨C', seen', h1, h2, h3, h4, h5⟩ := run_col1 p (k + 1) C hp hph (by rw [hj]; simp)
  refine ⟨C', h1, h2, h3, ?_⟩
  rw [h4]; congr 1
  simp only [endCol1, endCol1Full, hj, Fin.not_lt_zero, ↓reduceIte, Loc.mk.injEq, true_and,
    and_true]
  ext x; rw [h5]; simp [hj]

/-- The decision of lines 23–27 when the output condition fails. -/
lemma decision_wr (l : Loc P k) (hcard : l.seen.card ≤ k)
    (h : l.snap = false ∨ ∃ r, l.seen ≠ (l.collect r).seen) :
    decision k l = { l with phase := .wr } := by
  have h1 : ¬ k < l.seen.card := not_lt.2 hcard
  have h2 : ¬ (l.snap = true ∧ ∀ r, l.seen = (l.collect r).seen) := by
    rintro ⟨h1, h2⟩
    rcases h with h | ⟨r, hr⟩
    · rw [h1] at h; exact Bool.noConfusion h
    · exact hr (h2 r)
  unfold decision
  simp only [h1, h2, ↓reduceIte]

/-- A complete second collect (from `j = 0`) that does not produce an output: the seen set is
small and either some register changed since the first collect, or some collected seen set
differs from the process's seen set. -/
lemma run_col2_fail {C : Cfg P k} {p : P} (hp : C.pend p ≠ none) (hph : (C.loc p).phase = .col2)
    (hj : (C.loc p).j = 0) (hsub : ∀ r, ((C.loc p).collect r).seen ⊆ (C.loc p).seen)
    (hcard : (C.loc p).seen.card ≤ k)
    (hfail : (∃ r, C.mem r ≠ (C.loc p).collect r) ∨ ∃ r, (C.loc p).seen ≠ ((C.loc p).collect r).seen) :
    ∃ C' s, (alg1 k).runFrom C (List.replicate (k + 1) (.tau p)) = some C' ∧ C'.mem = C.mem ∧
      C'.pend = C.pend ∧
      C'.loc = Function.update C.loc p { C.loc p with j := Fin.last k, snap := s, phase := .wr } := by
  obtain ⟨C', s, h1, h2, h3, h4, h5⟩ := run_col2 p (k + 1) C hp hph (by rw [hj]; simp) hsub
  refine ⟨C', s, h1, h2, h3, ?_⟩
  rw [h4]; congr 1
  refine decision_wr { C.loc p with j := Fin.last k, snap := s } hcard ?_
  rcases hfail with ⟨r, hr⟩ | ⟨r, hr⟩
  · left
    cases hs : s
    · rfl
    · exact absurd ((h5 hs).2 r (by rw [hj]; exact Fin.zero_le _)) hr
  · exact Or.inr ⟨r, hr⟩

/-! ### The livelock -/

/-- The configurations at the start of each period of the livelock: `a` is about to start its
first collect, `b` is about to write, both have seen exactly `{a, b}`, all registers hold seen
sets inside `{a, b}`, and every register value is *older* than its writer's current sequence
number (so a new write is always detected by a concurrent second collect). -/
structure Good (a b : P) (C : Cfg P k) : Prop where
  pend_a : C.pend a ≠ none
  pend_b : C.pend b ≠ none
  phase_a : (C.loc a).phase = .col1
  j_a : (C.loc a).j = 0
  seen_a : (C.loc a).seen = {a, b}
  phase_b : (C.loc b).phase = .wr
  seen_b : (C.loc b).seen = {a, b}
  mem_seen : ∀ r, (C.mem r).seen ⊆ {a, b}
  fresh : ∀ r w, (C.mem r).id = some w → (C.mem r).seq < (C.loc w).seq

/-- One period of the livelock: `a` collects, `b` writes, `a` collects again (and fails),
`b` collects, `a` writes, `b` collects again (and fails). -/
def period (a b : P) (k : ℕ) : List (Label P (laObj P)) :=
  List.replicate (k + 1) (.tau a) ++ [.tau b] ++ List.replicate (k + 1) (.tau a) ++
    List.replicate (k + 1) (.tau b) ++ [.tau a] ++ List.replicate (k + 1) (.tau b)

lemma union_biUnion_eq {T l : Finset P} {M : Fin (k + 1) → Triple P} (h1 : l = T)
    (h2 : ∀ r, (M r).seen ⊆ T) : l ∪ Finset.univ.biUnion (fun r => (M r).seen) = T := by
  subst h1; exact Finset.union_eq_left.2 (Finset.biUnion_subset.2 fun r _ => h2 r)

/-- One period of the livelock leads from a `Good` configuration to a `Good` configuration. -/
theorem good_period {a b : P} (hab : a ≠ b) (hk : 2 ≤ k) {C : Cfg P k} (G : Good a b C) :
    ∃ C', (alg1 k).runFrom C (period a b k) = some C' ∧ Good a b C' := by
  obtain ⟨la, hla⟩ : ∃ l, C.loc a = l := ⟨_, rfl⟩
  obtain ⟨lb, hlb⟩ : ∃ l, C.loc b = l := ⟨_, rfl⟩
  have hab' := hab.symm
  -- 1. `a`: first collect
  obtain ⟨C1, r1, hm1, hp1, hl1⟩ := run_col1_full G.pend_a G.phase_a G.j_a
  rw [hla] at hl1
  have ha1 : C1.loc a = endCol1Full la C.mem := by rw [hl1, Function.update_self]
  have hb1 : C1.loc b = lb := by rw [hl1, Function.update_of_ne hab', hlb]
  -- 2. `b`: write
  obtain ⟨C2, r2, hm2, hp2, hl2⟩ := step_write' (C := C1) (p := b)
    (by rw [hp1]; exact G.pend_b) (by rw [hb1, ← hlb]; exact G.phase_b)
  rw [hb1, hm1] at hm2; rw [hb1] at hl2
  have ha2 : C2.loc a = endCol1Full la C.mem := by rw [hl2, Function.update_of_ne hab, ha1]
  have hb2 : C2.loc b = afterWrite lb := by rw [hl2, Function.update_self]
  -- 3. `a`: second collect, fails since `b`'s write is new
  have hseenA : (endCol1Full la C.mem).seen = {a, b} :=
    union_biUnion_eq (by rw [← hla]; exact G.seen_a) G.mem_seen
  have hfail3 : C2.mem lb.i ≠ (C2.loc a).collect lb.i := by
    rw [ha2, hm2, Function.update_self]
    show _ ≠ C.mem lb.i
    intro h
    have := G.fresh lb.i b (by rw [← h])
    rw [← h, hlb] at this
    exact lt_irrefl _ this
  obtain ⟨C3, s3, r3, hm3, hp3, hl3⟩ := run_col2_fail (C := C2) (p := a)
    (by rw [hp2, hp1]; exact G.pend_a) (by rw [ha2]; rfl) (by rw [ha2]; rfl)
    (by rw [ha2, hseenA]; exact G.mem_seen) (by rw [ha2, hseenA, Finset.card_pair hab]; exact hk)
    (Or.inl ⟨_, hfail3⟩)
  rw [ha2] at hl3
  have ha3 : C3.loc a = { endCol1Full la C.mem with j := Fin.last k, snap := s3, phase := .wr } := by
    rw [hl3, Function.update_self]
  have hb3 : C3.loc b = afterWrite lb := by rw [hl3, Function.update_of_ne hab', hb2]
  -- 4. `b`: first collect
  obtain ⟨C4, r4, hm4, hp4, hl4⟩ := run_col1_full (C := C3) (p := b)
    (by rw [hp3, hp2, hp1]; exact G.pend_b) (by rw [hb3]; rfl) (by rw [hb3]; rfl)
  rw [hb3, hm3] at hl4; rw [hm3] at hm4
  have ha4 : C4.loc a = { endCol1Full la C.mem with j := Fin.last k, snap := s3, phase := .wr } := by
    rw [hl4, Function.update_of_ne hab, ha3]
  have hb4 : C4.loc b = endCol1Full (afterWrite lb) C2.mem := by rw [hl4, Function.update_self]
  -- 5. `a`: write
  obtain ⟨C5, r5, hm5, hp5, hl5⟩ := step_write' (C := C4) (p := a)
    (by rw [hp4, hp3, hp2, hp1]; exact G.pend_a) (by rw [ha4])
  rw [ha4, hm4] at hm5; rw [ha4] at hl5
  replace hm5 : C5.mem = Function.update C2.mem la.i ⟨some a, la.seq, {a, b}⟩ := by
    rw [hm5, ← hseenA]; rfl
  have ha5 : C5.loc a = afterWrite
      { endCol1Full la C.mem with j := Fin.last k, snap := s3, phase := .wr } := by
    rw [hl5, Function.update_self]
  have hb5 : C5.loc b = endCol1Full (afterWrite lb) C2.mem := by
    rw [hl5, Function.update_of_ne hab', hb4]
  -- 6. `b`: second collect, fails since `a`'s write is new
  have hmem2 : ∀ r, (C2.mem r).seen ⊆ {a, b} := by
    intro r; rw [hm2, Function.update_apply]
    split_ifs
    · simp [← hlb, G.seen_b]
    · exact G.mem_seen r
  have hseenB : (endCol1Full (afterWrite lb) C2.mem).seen = {a, b} :=
    union_biUnion_eq (by rw [← hlb]; exact G.seen_b) hmem2
  have hfail6 : C5.mem la.i ≠ (C5.loc b).collect la.i := by
    rw [hb5, hm5]
    show Function.update C2.mem _ _ la.i ≠ C2.mem la.i
    rw [Function.update_self, hm2, Function.update_apply]
    split_ifs with h
    · simp [hab]
    · intro h'
      have := G.fresh la.i a (by rw [← h'])
      rw [← h', hla] at this
      exact lt_irrefl _ this
  obtain ⟨C6, s6, r6, hm6, hp6, hl6⟩ := run_col2_fail (C := C5) (p := b)
    (by rw [hp5, hp4, hp3, hp2, hp1]; exact G.pend_b) (by rw [hb5]; rfl) (by rw [hb5]; rfl)
    (by rw [hb5, hseenB]; exact hmem2) (by rw [hb5, hseenB, Finset.card_pair hab]; exact hk)
    (Or.inl ⟨_, hfail6⟩)
  have ha6 : C6.loc a = C5.loc a := by rw [hl6, Function.update_of_ne hab]
  have hb6 : C6.loc b = { C5.loc b with j := Fin.last k, snap := s6, phase := .wr } := by
    rw [hl6, Function.update_self]
  have hother : ∀ w, w ≠ a → w ≠ b → C6.loc w = C.loc w := by
    intro w h1 h2
    rw [hl6, Function.update_of_ne h2, hl5, Function.update_of_ne h1, hl4,
      Function.update_of_ne h2, hl3, Function.update_of_ne h1, hl2, Function.update_of_ne h2,
      hl1, Function.update_of_ne h1]
  refine ⟨C6, ?_, ?_⟩
  · unfold period
    rw [Impl.runFrom_append_of_eq _ ((Impl.runFrom_append_of_eq _ ((Impl.runFrom_append_of_eq _
      ((Impl.runFrom_append_of_eq _ ((Impl.runFrom_append_of_eq _ r1 _).trans r2) _).trans r3)
      _).trans r4) _).trans r5) _]
    exact r6
  · have hpend : C6.pend = C.pend := by rw [hp6, hp5, hp4, hp3, hp2, hp1]
    have hseqa : (C6.loc a).seq = la.seq + 1 := by rw [ha6, ha5]; rfl
    have hseqb : (C6.loc b).seq = lb.seq + 1 := by rw [hb6, hb5]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hpend]; exact G.pend_a
    · rw [hpend]; exact G.pend_b
    · rw [ha6, ha5]; rfl
    · rw [ha6, ha5]; rfl
    · rw [ha6, ha5]; exact hseenA
    · rw [hb6]
    · rw [hb6, hb5]; exact hseenB
    · intro r; rw [hm6, hm5, Function.update_apply]
      split_ifs
      · simp
      · exact hmem2 r
    · intro r w
      rw [hm6, hm5, hm2]
      simp only [Function.update_apply]
      split_ifs with h1 h2
      · intro h; simp only [Option.some.injEq] at h; rw [← h, hseqa]; dsimp only; omega
      · intro h; simp only [Option.some.injEq] at h; rw [← h, hseqb]; dsimp only; omega
      · intro h
        have := G.fresh r w h
        by_cases hwa : w = a
        · rw [hwa] at this ⊢; rw [hseqa]; rw [hla] at this; omega
        by_cases hwb : w = b
        · rw [hwb] at this ⊢; rw [hseqb]; rw [hlb] at this; omega
        rw [hother w hwa hwb]; exact this

lemma loc_of_update {C C' : Cfg P k} {p : P} {X : Loc P k}
    (h : C'.loc = Function.update C.loc p X) : C'.loc p = X ∧ ∀ q, q ≠ p → C'.loc q = C.loc q :=
  ⟨by rw [h, Function.update_self], fun q hq => by rw [h, Function.update_of_ne hq]⟩

omit [DecidableEq P] in
lemma seen_update_subset {M : Fin (k + 1) → Triple P} {S : Finset P} {i : Fin (k + 1)}
    {T : Triple P} (hM : ∀ r, (M r).seen ⊆ S) (hT : T.seen ⊆ S) :
    ∀ r, (Function.update M i T r).seen ⊆ S := by
  intro r; rw [Function.update_apply]; split_ifs
  · exact hT
  · exact hM r

/-- The prefix of the livelock: both processes invoke; `a` writes, collects twice (no output,
since the other registers are still initial), writes again; `b` writes, collects twice (no output,
`A[0]` has seen set `{b}`); `a` collects twice (no output, likewise) and writes. -/
def prefixExec (a b : P) (k : ℕ) : List (Label P (laObj P)) :=
  [.inv a ()] ++ [.inv b ()] ++ [.tau a] ++ List.replicate (k + 1) (.tau a) ++
    List.replicate (k + 1) (.tau a) ++ [.tau a] ++ [.tau b] ++ List.replicate (k + 1) (.tau b) ++
    List.replicate (k + 1) (.tau b) ++ List.replicate (k + 1) (.tau a) ++
    List.replicate (k + 1) (.tau a) ++ [.tau a]

/-- The prefix leads to a `Good` configuration. -/
theorem good_prefix {a b : P} (hab : a ≠ b) (hk : 2 ≤ k) :
    ∃ C, (alg1 k).run (prefixExec a b k) = some C ∧ Good a b C := by
  have hab' := hab.symm
  have h10 : (1 : Fin (k + 1)) ≠ 0 := by
    rw [Ne, Fin.ext_iff, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)]; omega
  have hl0 : Fin.last k ≠ 0 := by simp [Fin.ext_iff]; omega
  -- 1., 2. invocations
  obtain ⟨D1, r1, hm1, hp1, hl1⟩ := step_inv' (C := (alg1 k).initCfg) (p := a) rfl rfl
  obtain ⟨D2, r2, hm2, hp2, hl2⟩ := step_inv' (C := D1) (p := b)
    (by rw [hp1, Function.update_of_ne hab']; rfl) (by rw [hl1, Function.update_of_ne hab']; rfl)
  have hpa : D2.pend a ≠ none := by
    rw [hp2, Function.update_of_ne hab, hp1, Function.update_self]; simp
  have hpb : D2.pend b ≠ none := by rw [hp2, Function.update_self]; simp
  obtain ⟨A2, hA2, hA2ph, hA2i, hA2seq, hA2seen⟩ : ∃ A, D2.loc a = A ∧ A.phase = .wr ∧
      A.i = 0 ∧ A.seq = 0 ∧ A.seen = {a} :=
    ⟨_, by rw [(loc_of_update hl2).2 a hab, (loc_of_update hl1).1], rfl, rfl, rfl, rfl⟩
  obtain ⟨B2, hB2, hB2ph, hB2i, hB2seq, hB2seen⟩ : ∃ B, D2.loc b = B ∧ B.phase = .wr ∧
      B.i = 0 ∧ B.seq = 0 ∧ B.seen = {b} :=
    ⟨_, by rw [(loc_of_update hl2).1, (loc_of_update hl1).2 b hab'], rfl, rfl, rfl, rfl⟩
  -- 3. `a` writes `A[0] := ⟨a, 0, {a}⟩`
  obtain ⟨D3, r3, hm3, hp3, hl3⟩ := step_write' (C := D2) (p := a) hpa (by rw [hA2, hA2ph])
  rw [hA2, hA2i, hA2seq, hA2seen, hm2, hm1] at hm3; rw [hA2] at hl3
  obtain ⟨A3, hA3, hA3ph, hA3j, hA3i, hA3seq, hA3seen⟩ : ∃ A, D3.loc a = A ∧ A.phase = .col1 ∧
      A.j = 0 ∧ A.i = 1 ∧ A.seq = 1 ∧ A.seen = {a} :=
    ⟨_, (loc_of_update hl3).1, rfl, rfl, by simp [afterWrite, hA2i], by simp [afterWrite, hA2seq],
      by simp [afterWrite, hA2seen]⟩
  have hB3 : D3.loc b = B2 := by rw [(loc_of_update hl3).2 b hab', hB2]
  have hmem3 : ∀ r, (D3.mem r).seen ⊆ {a} := by
    rw [hm3]; exact seen_update_subset (fun r => by simp [Impl.initCfg, alg1, Triple.init])
      (by simp)
  -- 4. `a`: first collect
  obtain ⟨D4, r4, hm4, hp4, hl4⟩ := run_col1_full (C := D3) (p := a) (by rw [hp3]; exact hpa)
    (by rw [hA3, hA3ph]) (by rw [hA3, hA3j])
  rw [hA3] at hl4
  obtain ⟨A4, hA4, hA4ph, hA4j, hA4i, hA4seq, hA4seen, hA4col⟩ : ∃ A, D4.loc a = A ∧
      A.phase = .col2 ∧ A.j = 0 ∧ A.i = 1 ∧ A.seq = 1 ∧ A.seen = {a} ∧ A.collect = D3.mem :=
    ⟨_, (loc_of_update hl4).1, rfl, rfl, hA3i, hA3seq, union_biUnion_eq hA3seen hmem3, rfl⟩
  have hB4 : D4.loc b = B2 := by rw [(loc_of_update hl4).2 b hab', hB3]
  -- 5. `a`: second collect, fails since `A[k]` still holds the initial value
  obtain ⟨D5, s5, r5, hm5, hp5, hl5⟩ := run_col2_fail (C := D4) (p := a)
    (by rw [hp4, hp3]; exact hpa) (by rw [hA4, hA4ph]) (by rw [hA4, hA4j])
    (by rw [hA4, hA4seen, hA4col]; exact hmem3) (by rw [hA4, hA4seen]; simp; omega)
    (Or.inr ⟨Fin.last k, by
      rw [hA4, hA4seen, hA4col, hm3, Function.update_of_ne hl0]
      simp [Impl.initCfg, alg1, Triple.init]⟩)
  rw [hA4] at hl5
  obtain ⟨A5, hA5, hA5ph, hA5i, hA5seq, hA5seen⟩ : ∃ A, D5.loc a = A ∧ A.phase = .wr ∧
      A.i = 1 ∧ A.seq = 1 ∧ A.seen = {a} :=
    ⟨_, (loc_of_update hl5).1, rfl, hA4i, hA4seq, hA4seen⟩
  have hB5 : D5.loc b = B2 := by rw [(loc_of_update hl5).2 b hab', hB4]
  -- 6. `a` writes `A[1] := ⟨a, 1, {a}⟩`
  obtain ⟨D6, r6, hm6, hp6, hl6⟩ := step_write' (C := D5) (p := a)
    (by rw [hp5, hp4, hp3]; exact hpa) (by rw [hA5, hA5ph])
  rw [hA5, hA5i, hA5seq, hA5seen, hm5, hm4] at hm6; rw [hA5] at hl6
  obtain ⟨A6, hA6, hA6ph, hA6j, hA6i, hA6seq, hA6seen⟩ : ∃ A, D6.loc a = A ∧ A.phase = .col1 ∧
      A.j = 0 ∧ A.i = 1 + 1 ∧ A.seq = 2 ∧ A.seen = {a} :=
    ⟨_, (loc_of_update hl6).1, rfl, rfl, by simp [afterWrite, hA5i],
      by simp [afterWrite, hA5seq], by simp [afterWrite, hA5seen]⟩
  have hB6 : D6.loc b = B2 := by rw [(loc_of_update hl6).2 b hab', hB5]
  -- 7. `b` writes `A[0] := ⟨b, 0, {b}⟩`
  obtain ⟨D7, r7, hm7, hp7, hl7⟩ := step_write' (C := D6) (p := b)
    (by rw [hp6, hp5, hp4, hp3]; exact hpb) (by rw [hB6, hB2ph])
  rw [hB6, hB2i, hB2seq, hB2seen, hm6] at hm7; rw [hB6] at hl7
  obtain ⟨B7, hB7, hB7ph, hB7j, hB7seq, hB7seen⟩ : ∃ B, D7.loc b = B ∧ B.phase = .col1 ∧
      B.j = 0 ∧ B.seq = 1 ∧ B.seen = {b} :=
    ⟨_, (loc_of_update hl7).1, rfl, rfl, by simp [afterWrite, hB2seq], by simp [afterWrite, hB2seen]⟩
  have hA7 : D7.loc a = A6 := by rw [(loc_of_update hl7).2 a hab, hA6]
  have hmem7 : ∀ r, (D7.mem r).seen ⊆ {a, b} := by
    rw [hm7]
    refine seen_update_subset (seen_update_subset (fun r => (hmem3 r).trans (by simp))
      (by simp)) (by simp)
  have hm70 : (D7.mem 0).seen = {b} := by rw [hm7, Function.update_self]
  have hm71 : a ∈ (D7.mem 1).seen := by
    rw [hm7, Function.update_of_ne h10, Function.update_self]; simp
  have hm70' : ({a, b} : Finset P) ≠ (D7.mem 0).seen := by
    rw [hm70]; intro h
    have : a ∈ ({b} : Finset P) := h ▸ Finset.mem_insert_self a {b}
    exact hab (Finset.mem_singleton.1 this)
  have hcard : ({a, b} : Finset P).card ≤ k := by rw [Finset.card_pair hab]; exact hk
  -- 8. `b`: first collect (sees `a`)
  obtain ⟨D8, r8, hm8, hp8, hl8⟩ := run_col1_full (C := D7) (p := b)
    (by rw [hp7, hp6, hp5, hp4, hp3]; exact hpb) (by rw [hB7, hB7ph]) (by rw [hB7, hB7j])
  rw [hB7] at hl8
  obtain ⟨B8, hB8, hB8ph, hB8j, hB8seq, hB8seen, hB8col⟩ : ∃ B, D8.loc b = B ∧
      B.phase = .col2 ∧ B.j = 0 ∧ B.seq = 1 ∧ B.seen = {a, b} ∧ B.collect = D7.mem := by
    refine ⟨_, (loc_of_update hl8).1, rfl, rfl, hB7seq, ?_, rfl⟩
    show B7.seen ∪ _ = _
    rw [hB7seen]
    refine Finset.Subset.antisymm (Finset.union_subset (by simp)
      (Finset.biUnion_subset.2 fun r _ => hmem7 r)) ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨1, Finset.mem_univ _, hm71⟩)
    · simp
  have hA8 : D8.loc a = A6 := by rw [(loc_of_update hl8).2 a hab, hA7]
  -- 9. `b`: second collect, fails since `A[0]` has seen set `{b}`
  obtain ⟨D9, s9, r9, hm9, hp9, hl9⟩ := run_col2_fail (C := D8) (p := b)
    (by rw [hp8, hp7, hp6, hp5, hp4, hp3]; exact hpb) (by rw [hB8, hB8ph]) (by rw [hB8, hB8j])
    (by rw [hB8, hB8seen, hB8col]; exact hmem7) (by rw [hB8, hB8seen]; exact hcard)
    (Or.inr ⟨0, by rw [hB8, hB8seen, hB8col]; exact hm70'⟩)
  rw [hB8] at hl9
  obtain ⟨B9, hB9, hB9ph, hB9seq, hB9seen⟩ : ∃ B, D9.loc b = B ∧ B.phase = .wr ∧ B.seq = 1 ∧
      B.seen = {a, b} :=
    ⟨_, (loc_of_update hl9).1, rfl, hB8seq, hB8seen⟩
  have hA9 : D9.loc a = A6 := by rw [(loc_of_update hl9).2 a hab, hA8]
  -- 10. `a`: first collect (sees `b`)
  obtain ⟨D10, r10, hm10, hp10, hl10⟩ := run_col1_full (C := D9) (p := a)
    (by rw [hp9, hp8, hp7, hp6, hp5, hp4, hp3]; exact hpa) (by rw [hA9, hA6ph]) (by rw [hA9, hA6j])
  rw [hA9, hm9, hm8] at hl10
  obtain ⟨A10, hA10, hA10ph, hA10j, hA10i, hA10seq, hA10seen, hA10col⟩ : ∃ A, D10.loc a = A ∧
      A.phase = .col2 ∧ A.j = 0 ∧ A.i = 1 + 1 ∧ A.seq = 2 ∧ A.seen = {a, b} ∧ A.collect = D7.mem := by
    refine ⟨_, (loc_of_update hl10).1, rfl, rfl, hA6i, hA6seq, ?_, rfl⟩
    show A6.seen ∪ _ = _
    rw [hA6seen]
    refine Finset.Subset.antisymm (Finset.union_subset (by simp)
      (Finset.biUnion_subset.2 fun r _ => hmem7 r)) ?_
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · simp
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨0, Finset.mem_univ _, by simp [hm70]⟩)
  have hB10 : D10.loc b = B9 := by rw [(loc_of_update hl10).2 b hab', hB9]
  -- 11. `a`: second collect, fails since `A[0]` has seen set `{b}`
  obtain ⟨D11, s11, r11, hm11, hp11, hl11⟩ := run_col2_fail (C := D10) (p := a)
    (by rw [hp10, hp9, hp8, hp7, hp6, hp5, hp4, hp3]; exact hpa) (by rw [hA10, hA10ph])
    (by rw [hA10, hA10j]) (by rw [hA10, hA10seen, hA10col]; exact hmem7)
    (by rw [hA10, hA10seen]; exact hcard)
    (Or.inr ⟨0, by rw [hA10, hA10seen, hA10col]; exact hm70'⟩)
  rw [hA10] at hl11
  obtain ⟨A11, hA11, hA11ph, hA11i, hA11seq, hA11seen⟩ : ∃ A, D11.loc a = A ∧ A.phase = .wr ∧
      A.i = 1 + 1 ∧ A.seq = 2 ∧ A.seen = {a, b} :=
    ⟨_, (loc_of_update hl11).1, rfl, hA10i, hA10seq, hA10seen⟩
  have hB11 : D11.loc b = B9 := by rw [(loc_of_update hl11).2 b hab', hB10]
  -- 12. `a` writes `A[2] := ⟨a, 2, {a, b}⟩`
  obtain ⟨D12, r12, hm12, hp12, hl12⟩ := step_write' (C := D11) (p := a)
    (by rw [hp11, hp10, hp9, hp8, hp7, hp6, hp5, hp4, hp3]; exact hpa) (by rw [hA11, hA11ph])
  rw [hA11, hA11i, hA11seq, hA11seen, hm11, hm10, hm9, hm8] at hm12; rw [hA11] at hl12
  have hA12 := (loc_of_update hl12).1
  have hB12 : D12.loc b = B9 := by rw [(loc_of_update hl12).2 b hab', hB11]
  refine ⟨D12, ?_, ?_⟩
  · unfold prefixExec Impl.run
    have e := (Impl.runFrom_append_of_eq _ r1 _).trans r2
    have e := (Impl.runFrom_append_of_eq _ e _).trans r3
    have e := (Impl.runFrom_append_of_eq _ e _).trans r4
    have e := (Impl.runFrom_append_of_eq _ e _).trans r5
    have e := (Impl.runFrom_append_of_eq _ e _).trans r6
    have e := (Impl.runFrom_append_of_eq _ e _).trans r7
    have e := (Impl.runFrom_append_of_eq _ e _).trans r8
    have e := (Impl.runFrom_append_of_eq _ e _).trans r9
    have e := (Impl.runFrom_append_of_eq _ e _).trans r10
    have e := (Impl.runFrom_append_of_eq _ e _).trans r11
    exact (Impl.runFrom_append_of_eq _ e _).trans r12
  · have hpend : D12.pend = D2.pend := by
      rw [hp12, hp11, hp10, hp9, hp8, hp7, hp6, hp5, hp4, hp3]
    have hseqa : (D12.loc a).seq = 3 := by rw [hA12]; simp [afterWrite, hA11seq]
    have hseqb : (D12.loc b).seq = 1 := by rw [hB12, hB9seq]
    refine ⟨by rw [hpend]; exact hpa, by rw [hpend]; exact hpb, by rw [hA12]; rfl,
      by rw [hA12]; rfl, by rw [hA12]; exact hA11seen, by rw [hB12, hB9ph],
      by rw [hB12, hB9seen], ?_, ?_⟩
    · rw [hm12]; exact seen_update_subset hmem7 (by simp)
    · intro r w
      rw [hm12, hm7, hm3]
      simp only [Function.update_apply]
      split_ifs <;> simp [Impl.initCfg, alg1, Triple.init] <;> rintro rfl <;> simp [hseqa, hseqb]

/-- The livelocked execution, cut after `n` periods. -/
def livelockExec (a b : P) (k : ℕ) : ℕ → List (Label P (laObj P))
  | 0 => prefixExec a b k
  | n + 1 => livelockExec a b k n ++ period a b k

lemma livelockExec_good {a b : P} (hab : a ≠ b) (hk : 2 ≤ k) :
    ∀ n, ∃ C, (alg1 k).run (livelockExec a b k n) = some C ∧ Good a b C
  | 0 => good_prefix hab hk
  | n + 1 => by
    obtain ⟨C, hC, G⟩ := livelockExec_good hab hk n
    obtain ⟨C', hC', G'⟩ := good_period hab hk G
    exact ⟨C', by rw [livelockExec, Impl.run_append_of_eq _ hC]; exact hC', G'⟩

omit [DecidableEq P] in
lemma livelockExec_shape (a b : P) (k : ℕ) :
    ∀ n, ∃ rest, livelockExec a b k n = .inv a () :: .inv b () :: rest ∧
      ∀ ℓ ∈ rest, ℓ = .tau a ∨ ℓ = .tau b
  | 0 => ⟨_, rfl, by
      intro ℓ hℓ
      simp only [List.append_eq, List.nil_append, List.mem_append, List.mem_cons,
        List.mem_replicate, List.not_mem_nil] at hℓ
      tauto⟩
  | n + 1 => by
    obtain ⟨rest, h, hr⟩ := livelockExec_shape a b k n
    refine ⟨rest ++ period a b k, by rw [livelockExec, h]; rfl, ?_⟩
    intro ℓ hℓ
    rcases List.mem_append.1 hℓ with hℓ | hℓ
    · exact hr ℓ hℓ
    · simp only [period, List.mem_append, List.mem_cons, List.mem_replicate,
        List.not_mem_nil] at hℓ
      tauto

omit [DecidableEq P] in
lemma length_livelockExec (a b : P) (k : ℕ) : ∀ n, n ≤ (livelockExec a b k n).length
  | 0 => Nat.zero_le _
  | n + 1 => by
    have := length_livelockExec a b k n
    rw [livelockExec, List.length_append]
    have : 0 < (period a b k).length := by simp [period]; omega
    omega

lemma livelockExec_oneShot {a b : P} (hab : a ≠ b) (n : ℕ) : OneShot (livelockExec a b k n) := by
  intro p
  obtain ⟨rest, h, hr⟩ := livelockExec_shape a b k n
  have hrest : opsOf rest p = [] := by
    simp only [opsOf, List.filterMap_eq_nil_iff]
    intro ℓ hℓ
    rcases hr ℓ hℓ with rfl | rfl <;> rfl
  rw [h, opsOf_cons, opsOf_cons, hrest]
  by_cases hpa : a = p
  · subst hpa; simp [Label.invOf, hab.symm]
  · by_cases hpb : b = p
    · subst hpb; simp [Label.invOf, hpa]
    · simp [Label.invOf, hpa, hpb]

lemma getElem_mem_of_eq_cons {α : Type} {L rest : List α} {x y : α} {m : ℕ} (hm : 2 ≤ m)
    (hL : m < L.length) (h : L = x :: y :: rest) : L[m] ∈ rest := by
  subst h
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  exact List.getElem_mem _

/-- **The livelock of Algorithm 1.** For `k ≥ 2` and two distinct processes `a`, `b` there is
an infinite execution in which `a` and `b` each invoke the task once (labels `0` and `1`) and
then only take steps (all later labels are `tau a` or `tau b`), both stay pending forever, and
both take infinitely many steps. -/
theorem exists_livelock {a b : P} (hab : a ≠ b) (hk : 2 ≤ k) :
    ∃ e : (alg1 k).InfExec, e.lbl 0 = .inv a () ∧ e.lbl 1 = .inv b () ∧
      (∀ m, 2 ≤ m → e.lbl m = .tau a ∨ e.lbl m = .tau b) ∧
      (∀ n, OneShot ((List.range n).map e.lbl)) ∧
      (∀ m, 2 ≤ m → (e.cfg m).pend a ≠ none ∧ (e.cfg m).pend b ≠ none) ∧
      (∀ N, ∃ m ≥ N, e.lbl m = .tau a) ∧ (∀ N, ∃ m ≥ N, e.lbl m = .tau b) := by
  obtain ⟨e, hlbl, -⟩ := (alg1 k).exists_infExec_of_chain (livelockExec a b k)
    (fun n => List.prefix_append _ _) (length_livelockExec a b k)
    (fun n => let ⟨C, hC, _⟩ := livelockExec_good hab hk n; ⟨C, hC⟩)
  have hlen : ∀ m, m < (livelockExec a b k (m + 1)).length := fun m => by
    have := length_livelockExec a b k (m + 1); omega
  have hl0 : e.lbl 0 = .inv a () := by
    rw [hlbl 1 0 (hlen 0)]
    obtain ⟨rest, h, -⟩ := livelockExec_shape a b k 1
    simp only [h, List.getElem_cons_zero]
  have hl1 : e.lbl 1 = .inv b () := by
    rw [hlbl 2 1 (hlen 1)]
    obtain ⟨rest, h, -⟩ := livelockExec_shape a b k 2
    simp only [h, List.getElem_cons_succ, List.getElem_cons_zero]
  have htau : ∀ m, 2 ≤ m → e.lbl m = .tau a ∨ e.lbl m = .tau b := by
    intro m hm
    rw [hlbl (m + 1) m (hlen m)]
    obtain ⟨rest, h, hr⟩ := livelockExec_shape a b k (m + 1)
    exact hr _ (getElem_mem_of_eq_cons hm (hlen m) h)
  refine ⟨e, hl0, hl1, htau, ?_, ?_, ?_, ?_⟩
  · intro n
    have hn := length_livelockExec a b k n
    have : (List.range n).map e.lbl = (livelockExec a b k n).take n := by
      apply List.ext_getElem
      · simp; omega
      · intro i h1 h2
        simp only [List.getElem_map, List.getElem_range, List.getElem_take]
        exact hlbl n i (by simp at h1; omega)
    rw [this]
    have h := livelockExec_oneShot (k := k) hab n
    rw [← List.take_append_drop n (livelockExec a b k n)] at h
    exact h.of_append
  · have h1 := e.step_eq 0
    rw [e.cfg_zero, hl0] at h1
    have h2 := e.step_eq 1
    rw [hl1] at h2
    have hp1 := (Impl.step_inv h1).2.2.1
    have hp2 := (Impl.step_inv h2).2.2.1
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      rw [hp2, hp1]
      simp [hab]
    | succ m hm ih =>
      have h := e.step_eq m
      have hp : (e.cfg (m + 1)).pend = (e.cfg m).pend := by
        rcases htau m hm with h' | h' <;> rw [h'] at h <;> exact (Impl.step_tau h).2.1
      rw [hp]; exact ih
  · intro N
    refine ⟨(livelockExec a b k N).length, length_livelockExec a b k N, ?_⟩
    rw [hlbl (N + 1) _ (by simp [livelockExec, period]; omega)]
    simp [livelockExec, period, List.getElem_append_right]
  · intro N
    refine ⟨(livelockExec a b k N).length + (k + 1), by
      have := length_livelockExec a b k N; omega, ?_⟩
    rw [hlbl (N + 1) _ (by simp [livelockExec, period])]
    simp [livelockExec, period, List.getElem_append_right]

end Cslib.SharedMemory.StrangerFree

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

/-- **Algorithm 1 is not wait-free** for any `k ≥ 2`, already with two processes (contradicting
Theorem 3.1 of the paper): in the livelock of `exists_livelock`, process `a` is pending forever
and takes infinitely many steps. -/
theorem alg1_not_waitFree (k : ℕ) (hk : 2 ≤ k) {P : Type} [DecidableEq P] (a b : P)
    (hab : a ≠ b) : ¬ (alg1 (P := P) k).WaitFree := by
  intro hW
  obtain ⟨e, -, -, -, -, hpend, hinf, -⟩ := exists_livelock hab hk
  obtain ⟨N, hN⟩ := hW e a 2 (fun m hm => (hpend m hm).1)
  obtain ⟨m, hm, h⟩ := hinf N
  exact hN m hm h

end Cslib.SharedMemory.StrangerFree

