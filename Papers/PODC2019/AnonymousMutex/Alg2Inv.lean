import Papers.PODC2019.AnonymousMutex.Alg2

/-!
# Algorithm 2: the main invariant and Theorem 3 (mutual exclusion)

The invariant (`Inv`) of finite client-well-formed executions:
* `LocInv`: per program counter, which registers hold the process's identifier (`own`):
  during the read loop the part of the view already read is exact for the own identifier, in the
  loop of line 7 the own registers are exactly the not yet erased own entries of the view, in the
  critical section more than `m/2` registers are owned, waiting processes own nothing, …
* `RegInv`: the client region (from the history) and the program counter agree;
* `ValInv`: every register holds `⊥` or the identifier of a process.

The key frame property: a step of `q` never changes whether a register holds the identifier of
`p ≠ q` (`compare&swap(x, ⊥, id)` only overwrites `⊥`; line 7 and line 13 only erase `q`'s own
identifier).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace AnonymousMutex.Alg2

variable {Id : Type} [DecidableEq Id] {m : ℕ}

/-! ### `nextOwn` -/

lemma findFrom_spec (q : Fin m → Bool) (i : ℕ) :
    let j := (((List.finRange m).find? (fun x => decide (i ≤ x.val) && q x)).map Fin.val).getD m
    j ≤ m ∧ (∀ x : Fin m, i ≤ x.val → x.val < j → q x = false) ∧
      (∀ h : j < m, i ≤ j ∧ q ⟨j, h⟩ = true) := by
  intro j
  cases h : (List.finRange m).find? (fun x => decide (i ≤ x.val) && q x) with
  | none =>
    have hj : j = m := by simp [j, h]
    rw [List.find?_eq_none] at h
    refine ⟨hj.le, fun x hx _ => ?_, fun h' => by omega⟩
    have := h x (List.mem_finRange x)
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at this
    simpa using this hx
  | some b =>
    have hj : j = b.val := by simp [j, h]
    rw [List.find?_eq_some_iff_getElem] at h
    obtain ⟨hb, k, hk, hkb, hbefore⟩ := h
    have hkv : b.val = k := by rw [← hkb]; simp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    refine ⟨by omega, fun x hx hxj => ?_, fun h' => ?_⟩
    · have := hbefore x.val (by omega)
      simp only [List.getElem_finRange, Fin.cast_mk, Bool.not_eq_eq_eq_not, Bool.not_true,
        Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le] at this
      rcases this with h1 | h1
      · omega
      · simpa using h1
    · refine ⟨by omega, ?_⟩
      have : (⟨j, h'⟩ : Fin m) = b := Fin.ext hj
      rw [this]; exact hb.2

lemma nextOwn_le (view : Fin m → Option Id) (me : Id) (i : ℕ) : nextOwn view me i ≤ m :=
  (findFrom_spec (fun x => decide (view x = some me)) i).1

lemma nextOwn_skip (view : Fin m → Option Id) (me : Id) (i : ℕ) (x : Fin m) (hx : i ≤ x.val)
    (hxj : x.val < nextOwn view me i) : view x ≠ some me := by
  have := (findFrom_spec (fun x => decide (view x = some me)) i).2.1 x hx hxj
  simpa using this

lemma nextOwn_found (view : Fin m → Option Id) (me : Id) (i : ℕ) (h : nextOwn view me i < m) :
    i ≤ nextOwn view me i ∧ view ⟨nextOwn view me i, h⟩ = some me := by
  have := (findFrom_spec (fun x => decide (view x = some me)) i).2.2 h
  simpa [nextOwn] using this

/-! ### The invariant -/

variable {P : Type} [DecidableEq P] (ids : P → Id) (π : P → Equiv.Perm (Fin m))

/-- Configurations of Algorithm 2. -/
abbrev Cfg (Id : Type) [DecidableEq Id] (m : ℕ) (P : Type) := SymAlg.Cfg (P := P) (alg2 Id m)

/-- The (physical) registers holding the identifier of `p`. -/
def own (C : Cfg Id m P) (p : P) : Finset (Fin m) :=
  Finset.univ.filter (fun y => C.mem () y = some (ids p))

/-- Program counters of `lock()`. -/
def LockPC : PC → Prop
  | .cas _ | .read _ | .wr _ | .wait _ _ | .retLock => True
  | _ => False

/-- Program counters of `unlock()`. -/
def UnlockPC : PC → Prop
  | .un _ | .retUnlock => True
  | _ => False

/-- The local part of the invariant for process `p`. -/
def LocInv (C : Cfg Id m P) (p : P) : Prop :=
  (C.loc p).me = ids p ∧
  match (C.loc p).pc with
  | .rem => own ids C p = ∅
  | .cas i => i < m
  | .read i => i < m ∧ ∀ x : Fin m, x.val < i →
      ((C.loc p).view x = some (ids p) ↔ C.mem () (π p x) = some (ids p))
  | .wr i => ∃ h : i < m, (C.loc p).view ⟨i, h⟩ = some (ids p) ∧
      ∀ y, C.mem () y = some (ids p) ↔
        ∃ x : Fin m, i ≤ x.val ∧ (C.loc p).view x = some (ids p) ∧ π p x = y
  | .wait i _ => i < m ∧ own ids C p = ∅
  | .retLock => m < 2 * (own ids C p).card
  | .cs => m < 2 * (own ids C p).card
  | .un i => i < m ∧ ∀ y, C.mem () y = some (ids p) → ∃ x : Fin m, i ≤ x.val ∧ π p x = y
  | .retUnlock => own ids C p = ∅

/-- Regions (from the history) and program counters agree. -/
def RegInv (α : List (Label P mutexObj)) (C : Cfg Id m P) (p : P) : Prop :=
  (regionOf α p = some .rem → (C.loc p).pc = .rem ∧ C.pend p = none) ∧
  (regionOf α p = some .trying → C.pend p = some .lock ∧ LockPC (C.loc p).pc) ∧
  (regionOf α p = some .cs → (C.loc p).pc = .cs ∧ C.pend p = none) ∧
  (regionOf α p = some .exiting → C.pend p = some .unlock ∧ UnlockPC (C.loc p).pc)

/-- Every register holds `⊥` or a process identifier. -/
def ValInv (C : Cfg Id m P) : Prop := ∀ y, C.mem () y = none ∨ ∃ q, C.mem () y = some (ids q)

/-- The invariant. -/
def Inv (α : List (Label P mutexObj)) (C : Cfg Id m P) : Prop :=
  (∀ p, LocInv ids π C p) ∧ (∀ p, RegInv α C p) ∧ ValInv ids C

/-! ### Actions -/

section Act

variable {s : St Id m} {i : ℕ}

lemma act_cas (hpc : s.pc = .cas i) (h : i < m) : (alg2 Id m).act s =
    .rmw ⟨i, h⟩ (fun v => if v = none then some s.me else v)
      (fun _ => if i + 1 < m then { s with pc := .cas (i + 1) } else { s with pc := .read 0 }) := by
  simp [alg2, hpc, h]

lemma act_read (hpc : s.pc = .read i) (h : i < m) : (alg2 Id m).act s =
    .rmw ⟨i, h⟩ (fun v => v) (fun v =>
      if i + 1 < m then { s with view := Function.update s.view ⟨i, h⟩ v, pc := .read (i + 1) }
      else afterRead s (Function.update s.view ⟨i, h⟩ v)) := by
  simp [alg2, hpc, h]

lemma act_wr (hpc : s.pc = .wr i) (h : i < m) : (alg2 Id m).act s =
    .rmw ⟨i, h⟩ (fun _ => none) (fun _ => wrFrom s (i + 1)) := by
  simp [alg2, hpc, h]

lemma act_wait {ab : Bool} (hpc : s.pc = .wait i ab) (h : i < m) : (alg2 Id m).act s =
    .rmw ⟨i, h⟩ (fun v => v) (fun v =>
      if i + 1 < m then { s with pc := .wait (i + 1) (ab && v == none) }
      else if ab && v == none then { s with pc := .cas 0 } else { s with pc := .wait 0 true }) := by
  simp [alg2, hpc, h]

lemma act_un (hpc : s.pc = .un i) (h : i < m) : (alg2 Id m).act s =
    .rmw ⟨i, h⟩ (fun v => if v = some s.me then none else v)
      (fun _ => if i + 1 < m then { s with pc := .un (i + 1) } else { s with pc := .retUnlock }) := by
  simp [alg2, hpc, h]

lemma act_retLock (hpc : s.pc = .retLock) :
    (alg2 Id m).act s = .ret () { s with pc := .cs } := by
  simp [alg2, hpc]

lemma act_retUnlock (hpc : s.pc = .retUnlock) :
    (alg2 Id m).act s = .ret () { s with pc := .rem } := by
  simp [alg2, hpc]

lemma act_rem (hpc : s.pc = .rem) : (alg2 Id m).act s = .ret () s := by
  simp [alg2, hpc]

lemma act_cs (hpc : s.pc = .cs) : (alg2 Id m).act s = .ret () s := by
  simp [alg2, hpc]

end Act

/-! ### Frame -/

lemma own_congr {C C' : Cfg Id m P} {p : P}
    (h : ∀ y, C'.mem () y = some (ids p) ↔ C.mem () y = some (ids p)) :
    own ids C' p = own ids C p := by
  ext y; simp [own, h y]

lemma locInv_congr {C C' : Cfg Id m P} {p : P} (hloc : C'.loc p = C.loc p)
    (h : ∀ y, C'.mem () y = some (ids p) ↔ C.mem () y = some (ids p)) :
    LocInv ids π C' p ↔ LocInv ids π C p := by
  have hown := own_congr ids h
  unfold LocInv
  rw [hloc, hown]
  cases (C.loc p).pc <;> simp only [h]

lemma act_ne_snap (s : St Id m) (k : (Fin m → Option Id) → St Id m) :
    (alg2 Id m).act s ≠ .snap k := by
  simp only [alg2]
  split <;> (try split) <;> simp

/-- Number of view entries equal to `me` = number of physical registers holding `me`, if the
view is exact for `me`. -/
lemma owned_eq_card_own {C : Cfg Id m P} {p : P} {w : Fin m → Option Id}
    (hw : ∀ x, w x = some (ids p) ↔ C.mem () (π p x) = some (ids p)) :
    owned w (ids p) = (own ids C p).card := by
  unfold owned own
  refine Finset.card_bij (fun x _ => π p x) ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢; exact (hw x).1 hx
  · intro x _ y _ h; exact (π p).injective h
  · intro y hy
    refine ⟨(π p).symm y, ?_, by simp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [hw]; simpa using hy

variable (hid : Function.Injective ids) (hm : 0 < m)
include hid hm

omit hid hm in
lemma lockPC_wrFrom (s : St Id m) (i : ℕ) : LockPC (wrFrom s i).pc := by
  unfold wrFrom; split_ifs <;> trivial

omit hid hm in
lemma lockPC_afterRead (s : St Id m) (w : Fin m → Option Id) : LockPC (afterRead s w).pc := by
  unfold afterRead; split_ifs
  · exact lockPC_wrFrom _ _
  all_goals trivial

omit hid in
/-- Local invariant after `wrFrom` (line 7 loop continues at `i`), given that the own registers
are exactly the own entries of the view with local index `≥ i`. -/
lemma locInv_wrFrom {C' : Cfg Id m P} {q : P} (s : St Id m) (hme : s.me = ids q) (i : ℕ)
    (hown : ∀ y, C'.mem () y = some (ids q) ↔
      ∃ x : Fin m, i ≤ x.val ∧ s.view x = some (ids q) ∧ π q x = y)
    (hloc : C'.loc q = wrFrom s i) : LocInv ids π C' q := by
  unfold LocInv
  rw [hloc]
  unfold wrFrom
  split_ifs with h3
  · refine ⟨hme, h3, ?_, fun y => ?_⟩
    · rw [← hme]; exact (nextOwn_found s.view s.me i h3).2
    · rw [hown y]
      constructor
      · rintro ⟨x, hx, hvx, rfl⟩
        refine ⟨x, ?_, hvx, rfl⟩
        by_contra hlt
        exact nextOwn_skip s.view s.me i x hx (by omega) (by rw [hme]; exact hvx)
      · rintro ⟨x, hx, hvx, rfl⟩
        exact ⟨x, le_trans (nextOwn_found s.view s.me i h3).1 hx, hvx, rfl⟩
  · refine ⟨hme, hm, ?_⟩
    ext y
    simp only [own, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro hy
    obtain ⟨x, hx, hvx, -⟩ := (hown y).1 hy
    have : nextOwn s.view s.me i = m := le_antisymm (nextOwn_le _ _ _) (by omega)
    exact nextOwn_skip s.view s.me i x hx (by rw [this]; exact x.isLt) (by rw [hme]; exact hvx)

omit hid in
/-- Local invariant after the read loop of line 3 has completed with an exact view `w`. -/
lemma locInv_afterRead {C' : Cfg Id m P} {q : P} (s : St Id m) (hme : s.me = ids q)
    (w : Fin m → Option Id) (hw : ∀ x, w x = some (ids q) ↔ C'.mem () (π q x) = some (ids q))
    (hloc : C'.loc q = afterRead s w) : LocInv ids π C' q := by
  unfold afterRead at hloc
  split_ifs at hloc with h1 h2
  · refine locInv_wrFrom ids π hm { s with view := w } hme 0 (fun y => ?_) hloc
    constructor
    · intro hy
      refine ⟨(π q).symm y, Nat.zero_le _, ?_, by simp⟩
      rw [hw]; simpa using hy
    · rintro ⟨x, -, hx, rfl⟩
      exact (hw x).1 hx
  · unfold LocInv; rw [hloc]
    refine ⟨hme, ?_⟩
    rw [hme, owned_eq_card_own ids π hw] at h2
    exact h2
  · unfold LocInv; rw [hloc]
    exact ⟨hme, hm⟩

/-- The new local state of `q` after an internal step satisfies the local invariant, and the
step does not change the registers of other processes. -/
lemma tau_facts {C : Cfg Id m P} {q : P} (hq : LocInv ids π C q) {x : Fin m} {f : Option Id → Option Id}
    {k : Option Id → St Id m} (hact : (alg2 Id m).act (C.loc q) = .rmw x f k) :
    let C' : Cfg Id m P := { C with
      mem := Function.update C.mem () (Function.update (C.mem ()) (π q x) (f (C.mem () (π q x))))
      loc := Function.update C.loc q (k (C.mem () (π q x))) }
    (∀ p, p ≠ q → (f (C.mem () (π q x)) = some (ids p) ↔ C.mem () (π q x) = some (ids p))) ∧
    (f (C.mem () (π q x)) = none ∨ f (C.mem () (π q x)) = some (ids q) ∨
      f (C.mem () (π q x)) = C.mem () (π q x)) ∧
    (LockPC (C.loc q).pc → LockPC (k (C.mem () (π q x))).pc) ∧
    (UnlockPC (C.loc q).pc → UnlockPC (k (C.mem () (π q x))).pc) ∧
    LocInv ids π C' q := by
  intro C'
  obtain ⟨hme, hpc⟩ := hq
  have hloc' : C'.loc q = k (C.mem () (π q x)) := by simp [C']
  have hmem' : C'.mem () = Function.update (C.mem ()) (π q x) (f (C.mem () (π q x))) := by simp [C']
  have hown' : ∀ y, C'.mem () y = some (ids q) ↔
      (if y = π q x then f (C.mem () (π q x)) else C.mem () y) = some (ids q) := by
    intro y; rw [hmem', Function.update_apply]
  have hne : ∀ p, p ≠ q → ids p ≠ ids q := fun p hp h => hp (hid h)
  set v := C.mem () (π q x) with hv
  cases hpc0 : (C.loc q).pc with
  | rem => rw [act_rem hpc0] at hact; cases hact
  | cs => rw [act_cs hpc0] at hact; cases hact
  | retLock => rw [act_retLock hpc0] at hact; cases hact
  | retUnlock => rw [act_retUnlock hpc0] at hact; cases hact
  | cas i =>
    rw [hpc0] at hpc
    rw [act_cas hpc0 hpc] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    refine ⟨fun p hp => ?_, ?_, fun _ => ?_, fun h => ?_, ?_⟩
    · dsimp only; split_ifs with h0
      · simp [h0, hme, Ne.symm (hne p hp)]
      · rfl
    · dsimp only; split_ifs with h0
      · simp [hme]
      · simp
    · split_ifs <;> trivial
    · simp [UnlockPC, hpc0] at h
    · unfold LocInv
      rw [hloc']
      split_ifs with h1
      · exact ⟨hme, h1⟩
      · exact ⟨hme, hm, fun x hx => absurd hx (Nat.not_lt_zero _)⟩
  | read i =>
    rw [hpc0] at hpc
    obtain ⟨hi, hview⟩ := hpc
    rw [act_read hpc0 hi] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    have hmemeq : C'.mem () = C.mem () := by rw [hmem']; simp [v]
    refine ⟨fun p hp => Iff.rfl, Or.inr (Or.inr rfl), fun _ => ?_, fun h => ?_, ?_⟩
    · dsimp only; split_ifs
      · trivial
      · exact lockPC_afterRead _ _
    · simp [UnlockPC, hpc0] at h
    · have hw : ∀ x' : Fin m, x'.val < i + 1 →
          ((Function.update (C.loc q).view ⟨i, hi⟩ v) x' = some (ids q) ↔
          C'.mem () (π q x') = some (ids q)) := by
        intro x' hx'
        rw [hmemeq]
        by_cases hx : x' = ⟨i, hi⟩
        · subst hx; simp [v]
        · rw [Function.update_of_ne hx]
          exact hview x' (by
            have : x'.val ≠ i := fun h => hx (Fin.ext h)
            omega)
      dsimp only at hloc'
      split_ifs at hloc' with h1
      · unfold LocInv; rw [hloc']
        exact ⟨hme, h1, hw⟩
      · exact locInv_afterRead ids π hm (C.loc q) hme _ (fun x' => hw x' (by omega)) hloc' 
  | wr i =>
    rw [hpc0] at hpc
    obtain ⟨hi, hvi, hownI⟩ := hpc
    rw [act_wr hpc0 hi] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    have hv0 : v = some (ids q) := (hownI _).2 ⟨⟨i, hi⟩, le_rfl, hvi, rfl⟩
    refine ⟨fun p hp => ?_, Or.inl rfl, fun _ => lockPC_wrFrom _ _, fun h => ?_, ?_⟩
    · simp only [hv0, reduceCtorEq, false_iff, Option.some.injEq]
      exact hne p hp ∘ Eq.symm
    · simp [UnlockPC, hpc0] at h
    · refine locInv_wrFrom ids π hm (C.loc q) hme (i + 1) (fun y => ?_) hloc'
      rw [hown' y]
      by_cases hy : y = π q ⟨i, hi⟩
      · simp only [hy, ite_true, reduceCtorEq, false_iff]
        rintro ⟨x', hx', -, hxy⟩
        have := (π q).injective hxy
        rw [this] at hx'
        simp at hx'
      · simp only [hy, ite_false]
        rw [hownI y]
        constructor
        · rintro ⟨x', hx', hvx, rfl⟩
          refine ⟨x', ?_, hvx, rfl⟩
          have : x' ≠ ⟨i, hi⟩ := fun h => hy (by rw [h])
          have : x'.val ≠ i := fun h => this (Fin.ext h)
          omega
        · rintro ⟨x', hx', hvx, rfl⟩
          exact ⟨x', by omega, hvx, rfl⟩
  | wait i ab =>
    rw [hpc0] at hpc
    obtain ⟨hi, hempty⟩ := hpc
    rw [act_wait hpc0 hi] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    have hmemeq : C'.mem () = C.mem () := by rw [hmem']; simp [v]
    have hown0 : own ids C' q = ∅ := by
      rw [own_congr ids (C := C) (C' := C') (p := q) (fun y => by rw [hmemeq])]; exact hempty
    refine ⟨fun p hp => Iff.rfl, Or.inr (Or.inr rfl), fun _ => ?_, fun h => ?_, ?_⟩
    · dsimp only; split_ifs <;> trivial
    · simp [UnlockPC, hpc0] at h
    · unfold LocInv; rw [hloc']
      dsimp only
      split_ifs with h1 h2
      · exact ⟨hme, h1, hown0⟩
      · exact ⟨hme, hm⟩
      · exact ⟨hme, hm, hown0⟩
  | un i =>
    rw [hpc0] at hpc
    obtain ⟨hi, hownU⟩ := hpc
    rw [act_un hpc0 hi] at hact
    simp only [SymAction.rmw.injEq] at hact
    obtain ⟨rfl, rfl, rfl⟩ := hact
    refine ⟨fun p hp => ?_, ?_, fun h => ?_, fun _ => ?_, ?_⟩
    · dsimp only; split_ifs with h0
      · simp only [h0, hme, reduceCtorEq, false_iff, Option.some.injEq]
        exact hne p hp ∘ Eq.symm
      · rfl
    · dsimp only; split_ifs <;> simp
    · simp [LockPC, hpc0] at h
    · dsimp only; split_ifs <;> trivial
    · have hown'' : ∀ y, C'.mem () y = some (ids q) →
          C.mem () y = some (ids q) ∧ y ≠ π q ⟨i, hi⟩ := by
        intro y hy
        rw [hown' y] at hy
        by_cases hy0 : y = π q ⟨i, hi⟩
        · simp only [hy0, ite_true] at hy
          split_ifs at hy with h0
          rw [hme] at h0; exact absurd hy h0
        · simp only [hy0, ite_false] at hy
          exact ⟨hy, hy0⟩
      have hgt : ∀ y, C'.mem () y = some (ids q) → ∃ x' : Fin m, i + 1 ≤ x'.val ∧ π q x' = y := by
        intro y hy
        obtain ⟨hy1, hy2⟩ := hown'' y hy
        obtain ⟨x', hx', rfl⟩ := hownU y hy1
        refine ⟨x', ?_, rfl⟩
        have : x' ≠ ⟨i, hi⟩ := fun h => hy2 (by rw [h])
        have : x'.val ≠ i := fun h => this (Fin.ext h)
        omega
      unfold LocInv; rw [hloc']
      dsimp only
      split_ifs with h1
      · exact ⟨hme, h1, hgt⟩
      · refine ⟨hme, ?_⟩
        ext y
        simp only [own, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        intro hy
        obtain ⟨x', hx', -⟩ := hgt y hy
        omega

omit hid hm in
lemma clientWF_of_append {α : List (Label P mutexObj)} {ℓ : Label P mutexObj}
    (h : ClientWF (α ++ [ℓ])) : ClientWF α := by
  intro p hp
  apply h p
  rw [regionOf_append_singleton, hp]
  split_ifs <;> rfl

omit hid hm in
lemma regionOf_tau (α : List (Label P mutexObj)) (q p : P) :
    regionOf (α ++ [.tau q]) p = regionOf α p := by
  rw [regionOf_append_singleton]
  split_ifs
  · cases regionOf α p with
    | none => rfl
    | some r => cases r <;> rfl
  · rfl

lemma inv_tau {α : List (Label P mutexObj)} {C C' : Cfg Id m P} {q : P}
    (hI : Inv ids π α C) (h : ((alg2 Id m).impl ids π).step C (.tau q) = some C') :
    Inv ids π (α ++ [.tau q]) C' := by
  obtain ⟨hL, hR, hV⟩ := hI
  obtain ⟨hpend, hcase⟩ := SymAlg.impl_step_tau_cases h
  rcases hcase with ⟨x, f, k, hact, rfl⟩ | ⟨k, hact, -⟩
  swap
  · exact absurd hact (act_ne_snap _ _)
  obtain ⟨hframe, hval, hlock, hunlock, hq⟩ := tau_facts ids π hid hm (hL q) hact
  have hmemp : ∀ p, p ≠ q → ∀ y,
      (Function.update (C.mem ()) (π q x) (f (C.mem () (π q x)))) y = some (ids p) ↔
        C.mem () y = some (ids p) := by
    intro p hp y
    rw [Function.update_apply]
    split_ifs with hy
    · subst hy; exact hframe p hp
    · rfl
  refine ⟨fun p => ?_, fun p => ?_, fun y => ?_⟩
  · by_cases hpq : p = q
    · subst hpq; exact hq
    · refine (locInv_congr ids π (by simp [Function.update_of_ne hpq]) (fun y => ?_)).2 (hL p)
      simpa using hmemp p hpq y
  · rw [RegInv, regionOf_tau]
    obtain ⟨h1, h2, h3, h4⟩ := hR p
    by_cases hpq : p = q
    · subst hpq
      simp only [Function.update_self]
      refine ⟨fun hr => ?_, fun hr => ?_, fun hr => ?_, fun hr => ?_⟩
      · obtain ⟨hpc, -⟩ := h1 hr; rw [act_rem hpc] at hact; cases hact
      · exact ⟨(h2 hr).1, hlock (h2 hr).2⟩
      · obtain ⟨hpc, -⟩ := h3 hr; rw [act_cs hpc] at hact; cases hact
      · exact ⟨(h4 hr).1, hunlock (h4 hr).2⟩
    · simp only [Function.update_of_ne hpq]
      exact ⟨h1, h2, h3, h4⟩
  · simp only [Function.update_self]
    rw [Function.update_apply]
    split_ifs with hy
    · rcases hval with h0 | h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨q, h0⟩
      · rw [h0, ← hy]; exact hV _
    · exact hV y

lemma inv_inv {α : List (Label P mutexObj)} {C C' : Cfg Id m P} {q : P} {o : MutexOp}
    (hI : Inv ids π α C) (h : ((alg2 Id m).impl ids π).step C (.inv q o) = some C')
    (hwf : ClientWF (α ++ [.inv q o])) :
    Inv ids π (α ++ [.inv q o]) C' := by
  obtain ⟨hL, hR, hV⟩ := hI
  obtain ⟨hpend, rfl⟩ := SymAlg.impl_step_inv_cases h
  have hwq := hwf q
  rw [regionOf_append_singleton] at hwq
  simp only [Label.proc, ↓reduceIte] at hwq
  have hreg : ∀ p, p ≠ q → regionOf (α ++ [.inv q o]) p = regionOf α p := fun p hp =>
    regionOf_append_singleton_of_ne _ _ (Ne.symm hp)
  -- the region of `q` before the invocation
  cases hr : regionOf α q with
  | none => rw [hr] at hwq; exact absurd rfl hwq
  | some r =>
    rw [hr] at hwq
    obtain ⟨h1, h2, h3, h4⟩ := hR q
    have hnew : ∃ r', regionOf (α ++ [.inv q o]) q = some r' ∧
        ((r = .rem ∧ o = .lock ∧ r' = .trying) ∨ (r = .cs ∧ o = .unlock ∧ r' = .exiting)) := by
      rw [regionOf_append_singleton]
      simp only [Label.proc, ↓reduceIte, hr]
      cases r <;> cases o <;> simp_all [Region.next]
    obtain ⟨r', hr', hcase⟩ := hnew
    rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨hpc, -⟩ := h1 hr
      have hinvk : (alg2 Id m).invoke (C.loc q) .lock = { C.loc q with pc := .cas 0 } := by
        simp [alg2, hpc]
      refine ⟨fun p => ?_, fun p => ?_, hV⟩
      · by_cases hpq : p = q
        · subst hpq
          unfold LocInv
          simp only [Function.update_self, hinvk]
          exact ⟨(hL p).1, hm⟩
        · have hc := locInv_congr ids π (C := C) (p := p)
            (C' := { C with loc := Function.update C.loc q ((alg2 Id m).invoke (C.loc q) .lock),
                            pend := Function.update C.pend q (some .lock) })
            (by simp [Function.update_of_ne hpq]) (fun y => Iff.rfl)
          exact hc.2 (hL p)
      · by_cases hpq : p = q
        · subst hpq
          simp only [RegInv, hr', Function.update_self, hinvk]
          refine ⟨by simp, fun _ => by simp [LockPC], by simp, by simp⟩
        · simp only [RegInv, hreg p hpq, Function.update_of_ne hpq]
          exact hR p
    · obtain ⟨hpc, -⟩ := h3 hr
      have hinvk : (alg2 Id m).invoke (C.loc q) .unlock = { C.loc q with pc := .un 0 } := by
        simp [alg2, hpc]
      refine ⟨fun p => ?_, fun p => ?_, hV⟩
      · by_cases hpq : p = q
        · subst hpq
          unfold LocInv
          simp only [Function.update_self, hinvk]
          exact ⟨(hL p).1, hm, fun y _ => ⟨(π p).symm y, Nat.zero_le _, by simp⟩⟩
        · have hc := locInv_congr ids π (C := C) (p := p)
            (C' := { C with loc := Function.update C.loc q ((alg2 Id m).invoke (C.loc q) .unlock),
                            pend := Function.update C.pend q (some .unlock) })
            (by simp [Function.update_of_ne hpq]) (fun y => Iff.rfl)
          exact hc.2 (hL p)
      · by_cases hpq : p = q
        · subst hpq
          simp only [RegInv, hr', Function.update_self, hinvk]
          refine ⟨by simp, by simp, by simp, fun _ => by simp [UnlockPC]⟩
        · simp only [RegInv, hreg p hpq, Function.update_of_ne hpq]
          exact hR p

omit hid hm in
lemma act_ret_cases {C : Cfg Id m P} {q : P} (hq : LocInv ids π C q) {s : St Id m}
    (hact : (alg2 Id m).act (C.loc q) = .ret () s) :
    ((C.loc q).pc = .retLock ∧ s = { C.loc q with pc := .cs }) ∨
    ((C.loc q).pc = .retUnlock ∧ s = { C.loc q with pc := .rem }) ∨
    (C.loc q).pc = .rem ∨ (C.loc q).pc = .cs := by
  obtain ⟨-, hpc⟩ := hq
  cases hpc0 : (C.loc q).pc with
  | rem => exact Or.inr (Or.inr (Or.inl rfl))
  | cs => exact Or.inr (Or.inr (Or.inr rfl))
  | retLock =>
    rw [act_retLock hpc0] at hact; cases hact; exact Or.inl ⟨rfl, rfl⟩
  | retUnlock =>
    rw [act_retUnlock hpc0] at hact; cases hact; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | cas i => rw [hpc0] at hpc; rw [act_cas hpc0 hpc] at hact; cases hact
  | read i => rw [hpc0] at hpc; rw [act_read hpc0 hpc.1] at hact; cases hact
  | wr i => rw [hpc0] at hpc; obtain ⟨hi, -⟩ := hpc; rw [act_wr hpc0 hi] at hact; cases hact
  | wait i ab => rw [hpc0] at hpc; rw [act_wait hpc0 hpc.1] at hact; cases hact
  | un i => rw [hpc0] at hpc; rw [act_un hpc0 hpc.1] at hact; cases hact

lemma inv_ret {α : List (Label P mutexObj)} {C C' : Cfg Id m P} {q : P} {r : Unit}
    (hI : Inv ids π α C) (h : ((alg2 Id m).impl ids π).step C (.ret q r) = some C')
    (hwf : ClientWF (α ++ [.ret q r])) :
    Inv ids π (α ++ [.ret q r]) C' := by
  obtain ⟨hL, hR, hV⟩ := hI
  obtain ⟨hpend, s, hact, rfl⟩ := SymAlg.impl_step_ret_cases h
  have hreg : ∀ p, p ≠ q → regionOf (α ++ [.ret q r]) p = regionOf α p := fun p hp =>
    regionOf_append_singleton_of_ne _ _ (Ne.symm hp)
  have hwq := hwf q
  rw [regionOf_append_singleton] at hwq
  simp only [Label.proc, ↓reduceIte] at hwq
  obtain ⟨h1, h2, h3, h4⟩ := hR q
  have hothers : ∀ p, p ≠ q → LocInv ids π
      { C with pend := Function.update C.pend q none, loc := Function.update C.loc q s } p :=
    fun p hpq => (locInv_congr ids π (C := C) (p := p)
      (C' := { C with pend := Function.update C.pend q none, loc := Function.update C.loc q s })
      (by simp [Function.update_of_ne hpq]) (fun y => Iff.rfl)).2 (hL p)
  have hothersR : ∀ p, p ≠ q → RegInv (α ++ [.ret q r])
      { C with pend := Function.update C.pend q none, loc := Function.update C.loc q s } p := by
    intro p hpq
    simp only [RegInv, hreg p hpq, Function.update_of_ne hpq]
    exact hR p
  cases hr : regionOf α q with
  | none => rw [hr] at hwq; exact absurd rfl hwq
  | some reg =>
    cases reg with
    | rem => exact absurd (h1 hr).2 hpend
    | cs => exact absurd (h3 hr).2 hpend
    | trying =>
      have hnew : regionOf (α ++ [.ret q r]) q = some .cs := by
        rw [regionOf_append_singleton]; simp [hr, Region.next, Label.proc]
      obtain ⟨-, hlpc⟩ := h2 hr
      rcases act_ret_cases ids π (hL q) hact with ⟨hpc, rfl⟩ | ⟨hpc, -⟩ | hpc | hpc
      · have hL' := hL q
        unfold LocInv at hL'
        rw [hpc] at hL'
        refine ⟨fun p => ?_, fun p => ?_, hV⟩
        · by_cases hpq : p = q
          · subst hpq; unfold LocInv
            simp only [Function.update_self]
            exact ⟨hL'.1, hL'.2⟩
          · exact hothers p hpq
        · by_cases hpq : p = q
          · subst hpq; simp [RegInv, hnew]
          · exact hothersR p hpq
      · rw [hpc] at hlpc; exact absurd hlpc id
      · rw [hpc] at hlpc; exact absurd hlpc id
      · rw [hpc] at hlpc; exact absurd hlpc id
    | exiting =>
      have hnew : regionOf (α ++ [.ret q r]) q = some .rem := by
        rw [regionOf_append_singleton]; simp [hr, Region.next, Label.proc]
      obtain ⟨-, hupc⟩ := h4 hr
      rcases act_ret_cases ids π (hL q) hact with ⟨hpc, -⟩ | ⟨hpc, rfl⟩ | hpc | hpc
      · rw [hpc] at hupc; exact absurd hupc id
      · have hL' := hL q
        unfold LocInv at hL'
        rw [hpc] at hL'
        refine ⟨fun p => ?_, fun p => ?_, hV⟩
        · by_cases hpq : p = q
          · subst hpq; unfold LocInv
            simp only [Function.update_self]
            exact ⟨hL'.1, hL'.2⟩
          · exact hothers p hpq
        · by_cases hpq : p = q
          · subst hpq; simp [RegInv, hnew]
          · exact hothersR p hpq
      · rw [hpc] at hupc; exact absurd hupc id
      · rw [hpc] at hupc; exact absurd hupc id

lemma inv_init : Inv ids π [] ((alg2 Id m).impl ids π).initCfg := by
  refine ⟨fun p => ⟨rfl, ?_⟩, fun p => ?_, fun y => Or.inl rfl⟩
  · show own ids _ p = ∅
    ext y; simp [own, Impl.initCfg, SymAlg.impl, alg2]
  · simp only [RegInv, regionOf_nil, Option.some.injEq, reduceCtorEq, false_imp_iff, and_true]
    intro _; exact ⟨rfl, rfl⟩

/-- The invariant holds in every finite client-well-formed execution. -/
theorem inv_of_run {α : List (Label P mutexObj)} {C : Cfg Id m P} (hwf : ClientWF α)
    (h : ((alg2 Id m).impl ids π).run α = some C) : Inv ids π α C := by
  induction α using List.reverseRecOn generalizing C with
  | nil => cases h; exact inv_init ids π hid hm
  | append_singleton β ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hb : ((alg2 Id m).impl ids π).runFrom ((alg2 Id m).impl ids π).initCfg β with
    | none => rw [hb] at h; cases h
    | some B =>
      rw [hb] at h
      simp only [Option.bind_some, Impl.runFrom_singleton] at h
      have hB := ih (clientWF_of_append hwf) hb
      cases ℓ with
      | inv q o => exact inv_inv ids π hid hm hB h hwf
      | ret q r => exact inv_ret ids π hid hm hB h hwf
      | tau q => exact inv_tau ids π hid hm hB h

end AnonymousMutex.Alg2
