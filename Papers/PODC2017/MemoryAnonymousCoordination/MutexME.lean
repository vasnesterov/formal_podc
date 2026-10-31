import Papers.PODC2017.MemoryAnonymousCoordination.MutexAlg

/-!
# Figure 1: Theorem 3.2 (mutual exclusion)

The invariant `MEInv`: say that `a` *holds the lock* if it is at `retLock` or in the critical
section (`InH`), or if it is in the middle of a collect in which all values read so far were `a`
and all registers it has not read yet hold `a` (`e2`). Then the other process `b` is *safe*
(`Safe`): it does not hold the lock, at most one register is not `a` or is going to be written by
`b` without reading it first (`dset`, the pending writes `pend`: a write of line 2 or 5 decided by
an earlier read, or the remaining writes of line 12), and if all values `b` has read in its
current collect are `b`, some register it has not read yet is not `b`. Moreover (`e3`), when `b`
is in its exit section at position `j`, at most one register at positions `≥ j` (for `b`) is not
`b` or is going to be written by `a` without reading.

Only `m ≥ 2` is needed (for `m = 1` mutual exclusion fails); the threshold `⌈m/2⌉` of line 4
plays no role.
-/

set_option linter.unusedSectionVars false

namespace Podc.MemoryAnonymousCoordination.Mutex

open Cslib.SharedMemory Finset

variable {P : Type} [DecidableEq P] {m : ℕ} (π : P → Equiv.Perm (Fin m))

/-! ### Positions -/

/-- The local position (local register name) of the physical register `r` for process `x`. -/
def posn (x : P) (r : Fin m) : ℕ := ((π x).symm r).val

@[simp] lemma posn_apply (x : P) (j : ℕ) (hj : j < m) : posn π x (π x ⟨j, hj⟩) = j := by
  simp [posn]

lemma posn_lt (x : P) (r : Fin m) : posn π x r < m := ((π x).symm r).isLt

lemma eq_of_posn_eq {x : P} {r : Fin m} {j : ℕ} (hj : j < m) (h : posn π x r = j) :
    r = π x ⟨j, hj⟩ := by
  have : (π x).symm r = ⟨j, hj⟩ := Fin.ext h
  rw [← this]; simp

lemma posn_inj {x : P} {r r' : Fin m} (h : posn π x r = posn π x r') : r = r' := by
  have : (π x).symm r = (π x).symm r' := Fin.ext h
  simpa using this

/-- There is a register outside any set of at most one register (if `m ≥ 2`). -/
lemma exists_not_mem (hm : 2 ≤ m) {s : Finset (Fin m)} (hs : #s ≤ 1) : ∃ r, r ∉ s := by
  by_contra h
  push Not at h
  have : s = univ := eq_univ_iff_forall.2 h
  rw [this, card_univ, Fintype.card_fin] at hs
  omega

/-- A set containing all registers has `m` elements. -/
lemma card_eq_of_forall {s : Finset (Fin m)} (h : ∀ r, r ∈ s) : #s = m := by
  rw [eq_univ_iff_forall.2 h, card_univ, Fintype.card_fin]

/-! ### Pending writes and the danger set -/

/-- Registers that `x` (in local state `l`) is going to write without reading them first. -/
def pend (x : P) : Loc P → Finset (Fin m)
  | .scanW j | .rstW j => univ.filter (fun r => posn π x r = j)
  | .exit j => univ.filter (fun r => j ≤ posn π x r)
  | _ => ∅

lemma card_pend_single (x : P) (j : ℕ) : #(univ.filter (fun r => posn π x r = j)) ≤ 1 :=
  card_le_one.2 fun r hr r' hr' => by
    simp only [mem_filter, mem_univ, true_and] at hr hr'
    exact posn_inj π (hr.trans hr'.symm)

@[simp] lemma pend_nextScan (x : P) (j : ℕ) : pend π x (nextScan m j : Loc P) = ∅ := by
  unfold nextScan; split_ifs <;> rfl

@[simp] lemma pend_nextRst (x : P) (j : ℕ) : pend π x (nextRst m j : Loc P) = ∅ := by
  unfold nextRst; split_ifs <;> rfl

@[simp] lemma pend_afterColl (x y : P) (vs : List (Option P)) :
    pend π x (afterColl m y vs) = ∅ := by
  unfold afterColl; split_ifs <;> rfl

@[simp] lemma pend_afterWait (x : P) (j : ℕ) (z : Bool) (v : Option P) :
    pend π x (afterWait m j z v) = ∅ := by
  unfold afterWait; split_ifs <;> rfl

lemma pend_nextExit_sub (x : P) (j : ℕ) :
    pend π x (nextExit m j : Loc P) ⊆ univ.filter (fun r => j + 1 ≤ posn π x r) := by
  unfold nextExit; split_ifs <;> simp [pend]

/-- `a` holds the lock: `lock()` is about to return or `a` is in the critical section. -/
def InH : Loc P → Prop
  | .retLock => True
  | .cs => True
  | _ => False

/-- The danger set for `a` caused by `b`: registers not holding `a`, or that `b` is going to
write without reading them first. -/
def dset (a b : P) (lb : Loc P) (M : Fin m → Option P) : Finset (Fin m) :=
  univ.filter (fun r => M r ≠ some a ∨ r ∈ pend π b lb)

/-- `b` (in local state `lb`) is harmless while `a` holds the lock. -/
def Safe (a b : P) (lb : Loc P) (M : Fin m → Option P) : Prop :=
  ¬ InH lb ∧ #(dset π a b lb M) ≤ 1 ∧
    ∀ vs, lb = .coll vs → vs.count (some b) = vs.length →
      ∃ r, vs.length ≤ posn π b r ∧ M r ≠ some b

/-- The mutual-exclusion invariant. -/
structure MEInv (loc : P → Loc P) (M : Fin m → Option P) : Prop where
  bounds : ∀ x, Bounded m (loc x)
  e1 : ∀ a b, a ≠ b → InH (loc a) → Safe π a b (loc b) M
  e2 : ∀ a b, a ≠ b → ∀ vs, loc a = .coll vs → vs.count (some a) = vs.length →
    (∀ r, vs.length ≤ posn π a r → M r = some a) → Safe π a b (loc b) M
  e3 : ∀ a b, a ≠ b → ∀ j, loc b = .exit j →
    #(univ.filter (fun r => j ≤ posn π b r ∧ r ∈ dset π b a (loc a) M)) ≤ 1

/-! ### Frame lemmas -/

variable {π}

/-- A step of `x` never writes the identifier of `y ≠ x`. -/
lemma TStep.mem_some {x y : P} (hxy : x ≠ y) {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') {r : Fin m} (h : M' r = some y) : M r = some y := by
  cases hs <;> try exact h
  all_goals
    rename_i j hj
    by_cases hr : r = π x ⟨j, hj⟩
    · subst hr; simp_all
    · rwa [Function.update_of_ne hr] at h

/-- The danger set for `y` caused by `x` does not grow by a step of `x`, unless `x` leaves the
critical section. -/
lemma dset_sub {x y : P} (hxy : x ≠ y) {l l' : Loc P} {M M' : Fin m → Option P}
    (hs : TStep m π x l M l' M') (hcs : l = .cs → l' = .cs) :
    dset π y x l' M' ⊆ dset π y x l M := by
  intro r hr
  simp only [dset, mem_filter, mem_univ, true_and] at hr ⊢
  cases hs with
  | scan0 hj h0 =>
    rcases hr with h | h
    · exact Or.inl h
    · simp only [pend, mem_filter, mem_univ, true_and] at h
      left; rw [eq_of_posn_eq π hj h, h0]; simp
  | scan1 hj h0 => simp at hr; exact Or.inl hr
  | scanW hj =>
    simp only [pend_nextScan, notMem_empty, or_false] at hr
    by_cases hr0 : r = π x ⟨_, hj⟩
    · right; simp [pend, hr0]
    · left; rwa [Function.update_of_ne hr0] at hr
  | coll hj => simp at hr; exact Or.inl hr
  | rst0 hj h0 =>
    rcases hr with h | h
    · exact Or.inl h
    · simp only [pend, mem_filter, mem_univ, true_and] at h
      left; rw [eq_of_posn_eq π hj h, h0]; simpa using hxy
  | rst1 hj h0 => simp at hr; exact Or.inl hr
  | rstW hj =>
    simp only [pend_nextRst, notMem_empty, or_false] at hr
    by_cases hr0 : r = π x ⟨_, hj⟩
    · right; simp [pend, hr0]
    · left; rwa [Function.update_of_ne hr0] at hr
  | wait hj => simp at hr; exact Or.inl hr
  | exit hj =>
    by_cases hr0 : r = π x ⟨_, hj⟩
    · right; simp [pend, hr0]
    · rcases hr with h | h
      · left; rwa [Function.update_of_ne hr0] at h
      · right
        have := pend_nextExit_sub π x _ h
        simp only [mem_filter, mem_univ, true_and] at this
        simp only [pend, mem_filter, mem_univ, true_and]; omega
  | retLock => simpa [pend] using hr
  | retUnlock => simpa [pend] using hr
  | invLock => simpa [pend] using hr
  | invUnlock => exact absurd (hcs rfl) (by simp)
  | idle => exact hr

/-- Count of the values after appending one. -/
lemma count_append_one (vs : List (Option P)) (v a : Option P) :
    (vs ++ [v]).count a = vs.count a + if v = a then 1 else 0 := by
  simp [List.count_append, List.count_singleton]

/-- If all values in `vs ++ [v]` are `a`, then so are all values in `vs` and `v = a`. -/
lemma count_append_eq_length {vs : List (Option P)} {v a : Option P}
    (h : (vs ++ [v]).count a = (vs ++ [v]).length) : vs.count a = vs.length ∧ v = a := by
  rw [count_append_one] at h
  have := List.count_le_length (a := a) (l := vs)
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  split_ifs at h with hv
  · exact ⟨by omega, hv⟩
  · omega

/-- The step of `b` keeps `b` safe. -/
lemma safe_step {a b : P} (hab : a ≠ b) (hm : 2 ≤ m) {lb lb' : Loc P}
    {M M' : Fin m → Option P} (hS : Safe π a b lb M) (hs : TStep m π b lb M lb' M') :
    Safe π a b lb' M' := by
  obtain ⟨h1, h2, h3⟩ := hS
  have hsub := dset_sub hab.symm hs (fun h => by subst h; exact absurd trivial h1)
  have h2' := (card_le_card hsub).trans h2
  refine ⟨?_, h2', ?_⟩
  · cases hs with
    | @coll vs _ hj =>
      unfold afterColl
      split_ifs with h4 h5 h6 <;> simp only [InH, not_false_eq_true, not_true_eq_false]
      have hl : (vs ++ [M (π b ⟨vs.length, hj⟩)]).length = m := by simp at h4 ⊢; omega
      obtain ⟨hc, hv⟩ := count_append_eq_length (h6.trans hl.symm)
      obtain ⟨r, hr, hMr⟩ := h3 _ rfl hc
      have hr' : posn π b r = _ := le_antisymm (by have := posn_lt π b r; simp at hl; omega) hr
      rw [eq_of_posn_eq π hj hr'] at hMr
      exact hMr hv
    | retLock => exact absurd trivial h1
    | idle => exact h1
    | scan0 => simp [InH]
    | scan1 => unfold nextScan; split_ifs <;> simp [InH]
    | scanW => unfold nextScan; split_ifs <;> simp [InH]
    | rst0 => simp [InH]
    | rst1 => unfold nextRst; split_ifs <;> simp [InH]
    | rstW => unfold nextRst; split_ifs <;> simp [InH]
    | wait => unfold afterWait; split_ifs <;> simp [InH]
    | exit => unfold nextExit; split_ifs <;> simp [InH]
    | retUnlock => simp [InH]
    | invLock => simp [InH]
    | invUnlock => simp [InH]
  · intro vs hvs hc
    obtain ⟨r, hr⟩ := exists_not_mem hm h2'
    simp only [dset, mem_filter, mem_univ, true_and, not_or, not_not] at hr
    cases hs with
    | scan1 hj h0 =>
      unfold nextScan at hvs; split_ifs at hvs; cases hvs
      exact ⟨r, by simp, by rw [hr.1]; simpa using hab⟩
    | scanW hj =>
      unfold nextScan at hvs; split_ifs at hvs; cases hvs
      exact ⟨r, by simp, by rw [hr.1]; simpa using hab⟩
    | coll hj =>
      unfold afterColl at hvs; split_ifs at hvs; cases hvs
      obtain ⟨hc', hv⟩ := count_append_eq_length hc
      obtain ⟨r', hr', hMr'⟩ := h3 _ rfl hc'
      refine ⟨r', ?_, hMr'⟩
      have : posn π b r' ≠ _ := fun h => hMr' (by rw [eq_of_posn_eq π hj h]; exact hv)
      simp; omega
    | idle => exact h3 vs hvs hc
    | rst1 => unfold nextRst at hvs; split_ifs at hvs 
    | rstW => unfold nextRst at hvs; split_ifs at hvs
    | wait => unfold afterWait at hvs; split_ifs at hvs
    | exit => unfold nextExit at hvs; split_ifs at hvs
    | _ => cases hvs

/-! ### The invariant is inductive -/

/-- If every register holds `a` or is going to be written by `a` (and after the step every
register holds `a`), the other process `b` is safe. -/
lemma safe_of_full {loc : P → Loc P} {M : Fin m → Option P} (h : MEInv π loc M) (hm : 2 ≤ m)
    {a b : P} (hab : a ≠ b) (hfull : ∀ r, M r = some a ∨ r ∈ pend π a (loc a))
    {M' : Fin m → Option P} (hM' : ∀ r, M' r = some a) : Safe π a b (loc b) M' := by
  have hall : ∀ r, r ∈ dset π b a (loc a) M := fun r => by
    rcases hfull r with h | h <;> simp [dset, h, hab]
  refine ⟨fun hH => ?_, ?_, fun vs hvs _ => ?_⟩
  · have := (h.e1 b a hab.symm hH).2.1
    rw [card_eq_of_forall hall] at this; omega
  · have : dset π a b (loc b) M' = pend π b (loc b) := by ext r; simp [dset, hM']
    rw [this]
    cases hb : loc b with
    | scanW j => exact card_pend_single π b j
    | rstW j => exact card_pend_single π b j
    | exit j => simpa [hall, pend] using h.e3 a b hab j hb
    | _ => simp [pend]
  · have hb := h.bounds b
    rw [hvs] at hb
    simp only [Bounded] at hb
    exact ⟨π b ⟨vs.length, hb⟩, by simp, by rw [hM']; simpa using hab⟩

lemma MEInv.init : MEInv π (fun _ : P => (.rem : Loc P)) (fun _ => none) where
  bounds _ := trivial
  e1 _ _ _ h := absurd h (by simp [InH])
  e2 _ _ _ _ h := by simp at h
  e3 _ _ _ _ h := by simp at h

/-- The mutual-exclusion invariant is preserved by every step (two processes, `m ≥ 2`). -/
theorem MEInv.step (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (hm : 2 ≤ m)
    {loc : P → Loc P} {M M' : Fin m → Option P} {x : P} {l' : Loc P} (h : MEInv π loc M)
    (hs : TStep m π x (loc x) M l' M') : MEInv π (Function.update loc x l') M' where
  bounds y := by
    by_cases hy : y = x
    · subst hy; simpa using hs.bounded (by omega) (h.bounds y)
    · simpa [Function.update_of_ne hy] using h.bounds y
  e1 a b hab ha := by
    rcases hP a b x hab with hx | hx
    · subst x
      rw [Function.update_self] at ha
      rw [Function.update_of_ne hab.symm]
      generalize hlx : loc a = lx at hs
      cases hs with
      | @coll vs _ hj =>
        unfold afterColl at ha
        split_ifs at ha with h4 h5 h6 <;> simp only [InH] at ha
        have hl : (vs ++ [M (π a ⟨vs.length, hj⟩)]).length = m := by simp at h4 ⊢; omega
        obtain ⟨hc, hv⟩ := count_append_eq_length (h6.trans hl.symm)
        refine h.e2 a b hab vs hlx hc fun r hr => ?_
        have hr' : posn π a r = vs.length :=
          le_antisymm (by have := posn_lt π a r; simp at hl; omega) hr
        rw [eq_of_posn_eq π hj hr']; exact hv
      | retLock => exact h.e1 a b hab (by rw [hlx]; trivial)
      | idle => exact h.e1 a b hab (by rw [hlx]; exact ha)
      | scan0 => simp [InH] at ha
      | scan1 => unfold nextScan at ha; split_ifs at ha <;> simp [InH] at ha
      | scanW => unfold nextScan at ha; split_ifs at ha <;> simp [InH] at ha
      | rst0 => simp [InH] at ha
      | rst1 => unfold nextRst at ha; split_ifs at ha <;> simp [InH] at ha
      | rstW => unfold nextRst at ha; split_ifs at ha <;> simp [InH] at ha
      | wait => unfold afterWait at ha; split_ifs at ha <;> simp [InH] at ha
      | exit => unfold nextExit at ha; split_ifs at ha <;> simp [InH] at ha
      | retUnlock => simp [InH] at ha
      | invLock => simp [InH] at ha
      | invUnlock => simp [InH] at ha
    · subst x
      rw [Function.update_of_ne hab] at ha
      rw [Function.update_self]
      exact safe_step hab hm (h.e1 a b hab ha) hs
  e2 a b hab vs ha hc hall := by
    rcases hP a b x hab with hx | hx
    · subst x
      rw [Function.update_self] at ha
      rw [Function.update_of_ne hab.symm]
      generalize hlx : loc a = lx at hs
      cases hs with
      | scan1 hj h0 =>
        unfold nextScan at ha; split_ifs at ha; cases ha
        exact safe_of_full h hm hab (fun r => Or.inl (hall r (by simp))) fun r => hall r (by simp)
      | scanW hj =>
        unfold nextScan at ha; split_ifs at ha; cases ha
        refine safe_of_full h hm hab (fun r => ?_) fun r => hall r (by simp)
        by_cases hr : r = π a ⟨_, hj⟩
        · right; simp [hlx, pend, hr]
        · left; have := hall r (by simp); rwa [Function.update_of_ne hr] at this
      | @coll vs₀ _ hj =>
        unfold afterColl at ha; split_ifs at ha; cases ha
        obtain ⟨hc', hv⟩ := count_append_eq_length hc
        refine h.e2 a b hab vs₀ hlx hc' fun r hr => ?_
        by_cases hr' : posn π a r = vs₀.length
        · rw [eq_of_posn_eq π hj hr']; exact hv
        · exact hall r (by simp; omega)
      | idle => exact h.e2 a b hab vs (by rw [hlx]; exact ha) hc hall
      | scan0 => cases ha
      | rst0 => cases ha
      | rst1 => unfold nextRst at ha; split_ifs at ha
      | rstW => unfold nextRst at ha; split_ifs at ha
      | wait => unfold afterWait at ha; split_ifs at ha
      | exit => unfold nextExit at ha; split_ifs at ha
      | retLock => cases ha
      | retUnlock => cases ha
      | invLock => cases ha
      | invUnlock => cases ha
    · subst x
      rw [Function.update_of_ne hab] at ha
      rw [Function.update_self]
      have hall' : ∀ r, vs.length ≤ posn π a r → M r = some a := fun r hr =>
        hs.mem_some hab.symm (hall r hr)
      exact safe_step hab hm (h.e2 a b hab vs ha hc hall') hs
  e3 a b hab j hb := by
    rcases hP a b x hab with hx | hx
    · subst x
      rw [Function.update_of_ne hab.symm] at hb
      rw [Function.update_self]
      have key : (loc a = .cs → l' = .cs) ∨ (loc a = .cs ∧ l' = .exit 0 ∧ M' = M) := by
        by_cases hcs : loc a = .cs
        · rw [hcs] at hs
          generalize hlx : (Loc.cs : Loc P) = lx at hs
          cases hs <;> simp_all
        · exact Or.inl (fun h => absurd h hcs)
      rcases key with hk | ⟨hk1, -, rfl⟩
      · refine (card_le_card fun r hr => ?_).trans (h.e3 a b hab j hb)
        simp only [mem_filter, mem_univ, true_and] at hr ⊢
        exact ⟨hr.1, dset_sub hab hs hk hr.2⟩
      · have := (h.e1 a b hab (by rw [hk1]; trivial)).2.1
        refine (card_le_card fun r hr => ?_).trans this
        simp only [mem_filter, mem_univ, true_and] at hr
        simp [dset, hb, pend, hr.1]
    · subst x
      rw [Function.update_self] at hb
      rw [Function.update_of_ne hab]
      generalize hlx : loc b = lx at hs
      cases hs with
      | invUnlock =>
        cases hb
        refine (card_le_card fun r hr => ?_).trans (h.e1 b a hab.symm (by rw [hlx]; trivial)).2.1
        simp only [mem_filter, mem_univ, true_and] at hr
        exact hr.2
      | @exit j₀ _ hj =>
        unfold nextExit at hb; split_ifs at hb; cases hb
        refine (card_le_card fun r hr => ?_).trans (h.e3 a b hab j₀ hlx)
        simp only [mem_filter, mem_univ, true_and, dset] at hr ⊢
        have hr0 : r ≠ π b ⟨j₀, hj⟩ := fun h' => by rw [h'] at hr; simp at hr; omega
        rw [Function.update_of_ne hr0] at hr
        exact ⟨by omega, hr.2⟩
      | idle => exact h.e3 a b hab j (by rw [hlx]; exact hb)
      | scan0 => cases hb
      | scan1 => unfold nextScan at hb; split_ifs at hb
      | scanW => unfold nextScan at hb; split_ifs at hb
      | coll => unfold afterColl at hb; split_ifs at hb
      | rst0 => cases hb
      | rst1 => unfold nextRst at hb; split_ifs at hb
      | rstW => unfold nextRst at hb; split_ifs at hb
      | wait => unfold afterWait at hb; split_ifs at hb
      | retLock => cases hb
      | retUnlock => cases hb
      | invLock => cases hb

/-! ### Theorem 3.2 -/

/-- With at most two processes, every process is one of two distinct ones. -/
lemma two_procs [Fintype P] (hP : Fintype.card P ≤ 2) : ∀ a b c : P, a ≠ b → c = a ∨ c = b := by
  intro a b c hab
  by_contra h
  push Not at h
  have h3 : ({a, b, c} : Finset P).card = 3 := by
    rw [card_insert_of_notMem (by simp [hab, h.1.symm]), card_pair (Ne.symm h.2)]
  have := card_le_univ ({a, b, c} : Finset P)
  omega

variable (π) in
/-- The mutual-exclusion invariant holds in every reachable configuration. -/
theorem meInv_of_run (hP : ∀ a b c : P, a ≠ b → c = a ∨ c = b) (hm : 2 ≤ m)
    {α : List (Label P mutexObj)} {C : Cfg m P} (h : (I m π).run α = some C) :
    MEInv π C.loc C.mem :=
  Impl.invariant_of_run (Inv := fun C : Cfg m P => MEInv π C.loc C.mem) MEInv.init
    (fun C ℓ C' hC hs => by
      obtain ⟨h1, h2⟩ := step_tstep' hs
      rw [h2]; exact hC.step hP hm h1) h

/-- A process in its critical section (client region `cs`) is at the local state `cs`. -/
lemma loc_eq_cs_of_inCS (hm : 0 < m) {α : List (Label P mutexObj)} {C : Cfg m P}
    (hwf : ClientWF α) (h : (I m π).run α = some C) {x : P} (hx : InCS α x) :
    C.loc x = .cs := by
  have := (reg_inv hm hwf h x).1
  rw [InCS] at hx; rw [hx] at this
  cases hl : C.loc x <;> simp_all [regOf]

/-- **Theorem 3.2** of Taubenfeld (PODC 2017): the algorithm of Figure 1 satisfies mutual
exclusion, for two processes, every number `m ≥ 2` of registers and every adversarial numbering
`π` of the registers (memory anonymity). The paper assumes `m ≥ 3` odd; only `m ≥ 2` is needed
(for `m = 1` both processes can enter the critical section). -/
theorem theorem_3_2 [Fintype P] (hP : Fintype.card P ≤ 2) (hm : 2 ≤ m)
    (π : P → Equiv.Perm (Fin m)) : ((alg m).unnamed π).MutualExclusion := by
  rintro α ⟨C, hC⟩ hwf p q hp hq
  by_contra hpq
  have hpc := loc_eq_cs_of_inCS (by omega) hwf hC hp
  have hqc := loc_eq_cs_of_inCS (by omega) hwf hC hq
  have := ((meInv_of_run π (two_procs hP) hm hC).e1 p q hpq (by rw [hpc]; trivial)).1
  exact this (by rw [hqc]; trivial)

end Podc.MemoryAnonymousCoordination.Mutex
