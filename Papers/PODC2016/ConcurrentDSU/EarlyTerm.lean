import Papers.PODC2016.ConcurrentDSU.WaitFree

/-!
# Section 6: `SameSet` and `Unite` with early termination (Algorithms 6 and 7)

The two finds of an operation are interleaved: the smaller of the current nodes `u < v` is
advanced (with splitting), and the operation stops as soon as `u = v` (same set) or the smaller
node `u` is a root (`SameSet`: different sets; `Unite`: link `u` below `v` by `Cas`).

```
loop
  if u = v then return true                      -- linearization point (both algorithms)
  if v < u then swap(u, v)
  SameSet: if u = u.parent then return false      -- linearization point
  Unite:   if Cas(u.parent, u, v) then return     -- linearization point
  repeat k + 1 times: z ← u.parent; w ← z.parent; Cas(u.parent, z, w)
  u ← z
```

Algorithms 6/7 are `k = 1` (two tries, "do twice"); `k = 0` is the one-try variant mentioned in
the paper. The test `u = v` is local; it is folded into the step that produced the new value of
`u` (or into the invocation).

Results: `et_linearizable` and `et_waitFree` (the paper does not state them as theorems; it
presents the algorithms as correct implementations of `SameSet` and `Unite`). Here all
linearization points are "current" steps, no retroactive insertion is needed.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentDSU

open Cslib.SharedMemory

variable {E : Type} [DecidableEq E]

/-- Local states of Algorithms 6/7 (`b = true` for `Unite`).
* `rt u v` — `SameSet`: test `u = u.parent` (here `u < v`);
* `lk u v` — `Unite`: `Cas(u.parent, u, v)` (here `u < v`);
* `zr b u v i`, `wr b u v z i`, `cs b u v z w i` — try `i` of the splitting step
  `z ← u.parent; w ← z.parent; Cas(u.parent, z, w)`. -/
inductive ELoc (E : Type) where
  | idle
  | rt (u v : E)
  | lk (u v : E)
  | zr (b : Bool) (u v : E) (i : ℕ)
  | wr (b : Bool) (u v z : E) (i : ℕ)
  | cs (b : Bool) (u v z w : E) (i : ℕ)
  | done (r : Bool)

variable (key : E → ℕ)

/-- Top of the loop: return if `u = v`, otherwise order `u < v` and go to line 6. -/
def enter (b : Bool) (u v : E) : ELoc E :=
  if u = v then .done true
  else if key v < key u then (if b then .lk v u else .rt v u)
  else (if b then .lk u v else .rt u v)

/-- The program of Algorithms 6/7 with `k + 1` tries per splitting step. -/
def eact (k : ℕ) : ELoc E → Action (dsu E) (Ptr E) (ELoc E)
  | .idle => .ret true .idle
  | .rt u v => .access u .read (fun r => if val u r = u then .done false else .zr false u v 0)
  | .lk u v => .access u (.cas u v)
      (fun r => if r = .inr true then .done true else .zr true u v 0)
  | .zr b u v i => .access u .read (fun r => .wr b u v (val u r) i)
  | .wr b u v z i => .access z .read (fun r => .cs b u v z (val z r) i)
  | .cs b u v z w i => .access u (.cas z w)
      (fun _ => if i + 1 < k + 1 then .zr b u v (i + 1) else enter key b z v)
  | .done r => .ret r .idle

/-- Invocation. -/
def einvoke : DSUOp E → ELoc E
  | .sameSet x y => enter key false x y
  | .unite x y => enter key true x y

/-- Algorithms 6 and 7 (early termination, `k + 1`-try splitting) as an implementation. -/
def etImpl (k : ℕ) (P : Type) : Impl (dsu E) (Ptr E) P (ELoc E) where
  memInit a := a
  locInit _ := .idle
  invoke _ _ o := einvoke key o
  act _ l := eact key k l

variable [Fintype E] {P : Type} [DecidableEq P]

/-! ### Invariants -/

/-- `{u, v}` are in the trees of `{x, y}`. -/
def Track (m : E → E) (x y u v : E) : Prop :=
  (same m u x ∧ same m v y) ∨ (same m u y ∧ same m v x)

variable (k : ℕ)

/-- Invariant of a process. -/
def ELocInv (m : E → E) : Option (DSUOp E) → ELoc E → Prop
  | none, l => l = .idle
  | some _, .idle => False
  | some o, .rt u v => o.isUnite = false ∧ Track m o.x o.y u v ∧ key u < key v
  | some o, .lk u v => o.isUnite = true ∧ Track m o.x o.y u v ∧ key u < key v
  | some o, .zr b u v i => b = o.isUnite ∧ Track m o.x o.y u v ∧ key u < key v ∧ m u ≠ u ∧
      i < k + 1
  | some o, .wr b u v z i => b = o.isUnite ∧ Track m o.x o.y u v ∧ key u < key v ∧ m u ≠ u ∧
      i < k + 1 ∧ same m z u ∧ key u < key z
  | some o, .cs b u v z w i => b = o.isUnite ∧ Track m o.x o.y u v ∧ key u < key v ∧ m u ≠ u ∧
      i < k + 1 ∧ same m z u ∧ key u < key z ∧ same m w z ∧ (w = z ∨ key z < key w)
  | some _, .done _ => True

/-- Invariant of a configuration. -/
structure ELInv (C : Config (dsu E) (Ptr E) P (ELoc E)) : Prop where
  good : Good key C.mem
  loc : ∀ p, ELocInv key k C.mem (C.pend p) (C.loc p)

variable {key k}

lemma Track.legal {m m' : E → E} (h : Legal key m m') {x y u v : E} (ht : Track m x y u v) :
    Track m' x y u v := by
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h.sameMono _ _ h1, h.sameMono _ _ h2⟩
  · exact Or.inr ⟨h.sameMono _ _ h1, h.sameMono _ _ h2⟩

lemma Track.swap {m : E → E} {x y u v : E} (ht : Track m x y u v) : Track m x y v u := by
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · exact Or.inl ⟨h2, h1⟩

lemma Track.congr_left {m : E → E} {x y u v z : E} (ht : Track m x y u v) (hz : same m z u) :
    Track m x y z v := by
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨same_trans hz h1, h2⟩
  · exact Or.inr ⟨same_trans hz h1, h2⟩

lemma Track.same_of_eq {m : E → E} {x y u : E} (ht : Track m x y u u) : same m x y := by
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact same_trans (same_symm h1) h2
  · exact same_trans (same_symm h2) h1

lemma ELocInv.legal {m m' : E → E} (h : Legal key m m') {o : Option (DSUOp E)} {l : ELoc E}
    (hl : ELocInv key k m o l) : ELocInv key k m' o l := by
  rcases o with _ | o
  · exact hl
  · cases l with
    | idle => exact hl
    | done r => trivial
    | rt u v => exact ⟨hl.1, hl.2.1.legal h, hl.2.2⟩
    | lk u v => exact ⟨hl.1, hl.2.1.legal h, hl.2.2⟩
    | zr b u v i =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hl
      exact ⟨h1, h2.legal h, h3, h.nonroot h4, h5⟩
    | wr b u v z i =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hl
      exact ⟨h1, h2.legal h, h3, h.nonroot h4, h5, h.sameMono _ _ h6, h7⟩
    | cs b u v z w i =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hl
      exact ⟨h1, h2.legal h, h3, h.nonroot h4, h5, h.sameMono _ _ h6, h7, h.sameMono _ _ h8, h9⟩

/-- The result of `enter` satisfies the invariant (or is `done true` with `x ~ y`). -/
lemma enter_inv (hkey : Function.Injective key) {m : E → E} {o : DSUOp E} {u v : E}
    (ht : Track m o.x o.y u v) :
    ELocInv key k m (some o) (enter key o.isUnite u v) := by
  unfold enter
  split_ifs with h1 h2 h3 h3
  · trivial
  · exact ⟨h3, ht.swap, h2⟩
  · exact ⟨by simpa using h3, ht.swap, h2⟩
  · have : key u < key v := by
      have : key u ≠ key v := fun h => h1 (hkey h)
      omega
    exact ⟨h3, ht, this⟩
  · have : key u < key v := by
      have : key u ≠ key v := fun h => h1 (hkey h)
      omega
    exact ⟨by simpa using h3, ht, this⟩

lemma enter_cases (b : Bool) (u v : E) :
    (u = v ∧ enter key b u v = .done true) ∨ (u ≠ v ∧ ∀ r, enter key b u v ≠ .done r) := by
  unfold enter
  by_cases h : u = v
  · left; simp [h]
  · right; refine ⟨h, fun r => ?_⟩; simp only [h, ite_false]; split_ifs <;> simp

variable (key k) in
/-- The effect of a `tau` step. -/
def etRes (l : ELoc E) (m : E → E) : Option (ELoc E × (E → E)) :=
  match eact key k l with
  | .access i o c => some (c ((Ptr E i).δ (m i) o).2, Function.update m i ((Ptr E i).δ (m i) o).1)
  | .ret _ _ => none

lemma step_tau_etRes {C C' : Config (dsu E) (Ptr E) P (ELoc E)} {p : P}
    (h : (etImpl key k P).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ etRes key k (C.loc p) C.mem = some (C'.loc p, C'.mem) ∧
      C'.pend = C.pend ∧ ∀ q, q ≠ p → C'.loc q = C.loc q := by
  obtain ⟨hp, hpend, i, o, c, hact, hmem, hloc⟩ := Impl.step_tau h
  refine ⟨hp, ?_, hpend, fun q hq => by rw [hloc, Function.update_of_ne hq]⟩
  have : eact key k (C.loc p) = Action.access i o c := hact
  simp only [etRes, this, hmem, hloc, Function.update_self]

/-- The kinds of steps (with respect to linearization), together with the preservation of the
invariant. -/
theorem etRes_spec (hkey : Function.Injective key) {m : E → E} (hg : Good key m)
    {o : DSUOp E} {l l' : ELoc E} {m' : E → E} (hl : ELocInv key k m (some o) l)
    (h : etRes key k l m = some (l', m')) :
    Legal key m m' ∧ ELocInv key k m' (some o) l' ∧
    (((∀ r, l' ≠ .done r) ∧ same m' = same m) ∨
     (l' = .done true ∧ same m' = same m ∧ same m o.x o.y) ∨
     (l' = .done false ∧ m' = m ∧ o.isUnite = false ∧ ¬ same m o.x o.y) ∨
     (∃ x y, o = .unite x y ∧ l' = .done true ∧
        ∀ a b, same m' a b ↔ joinRel (same m) x y a b)) := by
  cases l with
  | idle => exact hl.elim
  | done r => simp [etRes, eact] at h
  | rt u v =>
    obtain ⟨hb, ht, hlt⟩ := hl
    simp only [etRes, eact, ptr_read, Function.update_eq_self, val, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Legal.refl hg, ?_⟩
    by_cases hr : m u = u
    · simp only [hr, ite_true]
      refine ⟨trivial, Or.inr (Or.inr (Or.inl ⟨by simp, by simp, hb, fun hxy => ?_⟩))⟩
      -- `u` is a root and `v` has a larger id: different trees
      have huv : ¬ same m u v := by
        intro h'
        unfold same at h'
        rw [rootOf_of_fixed hr] at h'
        have := key_le_rootOf hg v
        rw [← h'] at this; omega
      apply huv
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact same_trans h1 (same_trans hxy (same_symm h2))
      · exact same_trans h1 (same_trans (same_symm hxy) (same_symm h2))
    · simp only [hr, ite_false]
      exact ⟨⟨by simp [hb], ht, hlt, hr, Nat.succ_pos _⟩, Or.inl ⟨fun r => by simp, by simp⟩⟩
  | lk u v =>
    obtain ⟨hb, ht, hlt⟩ := hl
    simp only [etRes, eact, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases o with
    | sameSet x y => simp [DSUOp.isUnite] at hb
    | unite x y =>
    simp only [DSUOp.x, DSUOp.y] at ht
    by_cases hr : m u = u
    · simp only [hr, ite_true, Function.update_self]
      refine ⟨Legal.link hg hr hlt, trivial, Or.inr (Or.inr (Or.inr ⟨x, y, rfl, by simp, ?_⟩))⟩
      intro a b
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact same_update_link hg hr hlt h1 h2 a b
      · rw [same_update_link hg hr hlt h1 h2 a b, joinRel_comm]
    · simp only [hr, ite_false, Function.update_eq_self, Sum.inr.injEq, Bool.false_eq_true]
      exact ⟨Legal.refl hg, ⟨rfl, ht, hlt, hr, Nat.succ_pos _⟩, Or.inl ⟨fun r => by simp, by simp⟩⟩
  | zr b u v i =>
    obtain ⟨hb, ht, hlt, hu, hi⟩ := hl
    simp only [etRes, eact, ptr_read, Function.update_eq_self, val, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨Legal.refl hg, ⟨hb, ht, hlt, hu, hi, same_apply hg u, (hg u).resolve_left hu⟩,
      Or.inl ⟨fun r => by simp, by simp⟩⟩
  | wr b u v z i =>
    obtain ⟨hb, ht, hlt, hu, hi, hz, hkz⟩ := hl
    simp only [etRes, eact, ptr_read, Function.update_eq_self, val, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Legal.refl hg, ⟨hb, ht, hlt, hu, hi, hz, hkz, same_apply hg z, ?_⟩,
      Or.inl ⟨fun r => by simp, by simp⟩⟩
    rcases hg z with h | h
    · exact Or.inl h
    · exact Or.inr h
  | cs b u v z w i =>
    obtain ⟨hb, ht, hlt, hu, hi, hz, hkz, hw, hkw⟩ := hl
    have hleg : Legal key m (if m u = z then Function.update m u w else m) := by
      split_ifs with hmu
      · rcases hkw with hkw | hkw
        · subst hkw; rw [← hmu, Function.update_eq_self]; exact Legal.refl hg
        · exact Legal.split hg hmu hkw (by omega) (by unfold same at hw; exact hw)
      · exact Legal.refl hg
    have hsame : same (if m u = z then Function.update m u w else m) = same m := by
      split_ifs with hmu
      · rcases hkw with hkw | hkw
        · subst hkw; rw [← hmu, Function.update_eq_self]
        · funext a c
          have hw' : rootOf m w = rootOf m u := by
            unfold same at hw hz; rw [hw, hz]
          unfold same
          rw [rootOf_update_split hg (by omega) hw', rootOf_update_split hg (by omega) hw']
      · rfl
    have hres : etRes key k (.cs b u v z w i) m =
        some (if i + 1 < k + 1 then .zr b u v (i + 1) else enter key b z v,
          if m u = z then Function.update m u w else m) := by
      simp only [etRes, eact, ptr_cas]
      split_ifs <;> simp
    rw [hres] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hleg, ?_⟩
    generalize (if m u = z then Function.update m u w else m) = m' at hleg hsame ⊢
    by_cases hi' : i + 1 < k + 1
    · simp only [hi', ite_true]
      exact ⟨⟨hb, ht.legal hleg, hlt, hleg.nonroot hu, hi'⟩, Or.inl ⟨fun r => by simp, hsame⟩⟩
    · simp only [hi', ite_false]
      have ht' : Track m' o.x o.y z v := (ht.congr_left hz).legal hleg
      refine ⟨hb ▸ enter_inv hkey ht', ?_⟩
      rcases enter_cases (key := key) b z v with ⟨hzv, he⟩ | ⟨hzv, he⟩
      · rw [he]; right; left
        subst hzv
        exact ⟨rfl, hsame, (ht.congr_left hz).same_of_eq⟩
      · left; exact ⟨he, hsame⟩

/-! ### Invariants along executions -/

lemma eact_ret_cases {l : ELoc E} {r : Bool} {l' : ELoc E} (h : eact key k l = .ret r l') :
    (l = .done r ∧ l' = .idle) ∨ l = .idle := by
  cases l with
  | idle => right; rfl
  | done r' => left; simp only [eact] at h; cases h; exact ⟨rfl, rfl⟩
  | rt u v => simp [eact] at h
  | lk u v => simp [eact] at h
  | zr b u v i => simp [eact] at h
  | wr b u v z i => simp [eact] at h
  | cs b u v z w i => simp [eact] at h

lemma elinv_init : ELInv key k ((etImpl key k P).initCfg) :=
  ⟨fun _ => Or.inl rfl, fun _ => rfl⟩

theorem elinv_step (hkey : Function.Injective key) {C C' : Config (dsu E) (Ptr E) P (ELoc E)}
    {ℓ : Label P (dsu E)} (hI : ELInv key k C) (h : (etImpl key k P).step C ℓ = some C') :
    ELInv key k C' ∧ Legal key C.mem C'.mem := by
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    refine ⟨⟨hmem ▸ hI.good, fun q => ?_⟩, by rw [hmem]; exact Legal.refl hI.good⟩
    rw [hpend, hloc, hmem]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      have : Track C.mem o.x o.y o.x o.y := Or.inl ⟨rfl, rfl⟩
      show ELocInv key k C.mem (some o) (einvoke key o)
      cases o with
      | sameSet x y => exact enter_inv hkey this
      | unite x y => exact enter_inv hkey this
    · simp only [Function.update_of_ne hq]; exact hI.loc q
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    refine ⟨⟨hmem ▸ hI.good, fun q => ?_⟩, by rw [hmem]; exact Legal.refl hI.good⟩
    rw [hpend, hloc, hmem]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      have hact' : eact key k (C.loc q) = .ret r l := hact
      rcases eact_ret_cases hact' with ⟨-, rfl⟩ | h1
      · rfl
      · have := hI.loc q
        obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
        rw [ho, h1] at this; exact this.elim
    · simp only [Function.update_of_ne hq]; exact hI.loc q
  | tau p =>
    obtain ⟨hp, hres, hpend, hother⟩ := step_tau_etRes h
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
    have hl := hI.loc p
    rw [ho] at hl
    obtain ⟨hleg, hl', -⟩ := etRes_spec hkey hI.good hl hres
    refine ⟨⟨hleg.good, fun q => ?_⟩, hleg⟩
    rw [hpend]
    by_cases hq : q = p
    · subst hq; rw [ho]; exact hl'
    · rw [hother q hq]; exact (hI.loc q).legal hleg

theorem elinv_of_run (hkey : Function.Injective key) {C : Config (dsu E) (Ptr E) P (ELoc E)}
    {α : List (Label P (dsu E))} (h : (etImpl key k P).run α = some C) : ELInv key k C := by
  suffices ∀ C₀ β, ELInv key k C₀ → (etImpl key k P).runFrom C₀ β = some C → ELInv key k C from
    this _ α elinv_init h
  intro C₀ β
  induction β generalizing C₀ with
  | nil => intro hI h; simp only [Impl.runFrom_nil, Option.some.injEq] at h; exact h ▸ hI
  | cons ℓ β ih =>
    intro hI h
    simp only [Impl.runFrom_cons] at h
    cases hs : (etImpl key k P).step C₀ ℓ with
    | none => simp [hs] at h
    | some C₁ => rw [hs] at h; exact ih C₁ (elinv_step hkey hI hs).1 h

/-! ### Linearizability -/

/-- Per-process part of the linearization invariant. -/
structure EQOK (α : List (Label P (dsu E))) (C : Config (dsu E) (Ptr E) P (ELoc E))
    (L : List (OpId P × (dsu E).Op)) (q : P) : Prop where
  done : ∀ o r, C.pend q = some o → C.loc q = .done r →
    ∃ L₁ L₂, L = L₁ ++ (curOp α q, o) :: L₂ ∧ ((dsu E).δ (st L₁) o).2 = r
  notin : C.pend q ≠ none → (∀ r, C.loc q ≠ .done r) → curOp α q ∉ L.map Prod.fst

/-- The linearization invariant. -/
structure ELinInv (α : List (Label P (dsu E))) (C : Config (dsu E) (Ptr E) P (ELoc E))
    (L : List (OpId P × (dsu E).Op)) : Prop where
  lin : IsLinearization α L
  state : st L = same C.mem
  qok : ∀ q, EQOK α C L q

/-- Transport of the per-process invariant of a process `q ≠ p` when `L` is unchanged or
extended by an operation of `p`. -/
lemma EQOK.transport {α α' : List (Label P (dsu E))} {C C' : Config (dsu E) (Ptr E) P (ELoc E)}
    {L : List (OpId P × (dsu E).Op)} {q : P} (hq : EQOK α C L q) (ext : List (OpId P × (dsu E).Op))
    (hext : ∀ y ∈ ext.map Prod.fst, y.1 ≠ q)
    (hcur : curOp α' q = curOp α q) (hpend : C'.pend q = C.pend q) (hloc : C'.loc q = C.loc q) :
    EQOK α' C' (L ++ ext) q where
  done o r hp hl := by
    rw [hpend] at hp; rw [hloc] at hl
    obtain ⟨L₁, L₂, hsplit, hr⟩ := hq.done o r hp hl
    exact ⟨L₁, L₂ ++ ext, by rw [hcur, hsplit]; simp, hr⟩
  notin hp hl := by
    rw [hpend] at hp; rw [hloc] at hl
    rw [hcur, List.map_append, List.mem_append, not_or]
    exact ⟨hq.notin hp hl, fun h => hext _ h rfl⟩

lemma elinInv_nil : ELinInv ([] : List (Label P (dsu E))) (etImpl key k P).initCfg [] := by
  refine ⟨isLinearization_nil, ?_, fun q => ⟨?_, ?_⟩⟩
  · funext a b
    show (a = b) = ((fun a : E => a)^[Fintype.card E] a = (fun a : E => a)^[Fintype.card E] b)
    rw [Function.iterate_fixed rfl, Function.iterate_fixed rfl]
  · intro o r hp; simp [Impl.initCfg] at hp
  · intro hp; simp [Impl.initCfg] at hp

/-- Responses at linearization points. -/
lemma resp_true_of_same {L : List (OpId P × (dsu E).Op)} {m : E → E} (hs : st L = same m)
    {o : DSUOp E} (h : same m o.x o.y) : ((dsu E).δ (st L) o).2 = true := by
  cases o with
  | sameSet x y => exact @decide_eq_true _ (Classical.dec _) (by rw [hs]; exact h)
  | unite x y => rfl

lemma state_of_same {L : List (OpId P × (dsu E).Op)} {m : E → E} (hs : st L = same m)
    {o : DSUOp E} (h : same m o.x o.y) : ((dsu E).δ (st L) o).1 = same m := by
  cases o with
  | sameSet x y => exact hs
  | unite x y => show joinRel (st L) x y = _; rw [hs]; exact joinRel_same h

theorem exists_elinInv (hkey : Function.Injective key) {α : List (Label P (dsu E))}
    {C : Config (dsu E) (Ptr E) P (ELoc E)} (h : (etImpl key k P).run α = some C) :
    ∃ L, ELinInv α C L := by
  induction α using List.reverseRecOn generalizing C with
  | nil =>
    simp only [Impl.run, Impl.runFrom, Option.some.injEq] at h; subst h
    exact ⟨[], elinInv_nil⟩
  | append_singleton α ℓ ih =>
    rw [Impl.run, Impl.runFrom_append] at h
    cases hα : (etImpl key k P).runFrom (etImpl key k P).initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, Impl.runFrom_singleton] at h
      obtain ⟨L, hL⟩ := ih hα
      have hI : ELInv key k C₀ := elinv_of_run hkey hα
      cases ℓ with
      | inv p o =>
        obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
        have hcur : ∀ q, curOp (α ++ [.inv p o]) q = curOp α q := by
          intro q; simp [curOp, respsOf_append]
        have hlin := hL.lin.append_inv p o
        have hnotin : curOp α p ∉ L.map Prod.fst := by
          intro hm
          have hi := hL.lin.mem_invoked hm
          rcases Impl.run_counts _ hα p with ⟨-, h2⟩ | ⟨h1, -⟩
          · simp [Invoked, h2] at hi
          · exact h1 h0
        have hlp : C.loc p = einvoke key o := by rw [hloc, Function.update_self]; rfl
        have hpp : C.pend p = some o := by rw [hpend, Function.update_self]
        have hcf := Impl.run_pend_curOp (I := etImpl key k P) (α := α ++ [.inv p o])
          (by rw [Impl.run, Impl.runFrom_append, hα]
              simp only [Option.bind_some, Impl.runFrom_singleton]; exact h) hpp
        have hTr : Track C₀.mem o.x o.y o.x o.y := Or.inl ⟨rfl, rfl⟩
        have hen := enter_cases (key := key) o.isUnite o.x o.y
        have hei : einvoke key o = enter key o.isUnite o.x o.y := by cases o <;> rfl
        rcases hen with ⟨hxy, he⟩ | ⟨-, he⟩
        · -- `x = y`: linearize at the invocation
          have hsame : same C₀.mem o.x o.y := by rw [hxy]; exact same_refl _ _
          refine ⟨L ++ [(curOp α p, o)], ?_, ?_, fun q => ?_⟩
          · rw [← hcur p]; exact hlin.push hcf.2.2 (by rw [hcur]; exact hnotin) hcf.2.1
          · rw [st_append, hmem]; exact state_of_same hL.state hsame
          · by_cases hq : q = p
            · subst hq
              refine ⟨fun o' r hp' hl' => ?_, fun _ hd => absurd (by rw [hlp, hei, he]) (hd true)⟩
              rw [hpp] at hp'; cases hp'
              rw [hlp, hei, he] at hl'; cases hl'
              exact ⟨L, [], by rw [hcur], resp_true_of_same hL.state hsame⟩
            · exact (hL.qok q).transport _ (by simp [Ne.symm hq]) (hcur q)
                (by rw [hpend, Function.update_of_ne hq]) (by rw [hloc, Function.update_of_ne hq])
        · refine ⟨L ++ [], by simpa using hlin, by simp only [List.append_nil, hmem]; exact hL.state,
            fun q => ?_⟩
          by_cases hq : q = p
          · subst hq
            refine ⟨fun o' r hp' hl' => ?_, fun _ _ => by rw [hcur]; simpa using hnotin⟩
            rw [hpp] at hp'; cases hp'
            rw [hlp, hei] at hl'; exact absurd hl' (he r)
          · exact (hL.qok q).transport [] (by simp) (hcur q)
              (by rw [hpend, Function.update_of_ne hq]) (by rw [hloc, Function.update_of_ne hq])
      | ret p r =>
        obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
        obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
        have hact' : eact key k (C₀.loc p) = .ret r l := hact
        have hlp : C₀.loc p = .done r := by
          rcases eact_ret_cases hact' with ⟨h1, -⟩ | h1
          · exact h1
          · have := hI.loc p; rw [ho, h1] at this; exact this.elim
        obtain ⟨L₁, L₂, hsplit, hr⟩ := (hL.qok p).done o r ho hlp
        refine ⟨L ++ [], by simpa using hL.lin.append_ret L₁ L₂ o hsplit hr,
          by simp only [List.append_nil, hmem]; exact hL.state, fun q => ?_⟩
        by_cases hq : q = p
        · subst hq
          have hpq : C.pend q = none := by rw [hpend, Function.update_self]
          refine ⟨fun o' r' hp _ => ?_, fun hp _ => absurd hpq hp⟩
          rw [hpq] at hp; cases hp
        · have hcur : curOp (α ++ [.ret p r]) q = curOp α q := by
            simp [curOp, respsOf_append, Ne.symm hq]
          exact (hL.qok q).transport [] (by simp) hcur
            (by rw [hpend, Function.update_of_ne hq]) (by rw [hloc, Function.update_of_ne hq])
      | tau p =>
        obtain ⟨hp, hres, hpend, hother⟩ := step_tau_etRes h
        obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
        have hl := hI.loc p
        rw [ho] at hl
        obtain ⟨hleg, -, hcase⟩ := etRes_spec hkey hI.good hl hres
        have hcur : ∀ q, curOp (α ++ [.tau p]) q = curOp α q := by
          intro q; simp [curOp, respsOf_append]
        have hlin' := hL.lin.append_tau p
        have hcf := Impl.run_pend_curOp hα ho
        have hnc : ¬ Completed (α ++ [.tau p]) (curOp α p) := by
          simp [Completed, respsOf_append]
        have hop' : opOf (α ++ [.tau p]) (curOp α p) = some o := by
          rw [opOf_append_of_invoked hcf.1]; exact hcf.2.2
        have hldone : ∀ r, C₀.loc p ≠ .done r := fun r h' => by
          rw [h'] at hres; simp [etRes, eact] at hres
        have hnotin := (hL.qok p).notin (by rw [ho]; simp) hldone
        have others : ∀ ext : List (OpId P × (dsu E).Op), (∀ y ∈ ext.map Prod.fst, y.1 = p) →
            ∀ q, q ≠ p → EQOK (α ++ [.tau p]) C (L ++ ext) q := by
          intro ext hext q hq
          exact (hL.qok q).transport ext (fun y hy h' => hq (h' ▸ hext y hy)) (hcur q)
            (by rw [hpend]) (hother q hq)
        -- a linearization point of `p` at this step
        have linpt : ∀ r, C.loc p = .done r → ((dsu E).δ (st L) o).2 = r →
            ((dsu E).δ (st L) o).1 = same C.mem → ∃ L', ELinInv (α ++ [.tau p]) C L' := by
          intro r hl' hr hs
          refine ⟨L ++ [(curOp α p, o)], hlin'.push hop' hnotin hnc, by rw [st_append]; exact hs,
            fun q => ?_⟩
          by_cases hq : q = p
          · subst hq
            refine ⟨fun o' r' hp' hl'' => ?_, fun _ hd => absurd hl' (hd r)⟩
            rw [hpend, ho] at hp'; cases hp'
            rw [hl''] at hl'; cases hl'
            exact ⟨L, [], by rw [hcur], hr⟩
          · exact others _ (by simp) q hq
        rcases hcase with ⟨hnd, hsame⟩ | ⟨hl', hsame, hxy⟩ | ⟨hl', hm, hb, hxy⟩ |
          ⟨x, y, rfl, hl', hjoin⟩
        · refine ⟨L ++ [], by simpa using hlin', by
            simp only [List.append_nil]; rw [hL.state, hsame], fun q => ?_⟩
          by_cases hq : q = p
          · subst hq
            refine ⟨fun o' r' _ hl'' => absurd hl'' (hnd r'), fun _ _ => ?_⟩
            rw [hcur]; simpa using hnotin
          · exact others [] (by simp) q hq
        · exact linpt true hl' (resp_true_of_same hL.state hxy)
            (by rw [hsame]; exact state_of_same hL.state hxy)
        · cases o with
          | unite x y => simp [DSUOp.isUnite] at hb
          | sameSet x y =>
            refine linpt false hl' ?_ (by rw [hm]; exact hL.state)
            exact @decide_eq_false _ (Classical.dec _) (by rw [hL.state]; exact hxy)
        · refine linpt true hl' rfl ?_
          show joinRel (st L) x y = _
          rw [hL.state]
          funext a b
          exact propext (hjoin a b).symm

/-- **Algorithms 6 and 7 (early termination, `k + 1`-try splitting) are linearizable.** -/
theorem et_linearizable (hkey : Function.Injective key) : (etImpl key k P).Linearizable :=
  Impl.linearizable_of_run fun _ _ hC =>
    let ⟨L, hL⟩ := exists_elinInv hkey hC
    ⟨L, hL.lin⟩

/-! ### Wait-freedom -/

variable (key k) in
/-- Potential of a process: the ids of `u` and `v` and the program counter of the iteration. -/
def eΦ : ELoc E → ℕ
  | .idle => 0
  | .done _ => 0
  | .rt u v => (3 * k + 4) * (hgt key u + hgt key v) + 3 * (k + 1)
  | .lk u v => (3 * k + 4) * (hgt key u + hgt key v) + 3 * (k + 1)
  | .zr _ u v i => (3 * k + 4) * (hgt key u + hgt key v) + (3 * (k - i) + 2)
  | .wr _ u v _ i => (3 * k + 4) * (hgt key u + hgt key v) + (3 * (k - i) + 1)
  | .cs _ u v _ _ i => (3 * k + 4) * (hgt key u + hgt key v) + 3 * (k - i)

lemma eΦ_enter {b : Bool} {z v : E} :
    eΦ key k (enter key b z v) ≤ (3 * k + 4) * (hgt key z + hgt key v) + 3 * (k + 1) := by
  unfold enter
  split_ifs <;> simp only [eΦ] <;> first | omega | (rw [Nat.add_comm (hgt key v)])

theorem eΦ_dec {m : E → E} {o : DSUOp E}
    {l l' : ELoc E} {m' : E → E} (hl : ELocInv key k m (some o) l)
    (h : etRes key k l m = some (l', m')) : eΦ key k l' < eΦ key k l := by
  cases l with
  | idle => exact hl.elim
  | done r => simp [etRes, eact] at h
  | rt u v =>
    simp only [etRes, eact, ptr_read, Function.update_eq_self, val, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    by_cases hr : m u = u <;> simp only [hr, ite_true, ite_false, eΦ] <;> omega
  | lk u v =>
    simp only [etRes, eact, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    by_cases hr : m u = u <;> simp [hr, eΦ] <;> omega
  | zr b u v i =>
    simp only [etRes, eact, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [eΦ]; omega
  | wr b u v z i =>
    simp only [etRes, eact, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    simp only [eΦ]; omega
  | cs b u v z w i =>
    obtain ⟨hb, ht, hlt, hu, hi, hz, hkz, hw, hkw⟩ := hl
    simp only [etRes, eact, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    split_ifs with hi'
    · simp only [eΦ]; omega
    · have h1 := eΦ_enter (key := key) (k := k) (b := b) (z := z) (v := v)
      have h2 := hgt_lt hkz
      rw [show eΦ key k (ELoc.cs b u v z w i) = (3 * k + 4) * (hgt key u + hgt key v) + 3 * (k - i)
        from rfl]
      have : (3 * k + 4) * (hgt key z + hgt key v) + (3 * k + 4) ≤
          (3 * k + 4) * (hgt key u + hgt key v) := by
        rw [← Nat.mul_succ]; apply Nat.mul_le_mul_left; omega
      omega

/-- **Algorithms 6 and 7 are wait-free.** -/
theorem et_waitFree (hkey : Function.Injective key) : (etImpl key k P).WaitFree := by
  refine Impl.waitFree_of_cfgPotential _ (ELInv key k) elinv_init
    (fun C C' ℓ hI h => (elinv_step hkey hI h).1) (fun p C => eΦ key k (C.loc p)) ?_
  intro p C C' ℓ hI hp h
  by_cases hq : ℓ.proc = p
  · cases ℓ with
    | inv q o => simp only [Label.proc] at hq; subst hq; exact absurd (Impl.step_inv h).1 hp
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, -, l, hact, hl⟩ := Impl.step_ret h
      have hact' : eact key k (C.loc q) = .ret r l := hact
      rcases eact_ret_cases hact' with ⟨-, rfl⟩ | h1
      · refine ⟨?_, fun h' => by cases h'⟩
        rw [hl, Function.update_self]; simp [eΦ]
      · have := hI.loc q
        obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
        rw [ho, h1] at this; exact this.elim
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, hres, -, -⟩ := step_tau_etRes h
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
      have hl := hI.loc q
      rw [ho] at hl
      have := eΦ_dec hl hres
      exact ⟨this.le, fun _ => this⟩
  · rw [(Impl.step_other h hq).1]
    exact ⟨le_rfl, fun h' => absurd (by rw [h']; rfl) hq⟩

end Podc.ConcurrentDSU
