import Papers.PODC2016.ConcurrentDSU.Forest

/-!
# Local invariants of the concurrent DSU (Lemma 3.1 and the facts behind Lemma 3.2)

`LInv C`: the memory is a `Good` forest (Lemma 3.1) and every process's local variables
satisfy `LocInv`: the variable `u` of `SameSet(x, y)` / `Unite(x, y)` is always in the tree of
`x`, `v` in the tree of `y` ("u is always in the same tree as x", proof of Lemma 3.2), and the
variables of a running `Find` satisfy `FInv` (the value read as a parent is in the same tree and
has a larger id, etc.).

Main results:
* `tauRes_spec` — one step of a process: the memory change is `Legal` (`Find` only shortcuts
  inside a tree, `Unite` links a root below a node with a larger id) and the invariant of the
  stepping process is preserved;
* `LocInv.legal` — invariants of the other processes survive legal memory changes;
* `linv_step`, `linv_of_run` — `LInv` holds in every reachable configuration.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentDSU

open Cslib.SharedMemory

variable {E : Type} [Fintype E] [DecidableEq E] {P : Type} [DecidableEq P]

/-- First argument of an operation. -/
def DSUOp.x : DSUOp E → E
  | .sameSet x _ => x
  | .unite x _ => x

/-- Second argument of an operation. -/
def DSUOp.y : DSUOp E → E
  | .sameSet _ y => y
  | .unite _ y => y

/-- Is the operation a `Unite`? -/
def DSUOp.isUnite : DSUOp E → Bool
  | .sameSet _ _ => false
  | .unite _ _ => true

@[simp] lemma ptr_read (a q : E) : (Ptr E a).δ q .read = (q, .inl q) := rfl

@[simp] lemma ptr_cas (a q o n : E) :
    (Ptr E a).δ q (.cas o n) = if q = o then (n, .inr true) else (q, .inr false) := rfl

variable (K : FindKind) (key : E → ℕ)

/-- Invariant of a `Find` started at `s`, in memory `m`. -/
def FInv (m : E → E) (s : E) : FS E → Prop
  | .tst u => same m u s
  | .adv u => same m u s ∧ m u ≠ u
  | .rdP u i => i < K.tries ∧ same m u s
  | .rdG u v i => i < K.tries ∧ same m u s ∧ same m v u ∧ (v = u ∨ key u < key v) ∧
      (v ≠ u → m u ≠ u)
  | .cas u v w i => i < K.tries ∧ same m u s ∧ same m v u ∧ same m w v ∧ key v < key w ∧
      (v = u ∨ key u < key v) ∧ (v ≠ u → m u ≠ u) ∧ m v ≠ v

/-- Invariant of a process with pending operation `o` and local state `l`. -/
def LocInv (m : E → E) : Option (DSUOp E) → Loc E → Prop
  | none, l => l = .idle
  | some _, .idle => False
  | some o, .fu b fs v => b = o.isUnite ∧ FInv K key m o.x fs ∧ same m v o.y
  | some o, .fv b u fs => b = o.isUnite ∧ same m u o.x ∧ FInv K key m o.y fs
  | some o, .chk u v => o.isUnite = false ∧ same m u o.x ∧ same m v o.y ∧ u ≠ v
  | some o, .lnk u v => o.isUnite = true ∧ same m u o.x ∧ same m v o.y ∧ u ≠ v
  | some _, .done _ => True

/-- The invariant of a configuration. -/
structure LInv (C : Config (dsu E) (Ptr E) P (Loc E)) : Prop where
  good : Good key C.mem
  loc : ∀ p, LocInv K key C.mem (C.pend p) (C.loc p)

variable {K key}

lemma FInv.legal {m m' : E → E} (h : Legal key m m') {s : E} {fs : FS E}
    (hf : FInv K key m s fs) : FInv K key m' s fs := by
  cases fs with
  | tst u => exact h.sameMono _ _ hf
  | adv u => exact ⟨h.sameMono _ _ hf.1, h.nonroot hf.2⟩
  | rdP u i => exact ⟨hf.1, h.sameMono _ _ hf.2⟩
  | rdG u v i =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hf
    exact ⟨h1, h.sameMono _ _ h2, h.sameMono _ _ h3, h4, fun hv => h.nonroot (h5 hv)⟩
  | cas u v w i =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    exact ⟨h1, h.sameMono _ _ h2, h.sameMono _ _ h3, h.sameMono _ _ h4, h5, h6,
      fun hv => h.nonroot (h7 hv), h.nonroot h8⟩

lemma LocInv.legal {m m' : E → E} (h : Legal key m m') {o : Option (DSUOp E)} {l : Loc E}
    (hl : LocInv K key m o l) : LocInv K key m' o l := by
  rcases o with _ | o
  · exact hl
  · cases l with
    | idle => exact hl
    | fu b fs v => exact ⟨hl.1, hl.2.1.legal h, h.sameMono _ _ hl.2.2⟩
    | fv b u fs => exact ⟨hl.1, h.sameMono _ _ hl.2.1, hl.2.2.legal h⟩
    | chk u v => exact ⟨hl.1, h.sameMono _ _ hl.2.1, h.sameMono _ _ hl.2.2.1, hl.2.2.2⟩
    | lnk u v => exact ⟨hl.1, h.sameMono _ _ hl.2.1, h.sameMono _ _ hl.2.2.1, hl.2.2.2⟩
    | done r => trivial

lemma same_refl (m : E → E) (a : E) : same m a a := rfl

lemma same_symm {m : E → E} {a b : E} (h : same m a b) : same m b a := Eq.symm h

lemma same_trans {m : E → E} {a b c : E} (h1 : same m a b) (h2 : same m b c) : same m a c :=
  Eq.trans h1 h2

lemma FInv_start (m : E → E) (s u : E) (hu : same m u s) : FInv K key m s (FS.start K u) := by
  cases K with
  | naive => exact hu
  | split k => exact ⟨by simp [FindKind.tries], hu⟩

/-! ### One `Find` step -/

variable (K) in
/-- The effect of one step of a `Find` in memory `m`: its continuation value and the new
memory. -/
def fRes (fs : FS E) (m : E → E) : (FS E ⊕ E) × (E → E) :=
  match fs.next K with
  | .read a k => (k (m a), m)
  | .cas a o n k => (k, if m a = o then Function.update m a n else m)

/-- One step of a `Find`: the memory change is legal; the new `Find` state satisfies the
invariant, or the returned node is a root of the tree of `s` (at the time of the step). -/
lemma fRes_spec {m : E → E} (hg : Good key m) {s : E} {fs : FS E} (hf : FInv K key m s fs) :
    Legal key m (fRes K fs m).2 ∧
    (match (fRes K fs m).1 with
      | .inl fs' => FInv K key (fRes K fs m).2 s fs'
      | .inr r => (fRes K fs m).2 = m ∧ m r = r ∧ same m r s) := by
  cases fs with
  | tst u =>
    simp only [fRes, FS.next]
    refine ⟨Legal.refl hg, ?_⟩
    split_ifs with h
    · exact ⟨trivial, h, hf⟩
    · exact ⟨hf, h⟩
  | adv u =>
    simp only [fRes, FS.next]
    exact ⟨Legal.refl hg, same_trans (same_apply hg u) hf.1⟩
  | rdP u i =>
    simp only [fRes, FS.next]
    refine ⟨Legal.refl hg, hf.1, hf.2, same_apply hg u, ?_, fun h => h⟩
    rcases hg u with h | h
    · exact Or.inl h
    · exact Or.inr h
  | rdG u v i =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := hf
    simp only [fRes, FS.next]
    refine ⟨Legal.refl hg, ?_⟩
    split_ifs with h
    · exact ⟨trivial, h, same_trans h3 h2⟩
    · refine ⟨h1, h2, h3, same_apply hg v, (hg v).resolve_left h, h4, h5, h⟩
  | cas u v w i =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    -- the `Cas` can only succeed if `v ≠ u`
    have hku : m u = v → key u < key v := by
      intro hmu
      rcases h6 with h6 | h6
      · subst h6
        exfalso
        have hr : rootOf m w = v := by
          unfold same at h4 h3; rw [h4, h3, rootOf_of_fixed hmu]
        have := key_le_rootOf hg w; rw [hr] at this; omega
      · exact h6
    have hleg : Legal key m (if m u = v then Function.update m u w else m) := by
      split_ifs with hmu
      · exact Legal.split hg hmu h5 (by have := hku hmu; omega) h4
      · exact Legal.refl hg
    have hres : fRes K (.cas u v w i) m =
        (if i + 1 < K.tries then .inl (.rdP u (i + 1)) else .inl (.rdP v 0),
          if m u = v then Function.update m u w else m) := rfl
    rw [hres]
    generalize (if m u = v then Function.update m u w else m) = m' at hleg ⊢
    refine ⟨hleg, ?_⟩
    by_cases hi : i + 1 < K.tries
    · simp only [hi, ite_true]
      exact ⟨hi, hleg.sameMono _ _ h2⟩
    · simp only [hi, ite_false]
      exact ⟨K.tries_pos, hleg.sameMono _ _ (same_trans h3 h2)⟩

/-! ### One step of a process -/

variable (K key) in
/-- The effect of a `tau` step of a process in local state `l` with memory `m`. -/
def tauRes (l : Loc E) (m : E → E) : Option (Loc E × (E → E)) :=
  match act K key l with
  | .access i o k => some (k ((Ptr E i).δ (m i) o).2, Function.update m i ((Ptr E i).δ (m i) o).1)
  | .ret _ _ => none

lemma tauRes_liftF (fs : FS E) (c : FS E ⊕ E → Loc E) (m : E → E) :
    (match liftF K fs c with
      | .access i o k => some (k ((Ptr E i).δ (m i) o).2,
          Function.update m i ((Ptr E i).δ (m i) o).1)
      | .ret _ _ => none) = some (c (fRes K fs m).1, (fRes K fs m).2) := by
  unfold liftF fRes
  cases h : fs.next K with
  | read a k => simp [val]
  | cas a o n k =>
    simp only [ptr_cas]
    split_ifs with h1
    · rfl
    · simp

lemma step_tau_tauRes {C C' : Config (dsu E) (Ptr E) P (Loc E)} {p : P}
    (h : (dsuImpl K key P).step C (.tau p) = some C') :
    C.pend p ≠ none ∧ tauRes K key (C.loc p) C.mem = some (C'.loc p, C'.mem) ∧
      C'.pend = C.pend ∧ ∀ q, q ≠ p → C'.loc q = C.loc q := by
  obtain ⟨hp, hpend, i, o, k, hact, hmem, hloc⟩ := Impl.step_tau h
  refine ⟨hp, ?_, hpend, fun q hq => by rw [hloc, Function.update_of_ne hq]⟩
  have : act K key (C.loc p) = Action.access i o k := hact
  simp only [tauRes, this, hmem, hloc, Function.update_self]

/-- **One step of a process preserves its invariant, and the memory change is legal.** -/
theorem tauRes_spec (hkey : Function.Injective key) {m : E → E} (hg : Good key m)
    {o : DSUOp E} {l l' : Loc E} {m' : E → E} (hl : LocInv K key m (some o) l)
    (h : tauRes K key l m = some (l', m')) :
    Legal key m m' ∧ LocInv K key m' (some o) l' := by
  cases l with
  | idle => exact hl.elim
  | done r => simp [tauRes, act] at h
  | fu b fs v =>
    obtain ⟨hb, hf, hv⟩ := hl
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs := fRes_spec hg hf
    refine ⟨hs.1, ?_⟩
    revert hs
    cases (fRes K fs m).1 with
    | inl fs' => intro hs; exact ⟨hb, hs.2, hs.1.sameMono _ _ hv⟩
    | inr r =>
      rintro ⟨hleg, hm, hr, hrs⟩
      simp only [contU]
      rw [hm]
      exact ⟨hb, hrs, FInv_start m _ _ hv⟩
  | fv b u fs =>
    obtain ⟨hb, hu, hf⟩ := hl
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs := fRes_spec hg hf
    refine ⟨hs.1, ?_⟩
    revert hs
    cases (fRes K fs m).1 with
    | inl fs' => intro hs; exact ⟨hb, hs.1.sameMono _ _ hu, hs.2⟩
    | inr r =>
      rintro ⟨hleg, hm, hr, hrs⟩
      simp only [contV]
      rw [hm]
      split_ifs with h1 h2
      · trivial
      · exact ⟨hb ▸ h2, hu, hrs, h1⟩
      · exact ⟨by simpa [h2] using hb.symm, hu, hrs, h1⟩
  | chk u v =>
    obtain ⟨hb, hu, hv, huv⟩ := hl
    simp only [tauRes, act, ptr_read, Function.update_eq_self, val, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨Legal.refl hg, ?_⟩
    by_cases h1 : m u = u
    · simp only [h1, ite_true]; trivial
    · simp only [h1, ite_false]; exact ⟨by simp [hb], FInv_start _ _ _ hu, hv⟩
  | lnk u v =>
    obtain ⟨hb, hu, hv, huv⟩ := hl
    have hk : key u ≠ key v := fun h => huv (hkey h)
    by_cases hlt : key u < key v
    · simp only [tauRes, act, hlt, ite_true, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hr : m u = u
      · simp only [hr, ite_true, Function.update_self]
        exact ⟨Legal.link hg hr hlt, trivial⟩
      · simp only [hr, ite_false, Function.update_eq_self, reduceCtorEq]
        exact ⟨Legal.refl hg, by simp [hb], FInv_start _ _ _ hu, hv⟩
    · have hlt' : key v < key u := by omega
      simp only [tauRes, act, hlt, ite_false, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hr : m v = v
      · simp only [hr, ite_true, Function.update_self]
        exact ⟨Legal.link hg hr hlt', trivial⟩
      · simp only [hr, ite_false, Function.update_eq_self, reduceCtorEq]
        exact ⟨Legal.refl hg, by simp [hb], FInv_start _ _ _ hu, hv⟩

/-! ### The invariant in reachable configurations -/

lemma linv_init : LInv K key ((dsuImpl K key P).initCfg) := by
  refine ⟨fun a => Or.inl rfl, fun p => ?_⟩
  rfl

/-- Every step preserves `LInv`, and the memory change is legal. -/
theorem linv_step (hkey : Function.Injective key) {C C' : Config (dsu E) (Ptr E) P (Loc E)}
    {ℓ : Label P (dsu E)} (hI : LInv K key C) (h : (dsuImpl K key P).step C ℓ = some C') :
    LInv K key C' ∧ Legal key C.mem C'.mem := by
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    refine ⟨⟨hmem ▸ hI.good, fun q => ?_⟩, by rw [hmem]; exact Legal.refl hI.good⟩
    rw [hpend, hloc, hmem]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      cases o with
      | sameSet x y => exact ⟨rfl, FInv_start _ _ _ rfl, rfl⟩
      | unite x y => exact ⟨rfl, FInv_start _ _ _ rfl, rfl⟩
    · simp only [Function.update_of_ne hq]; exact hI.loc q
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    refine ⟨⟨hmem ▸ hI.good, fun q => ?_⟩, by rw [hmem]; exact Legal.refl hI.good⟩
    rw [hpend, hloc, hmem]
    by_cases hq : q = p
    · subst hq
      simp only [Function.update_self]
      have hl := hI.loc q
      have hact' : act K key (C.loc q) = .ret r l := hact
      obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
      rw [ho] at hl
      cases hc : C.loc q with
      | idle => rw [hc] at hl; exact hl.elim
      | done r' => rw [hc] at hact'; simp only [act] at hact'; cases hact'; rfl
      | fu b fs v => rw [hc] at hact'; simp only [act, liftF] at hact'; split at hact' <;> cases hact'
      | fv b u fs => rw [hc] at hact'; simp only [act, liftF] at hact'; split at hact' <;> cases hact'
      | chk u v => rw [hc] at hact'; simp [act] at hact'
      | lnk u v => rw [hc] at hact'; simp only [act] at hact'; split_ifs at hact'
    · simp only [Function.update_of_ne hq]; exact hI.loc q
  | tau p =>
    obtain ⟨hp, hres, hpend, hother⟩ := step_tau_tauRes h
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
    have hl := hI.loc p
    rw [ho] at hl
    obtain ⟨hleg, hl'⟩ := tauRes_spec hkey hI.good hl hres
    refine ⟨⟨hleg.good, fun q => ?_⟩, hleg⟩
    rw [hpend]
    by_cases hq : q = p
    · subst hq; rw [ho]; exact hl'
    · rw [hother q hq]; exact (hI.loc q).legal hleg

theorem linv_runFrom (hkey : Function.Injective key) {C C' : Config (dsu E) (Ptr E) P (Loc E)}
    {α : List (Label P (dsu E))} (hI : LInv K key C)
    (h : (dsuImpl K key P).runFrom C α = some C') : LInv K key C' := by
  induction α generalizing C with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; exact h ▸ hI
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (dsuImpl K key P).step C ℓ with
    | none => simp [hs] at h
    | some C₁ =>
      rw [hs] at h
      exact ih (linv_step hkey hI hs).1 h

theorem linv_of_run (hkey : Function.Injective key) {C : Config (dsu E) (Ptr E) P (Loc E)}
    {α : List (Label P (dsu E))} (h : (dsuImpl K key P).run α = some C) : LInv K key C :=
  linv_runFrom hkey linv_init h

end Podc.ConcurrentDSU
