import Papers.PODC2016.ConcurrentDSU.Main

/-!
# Lemma 3.1 with the union forest

The *union forest* is "the forest constructed by the links done in `Unite`s, ignoring all parent
changes done by `Find`s". We compute it along an execution (`uf α`): a step that turns a root `a`
into a non-root with parent `b` (a successful link) sets `U a := b`; other steps leave `U`
unchanged.

`lemma_3_1_union`: after every execution,
* the union forest has the same roots as the actual forest, ids increase along its edges, and
  the actual parent of every node is an ancestor of it in the union forest;
* every step either leaves the parent pointers unchanged, or links a root `a` below a node `b`
  of another tree (and the union forest gets the edge `a → b`), or replaces the parent `v` of a
  non-root by a *proper ancestor of `v` in the union forest* (the union forest is unchanged).

This is Lemma 3.1 as stated in the paper.
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentDSU

open Cslib.SharedMemory

variable {E : Type} [Fintype E] [DecidableEq E] {P : Type} [DecidableEq P]
variable {K : FindKind} {key : E → ℕ}

/-- `b` is an ancestor of `a` (or `a` itself) in the forest `U`. -/
def Reach (U : E → E) (a b : E) : Prop := ∃ j, U^[j] a = b

lemma Reach.refl (U : E → E) (a : E) : Reach U a a := ⟨0, rfl⟩

lemma Reach.trans {U : E → E} {a b c : E} (h1 : Reach U a b) (h2 : Reach U b c) : Reach U a c := by
  obtain ⟨i, rfl⟩ := h1; obtain ⟨j, rfl⟩ := h2
  exact ⟨j + i, by rw [Function.iterate_add_apply]⟩

lemma Reach.step (U : E → E) (a : E) : Reach U a (U a) := ⟨1, rfl⟩

/-- Linking a root `u` keeps all ancestor relations. -/
lemma Reach.link {U : E → E} {u b : E} (hu : U u = u) {x y : E} (h : Reach U x y) :
    Reach (Function.update U u b) x y := by
  obtain ⟨j, hj⟩ := h
  induction j generalizing x with
  | zero => exact ⟨0, hj⟩
  | succ j ih =>
    by_cases hx : x = u
    · subst hx
      rw [iterate_fixed hu] at hj
      subst hj; exact Reach.refl _ _
    · rw [Function.iterate_succ_apply] at hj
      obtain ⟨i, hi⟩ := ih hj
      refine ⟨i + 1, ?_⟩
      rw [Function.iterate_succ_apply, Function.update_of_ne hx]; exact hi

/-! ### The union forest along an execution -/

open Classical in
/-- The union-forest update of a step from `C` to `C'`: if a root `a` got a parent, add the edge
`a → C'.mem a`. -/
noncomputable def linkUpd (C C' : Config (dsu E) (Ptr E) P (Loc E)) (U : E → E) : E → E :=
  if h : ∃ a, C.mem a = a ∧ C'.mem a ≠ a then Function.update U h.choose (C'.mem h.choose) else U

variable (K key) in
/-- The union forest after running `α` from `C`, starting from `U`. -/
noncomputable def ufFrom : Config (dsu E) (Ptr E) P (Loc E) → List (Label P (dsu E)) →
    (E → E) → (E → E)
  | _, [], U => U
  | C, ℓ :: β, U =>
    match (dsuImpl K key P).step C ℓ with
    | some C' => ufFrom C' β (linkUpd C C' U)
    | none => U

variable (K key) in
/-- The union forest after the execution `α`. -/
noncomputable def uf (α : List (Label P (dsu E))) : E → E :=
  ufFrom K key (dsuImpl K key P).initCfg α id

lemma ufFrom_append {C C₁ : Config (dsu E) (Ptr E) P (Loc E)} {α : List (Label P (dsu E))}
    (h : (dsuImpl K key P).runFrom C α = some C₁) (β : List (Label P (dsu E))) (U : E → E) :
    ufFrom K key C (α ++ β) U = ufFrom K key C₁ β (ufFrom K key C α U) := by
  induction α generalizing C U with
  | nil => simp only [Impl.runFrom_nil, Option.some.injEq] at h; subst h; rfl
  | cons ℓ α ih =>
    simp only [Impl.runFrom_cons] at h
    cases hs : (dsuImpl K key P).step C ℓ with
    | none => simp [hs] at h
    | some C' =>
      rw [hs] at h
      simp only [List.cons_append, ufFrom, hs]
      exact ih h _

lemma uf_append {α : List (Label P (dsu E))} {C C' : Config (dsu E) (Ptr E) P (Loc E)}
    (h : (dsuImpl K key P).run α = some C) {ℓ : Label P (dsu E)}
    (hs : (dsuImpl K key P).step C ℓ = some C') :
    uf K key (α ++ [ℓ]) = linkUpd C C' (uf K key α) := by
  unfold uf
  rw [ufFrom_append h]
  simp only [ufFrom, hs]

lemma linkUpd_of_link {C C' : Config (dsu E) (Ptr E) P (Loc E)} {U : E → E} {a b : E}
    (ha : C.mem a = a) (hab : b ≠ a) (hm : C'.mem = Function.update C.mem a b) :
    linkUpd C C' U = Function.update U a b := by
  have hex : ∃ a', C.mem a' = a' ∧ C'.mem a' ≠ a' := ⟨a, ha, by simp [hm, hab]⟩
  unfold linkUpd
  rw [dif_pos hex]
  have hc := hex.choose_spec
  have hm' := congrFun hm
  have hch : hex.choose = a := by
    by_contra hne
    apply hc.2
    rw [hm' hex.choose, Function.update_of_ne hne]; exact hc.1
  rw [hch, hm' a, Function.update_self]

lemma linkUpd_of_noroot {C C' : Config (dsu E) (Ptr E) P (Loc E)} {U : E → E}
    (h : ∀ a, C.mem a = a → C'.mem a = a) : linkUpd C C' U = U := by
  unfold linkUpd
  rw [dite_cond_eq_false (eq_false ?_)]
  rintro ⟨a, h1, h2⟩
  exact h2 (h a h1)

/-! ### Ghost invariant -/

/-- Ghost facts of a `Find` about the union forest: the `w` of a pending `Cas(u.parent, v, w)`
is an ancestor of `v` in the union forest. -/
def FG (U : E → E) : FS E → Prop
  | .cas _ v w _ => Reach U v w
  | _ => True

/-- Ghost facts of a process. -/
def LG (U : E → E) : Loc E → Prop
  | .fu _ fs _ => FG U fs
  | .fv _ _ fs => FG U fs
  | _ => True

/-- The union-forest invariant. -/
structure UInv (C : Config (dsu E) (Ptr E) P (Loc E)) (U : E → E) : Prop where
  good : Good key U
  reach : ∀ x, Reach U x (C.mem x)
  root : ∀ x, U x = x ↔ C.mem x = x
  ghost : ∀ p, LG U (C.loc p)

lemma FG.link {U : E → E} {u b : E} (hu : U u = u) {fs : FS E} (h : FG U fs) :
    FG (Function.update U u b) fs := by
  cases fs <;> first | trivial | exact Reach.link hu h

lemma LG.link {U : E → E} {u b : E} (hu : U u = u) {l : Loc E} (h : LG U l) :
    LG (Function.update U u b) l := by
  cases l <;> first | trivial | exact FG.link hu h

lemma FG_start (U : E → E) (v : E) : FG U (FS.start K v) := by cases K <;> trivial

/-- Classification of a `Find` step with the union forest. -/
lemma fRes_union {m : E → E} (hg : Good key m) {U : E → E} (hreach : ∀ x, Reach U x (m x))
    {s : E} {fs : FS E} (hf : FInv K key m s fs) (hG : FG U fs) :
    (∀ fs', (fRes K fs m).1 = .inl fs' → FG U fs') ∧
    ((fRes K fs m).2 = m ∨
      ∃ a w, m a ≠ a ∧ (fRes K fs m).2 = Function.update m a w ∧ Reach U (m a) w ∧
        w ≠ m a) := by
  cases fs with
  | tst u =>
    refine ⟨fun fs' h => ?_, Or.inl rfl⟩
    simp only [fRes, FS.next] at h; split_ifs at h <;> cases h; trivial
  | adv u =>
    refine ⟨fun fs' h => ?_, Or.inl rfl⟩
    simp only [fRes, FS.next, Sum.inl.injEq] at h; subst h; trivial
  | rdP u i =>
    refine ⟨fun fs' h => ?_, Or.inl rfl⟩
    simp only [fRes, FS.next, Sum.inl.injEq] at h; subst h; trivial
  | rdG u v i =>
    refine ⟨fun fs' h => ?_, Or.inl rfl⟩
    simp only [fRes, FS.next] at h; split_ifs at h <;> cases h
    exact hreach v
  | cas u v w i =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    refine ⟨fun fs' h => ?_, ?_⟩
    · simp only [fRes, FS.next] at h; split_ifs at h <;> cases h <;> trivial
    · have hres : (fRes K (.cas u v w i) m).2 = if m u = v then Function.update m u w else m :=
        rfl
      rw [hres]
      split_ifs with hmu
      · right
        refine ⟨u, w, ?_, rfl, ?_, ?_⟩
        rotate_left
        · rw [hmu]; exact hG
        · rw [hmu]; intro h; rw [h] at h5; omega
        intro hu; rw [hu] at hmu; subst hmu
        unfold same at h4 h3
        have hr : rootOf m w = u := by rw [h4, rootOf_of_fixed hu]
        have := key_le_rootOf hg w
        rw [hr] at this; omega
      · exact Or.inl rfl

lemma Reach.key_le {U : E → E} (hU : Good key U) {x y : E} (h : Reach U x y) : key x ≤ key y := by
  obtain ⟨j, rfl⟩ := h; exact key_le_iterate hU x j

/-- Classification of a step of a process with the union forest. -/
lemma tauRes_union (hkey : Function.Injective key) {m U : E → E} (hg : Good key m)
    (hreach : ∀ x, Reach U x (m x)) {o : DSUOp E} {l l' : Loc E} {m' : E → E}
    (hl : LocInv K key m (some o) l) (hG : LG U l) (h : tauRes K key l m = some (l', m')) :
    (m' = m ∧ LG U l') ∨
    (∃ a b, m a = a ∧ key a < key b ∧ rootOf m b ≠ a ∧ m' = Function.update m a b ∧
      l' = .done true) ∨
    (∃ a w, m a ≠ a ∧ m' = Function.update m a w ∧ Reach U (m a) w ∧ w ≠ m a ∧ LG U l') := by
  have hroot : ∀ {a b : E}, key a < key b → rootOf m b ≠ a := fun {a b} hk hr => by
    have := key_le_rootOf hg b; rw [hr] at this; omega
  cases l with
  | idle => exact hl.elim
  | done r => simp [tauRes, act] at h
  | fu b fs v =>
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hfs, hcase⟩ := fRes_union hg hreach hl.2.1 hG
    have hl' : LG U (contU K b v (fRes K fs m).1) := by
      cases hc : (fRes K fs m).1 with
      | inl fs' => exact hfs fs' hc
      | inr r => exact FG_start U v
    rcases hcase with h1 | ⟨a, w, h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, hl'⟩
    · exact Or.inr (Or.inr ⟨a, w, h1, h2, h3, h4, hl'⟩)
  | fv b u fs =>
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hfs, hcase⟩ := fRes_union hg hreach hl.2.2 hG
    have hl' : LG U (contV b u (fRes K fs m).1) := by
      cases hc : (fRes K fs m).1 with
      | inl fs' => exact hfs fs' hc
      | inr r => simp only [contV]; split_ifs <;> trivial
    rcases hcase with h1 | ⟨a, w, h1, h2, h3, h4⟩
    · exact Or.inl ⟨h1, hl'⟩
    · exact Or.inr (Or.inr ⟨a, w, h1, h2, h3, h4, hl'⟩)
  | chk u v =>
    simp only [tauRes, act, ptr_read, Function.update_eq_self, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    left; refine ⟨rfl, ?_⟩
    split_ifs
    · trivial
    · exact FG_start U u
  | lnk u v =>
    have hk : key u ≠ key v := fun h => hl.2.2.2 (hkey h)
    by_cases hlt : key u < key v
    · simp only [tauRes, act, hlt, ite_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hr : m u = u
      · simp only [hr, ite_true]
        exact Or.inr (Or.inl ⟨u, v, hr, hlt, hroot hlt, rfl, by simp⟩)
      · simp only [hr, ite_false, Function.update_eq_self]
        exact Or.inl ⟨by simp, FG_start U u⟩
    · have hlt' : key v < key u := by omega
      simp only [tauRes, act, hlt, ite_false, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hr : m v = v
      · simp only [hr, ite_true]
        exact Or.inr (Or.inl ⟨v, u, hr, hlt', hroot hlt', rfl, by simp⟩)
      · simp only [hr, ite_false, Function.update_eq_self]
        exact Or.inl ⟨by simp, FG_start U u⟩

lemma uinv_init : UInv (key := key) ((dsuImpl K key P).initCfg) id :=
  ⟨fun _ => Or.inl rfl, fun _ => Reach.refl _ _, fun _ => Iff.rfl, fun _ => trivial⟩

/-- The three kinds of steps, with the corresponding change of the union forest. -/
def UStep (key : E → ℕ) (m m' U U' : E → E) : Prop :=
  (m' = m ∧ U' = U) ∨
  (∃ a b, m a = a ∧ key a < key b ∧ rootOf m b ≠ a ∧ m' = Function.update m a b ∧
    U' = Function.update U a b) ∨
  (∃ a w, m a ≠ a ∧ m' = Function.update m a w ∧ Reach U (m a) w ∧ w ≠ m a ∧ U' = U)

theorem uinv_step (hkey : Function.Injective key) {C C' : Config (dsu E) (Ptr E) P (Loc E)}
    {U : E → E} {ℓ : Label P (dsu E)} (hI : LInv K key C) (hU : UInv (key := key) C U)
    (h : (dsuImpl K key P).step C ℓ = some C') :
    UInv (key := key) C' (linkUpd C C' U) ∧ UStep key C.mem C'.mem U (linkUpd C C' U) := by
  have hnoroot : C'.mem = C.mem → linkUpd C C' U = U := fun hm =>
    linkUpd_of_noroot (fun a ha => by rw [hm]; exact ha)
  cases ℓ with
  | inv p o =>
    obtain ⟨-, -, -, hloc, hmem⟩ := Impl.step_inv h
    rw [hnoroot hmem]
    refine ⟨⟨hU.good, fun x => by rw [hmem]; exact hU.reach x, fun x => by rw [hmem]; exact hU.root x,
      fun q => ?_⟩, Or.inl ⟨hmem, rfl⟩⟩
    rw [hloc]
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      cases o <;> exact FG_start U _
    · rw [Function.update_of_ne hq]; exact hU.ghost q
  | ret p r =>
    obtain ⟨-, -, hmem, l, hact, hloc⟩ := Impl.step_ret h
    rw [hnoroot hmem]
    refine ⟨⟨hU.good, fun x => by rw [hmem]; exact hU.reach x, fun x => by rw [hmem]; exact hU.root x,
      fun q => ?_⟩, Or.inl ⟨hmem, rfl⟩⟩
    rw [hloc]
    by_cases hq : q = p
    · subst hq; simp only [Function.update_self]
      have hact' : act K key (C.loc q) = .ret r l := hact
      rcases act_ret_cases hact' with h1 | h1 <;> rw [h1] at hact' <;> simp only [act] at hact' <;>
        cases hact' <;> trivial
    · rw [Function.update_of_ne hq]; exact hU.ghost q
  | tau p =>
    obtain ⟨hp, hres, hpend, hother⟩ := step_tau_tauRes h
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
    have hl := hI.loc p
    rw [ho] at hl
    rcases tauRes_union hkey hI.good hU.reach hl (hU.ghost p) hres with
      ⟨hm, hG⟩ | ⟨a, b, ha, hab, hb, hm, hdone⟩ | ⟨a, w, ha, hm, hw, hwa, hG⟩
    · rw [hnoroot hm]
      refine ⟨⟨hU.good, fun x => by rw [hm]; exact hU.reach x, fun x => by rw [hm]; exact hU.root x,
        fun q => ?_⟩, Or.inl ⟨hm, rfl⟩⟩
      by_cases hq : q = p
      · subst hq; exact hG
      · rw [hother q hq]; exact hU.ghost q
    · have hba : b ≠ a := fun h' => by rw [h'] at hab; omega
      have hUa : U a = a := (hU.root a).2 ha
      rw [linkUpd_of_link ha hba hm]
      have hm' := congrFun hm
      refine ⟨⟨good_update hU.good hab, fun x => ?_, fun x => ?_, fun q => ?_⟩,
        Or.inr (Or.inl ⟨a, b, ha, hab, hb, hm, rfl⟩)⟩
      · by_cases hx : x = a
        · subst hx; rw [hm' x, Function.update_self]
          exact ⟨1, by simp⟩
        · rw [hm' x, Function.update_of_ne hx]; exact Reach.link hUa (hU.reach x)
      · by_cases hx : x = a
        · subst hx; rw [hm' x, Function.update_self, Function.update_self]
        · rw [hm' x, Function.update_of_ne hx, Function.update_of_ne hx]; exact hU.root x
      · by_cases hq : q = p
        · subst hq
          rw [hdone]; trivial
        · rw [hother q hq]; exact LG.link hUa (hU.ghost q)
    · have hUma : Reach U a (C.mem a) := hU.reach a
      have hka : key a < key (C.mem a) := (hI.good a).resolve_left ha
      have hwa' : w ≠ a := fun h' => by
        have := hw.key_le hU.good; rw [h'] at this; omega
      have hm' := congrFun hm
      have hno : linkUpd C C' U = U := linkUpd_of_noroot (fun x hx => by
        by_cases hxa : x = a
        · subst hxa; exact absurd hx ha
        · rw [hm' x, Function.update_of_ne hxa]; exact hx)
      rw [hno]
      refine ⟨⟨hU.good, fun x => ?_, fun x => ?_, fun q => ?_⟩,
        Or.inr (Or.inr ⟨a, w, ha, hm, hw, hwa, rfl⟩)⟩
      · by_cases hx : x = a
        · subst hx; rw [hm' x, Function.update_self]; exact hUma.trans hw
        · rw [hm' x, Function.update_of_ne hx]; exact hU.reach x
      · by_cases hx : x = a
        · subst hx; rw [hm' x, Function.update_self]
          exact ⟨fun h' => absurd ((hU.root x).1 h') ha, fun h' => absurd h' hwa'⟩
        · rw [hm' x, Function.update_of_ne hx]; exact hU.root x
      · by_cases hq : q = p
        · subst hq; exact hG
        · rw [hother q hq]; exact hU.ghost q

theorem uinv_of_run (hkey : Function.Injective key) {α : List (Label P (dsu E))}
    {C : Config (dsu E) (Ptr E) P (Loc E)} (h : (dsuImpl K key P).run α = some C) :
    UInv (key := key) C (uf K key α) := by
  refine Impl.run_induction (Q := fun α C => UInv (key := key) C (uf K key α)) uinv_init ?_ h
  intro α C₀ ℓ C hα ih h
  rw [uf_append hα h]
  exact (uinv_step hkey (linv_of_run hkey hα) ih h).1

/-- **Lemma 3.1 (with the union forest).** After every execution `α`, the union forest
`U = uf α` (the links done so far) has the same roots as the parent forest, ids increase along
its edges, and the parent of every node is an ancestor of the node in `U`. Every step either
leaves the parent pointers (and `U`) unchanged, or links a root `a` below a node `b` with a larger
id in another tree (and `U` gets the edge `a → b`), or replaces the parent of a non-root `a` by a
proper ancestor in `U` of its old parent (and `U` is unchanged). -/
theorem lemma_3_1_union (hkey : Function.Injective key) {α : List (Label P (dsu E))}
    {C : Config (dsu E) (Ptr E) P (Loc E)} (h : (dsuImpl K key P).run α = some C) :
    Good key (uf K key α) ∧ (∀ x, Reach (uf K key α) x (C.mem x)) ∧
    (∀ x, uf K key α x = x ↔ C.mem x = x) ∧
    ∀ ℓ C', (dsuImpl K key P).step C ℓ = some C' →
      UStep key C.mem C'.mem (uf K key α) (uf K key (α ++ [ℓ])) := by
  have hU := uinv_of_run hkey h
  refine ⟨hU.good, hU.reach, hU.root, fun ℓ C' hs => ?_⟩
  rw [uf_append h hs]
  exact (uinv_step hkey (linv_of_run hkey h) hU hs).2

end Podc.ConcurrentDSU
