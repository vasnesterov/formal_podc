import Papers.PODC2017.SeeingIsBelieving.Adya
import Podc.Foundations.Order.TopologicalSort

/-!
# Auxiliary lemmas: version orders, executions from acyclic relations

* `VersionOrder.transGen_ww_of_lt`, `VersionOrder.exists_isNext`, `VersionOrder.exists_isFirst`:
  in a finite version order, the write-dependency edges (immediate successors) generate the
  version order, and immediate successors / first versions exist.
* `Execution.vo`: the version order induced by an execution (order of installation in `e`).
* `Execution.exists_of_acyclic`: a topological sort of an acyclic relation on the committed
  transactions is an execution.
-/

set_option linter.unusedSectionVars false

namespace Podc.SeeingIsBelieving

open Relation

variable {K ι : Type*} [DecidableEq K] [DecidableEq ι] {H : TxnSet K ι}

namespace VersionOrder

variable (vo : VersionOrder H)

/-- The committed transactions installing versions of `k` strictly between `X`'s and `Y`'s. -/
noncomputable def between (k : K) (X Y : ι) : Finset ι := by
  classical exact H.committed.filter (fun Z => vo.lt k X Z ∧ vo.lt k Z Y)

/-- The committed transactions installing versions of `k` before `Y`'s. -/
noncomputable def below (k : K) (Y : ι) : Finset ι := by
  classical exact H.committed.filter (fun Z => vo.lt k Z Y)

lemma mem_between {k : K} {X Y Z : ι} :
    Z ∈ vo.between k X Y ↔ Z ∈ H.committed ∧ vo.lt k X Z ∧ vo.lt k Z Y := by
  classical simp [between]

lemma mem_below {k : K} {Y Z : ι} : Z ∈ vo.below k Y ↔ Z ∈ H.committed ∧ vo.lt k Z Y := by
  classical simp [below]

private lemma chain_aux (k : K) (n : ℕ) : ∀ X Y, (vo.between k X Y).card = n → vo.lt k X Y →
    TransGen vo.WW X Y ∧ ∃ N, vo.IsNext k X N ∧ (N = Y ∨ vo.lt k N Y) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X Y hn hXY
  by_cases hZ : ∃ Z, vo.lt k X Z ∧ vo.lt k Z Y
  · obtain ⟨Z, hXZ, hZY⟩ := hZ
    have hZc := (vo.dom hXZ).2.1
    have h1 : (vo.between k X Z).card < n := by
      rw [← hn]
      refine Finset.card_lt_card ⟨fun W hW => ?_, fun hsub => ?_⟩
      · rw [mem_between] at hW ⊢
        exact ⟨hW.1, hW.2.1, vo.trans hW.2.2 hZY⟩
      · have := (vo.mem_between.1 (hsub (vo.mem_between.2 ⟨hZc, hXZ, hZY⟩))).2.2
        exact vo.irrefl k Z this
    have h2 : (vo.between k Z Y).card < n := by
      rw [← hn]
      refine Finset.card_lt_card ⟨fun W hW => ?_, fun hsub => ?_⟩
      · rw [mem_between] at hW ⊢
        exact ⟨hW.1, vo.trans hXZ hW.2.1, hW.2.2⟩
      · have := (vo.mem_between.1 (hsub (vo.mem_between.2 ⟨hZc, hXZ, hZY⟩))).2.1
        exact vo.irrefl k Z this
    obtain ⟨hXZ', N, hN, hNZ⟩ := ih _ h1 X Z rfl hXZ
    obtain ⟨hZY', -⟩ := ih _ h2 Z Y rfl hZY
    refine ⟨hXZ'.trans hZY', N, hN, Or.inr ?_⟩
    rcases hNZ with rfl | hNZ
    · exact hZY
    · exact vo.trans hNZ hZY
  · have hnext : vo.IsNext k X Y := ⟨hXY, fun Z hZ' => hZ ⟨Z, hZ'⟩⟩
    exact ⟨TransGen.single ⟨k, hnext⟩, Y, hnext, Or.inl rfl⟩

/-- The write-dependency edges generate the version order. -/
lemma transGen_ww_of_lt {k : K} {X Y : ι} (h : vo.lt k X Y) : TransGen vo.WW X Y :=
  (vo.chain_aux k _ X Y rfl h).1

/-- Every version but the last has an immediate successor. -/
lemma exists_isNext {k : K} {X Y : ι} (h : vo.lt k X Y) :
    ∃ N, vo.IsNext k X N ∧ (N = Y ∨ vo.lt k N Y) :=
  (vo.chain_aux k _ X Y rfl h).2

private lemma first_aux (k : K) (n : ℕ) : ∀ Y, (vo.below k Y).card = n → Y ∈ H.committed →
    H.Writes Y k → ∃ F, vo.IsFirst k F ∧ (F = Y ∨ vo.lt k F Y) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y hn hY hwY
  by_cases hZ : ∃ Z, vo.lt k Z Y
  · obtain ⟨Z, hZY⟩ := hZ
    obtain ⟨hZc, -, hwZ, -⟩ := vo.dom hZY
    have h1 : (vo.below k Z).card < n := by
      rw [← hn]
      refine Finset.card_lt_card ⟨fun W hW => ?_, fun hsub => ?_⟩
      · rw [mem_below] at hW ⊢
        exact ⟨hW.1, vo.trans hW.2 hZY⟩
      · exact vo.irrefl k Z (vo.mem_below.1 (hsub (vo.mem_below.2 ⟨hZc, hZY⟩))).2
    obtain ⟨F, hF, hFZ⟩ := ih _ h1 Z rfl hZc hwZ
    refine ⟨F, hF, Or.inr ?_⟩
    rcases hFZ with rfl | hFZ
    · exact hZY
    · exact vo.trans hFZ hZY
  · exact ⟨Y, ⟨hY, hwY, fun Z hZY => hZ ⟨Z, hZY⟩⟩, Or.inl rfl⟩

/-- Every key written by a committed transaction has a first committed version. -/
lemma exists_isFirst {k : K} {Y : ι} (hY : Y ∈ H.committed) (hw : H.Writes Y k) :
    ∃ F, vo.IsFirst k F ∧ (F = Y ∨ vo.lt k F Y) :=
  vo.first_aux k _ Y rfl hY hw

/-- If a version `v` of `k` precedes the version installed by `Z` (`v = none` is the initial
version), then the version following `v` is installed by some `N` with a write-dependency
path from `N` to `Z`. -/
lemma exists_isNextAfter {k : K} {v : Option ι} {Z : ι} (hZ : Z ∈ H.committed)
    (hw : H.Writes Z k) (hv : v = none ∨ ∃ V, v = some V ∧ vo.lt k V Z) :
    ∃ N, vo.IsNextAfter k v N ∧ ReflTransGen vo.WW N Z := by
  rcases hv with rfl | ⟨V, rfl, hVZ⟩
  · obtain ⟨F, hF, hFZ⟩ := vo.exists_isFirst hZ hw
    refine ⟨F, hF, ?_⟩
    rcases hFZ with rfl | hFZ
    · exact ReflTransGen.refl
    · exact (vo.transGen_ww_of_lt hFZ).to_reflTransGen
  · obtain ⟨N, hN, hNZ⟩ := vo.exists_isNext hVZ
    refine ⟨N, hN, ?_⟩
    rcases hNZ with rfl | hNZ
    · exact ReflTransGen.refl
    · exact (vo.transGen_ww_of_lt hNZ).to_reflTransGen

lemma isNextAfter_committed {k : K} {v : Option ι} {N : ι} (h : vo.IsNextAfter k v N) :
    N ∈ H.committed ∧ H.Writes N k := by
  cases v with
  | none => exact ⟨h.1, h.2.1⟩
  | some V => exact ⟨(vo.dom h.1).2.1, (vo.dom h.1).2.2.2⟩

lemma ww_committed {X Y : ι} (h : vo.WW X Y) : X ∈ H.committed ∧ Y ∈ H.committed := by
  obtain ⟨k, hk, -⟩ := h
  exact ⟨(vo.dom hk).1, (vo.dom hk).2.1⟩

lemma dep_committed {X Y : ι} (h : vo.Dep X Y) : X ∈ H.committed ∧ Y ∈ H.committed := by
  rcases h with h | h
  · exact vo.ww_committed h
  · exact ⟨h.1, h.2.1⟩

end VersionOrder

namespace Execution

variable (e : Execution H)

/-- The version order induced by an execution: versions are ordered as they are installed. -/
def vo : VersionOrder H where
  lt k X Y := X ∈ H.committed ∧ Y ∈ H.committed ∧ H.Writes X k ∧ H.Writes Y k ∧ e.idx X < e.idx Y
  dom h := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  irrefl _ _ h := lt_irrefl _ h.2.2.2.2
  trans h₁ h₂ := ⟨h₁.1, h₂.2.1, h₁.2.2.1, h₂.2.2.2.1, h₁.2.2.2.2.trans h₂.2.2.2.2⟩
  total {_ X Y} hX hY hwX hwY hne := by
    rcases lt_trichotomy (e.idx X) (e.idx Y) with h | h | h
    · exact Or.inl ⟨hX, hY, hwX, hwY, h⟩
    · exact absurd (e.idx_inj hX hY h) hne
    · exact Or.inr ⟨hY, hX, hwY, hwX, h⟩

lemma vo_lt_iff {k : K} {X Y : ι} : e.vo.lt k X Y ↔
    X ∈ H.committed ∧ Y ∈ H.committed ∧ H.Writes X k ∧ H.Writes Y k ∧ e.idx X < e.idx Y :=
  Iff.rfl

lemma vo_ww_idx {X Y : ι} (h : e.vo.WW X Y) : e.idx X < e.idx Y := by
  obtain ⟨k, hk, -⟩ := h
  exact hk.2.2.2.2

/-- If `T` reads version `v` of `k` from state `s_i`, then the transaction installing the next
version of `k` comes at position `≥ i` in `e`. -/
lemma le_idx_of_isNextAfter {k : K} {v : Option ι} {N : ι} {i : ℕ} (hs : e.state i k = v)
    (hN : e.vo.IsNextAfter k v N) : i ≤ e.idx N := by
  obtain ⟨hNc, hwN⟩ := e.vo.isNextAfter_committed hN
  cases v with
  | none => exact e.state_eq_none_iff.1 hs N hNc hwN
  | some V =>
    obtain ⟨-, -, -, hmax⟩ := e.state_eq_some_iff.1 hs
    exact hmax N hNc hwN hN.1.2.2.2.2

/-- An execution from an order: a topological sort of an acyclic relation on the committed
transactions. -/
lemma exists_of_acyclic (r : ι → ι → Prop)
    (h : ∀ a, ¬ TransGen (H.committed.restrictRel r) a a) :
    ∃ e : Execution H, ∀ a b, a ∈ H.committed → b ∈ H.committed → r a b → e.idx a < e.idx b := by
  obtain ⟨l, hnd, hmem, hl⟩ := H.committed.exists_topologicalSort r h
  exact ⟨⟨l, hnd, hmem⟩, hl⟩

end Execution

/-- A relation all of whose edges join committed transactions is its own restriction. -/
lemma transGen_restrict_of {r : ι → ι → Prop}
    (hr : ∀ a b, r a b → a ∈ H.committed ∧ b ∈ H.committed) {a b : ι} :
    TransGen (H.committed.restrictRel r) a b ↔ TransGen r a b := by
  constructor
  · intro h
    induction h with
    | single h => exact TransGen.single h.2.2
    | tail _ h ih => exact ih.tail h.2.2
  · intro h
    induction h with
    | single h => exact TransGen.single ⟨(hr _ _ h).1, (hr _ _ h).2, h⟩
    | tail _ h ih => exact ih.tail ⟨(hr _ _ h).1, (hr _ _ h).2, h⟩

/-- Edges that go forward in a numbering admit no cycle. -/
lemma lt_of_transGen {β : Type*} [Preorder β] {r : ι → ι → Prop} (f : ι → β)
    (hr : ∀ a b, r a b → f a < f b) {a b : ι}
    (h : TransGen r a b) : f a < f b := by
  induction h with
  | single h => exact hr _ _ h
  | tail _ h ih => exact ih.trans (hr _ _ h)

lemma transGen_mono {p q : ι → ι → Prop} (hpq : ∀ a b, p a b → q a b) {a b : ι}
    (h : TransGen p a b) : TransGen q a b := by
  induction h with
  | single h => exact TransGen.single (hpq _ _ h)
  | tail _ h ih => exact ih.tail (hpq _ _ h)

lemma reflTransGen_mono {p q : ι → ι → Prop} (hpq : ∀ a b, p a b → q a b) {a b : ι}
    (h : ReflTransGen p a b) : ReflTransGen q a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ h ih => exact ih.tail (hpq _ _ h)

/-- Edges that go forward in a numbering go forward along paths. -/
lemma le_of_reflTransGen {β : Type*} [Preorder β] {r : ι → ι → Prop} (f : ι → β)
    (hr : ∀ a b, r a b → f a < f b) {a b : ι} (h : ReflTransGen r a b) : f a ≤ f b := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact ih.trans (hr _ _ h).le

/-- A cycle in `p ∪ q` either avoids `q` or uses some `q`-edge. -/
lemma transGen_or_split {p q : ι → ι → Prop} {a b : ι}
    (h : TransGen (fun x y => p x y ∨ q x y) a b) :
    TransGen p a b ∨ ∃ x y, q x y ∧ ReflTransGen (fun x y => p x y ∨ q x y) a x ∧
      ReflTransGen (fun x y => p x y ∨ q x y) y b := by
  induction h with
  | single h =>
    rcases h with h | h
    · exact Or.inl (TransGen.single h)
    · exact Or.inr ⟨_, _, h, ReflTransGen.refl, ReflTransGen.refl⟩
  | tail hab hbc ih =>
    rcases ih with ih | ⟨x, y, hxy, hax, hyb⟩
    · rcases hbc with h | h
      · exact Or.inl (ih.tail h)
      · refine Or.inr ⟨_, _, h, ?_, ReflTransGen.refl⟩
        exact (transGen_mono (fun _ _ h => Or.inl h) ih).to_reflTransGen
    · exact Or.inr ⟨x, y, hxy, hax, hyb.tail hbc⟩

namespace Execution

variable (e : Execution H)

lemma readState_read {T : ι} {m i : ℕ} {k : K} {v : Option ι}
    (h : (H.ops T)[m]? = some (.read k v)) :
    e.ReadState T m i ↔ i ≤ e.idx T ∧
      (e.state i k = v ∨ (v = some T ∧ Op.write k ∈ (H.ops T).take m)) := by
  simp [ReadState, h]

lemma readState_write {T : ι} {m i : ℕ} {k : K} (h : (H.ops T)[m]? = some (.write k)) :
    e.ReadState T m i ↔ i ≤ e.idx T := by
  simp [ReadState, h]

/-- If `T` reads the value of another transaction `X` from a read state `s_i`, then `X` is
committed and comes before position `i`. -/
lemma lt_of_readState_ne {T X : ι} {m i : ℕ} {k : K}
    (h : (H.ops T)[m]? = some (.read k (some X))) (hXT : X ≠ T) (hr : e.ReadState T m i) :
    X ∈ H.committed ∧ e.idx X < i := by
  rcases (e.readState_read h).1 hr with ⟨-, hs | ⟨hX, -⟩⟩
  · obtain ⟨hX, -, hlt, -⟩ := e.state_eq_some_iff.1 hs
    exact ⟨hX, hlt⟩
  · exact absurd (Option.some_inj.1 hX) hXT

/-- No aborted reads when every operation has a read state. -/
lemma not_G1a (hpre : ∀ T ∈ H.committed, e.PreRead T) : ¬ H.G1a := by
  rintro ⟨T, hT, k, X, hmem, hX⟩
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 hmem
  have hml : m < (H.ops T).length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; cases hm
  obtain ⟨i, hi⟩ := hpre T hT m hml
  by_cases hXT : X = T
  · exact hX (hXT ▸ hT)
  · exact hX (e.lt_of_readState_ne hm hXT hi).1

/-- **Reads see the right version.** Let `vo` be a version order consistent with `e`. If the
writer of `v` comes before position `j`, and no transaction installing a version of `k` at or
after the one following `v` comes before position `j`, then `s_j` maps `k` to `v`. -/
lemma state_eq_of_no_next (vo : VersionOrder H) {k : K} {v : Option ι} {j : ℕ}
    (hvo : ∀ Z V, vo.lt k Z V → e.idx Z < e.idx V)
    (hV : ∀ V, v = some V → V ∈ H.committed ∧ H.Writes V k ∧ e.idx V < j)
    (hN : ∀ N Z, vo.IsNextAfter k v N → ReflTransGen vo.WW N Z → Z ∈ H.committed →
      H.Writes Z k → e.idx Z < j → False) :
    e.state j k = v := by
  -- every writer before `j` installs a version not after `v`
  have key : ∀ Z ∈ H.committed, H.Writes Z k → e.idx Z < j →
      ∃ V, v = some V ∧ (Z = V ∨ vo.lt k Z V) := by
    intro Z hZ hwZ hZj
    cases v with
    | none =>
      obtain ⟨N, hN', hNZ⟩ := vo.exists_isNextAfter hZ hwZ (Or.inl rfl)
      exact (hN N Z hN' hNZ hZ hwZ hZj).elim
    | some V =>
      obtain ⟨hVc, hwV, -⟩ := hV V rfl
      refine ⟨V, rfl, ?_⟩
      by_cases hZV : Z = V
      · exact Or.inl hZV
      rcases vo.total hZ hVc hwZ hwV hZV with h | h
      · exact Or.inr h
      · obtain ⟨N, hN', hNZ⟩ := vo.exists_isNextAfter hZ hwZ (Or.inr ⟨V, rfl, h⟩)
        exact (hN N Z hN' hNZ hZ hwZ hZj).elim
  cases v with
  | none =>
    rw [e.state_eq_none_iff]
    intro Z hZ hwZ
    by_contra hc
    obtain ⟨V, hV', -⟩ := key Z hZ hwZ (by omega)
    cases hV'
  | some V =>
    obtain ⟨hVc, hwV, hVj⟩ := hV V rfl
    refine e.state_eq_some_iff.2 ⟨hVc, hwV, hVj, fun Z hZ hwZ hlt => ?_⟩
    by_contra hc
    obtain ⟨V', hV', hZV⟩ := key Z hZ hwZ (by omega)
    cases hV'
    rcases hZV with rfl | hZV
    · omega
    · have := hvo _ _ hZV; omega

end Execution

/-- From a membership in the operation list to an index. -/
lemma exists_getElem?_of_mem {l : List (Op K ι)} {o : Op K ι} (h : o ∈ l) :
    ∃ m < l.length, l[m]? = some o := by
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.1 h
  refine ⟨m, ?_, hm⟩
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at hm; cases hm

end Podc.SeeingIsBelieving
