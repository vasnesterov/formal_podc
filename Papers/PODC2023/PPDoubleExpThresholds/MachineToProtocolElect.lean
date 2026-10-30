import Papers.PODC2023.PPDoubleExpThresholds.MachineToProtocolClean

/-!
# Leader election (Lemma 15)

Counting agents per pointer level we define invariants of all configurations reachable from a
configuration with at least `|F|` agents in the initial state `(X_1)^{v_1}_none` (plus arbitrary
other agents):

* `J`: for every `l ≤ |F|` at least `l` agents belong to the pointers of level `< l`
  (the prefix-sum invariant of the paper's proof of Lemma 15);
* `K`: an empty level `l ∈ [1, |F| - 1)` has `≥ |F|` agents below it (levels `< |F| - 1` never
  become empty again once occupied);
* `Fr`: if there is no `IP` agent, then the agents of every *settled* level `l` (exactly `l + 1`
  agents at levels `≤ l`) are *fresh*: `X^{v_X}_none` (for `CF`: any value).

They are preserved by all transitions (`inv_step`). The key consequence (`elected_of_step`): the
first configuration in which every pointer has exactly one agent is `π(C)` for an *initial*
configuration `C` of the machine. This is the precise form of the claim "at the moment this happens,
these agents are in `X^v_none`, where `v` is the initial value" in the proof of Lemma 15.
-/

set_option linter.unusedSectionVars false

namespace Podc.PPDoubleExpThresholds

open Cslib Cslib.PopulationProtocol Cslib.TransitionSystem M2P

namespace Machine

variable {Q F : Type*} [Fintype Q] [Fintype F] [DecidableEq Q] [DecidableEq F]
variable (A : Machine Q F)

/-! ### Counting -/

/-- The level of an agent (`|F|` for register agents). -/
noncomputable def lvlOf (s : St Q F) : ℕ :=
  match s.owner with
  | some X => A.lvl X
  | none => Fintype.card F

/-- The number of agents of pointer `X`. -/
def cnt (c : Multiset (St Q F)) (X : F) : ℕ := c.countP (fun s => s.owner = some X)

/-- The number of agents of the pointers of level `< l`. -/
noncomputable def below (c : Multiset (St Q F)) (l : ℕ) : ℕ := c.countP (fun s => A.lvlOf s < l)

/-- Every pointer has exactly one agent. -/
def Elected (c : Multiset (St Q F)) : Prop := ∀ X, cnt c X = 1

/-- The prefix-sum invariant. -/
def InvJ (c : Multiset (St Q F)) : Prop := ∀ l ≤ Fintype.card F, l ≤ A.below c l

/-- Empty levels have many agents below them. -/
def InvK (c : Multiset (St Q F)) : Prop :=
  ∀ X, X ≠ A.IP → 0 < A.lvl X → cnt c X = 0 → Fintype.card F ≤ A.below c (A.lvl X)

/-- A fresh agent of `X`: `X^{v_X}_none` (for `CF` with any value). -/
def Fresh (X : F) (s : St Q F) : Prop :=
  s = .ptr X (A.v0 X) .none ∨ (X = A.CF ∧ ∃ b, s = .ptr A.CF (.bool b) .none)

/-- Without `IP` agents, settled levels consist of fresh agents. -/
def InvFr (c : Multiset (St Q F)) : Prop :=
  cnt c A.IP = 0 → ∀ X, X ≠ A.IP → A.below c (A.lvl X + 1) = A.lvl X + 1 →
    ∀ s ∈ c, s.owner = some X → A.Fresh X s

/-- The election invariant. -/
def Inv (c : Multiset (St Q F)) : Prop := A.InvJ c ∧ A.InvK c ∧ A.InvFr c

theorem lvlOf_eq_iff {s : St Q F} {X : F} : A.lvlOf s = A.lvl X ↔ s.owner = some X := by
  unfold lvlOf
  cases h : s.owner with
  | none => have := A.lvl_lt X; simp; omega
  | some Y => simp [A.lvl_eq_iff]

theorem lvlOf_of_owner {s : St Q F} {X : F} (h : s.owner = some X) : A.lvlOf s = A.lvl X :=
  (A.lvlOf_eq_iff).2 h

@[simp] theorem lvlOf_reg (q : Q) : A.lvlOf (.reg q : St Q F) = Fintype.card F := rfl
@[simp] theorem lvlOf_ptr (X : F) (v : Val Q) (s : Stage) :
    A.lvlOf (.ptr X v s : St Q F) = A.lvl X := rfl
@[simp] theorem lvlOf_map (X : F) (i : ℕ) : A.lvlOf (.map X i : St Q F) = A.lvl X := rfl

theorem below_succ (c : Multiset (St Q F)) {l : ℕ} (hl : l < Fintype.card F) :
    A.below c (l + 1) = A.below c l + cnt c (A.ptrAt l) := by
  unfold below cnt
  induction c using Multiset.induction_on with
  | empty => simp
  | cons s c ih =>
    simp only [Multiset.countP_cons, ih]
    have h1 : A.lvlOf s = l ↔ s.owner = some (A.ptrAt l) := by
      rw [← A.lvlOf_eq_iff, A.lvl_ptrAt hl]
    rcases lt_trichotomy (A.lvlOf s) l with h | h | h
    · have h' : ¬ s.owner = some (A.ptrAt l) := fun h' => by have := h1.2 h'; omega
      simp [h, h', show A.lvlOf s < l + 1 by omega]; omega
    · have h' := h1.1 h
      simp [h, h']; omega
    · have h' : ¬ s.owner = some (A.ptrAt l) := fun h' => by have := h1.2 h'; omega
      simp [h', show ¬ A.lvlOf s < l + 1 by omega, show ¬ A.lvlOf s < l by omega]

theorem below_lvl_succ (c : Multiset (St Q F)) (X : F) :
    A.below c (A.lvl X + 1) = A.below c (A.lvl X) + cnt c X := by
  rw [A.below_succ c (A.lvl_lt X), A.ptrAt_lvl]

theorem below_zero (c : Multiset (St Q F)) : A.below c 0 = 0 := by
  simp [below]

theorem below_card (c : Multiset (St Q F)) : A.below c (Fintype.card F) = ∑ X, cnt c X := by
  have : ∀ l ≤ Fintype.card F, A.below c l = ∑ X ∈ Finset.univ.filter (fun X => A.lvl X < l),
      cnt c X := by
    intro l hl
    induction l with
    | zero => simp [below_zero]
    | succ l ih =>
      rw [A.below_succ c (by omega), ih (by omega)]
      have : Finset.univ.filter (fun X => A.lvl X < l + 1) =
          insert (A.ptrAt l) (Finset.univ.filter (fun X => A.lvl X < l)) := by
        ext X
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro h
          rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
          · exact .inr h
          · left; rw [← h, A.ptrAt_lvl]
        · rintro (rfl | h)
          · rw [A.lvl_ptrAt (by omega)]; omega
          · omega
      rw [this, Finset.sum_insert (by simp [A.lvl_ptrAt (show l < _ by omega)]), add_comm]
  rw [this _ le_rfl, Finset.filter_true_of_mem (fun X _ => A.lvl_lt X)]

theorem cnt_le_card (c : Multiset (St Q F)) (X : F) : cnt c X ≤ Multiset.card c :=
  Multiset.countP_le_card _ _

/-! ### Counting along transitions -/

theorem fires_countP {t : Transition (St Q F)} {c c' : Multiset (St Q F)} (hf : t.Fires c c')
    (p : St Q F → Prop) [DecidablePred p] :
    c'.countP p + ((if p t.p then 1 else 0) + (if p t.q then 1 else 0)) =
      c.countP p + ((if p t.p' then 1 else 0) + (if p t.q' then 1 else 0)) := by
  have := congrArg (Multiset.countP p) (fires_iff_add.1 hf).2
  simp only [Multiset.countP_add, Transition.pre, Transition.post, Multiset.insert_eq_cons,
    ← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero] at this
  omega

theorem two_le_countP {c : Multiset (St Q F)} {p : St Q F → Prop} [DecidablePred p]
    {a b : St Q F} (hab : ({a, b} : Multiset (St Q F)) ≤ c) (ha : p a) (hb : p b) :
    2 ≤ c.countP p := by
  have := Multiset.countP_le_of_le p hab
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.countP_cons,
    Multiset.countP_zero, ha, hb, if_true] at this
  omega

theorem pair_le_of_ne {c : Multiset (St Q F)} {a b : St Q F} (hab : a ≠ b) (ha : a ∈ c)
    (hb : b ∈ c) : ({a, b} : Multiset (St Q F)) ≤ c := by
  rw [Multiset.insert_eq_cons, ← Multiset.cons_erase ha, Multiset.cons_le_cons_iff]
  exact Multiset.singleton_le.2 ((Multiset.mem_erase_of_ne (Ne.symm hab)).2 hb)

theorem exists_pair_of_two_le {c : Multiset (St Q F)} {p : St Q F → Prop} [DecidablePred p]
    (h : 2 ≤ c.countP p) : ∃ a b, p a ∧ p b ∧ ({a, b} : Multiset (St Q F)) ≤ c := by
  rw [Multiset.countP_eq_card_filter] at h
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (show 0 < Multiset.card (c.filter p) by omega)
  have h2 : 0 < Multiset.card ((c.filter p).erase a) := by
    simp only [Multiset.card_erase_of_mem ha, Nat.pred_eq_sub_one]; omega
  obtain ⟨b, hb⟩ := Multiset.card_pos_iff_exists_mem.1 h2
  have hle : ({a, b} : Multiset (St Q F)) ≤ c.filter p := by
    rw [Multiset.insert_eq_cons, ← Multiset.cons_erase ha, Multiset.cons_le_cons_iff]
    exact Multiset.singleton_le.2 hb
  refine ⟨a, b, (Multiset.mem_filter.1 ha).2,
    (Multiset.mem_filter.1 (Multiset.mem_of_mem_erase hb)).2, hle.trans (Multiset.filter_le p c)⟩

theorem eq_of_cnt_le_one {c : Multiset (St Q F)} {X : F} (h : cnt c X ≤ 1) {a b : St Q F}
    (ha : a ∈ c) (hb : b ∈ c) (hao : a.owner = some X) (hbo : b.owner = some X) : a = b := by
  by_contra hab
  have := two_le_countP (p := fun s => s.owner = some X) (pair_le_of_ne hab ha hb) hao hbo
  unfold cnt at h
  omega

/-! ### Classification of transitions -/

/-- Every transition is an `⟨elect⟩` transition of a non-`IP` pointer, an `⟨elect⟩` transition of
`IP`, or preserves the pointers the two agents belong to; in the last case, if no `IP` agent is
involved, fresh agents stay fresh. -/
theorem Tr.classify {t : Transition (St Q F)} (ht : A.Tr t) :
    (∃ X, X ≠ A.IP ∧ t.p.owner = some X ∧ t.q.owner = some X ∧
      t.p' = .ptr X (A.v0 X) .none ∧ t.q' = .ptr (A.nxt X) (A.v0 (A.nxt X)) .none) ∨
    (t.p.owner = some A.IP ∧ t.q.owner = some A.IP ∧ t.p' = .ptr A.X1 (A.v0 A.X1) .none ∧
      t.q' = .reg A.z0) ∨
    (t.p'.owner = t.p.owner ∧ t.q'.owner = t.q.owner ∧
      (t.p.owner ≠ some A.IP → t.q.owner ≠ some A.IP → ∀ X,
        (t.p.owner = some X → A.Fresh X t.p → A.Fresh X t.p') ∧
        (t.q.owner = some X → A.Fresh X t.q → A.Fresh X t.q'))) := by
  cases ht with
  | elect hX ha hb => exact .inl ⟨_, hX, ha, hb, rfl, rfl⟩
  | electIP ha hb => exact .inr (.inl ⟨ha, hb, rfl, rfl⟩)
  | tsSet b hI hv =>
    refine .inr (.inr ⟨rfl, rfl, fun _ _ X => ⟨?_, ?_⟩⟩)
    · intro _ h; rcases h with h | ⟨_, _, h⟩ <;> cases b <;> simp at h
    · intro h _; simp at h; subst h; exact .inr ⟨rfl, b, rfl⟩
  | asMap hI hXY hX hY hv =>
    refine .inr (.inr ⟨rfl, rfl, fun _ _ X => ⟨?_, ?_⟩⟩)
    · intro _ h; rcases h with h | ⟨_, _, h⟩ <;> simp at h
    · intro h hf; simp at h; subst h
      rcases hf with h | ⟨h1, b, h⟩
      · simp at h; obtain ⟨rfl, -⟩ := h; exact .inl rfl
      · simp at h; obtain ⟨rfl, rfl, -⟩ := h; exact .inr ⟨h1, b, rfl⟩
  | tsNo hI hv hq =>
    refine .inr (.inr ⟨rfl, rfl, fun _ _ X => ⟨?_, fun _ h => h⟩⟩)
    intro _ h; rcases h with h | ⟨_, _, h⟩ <;> simp at h
  | mvEmit hI hv =>
    refine .inr (.inr ⟨rfl, rfl, fun _ _ X => ⟨?_, fun h => by simp at h⟩⟩)
    intro _ h; rcases h with h | ⟨_, _, h⟩ <;> simp at h
  | mvPut hI hv =>
    refine .inr (.inr ⟨rfl, rfl, fun _ _ X => ⟨?_, fun h => by simp at h⟩⟩)
    intro _ h; rcases h with h | ⟨_, _, h⟩ <;> simp at h
  | tsYes hI hv =>
    refine .inr (.inr ⟨rfl, rfl, fun _ _ X => ⟨?_, fun h => by simp at h⟩⟩)
    intro _ h; rcases h with h | ⟨_, _, h⟩ <;> simp at h
  | mvStart hI hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | mvHalf hI hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | mvTake hI hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | mvEnd hI hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | tsStart hI hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | tsEnd hI hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | asStart hI hXY hX hY => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | asEnd hI hXY hX hY hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | jmp hI hY hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | asSelf hI hY hv => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | asIP hI hX => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)
  | jmpIP hI => exact .inr (.inr ⟨rfl, rfl, fun h => absurd rfl h⟩)

/-! ### Counts along the three kinds of transitions -/

section counts

variable {A} {t : Transition (St Q F)} {c c' : Multiset (St Q F)}

theorem cnt_local (hf : t.Fires c c') (hp : t.p'.owner = t.p.owner)
    (hq : t.q'.owner = t.q.owner) (X : F) : cnt c' X = cnt c X := by
  have := fires_countP hf (fun s => s.owner = some X)
  simp only [hp, hq] at this
  unfold cnt; omega

theorem below_local (hf : t.Fires c c') (hp : t.p'.owner = t.p.owner)
    (hq : t.q'.owner = t.q.owner) (l : ℕ) : A.below c' l = A.below c l := by
  have := fires_countP hf (fun s => A.lvlOf s < l)
  have e1 : A.lvlOf t.p' = A.lvlOf t.p := by unfold lvlOf; rw [hp]
  have e2 : A.lvlOf t.q' = A.lvlOf t.q := by unfold lvlOf; rw [hq]
  simp only [e1, e2] at this
  unfold below; omega

theorem cnt_elect (hf : t.Fires c c') {Y : F} (hY : Y ≠ A.IP) (hp : t.p.owner = some Y)
    (hq : t.q.owner = some Y) (hp' : t.p' = .ptr Y (A.v0 Y) .none)
    (hq' : t.q' = .ptr (A.nxt Y) (A.v0 (A.nxt Y)) .none) (X : F) :
    cnt c' X + (if Y = X then 1 else 0) = cnt c X + (if A.nxt Y = X then 1 else 0) := by
  have := fires_countP hf (fun s => s.owner = some X)
  simp only [hp, hq, hp', hq', St.owner_ptr, Option.some_inj] at this
  unfold cnt
  split_ifs at this ⊢ <;> omega

theorem below_elect (hf : t.Fires c c') {Y : F} (hY : Y ≠ A.IP) (hp : t.p.owner = some Y)
    (hq : t.q.owner = some Y) (hp' : t.p' = .ptr Y (A.v0 Y) .none)
    (hq' : t.q' = .ptr (A.nxt Y) (A.v0 (A.nxt Y)) .none) (l : ℕ) :
    A.below c' l + (if l = A.lvl Y + 1 then 1 else 0) = A.below c l := by
  have := fires_countP hf (fun s => A.lvlOf s < l)
  simp only [A.lvlOf_of_owner hp, A.lvlOf_of_owner hq, hp', hq', lvlOf_ptr, A.lvl_nxt hY] at this
  unfold below
  split_ifs at this ⊢ <;> omega

theorem cnt_electIP (hf : t.Fires c c') (hp : t.p.owner = some A.IP)
    (hq : t.q.owner = some A.IP) (hp' : t.p' = .ptr A.X1 (A.v0 A.X1) .none)
    (hq' : t.q' = .reg A.z0) (X : F) :
    cnt c' X + (if A.IP = X then 2 else 0) = cnt c X + (if A.X1 = X then 1 else 0) := by
  have := fires_countP hf (fun s => s.owner = some X)
  simp only [hp, hq, hp', hq', St.owner_ptr, St.owner_reg, Option.some_inj, reduceCtorEq,
    if_false, add_zero] at this
  unfold cnt
  split_ifs at this ⊢ <;> omega

theorem below_electIP (hf : t.Fires c c') (hp : t.p.owner = some A.IP)
    (hq : t.q.owner = some A.IP) (hp' : t.p' = .ptr A.X1 (A.v0 A.X1) .none)
    (hq' : t.q' = .reg A.z0) (l : ℕ) :
    A.below c' l + (if Fintype.card F - 1 < l then 2 else 0) =
      A.below c l + (if 0 < l then 1 else 0) + (if Fintype.card F < l then 1 else 0) := by
  have := fires_countP hf (fun s => A.lvlOf s < l)
  simp only [A.lvlOf_of_owner hp, A.lvlOf_of_owner hq, hp', hq', lvlOf_ptr, lvlOf_reg, A.lvl_X1,
    A.lvl_IP] at this
  unfold below
  split_ifs at this ⊢ <;> omega

end counts

/-! ### Preservation of the invariants -/

section preservation

variable {t : Transition (St Q F)} {c c' : Multiset (St Q F)}

theorem pre_le (hf : t.Fires c c') : ({t.p, t.q} : Multiset (St Q F)) ≤ c := hf.1

theorem p_mem (hf : t.Fires c c') : t.p ∈ c := Multiset.mem_of_le hf.1 (by simp [Transition.pre])
theorem q_mem (hf : t.Fires c c') : t.q ∈ c := Multiset.mem_of_le hf.1 (by simp [Transition.pre])
theorem p'_mem (hf : t.Fires c c') : t.p' ∈ c' := by
  rw [hf.2]; exact Multiset.mem_add.2 (.inr (by simp [Transition.post]))
theorem q'_mem (hf : t.Fires c c') : t.q' ∈ c' := by
  rw [hf.2]; exact Multiset.mem_add.2 (.inr (by simp [Transition.post]))

theorem two_le_cnt (hf : t.Fires c c') {Y : F} (hp : t.p.owner = some Y)
    (hq : t.q.owner = some Y) : 2 ≤ cnt c Y :=
  two_le_countP (p := fun s => s.owner = some Y) hf.1 hp hq

theorem cnt_pos_of_mem {s : St Q F} (hs : s ∈ c) {X : F} (h : s.owner = some X) :
    0 < cnt c X := Multiset.countP_pos.2 ⟨s, hs, h⟩

theorem lvl_lt_IP {X : F} (hX : X ≠ A.IP) : A.lvl X < Fintype.card F - 1 := by
  have := A.lvl_lt_of_ne_IP hX; omega

theorem ptrAt_last : A.ptrAt (Fintype.card F - 1) = A.IP := by
  rw [← A.lvl_IP, A.ptrAt_lvl]

theorem invJ_step (h : A.InvJ c) (ht : A.Tr t) (hf : t.Fires c c') : A.InvJ c' := by
  intro l hl
  rcases Tr.classify A ht with ⟨Y, hY, hp, hq, hp', hq'⟩ | ⟨hp, hq, hp', hq'⟩ | ⟨hp, hq, -⟩
  · have e := below_elect hf hY hp hq hp' hq' l
    have h2 := two_le_cnt hf hp hq
    have h3 := A.below_lvl_succ c Y
    have h4 := h (A.lvl Y) (A.lvl_lt Y).le
    have h5 := h l hl
    split_ifs at e with hl'
    · subst hl'; omega
    · omega
  · have e := below_electIP hf hp hq hp' hq' l
    have h5 := h l hl
    have := A.card_F_pos
    have h6 : A.below c (Fintype.card F) = A.below c (Fintype.card F - 1) + cnt c A.IP := by
      have h6 := A.below_succ c (l := Fintype.card F - 1) (by omega)
      rwa [A.ptrAt_last, Nat.sub_add_cancel (by omega)] at h6
    have h7 := h (Fintype.card F - 1) (by omega)
    have h8 := two_le_cnt hf hp hq
    split_ifs at e with e1 e2 e3
    · omega
    · have : l = Fintype.card F := by omega
      subst this; omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · rw [below_local hf hp hq]; exact h l hl

theorem invK_step (h : A.InvK c) (ht : A.Tr t) (hf : t.Fires c c') : A.InvK c' := by
  intro X hX hpos hc
  rcases Tr.classify A ht with ⟨Y, hY, hp, hq, hp', hq'⟩ | ⟨hp, hq, hp', hq'⟩ | ⟨hp, hq, -⟩
  · have e := cnt_elect hf hY hp hq hp' hq' X
    have h2 := two_le_cnt hf hp hq
    by_cases e1 : A.nxt Y = X
    · rw [if_pos e1] at e
      have : Y ≠ X := fun h => by
        have := A.lvl_nxt hY; rw [e1, h] at this; omega
      rw [if_neg this] at e; omega
    rw [if_neg e1] at e
    by_cases e2 : Y = X
    · subst e2; rw [if_pos rfl] at e; omega
    rw [if_neg e2] at e
    have hk := h X hX hpos (by omega)
    have e3 := below_elect hf hY hp hq hp' hq' (A.lvl X)
    have : A.lvl X ≠ A.lvl Y + 1 := fun h' => e1 (A.lvl_injective (by rw [A.lvl_nxt hY, h']))
    rw [if_neg this] at e3; omega
  · have e := cnt_electIP hf hp hq hp' hq' X
    have hX1 : A.X1 ≠ X := fun h' => by rw [← h', A.lvl_X1] at hpos; omega
    rw [if_neg (Ne.symm hX), if_neg hX1] at e
    have hk := h X hX hpos (by omega)
    have e3 := below_electIP hf hp hq hp' hq' (A.lvl X)
    have := A.lvl_lt_IP hX
    rw [if_neg (by omega), if_pos hpos, if_neg (by omega)] at e3
    omega
  · rw [below_local hf hp hq]
    exact h X hX hpos (by rw [← cnt_local hf hp hq X]; exact hc)

theorem invFr_step (h : A.Inv c) (ht : A.Tr t) (hf : t.Fires c c') : A.InvFr c' := by
  obtain ⟨hJ, -, hFr⟩ := h
  have hJ' := A.invJ_step hJ ht hf
  intro hIP X hX hset s hs ho
  rcases Tr.classify A ht with ⟨Y, hY, hp, hq, hp', hq'⟩ | ⟨hp, hq, hp', hq'⟩ | ⟨hp, hq, hfr⟩
  · have eIP := cnt_elect hf hY hp hq hp' hq' A.IP
    rw [if_neg hY, hIP] at eIP
    have hnY : A.nxt Y ≠ A.IP := fun h' => by rw [if_pos h'] at eIP; omega
    rw [if_neg hnY] at eIP
    by_cases hXY : X = Y
    · subst hXY
      have h1 := A.below_lvl_succ c' X
      have h2 := hJ' (A.lvl X) (A.lvl_lt X).le
      have hle : cnt c' X ≤ 1 := by omega
      have := eq_of_cnt_le_one hle hs (p'_mem hf) ho (by rw [hp']; rfl)
      rw [this, hp']; exact .inl rfl
    · have e := below_elect hf hY hp hq hp' hq' (A.lvl X + 1)
      have : A.lvl X + 1 ≠ A.lvl Y + 1 := fun h' => hXY (A.lvl_injective (by omega))
      rw [if_neg this] at e
      rcases fires_mem_of_mem hf hs with hs | rfl | rfl
      · exact hFr (by omega) X hX (by omega) s hs ho
      · rw [hp'] at ho; simp at ho; exact absurd ho.symm hXY
      · rw [hq'] at ho ⊢; simp at ho; subst ho; exact .inl rfl
  · exfalso
    have e := below_electIP hf hp hq hp' hq' (A.lvl X + 1)
    have := A.lvl_lt_IP hX
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)] at e
    have := hJ (A.lvl X + 1) (by omega)
    omega
  · have hc := cnt_local hf hp hq A.IP
    rw [hIP] at hc
    have hpIP : t.p.owner ≠ some A.IP := fun h' => by
      have := cnt_pos_of_mem (p_mem hf) h'; omega
    have hqIP : t.q.owner ≠ some A.IP := fun h' => by
      have := cnt_pos_of_mem (q_mem hf) h'; omega
    have hset' : A.below c (A.lvl X + 1) = A.lvl X + 1 := by
      rw [← below_local hf hp hq]; exact hset
    rcases fires_mem_of_mem hf hs with hs | rfl | rfl
    · exact hFr hc.symm X hX hset' s hs ho
    · rw [hp] at ho
      exact (hfr hpIP hqIP X).1 ho (hFr hc.symm X hX hset' _ (p_mem hf) ho)
    · rw [hq] at ho
      exact (hfr hpIP hqIP X).2 ho (hFr hc.symm X hX hset' _ (q_mem hf) ho)

theorem inv_step (h : A.Inv c) (ht : A.Tr t) (hf : t.Fires c c') : A.Inv c' :=
  ⟨A.invJ_step h.1 ht hf, A.invK_step h.2.1 ht hf, A.invFr_step h ht hf⟩

end preservation

/-! ### The map `π` and elected configurations -/

/-- The map `π` from machine configurations to protocol configurations: `C(x)` agents in
register `x`, and one agent `X^{C(X)}_none` per pointer. -/
def pi (C : Cfg Q F) : Multiset (St Q F) := render C.reg (fun X => .ptr X (C.ptr X) .none)

theorem ownerResp_idle (C : Cfg Q F) : OwnerResp (fun X => (.ptr X (C.ptr X) .none : St Q F)) :=
  fun _ => rfl

theorem card_regsM (r : Q → ℕ) : Multiset.card (regsM (F := F) r) = ∑ q, r q := by
  simp [regsM, Multiset.card_sum]

theorem card_render (r : Q → ℕ) (g : F → St Q F) :
    Multiset.card (render r g) = ∑ q, r q + Fintype.card F := by
  simp [render, card_regsM, Finset.card_univ]

theorem card_pi (C : Cfg Q F) : Multiset.card (pi C) = total C + Fintype.card F := by
  simp [pi, card_render, total]

theorem v0_mem_dom (hdom : ∀ X, (A.dom X).Nonempty) (X : F) : A.v0 X ∈ A.dom X := by
  unfold v0
  split_ifs with h1 h2 h3 h4
  · subst h1
    obtain ⟨v, hv⟩ := hdom A.IP
    rw [A.dom_IP] at hv ⊢
    obtain ⟨i, hi, -⟩ := Finset.mem_map.1 hv
    simp only [Finset.mem_Icc] at hi
    exact Finset.mem_map.2 ⟨1, by simp; omega, rfl⟩
  · rcases h2 with rfl | rfl
    · rw [A.dom_OF]; simp
    · rw [A.dom_CF]; simp
  · have hx := h3.choose_spec
    generalize h3.choose = x at hx ⊢
    subst hx; exact A.mem_dom_V x
  · exact h4.choose_spec
  · exact absurd (hdom X) h4

theorem below_of_elected {c : Multiset (St Q F)} (h : Elected c) :
    ∀ l ≤ Fintype.card F, A.below c l = l := by
  intro l hl
  induction l with
  | zero => exact A.below_zero c
  | succ l ih => rw [A.below_succ c (by omega), ih (by omega), h]

theorem invJ_elected_or {c : Multiset (St Q F)} (hJ : A.InvJ c) (h : ¬ Elected c) :
    ∃ X, 2 ≤ cnt c X := by
  by_contra hne
  push Not at hne
  apply h
  have hle : ∀ X, cnt c X ≤ 1 := fun X => by have := hne X; omega
  by_contra h'
  simp only [Elected, not_forall] at h'
  obtain ⟨X₀, hX₀⟩ := h'
  have h0 : cnt c X₀ = 0 := by have := hle X₀; omega
  have : ∀ l ≤ Fintype.card F, A.below c l + (if A.lvl X₀ < l then 1 else 0) ≤ l := by
    intro l hl
    induction l with
    | zero => simp [A.below_zero]
    | succ l ih =>
      rw [A.below_succ c (by omega)]
      have := ih (by omega)
      have h2 := hle (A.ptrAt l)
      by_cases e : A.lvl X₀ = l
      · have : A.ptrAt l = X₀ := by rw [← e, A.ptrAt_lvl]
        rw [this, h0]; split_ifs at * <;> omega
      · split_ifs at * <;> omega
  have h1 := this _ le_rfl
  have h2 := hJ _ le_rfl
  rw [if_pos (A.lvl_lt X₀)] at h1
  omega

theorem eq_render_of_elected {c : Multiset (St Q F)} (h : Elected c) :
    ∃ g, OwnerResp g ∧ (∀ X, g X ∈ c) ∧ c = render (fun q => c.count (.reg q)) g := by
  have hex : ∀ X, ∃ s ∈ c, s.owner = some X := fun X =>
    Multiset.countP_pos.1 (by have := h X; unfold cnt at this; omega)
  choose g hgc hgo using hex
  refine ⟨g, hgo, hgc, ?_⟩
  have hown : ∀ s X, s.owner = some X →
      c.count s = Multiset.card (Multiset.filter (fun Y => s = g Y) Finset.univ.val) := by
    intro s X hs
    have hf : Multiset.filter (fun Y => s = g Y) Finset.univ.val =
        if s = g X then {X} else 0 := by
      split_ifs with hsX
      · have : Finset.univ.filter (fun Y => s = g Y) = {X} := by
          ext Y
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro hY
            have := hgo Y; rw [← hY, hs] at this; exact (Option.some_injective _ this).symm
          · rintro rfl; exact hsX
        simpa using congrArg Finset.val this
      · rw [Multiset.filter_eq_nil]
        intro Y _ hY
        have := hgo Y; rw [← hY, hs] at this
        obtain rfl := Option.some_injective _ this
        exact hsX hY
    rw [hf]
    have hle : cnt c X ≤ 1 := (h X).le
    split_ifs with hsX
    · simp only [Multiset.card_singleton]
      subst hsX
      have h1 := Multiset.count_pos.2 (hgc X)
      have h2 : c.count (g X) ≤ cnt c X := by
        unfold cnt
        rw [Multiset.count_eq_card_filter_eq, Multiset.countP_eq_card_filter]
        exact Multiset.card_le_card (Multiset.monotone_filter_right c (fun s' hs' => by
          rw [← hs']; exact hgo X))
      omega
    · simp only [Multiset.card_zero]
      rw [Multiset.count_eq_zero]
      intro hsc
      exact hsX (eq_of_cnt_le_one hle hsc (hgc X) hs (hgo X))
  ext s
  rw [render, Multiset.count_add, count_regsM, Multiset.count_map]
  cases s with
  | reg q =>
    have : Multiset.filter (fun Y => St.reg q = g Y) Finset.univ.val = 0 := by
      rw [Multiset.filter_eq_nil]
      intro Y _ hY
      have := hgo Y; rw [← hY] at this; simp at this
    rw [this]; simp
  | ptr X v st => rw [hown _ X rfl]; simp
  | map X i => rw [hown _ X rfl]; simp

/-- `c` is `π(C)` for an initial configuration `C` of the machine. -/
def PiInit (c : Multiset (St Q F)) : Prop := ∃ C, A.IsInitial C ∧ c = pi C

theorem piInit_of_fresh (hdom : ∀ X, (A.dom X).Nonempty) {c : Multiset (St Q F)}
    (h : Elected c) (hfr : ∀ s ∈ c, ∀ X, s.owner = some X → A.Fresh X s) : A.PiInit c := by
  obtain ⟨g, hg, hgc, hc⟩ := eq_render_of_elected h
  have hfg : ∀ X, A.Fresh X (g X) := fun X => hfr _ (hgc X) X (hg X)
  let val : F → Val Q := fun X => match g X with | .ptr _ v _ => v | _ => A.v0 X
  have hval : ∀ X, g X = .ptr X (val X) .none := by
    intro X
    rcases hfg X with h1 | ⟨rfl, b, h1⟩ <;> simp only [val, h1]
  refine ⟨⟨fun q => c.count (.reg q), val⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · show val A.IP = _
    rcases hfg A.IP with h1 | ⟨h2, -⟩
    · simp only [val, h1, A.v0_IP]
    · exact absurd h2.symm A.CF_ne_IP
  · intro x
    show val _ = _
    rcases hfg (A.V (some x)) with h1 | ⟨h2, -⟩
    · simp only [val, h1, A.v0_V]
    · exact absurd h2 (A.V_ne_CF _)
  · intro X
    show val X ∈ _
    rcases hfg X with h1 | ⟨rfl, b, h1⟩
    · simp only [val, h1]; exact A.v0_mem_dom hdom X
    · simp only [val, h1, A.dom_CF]; cases b <;> simp
  · conv_lhs => rw [hc]
    simp only [pi]
    congr 1
    funext X
    exact hval X

/-- **Key step of Lemma 15.** If the invariant holds, `c` is not elected and a transition leads to
an elected configuration `c'`, then `c' = π(C)` for an initial configuration `C`. -/
theorem piInit_of_step (hdom : ∀ X, (A.dom X).Nonempty) {t : Transition (St Q F)}
    {c c' : Multiset (St Q F)} (h : A.Inv c) (hne : ¬ Elected c) (ht : A.Tr t)
    (hf : t.Fires c c') (he : Elected c') : A.PiInit c' := by
  obtain ⟨hJ, hK, hFr⟩ := h
  have hb' := A.below_of_elected he
  have hk1 : A.X1 ≠ A.IP := fun h' => by
    have := A.lvl_X1; rw [h', A.lvl_IP] at this
    have := Fintype.card_le_of_injective (fun b : Bool => if b then A.OF else A.CF)
      (by intro a b; cases a <;> cases b <;> simp [A.OF_ne_CF, A.OF_ne_CF.symm])
    simp at this; omega
  rcases Tr.classify A ht with ⟨Y, hY, hp, hq, hp', hq'⟩ | ⟨hp, hq, hp', hq'⟩ | ⟨hp, hq, -⟩
  · by_cases hnY : A.nxt Y = A.IP
    · -- the last step creates the `IP` agent
      have eIP := cnt_elect hf hY hp hq hp' hq' A.IP
      rw [if_neg hY, if_pos hnY, he] at eIP
      apply A.piInit_of_fresh hdom he
      intro s hs X ho
      by_cases hXY : X = Y
      · subst hXY
        have := eq_of_cnt_le_one (he X).le hs (p'_mem hf) ho (by rw [hp']; rfl)
        rw [this, hp']; exact .inl rfl
      by_cases hXI : X = A.IP
      · subst hXI
        have := eq_of_cnt_le_one (he _).le hs (q'_mem hf) ho (by rw [hq', hnY]; rfl)
        rw [this, hq', hnY]; exact .inl rfl
      rcases fires_mem_of_mem hf hs with hs | rfl | rfl
      · have e := below_elect hf hY hp hq hp' hq' (A.lvl X + 1)
        have : A.lvl X + 1 ≠ A.lvl Y + 1 := fun h' => hXY (A.lvl_injective (by omega))
        rw [if_neg this, hb' _ (A.lvl_lt X)] at e
        exact hFr (by omega) X hXI e.symm s hs ho
      · rw [hp'] at ho; simp at ho; exact absurd ho.symm hXY
      · rw [hq', hnY] at ho; simp at ho; exact absurd ho.symm hXI
    · exfalso
      have e := cnt_elect hf hY hp hq hp' hq' (A.nxt Y)
      have hYn : Y ≠ A.nxt Y := fun h' => by have := A.lvl_nxt hY; rw [← h'] at this; omega
      rw [if_neg hYn, if_pos rfl, he] at e
      have hl := A.lvl_nxt hY
      have hk := hK (A.nxt Y) hnY (by omega) (by omega)
      rw [hl] at hk
      have e2 := below_elect hf hY hp hq hp' hq' (A.lvl Y + 1)
      rw [if_pos rfl, hb' _ (by have := A.lvl_lt_of_ne_IP hY; omega)] at e2
      have := A.lvl_lt_IP hnY
      omega
  · exfalso
    have e := cnt_electIP hf hp hq hp' hq' A.X1
    rw [if_neg (Ne.symm hk1), if_pos rfl, he] at e
    have h1 : A.below c 1 = A.below c 0 + cnt c (A.ptrAt 0) := A.below_succ c A.card_F_pos
    rw [A.below_zero] at h1
    have h2 := hJ 1 A.card_F_pos
    have : A.ptrAt 0 = A.X1 := rfl
    rw [this] at h1
    omega
  · exact absurd (fun X => (cnt_local hf hp hq X) ▸ he X) hne

/-! ### Termination of the election and Lemma 15 -/

theorem inv_init {c : Multiset (St Q F)} (h : Fintype.card F ≤ c.count A.initS) : A.Inv c := by
  have hX1 : c.count A.initS ≤ A.below c 1 := by
    unfold below
    rw [Multiset.count_eq_card_filter_eq, Multiset.countP_eq_card_filter]
    refine Multiset.card_le_card (Multiset.monotone_filter_right c (fun s hs => ?_))
    rw [← hs]; simp [initS, A.lvl_X1]
  have hmono : ∀ l, 1 ≤ l → A.below c 1 ≤ A.below c l := by
    intro l hl
    unfold below
    rw [Multiset.countP_eq_card_filter, Multiset.countP_eq_card_filter]
    exact Multiset.card_le_card (Multiset.monotone_filter_right c (fun s hs => by omega))
  refine ⟨fun l _ => ?_, fun X _ hpos _ => ?_, fun _ X hX hset => ?_⟩
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · simp
    · have := hmono l hl; omega
  · have := hmono _ hpos; omega
  · exfalso
    have := hmono (A.lvl X + 1) (by omega)
    have := A.lvl_lt_IP hX
    omega

theorem inv_reach {c c' : Multiset (St Q F)} (h : A.Inv c) (hr : Reach A.basePP.Step c c') :
    A.Inv c' := by
  induction hr with
  | refl => exact h
  | tail _ hs ih =>
    rcases hs with rfl | ⟨t, ht, hf⟩
    · exact ih
    · exact A.inv_step ih ht hf

/-- The potential `∑ 3^{level}`, increased by every `⟨elect⟩` transition. -/
noncomputable def pot (c : Multiset (St Q F)) : ℕ := (c.map (fun s => 3 ^ A.lvlOf s)).sum

theorem lvlOf_le (s : St Q F) : A.lvlOf s ≤ Fintype.card F := by
  unfold lvlOf
  split
  · exact (A.lvl_lt _).le
  · exact le_rfl

theorem pot_le (c : Multiset (St Q F)) : A.pot c ≤ Multiset.card c * 3 ^ Fintype.card F := by
  unfold pot
  induction c using Multiset.induction_on with
  | empty => simp
  | cons s c ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have := Nat.pow_le_pow_right (by norm_num : 0 < 3) (A.lvlOf_le s)
    nlinarith

theorem elect_enabled {c : Multiset (St Q F)} (hJ : A.InvJ c) (hne : ¬ Elected c) :
    ∃ t c', A.Tr t ∧ t.Fires c c' ∧ A.pot c < A.pot c' := by
  obtain ⟨X, hX⟩ := A.invJ_elected_or hJ hne
  obtain ⟨a, b, ha, hb, hle⟩ := exists_pair_of_two_le (p := fun s => s.owner = some X) hX
  have key : ∀ t : Transition (St Q F), A.Tr t → t.p = a → t.q = b →
      3 ^ A.lvlOf a + 3 ^ A.lvlOf b < 3 ^ A.lvlOf t.p' + 3 ^ A.lvlOf t.q' →
      ∃ t c', A.Tr t ∧ t.Fires c c' ∧ A.pot c < A.pot c' := by
    intro t ht hp hq hlt
    obtain ⟨c', hc'⟩ : ∃ c', c' = c - t.pre + t.post := ⟨_, rfl⟩
    have hpre : t.pre = {a, b} := by simp [Transition.pre, hp, hq]
    have hf : t.Fires c c' := ⟨hpre ▸ hle, hc'⟩
    refine ⟨t, c', ht, hf, ?_⟩
    have := hf.sum_map (fun s => 3 ^ A.lvlOf s)
    rw [hpre] at this
    simp only [Transition.post, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.sum_cons, Multiset.map_singleton, Multiset.sum_singleton] at this
    unfold pot; omega
  by_cases hXI : X = A.IP
  · subst hXI
    refine key _ (Tr.electIP ha hb) rfl rfl ?_
    rw [A.lvlOf_of_owner ha, A.lvlOf_of_owner hb]
    simp only [lvlOf_ptr, lvlOf_reg, A.lvl_X1, A.lvl_IP, pow_zero]
    have := A.card_F_pos
    have : 3 ^ Fintype.card F = 3 * 3 ^ (Fintype.card F - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  · refine key _ (Tr.elect hXI ha hb) rfl rfl ?_
    rw [A.lvlOf_of_owner ha, A.lvlOf_of_owner hb]
    simp only [lvlOf_ptr, A.lvl_nxt hXI, pow_succ]
    have := Nat.one_le_pow (A.lvl X) 3 (by norm_num)
    omega

/-- From a configuration satisfying the election invariant that is not yet elected, the protocol
reaches `π(C)` for an initial configuration `C` (the first elected configuration on the way). -/
theorem exists_reach_piInit (hdom : ∀ X, (A.dom X).Nonempty) {c : Multiset (St Q F)}
    (h : A.Inv c) (hne : ¬ Elected c) : ∃ c', MReach {t | A.Tr t} c c' ∧ A.PiInit c' := by
  suffices ∀ N (c : Multiset (St Q F)), Multiset.card c * 3 ^ Fintype.card F - A.pot c = N →
      A.Inv c → ¬ Elected c → ∃ c', MReach {t | A.Tr t} c c' ∧ A.PiInit c' from
    this _ c rfl h hne
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro c hN h hne
    obtain ⟨t, c', ht, hf, hpot⟩ := A.elect_enabled h.1 hne
    have h' := A.inv_step h ht hf
    by_cases he : Elected c'
    · exact ⟨c', .single ⟨t, ht, hf⟩, A.piInit_of_step hdom h hne ht hf he⟩
    · have hle := A.pot_le c'
      have hcc : Multiset.card c' = Multiset.card c := hf.card_eq
      rw [hcc] at hle
      obtain ⟨c'', h1, h2⟩ := ih _ (by rw [← hN, hcc]; omega) c' rfl h' he
      exact ⟨c'', Relation.ReflTransGen.head ⟨t, ht, hf⟩ h1, h2⟩

theorem not_elected_init {c : Multiset (St Q F)} (h : Fintype.card F ≤ c.count A.initS) :
    ¬ Elected c := by
  intro he
  have h1 : c.count A.initS ≤ cnt c A.X1 := by
    unfold cnt
    rw [Multiset.count_eq_card_filter_eq, Multiset.countP_eq_card_filter]
    exact Multiset.card_le_card (Multiset.monotone_filter_right c (fun s hs => by
      rw [← hs]; rfl))
  have h2 : 2 ≤ Fintype.card F := by
    have := Fintype.card_le_of_injective (fun b : Bool => if b then A.OF else A.CF)
      (by intro a b; cases a <;> cases b <;> simp [A.OF_ne_CF, A.OF_ne_CF.symm])
    simpa using this
  have := he A.X1
  omega

/-- **Lemma 15.** Every configuration `c` of `PP` with at least `|F|` agents in the initial state
`(X_1)^{v_1}_none` (and arbitrary other agents) reaches `π(C)` for an initial configuration `C`
of the machine with `|C| = |π(C)| - |F|`. (Lean: `total C + |F| = |c|`.) -/
theorem lemma_15 (hdom : ∀ X, (A.dom X).Nonempty) (c : Multiset (St Q F))
    (hc : Fintype.card F ≤ c.count A.initS) :
    ∃ C, A.IsInitial C ∧ Reach A.basePP.Step c (pi C) ∧
      total C + Fintype.card F = Multiset.card c := by
  obtain ⟨c', hr, C, hC, rfl⟩ := A.exists_reach_piInit hdom (A.inv_init hc) (A.not_elected_init hc)
  refine ⟨C, hC, A.basePP.reach_of_mreach hr, ?_⟩
  rw [← card_pi, MReach.card_eq hr]

end Machine

end Podc.PPDoubleExpThresholds
