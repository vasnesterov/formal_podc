import Papers.PODC2016.ConcurrentDSU.Inv
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Model

/-!
# Linearizability (Lemma 3.2)

The linearization points are those of the paper:
* `SameSet` returning `true` and `Unite` returning without a link: the read in the last
  `Find(v)` that found `v` to be a root (then `u = v`);
* `Unite` doing a link: the successful `Cas`;
* `SameSet` returning `false`: also the read in the last `Find(v)` (`u` and `v` are then two
  different roots). This point is only known to be the linearization point *afterwards*, when
  `u = u.parent` is checked: the operation is inserted retroactively into the linearization
  (`IsLinearization.insert`, from `Cslib/Computability/Distributed/SharedMemory/LinPoints.lean`). The
  invariant keeps, for every process in state `chk u v` whose `u` is still a root, a cut
  `L = S₁ ++ S₂` of the current linearization after which `x` and `y` are in different sets and
  such that no operation of `S₂` precedes the `SameSet` in real time.

The invariant `LinInv` also says that the abstract state of the linearization is the
partition into trees of the current memory (`linState L = same C.mem`).
-/

set_option linter.unusedSectionVars false

namespace Podc.ConcurrentDSU

open Cslib.SharedMemory

variable {E : Type} [Fintype E] [DecidableEq E] {P : Type} [DecidableEq P]
variable {K : FindKind} {key : E → ℕ}

/-! ### Classification of steps -/

/-- Local states in which the current operation is not yet linearized and needs no extra
bookkeeping. -/
def IsRun : Loc E → Prop
  | .fu _ _ _ => True
  | .fv _ _ _ => True
  | .lnk _ _ => True
  | _ => False

lemma fRes_same {m : E → E} (hg : Good key m) {s : E} {fs : FS E} (hf : FInv K key m s fs) :
    same (fRes K fs m).2 = same m := by
  cases fs with
  | tst u => rfl
  | adv u => rfl
  | rdP u i => rfl
  | rdG u v i => rfl
  | cas u v w i =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hf
    show same (if m u = v then Function.update m u w else m) = same m
    split_ifs with hmu
    · have hku : key u < key w := by
        rcases h6 with h6 | h6
        · subst h6
          exfalso
          have hr : rootOf m w = v := by
            unfold same at h4 h3; rw [h4, h3, rootOf_of_fixed hmu]
          have := key_le_rootOf hg w; rw [hr] at this; omega
        · omega
      have hw : rootOf m w = rootOf m u := by
        unfold same at h4; rw [h4, ← hmu, rootOf_apply hg]
      funext a b
      unfold same
      rw [rootOf_update_split hg hku hw, rootOf_update_split hg hku hw]
    · rfl

lemma fRes_inr {m : E → E} {fs : FS E} {r : E} (h : (fRes K fs m).1 = .inr r) :
    (fRes K fs m).2 = m := by
  cases fs with
  | tst u => rfl
  | adv u => rfl
  | rdP u i => rfl
  | rdG u v i => rfl
  | cas u v w i =>
    simp only [fRes, FS.next] at h
    split_ifs at h

lemma joinRel_comm (s : E → E → Prop) (x y a b : E) : joinRel s y x a b ↔ joinRel s x y a b := by
  unfold joinRel; tauto

/-- The five kinds of steps of a process (with respect to linearization). -/
theorem tauRes_cases (hkey : Function.Injective key) {m : E → E} (hg : Good key m)
    {o : DSUOp E} {l l' : Loc E} {m' : E → E} (hl : LocInv K key m (some o) l)
    (h : tauRes K key l m = some (l', m')) :
    (IsRun l' ∧ same m' = same m) ∨
    (∃ u r x y, o = .sameSet x y ∧ l' = .chk u r ∧ m' = m ∧ m r = r ∧ same m u x ∧
      same m r y ∧ u ≠ r) ∨
    (l' = .done true ∧ m' = m ∧ same m o.x o.y) ∨
    (∃ u v x y, o = .sameSet x y ∧ l = .chk u v ∧ l' = .done false ∧ m' = m ∧ m u = u) ∨
    (∃ x y, o = .unite x y ∧ l' = .done true ∧ ∀ a b, same m' a b ↔ joinRel (same m) x y a b) := by
  cases l with
  | idle => exact hl.elim
  | done r => simp [tauRes, act] at h
  | fu b fs v =>
    obtain ⟨hb, hf, hv⟩ := hl
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    left
    refine ⟨?_, fRes_same hg hf⟩
    cases (fRes K fs m).1 <;> trivial
  | fv b u fs =>
    obtain ⟨hb, hu, hf⟩ := hl
    simp only [tauRes, act, tauRes_liftF, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hs := (fRes_spec hg hf).2
    have hsame := fRes_same hg hf
    revert hs
    cases hc : (fRes K fs m).1 with
    | inl fs' => intro; left; exact ⟨trivial, hsame⟩
    | inr r =>
      rintro ⟨hm, hr, hrs⟩
      simp only [contV]
      rw [hm]
      split_ifs with h1 h2
      · subst h1
        right; right; left
        exact ⟨rfl, by simp, same_trans (same_symm hu) hrs⟩
      · left; exact ⟨trivial, by simp⟩
      · right; left
        cases o with
        | unite x y => simp [DSUOp.isUnite] at hb; exact absurd (by simpa using hb) h2
        | sameSet x y => exact ⟨u, r, x, y, rfl, rfl, by simp, hr, hu, hrs, h1⟩
  | chk u v =>
    obtain ⟨hb, hu, hv, huv⟩ := hl
    simp only [tauRes, act, ptr_read, Function.update_eq_self, val, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    by_cases h1 : m u = u
    · simp only [h1, ite_true]
      right; right; right; left
      cases o with
      | unite x y => simp [DSUOp.isUnite] at hb
      | sameSet x y => exact ⟨u, v, x, y, rfl, rfl, by simp, by simp, h1⟩
    · simp only [h1, ite_false]
      left; exact ⟨trivial, by simp⟩
  | lnk u v =>
    obtain ⟨hb, hu, hv, huv⟩ := hl
    have hk : key u ≠ key v := fun h => huv (hkey h)
    cases o with
    | sameSet x y => simp [DSUOp.isUnite] at hb
    | unite x y =>
    simp only [DSUOp.x, DSUOp.y] at hu hv
    by_cases hlt : key u < key v
    · simp only [tauRes, act, hlt, ite_true, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hr : m u = u
      · simp only [hr, ite_true, Function.update_self]
        right; right; right; right
        exact ⟨x, y, rfl, by simp, fun a b => same_update_link hg hr hlt hu hv a b⟩
      · simp only [hr, ite_false, Function.update_eq_self, reduceCtorEq]
        left; exact ⟨trivial, by simp⟩
    · have hlt' : key v < key u := by omega
      simp only [tauRes, act, hlt, ite_false, ptr_cas, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      by_cases hr : m v = v
      · simp only [hr, ite_true, Function.update_self]
        right; right; right; right
        refine ⟨x, y, rfl, by simp, fun a b => ?_⟩
        rw [same_update_link hg hr hlt' hv hu a b, joinRel_comm]
      · simp only [hr, ite_false, Function.update_eq_self, reduceCtorEq]
        left; exact ⟨trivial, by simp⟩

/-! ### Bookkeeping -/

/-- The abstract state after a sequential history. -/
noncomputable abbrev st (L : List (OpId P × (dsu E).Op)) : (dsu E).State := linState L

lemma st_nil : st ([] : List (OpId P × (dsu E).Op)) = Eq := rfl

lemma st_append (L : List (OpId P × (dsu E).Op)) (x : OpId P) (o : (dsu E).Op) :
    st (L ++ [(x, o)]) = ((dsu E).δ (st L) o).1 := by
  show (dsu E).runOps _ ((L ++ [(x, o)]).map Prod.snd) = _
  rw [List.map_append, ObjSpec.runOps_append]; rfl

lemma st_insert (L₁ L₂ : List (OpId P × (dsu E).Op)) (x : OpId P) (a b : E) :
    st (L₁ ++ (x, (DSUOp.sameSet a b : (dsu E).Op)) :: L₂) = st (L₁ ++ L₂) := by
  show (dsu E).runOps _ ((L₁ ++ (x, (DSUOp.sameSet a b : (dsu E).Op)) :: L₂).map Prod.snd) =
    (dsu E).runOps _ ((L₁ ++ L₂).map Prod.snd)
  rw [List.map_append, List.map_append, ObjSpec.runOps_append, ObjSpec.runOps_append,
    List.map_cons, ObjSpec.runOps_cons]

lemma joinRel_same {m : E → E} {x y : E} (h : same m x y) : joinRel (same m) x y = same m := by
  funext a b
  apply propext
  unfold joinRel
  constructor
  · rintro (h1 | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h1
    · exact same_trans h1 (same_trans h h2)
    · exact same_trans h1 (same_trans (same_symm h) h2)
  · intro h1; exact Or.inl h1

/-- Per-process part of the linearization invariant. -/
structure QOK (α : List (Label P (dsu E))) (C : Config (dsu E) (Ptr E) P (Loc E))
    (L : List (OpId P × (dsu E).Op)) (q : P) : Prop where
  done : ∀ o r, C.pend q = some o → C.loc q = .done r →
    ∃ L₁ L₂, L = L₁ ++ (curOp α q, o) :: L₂ ∧ ((dsu E).δ (st L₁) o).2 = r
  notin : C.pend q ≠ none → (∀ r, C.loc q ≠ .done r) → curOp α q ∉ L.map Prod.fst
  chk : ∀ x y u v, C.pend q = some (.sameSet x y) → C.loc q = .chk u v → C.mem u = u →
    ∃ S₁ S₂, L = S₁ ++ S₂ ∧ ¬ st S₁ x y ∧ ∀ z ∈ S₂, ¬ Precedes α z.1 (curOp α q)

/-- The linearization invariant. -/
structure LinInv (α : List (Label P (dsu E))) (C : Config (dsu E) (Ptr E) P (Loc E))
    (L : List (OpId P × (dsu E).Op)) : Prop where
  lin : IsLinearization α L
  state : st L = same C.mem
  qok : ∀ q, QOK α C L q

/-- Transport of the per-process invariant of a process `q` that does not move. -/
lemma QOK.transport {α α' : List (Label P (dsu E))} {C C' : Config (dsu E) (Ptr E) P (Loc E)}
    {L L' : List (OpId P × (dsu E).Op)} {q : P} (hq : QOK α C L q)
    (hcur : curOp α' q = curOp α q) (hpend : C'.pend q = C.pend q) (hloc : C'.loc q = C.loc q)
    (hroot : ∀ a, C'.mem a = a → C.mem a = a)
    (hinv : C.pend q ≠ none → Invoked α (curOp α q))
    (hprec : ∀ a, Invoked α (curOp α q) → ¬ Precedes α a (curOp α q) → ¬ Precedes α' a (curOp α q))
    (hT : ∀ L₁ L₂ (o : (dsu E).Op), L = L₁ ++ (curOp α q, o) :: L₂ →
      ∃ L₁' L₂', L' = L₁' ++ (curOp α q, o) :: L₂' ∧ st L₁' = st L₁)
    (hS : ∀ S₁ S₂, L = S₁ ++ S₂ → ∃ S₁' S₂', L' = S₁' ++ S₂' ∧ st S₁' = st S₁ ∧
      ∀ z ∈ S₂', z ∈ S₂ ∨ ¬ Precedes α' z.1 (curOp α q))
    (hN : curOp α q ∉ L.map Prod.fst → curOp α q ∉ L'.map Prod.fst) : QOK α' C' L' q where
  done o r hp hl := by
    rw [hpend] at hp; rw [hloc] at hl
    obtain ⟨L₁, L₂, hsplit, hr⟩ := hq.done o r hp hl
    obtain ⟨L₁', L₂', h1, h2⟩ := hT L₁ L₂ o hsplit
    exact ⟨L₁', L₂', by rw [hcur]; exact h1, by rw [h2]; exact hr⟩
  notin hp hl := by
    rw [hpend] at hp; rw [hloc] at hl
    rw [hcur]; exact hN (hq.notin hp hl)
  chk x y u v hp hl hu := by
    rw [hpend] at hp; rw [hloc] at hl
    obtain ⟨S₁, S₂, hsplit, hst, hpr⟩ := hq.chk x y u v hp hl (hroot u hu)
    obtain ⟨S₁', S₂', h1, h2, h3⟩ := hS S₁ S₂ hsplit
    have hi := hinv (by rw [hp]; simp)
    refine ⟨S₁', S₂', h1, by rw [h2]; exact hst, fun z hz => ?_⟩
    rw [hcur]
    rcases h3 z hz with h | h
    · exact hprec _ hi (hpr z h)
    · exact h

/-- `L` unchanged. -/
lemma transport_same {α' : List (Label P (dsu E))} {L : List (OpId P × (dsu E).Op)} {c : OpId P} :
    (∀ L₁ L₂ (o : (dsu E).Op), L = L₁ ++ (c, o) :: L₂ →
      ∃ L₁' L₂', L = L₁' ++ (c, o) :: L₂' ∧ st L₁' = st L₁) ∧
    (∀ S₁ S₂, L = S₁ ++ S₂ → ∃ S₁' S₂', L = S₁' ++ S₂' ∧ st S₁' = st S₁ ∧
      ∀ z ∈ S₂', z ∈ S₂ ∨ ¬ Precedes α' z.1 c) :=
  ⟨fun L₁ L₂ _ h => ⟨L₁, L₂, h, rfl⟩, fun S₁ S₂ h => ⟨S₁, S₂, h, rfl, fun _ hz => Or.inl hz⟩⟩

/-- `L` extended by a new operation `x` that has not completed. -/
lemma transport_append {α' : List (Label P (dsu E))} {L : List (OpId P × (dsu E).Op)} {c x : OpId P}
    (o' : (dsu E).Op) (hx : ¬ Completed α' x) :
    (∀ L₁ L₂ (o : (dsu E).Op), L = L₁ ++ (c, o) :: L₂ →
      ∃ L₁' L₂', L ++ [(x, o')] = L₁' ++ (c, o) :: L₂' ∧ st L₁' = st L₁) ∧
    (∀ S₁ S₂, L = S₁ ++ S₂ → ∃ S₁' S₂', L ++ [(x, o')] = S₁' ++ S₂' ∧ st S₁' = st S₁ ∧
      ∀ z ∈ S₂', z ∈ S₂ ∨ ¬ Precedes α' z.1 c) := by
  refine ⟨fun L₁ L₂ _ h => ⟨L₁, L₂ ++ [(x, o')], by simp [h], rfl⟩,
    fun S₁ S₂ h => ⟨S₁, S₂ ++ [(x, o')], by simp [h], rfl, fun z hz => ?_⟩⟩
  rcases List.mem_append.1 hz with hz | hz
  · exact Or.inl hz
  · simp only [List.mem_singleton] at hz; subst hz
    exact Or.inr (fun h => hx h.completed)

/-- `L = W₁ ++ W₂` with a read-only operation `x` inserted between `W₁` and `W₂`. -/
lemma transport_insert {α' : List (Label P (dsu E))} {W₁ W₂ : List (OpId P × (dsu E).Op)}
    {c x : OpId P} (a b : E) (hx : ¬ Completed α' x) :
    (∀ L₁ L₂ (o : (dsu E).Op), W₁ ++ W₂ = L₁ ++ (c, o) :: L₂ →
      ∃ L₁' L₂', W₁ ++ (x, (.sameSet a b : (dsu E).Op)) :: W₂ = L₁' ++ (c, o) :: L₂' ∧ st L₁' = st L₁) ∧
    (∀ S₁ S₂, W₁ ++ W₂ = S₁ ++ S₂ → ∃ S₁' S₂', W₁ ++ (x, (.sameSet a b : (dsu E).Op)) :: W₂ = S₁' ++ S₂' ∧
      st S₁' = st S₁ ∧ ∀ z ∈ S₂', z ∈ S₂ ∨ ¬ Precedes α' z.1 c) := by
  refine ⟨fun L₁ L₂ o h => ?_, fun S₁ S₂ h => ?_⟩
  · obtain ⟨L₁', L₂', h1, h2⟩ := split_cons_insert h.symm (x, (DSUOp.sameSet a b : (dsu E).Op))
    refine ⟨L₁', L₂', h1, ?_⟩
    rcases h2 with h2 | ⟨A, B, rfl, rfl⟩
    · rw [h2]
    · exact st_insert A B x a b
  · obtain ⟨S₁', S₂', h1, h2, -, h4⟩ := split_insert h.symm (x, (DSUOp.sameSet a b : (dsu E).Op))
    refine ⟨S₁', S₂', h1, ?_, fun z hz => ?_⟩
    · rcases h4 with h4 | ⟨A, B, rfl, rfl⟩
      · rw [h4]
      · exact st_insert A B x a b
    · rcases h2 z hz with h | h
      · exact Or.inl h
      · subst h; exact Or.inr (fun h => hx h.completed)

/-! ### The invariant holds along every execution -/

lemma act_ret_cases {l : Loc E} {r : Bool} {l' : Loc E} (h : act K key l = .ret r l') :
    l = .done r ∨ l = .idle := by
  cases l with
  | idle => right; rfl
  | done r' => left; simp only [act] at h; cases h; rfl
  | fu b fs v => simp only [act, liftF] at h; split at h <;> cases h
  | fv b u fs => simp only [act, liftF] at h; split at h <;> cases h
  | chk u v => simp [act] at h
  | lnk u v => simp only [act] at h; split_ifs at h

lemma linInv_nil : LinInv ([] : List (Label P (dsu E))) (dsuImpl K key P).initCfg [] := by
  refine ⟨isLinearization_nil, ?_, fun q => ⟨?_, ?_, ?_⟩⟩
  · funext a b
    show (a = b) = ((fun a : E => a)^[Fintype.card E] a = (fun a : E => a)^[Fintype.card E] b)
    rw [Function.iterate_fixed rfl, Function.iterate_fixed rfl]
  · intro o r hp; simp [Impl.initCfg] at hp
  · intro hp; simp [Impl.initCfg] at hp
  · intro x y u v hp; simp [Impl.initCfg] at hp

/-- **The linearization invariant holds after every finite execution.** -/
theorem exists_linInv (hkey : Function.Injective key) {α : List (Label P (dsu E))}
    {C : Config (dsu E) (Ptr E) P (Loc E)} (h : (dsuImpl K key P).run α = some C) :
    ∃ L, LinInv α C L := by
  refine Impl.run_induction (Q := fun α C => ∃ L, LinInv α C L) ⟨[], linInv_nil⟩ ?_ h
  rintro α C₀ ℓ C hα ⟨L, hL⟩ h
  have hI : LInv K key C₀ := linv_of_run hkey hα
  have hinv : ∀ q, C₀.pend q ≠ none → Invoked α (curOp α q) := by
    intro q hq
    obtain ⟨o', ho'⟩ := Option.ne_none_iff_exists'.1 hq
    exact (Impl.run_pend_curOp hα ho').1
  have hprec : ∀ (β : List (Label P (dsu E))) q a, Invoked α (curOp α q) →
      ¬ Precedes α a (curOp α q) → ¬ Precedes (α ++ β) a (curOp α q) :=
    fun β q a hi hn => not_precedes_append hi hn
  cases ℓ with
  | inv p o =>
    obtain ⟨h0, -, hpend, hloc, hmem⟩ := Impl.step_inv h
    have hcur : ∀ q, curOp (α ++ [.inv p o]) q = curOp α q := by
      intro q; simp [curOp, respsOf_append]
    refine ⟨L, hL.lin.append_inv p o, by rw [hmem]; exact hL.state, fun q => ?_⟩
    by_cases hq : q = p
    · subst hq
      have hl : C.loc q = invoke K (C₀.loc q) o := by
        rw [hloc, Function.update_self]; rfl
      refine ⟨fun o' r _ hl' => ?_, fun _ _ => ?_, fun x y u v _ hl' => ?_⟩
      · rw [hl] at hl'; cases o <;> simp [invoke] at hl'
      · rw [hcur]
        exact fun hm => Impl.not_invoked_curOp_of_idle hα h0 (hL.lin.mem_invoked hm)
      · rw [hl] at hl'; cases o <;> simp [invoke] at hl'
    · exact (hL.qok q).transport (hcur q) (by rw [hpend, Function.update_of_ne hq])
        (by rw [hloc, Function.update_of_ne hq]) (fun a ha => by rwa [hmem] at ha) (hinv q)
        (hprec _ q) (transport_same (α' := α ++ [.inv p o])).1
        (transport_same (α' := α ++ [.inv p o])).2 id
  | ret p r =>
    obtain ⟨h0, hpend, hmem, l, hact, hloc⟩ := Impl.step_ret h
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 h0
    have hact' : act K key (C₀.loc p) = .ret r l := hact
    have hlp : C₀.loc p = .done r := by
      rcases act_ret_cases hact' with h1 | h1
      · exact h1
      · have := hI.loc p; rw [ho, h1] at this; exact this.elim
    obtain ⟨L₁, L₂, hsplit, hr⟩ := (hL.qok p).done o r ho hlp
    refine ⟨L, hL.lin.append_ret L₁ L₂ o hsplit hr, by rw [hmem]; exact hL.state,
      fun q => ?_⟩
    by_cases hq : q = p
    · subst hq
      have hpq : C.pend q = none := by rw [hpend, Function.update_self]
      refine ⟨fun o' r' hp _ => ?_, fun hp _ => absurd hpq hp, fun x y u v hp _ _ => ?_⟩
      · rw [hpq] at hp; cases hp
      · rw [hpq] at hp; cases hp
    · have hcur : curOp (α ++ [.ret p r]) q = curOp α q := by
        simp [curOp, respsOf_append, Ne.symm hq]
      exact (hL.qok q).transport hcur (by rw [hpend, Function.update_of_ne hq])
        (by rw [hloc, Function.update_of_ne hq]) (fun a ha => by rwa [hmem] at ha) (hinv q)
        (hprec _ q) (transport_same (α' := α ++ [.ret p r])).1
        (transport_same (α' := α ++ [.ret p r])).2 id
  | tau p =>
    obtain ⟨hp, hres, hpend, hother⟩ := step_tau_tauRes h
    obtain ⟨o, ho⟩ := Option.ne_none_iff_exists'.1 hp
    have hl := hI.loc p
    rw [ho] at hl
    have hleg := (tauRes_spec hkey hI.good hl hres).1
    have hcur : ∀ q, curOp (α ++ [.tau p]) q = curOp α q := by
      intro q; simp [curOp, respsOf_append]
    have hlin' := hL.lin.append_tau p
    have hcf := Impl.run_pend_curOp hα ho
    have hnc : ¬ Completed (α ++ [.tau p]) (curOp α p) := by
      simp [Completed, respsOf_append]
    have hop' : opOf (α ++ [.tau p]) (curOp α p) = some o := by
      rw [opOf_append_of_invoked hcf.1]; exact hcf.2.2
    have hldone : ∀ r, C₀.loc p ≠ .done r := fun r h' => by
      rw [h'] at hres; simp [tauRes, act] at hres
    have hnotin := (hL.qok p).notin (by rw [ho]; simp) hldone
    -- the processes that do not move
    have others : ∀ (L' : List (OpId P × (dsu E).Op)),
        (∀ q, q ≠ p → ∀ L₁ L₂ (o : (dsu E).Op), L = L₁ ++ (curOp α q, o) :: L₂ →
          ∃ L₁' L₂', L' = L₁' ++ (curOp α q, o) :: L₂' ∧ st L₁' = st L₁) →
        (∀ q, q ≠ p → ∀ S₁ S₂, L = S₁ ++ S₂ → ∃ S₁' S₂', L' = S₁' ++ S₂' ∧ st S₁' = st S₁ ∧
          ∀ z ∈ S₂', z ∈ S₂ ∨ ¬ Precedes (α ++ [.tau p]) z.1 (curOp α q)) →
        (∀ y ∈ L'.map Prod.fst, y ∈ L.map Prod.fst ∨ y = curOp α p) →
        ∀ q, q ≠ p → QOK (α ++ [.tau p]) C L' q := by
      intro L' hT hS hN q hq
      refine (hL.qok q).transport (hcur q) (by rw [hpend]) (hother q hq) hleg.root (hinv q)
        (hprec _ q) (hT q hq) (hS q hq) (fun hn hm => ?_)
      rcases hN _ hm with h1 | h1
      · exact hn h1
      · exact hq (congrArg Prod.fst h1)
    have hNsame : ∀ y ∈ L.map Prod.fst, y ∈ L.map Prod.fst ∨ y = curOp α p :=
      fun y hy => Or.inl hy
    have hNapp : ∀ y ∈ (L ++ [(curOp α p, o)]).map Prod.fst,
        y ∈ L.map Prod.fst ∨ y = curOp α p := by
      intro y hy
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
        List.mem_singleton] at hy
      exact hy
    rcases tauRes_cases hkey hI.good hl hres with
      ⟨hrun, hsame⟩ | ⟨u, r, x, y, rfl, hl', hm, hr, hux, hry, hur⟩ | ⟨hl', hm, hxy⟩ |
      ⟨u, v, x, y, rfl, hlc, hl', hm, hu⟩ | ⟨x, y, rfl, hl', hjoin⟩
    · -- no linearization point
      refine ⟨L, hlin', by rw [hL.state, hsame], fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        refine ⟨fun o' r' _ hl'' => ?_, fun _ _ => by rw [hcur]; exact hnotin,
          fun x y u v _ hl'' _ => ?_⟩
        · rw [hl''] at hrun; exact hrun.elim
        · rw [hl''] at hrun; exact hrun.elim
      · exact others L (fun q _ => (transport_same (α' := α ++ [.tau p])).1)
          (fun q _ => (transport_same (α' := α ++ [.tau p])).2) hNsame q hq
    · -- `SameSet` reaches line 8: record the cut
      refine ⟨L, hlin', by rw [hL.state, hm], fun q => ?_⟩
      by_cases hq : q = p
      · subst hq
        refine ⟨fun o' r' _ hl'' => ?_, fun _ _ => by rw [hcur]; exact hnotin,
          fun x' y' u' v' hp' hl'' hu' => ?_⟩
        · rw [hl''] at hl'; cases hl'
        · rw [hpend, ho] at hp'
          simp only [Option.some.injEq, DSUOp.sameSet.injEq] at hp'
          obtain ⟨rfl, rfl⟩ := hp'
          rw [hl''] at hl'
          simp only [Loc.chk.injEq] at hl'
          obtain ⟨rfl, rfl⟩ := hl'
          rw [hm] at hu'
          refine ⟨L, [], by simp, ?_, fun z hz => by simp at hz⟩
          rw [hL.state]
          intro hxy
          unfold same at hxy hux hry
          rw [rootOf_of_fixed hu'] at hux
          rw [rootOf_of_fixed hr] at hry
          exact hur (hux.trans (hxy.trans hry.symm))
      · exact others L (fun q _ => (transport_same (α' := α ++ [.tau p])).1)
          (fun q _ => (transport_same (α' := α ++ [.tau p])).2) hNsame q hq
    · -- linearization point: `u = v` found by the last `Find(v)`
      refine ⟨L ++ [(curOp α p, o)], hlin'.push hop' hnotin hnc, ?_, fun q => ?_⟩
      · rw [st_append, hm]
        cases o with
        | sameSet x y => exact hL.state
        | unite x y =>
          show joinRel (st L) x y = _
          rw [hL.state]; exact joinRel_same hxy
      · by_cases hq : q = p
        · subst hq
          refine ⟨fun o' r' hp' hl'' => ?_, fun _ hd => absurd hl' (hd true),
            fun x y u v _ hl'' _ => by rw [hl''] at hl'; cases hl'⟩
          rw [hpend, ho] at hp'; cases hp'
          rw [hl''] at hl'; cases hl'
          refine ⟨L, [], by rw [hcur], ?_⟩
          cases o with
          | sameSet x y =>
            show @decide (st L x y) (Classical.dec _) = true
            exact @decide_eq_true _ (Classical.dec _) (by rw [hL.state]; exact hxy)
          | unite x y => rfl
        · exact others _ (fun q _ => (transport_append o hnc).1)
            (fun q _ => (transport_append o hnc).2) hNapp q hq
    · -- `SameSet` returns `false`: retroactive linearization point
      obtain ⟨S₁, S₂, hsplit, hst, hpr⟩ := (hL.qok p).chk x y u v ho hlc hu
      subst hsplit
      refine ⟨S₁ ++ (curOp α p, .sameSet x y) :: S₂,
        hlin'.insert hop' hnotin hnc rfl
          (fun z hz => not_precedes_append hcf.1 (hpr z hz)), ?_, fun q => ?_⟩
      · rw [st_insert, hL.state, hm]
      · by_cases hq : q = p
        · subst hq
          refine ⟨fun o' r' hp' hl'' => ?_, fun _ hd => absurd hl' (hd false),
            fun x y u v _ hl'' _ => by rw [hl''] at hl'; cases hl'⟩
          rw [hpend, ho] at hp'; cases hp'
          rw [hl''] at hl'; cases hl'
          refine ⟨S₁, S₂, by rw [hcur], ?_⟩
          show @decide (st S₁ x y) (Classical.dec _) = false
          exact @decide_eq_false _ (Classical.dec _) hst
        · refine others _ (fun q _ => (transport_insert x y hnc).1)
            (fun q _ => (transport_insert x y hnc).2) (fun z hz => ?_) q hq
          simp only [List.map_append, List.map_cons, List.mem_append, List.mem_cons] at hz ⊢
          tauto
    · -- `Unite` links
      refine ⟨L ++ [(curOp α p, .unite x y)], hlin'.push hop' hnotin hnc, ?_, fun q => ?_⟩
      · rw [st_append]
        show joinRel (st L) x y = _
        rw [hL.state]
        funext a b
        exact propext (hjoin a b).symm
      · by_cases hq : q = p
        · subst hq
          refine ⟨fun o' r' hp' hl'' => ?_, fun _ hd => absurd hl' (hd true),
            fun x y u v _ hl'' _ => by rw [hl''] at hl'; cases hl'⟩
          rw [hpend, ho] at hp'; cases hp'
          rw [hl''] at hl'; cases hl'
          exact ⟨L, [], by rw [hcur], rfl⟩
        · exact others _ (fun q _ => (transport_append _ hnc).1)
            (fun q _ => (transport_append _ hnc).2) hNapp q hq

/-- **Lemma 3.2 (Linearizability).** The concurrent DSU (Algorithms 2 and 3) is linearizable
with any of the `Find` versions, for any injective node ids. Moreover, every execution has a
linearization whose abstract state is the partition of the elements into the trees of the
current parent forest. -/
theorem linearizable_with_state (hkey : Function.Injective key) {α : List (Label P (dsu E))}
    {C : Config (dsu E) (Ptr E) P (Loc E)} (h : (dsuImpl K key P).run α = some C) :
    ∃ L, IsLinearization α L ∧ linState L = fun a b => rootOf C.mem a = rootOf C.mem b := by
  obtain ⟨L, hL⟩ := exists_linInv hkey h
  exact ⟨L, hL.lin, hL.state⟩

/-- **Lemma 3.2 (Linearizability).** -/
theorem linearizable (hkey : Function.Injective key) : (dsuImpl K key P).Linearizable :=
  Impl.linearizable_of_run fun _ _ hC =>
    let ⟨L, hL⟩ := exists_linInv hkey hC
    ⟨L, hL.lin⟩

end Podc.ConcurrentDSU
