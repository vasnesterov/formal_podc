import Cslib.Computability.Distributed.SharedMemory.StrongLin
import Cslib.Computability.Distributed.SharedMemory.Linearization

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/WriteStrongLin.lean

/-!
# Strong linearizability with respect to a subset of operations

Hadzilacos, Hu and Toueg (PODC 2021) introduce *write strong-linearizability*: a linearization
function `h` is a *write strong-linearization function* if, whenever the execution `α` is a prefix
of the execution `β`, the sequence of **write** operations of `h α` is a prefix of the sequence of
write operations of `h β` (reads may be linearized "off-line"). More generally, an implementation
is *strongly linearizable with respect to a set `O` of operations* if the order of the operations
in `O` is fixed on-line.

* `Impl.IsStrongLinFunFor O h`, `Impl.StronglyLinearizableFor O` — strong linearizability with
  respect to the operations satisfying `O : A.Op → Bool`;
* `RWOp.isWrite`, `Impl.WriteStronglyLinearizable` — the case of read/write registers;
* `Impl.StronglyLinearizable.stronglyLinearizableFor`,
  `Impl.StronglyLinearizableFor.linearizable` — strong linearizability ⇒ strong linearizability
  for `O` ⇒ linearizability.

## Restricting linearizations to prefixes

`IsLinearization.restrict`: if `L` is a linearization of `α ++ γ`, then the entries of `L` that
are invoked in `α` form a linearization of `α`. (Entries invoked in `γ` come after every operation
completed in `α`, so dropping them does not change the response of any completed operation of `α`.)
In particular every prefix of a linearizable history is linearizable
(`IsLinearization.exists_of_prefix`).
-/

namespace Cslib.SharedMemory

open List

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

/-! ## Definitions -/

/-- The entries of a sequential history whose operation satisfies `O`. -/
def opsFor {Op : Type} (O : Op → Bool) (S : List (OpId P × Op)) : List (OpId P × Op) :=
  S.filter (fun y => O y.2)

lemma opsFor_append {Op : Type} (O : Op → Bool) (S S' : List (OpId P × Op)) :
    opsFor O (S ++ S') = opsFor O S ++ opsFor O S' := by
  simp [opsFor]

lemma opsFor_prefix {Op : Type} {O : Op → Bool} {S S' : List (OpId P × Op)} (h : S <+: S') :
    opsFor O S <+: opsFor O S' := by
  obtain ⟨T, rfl⟩ := h
  rw [opsFor_append]; exact prefix_append _ _

/-- A register operation is a write. -/
def RWOp.isWrite {V : Type} : RWOp V → Bool
  | .read => false
  | .write _ => true

@[simp] lemma RWOp.isWrite_read {V : Type} : (RWOp.read : RWOp V).isWrite = false := rfl
@[simp] lemma RWOp.isWrite_write {V : Type} (v : V) : (RWOp.write v).isWrite = true := rfl

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- A *strong linearization function with respect to `O`*: a linearization function such that,
if `α` is a prefix of the execution `β`, the operations satisfying `O` in `h α` form a prefix of
those in `h β`. -/
def IsStrongLinFunFor (O : A.Op → Bool) (h : List (Label P A) → List (OpId P × A.Op)) : Prop :=
  I.IsLinFun h ∧ ∀ α β, I.Valid β → α <+: β → opsFor O (h α) <+: opsFor O (h β)

/-- The implementation is strongly linearizable with respect to the operations satisfying `O`. -/
def StronglyLinearizableFor (O : A.Op → Bool) : Prop := ∃ h, I.IsStrongLinFunFor O h

/-- A *write strong-linearization function* (Definition 4 of Hadzilacos–Hu–Toueg, PODC 2021). -/
abbrev IsWriteStrongLinFun {V : Type} {v₀ : V} (I : Impl (register V v₀) B P L)
    (h : List (Label P (register V v₀)) → List (OpId P × RWOp V)) : Prop :=
  I.IsStrongLinFunFor RWOp.isWrite h

/-- A register implementation is *write strongly-linearizable* (Definition 5 of
Hadzilacos–Hu–Toueg, PODC 2021). -/
abbrev WriteStronglyLinearizable {V : Type} {v₀ : V} (I : Impl (register V v₀) B P L) : Prop :=
  I.StronglyLinearizableFor RWOp.isWrite

variable {I}

theorem IsStrongLinFun.isStrongLinFunFor {h : List (Label P A) → List (OpId P × A.Op)}
    (hh : I.IsStrongLinFun h) (O : A.Op → Bool) : I.IsStrongLinFunFor O h :=
  ⟨hh.1, fun α β hβ hαβ => opsFor_prefix (hh.2 α β hβ hαβ)⟩

/-- Strong linearizability implies strong linearizability with respect to any `O`. -/
theorem StronglyLinearizable.stronglyLinearizableFor (hI : I.StronglyLinearizable)
    (O : A.Op → Bool) : I.StronglyLinearizableFor O := by
  obtain ⟨h, hh⟩ := hI; exact ⟨h, hh.isStrongLinFunFor O⟩

/-- Strong linearizability with respect to `O` implies linearizability. -/
theorem StronglyLinearizableFor.linearizable {O : A.Op → Bool}
    (hI : I.StronglyLinearizableFor O) : I.Linearizable := by
  obtain ⟨h, hh, -⟩ := hI; exact ⟨h, hh⟩

/-- Strong linearizability with respect to all operations is strong linearizability. -/
theorem stronglyLinearizableFor_true_iff :
    I.StronglyLinearizableFor (fun _ => true) ↔ I.StronglyLinearizable := by
  have hO : ∀ S : List (OpId P × A.Op), opsFor (fun _ : A.Op => true) S = S := fun S => by
    simp [opsFor]
  constructor
  · rintro ⟨h, hh, hp⟩; exact ⟨h, hh, fun α β hβ hαβ => by simpa [hO] using hp α β hβ hαβ⟩
  · intro hI; exact hI.stronglyLinearizableFor _

end Impl

/-! ## Restricting a linearization to a prefix -/

section Restrict

variable [DecidableEq P]

instance (α : List (Label P A)) (x : OpId P) : Decidable (Invoked α x) :=
  inferInstanceAs (Decidable (_ < _))

instance (α : List (Label P A)) (x : OpId P) : Decidable (Completed α x) :=
  inferInstanceAs (Decidable (_ < _))

/-- Real-time precedence, decidably: `a` precedes `b` iff some prefix of `α` completes `a` without
invoking `b`. -/
lemma precedes_iff_take {α : List (Label P A)} {a b : OpId P} :
    Precedes α a b ↔
      ∃ k ∈ range (α.length + 1), Completed (α.take k) a ∧ ¬ Invoked (α.take k) b := by
  constructor
  · rintro ⟨β, γ, rfl, h1, h2⟩
    refine ⟨β.length, by simp; omega, ?_⟩
    simpa using ⟨h1, h2⟩
  · rintro ⟨k, -, h1, h2⟩
    exact ⟨α.take k, α.drop k, (take_append_drop k α).symm, h1, h2⟩

instance (α : List (Label P A)) (a b : OpId P) : Decidable (Precedes α a b) :=
  decidable_of_iff _ precedes_iff_take.symm

lemma seqOK_of_forall_not_completed {α : List (Label P A)} (q : A.State)
    (S : List (OpId P × A.Op)) (h : ∀ y ∈ S, ¬ Completed α y.1) : SeqOK α q S := by
  induction S generalizing q with
  | nil => trivial
  | cons y S ih =>
    obtain ⟨x, o⟩ := y
    refine ⟨fun r hr => absurd (Completed.of_respOf_eq_some hr) (h (x, o) (by simp)), ?_⟩
    exact ih _ (fun y hy => h y (by simp [hy]))

lemma sublist_pair_filter {X : Type} {p : X → Bool} {a b : X} {l : List X}
    (h : [a, b].Sublist l) (ha : p a) (hb : p b) : [a, b].Sublist (l.filter p) := by
  have := h.filter p
  simpa [ha, hb] using this

/-- Restriction of a linearization of `α ++ γ` to the operations invoked in `α`. -/
theorem IsLinearization.restrict {α γ : List (Label P A)} {S : List (OpId P × A.Op)}
    (hwf : WellFormed α) (hS : IsLinearization (α ++ γ) S) :
    IsLinearization α (S.filter (fun y => decide (Invoked α y.1))) := by
  have hmapfilter : (S.filter (fun y => decide (Invoked α y.1))).map Prod.fst =
      (S.map Prod.fst).filter (fun x => decide (Invoked α x)) := by
    rw [filter_map]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hmapfilter]; exact hS.nodup.filter _
  · intro y hy
    rw [mem_filter, decide_eq_true_eq] at hy
    rw [← opOf_append_of_invoked (β := γ) hy.2]
    exact hS.op_eq y hy.1
  · intro a ha
    rw [hmapfilter, mem_filter, decide_eq_true_eq]
    exact ⟨hS.complete a ha.mono, hwf.invoked_of_completed ha⟩
  · intro a b hab hb
    rw [hmapfilter] at hb ⊢
    rw [mem_filter, decide_eq_true_eq] at hb
    refine sublist_pair_filter (hS.realtime a b hab.mono hb.1) ?_ (by simpa using hb.2)
    simpa using hwf.invoked_of_completed hab.completed
  · -- the dropped entries come after all entries completed in `α`
    have key : ∀ (q : A.State) (T : List (OpId P × A.Op)), (T.map Prod.fst).Nodup →
        SeqOK (α ++ γ) q T →
        (∀ x ∈ T.map Prod.fst, ¬ Invoked α x → ∀ z ∈ T.map Prod.fst, Completed α z →
          [z, x].Sublist (T.map Prod.fst)) →
        SeqOK α q (T.filter (fun y => decide (Invoked α y.1))) := by
      intro q T
      induction T generalizing q with
      | nil => intros; trivial
      | cons y T ih =>
        obtain ⟨x, o⟩ := y
        intro hnd hseq hord
        rw [map_cons, nodup_cons] at hnd
        have hord' : ∀ x' ∈ T.map Prod.fst, ¬ Invoked α x' → ∀ z ∈ T.map Prod.fst,
            Completed α z → [z, x'].Sublist (T.map Prod.fst) := by
          intro x' hx' hn z hz hc
          have h1 := hord x' (by simp [hx']) hn z (by simp [hz]) hc
          rw [map_cons] at h1
          rcases sublist_cons_iff.1 h1 with h1 | ⟨r, hr, h1⟩
          · exact h1
          · injection hr with hr1 hr2
            subst hr1
            exact absurd hz hnd.1
        by_cases hx : Invoked α x
        · rw [filter_cons_of_pos (by simpa using hx)]
          refine ⟨fun r hr => hseq.1 r ?_, ih _ hnd.2 hseq.2 hord'⟩
          rw [respOf_append_of_completed (Completed.of_respOf_eq_some hr)]; exact hr
        · rw [filter_cons_of_neg (by simpa using hx)]
          apply seqOK_of_forall_not_completed
          intro y hy hc
          have hy' := (mem_filter.1 hy).1
          have h1 := hord x (by simp) hx y.1 (by simp [mem_map_of_mem hy']) hc
          rw [map_cons] at h1
          rcases sublist_cons_iff.1 h1 with h1 | ⟨r, hr, h1⟩
          · have := h1.subset (by simp : x ∈ [y.1, x]); exact hnd.1 this
          · cases hr
            exact hx (hwf.invoked_of_completed hc)
    refine key _ _ hS.nodup hS.seq ?_
    intro x hx hxn z hz hzc
    exact hS.realtime z x ⟨α, γ, rfl, hzc, hxn⟩ hx

/-- Every prefix of a linearizable history is linearizable. -/
theorem IsLinearization.exists_of_prefix {α β : List (Label P A)} {S : List (OpId P × A.Op)}
    (hwf : WellFormed β) (hS : IsLinearization β S) (h : α <+: β) :
    ∃ S', IsLinearization α S' ∧ S' = S.filter (fun y => decide (Invoked α y.1)) := by
  obtain ⟨γ, rfl⟩ := h
  exact ⟨_, hS.restrict hwf.of_append, rfl⟩

end Restrict

/-! ## Reads force the order of writes (registers) -/

section Register

variable [DecidableEq P] {V : Type} {v₀ : V}

/-- If an operation sequence of a register ends in a value `v` different from the starting value,
its last write writes `v`. -/
lemma register_runOps_eq {q v : V} (os : List (RWOp V))
    (h : (register V v₀).runOps q os = v) (hv : v ≠ q) :
    ∃ os₁ os₂, os = os₁ ++ .write v :: os₂ ∧ ∀ o ∈ os₂, o.isWrite = false := by
  induction os using List.reverseRecOn generalizing v with
  | nil => exact absurd h.symm hv
  | append_singleton os o ih =>
    rw [ObjSpec.runOps_append] at h
    cases o with
    | read =>
      obtain ⟨os₁, os₂, rfl, h2⟩ := ih h hv
      exact ⟨os₁, os₂ ++ [.read], by simp, by
        intro o ho; rcases mem_append.1 ho with ho | ho
        · exact h2 o ho
        · simp at ho; subst ho; rfl⟩
    | write x =>
      simp only [ObjSpec.runOps_cons, ObjSpec.runOps_nil, register_write] at h
      subst h
      exact ⟨os, [], rfl, by simp⟩

lemma register_runOps_eq_of_noWrite (q : V) (os : List (RWOp V))
    (h : ∀ o ∈ os, o.isWrite = false) : (register V v₀).runOps q os = q := by
  apply ObjSpec.runOps_of_readOnly
  intro o ho
  cases o with
  | read => intro q; rfl
  | write x => exact absurd (h _ ho) (by simp)

/-- The last entry of a list satisfying a predicate. -/
lemma exists_last_of_mem {X : Type} (p : X → Bool) {l : List X} {y : X} (hy : y ∈ l)
    (hp : p y = true) : ∃ T e R, l = T ++ e :: R ∧ p e = true ∧ ∀ z ∈ R, p z = false := by
  induction l using List.reverseRecOn with
  | nil => simp at hy
  | append_singleton l z ih =>
    by_cases hz : p z = true
    · exact ⟨l, z, [], by simp, hz, by simp⟩
    · rcases mem_append.1 hy with h | h
      · obtain ⟨T, e, R, h1, h2, h3⟩ := ih h
        refine ⟨T, e, R ++ [z], by simp [h1], h2, ?_⟩
        intro z' hz'; rcases mem_append.1 hz' with h' | h'
        · exact h3 z' h'
        · simp at h'; subst h'; simpa using hz
      · simp at h; subst h; exact absurd hp hz

/-- In a linearization, the response `v` of a completed read `r` is the value of the last write
before `r`; if `v` is not the initial value and `w` is the only operation of the linearization that
writes `v`, then every other write before `r` comes before `w` among the writes. -/
theorem IsLinearization.write_before_of_read {α : List (Label P (register V v₀))}
    {S : List (OpId P × RWOp V)} (hS : IsLinearization α S) {r : OpId P} {v : V}
    (hr : respOf α r = some v) (hrop : opOf α r = some .read) (hv : v ≠ v₀) {w : OpId P}
    (huniq : ∀ y ∈ S, y.2 = .write v → y.1 = w) {u : OpId P} {x : V}
    (hu : (u, .write x) ∈ S) (huw : u ≠ w) (hur : [u, r].Sublist (S.map Prod.fst)) :
    [(u, .write x), (w, .write v)].Sublist (opsFor RWOp.isWrite S) := by
  have hrS : r ∈ S.map Prod.fst := hur.subset (by simp)
  obtain ⟨⟨r', o⟩, hy, rfl⟩ := mem_map.1 hrS
  obtain ⟨S₁, S₂, rfl⟩ := append_of_mem hy
  have ho : o = .read := by
    have := hS.op_eq _ hy; rw [hrop] at this; exact (Option.some.inj this).symm
  subst ho
  have hseq := (seqOK_append (α := α) (register V v₀).init S₁ _).1 hS.seq
  have hq : (register V v₀).runOps v₀ (S₁.map Prod.snd) = v := by
    have := hseq.2.1 v hr; simpa using this
  obtain ⟨os₁, os₂, hsplit, hnw⟩ := register_runOps_eq _ hq hv
  obtain ⟨A₁, R₁, hA, hAm, hRm⟩ := map_eq_append_iff.1 hsplit
  obtain ⟨e, R, rfl, he, hRm'⟩ := map_eq_cons_iff.1 hRm
  subst hAm hRm'
  obtain ⟨ew, ev⟩ := e
  simp only at he; subst he
  have hew : ew = w := huniq (ew, .write v) (by rw [hA]; simp) rfl
  subst hew
  -- `u` is linearized before `r`
  have hnd := hS.nodup
  rw [map_append, map_cons] at hnd hur
  have hu₁ := mem_left_of_sublist_pair hnd hur
  obtain ⟨⟨u', x'⟩, hy', rfl⟩ := mem_map.1 hu₁
  have hx' : x' = .write x := by
    have h1 := hS.op_eq _ (mem_append_left _ hy')
    have h2 := hS.op_eq _ hu
    rw [h1] at h2; exact Option.some.inj h2
  subst hx'
  rw [hA] at hy'
  rw [hA]
  rcases mem_append.1 hy' with hy' | hy'
  · rw [opsFor_append, opsFor_append]
    have : (opsFor RWOp.isWrite A₁ ++ opsFor RWOp.isWrite ((ew, RWOp.write v) :: R)) <+
        (opsFor RWOp.isWrite A₁ ++ opsFor RWOp.isWrite ((ew, RWOp.write v) :: R)) ++
          opsFor RWOp.isWrite ((u', RWOp.read) :: S₂) := sublist_append_left _ _
    refine Sublist.trans ?_ this
    simp only [opsFor, filter_cons, RWOp.isWrite_write, ite_true]
    refine Sublist.trans (l₂ := [(u', RWOp.write x)] ++ [(ew, RWOp.write v)]) (by simp) ?_
    exact Sublist.append (singleton_sublist.2 (mem_filter.2 ⟨hy', rfl⟩)) (by simp)
  · rcases mem_cons.1 hy' with h | h
    · cases h; exact absurd rfl huw
    · have : (RWOp.write x : RWOp V).isWrite = false := hnw _ (mem_map.2 ⟨_, h, rfl⟩)
      simp at this

/-- In a linearization, if a completed read `r` returns `v ≠ v₀` and `w` is the only operation of
the linearization that writes `v`, then `w` is linearized before `r`. -/
theorem IsLinearization.writer_before_read {α : List (Label P (register V v₀))}
    {S : List (OpId P × RWOp V)} (hS : IsLinearization α S) {r : OpId P} {v : V}
    (hr : respOf α r = some v) (hrop : opOf α r = some .read) (hv : v ≠ v₀) {w : OpId P}
    (huniq : ∀ y ∈ S, y.2 = .write v → y.1 = w) (hrS : r ∈ S.map Prod.fst) :
    [w, r].Sublist (S.map Prod.fst) := by
  obtain ⟨⟨r', o⟩, hy, rfl⟩ := mem_map.1 hrS
  obtain ⟨S₁, S₂, rfl⟩ := append_of_mem hy
  have ho : o = .read := by
    have := hS.op_eq _ hy; rw [hrop] at this; exact (Option.some.inj this).symm
  subst ho
  have hseq := (seqOK_append (α := α) (register V v₀).init S₁ _).1 hS.seq
  have hq : (register V v₀).runOps v₀ (S₁.map Prod.snd) = v := by
    have := hseq.2.1 v hr; simpa using this
  obtain ⟨os₁, os₂, hsplit, -⟩ := register_runOps_eq _ hq hv
  obtain ⟨A₁, R₁, hA, -, hRm⟩ := map_eq_append_iff.1 hsplit
  obtain ⟨e, R, rfl, he, -⟩ := map_eq_cons_iff.1 hRm
  have hew : e.1 = w := huniq e (by rw [hA]; simp) he
  have hw : w ∈ S₁.map Prod.fst := by rw [hA, ← hew]; simp
  rw [map_append, map_cons]
  exact Sublist.append (l₁ := [w]) (singleton_sublist.2 hw)
    (cons_sublist_cons.2 (nil_sublist _))

/-- A completed read that returns the initial value `v₀`, if no operation of the linearization
writes `v₀`, comes before every write of the linearization. -/
theorem IsLinearization.read_before_of_init {α : List (Label P (register V v₀))}
    {S : List (OpId P × RWOp V)} (hS : IsLinearization α S) {r : OpId P}
    (hr : respOf α r = some v₀) (hrop : opOf α r = some .read)
    (hno : ∀ y ∈ S, y.2 ≠ .write v₀) (hrS : r ∈ S.map Prod.fst) {u : OpId P} {x : V}
    (hu : (u, .write x) ∈ S) : [r, u].Sublist (S.map Prod.fst) := by
  obtain ⟨⟨r', o⟩, hy, rfl⟩ := mem_map.1 hrS
  obtain ⟨S₁, S₂, rfl⟩ := append_of_mem hy
  have ho : o = .read := by
    have := hS.op_eq _ hy; rw [hrop] at this; exact (Option.some.inj this).symm
  subst ho
  have hseq := (seqOK_append (α := α) (register V v₀).init S₁ _).1 hS.seq
  have hq : (register V v₀).runOps v₀ (S₁.map Prod.snd) = v₀ := by
    have := hseq.2.1 v₀ hr; simpa using this
  -- `S₁` contains no write
  have hS₁ : ∀ y ∈ S₁, y.2.isWrite = false := by
    by_contra hc
    push_neg at hc
    obtain ⟨y, hy₁, hyw⟩ := hc
    -- the last write of `S₁` writes `v₀`
    have := exists_last_of_mem (fun z : OpId P × RWOp V => z.2.isWrite) hy₁ (by simpa using hyw)
    obtain ⟨T, ⟨e1, e2⟩, R, rfl, he, hR⟩ := this
    cases e2 with
    | read => simp at he
    | write z =>
      rw [map_append, map_cons, ObjSpec.runOps_append, ObjSpec.runOps_cons] at hq
      rw [register_runOps_eq_of_noWrite _ _ (by
        intro o ho; obtain ⟨z', hz', rfl⟩ := mem_map.1 ho; exact hR z' hz')] at hq
      simp only [register_write] at hq
      exact hno (e1, .write z) (by simp) (by rw [hq])
  have hu' : (u, RWOp.write x) ∈ (r', RWOp.read) :: S₂ := by
    rcases mem_append.1 hu with h | h
    · simpa using hS₁ _ h
    · exact h
  rcases mem_cons.1 hu' with h | h
  · cases h
  · rw [map_append, map_cons]
    refine Sublist.trans ?_ (sublist_append_right _ _)
    exact cons_sublist_cons.2 (singleton_sublist.2 (mem_map_of_mem h))

/-- If `l₁` is a prefix of the duplicate-free list `l₂`, `a` comes before `b` in `l₂` and `b` is
in `l₁`, then `a` comes before `b` in `l₁`. -/
lemma sublist_pair_of_prefix {X : Type} {l₁ l₂ : List X} {a b : X} (h : l₁ <+: l₂)
    (hnd : l₂.Nodup) (hab : [a, b].Sublist l₂) (hb : b ∈ l₁) : [a, b].Sublist l₁ := by
  obtain ⟨t, rfl⟩ := h
  have hbt : b ∉ t := fun hbt => by
    rw [nodup_append] at hnd; exact hnd.2.2 b hb b hbt rfl
  obtain ⟨x, y, hxy, hx, hy⟩ := sublist_append_iff.1 hab
  have hlen := congrArg length hxy
  simp only [length_cons, length_nil, length_append] at hlen
  have hylen : y.length ≤ 2 := by omega
  rcases y with _ | ⟨y₁, y⟩
  · rw [hxy]; simpa using hx
  · exfalso
    have : b ∈ y₁ :: y := by
      rcases x with _ | ⟨x₁, x⟩
      · simp only [nil_append] at hxy; rw [← hxy]; simp
      · simp only [cons_append, cons.injEq] at hxy
        rcases x with _ | ⟨x₂, x⟩
        · simp only [nil_append] at hxy; rw [← hxy.2]; simp
        · simp at hlen; omega
    exact hbt (hy.subset this)

/-- "Before" in a duplicate-free list is transitive. -/
lemma sublist_pair_trans {X : Type} {l : List X} {a b c : X} (hl : l.Nodup)
    (h₁ : [a, b].Sublist l) (h₂ : [b, c].Sublist l) : [a, c].Sublist l := by
  have hb : b ∈ l := h₁.subset (by simp)
  obtain ⟨A, B, rfl⟩ := append_of_mem hb
  have ha : a ∈ A := mem_left_of_sublist_pair hl h₁
  have hc : c ∈ B := by
    have h₂' : [c, b].Sublist (B.reverse ++ b :: A.reverse) := by
      have := reverse_sublist.2 h₂; simpa using this
    have hl' : (B.reverse ++ b :: A.reverse).Nodup := by
      have := (nodup_reverse.2 hl); simpa using this
    simpa using mem_left_of_sublist_pair hl' h₂'
  exact Sublist.append (l₁ := [a]) (singleton_sublist.2 ha)
    ((singleton_sublist.2 hc).cons b)

end Register

end Cslib.SharedMemory
