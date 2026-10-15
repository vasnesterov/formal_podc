import Papers.PODC2020.UndoableCRDTs.Group

/-!
# Counters and the tuple construction (Dolan, PODC 2020, Sections 1.1, 2.3, 2.6)

* The tuple of (undoable) CRDTs is an (undoable) CRDT (`CRDT.tuple`, `UndoableCRDT.tuple`).
* The counter modulo `n` is an undoable CRDT (`UndoableCRDT.modCounter`); `n = 0` gives the
  unbounded counter on `ℤ`.
* The group of actions of a tuple of counters `ZMod (m i)` is `∀ i, ZMod (m i)`, i.e. the direct
  sum of the cyclic groups `ℤ` / `ℤₙ` (Section 2.6): `UndoableCRDT.countersGroupEquiv`.
-/

namespace UndoableCRDTs

namespace OpSystem

section Tuple

variable {ι : Type w} [DecidableEq ι] (C : ι → OpSystem.{u, v})

lemma tuple_app (i : ι) (p : (C i).P) (s : (tuple C).S) :
    (tuple C).app ⟨i, p⟩ s = ((C i).app p (s i)).map (Function.update s i) := rfl

/-- An action of the `i`-th component, seen as an action of the tuple. -/
def liftAction (i : ι) (a : List (C i).P) : List (tuple C).P := a.map (Sigma.mk i)

lemma act_liftAction (i : ι) (a : List (C i).P) (s : (tuple C).S) :
    (tuple C).act s (liftAction C i a) = ((C i).act (s i) a).map (Function.update s i) := by
  induction a generalizing s with
  | nil => show some s = some _; rw [Function.update_eq_self]
  | cons p b ih =>
    change (tuple C).act s (⟨i, p⟩ :: liftAction C i b) = _
    rw [act_cons, tuple_app, act_cons]
    cases h : (C i).app p (s i) with
    | none => rfl
    | some t =>
      simp only [Option.map_some, Option.bind_some]
      rw [ih, Function.update_self]
      congr 1
      funext x
      exact Function.update_idem _ _ _

lemma ok_tuple_singleton_iff {i : ι} {p : (C i).P} {s : (tuple C).S} :
    (tuple C).Ok s [⟨i, p⟩] ↔ (C i).Ok (s i) [p] := by
  rw [ok_iff_isSome, ok_iff_isSome, act_singleton, act_singleton, tuple_app, Option.isSome_map]

lemma tuple_commutative (hc : ∀ i, (C i).Commutative) : (tuple C).Commutative := by
  rintro s ⟨i, p⟩ ⟨j, q⟩ hp hq
  rw [ok_tuple_singleton_iff] at hp hq
  obtain rfl | hij := eq_or_ne i j
  · obtain ⟨h1, h2, h3⟩ := hc i (s i) p q hp hq
    have e1 : ([⟨i, p⟩, ⟨i, q⟩] : List (tuple C).P) = liftAction C i [p, q] := rfl
    have e2 : ([⟨i, q⟩, ⟨i, p⟩] : List (tuple C).P) = liftAction C i [q, p] := rfl
    simp only [ok_iff_isSome] at h1 h2 ⊢
    rw [e1, e2, act_liftAction, act_liftAction, h3]
    simpa [Option.isSome_map] using h2
  · obtain ⟨t, ht⟩ := hp
    obtain ⟨u, hu⟩ := hq
    rw [act_singleton] at ht hu
    have k1 : (tuple C).act s [⟨i, p⟩, ⟨j, q⟩] =
        some (Function.update (Function.update s i t) j u) := by
      rw [act_cons, tuple_app, ht]
      show (tuple C).act (Function.update s i t) [⟨j, q⟩] = _
      rw [act_singleton, tuple_app, Function.update_of_ne hij.symm, hu]; rfl
    have k2 : (tuple C).act s [⟨j, q⟩, ⟨i, p⟩] =
        some (Function.update (Function.update s j u) i t) := by
      rw [act_cons, tuple_app, hu]
      show (tuple C).act (Function.update s j u) [⟨i, p⟩] = _
      rw [act_singleton, tuple_app, Function.update_of_ne hij, ht]; rfl
    refine ⟨ok_of_act k1, ok_of_act k2, ?_⟩
    rw [k1, k2, Function.update_comm hij]

lemma tuple_undoable (hu : ∀ i, (C i).Undoable) : (tuple C).Undoable := by
  rintro s ⟨i, p⟩ hp
  rw [ok_tuple_singleton_iff] at hp
  obtain ⟨qs, hqs⟩ := hu i (s i) p hp
  refine ⟨liftAction C i qs, ?_⟩
  change (tuple C).act s (liftAction C i (p :: qs)) = _
  rw [act_liftAction, hqs]
  simp

lemma tuple_reachable [Fintype ι] (hr : ∀ i, (C i).Reachable) : (tuple C).Reachable := by
  intro t
  choose a ha using fun i => hr i (t i)
  suffices H : ∀ L : List ι, L.Nodup → ∀ s : (tuple C).S, (∀ i ∈ L, s i = (C i).s0) →
      (tuple C).act s (L.flatMap fun i => liftAction C i (a i)) =
        some (fun j => if j ∈ L then t j else s j) by
    refine ⟨_, (H Finset.univ.toList (Finset.nodup_toList _) (tuple C).s0
      (fun _ _ => rfl)).trans ?_⟩
    simp
  intro L
  induction L with
  | nil => intro _ s _; simp; rfl
  | cons i L ih =>
    intro hnd s hs
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, act_append, act_liftAction, hs i List.mem_cons_self, ha i]
    simp only [Option.map_some, Option.bind_some]
    rw [ih hnd.2]
    · congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [hnd.1]
      · simp [hj]
    · intro j hj
      rw [Function.update_of_ne (by rintro rfl; exact hnd.1 hj)]
      exact hs j (List.mem_cons_of_mem _ hj)

end Tuple

section Counter

variable (n : ℕ)

lemma modCounter_app (p : CounterOp) (s : ZMod n) :
    (modCounter n).app p s = some (s + p.val) := rfl

lemma modCounter_act (s : ZMod n) (a : List CounterOp) :
    (modCounter n).act s a = some (s + (a.map (CounterOp.val (A := ZMod n))).sum) := by
  induction a generalizing s with
  | nil => simp; rfl
  | cons p b ih =>
    rw [act_cons_of _ (modCounter_app n p s), ih]
    simp [add_assoc]

lemma modCounter_commutative : (modCounter n).Commutative := by
  intro s p q _ _
  refine ⟨⟨_, modCounter_act n s _⟩, ⟨_, modCounter_act n s _⟩, ?_⟩
  rw [modCounter_act, modCounter_act]
  simp [add_comm]

lemma modCounter_undoable : (modCounter n).Undoable := by
  intro s p _
  refine ⟨[match p with | .inc => .dec | .dec => .inc], ?_⟩
  rw [modCounter_act]
  cases p <;> simp [CounterOp.val]

lemma modCounter_reachable : (modCounter n).Reachable := by
  have key : ∀ z : ℤ, ∃ a, (modCounter n).act 0 a = some (z : ZMod n) := by
    intro z
    induction z using Int.induction_on with
    | zero => exact ⟨[], by simp; rfl⟩
    | succ k ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a ++ [.inc], ?_⟩
      rw [act_append_of _ ha, act_singleton, modCounter_app]
      simp [CounterOp.val]
    | pred k ih =>
      obtain ⟨a, ha⟩ := ih
      refine ⟨a ++ [.dec], ?_⟩
      rw [act_append_of _ ha, act_singleton, modCounter_app]
      simp [CounterOp.val, sub_eq_add_neg]
  intro s
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective (n := n) s
  exact key z

end Counter

end OpSystem

open OpSystem

/-- The tuple of a finite family of CRDTs (Section 2.3). -/
abbrev CRDT.tuple {ι : Type w} [Fintype ι] [DecidableEq ι] (C : ι → CRDT.{u, v}) :
    CRDT.{max w u, max w v} where
  toOpSystem := OpSystem.tuple fun i => (C i).toOpSystem
  finite := by
    have := fun i => (C i).finite
    exact inferInstanceAs (Finite (Σ i, (C i).toOpSystem.P))
  reachable := tuple_reachable _ fun i => (C i).reachable
  comm := tuple_commutative _ fun i => (C i).comm

/-- The tuple of a finite family of undoable CRDTs is undoable. -/
abbrev UndoableCRDT.tuple {ι : Type w} [Fintype ι] [DecidableEq ι] (C : ι → UndoableCRDT.{u, v}) :
    UndoableCRDT.{max w u, max w v} where
  toCRDT := CRDT.tuple fun i => (C i).toCRDT
  undo := tuple_undoable _ fun i => (C i).undo

/-- The counter modulo `n` (Section 1.1) as an undoable CRDT; for `n = 0` the unbounded
counter (`ZMod 0 = ℤ`). -/
abbrev UndoableCRDT.modCounter (n : ℕ) : UndoableCRDT.{0, 0} where
  toOpSystem := OpSystem.modCounter n
  finite := inferInstanceAs (Finite CounterOp)
  reachable := modCounter_reachable n
  comm := modCounter_commutative n
  undo := modCounter_undoable n

/-- The unbounded counter has states `ℤ`. -/
example : (UndoableCRDT.modCounter 0).S = ℤ := rfl

namespace UndoableCRDT

variable {ι : Type} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)

/-- A tuple of counter and modulo-counter CRDTs: the `i`-th component counts modulo `m i`
(unbounded if `m i = 0`). -/
abbrev counters : UndoableCRDT.{0, 0} := UndoableCRDT.tuple fun i => modCounter (m i)

lemma counters_toOpSystem :
    (counters m).toOpSystem = OpSystem.tuple fun i => OpSystem.modCounter (m i) := rfl

/-- The displacement of a primitive operation of `counters m`. -/
def countersVal (x : (counters m).P) : ∀ i, ZMod (m i) := Pi.single x.1 x.2.val

lemma counters_act (s : ∀ i, ZMod (m i)) (a : List (counters m).P) :
    (counters m).toOpSystem.act s a = some (s + (a.map (countersVal m)).sum) := by
  induction a generalizing s with
  | nil => simp
  | cons x b ih =>
    obtain ⟨i, p⟩ := x
    have : (counters m).toOpSystem.app ⟨i, p⟩ s = some (s + countersVal m ⟨i, p⟩) := by
      change ((OpSystem.modCounter (m i)).app p (s i)).map (Function.update s i) = _
      rw [modCounter_app, Option.map_some]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj; simp [countersVal]
      · simp [countersVal, hj]
    rw [act_cons_of _ this, ih]
    simp [add_assoc]

/-- **Section 2.6**: the group of actions of a tuple of counters modulo `m i` is the direct sum
`∀ i, ZMod (m i)` of cyclic groups. -/
noncomputable def countersGroupEquiv : (counters m).G (counters m).s0 ≃+ ∀ i, ZMod (m i) where
  toEquiv := (counters m).stateEquiv
  map_add' x y := by
    induction x using G.ind with | h a ha => induction y using G.ind with | h b hb =>
    have key : ∀ (c : List (counters m).P) (hc : (counters m).toOpSystem.Ok (counters m).s0 c),
        ((counters m).stateEquiv (G.mk c hc) : ∀ i, ZMod (m i)) = (c.map (countersVal m)).sum := by
      intro c hc
      apply Option.some_injective
      rw [stateEquiv_apply, ← act_eq_eval]
      exact (counters_act m 0 c).trans (by simp)
    change ((counters m).stateEquiv (G.mk (a ++ b) _) : ∀ i, ZMod (m i)) =
      ((counters m).stateEquiv (G.mk a ha) : ∀ i, ZMod (m i)) +
        ((counters m).stateEquiv (G.mk b hb) : ∀ i, ZMod (m i))
    rw [key, key, key, List.map_append, List.sum_append]

end UndoableCRDT

end UndoableCRDTs
