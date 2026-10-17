import Papers.PODC2026.ConsistentRefereeing.Defs
import Podc.SharedMemory.StrongLin.OneAccess
import Podc.SharedMemory.ObjClasses.Basic

/-!
# Theorem 4: a strongly linearizable contest object from an `(n − 1)`-window register

Theorem 4 of Attiya, Castañeda, Enea, *Impossibility Results for Strong Linearizability: The
Difficulty of Consistent Refereeing* (PODC 2026): there is a wait-free strongly linearizable
implementation of the one-shot contest object from one `(n − 1)`-window register, where
`n = Fintype.card P` is the number of processes.

The algorithm: the window register `X` is initially empty (`⊥`). A competitor `p` invoking
`compete` writes its identifier into `X`; the referee invoking `decide` reads `X` and returns the
first (oldest) identifier of the window (`false`, i.e. `winner none`, if the window is empty).

In our model every process may invoke its operation any number of times (the contest object is
one-shot in the paper; we prove strong linearizability on *all* executions). To keep the window
from overflowing, a competitor writes only at its first `compete` and remembers that in a
persistent local bit; its later `compete`s read `X` and ignore the result. Every operation
accesses the register exactly once, so the implementation is a single-access implementation
(`OneAccess`), linearized at the access. Abstraction relation: the window is a duplicate-free
list of competitors, it contains exactly the competitors that have written, and the contest
state (the first competitor) is its head. Since at most `n − 1` distinct competitors write,
the window never overflows (`windowContest_sim`).

This shows that the bound `n − 2` of Theorem 5 is tight: `windowContest_hyps` checks that this
implementation satisfies all hypotheses of Theorem 5 except that its window is `n − 1`, and
`windowObj_not_windowLike` that an `(n − 1)`-window register is not `(n − 2)`-window-like.
-/

namespace Cslib.SharedMemory

namespace Referee

variable {P : Type} [DecidableEq P] [Fintype P]

/-- The single-access scheme of the algorithm of Theorem 4. The local datum records whether the
process has already written. -/
def windowScheme (ref : P) :
    OneAccess (contestObj P) (fun _ : Unit => windowObj P (Fintype.card P - 1)) P Bool where
  memInit _ := []
  dInit _ := false
  obj _ _ _ := ()
  prim _ d o := match o with
    | .compete i => if d then .read else .write i
    | .decide => .read
  upd _ d o _ := match o with
    | .compete _ => true
    | .decide => d
  out _ _ o r := match o with
    | .compete _ => .ok
    | .decide => .winner r.head?
  allowed p o := o = roleOp ref p

/-- The implementation of Theorem 4. -/
def windowContest (ref : P) :
    Impl (contestObj P) (fun _ : Unit => windowObj P (Fintype.card P - 1)) P (OALoc Bool
      (contestObj P)) :=
  (windowScheme ref).impl .ok

/-- The abstraction relation: the window `m ()` is a duplicate-free list of competitors, contains
exactly the competitors that have written, and its head is the contest state. -/
def windowAbs (ref : P) (m : (_ : Unit) → (windowObj P (Fintype.card P - 1)).State)
    (ds : P → Bool) (s : Option P) : Prop :=
  (m ()).Nodup ∧ ref ∉ m () ∧ (∀ x, x ≠ ref → (x ∈ m () ↔ ds x = true)) ∧ s = (m ()).head?

omit [Fintype P] in
@[simp] private lemma roleOp_self (ref : P) : roleOp ref ref = .decide := by simp [roleOp]

omit [Fintype P] in
@[simp] private lemma roleOp_of_ne {ref p : P} (h : p ≠ ref) : roleOp ref p = .compete p := by
  simp [roleOp, h]

omit [DecidableEq P] in
/-- The window never overflows: a duplicate-free list of competitors has at most `n − 1`
elements. -/
private lemma length_le_of_nodup {ref : P} {l : List P} (hl : l.Nodup) (hr : ref ∉ l) :
    l.length + 1 ≤ Fintype.card P := by
  have := (List.nodup_cons.2 ⟨hr, hl⟩).length_le_card
  simpa using this

lemma windowContest_sim (ref : P) : (windowScheme ref).Sim (windowAbs ref) := by
  refine ⟨⟨List.nodup_nil, by simp [windowScheme], fun x _ => by simp [windowScheme], rfl⟩, ?_⟩
  intro m ds s p d o hd habs hal
  obtain ⟨hnd, href, hmem, hs⟩ := habs
  simp only [windowScheme] at hal
  subst hal
  by_cases hp : p = ref
  · subst hp
    simp only [roleOp_self, windowScheme]
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simpa using hnd
    · simpa using href
    · intro x hx
      by_cases hxp : x = p
      · exact absurd hxp hx
      · simp [Function.update_of_ne hxp, hmem x hx]
    · simpa using hs
    · simp [hs]
  · simp only [roleOp_of_ne hp, windowScheme]
    cases d with
    | true =>
      have hpm : p ∈ m () := (hmem p hp).2 hd
      obtain ⟨a, l, hal⟩ : ∃ a l, m () = a :: l := by
        cases h : m () with
        | nil => simp [h] at hpm
        | cons a l => exact ⟨a, l, rfl⟩
      refine ⟨⟨?_, ?_, ?_, ?_⟩, trivial⟩
      · simpa using hnd
      · simpa using href
      · intro x hx
        by_cases hxp : x = p
        · subst hxp; simp [hpm]
        · simp [Function.update_of_ne hxp, hmem x hx]
      · simp [hs, hal]
    | false =>
      have hpm : p ∉ m () := fun h => by simpa [hd] using (hmem p hp).1 h
      have hlen := length_le_of_nodup (ref := ref) (List.nodup_cons.2 ⟨hpm, hnd⟩)
        (by simpa [Ne.symm hp] using href)
      simp only [List.length_cons] at hlen
      have hdrop : (m ()).length + 1 - (Fintype.card P - 1) = 0 := by omega
      simp only [hdrop, List.drop_zero]
      refine ⟨⟨?_, ?_, ?_, ?_⟩, trivial⟩
      · simp only [Function.update_self, Bool.false_eq_true, ↓reduceIte]
        exact List.nodup_append.2 ⟨hnd, List.nodup_singleton _,
          fun a ha b hb hab => by simp at hb; subst hb hab; exact hpm ha⟩
      · simp only [Function.update_self, Bool.false_eq_true, ↓reduceIte, List.mem_append,
          List.mem_singleton, not_or]
        exact ⟨href, Ne.symm hp⟩
      · intro x hx
        by_cases hxp : x = p
        · subst hxp; simp
        · simp [hmem x hx, hxp]
      · simp [hs, List.head?_append]

/-- **Theorem 4 of [ACE26].** For any number `n = Fintype.card P` of processes and any referee
`ref`, there is a wait-free strongly linearizable implementation of the contest object from a
single `(n − 1)`-window register (in which every process may invoke exactly the operation of its
role: `compete` for competitors, `decide` for the referee). Strong linearizability holds on all
executions, not only on the one-shot executions of the paper. -/
theorem theorem4 (ref : P) :
    ∃ (L : Type) (I : Impl (contestObj P)
      (fun _ : Unit => windowObj P (Fintype.card P - 1)) P L),
      (∀ p o, I.allowed p o ↔ o = roleOp ref p) ∧ I.WaitFree ∧ I.StronglyLinearizable :=
  ⟨_, windowContest ref, fun _ _ => Iff.rfl, (windowScheme ref).waitFree _,
    (windowScheme ref).stronglyLinearizable (windowContest_sim ref) _⟩

/-- Non-vacuity of Theorem 5: the implementation of Theorem 4 satisfies all hypotheses of
Theorem 5 except the window size — its only base object is an `(n − 1)`-window register
(window-like with window `n − 1`). -/
theorem windowContest_hyps (ref : P) :
    (∀ p, (windowContest ref).allowed p (roleOp ref p)) ∧
    (windowContest ref).LockFreeOn (Adm ref) ∧ (windowContest ref).StrongLinOn (Adm ref) ∧
    ∀ _ : Unit, (windowObj P (Fintype.card P - 1)).WindowLike (Fintype.card P - 1) := by
  refine ⟨fun p => rfl, ?_, ?_, fun _ => windowObj_windowLike P le_rfl⟩
  · exact Impl.WaitFreeOn.lockFreeOn (((windowScheme ref).waitFree _).waitFreeOn _)
      (fun α h => h.oneShot)
  · exact ((windowScheme ref).stronglyLinearizable (windowContest_sim ref) _).strongLinOn _

/-- An `(n − 1)`-window register is not `(n − 2)`-window-like (for `n ≥ 3`): `n − 2` writes from
the empty window and from a window with one element lead to windows of different lengths. Hence
Theorem 4 does not contradict Theorem 5, and the bound of Theorem 5 is tight. -/
theorem windowObj_not_windowLike {V : Type} (v : V) {n : ℕ} (hn : 3 ≤ n) :
    ¬ (windowObj V (n - 1)).WindowLike (n - 2) := by
  intro h
  have key := h.2 (List.replicate (n - 2) (.write v)) (by simp; omega) (by simp)
    (fun o ho => by
      rw [List.eq_of_mem_replicate ho]; intro hro; have := hro []; simp at this; omega) [] [v]
  obtain ⟨k, hk⟩ : ∃ k, n - 2 = k + 1 := ⟨n - 3, by omega⟩
  rw [hk, List.replicate_succ, show (List.replicate k (WinOp.write v) : List (windowObj V
    (n - 1)).Op) = (List.replicate k v).map WinOp.write by simp [List.map_replicate],
    ← List.map_cons, windowObj_runOps_writes, windowObj_runOps_writes] at key
  have := congrArg List.length key
  simp at this
  omega

end Referee

end Cslib.SharedMemory
