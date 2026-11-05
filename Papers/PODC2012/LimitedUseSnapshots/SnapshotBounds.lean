import Papers.PODC2012.LimitedUseSnapshots.SnapshotMain
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat

/-!
# Algorithm 3 is `(b − 1)`-limited-use: all indices stay below `b`

The paper builds Algorithm 3 from `MaxArray_{b×b}` objects, a `MaxReg_b` and `view` arrays of
length `b`, and claims that `b − 1` `Update`s can be performed. With the unbounded atomic objects
of `SnapshotDefs.lean` this is the statement that every value ever stored in a max array or in
`root.mr`, and every argument and index of a base-object access, is at most the number of
`Update`s invoked so far (`indices_le_updates`). Hence, if at most `b − 1` `Update`s are invoked,
all of them are `< b` (`limited_use`): the bounded objects of the paper behave exactly like the
unbounded ones (the paper's own argument: "the length of the array at a node is one greater than
the total number of updates that can be performed by processes whose components are in the
subtree rooted at that node").
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}

/-- `Update` operations. -/
def SOp.isUpd : SOp P V → Bool
  | .update _ _ => true
  | .scan => false

/-- The number of `Update`s invoked by `j` in `α`. -/
def updCount (α : List (Label P (swSnap P V v₀))) (j : P) : ℕ :=
  ((opsOf α j).filter SOp.isUpd).length

/-- The number of `Update`s invoked in `α` (all processes are leaves of `T`). -/
def nUpd (T : BTree P) (α : List (Label P (swSnap P V v₀))) : ℕ :=
  (T.leaves.map (updCount α)).sum

/-- `1` while the leaf write (Line 5) is pending, `0` otherwise. -/
def lwFlag (l : Loc P V) : ℕ :=
  match l.pc with
  | .lw _ => 1
  | _ => 0

omit [DecidableEq P] in
lemma lwFlag_cont (n : ℕ) (q : List Bool) (k : ℕ) : lwFlag (⟨n, cont q k⟩ : Loc P V) = 0 := by
  unfold cont; split_ifs <;> rfl

lemma act_access_flag {p : P} {l : Loc P V} {i : Obj} {o : (objSpec P V v₀ i).Op}
    {k : (objSpec P V v₀ i).Resp → Loc P V} (h : act T v₀ p l = .access i o k)
    (r : (objSpec P V v₀ i).Resp) : (k r).cnt + lwFlag (k r) = l.cnt + lwFlag l := by
  rcases l with ⟨n, pc⟩
  cases pc with
  | up a ptr => cases a <;> (simp only [act] at h; cases h; rfl)
  | lw v => simp only [act] at h; cases h; simp only [lwFlag_cont]; simp [lwFlag]
  | wv q k' val => simp only [act] at h; cases h; simp only [lwFlag_cont]; simp [lwFlag]
  | idle | ackU | retS _ => simp only [act] at h; cases h
  | sc _ | rl _ _ _ | rr _ _ _ _ | wm _ | s0 | s1 _ => simp only [act] at h; cases h; rfl

lemma act_ret_flag {p : P} {l l' : Loc P V} {r : Option (P → V)}
    (h : act T v₀ p l = .ret r l') : l'.cnt + lwFlag l' = l.cnt + lwFlag l := by
  rcases l with ⟨n, pc⟩
  cases pc with
  | up a ptr => cases a <;> (simp only [act] at h; cases h)
  | idle | ackU | retS _ => simp only [act] at h; cases h; rfl
  | _ => simp only [act] at h; cases h

/-- The counter of `j` (plus a pending leaf write) is the number of `Update`s invoked by `j`. -/
theorem cnt_eq_updCount (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) (j : P) :
    (C.loc j).cnt + lwFlag (C.loc j) = updCount α j := by
  refine Impl.run_induction (Q := fun α C => ∀ j, (C.loc j).cnt + lwFlag (C.loc j) = updCount α j)
    (fun j => rfl) (fun α C ℓ C' hα ih hs j => ?_) h j
  by_cases hq : ℓ.proc = j
  · cases ℓ with
    | inv q o =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨hpend, -, -, hloc, -⟩ := Impl.step_inv hs
      obtain ⟨R, L, s₀, hI⟩ := exists_inv hT hα
      have hidle := (hpend ▸ hI.proc q).pc_idle
      have := ih q
      simp only [lwFlag, hidle, updCount] at this
      simp only [hloc, Function.update_self, updCount, opsOf_concat, List.filter_append]
      cases o <;> simp [lwFlag, SOp.isUpd, List.filter] <;> omega
    | tau q =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, i, o, k, hact, -, hloc⟩ := Impl.step_tau hs
      rw [hloc, Function.update_self, act_access_flag hact, ih q]
      simp [updCount]
    | ret q r =>
      simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, -, l, hact, hloc⟩ := Impl.step_ret hs
      rw [hloc, Function.update_self, act_ret_flag hact, ih q]
      simp [updCount]
  · rw [(Impl.step_other hs hq).1, ih j]
    rw [updCount, updCount, opsOf_concat_of_ne (α := α) (ℓ := ℓ) (q := j)
      (fun o he => hq (by rw [he]; rfl))]

/-- Indices of the node `a` are bounded by the sum of the counters. -/
lemma seq_index_le (hT : T.WF) {R : List Bool → Set (ℕ × ℕ)} {c : P → ℕ} {t : BTree P}
    {a : List Bool} {k : ℕ} {s : P → ℕ} (hsub : T.sub a = some t) (h : SeqR R c t a k s) :
    k ≤ (T.leaves.map c).sum := by
  rw [← SeqR.sum (BTree.nodup_of_sub hsub hT.nodup) h]
  exact (List.sum_le_sum fun j _ => seq_le_cnt hT hsub h j).trans
    ((BTree.sub_leaves_sublist hsub).map c |>.sum_le_sum fun _ _ => Nat.zero_le _)

/-- The indices and arguments of the next base-object access of a process. -/
def nextIdx (l : Loc P V) : List ℕ :=
  match l.pc with
  | .lw _ => [l.cnt + 1]
  | .up _ ptr => [ptr]
  | .rl _ x y => [x, y]
  | .rr _ x y _ => [x, y]
  | .wv _ k _ => [k]
  | .wm d => [d]
  | .s1 c => [c]
  | _ => []

/-- **All indices are bounded by the number of `Update`s.** In every reachable configuration
of Algorithm 3, the components of every max array, the value of `root.mr`, and every index or
argument of the next access of every process (view index, `MaxUpdate` or `WriteMax` argument)
are at most the number of `Update`s invoked so far. -/
theorem indices_le_updates (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) :
    C.mem .mr ≤ nUpd T α ∧
      (∀ a l r, T.sub a = some (.node l r) →
        (C.mem (.ma a)).1 ≤ nUpd T α ∧ (C.mem (.ma a)).2 ≤ nUpd T α) ∧
      ∀ p, ∀ n ∈ nextIdx (C.loc p), n ≤ nUpd T α := by
  obtain ⟨R, L, s₀, hI⟩ := exists_inv hT h
  have hG := hI.g
  have hcnt : (T.leaves.map (cntOf C)).sum ≤ nUpd T α :=
    List.sum_le_sum fun j _ => by
      have := cnt_eq_updCount hT h j; simp only [cntOf]; omega
  have hb : ∀ {t a k s}, T.sub a = some t → SeqR R (cntOf C) t a k s → k ≤ nUpd T α :=
    fun hsub hs => (seq_index_le hT hsub hs).trans hcnt
  refine ⟨hb rfl hG.root.1, fun a l r hsub => ?_, fun p n hn => ?_⟩
  · obtain ⟨⟨s₁, h₁, -⟩, ⟨s₂, h₂, -⟩⟩ := hG.reach a l r hsub _ _ (hG.cur a)
    exact ⟨hb (by simp [hsub, BTree.child]) h₁, hb (by simp [hsub, BTree.child]) h₂⟩
  · have hP := hI.proc p
    unfold nextIdx at hn
    unfold PInv at hP
    split at hn <;> rename_i hpc <;> simp only [hpc] at hP <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    · subst hn
      have := cnt_eq_updCount hT h p
      simp only [lwFlag, hpc] at this
      have : updCount α p ≤ nUpd T α :=
        List.single_le_sum (fun _ _ => Nat.zero_le _) _
          (List.mem_map.2 ⟨p, hT.mem p, rfl⟩)
      omega
    · subst hn
      obtain ⟨-, -, -, t, hsub, s, hs, -⟩ := hP
      exact hb hsub hs
    · obtain ⟨-, -, lt, rt, hsub, -, s₁, s₂, h₁, h₂, -⟩ := hP
      rcases hn with rfl | rfl
      · exact hb (by simp [hsub, BTree.child]) h₁
      · exact hb (by simp [hsub, BTree.child]) h₂
    · obtain ⟨-, -, lt, rt, hsub, -, s₁, s₂, h₁, h₂, -⟩ := hP
      rcases hn with rfl | rfl
      · exact hb (by simp [hsub, BTree.child]) h₁
      · exact hb (by simp [hsub, BTree.child]) h₂
    · subst hn
      obtain ⟨-, -, lt, rt, hsub, s, hs, -⟩ := hP
      exact hb hsub hs
    · subst hn
      obtain ⟨-, s, hs, -⟩ := hP
      exact hb rfl hs
    · subst hn
      obtain ⟨-, -, s, hs, -⟩ := hP
      exact hb rfl hs

/-- **`(b − 1)`-limited use.** If at most `b − 1` `Update`s are invoked, every max-array
component, the value of `root.mr` and every index/argument of every access is `< b`, so
`MaxArray_{b×b}`, `MaxReg_b` and `view` arrays of length `b` suffice. -/
theorem limited_use (hT : T.WF) {α : List (Label P (swSnap P V v₀))} {C : Cfg v₀}
    (h : (alg3 T v₀).run α = some C) {b : ℕ} (hb : nUpd T α < b) :
    C.mem .mr < b ∧
      (∀ a l r, T.sub a = some (.node l r) → (C.mem (.ma a)).1 < b ∧ (C.mem (.ma a)).2 < b) ∧
      ∀ p, ∀ n ∈ nextIdx (C.loc p), n < b := by
  obtain ⟨h1, h2, h3⟩ := indices_le_updates hT h
  exact ⟨lt_of_le_of_lt h1 hb, fun a l r hs =>
    ⟨lt_of_le_of_lt (h2 a l r hs).1 hb, lt_of_le_of_lt (h2 a l r hs).2 hb⟩,
    fun p n hn => lt_of_le_of_lt (h3 p n hn) hb⟩

end Podc.LimitedUseSnapshots.Snapshot
