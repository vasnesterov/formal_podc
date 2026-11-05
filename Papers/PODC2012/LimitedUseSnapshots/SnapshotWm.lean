import Papers.PODC2012.LimitedUseSnapshots.SnapshotMax

/-!
# Algorithm 3: `WriteMax(root.mr, ptr)` (Line 18), the linearization point of `Update`s

When `root.mr` grows from `c₀` to `c₁`, every process `j` whose leaf pointer in
`root.seq[c₁]` exceeds the one in `root.seq[c₀]` has a pending `Update` (with counter value
`root.seq[c₁]_j`); all of them are linearized at this step (in the order of the leaves).
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}
  {α : List (Label P (swSnap P V v₀))} {C C' : Cfg v₀} {R : List Bool → Set (ℕ × ℕ)}
  {L : Lin v₀} {s₀ : P → ℕ}

/-- Applying updates of distinct components. -/
lemma runOps_updates (l : List P) (hl : l.Nodup) (f : P → V) (q : P → V) :
    (swSnap P V v₀).runOps q (l.map (fun j => SOp.update j (f j))) =
      fun i => if i ∈ l then f i else q i := by
  induction l generalizing q with
  | nil => rfl
  | cons j l ih =>
    rw [List.map_cons, ObjSpec.runOps_cons, ih (List.nodup_cons.1 hl).2]
    funext i
    by_cases hij : i = j
    · subst hij; simp [(List.nodup_cons.1 hl).1]
    · simp [hij]

/-- A process whose leaf pointer is newly covered by the root pointer has a pending `Update` with
that counter value, not yet linearized. -/
lemma PInv.upd_of_lt {M : Mem v₀} {c : P → ℕ} {l : Loc P V} {pd : Option (SOp P V)}
    {x : OpId P} {i : P} (h : PInv T M c R L s₀ l pd x i) {s' : P → ℕ} (hlt : s₀ i < s' i)
    (hle : s' i ≤ l.cnt) :
    pd = some (.update i (lvM T M i l.cnt)) ∧ s' i = l.cnt ∧ x ∉ L.map Prod.fst := by
  have key : UpdLin T M L s₀ l pd x i →
      pd = some (.update i (lvM T M i l.cnt)) ∧ s' i = l.cnt ∧ x ∉ L.map Prod.fst :=
    fun hU => ⟨hU.1, by have := hU.2.2.1; omega, fun hx => by have := hU.2.2.2.1 hx; omega⟩
  unfold PInv at h
  split at h <;>
    first
    | exact key h.1
    | exact key h
    | (exfalso; have := h.2; omega)

lemma inv_step_wm (hT : T.WF) (hα : (alg3 T v₀).run α = some C) (hI : Inv T α C R L s₀)
    {p : P} {d : ℕ} (hpc : (C.loc p).pc = .wm d) (h : (alg3 T v₀).step C (.tau p) = some C') :
    ∃ L' s₀', Inv T (α ++ [.tau p]) C' R L' s₀' := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨hu, s, hs, hsi, hag⟩ := hP
  have hpend : C.pend p ≠ none := by rw [hu.1]; simp
  have hact : act T v₀ p (C.loc p) = .access .mr (MaxOp.writeMax d)
      (fun _ => ⟨(C.loc p).cnt, .ackU⟩) := by simp [act, hpc]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  have hG := hI.g
  set c₀ : ℕ := C.mem .mr with hc₀
  -- the new root pointer and its `seq`
  obtain ⟨s', hs', hag'⟩ : ∃ s', SeqR R (cntOf C) T [] (max c₀ d) s' ∧
      Agr T C.mem T s' (C.mem (.view [] (max c₀ d))) := by
    rcases max_choice c₀ d with hm | hm <;> rw [hm]
    · exact ⟨s₀, hG.root⟩
    · exact ⟨s, hs, hag⟩
  have h0s : s₀ ≤ s' := SeqR.le hG.chain hG.root.1 hs' (le_max_left _ _)
  have hss : s ≤ s' := SeqR.le hG.chain hs hs' (le_max_right _ _)
  have hsc : s' ≤ cntOf C := seq_le_cnt_root hT hs'
  -- the newly linearized updates
  set J := T.leaves.filter (fun j => decide (s₀ j < s' j)) with hJ
  have hJnd : J.Nodup := hT.nodup.filter _
  have hmemJ : ∀ j, j ∈ J ↔ s₀ j < s' j := fun j => by simp [hJ, hT.mem j]
  set Mlist : Lin v₀ := J.map (fun j => (curOp α j, SOp.update j (lvM T C.mem j (s' j))))
    with hMlist
  have hupd : ∀ j ∈ J, C.pend j = some (.update j (lvM T C.mem j (C.loc j).cnt)) ∧
      s' j = (C.loc j).cnt ∧ curOp α j ∉ L.map Prod.fst :=
    fun j hj => (hI.proc j).upd_of_lt ((hmemJ j).1 hj) (hsc j)
  have hcur_inj : ∀ i j, curOp α i = curOp α j → i = j := fun i j h => congrArg Prod.fst h
  have hfst : Mlist.map Prod.fst = J.map (curOp α) := by simp [hMlist]
  have hL' : IsLinearization (α ++ [.tau p]) (L ++ Mlist) := by
    refine (hI.lin.append_tau p).push_list Mlist ?_ ?_ ?_
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      obtain ⟨h1, h2, -⟩ := hupd j hj
      obtain ⟨hinv, -, hop⟩ := Impl.run_pend_curOp hα h1
      refine ⟨by rw [opOf_append_of_invoked hinv, hop, h2], ?_⟩
      have := not_completed_curOp (α ++ [.tau p]) j
      rwa [curOp_append_tau] at this
    · rw [hfst]; exact hJnd.map (fun i j h => hcur_inj i j h)
    · intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      exact (hupd j hj).2.2
  have hLall : ∀ i, (curOp α i ∈ (L ++ Mlist).map Prod.fst ↔
      curOp α i ∈ L.map Prod.fst ∨ s₀ i < s' i) := by
    intro i
    rw [List.map_append, List.mem_append, hfst, ← hmemJ i]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · obtain ⟨j, hj, he⟩ := List.mem_map.1 h
        exact Or.inr (hcur_inj j i he ▸ hj)
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr (List.mem_map.2 ⟨i, h, rfl⟩)
  have hresp : ∀ y ∈ L.map Prod.fst, (swSnap P V v₀).respIn (swSnap P V v₀).init
      (L ++ Mlist) y = (swSnap P V v₀).respIn (swSnap P V v₀).init L y :=
    fun y hy => ObjSpec.respIn_append_of_mem hy _
  -- the configuration after the step
  have hc : cntOf C' = cntOf C := by rw [hC']; exact cntOf_update rfl
  have hmem : C'.mem = Function.update C.mem .mr (max c₀ d) := by rw [hC']
  have hv : ∀ a k, C'.mem (.view a k) = C.mem (.view a k) := fun a k => by
    rw [hmem, Function.update_of_ne (by simp)]
  have hma : ∀ a, C'.mem (.ma a) = C.mem (.ma a) := fun a => by
    rw [hmem, Function.update_of_ne (by simp)]
  have hmr : C'.mem .mr = max c₀ d := by rw [hmem]; simp
  have hF : Frame T C.mem C'.mem (cntOf C) (cntOf C') R R := by
    rw [hc]; exact Frame.of_views (fun _ => subset_rfl) hG.chain le_rfl hv
  have hlv : ∀ j m, lvM T C'.mem j m = lvM T C.mem j m := fun j m => by simp [lvM, hv]
  have hstate : linState (A := swSnap P V v₀) (L ++ Mlist) =
      fun j => lvM T C'.mem j (s' j) := by
    rw [linState_append, hG.state]
    have : Mlist.map Prod.snd = J.map (fun j => SOp.update j (lvM T C.mem j (s' j))) := by
      simp [hMlist]
    rw [this, runOps_updates J hJnd]
    funext i
    rw [hlv]
    split_ifs with hi
    · rfl
    · have := (hmemJ i).not.1 hi
      rw [le_antisymm (h0s i) (not_lt.1 this)]
  refine ⟨L ++ Mlist, s', hL', ⟨hG.chain, fun a => by rw [hma]; exact hG.cur a,
    fun a => by rw [hma]; exact hG.le_cur a, fun a l r hsub x y hxy => ?_, ?_, hstate⟩,
    fun i => ?_⟩
  · obtain ⟨h1, h2⟩ := hG.reach a l r hsub x y hxy
    exact ⟨hF.corr (by simp [hsub, BTree.child]) h1, hF.corr (by simp [hsub, BTree.child]) h2⟩
  · rw [hmr, hc]
    exact ⟨hs', fun j hj => by rw [hv, hlv]; exact hag' j hj⟩
  · rw [curOp_append_tau]
    by_cases hi : i = p
    · subst hi
      have hloc : C'.loc i = ⟨(C.loc i).cnt, .ackU⟩ := by rw [hC']; simp
      have hpd : C'.pend i = C.pend i := by rw [hC']
      rw [hloc, hpd]
      have hs'i : s' i = (C.loc i).cnt := le_antisymm (hsc i) (hsi ▸ hss i)
      unfold PInv; dsimp only
      exact ⟨hu.frame (hlv i _) (h0s i) hs'i.le (hLall i), hs'i⟩
    · exact proc_others hT hI.proc hF (p := p) (fun j hj => by rw [hC']; simp [hj])
        (fun j _ => by rw [hC']) (fun _ _ => rfl) h0s (by rw [hc]; exact hsc)
        (fun j _ => hLall j) hresp i hi

end Podc.LimitedUseSnapshots.Snapshot
