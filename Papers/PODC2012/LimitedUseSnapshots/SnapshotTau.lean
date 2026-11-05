import Papers.PODC2012.LimitedUseSnapshots.SnapshotStep

/-!
# Algorithm 3: preservation of the invariant by base-object accesses
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}
  {α : List (Label P (swSnap P V v₀))} {C C' : Cfg v₀} {R : List Bool → Set (ℕ × ℕ)}
  {L : Lin v₀} {s₀ : P → ℕ}

/-- The configuration after an access step with a known action. -/
lemma tau_cfg {p : P} (hpend : C.pend p ≠ none) {i : Obj} {o : (objSpec P V v₀ i).Op}
    {k : (objSpec P V v₀ i).Resp → Loc P V}
    (hact : act T v₀ p (C.loc p) = .access i o k)
    (h : (alg3 T v₀).step C (.tau p) = some C') :
    C' = { C with mem := Function.update C.mem i ((objSpec P V v₀ i).δ (C.mem i) o).1,
                  loc := Function.update C.loc p (k ((objSpec P V v₀ i).δ (C.mem i) o).2) } := by
  rw [Impl.step_tau_eq_some (I := alg3 T v₀) hpend hact] at h
  exact (Option.some.inj h).symm

omit [DecidableEq P] in
/-- Read-like accesses leave the memory unchanged. -/
lemma update_mem_self {M : Mem v₀} {i : Obj} {x : (objSpec P V v₀ i).State} (hx : x = M i) :
    Function.update M i x = M := by subst hx; exact Function.update_eq_self i M

/-- The common shape of a step of `p` that only changes the local state of `p` (keeping its
counter), without new linearization points. -/
lemma inv_of_local {p : P} (hI : Inv T α C R L s₀) {l' : Loc P V}
    (hC' : C' = { C with loc := Function.update C.loc p l' }) (hcnt : l'.cnt = (C.loc p).cnt)
    (hp : PInv T C.mem (cntOf C) R L s₀ l' (C.pend p) (curOp α p) p) :
    Inv T (α ++ [.tau p]) C' R L s₀ := by
  have hc : cntOf C' = cntOf C := by rw [hC']; exact cntOf_update hcnt
  refine ⟨hI.lin.append_tau p, by rw [hc, hC']; exact hI.g, fun i => ?_⟩
  rw [hc, curOp_append_tau]
  by_cases hi : i = p
  · subst hi; rw [hC']; simpa using hp
  · rw [hC']; simpa [Function.update_of_ne hi] using hI.proc i

/-- The `seq` of a node at a pair of indices whose sum covers the counter of `i`. -/
lemma node_seq_eq (hT : T.WF) {c : P → ℕ} {q : List Bool} {lt rt : BTree P}
    (hsub : T.sub q = some (.node lt rt)) {x y : ℕ} (hxy : (x, y) ∈ R q) {s₁ s₂ : P → ℕ}
    (h₁ : SeqR R c lt (false :: q) x s₁) (h₂ : SeqR R c rt (true :: q) y s₂) {i : P}
    (hge : c i ≤ s₁ i + s₂ i) : s₁ i + s₂ i = c i := by
  have hnode : SeqR R c (.node lt rt) q (x + y) (s₁ + s₂) := ⟨x, y, hxy, rfl, s₁, s₂, h₁, h₂, rfl⟩
  have := seq_le_cnt hT hsub hnode i
  simp only [Pi.add_apply] at this; omega

/-! ### `MaxScan(u.ma)` (Line 12) -/

lemma inv_step_sc (hT : T.WF) (hI : Inv T α C R L s₀) {p : P} {q : List Bool}
    (hpc : (C.loc p).pc = .sc q) (h : (alg3 T v₀).step C (.tau p) = some C') :
    Inv T (α ++ [.tau p]) C' R L s₀ := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨hu, hsuf, lt, rt, hsub, u, w, huw, s₁, s₂, h₁, h₂, hsum⟩ := hP
  have hpend : C.pend p ≠ none := by rw [hu.1]; simp
  have hact : act T v₀ p (C.loc p) = .access (.ma q) MAOp.scan
      (fun r => ⟨(C.loc p).cnt, .rl q r.1 r.2⟩) := by simp [act, hpc]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  rw [update_mem_self rfl] at hC'
  refine inv_of_local hI hC' rfl ?_
  unfold PInv; dsimp only
  -- the result of the scan is the current state
  set xy := C.mem (.ma q) with hxy
  obtain ⟨⟨t₁, ht₁, -⟩, ⟨t₂, ht₂, -⟩⟩ := hI.g.reach q lt rt hsub xy.1 xy.2 (hI.g.cur q)
  have hle := Prod.mk_le_mk.1 (hI.g.le_cur q _ huw)
  have m₁ := SeqR.le hI.g.chain h₁ ht₁ hle.1
  have m₂ := SeqR.le hI.g.chain h₂ ht₂ hle.2
  refine ⟨hu, hsuf, lt, rt, hsub, hI.g.cur q, t₁, t₂, ht₁, ht₂, ?_⟩
  refine node_seq_eq hT hsub (hI.g.cur q) ht₁ ht₂ ?_
  show (C.loc p).cnt ≤ _
  rw [← hsum]; exact Nat.add_le_add (m₁ p) (m₂ p)

/-! ### Reading the children's views (Lines 13–14) -/

lemma inv_step_rl (hI : Inv T α C R L s₀) {p : P} {q : List Bool} {x y : ℕ}
    (hpc : (C.loc p).pc = .rl q x y) (h : (alg3 T v₀).step C (.tau p) = some C') :
    Inv T (α ++ [.tau p]) C' R L s₀ := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨hu, hsuf, lt, rt, hsub, hxy, s₁, s₂, h₁, h₂, hsum⟩ := hP
  have hpend : C.pend p ≠ none := by rw [hu.1]; simp
  have hact : act T v₀ p (C.loc p) = .access (.view (false :: q) x) RWOp.read
      (fun lv => ⟨(C.loc p).cnt, .rr q x y lv⟩) := by simp [act, hpc]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  rw [update_mem_self rfl] at hC'
  refine inv_of_local hI hC' rfl ?_
  unfold PInv; dsimp only
  obtain ⟨⟨t₁, ht₁, hag⟩, -⟩ := hI.g.reach q lt rt hsub x y hxy
  obtain rfl := SeqR.unique hI.g.chain ht₁ h₁
  exact ⟨hu, hsuf, lt, rt, hsub, hxy, t₁, s₂, ht₁, h₂, hsum, hag⟩

lemma inv_step_rr (hT : T.WF) (hI : Inv T α C R L s₀) {p : P} {q : List Bool} {x y : ℕ}
    {lv : P → V} (hpc : (C.loc p).pc = .rr q x y lv)
    (h : (alg3 T v₀).step C (.tau p) = some C') :
    Inv T (α ++ [.tau p]) C' R L s₀ := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨hu, hsuf, lt, rt, hsub, hxy, s₁, s₂, h₁, h₂, hsum, hag₁⟩ := hP
  have hpend : C.pend p ≠ none := by rw [hu.1]; simp
  have hact : act T v₀ p (C.loc p) = .access (.view (true :: q) y) RWOp.read
      (fun rv => ⟨(C.loc p).cnt, .wv q (x + y) (concat T q lv rv)⟩) := by simp [act, hpc]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  rw [update_mem_self rfl] at hC'
  refine inv_of_local hI hC' rfl ?_
  unfold PInv; dsimp only
  obtain ⟨-, ⟨t₂, ht₂, hag₂⟩⟩ := hI.g.reach q lt rt hsub x y hxy
  obtain rfl := SeqR.unique hI.g.chain ht₂ h₂
  have hnd := BTree.nodup_of_sub hsub hT.nodup
  refine ⟨hu, hsuf, lt, rt, hsub, s₁ + t₂, ⟨x, y, hxy, rfl, s₁, t₂, h₁, ht₂, rfl⟩,
    by simpa using hsum, fun j hj => ?_⟩
  have hl : T.leavesAt (false :: q) = lt.leaves :=
    BTree.leavesAt_of_sub (by simp [hsub, BTree.child])
  simp only [concat, hl, Pi.add_apply]
  split_ifs with hjl
  · rw [SeqR.zero_of_not_mem ht₂ j (fun hr => BTree.disjoint_of_node hnd hjl hr), add_zero]
    exact hag₁ j hjl
  · have hjr : j ∈ rt.leaves := by
      simp only [BTree.leaves, List.mem_append] at hj; exact hj.resolve_left hjl
    rw [SeqR.zero_of_not_mem h₁ j hjl, zero_add]
    exact hag₂ j hjr

/-! ### `Scan`: reading `root.view` (Line 21) -/

lemma inv_step_s1 (hT : T.WF) (hI : Inv T α C R L s₀) {p : P} {d : ℕ}
    (hpc : (C.loc p).pc = .s1 d) (h : (alg3 T v₀).step C (.tau p) = some C') :
    Inv T (α ++ [.tau p]) C' R L s₀ := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨h1, h2, s, hs, hag, hr⟩ := hP
  have hpend : C.pend p ≠ none := by rw [h1]; simp
  have hact : act T v₀ p (C.loc p) = .access (.view [] d) RWOp.read
      (fun v => ⟨(C.loc p).cnt, .retS v⟩) := by simp [act, hpc]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  rw [update_mem_self rfl] at hC'
  refine inv_of_local hI hC' rfl ?_
  unfold PInv; dsimp only
  refine ⟨h1, h2, ?_⟩
  have : (C.mem (.view [] d) : P → V) = fun j => lvM T C.mem j (s j) :=
    funext fun j => hag j (hT.mem j)
  simp only [this]; exact hr

/-! ### `Scan`: `ReadMax(root.mr)` (Line 20), the linearization point of a `Scan` -/

lemma inv_step_s0 (hT : T.WF) (hα : (alg3 T v₀).run α = some C) (hI : Inv T α C R L s₀) {p : P}
    (hpc : (C.loc p).pc = .s0) (h : (alg3 T v₀).step C (.tau p) = some C') :
    Inv T (α ++ [.tau p]) C' R (L ++ [(curOp α p, .scan)]) s₀ := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨h1, h2, hnot⟩ := hP
  have hpend : C.pend p ≠ none := by rw [h1]; simp
  have hact : act T v₀ p (C.loc p) = .access .mr MaxOp.readMax
      (fun c => ⟨(C.loc p).cnt, .s1 c⟩) := by simp [act, hpc]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  rw [update_mem_self rfl] at hC'
  have hc : cntOf C' = cntOf C := by rw [hC']; exact cntOf_update rfl
  obtain ⟨hinv, -, hop⟩ := Impl.run_pend_curOp hα h1
  have hL' : IsLinearization (α ++ [.tau p]) (L ++ [(curOp α p, .scan)]) := by
    refine (hI.lin.append_tau p).push ?_ hnot ?_
    · rw [opOf_append_of_invoked hinv]; exact hop
    · have := not_completed_curOp (α ++ [.tau p]) p
      rwa [curOp_append_tau] at this
  have hstate : linState (A := swSnap P V v₀) (L ++ [(curOp α p, .scan)]) =
      linState (A := swSnap P V v₀) L := by rw [linState_concat]
  have hresp : ∀ y ∈ L.map Prod.fst, (swSnap P V v₀).respIn (swSnap P V v₀).init
      (L ++ [(curOp α p, .scan)]) y = (swSnap P V v₀).respIn (swSnap P V v₀).init L y :=
    fun y hy => ObjSpec.respIn_append_of_mem hy _
  have hG := hI.g
  have hmem : C'.mem = C.mem := by rw [hC']
  refine ⟨hL', ⟨hG.chain, ?_, ?_, ?_, ?_, ?_⟩, fun i => ?_⟩
  · simp only [hmem]; exact hG.cur
  · simp only [hmem]; exact hG.le_cur
  · simp only [hmem, hc]; exact hG.reach
  · rw [hc, hC']; exact hG.root
  · rw [hmem, hstate]; exact hG.state
  · rw [curOp_append_tau]
    by_cases hi : i = p
    · subst hi
      rw [hc, hC']
      simp only [Function.update_self]
      unfold PInv; dsimp only
      refine ⟨h1, h2, s₀, hG.root.1, hG.root.2, ?_⟩
      rw [ObjSpec.respIn_concat_self hnot, ← hG.state]; rfl
    · refine proc_others hT hI.proc (by rw [hmem, hc]; exact Frame.refl hG.chain _ _) (p := p)
        ?_ ?_ (fun _ _ => rfl)
        le_rfl ?_ ?_ hresp i hi
      · intro j hj; rw [hC']; exact Function.update_of_ne hj _ _
      · intro j hj; rw [hC']
      · rw [hc]; exact seq_le_cnt_root hT hG.root.1
      · intro j hj
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton, lt_self_iff_false, or_false]
        constructor
        · rintro (h | h); exact h; exact absurd (congrArg Prod.fst h) hj
        · exact Or.inl

end Podc.LimitedUseSnapshots.Snapshot
