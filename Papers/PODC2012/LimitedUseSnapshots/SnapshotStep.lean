import Papers.PODC2012.LimitedUseSnapshots.SnapshotInv

/-!
# Algorithm 3: preservation of the invariant (general lemmas, invocations, responses)
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}

/-! ### Small lemmas -/

lemma seqR_zero {R : List Bool → Set (ℕ × ℕ)} {c : P → ℕ} (h0 : ∀ a, ((0 : ℕ), (0 : ℕ)) ∈ R a) :
    ∀ (t : BTree P) (a : List Bool), SeqR R c t a 0 0
  | .leaf j, _ => ⟨Nat.zero_le _, by simp⟩
  | .node l r, a => ⟨0, 0, h0 a, rfl, 0, 0, seqR_zero h0 l _, seqR_zero h0 r _, by simp⟩

lemma path_injective (hT : T.WF) {i j : P} (h : T.path i = T.path j) : i = j := by
  have h1 := BTree.sub_path (hT.mem i)
  rw [h, BTree.sub_path (hT.mem j)] at h1
  cases h1; rfl

/-- The response of an `Update` in any linearization containing it. -/
lemma respIn_update {α : List (Label P (swSnap P V v₀))} {L : Lin v₀}
    (hL : IsLinearization α L) {x : OpId P} (hx : x ∈ L.map Prod.fst) {i : P} {v : V}
    (hop : opOf α x = some (.update i v)) :
    (swSnap P V v₀).respIn (swSnap P V v₀).init L x = some none := by
  obtain ⟨⟨y, o⟩, hy, rfl⟩ := List.mem_map.1 hx
  obtain ⟨L₁, L₂, hsplit⟩ := List.append_of_mem hy
  have := hL.op_eq _ hy
  rw [hop] at this; cases this
  rw [ObjSpec.respIn_of_split hL.nodup hsplit]

/-! ### Frames -/

lemma Frame.refl (hch : Chain R) (M : Mem v₀) (c : P → ℕ) : Frame T M M c c R R :=
  ⟨fun _ => subset_rfl, hch, le_rfl, fun _ _ _ => rfl, fun _ _ _ _ _ _ h => h⟩

/-- A frame for steps that do not write any view register. -/
lemma Frame.of_views {M M' : Mem v₀} {c c' : P → ℕ} {R R' : List Bool → Set (ℕ × ℕ)}
    (hR : ∀ a, R a ⊆ R' a) (hch : Chain R') (hc : c ≤ c')
    (hv : ∀ a k, M' (.view a k) = M (.view a k)) : Frame T M M' c c' R R' := by
  refine ⟨hR, hch, hc, fun j m _ => by simp [lvM, hv], fun a k t s _ _ hag j hj => ?_⟩
  rw [hv, hag j hj]; simp [lvM, hv]

/-- The global invariant survives a step that changes neither max arrays, `root.mr`, the ghost
`R`, `L`, `s₀`. -/
lemma GInv.frame {M M' : Mem v₀} {c c' : P → ℕ} {R : List Bool → Set (ℕ × ℕ)} {L : Lin v₀}
    {s₀ : P → ℕ} (hT : T.WF) (hG : GInv T M c R L s₀) (hF : Frame T M M' c c' R R)
    (hma : ∀ a, M' (.ma a) = M (.ma a)) (hmr : M' .mr = M .mr) : GInv T M' c' R L s₀ where
  chain := hG.chain
  cur a := by rw [hma]; exact hG.cur a
  le_cur a q hq := by rw [hma]; exact hG.le_cur a q hq
  reach a l r hsub x y hxy := by
    obtain ⟨h1, h2⟩ := hG.reach a l r hsub x y hxy
    exact ⟨hF.corr (by simp [hsub, BTree.child]) h1, hF.corr (by simp [hsub, BTree.child]) h2⟩
  root := by
    rw [hmr]
    exact ⟨hF.seq hG.root.1, hF.view [] _ T s₀ rfl hG.root.1 hG.root.2⟩
  state := by rw [hG.state, hF.lvfun (seq_le_cnt_root hT hG.root.1)]

/-- Steps of `p` preserve the per-process invariants of the other processes. -/
lemma proc_others (hT : T.WF) {C C' : Cfg v₀} {α α' : List (Label P (swSnap P V v₀))}
    {R R' : List Bool → Set (ℕ × ℕ)} {L L' : Lin v₀} {s₀ s₀' : P → ℕ} {p : P}
    (hP : ∀ i, PInv T C.mem (cntOf C) R L s₀ (C.loc i) (C.pend i) (curOp α i) i)
    (hF : Frame T C.mem C'.mem (cntOf C) (cntOf C') R R')
    (hloc : ∀ i, i ≠ p → C'.loc i = C.loc i) (hpend : ∀ i, i ≠ p → C'.pend i = C.pend i)
    (hcur : ∀ i, i ≠ p → curOp α' i = curOp α i)
    (hs₀ : s₀ ≤ s₀') (hs₀c : s₀' ≤ cntOf C')
    (hL : ∀ i, i ≠ p → (curOp α i ∈ L'.map Prod.fst ↔ curOp α i ∈ L.map Prod.fst ∨ s₀ i < s₀' i))
    (hresp : ∀ y ∈ L.map Prod.fst, (swSnap P V v₀).respIn (swSnap P V v₀).init L' y =
      (swSnap P V v₀).respIn (swSnap P V v₀).init L y) :
    ∀ i, i ≠ p → PInv T C'.mem (cntOf C') R' L' s₀' (C'.loc i) (C'.pend i) (curOp α' i) i := by
  intro i hi
  rw [hloc i hi, hpend i hi, hcur i hi]
  refine (hP i).frame hT hF le_rfl hs₀ ?_ (hL i hi) hresp
  have := hs₀c i; simp only [cntOf, hloc i hi] at this; exact this

/-! ### Initial configuration -/

/-- The initial ghost: every max array has only been `(0, 0)`. -/
def R₀ : List Bool → Set (ℕ × ℕ) := fun _ => {(0, 0)}

lemma inv_init :
    Inv T ([] : List (Label P (swSnap P V v₀))) (alg3 T v₀).initCfg R₀ [] 0 := by
  have hc : cntOf ((alg3 T v₀).initCfg) = 0 := rfl
  have h0 : ∀ a, ((0 : ℕ), (0 : ℕ)) ∈ R₀ a := fun _ => rfl
  refine ⟨isLinearization_nil, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a p hp q hq; simp only [R₀, Set.mem_singleton_iff] at hp hq; subst hp hq; simp
  · intro a; rfl
  · intro a q hq; simp only [R₀, Set.mem_singleton_iff] at hq; subst hq; exact le_rfl
  · intro a l r _ x y hxy
    simp only [R₀, Set.mem_singleton_iff, Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact ⟨⟨0, seqR_zero h0 _ _, fun j _ => rfl⟩, ⟨0, seqR_zero h0 _ _, fun j _ => rfl⟩⟩
  · exact ⟨seqR_zero h0 _ _, fun j _ => rfl⟩
  · rfl
  · intro i; exact ⟨rfl, rfl⟩

lemma PInv.pc_idle {M : Mem v₀} {c : P → ℕ} {R : List Bool → Set (ℕ × ℕ)} {L : Lin v₀}
    {s₀ : P → ℕ} {l : Loc P V} {x : OpId P} {i : P} (h : PInv T M c R L s₀ l none x i) :
    l.pc = .idle := by
  unfold PInv at h; split at h <;> simp_all [UpdLin]

lemma cntOf_update {C : Cfg v₀} {mem : Mem v₀} {pend : P → Option (SOp P V)} {p : P}
    {l : Loc P V} (h : l.cnt = (C.loc p).cnt) :
    cntOf (⟨Function.update C.loc p l, pend, mem⟩ : Cfg v₀) = cntOf C := by
  funext j; by_cases hj : j = p
  · subst hj; simp [cntOf, h]
  · simp [cntOf, hj]

/-! ### Invocations -/

lemma inv_step_inv (hα : (alg3 T v₀).run α = some C) (hI : Inv T α C R L s₀) {p : P}
    {o : SOp P V} (h : (alg3 T v₀).step C (.inv p o) = some C') :
    Inv T (α ++ [.inv p o]) C' R L s₀ := by
  obtain ⟨hpend, hallow, hpend', hloc', hmem'⟩ := Impl.step_inv h
  have hcnt : cntOf C' = cntOf C := by
    have : C' = ⟨Function.update C.loc p ((alg3 T v₀).invoke p (C.loc p) o), C'.pend, C.mem⟩ := by
      cases C'; simp_all
    rw [this]; apply cntOf_update; cases o <;> rfl
  refine ⟨hI.lin.append_inv p o, by rw [hmem', hcnt]; exact hI.g, fun i => ?_⟩
  rw [hmem', hcnt, curOp_append_inv]
  by_cases hi : i = p
  · subst hi
    have hidle := (hpend ▸ hI.proc i).pc_idle
    have hidle' := hI.proc i
    rw [hpend] at hidle'
    unfold PInv at hidle'; rw [hidle] at hidle'
    have hnot : curOp α i ∉ L.map Prod.fst := fun hx =>
      Impl.not_invoked_curOp_of_idle hα hpend (hI.lin.mem_invoked hx)
    rw [hloc', hpend', Function.update_self, Function.update_self]
    cases o with
    | update j v =>
      have : j = i := hallow
      subst this
      exact ⟨rfl, hidle'.2, hnot⟩
    | scan => exact ⟨rfl, hidle'.2, hnot⟩
  · rw [hloc', hpend', Function.update_of_ne hi, Function.update_of_ne hi]; exact hI.proc i

/-! ### Responses -/

lemma inv_step_ret (hα : (alg3 T v₀).run α = some C) (hI : Inv T α C R L s₀) {p : P}
    {r : Option (P → V)} (h : (alg3 T v₀).step C (.ret p r) = some C') :
    Inv T (α ++ [.ret p r]) C' R L s₀ := by
  obtain ⟨hpend, hpend', hmem', l, hact, hloc'⟩ := Impl.step_ret h
  have hP := hI.proc p
  -- the response and the new local state
  have key : l = ⟨(C.loc p).cnt, .idle⟩ ∧
      (swSnap P V v₀).respIn (swSnap P V v₀).init L (curOp α p) = some r ∧
      s₀ p = (C.loc p).cnt := by
    have hact' : act T v₀ p (C.loc p) = .ret r l := hact
    cases hpc : (C.loc p).pc with
    | idle => simp only [PInv, hpc] at hP; exact absurd hP.1 hpend
    | ackU =>
      simp only [PInv, hpc] at hP
      simp only [act, hpc, Action.ret.injEq] at hact'
      obtain ⟨rfl, rfl⟩ := hact'
      obtain ⟨⟨h1, -, -, h4⟩, h5⟩ := hP
      refine ⟨rfl, ?_, h5⟩
      obtain ⟨-, -, hop⟩ := Impl.run_pend_curOp hα h1
      exact respIn_update hI.lin (h4.2 h5) hop
    | retS val =>
      simp only [PInv, hpc] at hP
      simp only [act, hpc, Action.ret.injEq] at hact'
      obtain ⟨rfl, rfl⟩ := hact'
      exact ⟨rfl, hP.2.2, hP.2.1⟩
    | up a ptr => cases a <;> simp [act, hpc] at hact'
    | _ => simp [act, hpc] at hact'
  obtain ⟨rfl, hr, hs⟩ := key
  have hcnt : cntOf C' = cntOf C := by
    have : C' = ⟨Function.update C.loc p ⟨(C.loc p).cnt, .idle⟩, C'.pend, C.mem⟩ := by
      cases C'; simp_all
    rw [this]; exact cntOf_update rfl
  refine ⟨hI.lin.append_ret_of_respIn hr, by rw [hmem', hcnt]; exact hI.g, fun i => ?_⟩
  rw [hmem', hcnt]
  by_cases hi : i = p
  · subst hi
    rw [hloc', hpend', Function.update_self, Function.update_self]
    exact ⟨rfl, hs⟩
  · rw [hloc', hpend', Function.update_of_ne hi, Function.update_of_ne hi,
      curOp_append_ret_of_ne α r (Ne.symm hi)]
    exact hI.proc i

end Podc.LimitedUseSnapshots.Snapshot
