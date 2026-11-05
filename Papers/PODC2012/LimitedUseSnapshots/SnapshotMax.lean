import Papers.PODC2012.LimitedUseSnapshots.SnapshotWrite

/-!
# Algorithm 3: preservation of the invariant by `MaxUpdate` (Lines 8, 10)
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}
  {α : List (Label P (swSnap P V v₀))} {C C' : Cfg v₀} {R : List Bool → Set (ℕ × ℕ)}
  {L : Lin v₀} {s₀ : P → ℕ}

/-- The ghost after the max array of `q` takes the state `new`. -/
def extR (R : List Bool → Set (ℕ × ℕ)) (q : List Bool) (new : ℕ × ℕ) :
    List Bool → Set (ℕ × ℕ) :=
  Function.update R q (insert new (R q))

lemma subset_extR (R : List Bool → Set (ℕ × ℕ)) (q : List Bool) (new : ℕ × ℕ) (a : List Bool) :
    R a ⊆ extR R q new a := by
  by_cases ha : a = q
  · subst ha; simp only [extR, Function.update_self]; exact Set.subset_insert _ _
  · simp [extR, ha]

lemma mem_extR_self (R : List Bool → Set (ℕ × ℕ)) (q : List Bool) (new : ℕ × ℕ) :
    new ∈ extR R q new q := by simp [extR]

lemma mem_extR {R : List Bool → Set (ℕ × ℕ)} {q a : List Bool} {new z : ℕ × ℕ}
    (h : z ∈ extR R q new a) : (a = q ∧ z = new) ∨ z ∈ R a := by
  by_cases ha : a = q
  · subst ha; simp only [extR, Function.update_self, Set.mem_insert_iff] at h
    rcases h with h | h
    · exact Or.inl ⟨rfl, h⟩
    · exact Or.inr h
  · simp only [extR, ha, Function.update_of_ne, ne_eq, not_false_eq_true] at h; exact Or.inr h

lemma chain_extR {M : Mem v₀} {c : P → ℕ} {q : List Bool} {new : ℕ × ℕ}
    (hG : GInv T M c R L s₀) (hle : M (.ma q) ≤ new) : Chain (extR R q new) := by
  intro a x hx y hy
  rcases mem_extR hx with ⟨ha, hxe⟩ | hx' <;> rcases mem_extR hy with ⟨ha', hye⟩ | hy'
  · left; rw [hxe, hye]
  · right; subst ha; rw [hxe]; exact (hG.le_cur _ y hy').trans hle
  · left; subst ha'; rw [hye]; exact (hG.le_cur _ x hx').trans hle
  · exact hG.chain a x hx' y hy'

/-- Generic `MaxUpdate` step of `p` on the max array of the node `q`, which takes the state
`new ≥` the current one, after which `p` goes to `MaxScan(q.ma)`. -/
lemma inv_step_ma (hT : T.WF) (hI : Inv T α C R L s₀) {p : P} {q : List Bool} {new : ℕ × ℕ}
    {lt rt : BTree P}
    (hC' : C' = { C with mem := Function.update C.mem (.ma q) new,
                          loc := Function.update C.loc p ⟨(C.loc p).cnt, .sc q⟩ })
    (hle : C.mem (.ma q) ≤ new) (hsub : T.sub q = some (.node lt rt)) (hsuf : q <:+ T.path p)
    (hu : UpdLin T C.mem L s₀ (C.loc p) (C.pend p) (curOp α p) p)
    (hnew : Corr T C.mem R (cntOf C) lt (false :: q) new.1 ∧
      Corr T C.mem R (cntOf C) rt (true :: q) new.2)
    (hpn : ∃ s₁ s₂, SeqR (extR R q new) (cntOf C) lt (false :: q) new.1 s₁ ∧
      SeqR (extR R q new) (cntOf C) rt (true :: q) new.2 s₂ ∧ s₁ p + s₂ p = (C.loc p).cnt) :
    Inv T (α ++ [.tau p]) C' (extR R q new) L s₀ := by
  have hG := hI.g
  set R' := extR R q new with hR'
  have hc : cntOf C' = cntOf C := by rw [hC']; exact cntOf_update rfl
  have hmem : C'.mem = Function.update C.mem (.ma q) new := by rw [hC']
  have hv : ∀ a k, C'.mem (.view a k) = C.mem (.view a k) := fun a k => by
    rw [hmem, Function.update_of_ne (by simp)]
  have hmr : C'.mem .mr = C.mem .mr := by rw [hmem, Function.update_of_ne (by simp)]
  have hma : ∀ a, a ≠ q → C'.mem (.ma a) = C.mem (.ma a) := fun a ha => by
    rw [hmem, Function.update_of_ne (by simpa using ha)]
  have hmaq : C'.mem (.ma q) = new := by rw [hmem]; simp
  have hch : Chain R' := chain_extR hG hle
  have hF : Frame T C.mem C'.mem (cntOf C) (cntOf C') R R' := by
    rw [hc]; exact Frame.of_views (subset_extR R q new) hch le_rfl hv
  have hGI : GInv T C'.mem (cntOf C') R' L s₀ := by
    refine ⟨hch, fun a => ?_, fun a z hz => ?_, fun a l r hs x y hxy => ?_, ?_, ?_⟩
    · by_cases ha : a = q
      · subst ha; rw [hmaq]; exact mem_extR_self R a new
      · rw [hma a ha]; exact subset_extR R q new a (hG.cur a)
    · by_cases ha : a = q
      · subst ha; rw [hmaq]
        rcases mem_extR hz with ⟨-, rfl⟩ | hz
        · exact le_rfl
        · exact (hG.le_cur _ z hz).trans hle
      · rw [hma a ha]
        rcases mem_extR hz with ⟨h, -⟩ | hz
        · exact absurd h ha
        · exact hG.le_cur a z hz
    · rcases mem_extR hxy with ⟨rfl, he⟩ | hxy
      · rw [hsub] at hs; cases hs
        have hx : x = new.1 := by rw [← he]
        have hy : y = new.2 := by rw [← he]
        subst hx hy
        exact ⟨hF.corr (by simp [hsub, BTree.child]) hnew.1,
          hF.corr (by simp [hsub, BTree.child]) hnew.2⟩
      · obtain ⟨h1, h2⟩ := hG.reach a l r hs x y hxy
        exact ⟨hF.corr (by simp [hs, BTree.child]) h1, hF.corr (by simp [hs, BTree.child]) h2⟩
    · rw [hmr]
      exact ⟨hF.seq hG.root.1, hF.view [] _ T s₀ rfl hG.root.1 hG.root.2⟩
    · rw [hG.state]; funext j; simp [lvM, hv]
  refine ⟨hI.lin.append_tau p, hGI, fun i => ?_⟩
  rw [curOp_append_tau]
  by_cases hi : i = p
  · subst hi
    have hloc : C'.loc i = ⟨(C.loc i).cnt, .sc q⟩ := by rw [hC']; simp
    have hpd : C'.pend i = C.pend i := by rw [hC']
    rw [hloc, hpd, hc]
    unfold PInv; dsimp only
    refine ⟨hu.frame (hF.lv i _ le_rfl) le_rfl (seq_le_cnt_root hT hG.root.1 i) (by simp),
      hsuf, lt, rt, hsub, new.1, new.2, by simpa using mem_extR_self R q new, hpn⟩
  · refine proc_others hT hI.proc hF (p := p) ?_ ?_ (fun _ _ => rfl) le_rfl
      (by rw [hc]; exact seq_le_cnt_root hT hG.root.1) (fun _ _ => by simp) (fun _ _ => rfl) i hi
    · intro j hj; rw [hC']; exact Function.update_of_ne hj _ _
    · intro j hj; rw [hC']

lemma corr_max {M : Mem v₀} {c : P → ℕ} {t : BTree P} {a : List Bool} {x y : ℕ}
    (hx : Corr T M R c t a x) (hy : Corr T M R c t a y) : Corr T M R c t a (max x y) := by
  rcases max_choice x y with h | h <;> rw [h]
  · exact hx
  · exact hy

/-- **Lines 7–10**: `MaxUpdate_b(u.parent.ma, ptr)`. -/
lemma inv_step_up (hT : T.WF) (hI : Inv T α C R L s₀) {p : P} {a : List Bool} {ptr : ℕ}
    (hpc : (C.loc p).pc = .up a ptr) (h : (alg3 T v₀).step C (.tau p) = some C') :
    ∃ R', Inv T (α ++ [.tau p]) C' R' L s₀ ∧ ∀ a, R a ⊆ R' a := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨hu, ha, hsuf, t, hsubt, s, hs, hsi, hag⟩ := hP
  have hpend : C.pend p ≠ none := by rw [hu.1]; simp
  have hG := hI.g
  cases a with
  | nil => exact absurd rfl ha
  | cons b q =>
  obtain ⟨-, lt, rt, hsubq, hchild⟩ := BTree.exists_parent (hT.mem p) hsuf
  have hsufq : q <:+ T.path p := (List.suffix_cons b q).trans hsuf
  set cur := C.mem (.ma q) with hcur
  obtain ⟨hc₁, hc₂⟩ := hG.reach q lt rt hsubq cur.1 cur.2 (hG.cur q)
  have hptr : Corr T C.mem R (cntOf C) t (b :: q) ptr := ⟨s, hs, hag⟩
  cases b with
  | false =>
    have ht : t = lt := by
      rw [hsubt] at hchild; exact (Option.some.inj hchild).symm
    subst ht
    have hact : act T v₀ p (C.loc p) = .access (.ma q) (MAOp.upd0 ptr)
        (fun _ => ⟨(C.loc p).cnt, .sc q⟩) := by simp [act, hpc]
    have hC' := tau_cfg hpend hact h
    simp only [objSpec] at hC'
    set new : ℕ × ℕ := (max cur.1 ptr, cur.2) with hnew
    have hle : cur ≤ new := Prod.mk_le_mk.2 ⟨le_max_left _ _, le_rfl⟩
    have hch := chain_extR hG hle
    have hnew' : Corr T C.mem R (cntOf C) t (false :: q) new.1 := corr_max hc₁ hptr
    obtain ⟨s₁, h₁, -⟩ := hnew'
    obtain ⟨s₂, h₂, -⟩ := id hc₂
    have h₁' := SeqR.mono (subset_extR R q new) le_rfl h₁
    have h₂' := SeqR.mono (subset_extR R q new) le_rfl h₂
    have hm := SeqR.le hch (SeqR.mono (subset_extR R q new) le_rfl hs) h₁' (le_max_right _ _)
    refine ⟨_, inv_step_ma hT hI (new := new) hC' hle hsubq hsufq hu ⟨corr_max hc₁ hptr, hc₂⟩
      ⟨s₁, s₂, h₁', h₂', node_seq_eq hT hsubq (mem_extR_self R q new) h₁' h₂' ?_⟩,
      subset_extR R q new⟩
    exact le_trans (by show (C.loc p).cnt ≤ _; rw [← hsi]; exact hm p) (Nat.le_add_right _ _)
  | true =>
    have ht : t = rt := by
      rw [hsubt] at hchild; exact (Option.some.inj hchild).symm
    subst ht
    have hact : act T v₀ p (C.loc p) = .access (.ma q) (MAOp.upd1 ptr)
        (fun _ => ⟨(C.loc p).cnt, .sc q⟩) := by simp [act, hpc]
    have hC' := tau_cfg hpend hact h
    simp only [objSpec] at hC'
    set new : ℕ × ℕ := (cur.1, max cur.2 ptr) with hnew
    have hle : cur ≤ new := Prod.mk_le_mk.2 ⟨le_rfl, le_max_left _ _⟩
    have hch := chain_extR hG hle
    have hnew' : Corr T C.mem R (cntOf C) t (true :: q) new.2 := corr_max hc₂ hptr
    obtain ⟨s₂, h₂, -⟩ := hnew'
    obtain ⟨s₁, h₁, -⟩ := id hc₁
    have h₁' := SeqR.mono (subset_extR R q new) le_rfl h₁
    have h₂' := SeqR.mono (subset_extR R q new) le_rfl h₂
    have hm := SeqR.le hch (SeqR.mono (subset_extR R q new) le_rfl hs) h₂' (le_max_right _ _)
    refine ⟨_, inv_step_ma hT hI (new := new) hC' hle hsubq hsufq hu ⟨hc₁, corr_max hc₂ hptr⟩
      ⟨s₁, s₂, h₁', h₂', node_seq_eq hT hsubq (mem_extR_self R q new) h₁' h₂' ?_⟩,
      subset_extR R q new⟩
    exact le_trans (by show (C.loc p).cnt ≤ _; rw [← hsi]; exact hm p) (Nat.le_add_left _ _)

end Podc.LimitedUseSnapshots.Snapshot
