import Papers.PODC2012.LimitedUseSnapshots.SnapshotTau

/-!
# Algorithm 3: preservation of the invariant by the writes of `view` registers (Lines 5, 16)
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

variable {P V : Type} [DecidableEq P] {T : BTree P} {v₀ : P → V}
  {α : List (Label P (swSnap P V v₀))} {C C' : Cfg v₀} {R : List Bool → Set (ℕ × ℕ)}
  {L : Lin v₀} {s₀ : P → ℕ}

/-- A frame for a write of `val` into `view[k]` of the node `a`: the written register is not
the location of a value referenced by the leaf counters, and the new content agrees with every
`seq` that the index may represent. -/
lemma Frame.write (hT : T.WF) {M : Mem v₀} {c c' : P → ℕ} (hch : Chain R) (hc : c ≤ c')
    {a : List Bool} {k : ℕ} {val : P → V}
    (hlv : ∀ j m, m ≤ c j → ¬ (T.path j = a ∧ m = k))
    (hval : ∀ t s, T.sub a = some t → SeqR R c t a k s → Agr T M t s (M (.view a k)) →
      Agr T M t s val) :
    Frame T M (Function.update M (.view a k) val) c c' R R := by
  have hlv' : ∀ j m, m ≤ c j → lvM T (Function.update M (.view a k) val) j m = lvM T M j m := by
    intro j m hm
    simp only [lvM]
    rw [Function.update_of_ne]
    intro he; simp only [Obj.view.injEq] at he; exact hlv j m hm he
  refine ⟨fun _ => subset_rfl, hch, hc, hlv', fun a' k' t s hsub hs hag j hj => ?_⟩
  have hsc := seq_le_cnt hT hsub hs
  rw [hlv' j (s j) (hsc j)]
  by_cases he : Obj.view a' k' = Obj.view a k
  · simp only [Obj.view.injEq] at he; obtain ⟨rfl, rfl⟩ := he
    rw [Function.update_self]
    exact hval t s hsub hs hag j hj
  · rw [Function.update_of_ne he]; exact hag j hj

/-! ### Line 5: writing the new value into `leaf_i.view[count_i]` -/

lemma inv_step_lw (hT : T.WF) (hI : Inv T α C R L s₀) {p : P} {v : V}
    (hpc : (C.loc p).pc = .lw v) (h : (alg3 T v₀).step C (.tau p) = some C') :
    Inv T (α ++ [.tau p]) C' R L s₀ := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨h1, h2, hnot⟩ := hP
  have hpend : C.pend p ≠ none := by rw [h1]; simp
  set n := (C.loc p).cnt with hn
  have hact : act T v₀ p (C.loc p) = .access (.view (T.path p) (n + 1)) (RWOp.write (fun _ => v))
      (fun _ => ⟨n + 1, cont (T.path p) (n + 1)⟩) := by simp [act, hpc, hn]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  have hG := hI.g
  have hpl := BTree.sub_path (hT.mem p)
  have hc : cntOf C' = Function.update (cntOf C) p (n + 1) := by
    funext j; rw [hC']; by_cases hj : j = p
    · subst hj; simp [cntOf]
    · simp [cntOf, hj]
  have hcle : cntOf C ≤ cntOf C' := by
    intro j; rw [hc]; by_cases hj : j = p
    · subst hj; simp [cntOf, hn]
    · simp [hj]
  have hmem : C'.mem = Function.update C.mem (.view (T.path p) (n + 1)) (fun _ => v) := by
    rw [hC']
  have hF : Frame T C.mem C'.mem (cntOf C) (cntOf C') R R := by
    rw [hmem]
    refine Frame.write hT hG.chain hcle ?_ ?_
    · rintro j m hm ⟨hj, rfl⟩
      obtain rfl := path_injective hT hj
      change n + 1 ≤ (C.loc _).cnt at hm; omega
    · intro t s hsub hs _
      rw [hpl] at hsub; cases hsub
      exact absurd hs.1 (by simp [cntOf, hn])
  have hGI : GInv T C'.mem (cntOf C') R L s₀ :=
    GInv.frame hT hG hF (fun a => by rw [hmem, Function.update_of_ne (by simp)])
      (by rw [hmem, Function.update_of_ne (by simp)])
  refine ⟨hI.lin.append_tau p, hGI, fun i => ?_⟩
  rw [curOp_append_tau]
  by_cases hi : i = p
  · subst hi
    have hlvp : lvM T C'.mem i (n + 1) = v := by simp [lvM, hmem]
    have hloc : C'.loc i = ⟨n + 1, cont (T.path i) (n + 1)⟩ := by rw [hC']; simp
    have hpd : C'.pend i = C.pend i := by rw [hC']
    rw [hloc, hpd]
    have hU : UpdLin T C'.mem L s₀ ⟨n + 1, cont (T.path i) (n + 1)⟩ (C.pend i) (curOp α i) i :=
      ⟨by rw [hlvp]; exact h1, by simp, by simp [h2, hn], by
        simp only; constructor
        · intro hx; exact absurd hx hnot
        · intro he; omega⟩
    have hci : cntOf C' i = n + 1 := by rw [hc]; simp
    have hseq : SeqR R (cntOf C') (.leaf i) (T.path i) (n + 1) (Pi.single i (n + 1)) :=
      ⟨hci.ge, rfl⟩
    unfold PInv
    by_cases hnil : T.path i = []
    · simp only [cont, hnil, ↓reduceIte]
      have hTl : T = .leaf i := by
        have := hpl; rw [hnil] at this; exact (Option.some.inj this)
      refine ⟨hU, Pi.single i (n + 1), ?_, by simp, ?_⟩
      · rw [hTl]; exact ⟨hci.ge, rfl⟩
      · intro j hj
        rw [hTl] at hj; simp only [BTree.leaves, List.mem_singleton] at hj; subst hj
        rw [lvM, Pi.single_eq_same, hnil]
    · simp only [cont, hnil, ↓reduceIte]
      refine ⟨hU, hnil, List.suffix_refl _, .leaf i, hpl, Pi.single i (n + 1), hseq, by simp, ?_⟩
      intro j hj
      simp only [BTree.leaves, List.mem_singleton] at hj; subst hj
      rw [lvM, Pi.single_eq_same]
  · refine proc_others hT hI.proc hF (p := p) ?_ ?_ (fun _ _ => rfl) le_rfl
      ((seq_le_cnt_root hT hG.root.1).trans hcle) (fun _ _ => by simp) (fun _ _ => rfl) i hi
    · intro j hj; rw [hC']; exact Function.update_of_ne hj _ _
    · intro j hj; rw [hC']

/-! ### Line 16: writing the combined partial snapshot into `u.view[ptr]` -/

lemma inv_step_wv (hT : T.WF) (hI : Inv T α C R L s₀) {p : P} {q : List Bool} {k : ℕ}
    {val : P → V} (hpc : (C.loc p).pc = .wv q k val)
    (h : (alg3 T v₀).step C (.tau p) = some C') :
    Inv T (α ++ [.tau p]) C' R L s₀ := by
  have hP := hI.proc p
  simp only [PInv, hpc] at hP
  obtain ⟨hu, hsuf, lt, rt, hsub, s, hs, hsi, hag⟩ := hP
  have hpend : C.pend p ≠ none := by rw [hu.1]; simp
  have hact : act T v₀ p (C.loc p) = .access (.view q k) (RWOp.write val)
      (fun _ => ⟨(C.loc p).cnt, cont q k⟩) := by simp [act, hpc]
  have hC' := tau_cfg hpend hact h
  simp only [objSpec] at hC'
  have hG := hI.g
  have hc : cntOf C' = cntOf C := by rw [hC']; exact cntOf_update rfl
  have hmem : C'.mem = Function.update C.mem (.view q k) val := by rw [hC']
  have hF : Frame T C.mem C'.mem (cntOf C) (cntOf C') R R := by
    rw [hmem, hc]
    refine Frame.write hT hG.chain le_rfl ?_ ?_
    · rintro j m - ⟨hj, rfl⟩
      exact BTree.ne_path_of_sub_node hsub j (hT.mem j) hj.symm
    · intro t s' hsub' hs' _
      rw [hsub] at hsub'; cases hsub'
      obtain rfl := SeqR.unique hG.chain hs' hs
      exact hag
  have hGI : GInv T C'.mem (cntOf C') R L s₀ :=
    GInv.frame hT hG hF (fun a => by rw [hmem, Function.update_of_ne (by simp)])
      (by rw [hmem, Function.update_of_ne (by simp)])
  refine ⟨hI.lin.append_tau p, hGI, fun i => ?_⟩
  rw [curOp_append_tau]
  by_cases hi : i = p
  · subst hi
    have hloc : C'.loc i = ⟨(C.loc i).cnt, cont q k⟩ := by rw [hC']; simp
    have hpd : C'.pend i = C.pend i := by rw [hC']
    rw [hloc, hpd]
    have hU : UpdLin T C'.mem L s₀ ⟨(C.loc i).cnt, cont q k⟩ (C.pend i) (curOp α i) i :=
      hu.frame (hF.lv i _ le_rfl) le_rfl (seq_le_cnt_root hT hG.root.1 i) (by simp)
    have hagv : Agr T C'.mem (.node lt rt) s val := hF.agr (seq_le_cnt hT hsub hs) hag
    have hvk : C'.mem (.view q k) = val := by rw [hmem]; simp
    unfold PInv
    by_cases hnil : q = []
    · subst hnil
      simp only [cont, ↓reduceIte]
      have hTn : T = .node lt rt := Option.some.inj hsub
      refine ⟨hU, s, ?_, hsi, ?_⟩
      · rw [hc, hTn]; exact hs
      · rw [hvk, hTn]; rw [hTn] at hagv; exact hagv
    · simp only [cont, hnil, ↓reduceIte]
      refine ⟨hU, hnil, hsuf, .node lt rt, hsub, s, by rw [hc]; exact hs, hsi, ?_⟩
      rw [hvk]; exact hagv
  · refine proc_others hT hI.proc hF (p := p) ?_ ?_ (fun _ _ => rfl) le_rfl
      (by rw [hc]; exact seq_le_cnt_root hT hG.root.1) (fun _ _ => by simp) (fun _ _ => rfl) i hi
    · intro j hj; rw [hC']; exact Function.update_of_ne hj _ _
    · intro j hj; rw [hC']

end Podc.LimitedUseSnapshots.Snapshot
