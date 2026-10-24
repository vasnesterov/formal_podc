import Papers.PODC2014.NetworkConstructors.CliquesReach

/-!
# Protocol 9 (`c`-Cliques): removing wrong edges and completing the cliques

Phases 5 and 6 of the reachability argument (see `CliquesReach.lean`): once only completed
components (with returned tokens) and at most one partial component are left,

5. every wrong edge `xy` (between followers of different leaders `a`, `b`) is removed by the
   sequence `a` visits `x`, `b` visits `y`, `(l'_i, l'_j, 1) → (l'_{i−1}, l'_{j−1}, 0)`, both tokens
   return (`cut_wrong`);
6. then every follower of degree `< c − 1` misses an edge to another follower of its own
   component, which also has degree `< c − 1`, and the rule `(i, j, 0)` adds it (`complete_all`).
-/

namespace Podc.NetworkConstructors.Cliques

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

variable {c : ℕ} {hc : 3 ≤ c} {V : Type*} [Fintype V] [DecidableEq V]
  {C : Config V (St c)} {p : V → V} {ht : V → ℕ}

/-! ### Structure of the configurations without `l̄` and `r` -/

theorem Inv.card_filter_pos (_hI : Inv C p ht) {z w : V} (hw : w ∈ kids p z) {P : St c → Bool}
    (hP : P (C.st w) = true) : 0 < ((kids p z).filter fun v => P (C.st v) = true).card :=
  Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨hw, hP⟩⟩

theorem Inv.p_ne_of_fol (hI : Inv C p ht) {x : V} (hx : (C.st x).isFol = true) : p x ≠ x :=
  hI.p_ne (by cases h : C.st x <;> simp_all [St.isFol, St.isRoot])

theorem Inv.mem_kids_parent (hI : Inv C p ht) {x : V} (hx : (C.st x).isFol = true) :
    x ∈ kids p (p x) :=
  mem_kids.2 ⟨rfl, (hI.p_ne_of_fol hx).symm⟩

/-- Without `r`, numbered followers are not visited. -/
theorem Inv.num_of_fol (hI : Inv C p ht) (hR : NoR C) {x : V} (hx : (C.st x).isFol = true) :
    ∃ k h1 h2, C.st x = .num k h1 h2 := by
  cases h : C.st x with
  | num k h1 h2 => exact ⟨k, h1, h2, rfl⟩
  | lp k h1 h2 =>
    exfalso
    have := hI.card_filter_pos (hI.mem_kids_parent hx) (P := St.isVis) (by simp [h, St.isVis])
    rw [hI.nvis] at this
    have hr := hR (p x)
    cases h' : C.st (p x) <;> simp_all [St.nvis]
  | _ => simp [h, St.isFol] at hx

/-- Without `l̄` and `r`, the parent of a numbered follower is a leader `l`. -/
theorem Inv.parent_lead (hI : Inv C p ht) (hL : NoLbar C) (hR : NoR C) {x : V}
    (hx : (C.st x).isFol = true) : C.st (p x) = .lead := by
  have := hI.card_filter_pos (hI.mem_kids_parent hx) (P := St.isFol) hx
  rw [hI.nfol] at this
  have hr := hR (p x)
  have hl := hL (p x)
  cases h' : C.st (p x) <;> simp_all [St.nfol, St.isLbar]

/-- A numbered follower is joined to a non-numbered agent only through its parent. -/
theorem Inv.edge_fol_nonfol (hI : Inv C p ht) {x y : V} (hxy : x ≠ y)
    (hx : (C.st x).isFol = true) (hy : (C.st y).isFol = false) :
    C.edge x y = true ↔ p x = y := by
  rw [hI.edge x y hxy (by simp [hy])]
  have hk : kids p x = ∅ := hI.kids_empty (by cases h : C.st x <;> simp_all [St.isFol, St.nkids])
  constructor
  · rintro (h | h)
    · exact h
    · have : y ∈ kids p x := mem_kids.2 ⟨h, Ne.symm hxy⟩
      simp [hk] at this
  · exact .inl

theorem card_le_deg {Q : Type*} {D : Config V Q} {x : V} {S : Finset V}
    (h : ∀ y ∈ S, y ≠ x ∧ D.edge x y = true) : S.card ≤ D.deg x :=
  Finset.card_le_card fun y hy => by simpa using h y hy

theorem deg_le_card {Q : Type*} {D : Config V Q} {x : V} {S : Finset V}
    (h : ∀ y, y ≠ x → D.edge x y = true → y ∈ S) : D.deg x ≤ S.card :=
  Finset.card_le_card fun y hy => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact h y hy.1 hy.2

/-! ### Phase 5: removing a wrong edge -/

/-- The macro step removing a wrong edge `xy` (`p x ≠ p y`): five interactions. -/
theorem cut_wrong (hI : Inv C p ht) (hL : NoLbar C) (hR : NoR C) {x y : V} (hxy : x ≠ y)
    {i hi1 hi2 j hj1 hj2} (hxi : C.st x = .num i hi1 hi2) (hyj : C.st y = .num j hj1 hj2)
    (he : C.edge x y = true) (hp : p x ≠ p y) :
    ∃ E, (cliques c hc).Reachable C E ∧ Inv E p ht ∧
      (∀ z, z ≠ x → z ≠ y → E.st z = C.st z) ∧
      ∃ i' hi1' hi2' j' hj1' hj2', E.st x = .num i' hi1' hi2' ∧ E.st y = .num j' hj1' hj2' ∧
        i' + 1 = i ∧ j' + 1 = j := by
  have hx : (C.st x).isFol = true := by simp [hxi, St.isFol]
  have hy : (C.st y).isFol = true := by simp [hyj, St.isFol]
  have ha : C.st (p x) = .lead := hI.parent_lead hL hR hx
  have hb : C.st (p y) = .lead := hI.parent_lead hL hR hy
  generalize hav : p x = a at ha hp
  generalize hbv : p y = b at hb hp
  have hax : a ≠ x := hav ▸ hI.p_ne_of_fol hx
  have hby : b ≠ y := hbv ▸ hI.p_ne_of_fol hy
  have hay : a ≠ y := fun h => by subst h; rw [hyj] at ha; cases ha
  have hbx : b ≠ x := fun h => by subst h; rw [hxi] at hb; cases hb
  have hea : C.edge a x = true := (hI.edge a x hax (by simp [ha, St.isFol])).2 (.inr hav)
  have heb : C.edge b y = true := (hI.edge b y hby (by simp [hb, St.isFol])).2 (.inr hbv)
  -- the numbers are at least 2
  have hi : 2 ≤ i := by
    have h := card_le_deg (D := C) (x := x) (S := {a, y}) (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ⟨hax, by rw [C.symm]; exact hea⟩
      · exact ⟨Ne.symm hxy, he⟩)
    rw [hI.deg x hx, hxi, Finset.card_pair hay] at h
    simpa [St.idx] using h
  have hj : 2 ≤ j := by
    have h := card_le_deg (D := C) (x := y) (S := {b, x}) (by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact ⟨hby, by rw [C.symm]; exact heb⟩
      · exact ⟨hxy, by rw [C.symm]; exact he⟩)
    rw [hI.deg y hy, hyj, Finset.card_pair hbx] at h
    simpa [St.idx] using h
  -- step 1: `a` visits `x`
  have hI1 := hI.visit (hc := hc) hax ha hxi hea
  generalize hC1 : (cliques c hc).interact C a x = C1 at hI1
  have h1a : C1.st a = .r := by rw [← hC1]; simp [ha, hxi, hea, δ]
  have h1x : C1.st x = .lp i hi1 hi2 := by
    rw [← hC1, Protocol.interact_st_right C hax]; simp [ha, hxi, hea, δ]
  have h1o : ∀ z, z ≠ a → z ≠ x → C1.st z = C.st z := fun z h1 h2 => by
    rw [← hC1]; exact Protocol.interact_st_other C h1 h2
  have h1e : C1.edge = C.edge := by
    rw [← hC1]; exact Protocol.interact_edge_of_edge_eq (by simp [ha, hxi, hea, δ])
  -- step 2: `b` visits `y`
  have hI2 := hI1.visit (hc := hc) hby (by rw [h1o b hp.symm hbx, hb])
    (by rw [h1o y (Ne.symm hay) (Ne.symm hxy), hyj]) (by rw [h1e, heb])
  generalize hC2 : (cliques c hc).interact C1 b y = C2 at hI2
  have h2b : C2.st b = .r := by
    rw [← hC2]; simp [h1o b hp.symm hbx, hb, h1o y (Ne.symm hay) (Ne.symm hxy), hyj, h1e, heb, δ]
  have h2y : C2.st y = .lp j hj1 hj2 := by
    rw [← hC2, Protocol.interact_st_right C1 hby]
    simp [h1o b hp.symm hbx, hb, h1o y (Ne.symm hay) (Ne.symm hxy), hyj, h1e, heb, δ]
  have h2o : ∀ z, z ≠ b → z ≠ y → C2.st z = C1.st z := fun z h1 h2 => by
    rw [← hC2]; exact Protocol.interact_st_other C1 h1 h2
  have h2e : C2.edge = C.edge := by
    rw [← hC2, Protocol.interact_edge_of_edge_eq, h1e]
    simp [h1o b hp.symm hbx, hb, h1o y (Ne.symm hay) (Ne.symm hxy), hyj, h1e, heb, δ]
  -- step 3: the visited followers cut the wrong edge
  have h2x : C2.st x = .lp i hi1 hi2 := by rw [h2o x (Ne.symm hbx) hxy, h1x]
  have hI3 := hI2.cut (hc := hc) hxy h2x h2y hi hj (by rw [h2e, he])
  generalize hC3 : (cliques c hc).interact C2 x y = C3 at hI3
  have h3x : C3.st x = .lp (i - 1) (by omega) (by omega) := by
    rw [← hC3]; simp [h2x, h2y, h2e, he, δ, hi, hj]
  have h3y : C3.st y = .lp (j - 1) (by omega) (by omega) := by
    rw [← hC3, Protocol.interact_st_right C2 hxy]; simp [h2x, h2y, h2e, he, δ, hi, hj]
  have h3o : ∀ z, z ≠ x → z ≠ y → C3.st z = C2.st z := fun z h1 h2 => by
    rw [← hC3]; exact Protocol.interact_st_other C2 h1 h2
  have h3e : ∀ z w, ¬((z = x ∧ w = y) ∨ (z = y ∧ w = x)) → C3.edge z w = C.edge z w :=
    fun z w h => by rw [← hC3, Protocol.interact_edge_other C2 h, h2e]
  -- step 4: the token of `a` returns
  have h3a : C3.st a = .r := by rw [h3o a hax hay, h2o a hp hay, h1a]
  have hI4 := hI3.back (hc := hc) (Ne.symm hax) h3x h3a
    (by rw [h3e x a (by tauto), C.symm]; exact hea)
  generalize hC4 : (cliques c hc).interact C3 x a = C4 at hI4
  have h4x : C4.st x = .num (i - 1) (by omega) (by omega) := by
    rw [← hC4]; simp [h3x, h3a, h3e x a (by tauto), C.symm x a, hea, δ]
  have h4a : C4.st a = .lead := by
    rw [← hC4, Protocol.interact_st_right C3 (Ne.symm hax)]
    simp [h3x, h3a, h3e x a (by tauto), C.symm x a, hea, δ]
  have h4o : ∀ z, z ≠ x → z ≠ a → C4.st z = C3.st z := fun z h1 h2 => by
    rw [← hC4]; exact Protocol.interact_st_other C3 h1 h2
  have h4e : C4.edge y b = C.edge y b := by
    rw [← hC4, Protocol.interact_edge_other C3 (by tauto), h3e y b (by tauto)]
  -- step 5: the token of `b` returns
  have h4y : C4.st y = .lp (j - 1) (by omega) (by omega) := by
    rw [h4o y (Ne.symm hxy) (Ne.symm hay), h3y]
  have h4b : C4.st b = .r := by
    rw [h4o b hbx (Ne.symm hp), h3o b hbx hby, h2b]
  have hI5 := hI4.back (hc := hc) (Ne.symm hby) h4y h4b (by rw [h4e, C.symm]; exact heb)
  generalize hC5 : (cliques c hc).interact C4 y b = C5 at hI5
  have h5y : C5.st y = .num (j - 1) (by omega) (by omega) := by
    rw [← hC5]; simp [h4y, h4b, h4e, C.symm y b, heb, δ]
  have h5b : C5.st b = .lead := by
    rw [← hC5, Protocol.interact_st_right C4 (Ne.symm hby)]
    simp [h4y, h4b, h4e, C.symm y b, heb, δ]
  have h5o : ∀ z, z ≠ y → z ≠ b → C5.st z = C4.st z := fun z h1 h2 => by
    rw [← hC5]; exact Protocol.interact_st_other C4 h1 h2
  refine ⟨C5, ?_, hI5, fun z hzx hzy => ?_, i - 1, by omega, by omega, j - 1, by omega, by omega,
    by rw [h5o x hxy hbx.symm, h4x], h5y, by omega, by omega⟩
  · rw [← hC5, ← hC4, ← hC3, ← hC2, ← hC1]
    exact (Protocol.reachable_of_ne hax).trans <| (Protocol.reachable_of_ne hby).trans <|
      (Protocol.reachable_of_ne hxy).trans <| (Protocol.reachable_of_ne (Ne.symm hax)).trans <|
      Protocol.reachable_of_ne (Ne.symm hby)
  · by_cases hzb : z = b
    · subst hzb; rw [h5b, hb]
    by_cases hza : z = a
    · subst hza; rw [h5o z hzy hzb, h4a, ha]
    rw [h5o z hzy hzb, h4o z hzx hza, h3o z hzx hzy, h2o z hzb hzy, h1o z hza hzx]

/-- **Phase 5.** All wrong edges can be removed. -/
theorem cut_all (C : Config V (St c))
    (hC : Inv C p ht ∧ NoFi C ∧ OnePartial C ∧ NoLbar C ∧ NoR C) :
    ∃ D, (cliques c hc).Reachable C D ∧ (Inv D p ht ∧ NoFi D ∧ OnePartial D ∧ NoLbar D ∧ NoR D) ∧
      NoWrong D p := by
  refine reach_good (R := (cliques c hc).Step)
    (fun D => Inv D p ht ∧ NoFi D ∧ OnePartial D ∧ NoLbar D ∧ NoR D) (fun D => NoWrong D p)
    (wsum St.idx) ?_ C hC
  rintro C ⟨hI, hF, hO, hL, hR⟩ hg
  simp only [NoWrong, not_forall] at hg
  obtain ⟨x, y, hxy, hx, hy, he, hp⟩ := hg
  obtain ⟨i, hi1, hi2, hxi⟩ := hI.num_of_fol hR hx
  obtain ⟨j, hj1, hj2, hyj⟩ := hI.num_of_fol hR hy
  obtain ⟨E, hCE, hIE, hEo, i', hi1', hi2', j', hj1', hj2', hEx, hEy, hii, hjj⟩ :=
    cut_wrong (hc := hc) hI hL hR hxy hxi hyj he hp
  have hW := wsum_change (w := St.idx) hxy hEo
  rw [hxi, hyj, hEx, hEy] at hW
  simp only [St.idx] at hW
  refine ⟨E, hCE, ⟨hIE, forall_of_change (P := fun q => q.isFi = false) hF hEo ?_ ?_,
    onePartial_of_change hO hEo ?_ ?_, forall_of_change (P := fun q => q.isLbar = false) hL hEo ?_ ?_,
    forall_of_change (P := fun q => q ≠ .r) hR hEo ?_ ?_⟩, .inr (by omega)⟩ <;>
    first | (rw [hEx]; simp [St.isFi, St.isL, St.isLbar]) | (rw [hEy]; simp [St.isFi, St.isL, St.isLbar])

/-! ### Phase 6: completing the cliques -/

/-- **Phase 6.** Once there are no wrong edges, all missing edges inside components are added. -/
theorem complete_all (C : Config V (St c))
    (hC : Inv C p ht ∧ NoFi C ∧ OnePartial C ∧ NoLbar C ∧ NoR C ∧ NoWrong C p) :
    ∃ D, (cliques c hc).Reachable C D ∧
      (Inv D p ht ∧ NoFi D ∧ OnePartial D ∧ NoLbar D ∧ NoR D ∧ NoWrong D p) ∧ Full D := by
  refine reach_good (R := (cliques c hc).Step)
    (fun D => Inv D p ht ∧ NoFi D ∧ OnePartial D ∧ NoLbar D ∧ NoR D ∧ NoWrong D p) Full
    (wsum wMiss) ?_ C hC
  rintro C ⟨hI, hF, hO, hL, hR, hW⟩ hg
  simp only [Full, not_forall] at hg
  obtain ⟨x, hx, hxc⟩ := hg
  obtain ⟨k, hk1, hk2, hxk⟩ := hI.num_of_fol hR hx
  rw [hxk] at hxc
  simp only [St.idx] at hxc
  have hk : k < c - 1 := by omega
  have ha : C.st (p x) = .lead := hI.parent_lead hL hR hx
  generalize hav : p x = a at ha
  have hax : a ≠ x := hav ▸ hI.p_ne_of_fol hx
  have hxa : x ∈ kids p a := hav ▸ hI.mem_kids_parent hx
  have haa : a ∉ kids p a := by simp
  have hka : (kids p a).card = c - 1 := by rw [hI.nkids, ha]; rfl
  have hfol : ∀ w ∈ kids p a, (C.st w).isFol = true := by
    have h := hI.nfol a
    rw [ha] at h
    simp only [St.nfol] at h
    rw [← hka] at h
    exact Finset.filter_card_eq h
  -- a follower `y` of `a` not adjacent to `x`
  obtain ⟨y, hy, hyx, hexy⟩ : ∃ y ∈ kids p a, y ≠ x ∧ C.edge x y = false := by
    by_contra hno
    push Not at hno
    have h := card_le_deg (D := C) (x := x) (S := insert a ((kids p a).erase x)) (by
      intro z hz
      rcases Finset.mem_insert.1 hz with rfl | hz
      · exact ⟨hax, by
          rw [C.symm]; exact (hI.edge z x hax (by simp [ha, St.isFol])).2 (.inr hav)⟩
      · have hz' := Finset.mem_erase.1 hz
        exact ⟨hz'.1, by simpa using hno z hz'.2 hz'.1⟩)
    rw [Finset.card_insert_of_notMem (fun h => haa (Finset.mem_of_mem_erase h)),
      Finset.card_erase_of_mem hxa, hka, hI.deg x hx, hxk] at h
    simp only [St.idx] at h
    omega
  have hy' := mem_kids.1 hy
  obtain ⟨j, hj1, hj2, hyj⟩ := hI.num_of_fol hR (hfol y hy)
  have hxy : x ≠ y := Ne.symm hyx
  have hj : j < c - 1 := by
    have h := deg_le_card (D := C) (x := y) (S := insert a (((kids p a).erase y).erase x)) (by
      intro z hzy hez
      by_cases hzf : (C.st z).isFol = true
      · have hpz : p z = a := (hW y z (Ne.symm hzy) (hfol y hy) hzf hez).symm.trans hy'.1
        have hzx : z ≠ x := by
          rintro rfl; rw [C.symm] at hez; rw [hez] at hexy; exact Bool.noConfusion hexy
        exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hzx, Finset.mem_erase.2
          ⟨hzy, mem_kids.2 ⟨hpz, fun h => by rw [h, ha] at hzf; simp [St.isFol] at hzf⟩⟩⟩)
      · have := (hI.edge_fol_nonfol (Ne.symm hzy) (hfol y hy) (by simpa using hzf)).1 hez
        rw [hy'.1] at this
        rw [← this]; exact Finset.mem_insert_self _ _)
    have hc1 := Finset.card_insert_le a (((kids p a).erase y).erase x)
    rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hyx.symm, hxa⟩),
      Finset.card_erase_of_mem hy, hka] at hc1
    rw [hI.deg y (hfol y hy), hyj] at h
    simp only [St.idx] at h
    omega
  have hI' := hI.connect (hc := hc) hxy hxk hyj hk hj hexy
  obtain ⟨hDx, hDy, hDo⟩ := interact_states (hc := hc) (C := C) hxy
  rw [hxk, hyj, hexy] at hDx hDy
  simp only [δ, hk, hj, and_self, dite_true] at hDx hDy
  have hWc := wsum_change (w := wMiss) hxy hDo
  rw [hxk, hyj, hDx, hDy] at hWc
  simp only [wMiss] at hWc
  refine ⟨_, Protocol.reachable_of_ne hxy, ⟨hI',
    forall_of_change (P := fun q => q.isFi = false) hF hDo (by rw [hDx]; rfl) (by rw [hDy]; rfl),
    onePartial_of_change hO hDo (by rw [hDx]; rfl) (by rw [hDy]; rfl),
    forall_of_change (P := fun q => q.isLbar = false) hL hDo (by rw [hDx]; rfl) (by rw [hDy]; rfl),
    forall_of_change (P := fun q => q ≠ .r) hR hDo (by rw [hDx]; simp) (by rw [hDy]; simp),
    ?_⟩, .inr (by omega)⟩
  -- no wrong edge is created
  have hfolD : ∀ z, (((cliques c hc).interact C x y).st z).isFol = (C.st z).isFol := by
    intro z
    by_cases hzx : z = x
    · subst hzx; rw [hDx, hxk]; rfl
    by_cases hzy : z = y
    · subst hzy; rw [hDy, hyj]; rfl
    rw [hDo z hzx hzy]
  intro z w hzw hz hw hezw
  rw [hfolD] at hz hw
  by_cases hp : (z = x ∧ w = y) ∨ (z = y ∧ w = x)
  · rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hav, hy'.1]
    · rw [hav, hy'.1]
  · rw [Protocol.interact_edge_other C hp] at hezw
    exact hW z w hzw hz hw hezw

end Podc.NetworkConstructors.Cliques
