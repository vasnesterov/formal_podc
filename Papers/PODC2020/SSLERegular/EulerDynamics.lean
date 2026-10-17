import Papers.PODC2020.SSLERegular.EulerStructure

/-!
# One interaction of the repaired SS-EulerCycle in a coherent configuration

`Base S C`: the configuration `C` has skeleton `S` (colours and slot colours), satisfies the
SS-TwoHop bit invariant (`BitInv`: matched pairs have equal `colorBit`s, so SS-TwoHop never
recolours) and has no error flag. If `S` is coherent (`InjCol`, `EdgeOK`, `2k`-regular graph), an
interaction between the two endpoints of a virtual edge `w → σ w` (in either role) runs exactly
the Ring-Protocol and SS-Token on that virtual edge (`interact_fwd`, `interact_bwd`); unless
tokens sit on both interacting nodes afterwards, the result is again `Base S` and only the two
virtual nodes `w`, `σ w` change.
-/

set_option linter.unusedSectionVars false

open Finset

namespace SSLERegular

variable {RS : Type*} {k : ℕ} {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The virtual node `w = (v, i)` of a configuration. -/
def vn (C : V → EState k RS) (w : V × Fin k) : VNode k RS := (C w.1).node w.2

variable (G)

/-- SS-TwoHop invariant: matched pairs have equal colour bits. -/
def BitInv (C : V → EState k RS) : Prop :=
  ∀ u v, G.Adj u v → (C u).prevColor = (C v).color → (C v).prevColor = (C u).color →
    (C u).colorBit = (C v).colorBit

/-- No error flag is set. -/
def NoErr (C : V → EState k RS) : Prop := ∀ v, (C v).errFlag = false

/-- The base invariant for a fixed skeleton. -/
def Base (S : V → Skel k) (C : V → EState k RS) : Prop :=
  (∀ v, skel (C v) = S v) ∧ BitInv G C ∧ NoErr C

variable {G}

lemma fmatch_iff_vedge {S : V → Skel k} {C : V → EState k RS} (hS : ∀ v, skel (C v) = S v)
    {u x : V} (h : G.Adj u x) (i j : Fin k) : FMatch (C u) (C x) i j ↔ VEdge G S u i x j := by
  have hu := hS u; have hx := hS x
  simp only [skel] at hu hx
  unfold VEdge
  rw [← hu, ← hx]
  simp [FMatch, h]

lemma twoHopE_noconf (rc1 rc2 : Fin (4 * k ^ 2)) (rb : Bool) {u v : EState k RS}
    (h : u.prevColor = v.color → v.prevColor = u.color → u.colorBit = v.colorBit) :
    twoHopE rc1 rc2 rb u v = (u.withPrev v.color rb, v.withPrev u.color rb) := by
  unfold twoHopE
  rw [if_neg (by rintro ⟨h1, h2, h3⟩; exact h3 (h h1 h2))]
  rfl

/-- The bit invariant after an interaction of `u` and `x` that keeps colours. -/
lemma bitInv_upd {S : V → Skel k} (hinj : InjCol G S) {C : V → EState k RS}
    (hS : ∀ v, skel (C v) = S v) (hB : BitInv G C) {u x : V} (hux : G.Adj u x)
    (o : EState k RS × EState k RS) (h1 : skel o.1 = S u) (h2 : skel o.2 = S x)
    (hp1 : o.1.prevColor = (C x).color) (hp2 : o.2.prevColor = (C u).color)
    (hb : o.1.colorBit = o.2.colorBit) : BitInv G (upd C u x o) := by
  have hne : u ≠ x := G.ne_of_adj hux
  set D := upd C u x o
  have hDu : D u = o.1 := upd_left _ hne _
  have hDx : D x = o.2 := upd_right _ _ _ _
  have hDo : ∀ z, z ≠ u → z ≠ x → D z = C z := fun z h1 h2 => upd_other _ h1 h2 _
  have col : ∀ z, (D z).color = (S z).1 := by
    intro z
    by_cases hzx : z = x
    · subst hzx; rw [hDx]; exact congrArg Prod.fst h2
    by_cases hzu : z = u
    · subst hzu; rw [hDu]; exact congrArg Prod.fst h1
    rw [hDo z hzu hzx]; exact congrArg Prod.fst (hS z)
  have colC : ∀ z, (C z).color = (S z).1 := fun z => congrArg Prod.fst (hS z)
  intro a b hab ha hb'
  rw [col] at ha hb'
  by_cases hau : a = u
  · subst hau
    by_cases hbx : b = x
    · subst hbx; rw [hDu, hDx]; exact hb
    · exfalso; rw [hDu, hp1, colC] at ha; exact hbx (hinj a x b hux hab ha).symm
  by_cases hax : a = x
  · subst hax
    by_cases hbu : b = u
    · subst hbu; rw [hDu, hDx]; exact hb.symm
    · exfalso; rw [hDx, hp2, colC] at ha; exact hbu (hinj a u b hux.symm hab ha).symm
  by_cases hbu : b = u
  · subst hbu; exfalso; rw [hDu, hp1, colC] at hb'
    exact hax (hinj b x a hux hab.symm hb').symm
  by_cases hbx : b = x
  · subst hbx; exfalso; rw [hDx, hp2, colC] at hb'
    exact hau (hinj b u a hux.symm hab.symm hb').symm
  rw [hDo a hau hax, hDo b hbu hbx]
  rw [hDo a hau hax] at ha; rw [hDo b hbu hbx] at hb'
  exact hB a b hab (by rw [colC]; exact ha) (by rw [colC]; exact hb')

section Interact

variable [Fintype V] [DecidableRel G.Adj] {S : V → Skel k}
  (hdeg : ∀ v, G.degree v = 2 * k) (hinj : InjCol G S) (hok : EdgeOK G S)
  (R : RingProtocol RS)

/-- The virtual-node view after running the ring and token step on the virtual edge
`w → σ w` with ring selection `ρ`. -/
noncomputable def vnAfter (C : V → EState k RS) (ρ : RS → RS → RS × RS) (w : V × Fin k) :
    V × Fin k → VNode k RS :=
  Function.update (Function.update (vn C) w
      (vEdge R ρ (vn C w) (vn C (vperm hdeg hinj hok w))).1)
    (vperm hdeg hinj hok w) (vEdge R ρ (vn C w) (vn C (vperm hdeg hinj hok w))).2

/-- Tokens on both endpoints `a` (as `u` in `tokenDetect`) and `b` (as `v`). -/
def TokBoth (F : V × Fin k → VNode k RS) (a b : V) : Prop :=
  ∃ p q, (F (b, p)).token = true ∧ (F (a, q)).token = true

lemma node_ne_vperm (w : V × Fin k) : w.1 ≠ (vperm hdeg hinj hok w).1 :=
  G.ne_of_adj (adj_vperm hdeg hinj hok w)

/-- The node states after the ring/token step (before error detection), in terms of
`vnAfter`. -/
lemma runEdge_eq_vnAfter (C : V → EState k RS) (ρ : RS → RS → RS × RS) (w : V × Fin k)
    (cu cx : Fin (4 * k ^ 2)) (b : Bool) :
    (∀ l, ((runEdge R ρ ((C w.1).withPrev cu b) ((C (vperm hdeg hinj hok w).1).withPrev cx b) w.2
      (vperm hdeg hinj hok w).2).1.node l) = vnAfter hdeg hinj hok R C ρ w (w.1, l)) ∧
    (∀ l, ((runEdge R ρ ((C w.1).withPrev cu b) ((C (vperm hdeg hinj hok w).1).withPrev cx b) w.2
      (vperm hdeg hinj hok w).2).2.node l) =
        vnAfter hdeg hinj hok R C ρ w ((vperm hdeg hinj hok w).1, l)) := by
  have hne : w.1 ≠ (vperm hdeg hinj hok w).1 := node_ne_vperm hdeg hinj hok w
  constructor
  · intro l
    simp only [runEdge, vnAfter, EState.withPrev, Function.update_apply, vn, Prod.ext_iff]
    by_cases hl : l = w.2
    · subst hl; simp [hne]
    · simp [hl, hne]
  · intro l
    simp only [runEdge, vnAfter, EState.withPrev, Function.update_apply, vn, Prod.ext_iff]
    by_cases hl : l = (vperm hdeg hinj hok w).2
    · subst hl; simp
    · simp [hl, Ne.symm hne]

lemma vn_upd_of_nodes (C : V → EState k RS) (w : V × Fin k) (o : EState k RS × EState k RS)
    (h1 : ∀ l, o.1.node l = vnAfter hdeg hinj hok R C ρ w (w.1, l))
    (h2 : ∀ l, o.2.node l = vnAfter hdeg hinj hok R C ρ w ((vperm hdeg hinj hok w).1, l)) :
    vn (upd C w.1 (vperm hdeg hinj hok w).1 o) = vnAfter hdeg hinj hok R C ρ w := by
  have hne := node_ne_vperm hdeg hinj hok w
  funext ⟨z, l⟩
  by_cases hzx : z = (vperm hdeg hinj hok w).1
  · subst hzx; simp only [vn, upd_right]; exact h2 l
  by_cases hzu : z = w.1
  · subst hzu; simp only [vn]; rw [upd_left _ hne]; exact h1 l
  simp only [vn]
  rw [upd_other _ hzu hzx]
  simp only [vnAfter]
  rw [Function.update_of_ne (fun h => hzx (congrArg Prod.fst h)),
    Function.update_of_ne (fun h => hzu (congrArg Prod.fst h))]
  rfl

/-- **Forward interaction**: initiator = node of `w`, responder = node of `σ w`. -/
lemma interact_fwd {C : V → EState k RS} (hC : Base G S C) (w : V × Fin k) (ch : EChoice k RS)
    (hch : ch.Valid R) :
    let u := w.1
    let x := (vperm hdeg hinj hok w).1
    let D := upd C u x (eulerStep true R ch (C u) (C x))
    let F := vnAfter hdeg hinj hok R C ch.ρ w
    (TokBoth F u x → (D u).errFlag = ch.b1) ∧ (¬ TokBoth F u x → Base G S D ∧ vn D = F) := by
  intro u x D F
  obtain ⟨hS, hB, hN⟩ := hC
  have hne : u ≠ x := node_ne_vperm hdeg hinj hok w
  have hux : G.Adj u x := adj_vperm hdeg hinj hok w
  have hE := vedge_vperm hdeg hinj hok w
  have h2h := twoHopE_noconf ch.rc1 ch.rc2 ch.rb (hB u x hux)
  -- the match found is the virtual edge `w → σ w`
  have hsk1 : ∀ v (c : Fin (4 * k ^ 2)) b, skel ((C v).withPrev c b) = S v := fun v c b => hS v
  have hfm : ∀ i j, FMatch ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)
      i j ↔ VEdge G S u i x j := by
    intro i j
    rw [fmatch_of_skel ((hsk1 u _ _).trans (hS u).symm) ((hsk1 x _ _).trans (hS x).symm)]
    exact fmatch_iff_vedge hS hux i j
  have hex : ∃ i j, FMatch ((C u).withPrev (C x).color ch.rb)
      ((C x).withPrev (C u).color ch.rb) i j := ⟨w.2, _, (hfm _ _).2 hE⟩
  have hpick := (hfm _ _).1 (hch.2 _ _ hex)
  have hp1 : (ch.pick ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)).1
      = w.2 := (vedge_succ_unique hdeg hinj hok hE hpick).symm
  have hp2 : (ch.pick ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)).2
      = (vperm hdeg hinj hok w).2 := (vedge_pred_unique hdeg hinj hok hE hpick).symm
  have hrp : ringPart true R ch ((C u).withPrev (C x).color ch.rb)
      ((C x).withPrev (C u).color ch.rb) = runEdge R ch.ρ ((C u).withPrev (C x).color ch.rb)
      ((C x).withPrev (C u).color ch.rb) w.2 (vperm hdeg hinj hok w).2 := by
    unfold ringPart; rw [if_pos hex, hp1, hp2]
  obtain ⟨hn1, hn2⟩ := runEdge_eq_vnAfter hdeg hinj hok R C ch.ρ w (C x).color (C u).color ch.rb
  set o := runEdge R ch.ρ ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)
    w.2 (vperm hdeg hinj hok w).2 with ho
  have htok : (∃ p q, (o.2.node p).token = true ∧ (o.1.node q).token = true) ↔ TokBoth F u x := by
    simp only [TokBoth, F]
    constructor
    · rintro ⟨p, q, a, b⟩; exact ⟨p, q, by rw [← hn2]; exact a, by rw [← hn1]; exact b⟩
    · rintro ⟨p, q, a, b⟩; exact ⟨p, q, by rw [hn2]; exact a, by rw [hn1]; exact b⟩
  have hD : D = upd C u x (randChangeE ch (tokenDetect o)) := by
    simp only [D, eulerStep]; rw [h2h]; simp only; rw [hrp]
  have hoerr : o.1.errFlag = false := by rw [ho]; simp [runEdge, EState.withPrev, hN u]
  constructor
  · intro hT
    rw [hD, upd_left _ hne]
    have : (tokenDetect o).1.errFlag = true := by
      unfold tokenDetect; rw [if_pos (htok.2 hT)]
    simp [randChangeE, this]
  · intro hT
    have htd : tokenDetect o = o := by unfold tokenDetect; rw [if_neg (fun h => hT (htok.1 h))]
    have hrc : randChangeE ch o = o := by unfold randChangeE; rw [if_neg (by simp [hoerr])]
    rw [htd, hrc] at hD
    obtain ⟨⟨f1, f1p, f1b⟩, ⟨f2, f2p, f2b⟩⟩ := runEdge_frame R ch.ρ
      ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)
      w.2 (vperm hdeg hinj hok w).2
    rw [← ho] at f1 f1p f1b f2 f2p f2b
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro v
      rw [hD]
      by_cases hvx : v = x
      · rw [hvx, upd_right, f2]; exact hS _
      by_cases hvu : v = u
      · rw [hvu, upd_left _ hne, f1]; exact hS _
      rw [upd_other _ hvu hvx]; exact hS v
    · rw [hD]
      exact bitInv_upd hinj hS hB hux o (f1.trans (hS u)) (f2.trans (hS x))
        (by rw [f1p]; rfl) (by rw [f2p]; rfl) (by rw [f1b, f2b]; rfl)
    · intro v
      rw [hD]
      by_cases hvx : v = x
      · rw [hvx, upd_right, ho]; simp [runEdge, EState.withPrev, hN x]
      by_cases hvu : v = u
      · rw [hvu, upd_left _ hne]; exact hoerr
      rw [upd_other _ hvu hvx]; exact hN v
    · rw [hD]; exact vn_upd_of_nodes hdeg hinj hok R C w o hn1 hn2

lemma upd_swap {Q : Type*} (C : V → Q) {u x : V} (h : u ≠ x) (o : Q × Q) :
    upd C x u o.swap = upd C u x o := by
  funext z
  by_cases hzx : z = x
  · subst hzx; rw [upd_left _ (Ne.symm h), upd_right]; rfl
  by_cases hzu : z = u
  · subst hzu; rw [upd_right, upd_left _ h]; rfl
  rw [upd_other _ hzx hzu, upd_other _ hzu hzx]

/-- **Backward interaction**: initiator = node of `σ w`, responder = node of `w` (the repair:
the virtual edge `w → σ w` is used in the reverse role). -/
lemma interact_bwd {C : V → EState k RS} (hC : Base G S C) (w : V × Fin k) (ch : EChoice k RS)
    (hch : ch.Valid R) :
    (TokBoth (vnAfter hdeg hinj hok R C ch.ρ w) (vperm hdeg hinj hok w).1 w.1 →
      (upd C (vperm hdeg hinj hok w).1 w.1 (eulerStep true R ch (C (vperm hdeg hinj hok w).1)
        (C w.1)) (vperm hdeg hinj hok w).1).errFlag = ch.b1) ∧
    (¬ TokBoth (vnAfter hdeg hinj hok R C ch.ρ w) (vperm hdeg hinj hok w).1 w.1 →
      Base G S (upd C (vperm hdeg hinj hok w).1 w.1 (eulerStep true R ch
        (C (vperm hdeg hinj hok w).1) (C w.1))) ∧
      vn (upd C (vperm hdeg hinj hok w).1 w.1 (eulerStep true R ch (C (vperm hdeg hinj hok w).1)
        (C w.1))) = vnAfter hdeg hinj hok R C ch.ρ w) := by
  set u := w.1 with hu
  set x := (vperm hdeg hinj hok w).1 with hx
  set F := vnAfter hdeg hinj hok R C ch.ρ w with hF
  obtain ⟨hS, hB, hN⟩ := hC
  have hne : u ≠ x := node_ne_vperm hdeg hinj hok w
  have hux : G.Adj u x := adj_vperm hdeg hinj hok w
  have hE := vedge_vperm hdeg hinj hok w
  have h2h := twoHopE_noconf ch.rc1 ch.rc2 ch.rb (hB x u hux.symm)
  have hsk1 : ∀ v (c : Fin (4 * k ^ 2)) b, skel ((C v).withPrev c b) = S v := fun v c b => hS v
  have hfm : ∀ i j, FMatch ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)
      i j ↔ VEdge G S u i x j := by
    intro i j
    rw [fmatch_of_skel ((hsk1 u _ _).trans (hS u).symm) ((hsk1 x _ _).trans (hS x).symm)]
    exact fmatch_iff_vedge hS hux i j
  have hnot : ¬ ∃ i j, FMatch ((C x).withPrev (C u).color ch.rb)
      ((C u).withPrev (C x).color ch.rb) i j := by
    rintro ⟨i, j, h⟩
    rw [fmatch_of_skel ((hsk1 x _ _).trans (hS x).symm) ((hsk1 u _ _).trans (hS u).symm),
      fmatch_iff_vedge hS hux.symm i j] at h
    exact edge_not_rev hdeg hinj hok hE i j h
  have hex : ∃ i j, FMatch ((C u).withPrev (C x).color ch.rb)
      ((C x).withPrev (C u).color ch.rb) i j := ⟨w.2, _, (hfm _ _).2 hE⟩
  have hpick := (hfm _ _).1 (hch.2 _ _ hex)
  have hp1 : (ch.pick ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)).1
      = w.2 := (vedge_succ_unique hdeg hinj hok hE hpick).symm
  have hp2 : (ch.pick ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)).2
      = (vperm hdeg hinj hok w).2 := (vedge_pred_unique hdeg hinj hok hE hpick).symm
  set o := runEdge R ch.ρ ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)
    w.2 (vperm hdeg hinj hok w).2 with ho
  have hrp : ringPart true R ch ((C x).withPrev (C u).color ch.rb)
      ((C u).withPrev (C x).color ch.rb) = o.swap := by
    unfold ringPart; rw [if_neg hnot, if_pos ⟨rfl, hex⟩, hp1, hp2]
  obtain ⟨hn1, hn2⟩ := runEdge_eq_vnAfter hdeg hinj hok R C ch.ρ w (C x).color (C u).color ch.rb
  have htok : (∃ p q, (o.swap.2.node p).token = true ∧ (o.swap.1.node q).token = true) ↔
      TokBoth F x u := by
    simp only [TokBoth, hF, Prod.fst_swap, Prod.snd_swap]
    constructor
    · rintro ⟨p, q, a, b⟩; exact ⟨p, q, by rw [← hn1]; exact a, by rw [← hn2]; exact b⟩
    · rintro ⟨p, q, a, b⟩; exact ⟨p, q, by rw [hn1]; exact a, by rw [hn2]; exact b⟩
  have hD : upd C x u (eulerStep true R ch (C x) (C u)) =
      upd C x u (randChangeE ch (tokenDetect o.swap)) := by
    simp only [eulerStep]; rw [h2h]; simp only; rw [hrp]
  have hoerr : o.swap.1.errFlag = false := by rw [ho]; simp [runEdge, EState.withPrev, hN x]
  constructor
  · intro hT
    rw [hD, upd_left _ (Ne.symm hne)]
    have : (tokenDetect o.swap).1.errFlag = true := by
      unfold tokenDetect; rw [if_pos (htok.2 hT)]
    simp [randChangeE, this]
  · intro hT
    have htd : tokenDetect o.swap = o.swap := by
      unfold tokenDetect; rw [if_neg (fun h => hT (htok.1 h))]
    have hrc : randChangeE ch o.swap = o.swap := by
      unfold randChangeE; rw [if_neg (by rw [hoerr]; simp)]
    rw [htd, hrc, upd_swap C hne] at hD
    obtain ⟨⟨f1, f1p, f1b⟩, ⟨f2, f2p, f2b⟩⟩ := runEdge_frame R ch.ρ
      ((C u).withPrev (C x).color ch.rb) ((C x).withPrev (C u).color ch.rb)
      w.2 (vperm hdeg hinj hok w).2
    rw [← ho] at f1 f1p f1b f2 f2p f2b
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro v
      rw [hD]
      by_cases hvx : v = x
      · rw [hvx, upd_right, f2]; exact hS _
      by_cases hvu : v = u
      · rw [hvu, upd_left _ hne, f1]; exact hS _
      rw [upd_other _ hvu hvx]; exact hS v
    · rw [hD]
      exact bitInv_upd hinj hS hB hux o (f1.trans (hS u)) (f2.trans (hS x))
        (by rw [f1p]; rfl) (by rw [f2p]; rfl) (by rw [f1b, f2b]; rfl)
    · intro v
      rw [hD]
      by_cases hvx : v = x
      · rw [hvx, upd_right, ho]; simp [runEdge, EState.withPrev, hN x]
      by_cases hvu : v = u
      · rw [hvu, upd_left _ hne, ho]; simp [runEdge, EState.withPrev, hN u]
      rw [upd_other _ hvu hvx]; exact hN v
    · rw [hD]; exact vn_upd_of_nodes hdeg hinj hok R C w o hn1 hn2

end Interact

end SSLERegular
