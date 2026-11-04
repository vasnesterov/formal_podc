import Papers.PODC2014.WritableObjects.Lemma48Exec4

/-!
# Lemma 4.8, part 12: the steps of `Exec` (lines 34–46)
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

lemma EqOK.of_q {c c' : Cfg n T} {q : Fin n} (h : EqOK c q) (heq : (c'.loc q).eq = (c.loc q).eq)
    (htr : c'.tr = c.tr) : EqOK c' q := by
  unfold EqOK at *; rw [heq]; simp only [htr]; exact h

lemma WinOK.of_q {c c' : Cfg n T} {q : Fin n} {x : ℕ} (h : WinOK c q x) (hS : c'.S q = c.S q)
    (hm : (c'.loc q).m = (c.loc q).m) (heq : (c'.loc q).eq = (c.loc q).eq)
    (hτ : (c'.loc q).τ35 = (c.loc q).τ35) (hlen : c.tr.length ≤ c'.tr.length) :
    WinOK c' q x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨hS ▸ h1, hm ▸ h2, heq ▸ hτ ▸ h3, by rw [hτ]; omega⟩

set_option hygiene false in
/-- The step is by `q`. -/
local macro "own" p:ident : tactic => `(tactic| (
  have e : q = $p := by by_contra hne; exact hq (by simp [Function.update_of_ne hne])
  subst e))

set_option hygiene false in
/-- `q` only changes its program counter. -/
local macro "mkQPC" : tactic => `(tactic| (
  set C := c.setLoc q _ with hC
  have hQ : QPC c C.loc q := ⟨fun p hp => by simp [hC, Function.update_of_ne hp], by simp [hC],
    by simp [hC], by simp [hC], by simp [hC], by simp [h, isExecPC], by simp [hC, isExecPC]⟩
  rw [hC] at hQ ⊢
  clear_value C))

/-- The steps of `Exec` establish the invariant of the next line (proof of Lemma 4.8). -/
theorem Inv.exec_own (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q ≠ c.loc q) :
    ExecInv c' q := by
  have ho := hI.exec q
  cases hs
  case einv p o ho' h =>
    own p
    simp only [ExecInv, Function.update_self]
    refine ⟨by simp, ⟨o, by simp⟩, fun k hk hk' => ?_⟩
    simp at hk hk'; omega
  case l34 p o h =>
    own p
    simp only [ExecInv, h] at ho
    simp only [ExecInv, Function.update_self]
    refine ⟨ho.of_q (by simp) rfl, ?_⟩
    have hn := Nat.pos_of_neZero n
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))]
  case l35 p o x h =>
    own p
    simp only [ExecInv, h] at ho
    simp only [ExecInv, Function.update_self]
    refine ⟨ho.1.of_q (by simp) rfl, by simp, by simp, ?_, by simp⟩
    simpa using ho.1.1
  case l36 p o x h =>
    own p
    mkQPC
    simp only [ExecInv, h] at ho
    obtain ⟨h1, h2⟩ := ho
    simp only [ExecInv, Function.update_self]
    refine ⟨h1.of_q (by simp) rfl, h2.of_q rfl (by simp) (by simp) (by simp) le_rfl,
      by simpa using h1.1, le_rfl, fun i' hi' => ⟨by rw [← hI.ptrEq]; exact hi', Or.inl ?_⟩⟩
    obtain ⟨hP, hpp, -⟩ := hI.ptrProt i' hi'
    obtain ⟨π, hπ⟩ := Option.ne_none_iff_exists'.1 hpp
    have hπl := lt_of_get (hI.swf _ _ _ hπ).2.1
    have hg : (Option.map (fun i => (c.loc i.1).ctr) c.ptr).getD 0 = (c.loc i'.1).ctr := by
      rw [hi']; rfl
    refine ⟨(hQ.prot hP).mono (by rw [hg]), hQ.ppok ⟨π, hπ, by omega⟩,
      by rw [hQ.ctr', hg], fun w h1 h2 => ?_, ?_⟩
    · rw [hQ.ctr', ← hg] at h2; omega
    · intro h1; rw [hQ.ctr', ← hg] at h1; omega
  case l37 p o x i g ts h =>
    own p
    mkQPC
    simp only [ExecInv, h] at ho
    obtain ⟨h1, h2, h3, h4, h5⟩ := ho
    simp only [ExecInv, Function.update_self]
    refine ⟨h1.of_q (by simp) rfl, h2.of_q rfl (by simp) (by simp) (by simp) le_rfl, h3, h4,
      fun i' hi' => ?_⟩
    obtain ⟨e1, e2⟩ := h5 i' hi'
    refine ⟨e1, by simp [hi'], ?_⟩
    rcases e2 with ⟨hP, hpp, -, hw, -⟩ | ⟨j, hB⟩
    · refine Or.inl ⟨⟨by simp [hi'], hQ.slot (hP.mono (nr_le_of_A1 hw))⟩, hQ.ppok hpp⟩
    · exact Or.inr ⟨j, hQ.bcore rfl rfl hB⟩
  case l39 p o x i g ts h =>
    own p
    mkQPC
    simp only [ExecInv, h] at ho
    obtain ⟨h1, h2, h3, h4, h5⟩ := ho
    obtain ⟨e1, e2, e3⟩ := h5 i rfl
    simp only [ExecInv, Function.update_self]
    refine ⟨h1.of_q (by simp) rfl, h2.of_q rfl (by simp) (by simp) (by simp) le_rfl, h3, h4, e1,
      e2, ?_, fun h' hv hs' => ?_⟩
    · rcases e3 with ⟨hD, hpp⟩ | ⟨j, hB⟩
      · exact Or.inl ⟨hQ.dcore rfl hD, hQ.ppok hpp⟩
      · have hB' := hB
        obtain ⟨a, b, ha, hb, haj, -⟩ := hB'
        subst haj
        exact Or.inr ⟨a, ha, ha, hQ.bcore rfl rfl hB⟩
    · refine ⟨h', hv, le_rfl, fun _ => ⟨rfl, hs', fun b hb hbf => ?_⟩, fun h0 => absurd h0 (lt_irrefl _)⟩
      by_cases hW : isW1921 (c.loc i.1).pc ∧ cq (c.loc i.1).ctr = q
      · obtain ⟨e4, e5, -⟩ := hI.pairIn i.1 q hW.1 hW.2 h' hv
        obtain ⟨-, -, e6, e7, -⟩ := hI.hint' i.1 q b hb
        have e8 := (hI.chosen i.1 h'.f e5).2.2
        rw [hbf] at e6; omega
      · exact ((hI.pairOut i.1 q hW h' b hv hb).1).symm
  case l40h p o x i g ts hv h hb hb' e1 e2 e3 e4 e5 =>
    own p
    mkQPC
    simp only [ExecInv, h] at ho
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ho
    obtain ⟨a, ha, hle, hii, hiii⟩ := h8 hb e1 e3
    obtain ⟨hw, haf, has⟩ : a.w = hb'.w ∧ a.f = hb.f ∧ a.s = x := by
      rcases Nat.lt_or_ge hb.w a.w with hlt | hge
      · obtain ⟨-, k2, -⟩ := hiii hlt
        obtain ⟨k3, k4, k5⟩ := k2 hb' e2 e5.symm e4
        exact ⟨k3.symm, k4, k5⟩
      · obtain ⟨k1, k2, k3⟩ := hii (by omega)
        exact ⟨by rw [k3 hb' e2 e5.symm]; omega, k1, k2⟩
    have hxS : (x : ℤ) = Sval n (c.loc q).m := h2.1.trans (hI.sEq q)
    have hfr := hI.fresh ha e2 hw (by rw [e4, hxS]) (by simp [pre44, h])
    obtain ⟨hf1, -, -, -, hpp, -, -, hτ⟩ := hI.hint' i.1 q hb' e2
    obtain ⟨-, htr, -⟩ := hI.swf _ _ _ hpp
    have hπl := lt_of_get htr
    have hps := hI.pside_of_hint ha e2 hw has e4 hxS hfr
    simp only [ExecInv, Function.update_self]
    have htr' : c.tr[hb'.π]? = some (.ptr hb.f.1 hb.f) := by rw [e5, hf1]; exact htr
    have hpp' : (c.loc hb.f.1).pp hb.f = some hb'.π := by rw [e5, hf1]; exact hpp
    have hf1' : hb.f.1 = i.1 := by rw [e5, hf1]
    have hB : Bcore c hb.f.1 q x hb.f := by
      rw [hf1']; exact ⟨a, hb', ha, e2, haf, e5.symm, hw, has, e4, hps⟩
    refine ⟨h1.of_q (by simp) rfl, h2.of_q rfl (by simp) (by simp) (by simp) le_rfl, ?_,
      by simp; omega, ptrAt_of_get htr', hQ.ppok ⟨hb'.π, hpp', le_rfl⟩, Or.inr (hQ.bcore rfl rfl hB)⟩
    have := hτ hfr; have := h2.2.2.1; simp only [Function.update_self]; omega
  case l40d p o x i g ts hv h hn =>
    own p
    mkQPC
    simp only [ExecInv, h] at ho
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := ho
    simp only [ExecInv, Function.update_self]
    rcases h7 with ⟨hD, hpp⟩ | ⟨h', hv', hH, hB⟩
    · exact ⟨h1.of_q (by simp) rfl, h2.of_q rfl (by simp) (by simp) (by simp) le_rfl,
        by simpa using h3, h4, h5, hQ.ppok hpp, Or.inl (hQ.dcore rfl hD)⟩
    · exfalso; apply hn
      obtain ⟨a, b, ha, hb, haf, hbf, -, has, hbs, -⟩ := hB
      rw [hH] at ha
      obtain rfl := Option.some.inj ha
      exact ⟨_, b, hv', hb, has, hbs, haf.trans hbf.symm⟩
  case opinv p o x i ts h =>
    own p
    mkQPC
    simp only [ExecInv, h] at ho
    obtain ⟨-, h2, h3, h4, h5, h6, h7⟩ := ho
    simp only [ExecInv, Function.update_self]
    refine ⟨h2.of_q rfl (by simp) (by simp) (by simp) (by simp), ⟨by simpa using h3, by simp; omega,
      by rw [ptrAt_concat_le h4]; exact h5, hQ.ppok h6, ?_⟩, h4⟩
    rcases h7 with hD | hB
    · exact Or.inl (hQ.dcore rfl hD)
    · exact Or.inr (hQ.bcore rfl rfl hB)
  case opret p x i ts t r h =>
    own p
    simp only [ExecInv, h] at ho
    simp only [ExecInv, Function.update_self]
    exact ho.1.of_q rfl (by simp) (by simp) (by simp) (by simp)
  case l44 p x r h =>
    own p
    simp only [ExecInv, h] at ho
    simp only [ExecInv, Function.update_self]
    exact ho.of_q rfl (by simp) (by simp) (by simp) le_rfl
  all_goals
    unfold ExecInv
    simp only [Function.update_apply]
    split_ifs with hp
    · simp
    · exact absurd (Function.update_of_ne hp _ _) hq

end Podc.WritableObjects.WF
