import Papers.PODC2026.RandomizedWaitFreeLocks.Alg1Inv

/-!
# Algorithm 1: the frame lemma

`Inv.frame`: if only the local state of `p` changes, keeping its call
(`dsc`, `fT`, `b`, membership in `act`), the invariant is preserved as soon as the new local
state satisfies the instances of the invariant that mention `p`.
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

variable {P D : Type*} [DecidableEq P] [DecidableEq D] (own : D → P)

omit [DecidableEq D] in
@[simp] lemma upd_loc (c : Cfg P D) (p : P) (l : Loc D) (x : P) :
    (c.upd p l).loc x = if x = p then l else c.loc x := by
  simp [Cfg.upd, Function.update_apply]

section
variable (c : Cfg P D) (p : P) (l : Loc D)
omit [DecidableEq D]
@[simp] lemma upd_L : (c.upd p l).L = c.L := rfl
@[simp] lemma upd_R : (c.upd p l).R = c.R := rfl
@[simp] lemma upd_C : (c.upd p l).C = c.C := rfl
@[simp] lemma upd_done : (c.upd p l).done = c.done := rfl
@[simp] lemma upd_T : (c.upd p l).T = c.T := rfl
@[simp] lemma upd_lastW : (c.upd p l).lastW = c.lastW := rfl
@[simp] lemma upd_lastChg : (c.upd p l).lastChg = c.lastChg := rfl
@[simp] lemma upd_eT : (c.upd p l).eT = c.eT := rfl
@[simp] lemma upd_started : (c.upd p l).started = c.started := rfl
@[simp] lemma upd_act : (c.upd p l).act = c.act := rfl
@[simp] lemma upd_retT : (c.upd p l).retT = c.retT := rfl
@[simp] lemma upd_failed : (c.upd p l).failed = c.failed := rfl
@[simp] lemma tick_L : c.tick.L = c.L := rfl
@[simp] lemma tick_R : c.tick.R = c.R := rfl
@[simp] lemma tick_C : c.tick.C = c.C := rfl
@[simp] lemma tick_done : c.tick.done = c.done := rfl
@[simp] lemma tick_T : c.tick.T = c.T + 1 := rfl
@[simp] lemma tick_lastW : c.tick.lastW = c.lastW := rfl
@[simp] lemma tick_lastChg : c.tick.lastChg = c.lastChg := rfl
@[simp] lemma tick_eT : c.tick.eT = c.eT := rfl
@[simp] lemma tick_started : c.tick.started = c.started := rfl
@[simp] lemma tick_act : c.tick.act = c.act := rfl
@[simp] lemma tick_retT : c.tick.retT = c.retT := rfl
@[simp] lemma tick_failed : c.tick.failed = c.failed := rfl
@[simp] lemma tick_loc : c.tick.loc = c.loc := rfl
@[simp] lemma eTo_tick (x : Option D) : c.tick.eTo x = c.eTo x := by cases x <;> rfl
@[simp] lemma eTo_upd (x : Option D) : (c.upd p l).eTo x = c.eTo x := by cases x <;> rfl
@[simp] lemma everL_tick (x : Option D) : c.tick.everL x ↔ c.everL x := by cases x <;> rfl
@[simp] lemma everL_upd (x : Option D) : (c.upd p l).everL x ↔ c.everL x := by cases x <;> rfl
end

lemma filter_congr_fT {c : Cfg P D} {p : P} {l' : Loc D} (hfT : l'.fT = (c.loc p).fT) (t : ℕ) :
    c.act.filter (fun z => ((c.upd p l').loc z).fT < t) =
      c.act.filter (fun z => (c.loc z).fT < t) := by
  apply Finset.filter_congr
  intro z _
  by_cases hz : z = p
  · subst hz; simp [hfT]
  · simp [hz]

/-- **Frame lemma** for steps changing only `p`'s local state. -/
lemma Inv.frame {c : Cfg P D} {p : P} (hI : Inv own c) (l' : Loc D)
    (hdsc : l'.dsc = (c.loc p).dsc) (hfT : l'.fT = (c.loc p).fT) (hb : l'.b = (c.loc p).b)
    (hidle : l'.pc = .idle ↔ (c.loc p).pc = .idle) (hact : l'.pc.inAct = (c.loc p).pc.inAct)
    (s_l6 : (l'.pc.hap || l'.pc.post) = true → l'.l6 ≤ c.T)
    (s_a : l'.pc.h24 = true → l'.l6 < l'.a ∧ l'.a ≤ c.T)
    (s_rb : ∀ i, l'.pc = .cas i → l'.a < l'.rb ∧ l'.rb ≤ c.T)
    (s_e1 : ∀ i ω, (l'.pc = .exS i ∨ l'.pc = .exE i) → l'.w = some ω →
      c.L = some ω ∨ c.done ω = true)
    (s_e2 : ∀ i ω, (l'.pc = .rdR i ∨ l'.pc = .cas i) → l'.w = some ω → c.done ω = true)
    (s_e3 : ∀ ω, (l'.pc = .exS8 ∨ l'.pc = .exE8) → l'.dsc = some ω →
      c.L = some ω ∨ c.done ω = true)
    (s_f3 : l'.pc.h24 = true → c.eTo l'.w < l'.a ∧ c.everL l'.w)
    (s_f3c : l'.pc.h24 = true → c.lastChg < l'.a → c.L = l'.w)
    (s_f4 : ∀ i, l'.pc = .cas i → c.L = l'.w → l'.d ≠ l'.w →
      ∃ δ, l'.d = some δ ∧ c.eT δ = 0 ∧
        (if own δ = p then l' else c.loc (own δ)).dsc = some δ ∧
        (if own δ = p then l' else c.loc (own δ)).pc.hap = true)
    (s_f4o : ∀ x i δ, x ≠ p → (c.loc x).pc = .cas i → c.L = (c.loc x).w →
      (c.loc x).d = some δ → (c.loc x).d ≠ (c.loc x).w → c.eT δ = 0 → own δ = p →
      l'.pc.hap = true)
    (s_f6 : ∀ i, l'.pc = .cas i → c.L = l'.w → l'.d ≠ l'.w → c.R ≠ l'.w)
    (s_f7 : ∀ δ, c.R = some δ → c.eT δ = 0 → own δ = p → l'.dsc = some δ →
      l'.pc.hap = true ∧ l'.l6 = c.lastW)
    (s_o1 : ∀ δ, c.eT δ ≠ 0 → own δ = p → l'.dsc = some δ → c.retT δ = false →
      (l'.pc.hap || l'.pc.post) = true)
    (s_o2 : ∀ δ, c.eT δ ≠ 0 → own δ = p → l'.dsc = some δ → (l'.pc = .fad ∨ l'.pc = .ret) →
      c.done δ = true)
    (s_g1 : ∀ δ, c.R = some δ → c.eT δ = 0 → (l'.pc.hap || l'.pc.post) = true →
      c.lastW ≤ l'.l6 → l'.pc.hap = true)
    (s_g2 : ∀ δ, c.R = some δ → c.eT δ = 0 → l'.pc.hap2 = true → c.lastW ≤ l'.l6 →
      c.lastW < c.lastChg)
    (s_g3 : ∀ δ, c.R = some δ → c.eT δ = 0 → l'.pc.h24₂ = true → c.lastW ≤ l'.l6 → c.L = l'.w)
    (s_ib : ∀ i, l'.pc = .cas i → c.lastW < l'.rb → l'.d = c.R)
    (s_ij : ∀ i δ, l'.pc = .cas i → c.L = l'.w → l'.d = some δ → l'.d ≠ l'.w →
      (if own δ = p then l' else c.loc (own δ)).pc.isCas = true →
      c.L = (if own δ = p then l' else c.loc (own δ)).w →
      (if own δ = p then l' else c.loc (own δ)).d ≠ (if own δ = p then l' else c.loc (own δ)).w)
    (s_ijo : ∀ x i δ, x ≠ p → (c.loc x).pc = .cas i → c.L = (c.loc x).w →
      (c.loc x).d = some δ → (c.loc x).d ≠ (c.loc x).w → own δ = p →
      l'.pc.isCas = true → c.L = l'.w → l'.d ≠ l'.w)
    (s_ik : ∀ i δ, l'.pc = .cas i → c.L = l'.w → l'.d = some δ → l'.d ≠ l'.w →
      (if own δ = p then l' else c.loc (own δ)).pc.h24₂ = true →
      c.L = (if own δ = p then l' else c.loc (own δ)).w)
    (s_iko : ∀ x i δ, x ≠ p → (c.loc x).pc = .cas i → c.L = (c.loc x).w →
      (c.loc x).d = some δ → (c.loc x).d ≠ (c.loc x).w → own δ = p →
      l'.pc.h24₂ = true → c.L = l'.w) :
    Inv own (c.upd p l') := by
  have L1 : ∀ x, x ≠ p → ((c.upd p l').loc x) = c.loc x := fun x hx => by simp [hx]
  have L2 : (c.upd p l').loc p = l' := by simp
  have hpos : ∀ δ, own δ = p → ((c.upd p l').loc (own δ)) = l' := fun δ h => by simp [h]
  have hif : ∀ δ, ((c.upd p l').loc (own δ)) =
      (if own δ = p then l' else c.loc (own δ)) := fun δ => by simp
  constructor
  · intro x; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hidle, hdsc]; exact hI.idle_iff x
    · rw [L1 x hx]; exact hI.idle_iff x
  · intro x δ; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hdsc]; exact hI.own_dsc x δ
    · rw [L1 x hx]; exact hI.own_dsc x δ
  · intro x; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hact]; exact hI.act_iff x
    · rw [L1 x hx]; exact hI.act_iff x
  · exact hI.C_eq
  · simpa using hI.lastW_le
  · simpa using hI.lastChg_le
  · intro ω; simpa using hI.eT_le ω
  · intro x; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_l6
    · rw [L1 x hx]; intro h; have := hI.l6_le x h; simp; omega
  · intro x; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_a
    · rw [L1 x hx]; intro h; have := hI.a_bd x h; simp; omega
  · intro x i; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_rb i
    · rw [L1 x hx]; intro h; have := hI.rb_bd x i h; simp; omega
  · intro x hx; simp only [upd_act] at hx ⊢
    rcases eq_or_ne x p with rfl | hxp
    · rw [L2, hfT]; have := hI.fT_bd x hx; simp; omega
    · rw [L1 x hxp]; have := hI.fT_bd x hx; simp; omega
  · intro x i ω; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_e1 i ω
    · rw [L1 x hx]; exact hI.e1 x i ω
  · intro x i ω; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_e2 i ω
    · rw [L1 x hx]; exact hI.e2 x i ω
  · intro x ω; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_e3 ω
    · rw [L1 x hx]; exact hI.e3 x ω
  · exact hI.e4
  · exact hI.f1
  · exact hI.f1'
  · exact hI.f2
  · intro x; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; simpa using s_f3
    · rw [L1 x hx]; simpa using hI.f3 x
  · intro x; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_f3c
    · rw [L1 x hx]; exact hI.f3c x
  · intro x i; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; intro h1 h2 h3
      obtain ⟨δ, h4, h5, h6, h7⟩ := s_f4 i h1 h2 h3
      exact ⟨δ, h4, h5, by rw [hif]; exact h6, by rw [hif]; exact h7⟩
    · rw [L1 x hx]; intro h1 h2 h3
      obtain ⟨δ, h4, h5, h6, h7⟩ := hI.f4 x i h1 h2 h3
      refine ⟨δ, h4, h5, ?_, ?_⟩
      · rw [hif]; split_ifs with ho
        · rw [hdsc, ← ho]; exact h6
        · exact h6
      · rw [hif]; split_ifs with ho
        · exact s_f4o x i δ hx h1 h2 h4 h3 h5 ho
        · exact h7
  · exact hI.f5
  · exact hI.f5'
  · intro x i; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_f6 i
    · rw [L1 x hx]; exact hI.f6 x i
  · intro δ h1 h2
    obtain ⟨h3, h4, h5⟩ := hI.f7 δ h1 h2
    rw [hif]; split_ifs with ho
    · have hd : l'.dsc = some δ := by rw [hdsc, ← ho]; exact h3
      exact ⟨hd, s_f7 δ h1 h2 ho hd⟩
    · exact ⟨h3, h4, h5⟩
  · intro δ h1
    rcases hI.o1 δ h1 with h | ⟨h3, h4⟩
    · exact Or.inl h
    · right; rw [hif]; split_ifs with ho
      · have hd : l'.dsc = some δ := by rw [hdsc, ← ho]; exact h3
        refine ⟨hd, s_o1 δ h1 ho hd ?_⟩
        exact hI.o3 _ δ h3
      · exact ⟨h3, h4⟩
  · intro δ h1; rw [hif]; split_ifs with ho
    · exact s_o2 δ h1 ho
    · exact hI.o2 δ h1
  · intro x δ; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hdsc]; exact hI.o3 x δ
    · rw [L1 x hx]; exact hI.o3 x δ
  · exact hI.o4
  · intro x δ; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_g1 δ
    · rw [L1 x hx]; exact hI.g1 x δ
  · intro x δ; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_g2 δ
    · rw [L1 x hx]; exact hI.g2 x δ
  · intro x δ; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_g3 δ
    · rw [L1 x hx]; exact hI.g3 x δ
  · intro x i; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_ib i
    · rw [L1 x hx]; exact hI.ib x i
  · intro x i δ; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hif]; exact s_ij i δ
    · rw [L1 x hx, hif]; intro h1 h2 h3 h4
      split_ifs with ho
      · exact s_ijo x i δ hx h1 h2 h3 h4 ho
      · exact hI.ij x i δ h1 h2 h3 h4
  · intro x i δ; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hif]; exact s_ik i δ
    · rw [L1 x hx, hif]; intro h1 h2 h3 h4
      split_ifs with ho
      · exact s_iko x i δ hx h1 h2 h3 h4 ho
      · exact hI.ik x i δ h1 h2 h3 h4
  · intro x hx
    simp only [upd_act, filter_congr_fT hfT]
    rcases eq_or_ne x p with rfl | hxp
    · rw [L2, hb, hfT]; exact hI.k1 x hx
    · rw [L1 x hxp]; exact hI.k1 x hx
  · intro x hx z hz
    simp only [upd_act] at hx hz
    have e : ∀ y, ((c.upd p l').loc y).fT = (c.loc y).fT := by
      intro y; rcases eq_or_ne y p with rfl | hy
      · rw [L2, hfT]
      · rw [L1 y hy]
    rw [e, e]; exact hI.k2 x hx z hz

/-- **General frame lemma**: `p`'s local state, `act`, `C`, `retT`, `failed` may change. -/
lemma Inv.frameG {c : Cfg P D} {p : P} (hI : Inv own c) (l' : Loc D)
    (A : Finset P) (Cn : ℕ) (RT : D → Bool) (F : P → ℕ → Bool)
    (g_idle : l'.pc = .idle ↔ l'.dsc = none) (g_own : ∀ δ, l'.dsc = some δ → own δ = p)
    (g_actp : p ∈ A ↔ l'.pc.inAct = true) (g_acto : ∀ x, x ≠ p → (x ∈ A ↔ x ∈ c.act))
    (g_C : Cn = A.card) (g_fT : p ∈ A → 0 < l'.fT ∧ l'.fT ≤ c.T)
    (g_k1 : ∀ x ∈ A, 1 + (A.filter (fun z => ((c.upd p l').loc z).fT <
      ((c.upd p l').loc x).fT)).card ≤ ((c.upd p l').loc x).b)
    (g_k2 : ∀ x ∈ A, ∀ z ∈ A, ((c.upd p l').loc x).fT = ((c.upd p l').loc z).fT → x = z)
    (g_RT : ∀ δ, own δ ≠ p → RT δ = c.retT δ) (g_RTp : ∀ δ, l'.dsc = some δ → RT δ = false)
    (g_RTd : ∀ δ, RT δ = true → c.done δ = true)
    (s_l6 : (l'.pc.hap || l'.pc.post) = true → l'.l6 ≤ c.T)
    (s_a : l'.pc.h24 = true → l'.l6 < l'.a ∧ l'.a ≤ c.T)
    (s_rb : ∀ i, l'.pc = .cas i → l'.a < l'.rb ∧ l'.rb ≤ c.T)
    (s_e1 : ∀ i ω, (l'.pc = .exS i ∨ l'.pc = .exE i) → l'.w = some ω →
      c.L = some ω ∨ c.done ω = true)
    (s_e2 : ∀ i ω, (l'.pc = .rdR i ∨ l'.pc = .cas i) → l'.w = some ω → c.done ω = true)
    (s_e3 : ∀ ω, (l'.pc = .exS8 ∨ l'.pc = .exE8) → l'.dsc = some ω →
      c.L = some ω ∨ c.done ω = true)
    (s_f3 : l'.pc.h24 = true → c.eTo l'.w < l'.a ∧ c.everL l'.w)
    (s_f3c : l'.pc.h24 = true → c.lastChg < l'.a → c.L = l'.w)
    (s_f4 : ∀ i, l'.pc = .cas i → c.L = l'.w → l'.d ≠ l'.w →
      ∃ δ, l'.d = some δ ∧ c.eT δ = 0 ∧
        (if own δ = p then l' else c.loc (own δ)).dsc = some δ ∧
        (if own δ = p then l' else c.loc (own δ)).pc.hap = true)
    (s_f4o : ∀ x i δ, x ≠ p → (c.loc x).pc = .cas i → c.L = (c.loc x).w →
      (c.loc x).d = some δ → (c.loc x).d ≠ (c.loc x).w → c.eT δ = 0 → own δ = p →
      l'.dsc = some δ ∧ l'.pc.hap = true)
    (s_f6 : ∀ i, l'.pc = .cas i → c.L = l'.w → l'.d ≠ l'.w → c.R ≠ l'.w)
    (s_f7 : ∀ δ, c.R = some δ → c.eT δ = 0 → own δ = p →
      l'.dsc = some δ ∧ l'.pc.hap = true ∧ l'.l6 = c.lastW)
    (s_o1 : ∀ δ, c.eT δ ≠ 0 → own δ = p → RT δ = true ∨
      (l'.dsc = some δ ∧ (l'.pc.hap || l'.pc.post) = true))
    (s_o2 : ∀ δ, c.eT δ ≠ 0 → own δ = p → l'.dsc = some δ → (l'.pc = .fad ∨ l'.pc = .ret) →
      c.done δ = true)
    (s_g1 : ∀ δ, c.R = some δ → c.eT δ = 0 → (l'.pc.hap || l'.pc.post) = true →
      c.lastW ≤ l'.l6 → l'.pc.hap = true)
    (s_g2 : ∀ δ, c.R = some δ → c.eT δ = 0 → l'.pc.hap2 = true → c.lastW ≤ l'.l6 →
      c.lastW < c.lastChg)
    (s_g3 : ∀ δ, c.R = some δ → c.eT δ = 0 → l'.pc.h24₂ = true → c.lastW ≤ l'.l6 → c.L = l'.w)
    (s_ib : ∀ i, l'.pc = .cas i → c.lastW < l'.rb → l'.d = c.R)
    (s_ij : ∀ i δ, l'.pc = .cas i → c.L = l'.w → l'.d = some δ → l'.d ≠ l'.w →
      (if own δ = p then l' else c.loc (own δ)).pc.isCas = true →
      c.L = (if own δ = p then l' else c.loc (own δ)).w →
      (if own δ = p then l' else c.loc (own δ)).d ≠ (if own δ = p then l' else c.loc (own δ)).w)
    (s_ijo : ∀ x i δ, x ≠ p → (c.loc x).pc = .cas i → c.L = (c.loc x).w →
      (c.loc x).d = some δ → (c.loc x).d ≠ (c.loc x).w → own δ = p →
      l'.pc.isCas = true → c.L = l'.w → l'.d ≠ l'.w)
    (s_ik : ∀ i δ, l'.pc = .cas i → c.L = l'.w → l'.d = some δ → l'.d ≠ l'.w →
      (if own δ = p then l' else c.loc (own δ)).pc.h24₂ = true →
      c.L = (if own δ = p then l' else c.loc (own δ)).w)
    (s_iko : ∀ x i δ, x ≠ p → (c.loc x).pc = .cas i → c.L = (c.loc x).w →
      (c.loc x).d = some δ → (c.loc x).d ≠ (c.loc x).w → own δ = p →
      l'.pc.h24₂ = true → c.L = l'.w) :
    Inv own { (c.upd p l') with act := A, C := Cn, retT := RT, failed := F } := by
  have L1 : ∀ x, x ≠ p → ((c.upd p l').loc x) = c.loc x := fun x hx => by simp [hx]
  have L2 : (c.upd p l').loc p = l' := by simp
  have hif : ∀ δ, ((c.upd p l').loc (own δ)) =
      (if own δ = p then l' else c.loc (own δ)) := fun δ => by simp
  constructor
  · intro x; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact g_idle
    · rw [L1 x hx]; exact hI.idle_iff x
  · intro x δ; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact g_own δ
    · rw [L1 x hx]; exact hI.own_dsc x δ
  · intro x; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact g_actp
    · rw [L1 x hx, g_acto x hx]; exact hI.act_iff x
  · exact g_C
  · simpa using hI.lastW_le
  · simpa using hI.lastChg_le
  · intro ω; simpa using hI.eT_le ω
  · intro x; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_l6
    · rw [L1 x hx]; intro h; simpa using hI.l6_le x h
  · intro x; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_a
    · rw [L1 x hx]; intro h; simpa using hI.a_bd x h
  · intro x i; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_rb i
    · rw [L1 x hx]; intro h; simpa using hI.rb_bd x i h
  · intro x hx; simp only at hx ⊢
    rcases eq_or_ne x p with rfl | hxp
    · rw [L2]; simpa using g_fT hx
    · rw [L1 x hxp]; simpa using hI.fT_bd x ((g_acto x hxp).1 hx)
  · intro x i ω; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_e1 i ω
    · rw [L1 x hx]; exact hI.e1 x i ω
  · intro x i ω; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_e2 i ω
    · rw [L1 x hx]; exact hI.e2 x i ω
  · intro x ω; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_e3 ω
    · rw [L1 x hx]; exact hI.e3 x ω
  · exact hI.e4
  · exact hI.f1
  · exact hI.f1'
  · exact hI.f2
  · intro x; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; rcases hw : l'.w with _ | ω <;> simpa [hw, Cfg.eTo, Cfg.everL] using s_f3
    · rw [L1 x hx]; rcases hw : (c.loc x).w with _ | ω <;>
        simpa [hw, Cfg.eTo, Cfg.everL] using hI.f3 x
  · intro x; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_f3c
    · rw [L1 x hx]; exact hI.f3c x
  · intro x i; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; intro h1 h2 h3
      obtain ⟨δ, h4, h5, h6, h7⟩ := s_f4 i h1 h2 h3
      exact ⟨δ, h4, h5, by rw [hif]; exact h6, by rw [hif]; exact h7⟩
    · rw [L1 x hx]; intro h1 h2 h3
      obtain ⟨δ, h4, h5, h6, h7⟩ := hI.f4 x i h1 h2 h3
      refine ⟨δ, h4, h5, ?_, ?_⟩
      · rw [hif]; split_ifs with ho
        · exact (s_f4o x i δ hx h1 h2 h4 h3 h5 ho).1
        · exact h6
      · rw [hif]; split_ifs with ho
        · exact (s_f4o x i δ hx h1 h2 h4 h3 h5 ho).2
        · exact h7
  · exact hI.f5
  · exact hI.f5'
  · intro x i; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_f6 i
    · rw [L1 x hx]; exact hI.f6 x i
  · intro δ h1 h2; simp only
    rw [hif]; split_ifs with ho
    · exact s_f7 δ h1 h2 ho
    · exact hI.f7 δ h1 h2
  · intro δ h1; simp only
    rw [hif]; split_ifs with ho
    · exact s_o1 δ h1 ho
    · rw [g_RT δ ho]; exact hI.o1 δ h1
  · intro δ h1; simp only; rw [hif]; split_ifs with ho
    · exact s_o2 δ h1 ho
    · exact hI.o2 δ h1
  · intro x δ; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact g_RTp δ
    · rw [L1 x hx]; intro h
      rw [g_RT δ (by rw [hI.own_dsc x δ h]; exact hx)]; exact hI.o3 x δ h
  · exact g_RTd
  · intro x δ; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_g1 δ
    · rw [L1 x hx]; exact hI.g1 x δ
  · intro x δ; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_g2 δ
    · rw [L1 x hx]; exact hI.g2 x δ
  · intro x δ; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_g3 δ
    · rw [L1 x hx]; exact hI.g3 x δ
  · intro x i; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2]; exact s_ib i
    · rw [L1 x hx]; exact hI.ib x i
  · intro x i δ; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hif]; exact s_ij i δ
    · rw [L1 x hx, hif]; intro h1 h2 h3 h4
      split_ifs with ho
      · exact s_ijo x i δ hx h1 h2 h3 h4 ho
      · exact hI.ij x i δ h1 h2 h3 h4
  · intro x i δ; simp only; rcases eq_or_ne x p with rfl | hx
    · rw [L2, hif]; exact s_ik i δ
    · rw [L1 x hx, hif]; intro h1 h2 h3 h4
      split_ifs with ho
      · exact s_iko x i δ hx h1 h2 h3 h4 ho
      · exact hI.ik x i δ h1 h2 h3 h4
  · exact g_k1
  · exact g_k2

/-- The clock may advance. -/
lemma Inv.tick {c : Cfg P D} (hI : Inv own c) : Inv own c.tick := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩ := hI
  refine ⟨a1, a2, a3, a4, by simp; omega, by simp; omega, fun ω => by simp; have := a7 ω; omega,
    fun x h => by simp; have := a8 x h; omega, fun x h => by simp; have := a9 x h; omega,
    fun x i h => by simp; have := a10 x i h; omega, fun x h => by simp; have := a11 x h; omega,
    a12, a13, a14, a15, a16, a17, a18, ?_, a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30,
    a31, a32, a33, a34, a35, a36, a37⟩
  intro x; simpa using a19 x

/-- Setting the `isDone` register of a descriptor. -/
lemma Inv.setDone {c : Cfg P D} (hI : Inv own c) (ω : D) :
    Inv own { c with done := Function.update c.done ω true } := by
  have hd : ∀ δ, c.done δ = true → Function.update c.done ω true δ = true := by
    intro δ h; by_cases e : δ = ω
    · subst e; simp
    · simp [e, h]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩ := hI
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, fun x i ω' h1 h2 => (a12 x i ω' h1 h2).imp_right (hd _),
    fun x i ω' h1 h2 => hd _ (a13 x i ω' h1 h2), fun x ω' h1 h2 => (a14 x ω' h1 h2).imp_right (hd _),
    ?_, a16, a17, fun ω' h1 h2 => hd _ (a18 ω' h1 h2), a19,
    a20, a21, a22, a23, a24, a25, a26, fun δ h1 h2 h3 => hd _ (a27 δ h1 h2 h3), a28,
    fun δ h => hd _ (a29 δ h), a30,
    a31, a32, a33, a34, a35, a36, a37⟩
  intro ω' h1 h2
  by_cases e : ω' = ω
  · subst e; simp at h2
  · simp [e] at h2; exact a15 ω' h1 h2

/-- Starting the execution of a thunk whose descriptor is in `L` or done. -/
lemma Inv.setStarted {c : Cfg P D} (hI : Inv own c) (ω : D) (h : c.L = some ω ∨ c.done ω = true) :
    Inv own { c with started := Function.update c.started ω true } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30, a31, a32, a33, a34, a35, a36, a37⟩ := hI
  refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, ?_, a16, a17, a18, a19,
    a20, a21, a22, a23, a24, a25, a26, a27, a28, a29, a30,
    a31, a32, a33, a34, a35, a36, a37⟩
  intro ω' h1 h2
  by_cases e : ω' = ω
  · subst e; rcases h with h | h
    · exact h
    · simp [h] at h2
  · simp [e] at h1; exact a15 ω' h1 h2

end Podc.RandomizedWaitFreeLocks.Alg1
