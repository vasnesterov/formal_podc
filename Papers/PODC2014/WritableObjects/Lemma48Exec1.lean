import Papers.PODC2014.WritableObjects.Lemma48Pres2

/-!
# Lemma 4.8, part 8: the state of a pending `Exec` is not disturbed by other processes
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

/-- The `n` consecutive numbers `g+1, …, g+n` contain one `≡ q (mod n)`. -/
lemma le_of_no_mod {g C q : ℕ} (hq : q < n) (h : ∀ w, g < w → w < C → w % n ≠ q) :
    C ≤ g + n := by
  by_contra hC
  have hn := Nat.pos_of_neZero n
  obtain ⟨h1, h2⟩ := dist_spec (n := n) (g + 1) q hq
  exact h _ (by omega) (by omega) h2

/-- Some `e ∈ (a, a + n]` has `(e - 1) mod n = p`. -/
lemma exists_mod_window (a p : ℕ) (hp : p < n) :
    ∃ e, a < e ∧ e ≤ a + n ∧ (e - 1) % n = p := by
  obtain ⟨h1, h2⟩ := dist_spec (n := n) a p hp
  exact ⟨a + (p + n - a % n) % n + 1, by omega, by omega, by simpa using h2⟩

lemma ptrAt_of_get {tr : List (Ev (Fin n) (Idx n) T)} {π : ℕ} {p : Fin n} {i : Idx n}
    (h : tr[π]? = some (.ptr p i)) : ptrAt tr (π + 1) = some i := by
  have hl := lt_of_get h
  unfold ptrAt
  rw [List.take_add_one, List.filterMap_append, h]
  simp [Ev.ptrVal]

/-- GI-Fresh (Claim 4.25(b)): if both hint entries come from the same `Write` and the second
carries the current value of `S_q`, then line 19 of that `Write` read the current epoch. -/
lemma Inv.fresh (hI : Inv W c) {p q : Fin n} {a : HE n} {b : HE' n} (ha : c.hH p q = some a)
    (hb : c.hH' p q = some b) (hw : a.w = b.w) (hs : b.s = Sval n (c.loc q).m)
    (hpre : pre44 (c.loc q).pc = true) : b.m19 = (c.loc q).m := by
  have hn := Nat.pos_of_neZero n
  have hpo : ¬ (isW1921 (c.loc p).pc ∧ cq (c.loc p).ctr = q) := by
    rintro ⟨h1, h2⟩
    have e1 := (hI.pairIn p q h1 h2 a ha).1
    have e2 := (hI.hint' p q b hb).2.2.2.1
    omega
  obtain ⟨-, -, hm⟩ := hI.pairOut p q hpo a b ha hb
  obtain ⟨-, -, -, -, -, hb6, hb7, -⟩ := hI.hint' p q b hb
  have hwin : (c.loc q).m ≤ a.m18 + n := by
    by_contra hc
    obtain ⟨e, he1, he2, he3⟩ := exists_mod_window a.m18 p.val p.isLt
    exact hI.reset p q a ha e he1 (by simp [done44, hpre]; omega) he3
  rw [hb6] at hs
  exact Sval_inj hb7 (by omega) hs

/-- Protection of a slot is kept by any step, provided the slot holds the index. -/
lemma Inv.slotProt_step (hI : Inv W c) (hs : Step W c c') {p : Fin n} {i : Idx n} {o : Fin 4}
    {q : Fin n} (ho : o ≠ 0) (hip : i.1 = p) (h : (c.loc p).SlotProt i o q)
    (r1 : o = 1 → c.annc q = some i) (r2 : o = 2 → (c.hH p q).map HE.f = some i)
    (r3 : o = 3 → (c.hH' p q).map HE'.f = some i) : (c'.loc p).SlotProt i o q := by
  cases hs
  case rec27 p0 v f hpc hf =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      exact Loc.r27_slot hpc (hI.qok _) ho h hip (fun h1 h2 => h2 ▸ r1 h1)
    · simpa [Function.update_of_ne hp] using h
  case rec29 p0 v f hpc =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      exact Loc.r29_slot hpc (hI.qok _) ho h hip (fun h1 h2 => h2 ▸ r2 h1)
    · simpa [Function.update_of_ne hp] using h
  case rec31 p0 v f hpc =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      exact Loc.r31_slot hpc (hI.qok _) ho h hip (fun h1 h2 => h2 ▸ r3 h1)
    · simpa [Function.update_of_ne hp] using h
  case l21 p0 v f s' m19 τ19 π hpc =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      exact h.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, hpc]; omega)
    · simpa [Function.update_of_ne hp] using h
  case l23 p0 v f hpc =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      exact h.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, hpc]; omega)
    · simpa [Function.update_of_ne hp] using h
  all_goals
    simp only [Function.update_apply]; split_ifs with hp
    · subst hp; exact h.congr rfl (Loc.U_congr rfl (by simp [stage, *]))
    · exact h

/-- `pp` of a protected index does not change. -/
lemma Inv.pp_step (hI : Inv W c) (hs : Step W c c') {p : Fin n} {i : Idx n} {π : ℕ}
    (h : (c.loc p).pp i = some π) (hf : i ∉ (c.loc p).qs.free) : (c'.loc p).pp i = some π := by
  cases hs
  case rec27 p0 v f hpc hff =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      have : i ≠ f := fun e => hf (e ▸ hff)
      simpa [Function.update_of_ne this] using h
    · simpa [Function.update_of_ne hp] using h
  case l20 p0 v f s' m19 τ19 hpc =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      have : i ≠ f := by
        rintro rfl
        rw [hI.prePtr p i (by simp [hpc, curF]) (by simp [hpc, isPrePtr])] at h; simp at h
      simpa [Function.update_of_ne this] using h
    · simpa [Function.update_of_ne hp] using h
  case l23 p0 v f hpc =>
    by_cases hp : p = p0
    · subst hp; simp only [Function.update_self]
      have : i ≠ f := by
        rintro rfl
        rw [hI.prePtr p i (by simp [hpc, curF]) (by simp [hpc, isPrePtr])] at h; simp at h
      simpa [Function.update_of_ne this] using h
    · simpa [Function.update_of_ne hp] using h
  all_goals
    simp only [Function.update_apply]; split_ifs with hp
    · subst hp; simpa using h
    · exact h

lemma Inv.ppok_step (hI : Inv W c) (hs : Step W c c') {i : Idx n} {ts : ℕ} (h : PPok c i ts)
    (hf : i ∉ (c.loc i.1).qs.free) : PPok c' i ts := by
  obtain ⟨π, h1, h2⟩ := h
  exact ⟨π, hI.pp_step hs h1 hf, h2⟩

set_option hygiene false in
/-- In a step of `p` that does not change `q`'s local state, `p ≠ q`. -/
local macro "nq" p:ident : tactic => `(tactic| (
  have hne : $p ≠ q := by
    rintro rfl
    have h' := congrArg Loc.pc hq
    simp only [Function.update_self] at h'
    rw [h] at h'; simp at h'))

lemma Inv.len_step (hs : Step W c c') : c.tr.length ≤ c'.tr.length := by
  cases hs <;> simp

/-- The events appended by a step of another process are not `q`'s. -/
lemma Inv.newev_ne (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q) :
    ∀ k (hk : k < c'.tr.length), c.tr.length ≤ k → (c'.tr[k]).proc ≠ q := by
  intro k hk hk'
  cases hs
  case winv p v h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case swinv p v f h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case swret p v f r h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case l20 p v f s' m19 τ19 h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case l23 p v f h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case wret p v h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case einv p o ho h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case opinv p o x i ts h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case opret p x i ts t r h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  case eret p r h =>
    nq p
    have : k = c.tr.length := by simp at hk; omega
    subst this; simp [Ev.proc, hne]
  all_goals simp at hk; omega

lemma Inv.eqOK_frame (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q)
    (h : EqOK c q) : EqOK c' q := by
  obtain ⟨h1, ⟨o, h2⟩, h3⟩ := h
  have hlen := Inv.len_step hs
  obtain ⟨t, ht⟩ : ∃ t, c'.tr = c.tr ++ t := by cases hs <;> simp
  rw [EqOK, hq]
  refine ⟨by omega, ⟨o, by rw [ht, List.getElem?_append_left (lt_of_get h2)]; exact h2⟩, ?_⟩
  intro k hk hk'
  rcases Nat.lt_or_ge k c.tr.length with hlt | hge
  · have : c'.tr[k] = c.tr[k] := by simp only [ht]; exact List.getElem_append_left hlt
    rw [this]; exact h3 k hlt hk'
  · exact Inv.newev_ne hs hq k hk hge

lemma Inv.winOK_frame (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q)
    {x : ℕ} (h : WinOK c q x) : WinOK c' q x := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hlen := Inv.len_step hs
  have hS : c'.S q = c.S q := by rw [hI.sEq_step hs q, hq, hI.sEq q]
  rw [WinOK, hq, hS]
  exact ⟨h1, h2, h3, by omega⟩

lemma upd2_ne {α β γ : Type} [DecidableEq α] [DecidableEq β] (F : α → β → γ) (a : α) (b : β)
    (v : γ) (p : α) {q : β} (hq : q ≠ b) : Function.update F a (Function.update (F a) b v) p q = F p q := by
  by_cases hp : p = a
  · subst hp; simp [Function.update_of_ne hq]
  · simp [Function.update_of_ne hp]

lemma PSide.congr {c c' : Cfg n T} {p q : Fin n} {x : ℤ} (hlp : c'.loc p = c.loc p)
    (hlq : c'.loc q = c.loc q) : PSide c' p q x ↔ PSide c p q x := by
  unfold PSide; rw [hlp, hlq]

set_option hygiene false in
/-- Generic case of `bcore_frame`. -/
local macro "bgen" p0:ident : tactic => `(tactic| (
  by_cases hp : p = $p0
  · subst hp; exact ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs, by simp [PSide]⟩
  · exact ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs,
      (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩))

/-- A stable hint stays stable while `q` does not move (Claim 4.18). -/
lemma Inv.bcore_frame (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q)
    {p : Fin n} {x : ℤ} {j : Idx n} (hx : x = c.S q) (hB : Bcore c p q x j) :
    Bcore c' p q x j := by
  obtain ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs, hps⟩ := hB
  have hxS : x = Sval n (c.loc q).m := hx.trans (hI.sEq q)
  cases hs
  case winv p0 v h => bgen p0
  case rec27 p0 v f h hff => bgen p0
  case rec29 p0 v f h => bgen p0
  case rec31 p0 v f h => bgen p0
  case swinv p0 v f h => bgen p0
  case swret p0 v f r h => bgen p0
  case l16s p0 v f s m14 olds h hc => bgen p0
  case l23 p0 v f h => bgen p0
  case wret p0 v h => bgen p0
  case einv p0 o ho h => bgen p0
  case l34 p0 o h => bgen p0
  case l36 p0 o x h => bgen p0
  case l37 p0 o x i g ts h => bgen p0
  case l39 p0 o x i g ts h => bgen p0
  case l40h p0 o x i g ts hv h hb hb' h1 h2 h3 h4 h5 => bgen p0
  case l40d p0 o x i g ts hv h hn => bgen p0
  case opinv p0 o x i ts h => bgen p0
  case opret p0 x i ts t r h => bgen p0
  case eret p0 r h => bgen p0
  case l14 p0 v f h =>
    by_cases hp : p = p0
    · subst hp
      nq p
      refine ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs, ?_⟩
      simp only [PSide, Function.update_self]
      intro hcq; rw [hcq, Function.update_of_ne (Ne.symm hne)]
    · exact ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs,
        (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l15 p0 v f s m14 h =>
    by_cases hp : p = p0
    · subst hp
      nq p
      refine ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs, ?_⟩
      simp only [PSide, h] at hps
      simp only [PSide, Function.update_self]
      intro hcq
      refine ⟨?_, by rw [hcq, hH]; simp [hsx]⟩
      rw [hps hcq, hcq, Function.update_of_ne (Ne.symm hne)]
    · exact ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs,
        (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l16w p0 v f s m14 olds h hc =>
    by_cases hp : p = p0
    · subst hp
      nq p
      refine ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs, ?_⟩
      simp only [PSide, Function.update_self]
      intro hcq
      simp only [PSide, h] at hps
      obtain ⟨e1, e2⟩ := hps hcq
      have hl := (hI.locRd p).1 s m14 (by simp [h, smOf])
      rw [hcq, hH'] at hc
      rw [e2, hl.1, e1, ← hxS] at hc
      simp [hbs] at hc
    · exact ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs,
        (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l18 p0 v f s m14 olds olds' h =>
    by_cases hp : p = p0
    · subst hp
      simp only [PSide, h] at hps
      refine ⟨h₀, b, ?_, hH', hf, hbf, hw, hsx, hbs, ?_⟩
      · simpa [Function.update_of_ne (Ne.symm hps)] using hH
      · simp only [PSide, Function.update_self]; exact hps
    · exact ⟨h₀, b, by simpa [Function.update_of_ne hp] using hH, hH', hf, hbf, hw, hsx, hbs,
        (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l19 p0 v f h =>
    by_cases hp : p = p0
    · subst hp
      simp only [PSide, h] at hps
      refine ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs, ?_⟩
      simp only [PSide, Function.update_self]; exact hps
    · exact ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs,
        (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l20 p0 v f s' m19 τ19 h =>
    by_cases hp : p = p0
    · subst hp
      simp only [PSide, h] at hps
      refine ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs, ?_⟩
      simp only [PSide, Function.update_self]; exact hps
    · exact ⟨h₀, b, hH, hH', hf, hbf, hw, hsx, hbs,
        (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l21 p0 v f s' m19 τ19 π h =>
    by_cases hp : p = p0
    · subst hp
      simp only [PSide, h] at hps
      refine ⟨h₀, b, hH, ?_, hf, hbf, hw, hsx, hbs, by simp [PSide]⟩
      simpa [Function.update_of_ne (Ne.symm hps)] using hH'
    · exact ⟨h₀, b, hH, by simpa [Function.update_of_ne hp] using hH', hf, hbf, hw, hsx, hbs,
        (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l35 p0 o x' h => nq p0; bgen p0
  case l44 p0 x' r h =>
    nq p0
    by_cases hp : p = p0
    · subst hp; exact ⟨h₀, b, (upd2_ne _ _ _ _ _ (Ne.symm hne)).trans hH, hH', hf, hbf,
        hw, hsx, hbs, by simp [PSide]⟩
    · exact ⟨h₀, b, (upd2_ne _ _ _ _ _ (Ne.symm hne)).trans hH, hH', hf, hbf, hw, hsx,
        hbs, (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩
  case l45 p0 x' r h =>
    nq p0
    by_cases hp : p = p0
    · subst hp; exact ⟨h₀, b, hH, (upd2_ne _ _ _ _ _ (Ne.symm hne)).trans hH', hf, hbf,
        hw, hsx, hbs, by simp [PSide]⟩
    · exact ⟨h₀, b, hH, (upd2_ne _ _ _ _ _ (Ne.symm hne)).trans hH', hf, hbf, hw, hsx,
        hbs, (PSide.congr (by simp [Function.update_of_ne hp]) hq).2 hps⟩

lemma Inv.tr_ext (hs : Step W c c') : ∃ t, c'.tr = c.tr ++ t := by
  cases hs <;> simp

lemma ptrAt_ext {tr t : List (Ev (Fin n) (Idx n) T)} {ts : ℕ} (h : ts ≤ tr.length) :
    ptrAt (tr ++ t) ts = ptrAt tr ts := by
  unfold ptrAt; rw [List.take_append_of_le_length h]

lemma Inv.annc_frame (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q) :
    c'.annc q = c.annc q := by
  cases hs
  case l37 p o x i g ts h =>
    nq p; simp [Function.update_of_ne (Ne.symm hne)]
  all_goals rfl

/-- If neither `p` nor `q` moves, the hint entries `H_p[q]`, `H'_p[q]` do not change. -/
lemma Inv.hH_frame (hs : Step W c c') {p q : Fin n} (hq : c'.loc q = c.loc q)
    (hp : c'.loc p = c.loc p) : c'.hH p q = c.hH p q ∧ c'.hH' p q = c.hH' p q := by
  cases hs
  case l18 p0 v f s m14 olds olds' h =>
    have hne : p0 ≠ p := by
      rintro rfl; have h' := congrArg Loc.pc hp
      simp only [Function.update_self] at h'; rw [h] at h'; simp at h'
    exact ⟨by simp [Function.update_of_ne (Ne.symm hne)], rfl⟩
  case l21 p0 v f s' m19 τ19 π h =>
    have hne : p0 ≠ p := by
      rintro rfl; have h' := congrArg Loc.pc hp
      simp only [Function.update_self] at h'; rw [h] at h'; simp at h'
    exact ⟨rfl, by simp [Function.update_of_ne (Ne.symm hne)]⟩
  case l44 p0 x r h =>
    nq p0; exact ⟨upd2_ne _ _ _ _ _ (Ne.symm hne), rfl⟩
  case l45 p0 x r h =>
    nq p0; exact ⟨rfl, upd2_ne _ _ _ _ _ (Ne.symm hne)⟩
  all_goals exact ⟨rfl, rfl⟩

lemma Bcore.congr {c c' : Cfg n T} {p q : Fin n} {x : ℤ} {j : Idx n} (hlp : c'.loc p = c.loc p)
    (hlq : c'.loc q = c.loc q) (hH : c'.hH p q = c.hH p q) (hH' : c'.hH' p q = c.hH' p q) :
    Bcore c' p q x j ↔ Bcore c p q x j := by
  unfold Bcore; rw [hH, hH', PSide.congr hlp hlq]

lemma Cprog.congr {c c' : Cfg n T} {p q : Fin n} {x : ℤ} {g : ℕ} (hlp : c'.loc p = c.loc p)
    (hlq : c'.loc q = c.loc q) (hH : c'.hH p q = c.hH p q) (hH' : c'.hH' p q = c.hH' p q) :
    Cprog c' p q x g ↔ Cprog c p q x g := by
  unfold Cprog
  simp only [Bcore.congr hlp hlq hH hH', hlp, hlq, hH]

lemma A1.congr {c c' : Cfg n T} {q : Fin n} {x : ℤ} {i : Idx n} {g ts : ℕ}
    (hlp : c'.loc i.1 = c.loc i.1) (hlq : c'.loc q = c.loc q) (hH : c'.hH i.1 q = c.hH i.1 q)
    (hH' : c'.hH' i.1 q = c.hH' i.1 q) : A1 c' q x i g ts ↔ A1 c q x i g ts := by
  unfold A1 PPok; rw [Cprog.congr hlp hlq hH hH', hlp]

lemma Inv.dcore_frame (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q)
    {i : Idx n} (h : Dcore c q i) : Dcore c' q i := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨(Inv.annc_frame hs hq).trans h1, ?_⟩
  exact hI.slotProt_step hs (by decide) rfl h2 (fun _ => h1) (fun h => absurd h (by decide))
    (fun h => absurd h (by decide))

lemma Inv.notfree_of_bcore (hI : Inv W c) {p q : Fin n} {x : ℤ} {i : Idx n}
    (h : Bcore c p q x i) : i ∉ (c.loc p).qs.free ∧ i.1 = p := by
  obtain ⟨a, b, ha, -, rfl, -⟩ := h
  obtain ⟨h1, h2, -⟩ := hI.hint p q a ha
  exact ⟨h2.1, h1⟩

lemma Inv.commit_frame (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q)
    {x : ℕ} {i : Idx n} {ts : ℕ} (hx : (x : ℤ) = c.S q) (h : Commit c q x i ts) :
    Commit c' q x i ts := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  obtain ⟨t, ht⟩ := Inv.tr_ext hs
  have hfree : i ∉ (c.loc i.1).qs.free := by
    rcases h5 with h5 | h5
    · exact h5.2.1
    · exact (hI.notfree_of_bcore h5).1
  refine ⟨by rw [hq]; exact h1, by rw [ht]; simp; omega, by rw [ht, ptrAt_ext h2]; exact h3,
    hI.ppok_step hs h4 hfree, ?_⟩
  rcases h5 with h5 | h5
  · exact Or.inl (hI.dcore_frame hs hq h5)
  · exact Or.inr (hI.bcore_frame hs hq hx h5)

end Podc.WritableObjects.WF
