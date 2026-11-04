import Papers.PODC2014.WritableObjects.Lemma48Exec1

/-!
# Lemma 4.8, part 9: the window between lines 36 and 40 of `Exec` (Claims 4.20, 4.24)
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

set_option hygiene false in
/-- Generic case of `a1_frame`: the owner moves to a line where `Cprog` is trivial. -/
local macro "a1gen" p0:ident : tactic => `(tactic| (
  have e : i.1 = $p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
  subst e
  left
  unfold A1; simp only [Function.update_self]
  refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, *])), by simpa [PPok] using hPP', hg,
    hw, ?_⟩
  intro _ _; simp [Cprog]))

/-- Claim 4.20 / (4.32): between lines 36 and 37 of `Exec`, either the owner of the index read
from `Ptr` has not completed a `Write` with `ctr ≡ q` since, or a stable hint for `q` exists. -/
lemma Inv.a1_frame (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q)
    {x : ℕ} {i : Idx n} {g ts : ℕ} (hx : (x : ℤ) = c.S q)
    (h : A1 c q x i g ts ∨ ∃ j, Bcore c i.1 q x j) :
    A1 c' q x i g ts ∨ ∃ j, Bcore c' i.1 q x j := by
  rcases h with hA | ⟨j, hB⟩
  swap; · exact Or.inr ⟨j, hI.bcore_frame hs hq hx hB⟩
  by_cases hp : c'.loc i.1 = c.loc i.1
  · obtain ⟨e1, e2⟩ := Inv.hH_frame hs hq hp
    exact Or.inl ((A1.congr hp hq e1 e2).2 hA)
  obtain ⟨hP, hPP, hg, hw, hC⟩ := hA
  have hxS : (x : ℤ) = Sval n (c.loc q).m := hx.trans (hI.sEq q)
  have hctr : (c.loc i.1).ctr ≤ g + n :=
    le_of_no_mod q.isLt (fun w h1 h2 h3 => hw w h1 h2 (Fin.ext h3))
  have hn := Nat.pos_of_neZero n
  have hPP' := hI.ppok_step hs hPP hP.1
  cases hs
  case winv p0 v h => a1gen p0
  case swinv p0 v f h => a1gen p0
  case swret p0 v f r h => a1gen p0
  case wret p0 v h => a1gen p0
  case einv p0 o ho h => a1gen p0
  case l34 p0 o h => a1gen p0
  case l35 p0 o x' h => a1gen p0
  case l36 p0 o x' h => a1gen p0
  case l37 p0 o x' i' g' ts' h => a1gen p0
  case l39 p0 o x' i' g' ts' h => a1gen p0
  case l40h p0 o x' i' g' ts' hv h hb hb' h1 h2 h3 h4 h5 => a1gen p0
  case l40d p0 o x' i' g' ts' hv h hn' => a1gen p0
  case opinv p0 o x' i' ts' h => a1gen p0
  case opret p0 x' i' ts' t r h => a1gen p0
  case l44 p0 x' r h => a1gen p0
  case l45 p0 x' r h => a1gen p0
  case eret p0 r h => a1gen p0
  case rec27 p0 v f h hf =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e; left
    unfold A1; simp only [Function.update_self]
    refine ⟨Loc.r27_Prot h (hI.qok _) hP (by omega), by simpa [PPok] using hPP', hg, hw, ?_⟩
    intro _ _; simp [Cprog]
  case rec29 p0 v f h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e; left
    unfold A1; simp only [Function.update_self]
    refine ⟨Loc.r29_Prot h (hI.qok _) hP (by omega), by simpa [PPok] using hPP', hg, hw, ?_⟩
    intro _ _; simp [Cprog]
  case rec31 p0 v f h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e; left
    unfold A1; simp only [Function.update_self]
    refine ⟨Loc.r31_Prot h (hI.qok _) hP (by omega), by simpa [PPok] using hPP', hg, hw, ?_⟩
    intro _ _; simp [Cprog]
  case l14 p0 v f h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    left
    unfold A1; simp only [Function.update_self]
    refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simpa [PPok] using hPP', hg,
      hw, ?_⟩
    simp only [Cprog, Function.update_self, Function.update_of_ne (Ne.symm hne)]
    intro _ hcq; rw [hcq]; try simp [Function.update_of_ne (Ne.symm hne)]
  case l15 p0 v f s m14 h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    left
    unfold A1; simp only [Function.update_self]
    refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simpa [PPok] using hPP', hg,
      hw, ?_⟩
    simp only [Cprog, h] at hC
    simp only [Cprog, Function.update_self, Function.update_of_ne (Ne.symm hne)]
    intro h1 hcq; exact ⟨hC h1 hcq, by rw [hcq]⟩
  case l16w p0 v f s m14 olds h hc =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    left
    unfold A1; simp only [Function.update_self]
    refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simpa [PPok] using hPP', hg,
      hw, ?_⟩
    simp only [Cprog, h] at hC
    simp only [Cprog, Function.update_self, Function.update_of_ne (Ne.symm hne)]
    intro h1 hcq; exact (hC h1 hcq).1
  case l16s p0 v f s m14 olds h hc =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    by_cases hcond : g < (c.loc i.1).ctr ∧ cq (c.loc i.1).ctr = q
    · -- the hint for `q` is valid: it becomes stable (Claim 4.20, first case)
      right
      simp only [Cprog, h] at hC
      obtain ⟨e1, e2⟩ := hC hcond.1 hcond.2
      have hl := (hI.locRd i.1).1 s m14 (by simp [h, smOf])
      rw [hcond.2] at hc
      simp only [not_or, not_not] at hc
      obtain ⟨hc1, hc2⟩ := hc
      rw [e2] at hc1
      have hsx : s = x := by rw [hl.1, e1, ← hxS]
      obtain ⟨a, ha, has⟩ : ∃ a, c.hH i.1 q = some a ∧ a.s = s := by
        cases hh : c.hH i.1 q with
        | none => rw [hh] at hc1; simp at hc1
        | some a => rw [hh] at hc1; simp at hc1; exact ⟨a, rfl, hc1.symm⟩
      obtain ⟨b, hb, hbs⟩ : ∃ b, c.hH' i.1 q = some b ∧ b.s = s := by
        cases hh : c.hH' i.1 q with
        | none => rw [hh] at hc2; simp at hc2
        | some b => rw [hh] at hc2; simp at hc2; exact ⟨b, rfl, hc2.symm⟩
      obtain ⟨hw1, hf1, -⟩ := hI.pairOut i.1 q (by simp [h, isW1921]) a b ha hb
      exact ⟨a.f, a, b, ha, hb, rfl, hf1.symm, hw1, by rw [has, hsx], by rw [hbs, hsx],
        by simp [PSide]⟩
    · left
      unfold A1; simp only [Function.update_self]
      refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simpa [PPok] using hPP', hg,
        hw, ?_⟩
      intro h1 h2; exact absurd ⟨by simpa using h1, by simpa using h2⟩ hcond
  case l18 p0 v f s m14 olds olds' h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    left
    unfold A1; simp only [Function.update_self]
    refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simpa [PPok] using hPP', hg,
      hw, ?_⟩
    simp only [Cprog, h] at hC
    simp only [Cprog, Function.update_self]
    intro h1 hcq
    have hl := (hI.locRd i.1).1 s m14 (by simp [h, smOf])
    refine ⟨⟨f, s, (c.loc i.1).ctr, m14, (c.loc (cq (c.loc i.1).ctr)).m⟩, ?_, rfl, ?_, rfl⟩
    · subst hcq; simp
    · simp only; rw [hl.1, hC h1 hcq, ← hxS]
  case l19 p0 v f h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    left
    unfold A1; simp only [Function.update_self]
    refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simpa [PPok] using hPP', hg,
      hw, ?_⟩
    simp only [Cprog, h] at hC
    simp only [Cprog, Function.update_self]
    intro h1 hcq
    refine ⟨hC h1 hcq, ?_⟩
    rw [hcq, Function.update_of_ne (Ne.symm hne)]
  case l20 p0 v f s' m19 τ19 h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    left
    unfold A1; simp only [Function.update_self]
    refine ⟨hP.congr rfl (Loc.U_congr rfl (by simp [stage, h])), by simpa [PPok] using hPP', hg,
      hw, ?_⟩
    simp only [Cprog, h] at hC
    simp only [Cprog, Function.update_self]
    intro h1 hcq
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    simpa [Function.update_of_ne (Ne.symm hne)] using hC h1 hcq
  case l21 p0 v f s' m19 τ19 π h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    by_cases hcond : g < (c.loc i.1).ctr ∧ cq (c.loc i.1).ctr = q
    · -- the new hint becomes stable (Claim 4.20, second case)
      right
      simp only [Cprog, h] at hC
      obtain ⟨⟨a, ha, haf, has, haw⟩, hm19⟩ := hC hcond.1 hcond.2
      have hl := (hI.locRd i.1).2.2.2.2 s' m19 τ19 (by simp [h, s19Of])
      rw [hcond.2] at hl
      refine ⟨f, a, ⟨f, s', (c.loc i.1).ctr, m19, π⟩, ha, ?_, haf, rfl, haw, has, ?_,
        by simp [PSide]⟩
      · simp [← hcond.2]
      · simp only; rw [hl.1, hm19, ← hxS]
    · left
      unfold A1; simp only [Function.update_self]
      refine ⟨hP.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, h]; omega),
        by simpa [PPok] using hPP', by omega, ?_, by intro _ _; simp [Cprog]⟩
      intro w h1 h2
      rcases Nat.lt_or_ge w (c.loc i.1).ctr with h3 | h3
      · exact hw w h1 h3
      · have : w = (c.loc i.1).ctr := by omega
        subst this; exact fun h4 => hcond ⟨h1, h4⟩
  case l23 p0 v f h =>
    have e : i.1 = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : i.1 ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    by_cases hcond : g < (c.loc i.1).ctr ∧ cq (c.loc i.1).ctr = q
    · right
      simp only [Cprog, h] at hC
      obtain ⟨j, a, b, ha, hb, h1, h2, h3, h4, h5, -⟩ := hC hcond.1 hcond.2
      exact ⟨j, a, b, ha, hb, h1, h2, h3, h4, h5, by simp [PSide]⟩
    · left
      unfold A1; simp only [Function.update_self]
      refine ⟨hP.congr rfl (by funext o; have := o.isLt; simp [Loc.U, stage, h]; omega),
        by simpa [PPok] using hPP', by omega, ?_, by intro _ _; simp [Cprog]⟩
      intro w h1 h2
      rcases Nat.lt_or_ge w (c.loc i.1).ctr with h3 | h3
      · exact hw w h1 h3
      · have : w = (c.loc i.1).ctr := by omega
        subst this; exact fun h4 => hcond ⟨h1, h4⟩

lemma M14c.congr {c c' : Cfg n T} {p q : Fin n} {w : ℕ} (hlp : c'.loc p = c.loc p)
    (hlq : c'.loc q = c.loc q) : M14c c' p q w ↔ M14c c p q w := by
  unfold M14c; rw [hlp, hlq]

lemma I39.congr {c c' : Cfg n T} {p q : Fin n} {x : ℤ} {h : HE n} (hlp : c'.loc p = c.loc p)
    (hlq : c'.loc q = c.loc q) (hH : c'.hH p q = c.hH p q) (hH' : c'.hH' p q = c.hH' p q) :
    I39 c' p q x h ↔ I39 c p q x h := by
  unfold I39; simp only [hH, hH', M14c.congr hlp hlq]

set_option hygiene false in
/-- Generic case of `i39_frame`: the owner moves without touching `H_p[q]`, `H'_p[q]`. -/
local macro "i39gen" p0:ident : tactic => `(tactic| (
  have e : p = $p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
  subst e
  obtain ⟨a, ha, hle, hii, hiii⟩ := hI39
  have hne : p ≠ q := by rintro e; rw [← e] at hq; exact hp hq
  refine ⟨a, ?_, hle, ?_, ?_⟩
  · first | exact ha | exact (upd2_ne _ _ _ _ _ (Ne.symm hne)).trans ha
  · intro e1; obtain ⟨e2, e3, e4⟩ := hii e1
    refine ⟨e2, e3, fun b hb => e4 b ?_⟩
    first | exact hb | exact (upd2_ne _ _ _ _ _ (Ne.symm hne)).symm.trans hb
  · intro e1; obtain ⟨e2, e3, e4⟩ := hiii e1
    refine ⟨e2, fun b hb => e3 b ?_, ?_⟩
    · first | exact hb | exact (upd2_ne _ _ _ _ _ (Ne.symm hne)).symm.trans hb
    · intro mm hmm hcq hw
      simp only [Function.update_self, Function.update_of_ne (Ne.symm hne), m14Of, reduceCtorEq,
        Option.some.injEq] at hmm hcq hw ⊢
      all_goals exact e4 mm (by simp [h0, m14Of, hmm]) hcq hw))

/-- Claim 4.24: after line 39, a hint read later from `H'_p[q]` that matches the one read from
`H_p[q]` comes from the same `Write` as the current `H_p[q]`. -/
lemma Inv.i39_frame (hI : Inv W c) (hs : Step W c c') {q : Fin n} (hq : c'.loc q = c.loc q)
    {p : Fin n} {x : ℕ} {h : HE n} (hx : (x : ℤ) = c.S q) (hpre : pre44 (c.loc q).pc = true)
    (hI39 : I39 c p q x h) : I39 c' p q x h := by
  by_cases hp : c'.loc p = c.loc p
  · obtain ⟨e1, e2⟩ := Inv.hH_frame hs hq hp
    exact (I39.congr hp hq e1 e2).2 hI39
  have hxS : (x : ℤ) = Sval n (c.loc q).m := hx.trans (hI.sEq q)
  cases hs
  case winv p0 v h0 => i39gen p0
  case rec27 p0 v f h0 hf => i39gen p0
  case rec29 p0 v f h0 => i39gen p0
  case rec31 p0 v f h0 => i39gen p0
  case swinv p0 v f h0 => i39gen p0
  case swret p0 v f r h0 => i39gen p0
  case l15 p0 v f s m14 h0 => i39gen p0
  case l16w p0 v f s m14 olds h0 hc => i39gen p0
  case l16s p0 v f s m14 olds h0 hc => i39gen p0
  case l19 p0 v f h0 => i39gen p0
  case l20 p0 v f s' m19 τ19 h0 => i39gen p0
  case l23 p0 v f h0 => i39gen p0
  case wret p0 v h0 => i39gen p0
  case einv p0 o ho h0 => i39gen p0
  case l34 p0 o h0 => i39gen p0
  case l35 p0 o x' h0 => i39gen p0
  case l36 p0 o x' h0 => i39gen p0
  case l37 p0 o x' i' g' ts' h0 => i39gen p0
  case l39 p0 o x' i' g' ts' h0 => i39gen p0
  case l40h p0 o x' i' g' ts' hv h0 hb hb' h1 h2 h3 h4 h5 => i39gen p0
  case l40d p0 o x' i' g' ts' hv h0 hn' => i39gen p0
  case opinv p0 o x' i' ts' h0 => i39gen p0
  case opret p0 x' i' ts' t r h0 => i39gen p0
  case l44 p0 x' r h0 => i39gen p0
  case l45 p0 x' r h0 => i39gen p0
  case eret p0 r h0 => i39gen p0
  case l14 p0 v f h0 =>
    have e : p = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : p ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    obtain ⟨a, ha, hle, hii, hiii⟩ := hI39
    refine ⟨a, ha, hle, hii, fun e1 => ⟨(hiii e1).1, (hiii e1).2.1, ?_⟩⟩
    intro m14 hm14 hcq hw
    simp only [Function.update_self, m14Of, Option.some.injEq] at hm14 hcq hw ⊢
    subst hm14; rw [hcq]; simp [Function.update_of_ne (Ne.symm hne)]
  case l18 p0 v f s m14 olds olds' h0 =>
    have e : p = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : p ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    obtain ⟨a, ha, hle, hii, hiii⟩ := hI39
    by_cases hcq : cq (c.loc p).ctr = q
    swap
    · refine ⟨a, by simpa [Function.update_of_ne (Ne.symm hcq)] using ha, hle, hii, ?_⟩
      intro e1; obtain ⟨e2, e3, -⟩ := hiii e1
      refine ⟨e2, e3, ?_⟩
      intro m14' hm14; simp [m14Of] at hm14
    subst hcq
    -- the new entry of `H_p[q]`, written by the current `Write`
    have haw : a.w < (c.loc p).ctr := by
      rcases (hI.hint p _ a ha).2.2.2.2.2.2 with h1 | ⟨-, h1, -⟩
      · exact h1
      · simp [h0, isW1921] at h1
    have hl := (hI.locRd p).1 s m14 (by simp [h0, smOf])
    obtain ⟨-, hO, hO', hbr, -⟩ := hI.locRd p
    have holds := hO olds (by simp [h0, oldsOf]) a ha
    have hbr' := hbr _ _ _ _ _ _ h0
    have hmono := hI.mono p m14 (by simp [h0, m14Of])
    have hlm := hl.2
    refine ⟨⟨f, s, (c.loc p).ctr, m14, (c.loc (cq (c.loc p).ctr)).m⟩, by simp, by simp; omega,
      fun e1 => by simp at e1; omega, fun _ => ⟨?_, ?_, ?_⟩⟩
    · intro hf
      simp only at hf ⊢
      rcases Nat.lt_or_ge h.w a.w with hlt | hge
      · have := (hiii hlt).2.2 m14 (by simp [h0, m14Of]) rfl haw
        rw [hl.1, this, ← hxS]
      · have e1 : a.w = h.w := by omega
        obtain ⟨e2, -, -⟩ := hii e1
        have hlc1 := (hI.chosen p f (by simp [h0, curF])).2.2
        have hlc2 := (hI.hint p _ a ha).2.2.1
        rw [e2, ← hf] at hlc2
        omega
    · intro b hb hbf hbs
      exfalso
      have hold' := hO' olds' (by simp [h0, olds'Of]) b hb
      have hm14 : m14 = (c.loc (cq (c.loc p).ctr)).m := by
        rcases Nat.lt_or_ge h.w a.w with hlt | hge
        · exact (hiii hlt).2.2 m14 (by simp [h0, m14Of]) rfl haw
        · have e1 : a.w = h.w := by omega
          have hbw := (hii e1).2.2 b hb hbf
          have hfr := hI.fresh ha hb (by omega) (by rw [hbs, hxS]) hpre
          have := hmono b hb
          omega
      have has : a.s = x := by
        rcases Nat.lt_or_ge h.w a.w with hlt | hge
        · exact ((hiii hlt).2.1 b hb hbf hbs).2.2
        · exact (hii (by omega)).2.1
      rw [holds, hold', has, hbs, hl.1, hm14, ← hxS] at hbr'
      simp at hbr'
    · intro m14' hm14; simp [m14Of] at hm14
  case l21 p0 v f s' m19 τ19 π h0 =>
    have e : p = p0 := by by_contra hne; exact hp (by simp [Function.update_of_ne hne])
    subst e
    have hne : p ≠ q := by rintro e; rw [← e] at hq; exact hp hq
    obtain ⟨a, ha, hle, hii, hiii⟩ := hI39
    by_cases hcq : cq (c.loc p).ctr = q
    swap
    · refine ⟨a, ha, hle, fun e1 => ?_, fun e1 => ?_⟩
      · obtain ⟨e2, e3, e4⟩ := hii e1
        exact ⟨e2, e3, fun b hb => e4 b (by simpa [Function.update_of_ne (Ne.symm hcq)] using hb)⟩
      · obtain ⟨e2, e3, -⟩ := hiii e1
        refine ⟨e2, fun b hb => e3 b (by simpa [Function.update_of_ne (Ne.symm hcq)] using hb), ?_⟩
        intro m14' hm14; simp [m14Of] at hm14
    subst hcq
    obtain ⟨hpa1, hpa2, -⟩ := hI.pairIn p _ (by simp [h0, isW1921]) rfl a ha
    simp only [h0, curF, Option.some.injEq] at hpa2
    refine ⟨a, ha, hle, fun e1 => ?_, fun e1 => ?_⟩
    · obtain ⟨e2, e3, -⟩ := hii e1
      refine ⟨e2, e3, fun b hb hbf => ?_⟩
      simp only [Function.update_self, Option.some.injEq] at hb; subst hb
      simp only; omega
    · obtain ⟨e2, -, -⟩ := hiii e1
      refine ⟨e2, fun b hb hbf hbs => ?_, ?_⟩
      · simp only [Function.update_self, Option.some.injEq] at hb; subst hb
        simp only at hbf
        have haf : a.f = h.f := by rw [← hpa2, hbf]
        exact ⟨hpa1.symm, haf, e2 haf⟩
      · intro m14' hm14; simp [m14Of] at hm14

end Podc.WritableObjects.WF
