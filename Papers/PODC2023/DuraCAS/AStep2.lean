import Papers.PODC2023.DuraCAS.AStep1
import Papers.PODC2023.DuraCAS.AStepL

/-!
# Preservation of the global invariant: successful `ECSC`s

`GInv.ec`: a successful `ECSC` of process `p` (at its call site or as an orphan) on an EC object of
the object `r.k` of its operation `r`; the other processes on `r.k` are handled by the frame lemmas
of `AFrame.lean`, those on other objects are unaffected.
-/

namespace Podc.DuraCAS

set_option linter.unusedSectionVars false

variable {P K V : Type} [DecidableEq P] [DecidableEq K] [DecidableEq V]

/-- The A-level state after a successful `ECSC` of `p`. -/
def AS.ec (a : AS P K V) (p : P) (o : Obj K) (c' : Cell V) (h : Hd P) (s' : ℕ)
    (st' : APS P K V) : AS P K V :=
  { a with Y := Function.update a.Y o c', ls := Function.update a.ls h s',
           ps := Function.update a.ps p st' }

/-- The ghost state after a successful `ECSC` on an EC object of `k`. -/
def Gh.ec (g : Gh P K V) (k : K) (L' : List (GE K V)) (wit' : P → Option ℕ) (pw' : Option ℕ)
    (zAt' : ℕ) (lm' : Bool) : Gh P K V :=
  { g with clk := g.clk + 1, L := L', wit := wit', pw := Function.update g.pw k pw',
           zAt := Function.update g.zAt k zAt', lm := Function.update g.lm k lm' }

theorem GInv.ec {init : K → V} {a : AS P K V} {g : Gh P K V} {p : P} {r : OpRec K V}
    (h : GInv init a g) (hop : (a.ps p).op = some r) {o : Obj K} {c' : Cell V} {hd : Hd P}
    {s' : ℕ} {st' : APS P K V} (ho : o.1 = r.k) (hh : hd.1 = p) (hst : st'.op = some r)
    {L' : List (GE K V)} {wit' : P → Option ℕ} {pw' : Option ℕ} {zAt' : ℕ} {lm' : Bool}
    (hLg : LGood init L' (g.clk + 1)) (hsub : ∀ e ∈ g.L, e ∈ L')
    (hmem : ∀ e ∈ L', e ∈ g.L ∨ (e.key = 4 * g.clk + 1 ∧ ∃ q s, (a.ps q).op = some s ∧
      s.k = r.k ∧ e.id = s.id ∧ e.k = s.k ∧ e.op = s.op ∧ e.rsp = .ok true))
    (hstt : ∀ t < g.clk, stAt init L' t = stAt init g.L t)
    (hcur : ∀ k', k' ≠ r.k → curSt init L' k' = curSt init g.L k')
    (hwit : ∀ q, wit' q = g.wit q ∨ (wit' q = some g.clk ∧ ∃ s, (a.ps q).op = some s ∧
      s.k = r.k ∧ (∀ old new, s.op = .cas old new → curSt init L' r.k ≠ old) ∧
      (∀ u, s.op = .write u → ∃ y ∈ L', y.key = 4 * g.clk + 1 ∧ y.k = r.k ∧ y.op.IsWrite)))
    (hkv : (view init (a.ec p o c' hd s' st') (g.ec r.k L' wit' pw' zAt' lm') r.k).Inv)
    (hlocs : ∀ q s, (a.ps q).op = some s → s.k = r.k →
      Loc q (view init (a.ec p o c' hd s' st') (g.ec r.k L' wit' pw' zAt' lm') r.k)
        (pview (a.ec p o c' hd s' st') (g.ec r.k L' wit' pw' zAt' lm') q s))
    (hpw : pw' = none ∨ pw' = g.pw r.k ∨ pw' = some r.id) :
    GInv init (a.ec p o c' hd s' st') (g.ec r.k L' wit' pw' zAt' lm') := by
  set a' := a.ec p o c' hd s' st'
  set g' := g.ec r.k L' wit' pw' zAt' lm'
  have hops : ∀ q, (a'.ps q).op = (a.ps q).op := update_op_eq (by rw [hst, hop])
  have hpsq : ∀ q, q ≠ p → a'.ps q = a.ps q := fun q hq => by
    simp [a', AS.ec, Function.update_of_ne hq]
  have hidnew : ∀ e ∈ L', e ∉ g.L → ∃ q s, (a.ps q).op = some s ∧ s.k = r.k ∧ e.id = s.id ∧
      e.k = s.k ∧ e.op = s.op ∧ e.rsp = .ok true ∧ e.key = 4 * g.clk + 1 := by
    intro e he hn
    rcases hmem e he with h' | ⟨hk, q, s, hs, h'⟩
    · exact absurd h' hn
    · exact ⟨q, s, hs, h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.2.2, hk⟩
  have hv : ∀ k, k ≠ r.k → view init a' g' k = view init a g k := by
    intro k hk
    have h1 : o ≠ (k, .W) := fun e => hk (by rw [← ho, e])
    have h2 : o ≠ (k, .Z) := fun e => hk (by rw [← ho, e])
    simp only [view, a', g', AS.ec, Gh.ec, Function.update_of_ne h1.symm,
      Function.update_of_ne h2.symm, Function.update_of_ne hk, hcur k hk]
  have hnotp : ∀ q s, (a.ps q).op = some s → s.k ≠ r.k → q ≠ p := by
    intro q s hs hk e; subst e; rw [hop] at hs; cases hs; exact hk rfl
  have hpv : ∀ q s, (a.ps q).op = some s → s.k ≠ r.k → pview a' g' q s = pview a g q s := by
    intro q s hs hk
    have hq := hnotp q s hs hk
    have hhd : hd ≠ (q, .crit) := fun e => hq (by rw [← hh, e])
    have hw : wit' q = g.wit q := by
      rcases hwit q with h' | ⟨-, s2, hs2, hk2, -⟩
      · exact h'
      · rw [hs] at hs2; cases hs2; exact absurd hk2 hk
    simp only [pview, a', g', AS.ec, Gh.ec, Function.update_of_ne hq, Function.update_of_ne hhd.symm, hw]
    congr 1
    apply propext
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, he, hid⟩
      by_cases hn : e ∈ g.L
      · exact ⟨e, hn, hid⟩
      · obtain ⟨q2, s2, hs2, hk2, hid2, -⟩ := hidnew e he hn
        have := h.uniq q q2 s s2 hs hs2 (hid ▸ hid2)
        subst this; rw [hs] at hs2; cases hs2; exact absurd hk2 hk
    · rintro ⟨e, he, hid⟩; exact ⟨e, hsub e he, hid⟩
  have hhist : a'.hist = a.hist := rfl
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24⟩ := h
  have hbi : ∀ q s, (a.ps q).op = some s → ∀ i q' k op d,
      a.hist[i]? = some (Ev.inv s.id q' k op d) → g.evT i = g.it q := fun q s hs i q' k op d hi =>
    (GInv.inv_of_busy ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15,
          h16, h17, h18, h19, h20, h21, h22, h23, h24⟩ hs hi).2.2.2.2
  refine ⟨fun k => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hLg, h13, ?_, h15, h16, h17, ?_, ?_,
    ?_, ?_, h22, ?_, ?_⟩
  · by_cases hk : k = r.k
    · subst hk; exact hkv
    · rw [hv k hk]; exact h1 k
  · intro q s hs
    rw [hops] at hs
    by_cases hk : s.k = r.k
    · exact hk ▸ hlocs q s hs hk
    · rw [hpv q s hs hk, hv _ hk]; exact h2 q s hs
  · intro q hq
    rw [hops] at hq
    have hqp : q ≠ p := fun e => by subst e; rw [hop] at hq; cases hq
    rw [hpsq q hqp]; exact h3 q hq
  · intro k id hk
    by_cases hkk : k = r.k
    · subst hkk
      simp only [g', Gh.ec, Function.update_self] at hk
      rcases hpw with rfl | rfl | rfl
      · cases hk
      · obtain ⟨q, s, hs, h'⟩ := h4 _ id hk; exact ⟨q, s, by rw [hops]; exact hs, h'⟩
      · cases hk; exact ⟨p, r, by rw [hops]; exact hop, rfl, rfl⟩
    · simp only [g', Gh.ec, Function.update_of_ne hkk] at hk
      obtain ⟨q, s, hs, h'⟩ := h4 k id hk; exact ⟨q, s, by rw [hops]; exact hs, h'⟩
  · intro q q' s s2 hs hs2; rw [hops] at hs hs2; exact h5 q q' s s2 hs hs2
  · intro q s hs; rw [hops] at hs; exact h6 q s hs
  · intro q s hs; rw [hops] at hs; exact h7 q s hs
  · intro q s hs; rw [hops] at hs; exact h8 q s hs
  · intro q s hs; rw [hops] at hs; have := h9 q s hs; simp only [g', Gh.ec]; omega
  · intro q s hs t ht
    rw [hops] at hs
    rcases hwit q with hw | ⟨hw, s2, hs2, hk2, hc, hwr⟩
    · rw [show g'.wit q = wit' q from rfl, hw] at ht
      obtain ⟨a1, a2, a3, a4⟩ := h10 q s hs t ht
      refine ⟨a1, by simp only [g', Gh.ec]; omega, fun old new hop' => ?_, fun u hu => ?_⟩
      · simp only [g', Gh.ec]; rw [hstt t a2]; exact a3 old new hop'
      · obtain ⟨b1, y, hy, hy'⟩ := a4 u hu
        exact ⟨b1, y, hsub y hy, hy'⟩
    · rw [hs] at hs2; cases hs2
      rw [show g'.wit q = wit' q from rfl, hw] at ht; cases ht
      have hit := h9 q s hs
      refine ⟨by simp only [g', Gh.ec]; omega, by simp only [g', Gh.ec]; omega,
        fun old new hop' => ?_, fun u hu => ⟨by simp only [g', Gh.ec]; omega, by rw [hk2]; exact hwr u hu⟩⟩
      simp only [g', Gh.ec]
      rw [stAt_eq_curSt _ _ _ (fun e he => by have := hLg.key_lt e he; omega), hk2]
      exact hc old new hop'
  · intro q s hs e he hid
    rw [hops] at hs
    by_cases hn : e ∈ g.L
    · exact h11 q s hs e hn hid
    · obtain ⟨q2, s2, hs2, -, hid2, hk2, hop2, hr2, -⟩ := hidnew e he hn
      have := h5 q q2 s s2 hs hs2 (hid ▸ hid2)
      subst this; rw [hs] at hs2; cases hs2
      exact ⟨hk2, hop2, hr2⟩
  · intro i hi; have := h14 i hi; simp only [g', Gh.ec]; omega
  · intro e he
    by_cases hn : e ∈ g.L
    · exact h18 e hn
    · obtain ⟨q2, s2, hs2, -, hid2, hk2, hop2, -⟩ := hidnew e he hn
      obtain ⟨i, hi, -⟩ := h7 q2 s2 hs2
      exact ⟨i, q2, s2.d1, by rw [hid2, hk2, hop2]; exact hi⟩
  · intro e he i q k op d hi
    by_cases hn : e ∈ g.L
    · exact h19 e hn i q k op d hi
    · obtain ⟨q2, s2, hs2, -, hid2, -, -, -, hkey⟩ := hidnew e he hn
      rw [hid2] at hi
      have := hbi q2 s2 hs2 i q k op d hi
      have := h9 q2 s2 hs2
      simp only [g', Gh.ec]; rw [hkey]; omega
  · intro e he i y hi hy
    by_cases hn : e ∈ g.L
    · exact h20 e hn i y hi hy
    · obtain ⟨q2, s2, hs2, -, hid2, -⟩ := hidnew e he hn
      rw [hid2] at hy
      exact absurd hy (h8 q2 s2 hs2 y (List.mem_of_getElem? hi))
  · intro id resp d hr
    obtain ⟨e, he, h'⟩ := h21 id resp d hr
    exact ⟨e, hsub e he, h'⟩
  · intro id q k op d hm y hy hyend hlt
    obtain ⟨e, he, h'⟩ := h23 id q k op d hm y hy hyend hlt
    exact ⟨e, hsub e he, h'⟩
  · intro id q k op d hm hrd hin
    obtain ⟨e, he, hid⟩ := List.mem_map.1 hin
    by_cases hn : e ∈ g.L
    · exact h24 id q k op d hm hrd (List.mem_map.2 ⟨e, hn, hid⟩)
    · obtain ⟨q2, s2, hs2, -, hid2, -⟩ := hidnew e he hn
      rw [← hid, hid2] at hrd
      exact h8 q2 s2 hs2 _ hrd rfl

end Podc.DuraCAS
