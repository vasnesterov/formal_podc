import Papers.PODC2014.WritableObjects.Lemma48Exec3

/-!
# Lemma 4.8, part 11: the steps of a pending `Exec` itself (proof of Lemma 4.8, both cases)
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec} [NeZero n] {W : Writable T} {c c' : Cfg n T}

/-- Program counters of `Exec`. -/
def isExecPC : PC n T → Prop
  | .e34 .. | .e35 .. | .e36 .. | .e37 .. | .e39 .. | .e40 .. | .e43 .. | .eOp .. | .e44 ..
  | .e45 .. | .eRet .. => True
  | _ => False

lemma PSide_of_exec {c : Cfg n T} {p q : Fin n} {x : ℤ} (h : isExecPC (c.loc p).pc) :
    PSide c p q x := by
  unfold PSide; cases hp : (c.loc p).pc <;> simp_all [isExecPC]

lemma PSide.congr' {c c' : Cfg n T} {p q : Fin n} {x : ℤ} (hlp : c'.loc p = c.loc p)
    (hm : (c'.loc q).m = (c.loc q).m) : PSide c' p q x ↔ PSide c p q x := by
  unfold PSide; rw [hlp, hm]

/-- `q` changes only its program counter, between two `Exec` lines. -/
structure QPC (c : Cfg n T) (L : Fin n → Loc n T) (q : Fin n) : Prop where
  ne : ∀ p, p ≠ q → L p = c.loc p
  qs : (L q).qs = (c.loc q).qs
  ctr : (L q).ctr = (c.loc q).ctr
  pp : (L q).pp = (c.loc q).pp
  m : (L q).m = (c.loc q).m
  ex : isExecPC (c.loc q).pc
  ex' : isExecPC (L q).pc

lemma stage_of_exec {pc : PC n T} (h : isExecPC pc) : stage pc = 0 := by
  cases pc <;> simp_all [isExecPC, stage]

lemma QPC.qs' (h : QPC c c'.loc q) (p : Fin n) : (c'.loc p).qs = (c.loc p).qs := by
  by_cases hp : p = q
  · subst hp; exact h.qs
  · rw [h.ne p hp]

lemma QPC.U' (h : QPC c c'.loc q) (p : Fin n) : (c'.loc p).U = (c.loc p).U := by
  by_cases hp : p = q
  · subst hp; exact Loc.U_congr h.ctr (by rw [stage_of_exec h.ex, stage_of_exec h.ex'])
  · rw [h.ne p hp]

lemma QPC.pp' (h : QPC c c'.loc q) (p : Fin n) : (c'.loc p).pp = (c.loc p).pp := by
  by_cases hp : p = q
  · subst hp; exact h.pp
  · rw [h.ne p hp]

lemma QPC.m' (h : QPC c c'.loc q) (p : Fin n) : (c'.loc p).m = (c.loc p).m := by
  by_cases hp : p = q
  · subst hp; exact h.m
  · rw [h.ne p hp]

lemma QPC.ctr' (h : QPC c c'.loc q) (p : Fin n) : (c'.loc p).ctr = (c.loc p).ctr := by
  by_cases hp : p = q
  · subst hp; exact h.ctr
  · rw [h.ne p hp]

lemma QPC.prot (h : QPC c c'.loc q) {p : Fin n} {i : Idx n} {γ : ℕ} (hp : (c.loc p).Prot i γ) :
    (c'.loc p).Prot i γ := hp.congr (h.qs' p) (h.U' p)

lemma QPC.slot (h : QPC c c'.loc q) {p : Fin n} {i : Idx n} {o : Fin 4} {q' : Fin n}
    (hp : (c.loc p).SlotProt i o q') : (c'.loc p).SlotProt i o q' := hp.congr (h.qs' p) (h.U' p)

lemma QPC.ppok (h : QPC c c'.loc q) {i : Idx n} {ts : ℕ} (hp : PPok c i ts) : PPok c' i ts := by
  obtain ⟨π, h1, h2⟩ := hp; exact ⟨π, by rw [h.pp']; exact h1, h2⟩

lemma QPC.pside (h : QPC c c'.loc q) {p q' : Fin n} {x : ℤ} (hp : PSide c p q' x) :
    PSide c' p q' x := by
  by_cases hpq : p = q
  · subst hpq; exact PSide_of_exec h.ex'
  · exact (PSide.congr' (h.ne p hpq) (h.m' q')).2 hp

lemma QPC.bcore (h : QPC c c'.loc q) {p q' : Fin n} {x : ℤ} {j : Idx n}
    (hH : c'.hH p q' = c.hH p q') (hH' : c'.hH' p q' = c.hH' p q') (hB : Bcore c p q' x j) :
    Bcore c' p q' x j := by
  obtain ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hB
  exact ⟨a, b, hH.trans h1, hH'.trans h2, h3, h4, h5, h6, h7, h.pside h8⟩

lemma QPC.dcore (h : QPC c c'.loc q) {q' : Fin n} {i : Idx n} (hA : c'.annc q' = c.annc q')
    (hD : Dcore c q' i) : Dcore c' q' i := ⟨hA.trans hD.1, h.slot hD.2⟩

/-- The writer side of a hint that `q` read twice with its current sequence number
(the `p`-side of Claim 4.18, used in case 2 of Lemma 4.8). -/
lemma Inv.pside_of_hint (hI : Inv W c) {p q : Fin n} {x : ℤ} {a : HE n} {b : HE' n}
    (ha : c.hH p q = some a) (hb : c.hH' p q = some b) (hw : a.w = b.w) (has : a.s = x)
    (hbs : b.s = x) (hx : x = Sval n (c.loc q).m) (hfr : b.m19 = (c.loc q).m) :
    PSide c p q x := by
  obtain ⟨L1, L2, L3, L4, -⟩ := hI.locRd p
  have hmono := hI.mono p
  unfold PSide
  cases hpc : (c.loc p).pc <;> simp only
  case w15 v f s m14 =>
    intro hcq
    have e1 := hmono m14 (by simp [hpc, m14Of]) b (by rw [hcq]; exact hb)
    have e2 := (L1 s m14 (by simp [hpc, smOf])).2
    rw [hcq] at e2; omega
  case w16 v f s m14 olds =>
    intro hcq
    have e1 := hmono m14 (by simp [hpc, m14Of]) b (by rw [hcq]; exact hb)
    have e2 := (L1 s m14 (by simp [hpc, smOf])).2
    rw [hcq] at e2
    refine ⟨by omega, ?_⟩
    rw [L2 olds (by simp [hpc, oldsOf]) a (by rw [hcq]; exact ha), has]
  case w18 v f s m14 olds olds' =>
    intro hcq
    have e1 := hmono m14 (by simp [hpc, m14Of]) b (by rw [hcq]; exact hb)
    have e2 := L1 s m14 (by simp [hpc, smOf])
    rw [hcq] at e2
    have e3 := L2 olds (by simp [hpc, oldsOf]) a (by rw [hcq]; exact ha)
    have e4 := L3 olds' (by simp [hpc, olds'Of]) b (by rw [hcq]; exact hb)
    have e5 := L4 _ _ _ _ _ _ hpc
    have hm : m14 = (c.loc q).m := by omega
    rw [e3, e4, has, hbs, e2.1, hm, ← hx] at e5
    simp at e5
  case w19 v f =>
    intro hcq
    have e1 := (hI.pairIn p q (by simp [hpc, isW1921]) hcq a ha).1
    have e2 := (hI.hint' p q b hb).2.2.2.1
    omega
  case w20 v f s' m19 τ19 =>
    intro hcq
    have e1 := (hI.pairIn p q (by simp [hpc, isW1921]) hcq a ha).1
    have e2 := (hI.hint' p q b hb).2.2.2.1
    omega
  case w21 v f s' m19 τ19 π =>
    intro hcq
    have e1 := (hI.pairIn p q (by simp [hpc, isW1921]) hcq a ha).1
    have e2 := (hI.hint' p q b hb).2.2.2.1
    omega

lemma nr_le_of_A1 {l : Loc n T} {g : ℕ} {q : Fin n} (hw : ∀ w, g < w → w < l.ctr → cq w ≠ q) :
    l.nr 1 q ≤ 4 * (g + 2 * n + 1) := by
  have hctr : l.ctr ≤ g + n := le_of_no_mod q.isLt (fun w h1 h2 h3 => hw w h1 h2 (Fin.ext h3))
  have h1 := nextR_le (n := n) (l.U 1) 1 q
  have h2 : l.U 1 ≤ l.ctr + 1 := by unfold Loc.U; split_ifs <;> omega
  have hn := Nat.pos_of_neZero n
  have hv : ((1 : Fin 4) : ℕ) = 1 := rfl
  unfold Loc.nr; rw [hv]; omega

end Podc.WritableObjects.WF
