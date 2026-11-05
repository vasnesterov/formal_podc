import Papers.PODC2024.NoBroadcastKSA.Sim

/-!
# Sequential composition of process runs, and its admissibility

The adversarial executions of the repaired proof of Theorem 1 are concatenations
`catRun pars L fin`: first the runs of the processes `(pars i).p` for `L i` slots each, one after
the other (`i = 0, …, m-1`), then the run of `fin.p` forever. Only `fin.p` is correct; the other
processes crash at the end of their segment, and the processes outside the segments crash
initially.

`catRun_adm` gives the admissibility of such an execution in `CAMP_n[k-SA]`, under hypotheses on
the k-SA answers of the final run, its pending messages, and k-SA agreement.
-/

namespace Podc.NoBroadcastKSA.Camp

open Classical

variable {P C V X O W : Type} [DecidableEq P] [DecidableEq C]
variable (A : Algo P C V) (B : BAlgo P (Msg C) X O W)

/-! ## Structure of a process run -/

section RunStructure

variable (par : RunPar P C V X O W)

lemma mod4_cases (j : ℕ) : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega

lemma upperStep_proc (h : List (FLEv P (Msg C) X O W)) : (upperStep A par h).proc = par.p := by
  unfold upperStep
  split
  · split_ifs <;> rfl
  · rfl

/-- Whether the current copy has decided. -/
abbrev Dec (h : List (FLEv P (Msg C) X O W)) : Prop :=
  (simView A par.p par.v par.R par.F h).any isDecL = true

lemma pstep0 {t j : ℕ} (hj : j % 4 = 0) (st : LSt P C X O W) :
    pstep A B par t j st = (some (upperStep A par st.h),
      { st with h := st.h ++ [(upperStep A par st.h).floc] }) := by
  simp [pstep, hj]

lemma pstep1 {t j : ℕ} (hj : j % 4 = 1) (st : LSt P C X O W) :
    pstep A B par t j st = (some (.act par.p (B.next par.p (bview st.h))),
      { st with h := st.h ++ [FLEv.b (CLEv.act (B.next par.p (bview st.h)))]
                last := some (B.next par.p (bview st.h)) }) := by
  simp [pstep, hj]

lemma pstep2 {t j : ℕ} (hj : j % 4 = 2) (st : LSt P C X O W) :
    (∃ x, st.last = some (.send par.p x) ∧ pstep A B par t j st =
      (some (.recv par.p par.p x (t - 1)), { st with h := st.h ++ [.b (.recv par.p x)] })) ∨
    (∃ o w, st.last = some (.propose o w) ∧ pstep A B par t j st =
      (some (.dec par.p o (par.resp o w)), { st with h := st.h ++ [.b (.dec o (par.resp o w))] })) ∨
    ((∀ x, st.last ≠ some (.send par.p x)) ∧ (∀ o w, st.last ≠ some (.propose o w)) ∧
      pstep A B par t j st = (none, st)) := by
  obtain ⟨h, last, i1, i2⟩ := st
  rcases last with _ | (⟨q, x⟩ | ⟨o, w⟩ | _ | _ | _)
  all_goals simp only [pstep, hj]
  · simp
  · by_cases hq : q = par.p
    · subst hq; simp
    · simp [hq]
  · simp
  all_goals simp

lemma pstep3 {t j : ℕ} (hj : j % 4 = 3) (st : LSt P C X O W) :
    (∃ q x s, par.pendNow[st.iNow]? = some (q, x, s) ∧ pstep A B par t j st =
      (some (.recv par.p q x s), { st with h := st.h ++ [.b (.recv q x)], iNow := st.iNow + 1 })) ∨
    (par.pendNow[st.iNow]? = none ∧ Dec A par st.h ∧ ∃ q x s, par.pendLater[st.iLater]? = some (q, x, s) ∧
      pstep A B par t j st =
      (some (.recv par.p q x s), { st with h := st.h ++ [.b (.recv q x)], iLater := st.iLater + 1 })) ∨
    (par.pendNow[st.iNow]? = none ∧ (Dec A par st.h → par.pendLater[st.iLater]? = none) ∧
      pstep A B par t j st = (none, st)) := by
  simp only [pstep, hj]
  rcases hn : par.pendNow[st.iNow]? with _ | ⟨q, x, s⟩
  · by_cases hd : Dec A par st.h
    · rcases hl : par.pendLater[st.iLater]? with _ | ⟨q, x, s⟩
      · simp only [Dec] at hd
        simp [hd, -List.any_eq_true]
      · simp only [Dec] at hd
        simp [hd, -List.any_eq_true]
        exact hd
    · simp only [Dec] at hd
      simp [hd, -List.any_eq_true]
  · simp

lemma pstep_proc {t j : ℕ} {st : LSt P C X O W} {s : CStep P (Msg C) X O W}
    (h : (pstep A B par t j st).1 = some s) : s.proc = par.p := by
  rcases mod4_cases j with hj | hj | hj | hj
  · rw [pstep0 A B par hj] at h; cases h; exact upperStep_proc A par _
  · rw [pstep1 A B par hj] at h; cases h; rfl
  · rcases pstep2 A B par (t := t) hj st with ⟨x, -, he⟩ | ⟨o, w, -, he⟩ | ⟨-, -, he⟩ <;>
      rw [he] at h <;> cases h <;> rfl
  · rcases pstep3 A B par (t := t) hj st with ⟨q, x, s, -, he⟩ | ⟨-, -, q, x, s, -, he⟩ | ⟨-, -, he⟩ <;>
      rw [he] at h <;> cases h <;> rfl

lemma prun_proc {off j : ℕ} {s : CStep P (Msg C) X O W} (h : prun A B par off j = some s) :
    s.proc = par.p :=
  pstep_proc A B par h

lemma pstep_h (t j : ℕ) (st : LSt P C X O W) :
    (pstep A B par t j st).2.h = st.h ++ ((pstep A B par t j st).1.map CStep.floc).toList := by
  rcases mod4_cases j with hj | hj | hj | hj
  · rw [pstep0 A B par hj]; rfl
  · rw [pstep1 A B par hj]; rfl
  · rcases pstep2 A B par (t := t) hj st with ⟨x, -, he⟩ | ⟨o, w, -, he⟩ | ⟨-, -, he⟩ <;>
      rw [he] <;> simp [CStep.floc, CStep.bloc]
  · rcases pstep3 A B par (t := t) hj st with ⟨q, x, s, -, he⟩ | ⟨-, -, q, x, s, -, he⟩ | ⟨-, -, he⟩ <;>
      rw [he] <;> simp [CStep.floc, CStep.bloc]

lemma lst_h_succ (off j : ℕ) :
    (lst A B par (j + 1)).h = (lst A B par j).h ++ ((prun A B par off j).map CStep.floc).toList := by
  rw [lst_succ A B par off j, pstep_h]; rfl

/-- The steps of the upper layer (slot 0). -/
lemma prun_slot0 (off j : ℕ) (hj : j % 4 = 0) :
    prun A B par off j = some (upperStep A par (lst A B par j).h) := by
  rw [prun, pstep0 A B par hj]

/-- The steps of `B` (slot 1). -/
lemma prun_slot1 (off j : ℕ) (hj : j % 4 = 1) :
    prun A B par off j = some (.act par.p (B.next par.p (bview (lst A B par j).h))) := by
  rw [prun, pstep1 A B par hj]

lemma lst_last_slot2 {j : ℕ} (hj : j % 4 = 2) :
    (lst A B par j).last = some (B.next par.p (bview (lst A B par (j - 1)).h)) := by
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [lst, pstep1 A B par (by omega)]
  rfl

/-- The immediate answers of the environment (slot 2). -/
lemma prun_slot2 (off j : ℕ) (hj : j % 4 = 2) :
    prun A B par off j =
      match B.next par.p (bview (lst A B par (j - 1)).h) with
      | .send q x => if q = par.p then some (.recv par.p par.p x (off + j - 1)) else none
      | .propose o w => some (.dec par.p o (par.resp o w))
      | _ => none := by
  have hl := lst_last_slot2 A B par hj
  rw [prun]
  rcases pstep2 A B par (t := off + j) hj (lst A B par j) with
    ⟨x, h1, he⟩ | ⟨o, w, h1, he⟩ | ⟨h1, h2, he⟩
  · rw [he, Option.some_inj.1 (hl.symm.trans h1)]; simp
  · rw [he, Option.some_inj.1 (hl.symm.trans h1)]
  · rw [he]
    rcases hb : B.next par.p (bview (lst A B par (j - 1)).h) with ⟨q, x⟩ | ⟨o, w⟩ | _ | _ | _
    all_goals simp only
    · rw [hb] at hl
      split_ifs with hq
      · subst hq; exact absurd hl (h1 x)
      · rfl
    · rw [hb] at hl; exact absurd hl (h2 o w)

/-- The receptions of pending messages (slot 3). -/
lemma prun_slot3 {off j : ℕ} (hj : j % 4 = 3) {p q : P} {x : X} {s : ℕ}
    (h : prun A B par off j = some (.recv p q x s)) :
    (q, x, s) ∈ par.pendNow ∨
      ((q, x, s) ∈ par.pendLater ∧ (simView A par.p par.v par.R par.F (lst A B par j).h).any isDecL) := by
  rw [prun] at h
  rcases pstep3 A B par (t := off + j) hj (lst A B par j) with
    ⟨q', x', s', h1, he⟩ | ⟨-, hd, q', x', s', h1, he⟩ | ⟨-, -, he⟩ <;> rw [he] at h <;> cases h
  · exact Or.inl (List.mem_of_getElem? h1)
  · exact Or.inr ⟨List.mem_of_getElem? h1, hd⟩


lemma upperStep_cases (h : List (FLEv P (Msg C) X O W)) :
    upperStep A par h = .up par.p ∨ (noPend h ∧ ∃ c, upperStep A par h = .inv par.p (nInv h, c)) := by
  unfold upperStep
  split
  · split_ifs with hn
    · exact Or.inr ⟨hn, _, rfl⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

/-- Classification of the steps of a process run. -/
lemma prun_cases {off j : ℕ} {s : CStep P (Msg C) X O W} (h : prun A B par off j = some s) :
    (j % 4 = 0 ∧ s = upperStep A par (lst A B par j).h) ∨
    (j % 4 = 1 ∧ s = .act par.p (B.next par.p (bview (lst A B par j).h))) ∨
    (j % 4 = 2 ∧ ∃ x, B.next par.p (bview (lst A B par (j - 1)).h) = .send par.p x ∧
      s = .recv par.p par.p x (off + j - 1)) ∨
    (j % 4 = 2 ∧ ∃ o w, B.next par.p (bview (lst A B par (j - 1)).h) = .propose o w ∧
      s = .dec par.p o (par.resp o w)) ∨
    (j % 4 = 3 ∧ ∃ q x s', s = .recv par.p q x s' ∧ ((q, x, s') ∈ par.pendNow ∨
      ((q, x, s') ∈ par.pendLater ∧ Dec A par (lst A B par j).h))) := by
  rcases mod4_cases j with hj | hj | hj | hj
  · rw [prun_slot0 A B par off j hj] at h; cases h; exact Or.inl ⟨hj, rfl⟩
  · rw [prun_slot1 A B par off j hj] at h; cases h; exact Or.inr (Or.inl ⟨hj, rfl⟩)
  · rw [prun_slot2 A B par off j hj] at h
    rcases hb : B.next par.p (bview (lst A B par (j - 1)).h) with ⟨q, x⟩ | ⟨o, w⟩ | _ | _ | _ <;>
      rw [hb] at h <;> simp only [reduceCtorEq] at h
    · split_ifs at h with hq
      · subst hq; cases h; exact Or.inr (Or.inr (Or.inl ⟨hj, x, rfl, rfl⟩))
    · cases h; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hj, o, w, rfl, rfl⟩)))
  · rw [prun] at h
    rcases pstep3 A B par (t := off + j) hj (lst A B par j) with
      ⟨q, x, s', h1, he⟩ | ⟨-, hd, q, x, s', h1, he⟩ | ⟨-, -, he⟩ <;> rw [he] at h <;> cases h
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hj, q, x, s', rfl, Or.inl (List.mem_of_getElem? h1)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨hj, q, x, s', rfl, Or.inr ⟨List.mem_of_getElem? h1, hd⟩⟩)))

lemma simStep_dec (p : P) (v : V) (R : Set O) (F : P → Msg C → Prop) (view : List (LEv P (Msg C) V))
    (e : FLEv P (Msg C) X O W) (h : view.any isDecL = true) :
    (simStep A p v R F view e).any isDecL = true := by
  rcases e with (⟨⟨q, x⟩ | ⟨o, w⟩ | m | ⟨q, m⟩ | _⟩ | m | ⟨q, x⟩ | ⟨o, w⟩) | _
  all_goals simp only [simStep]
  all_goals (try split_ifs) <;> (try split) <;> simp_all [List.any_append]

lemma dec_append (h l : List (FLEv P (Msg C) X O W)) (hd : Dec A par h) : Dec A par (h ++ l) := by
  unfold Dec at *
  induction l using List.reverseRecOn with
  | nil => simpa using hd
  | append_singleton l e ih =>
    rw [← List.append_assoc, simView_append]
    exact simStep_dec A _ _ _ _ _ _ ih

lemma dec_mono {a b : ℕ} (hab : a ≤ b) (hd : Dec A par (lst A B par a).h) :
    Dec A par (lst A B par b).h := by
  induction b, hab using Nat.le_induction with
  | base => exact hd
  | succ b _ ih =>
    rw [lst_h_succ A B par 0 b]
    exact dec_append A par _ _ ih

/-- Number of pending messages received after `j` slots. -/
noncomputable def cnt (j : ℕ) : ℕ := (lst A B par j).iNow + (lst A B par j).iLater

/-- Invariant of the reception indices. -/
def PInv (j : ℕ) : Prop :=
  (lst A B par j).iNow ≤ par.pendNow.length ∧ (lst A B par j).iLater ≤ par.pendLater.length ∧
    (0 < (lst A B par j).iLater → (lst A B par j).iNow = par.pendNow.length)

lemma lst_idx_other {j : ℕ} (hj : j % 4 ≠ 3) :
    (lst A B par (j + 1)).iNow = (lst A B par j).iNow ∧
      (lst A B par (j + 1)).iLater = (lst A B par j).iLater := by
  rw [lst]
  rcases mod4_cases j with hj' | hj' | hj' | hj'
  · rw [pstep0 A B par hj']; exact ⟨rfl, rfl⟩
  · rw [pstep1 A B par hj']; exact ⟨rfl, rfl⟩
  · rcases pstep2 A B par (t := 0) hj' (lst A B par j) with ⟨x, -, he⟩ | ⟨o, w, -, he⟩ | ⟨-, -, he⟩ <;>
      rw [he] <;> exact ⟨rfl, rfl⟩
  · exact absurd hj' hj

lemma slot3_char {off j : ℕ} (hj : j % 4 = 3) (hinv : PInv A B par j) :
    (cnt A B par (j + 1) = cnt A B par j + 1 ∧ PInv A B par (j + 1) ∧ ∃ q x s,
      (par.pendNow ++ par.pendLater)[cnt A B par j]? = some (q, x, s) ∧
      prun A B par off j = some (.recv par.p q x s)) ∨
    (cnt A B par (j + 1) = cnt A B par j ∧ PInv A B par (j + 1) ∧ prun A B par off j = none ∧
      (cnt A B par j < (par.pendNow ++ par.pendLater).length →
        (lst A B par j).iNow < par.pendNow.length ∨ Dec A par (lst A B par j).h → False)) := by
  obtain ⟨i1, i2, i3⟩ := hinv
  unfold PInv cnt
  rw [prun, lst_succ A B par off j]
  rcases pstep3 A B par (t := off + j) hj (lst A B par j) with
    ⟨q, x, s', h1, he⟩ | ⟨h0, hd, q, x, s', h1, he⟩ | ⟨h0, h2, he⟩ <;> rw [he] <;> dsimp only
  · have hlt : (lst A B par j).iNow < par.pendNow.length := (List.getElem?_eq_some_iff.1 h1).1
    have hz : (lst A B par j).iLater = 0 := by
      by_contra hne; have := i3 (by omega); omega
    refine Or.inl ⟨by omega, ⟨by omega, by omega, by omega⟩, q, x, s', ?_, rfl⟩
    rw [hz, Nat.add_zero, List.getElem?_append_left hlt, h1]
  · have hge := List.getElem?_eq_none_iff.1 h0
    have hlt : (lst A B par j).iLater < par.pendLater.length := (List.getElem?_eq_some_iff.1 h1).1
    have heq : (lst A B par j).iNow = par.pendNow.length := by omega
    refine Or.inl ⟨by omega, ⟨by omega, by omega, fun _ => heq⟩, q, x, s', ?_, rfl⟩
    rw [List.getElem?_append_right (by omega), heq, Nat.add_sub_cancel_left, h1]
  · have hge := List.getElem?_eq_none_iff.1 h0
    refine Or.inr ⟨rfl, ⟨i1, i2, i3⟩, rfl, ?_⟩
    intro hc hor
    rcases hor with hor | hor
    · omega
    · have := List.getElem?_eq_none_iff.1 (h2 hor)
      simp only [List.length_append] at hc
      omega

lemma pinv_all (j : ℕ) : PInv A B par j := by
  induction j with
  | zero => simp [PInv, lst, LSt.init]
  | succ j ih =>
    by_cases hj : j % 4 = 3
    · rcases slot3_char A B par (off := 0) hj ih with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> exact h
    · obtain ⟨e1, e2⟩ := lst_idx_other A B par hj
      unfold PInv; rw [e1, e2]; exact ih

lemma cnt_succ (j : ℕ) : cnt A B par j ≤ cnt A B par (j + 1) ∧ cnt A B par (j + 1) ≤ cnt A B par j + 1 := by
  by_cases hj : j % 4 = 3
  · rcases slot3_char A B par (off := 0) hj (pinv_all A B par j) with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  · obtain ⟨e1, e2⟩ := lst_idx_other A B par hj
    unfold cnt; rw [e1, e2]; omega

lemma cnt_mono {a b : ℕ} (hab : a ≤ b) : cnt A B par a ≤ cnt A B par b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_refl _
  | succ b _ ih => exact ih.trans (cnt_succ A B par b).1

lemma cnt_zero : cnt A B par 0 = 0 := rfl

/-- Every pending message is eventually received (the messages of `pendLater` once the copy
has decided). -/
lemma recv_all (hdec : par.pendLater ≠ [] → ∃ j, Dec A par (lst A B par j).h) (off : ℕ) {idx : ℕ}
    (hidx : idx < (par.pendNow ++ par.pendLater).length) :
    ∃ j, j % 4 = 3 ∧ cnt A B par j = idx ∧ ∃ q x s,
      (par.pendNow ++ par.pendLater)[idx]? = some (q, x, s) ∧
      prun A B par off j = some (.recv par.p q x s) := by
  set len := (par.pendNow ++ par.pendLater).length with hlen
  have hj0 : ∃ j0, ∀ j ≥ j0, cnt A B par j < len →
      (lst A B par j).iNow < par.pendNow.length ∨ Dec A par (lst A B par j).h := by
    by_cases hl : par.pendLater = []
    · refine ⟨0, fun j _ hc => Or.inl ?_⟩
      have := (pinv_all A B par j).2.1
      simp only [hl, List.length_nil, List.append_nil] at this hlen
      unfold cnt at hc; omega
    · obtain ⟨j0, hd⟩ := hdec hl
      exact ⟨j0, fun j hj _ => Or.inr (dec_mono A B par hj hd)⟩
  obtain ⟨j0, hj0⟩ := hj0
  have hprog : ∀ r, min r len ≤ cnt A B par (4 * j0 + 3 + 4 * r) := by
    intro r
    induction r with
    | zero => simp
    | succ r ih =>
      set a := 4 * j0 + 3 + 4 * r with ha
      have hmono : cnt A B par (a + 1) ≤ cnt A B par (4 * j0 + 3 + 4 * (r + 1)) :=
        cnt_mono A B par (by omega)
      by_cases hc : len ≤ cnt A B par a
      · have := (cnt_succ A B par a).1; omega
      · rcases slot3_char A B par (off := 0) (j := a) (by omega) (pinv_all A B par a) with
          ⟨h1, -⟩ | ⟨-, -, -, h2⟩
        · omega
        · exact absurd (hj0 a (by omega) (by omega)) (fun h => h2 (by omega) h)
  have hex : ∃ j, idx < cnt A B par j := ⟨_, lt_of_lt_of_le (by omega) (hprog len)⟩
  classical
  set j1 := Nat.find hex with hj1
  have hspec : idx < cnt A B par j1 := Nat.find_spec hex
  have hpos : j1 ≠ 0 := by intro h0; rw [h0, cnt_zero] at hspec; omega
  obtain ⟨j, hj⟩ : ∃ j, j1 = j + 1 := ⟨j1 - 1, by omega⟩
  have hmin : ¬ idx < cnt A B par j := Nat.find_min hex (by omega)
  rw [hj] at hspec
  have hs := cnt_succ A B par j
  have hjm : j % 4 = 3 := by
    by_contra hne
    obtain ⟨e1, e2⟩ := lst_idx_other A B par hne
    unfold cnt at hspec hmin; rw [e1, e2] at hspec; omega
  rcases slot3_char A B par (off := off) hjm (pinv_all A B par j) with
    ⟨-, -, q, x, s, h1, h2⟩ | ⟨h1, -⟩
  · have hc : cnt A B par j = idx := by omega
    exact ⟨j, hjm, hc, q, x, s, hc ▸ h1, h2⟩
  · omega

lemma recv_idx {off j : ℕ} (hj : j % 4 = 3) {p q : P} {x : X} {s : ℕ}
    (h : prun A B par off j = some (.recv p q x s)) :
    (par.pendNow ++ par.pendLater)[cnt A B par j]? = some (q, x, s) ∧
      cnt A B par (j + 1) = cnt A B par j + 1 := by
  rcases slot3_char A B par (off := off) hj (pinv_all A B par j) with
    ⟨h1, -, q', x', s', h2, h3⟩ | ⟨-, -, h3, -⟩
  · rw [h3] at h; cases h; exact ⟨h2, h1⟩
  · rw [h3] at h; cases h

lemma nodup_map_idx {α β : Type} {l : List α} {f : α → β} (h : (l.map f).Nodup) {a b : ℕ} {x y : α}
    (ha : l[a]? = some x) (hb : l[b]? = some y) (hf : f x = f y) : a = b := by
  have ha' : (l.map f)[a]? = some (f x) := by simp [ha]
  have hb' : (l.map f)[b]? = some (f y) := by simp [hb]
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd (ha'.trans (hf ▸ hb'.symm)) (List.nodup_iff_getElem?_ne_getElem?.1 h a b hab
      (List.getElem?_eq_some_iff.1 hb').1)
  · exact hab
  · exact absurd (hb'.trans (hf ▸ ha'.symm)) (List.nodup_iff_getElem?_ne_getElem?.1 h b a hab
      (List.getElem?_eq_some_iff.1 ha').1)

lemma prun_act {off j : ℕ} {p : P} {a : BAct P (Msg C) X O W}
    (h : prun A B par off j = some (.act p a)) :
    j % 4 = 1 ∧ p = par.p ∧ a = B.next par.p (bview (lst A B par j).h) := by
  rcases prun_cases A B par h with ⟨-, he⟩ | ⟨hj, he⟩ | ⟨-, x, -, he⟩ | ⟨-, o, w, -, he⟩ |
    ⟨-, q, x, s, he, -⟩
  · rcases upperStep_cases A par (lst A B par j).h with h' | ⟨-, c, h'⟩ <;> rw [h'] at he <;> cases he
  · cases he; exact ⟨hj, rfl, rfl⟩
  · cases he
  · cases he
  · cases he

end RunStructure

/-! ## Generic facts on full local histories -/

section Generic

variable {α : CExec P (Msg C) X O W} {p : P}

omit [DecidableEq C] in
lemma mem_fhist {t : ℕ} {e : FLEv P (Msg C) X O W} :
    e ∈ fhist α p t ↔ ∃ s < t, ∃ st, α s = some st ∧ st.proc = p ∧ st.floc = e := by
  induction t with
  | zero => simp [fhist]
  | succ t ih =>
    simp only [fhist, List.mem_append, ih, Option.mem_toList, Option.bind_eq_some_iff]
    constructor
    · rintro (⟨s, hs, st, h1, h2, h3⟩ | ⟨st, h1, h2⟩)
      · exact ⟨s, by omega, st, h1, h2, h3⟩
      · split_ifs at h2 with hp
        · cases h2; exact ⟨t, by omega, st, h1, hp, rfl⟩
    · rintro ⟨s, hs, st, h1, h2, h3⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact Or.inl ⟨s, hs, st, h1, h2, h3⟩
      · exact Or.inr ⟨st, h1, by simp [h2, h3]⟩

omit [DecidableEq C] in
lemma fhist_prefix {s t : ℕ} (hst : s ≤ t) : ∃ r, fhist α p t = fhist α p s ++ r := by
  induction t, hst using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ t _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨r ++ _, by rw [fhist, hr, List.append_assoc]⟩

omit [DecidableEq P] [DecidableEq C] in
lemma floc_eq_act {st : CStep P (Msg C) X O W} {a : BAct P (Msg C) X O W}
    (h : st.floc = .b (.act a)) : st = .act st.proc a := by
  rcases st with _ | _ | _ | _ | _ <;> simp_all [CStep.floc, CStep.bloc, CStep.proc]

omit [DecidableEq P] [DecidableEq C] in
lemma nInv_append (h h' : List (FLEv P (Msg C) X O W)) : nInv (h ++ h') = nInv h + nInv h' := by
  simp [nInv, List.countP_append]

omit [DecidableEq C] in
/-- The events of the full local history between times `s` and `t`. -/
lemma fhist_split {s t : ℕ} (hst : s ≤ t) : ∃ r, fhist α p t = fhist α p s ++ r ∧
    ∀ e ∈ r, ∃ s', s ≤ s' ∧ s' < t ∧ ∃ st, α s' = some st ∧ st.proc = p ∧ st.floc = e := by
  induction t, hst using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ t hst ih =>
    obtain ⟨r, hr, hmem⟩ := ih
    refine ⟨r ++ ((α t).bind fun st => if st.proc = p then some st.floc else none).toList,
      by rw [fhist, hr, List.append_assoc], ?_⟩
    intro e he
    rcases List.mem_append.1 he with he | he
    · obtain ⟨s', h1, h2, h3⟩ := hmem e he
      exact ⟨s', h1, by omega, h3⟩
    · simp only [Option.mem_toList, Option.bind_eq_some_iff] at he
      obtain ⟨st, h1, h2⟩ := he
      split_ifs at h2 with hp
      cases h2
      exact ⟨t, hst, by omega, st, h1, hp, rfl⟩

/-- Well-formedness of the upper layer, from the shape of its invocations: it invokes with
identifier `nInv h` when every earlier invocation has been followed by its return. -/
lemma invWF_of
    (hinv : ∀ t p m, α t = some (.inv p m) →
      (∃ c, m = (nInv (fhist α p t), c)) ∧ noPend (fhist α p t)) :
    ∀ (t : ℕ) (p : P) (m : Msg C), α t = some (.inv p m) → ∀ s < t, ∀ m',
      α s = some (.inv p m') → m' ≠ m ∧ ∃ s', s < s' ∧ s' < t ∧ α s' = some (.act p (.ret m')) := by
  intro t p m ht s hst m' hs
  have h1 : fhist α p (s + 1) = fhist α p s ++ [.b (.inv m')] := by
    rw [fhist, hs]; simp [CStep.proc, CStep.floc, CStep.bloc]
  obtain ⟨r, hr, hmem⟩ := fhist_split (α := α) (p := p) (Nat.succ_le_of_lt hst)
  rw [h1, List.append_assoc, List.singleton_append] at hr
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨c, rfl⟩, -⟩ := hinv t p m ht
    obtain ⟨⟨c', rfl⟩, -⟩ := hinv s p m' hs
    rw [hr, nInv_append, show FLEv.b (.inv (nInv (fhist α p s), c')) :: r =
      [FLEv.b (.inv (nInv (fhist α p s), c'))] ++ r from rfl, nInv_append]
    intro heq
    have := congrArg Prod.fst heq
    simp [nInv] at this
  · have hret := (hinv t p m ht).2 _ _ m' hr
    obtain ⟨s', h2, h3, st, h4, h5, h6⟩ := hmem _ hret
    have hst' := floc_eq_act h6
    rw [h5] at hst'
    subst hst'
    exact ⟨s', by omega, h3, h4⟩

end Generic

/-! ## Concatenation -/

/-- The offset of segment `i`. -/
def segOff {m : ℕ} (L : Fin m → ℕ) (i : Fin m) : ℕ :=
  ∑ j ∈ Finset.univ.filter (· < i), L j

/-- The end of the finite segments. -/
def segEnd {m : ℕ} (L : Fin m → ℕ) : ℕ :=
  ∑ j, L j

/-- The concatenation of the runs of `(pars i).p` for `L i` slots each, then of `fin`
forever. -/
noncomputable def catRun {m : ℕ} (pars : Fin m → RunPar P C V X O W) (L : Fin m → ℕ)
    (fin : RunPar P C V X O W) : CExec P (Msg C) X O W := fun t =>
  if h : ∃ i, segOff L i ≤ t ∧ t < segOff L i + L i then
    prun A B (pars h.choose) (segOff L h.choose) (t - segOff L h.choose)
  else prun A B fin (segEnd L) (t - segEnd L)

section Cat

variable {m : ℕ} (pars : Fin m → RunPar P C V X O W) (L : Fin m → ℕ) (fin : RunPar P C V X O W)

lemma segOff_add_eq (i : Fin m) :
    segOff L i + L i = ∑ j ∈ Finset.univ.filter (· ≤ i), L j := by
  have : Finset.univ.filter (· ≤ i) = insert i (Finset.univ.filter (· < i)) := by
    ext k; simp [le_iff_lt_or_eq, or_comm]
  rw [this, Finset.sum_insert (by simp), add_comm, segOff]

lemma segOff_add_le {i j : Fin m} (hij : i < j) : segOff L i + L i ≤ segOff L j := by
  rw [segOff_add_eq, segOff]
  apply Finset.sum_le_sum_of_subset
  intro k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; intro hk
  exact lt_of_le_of_lt hk hij

lemma segOff_add_le_end (i : Fin m) : segOff L i + L i ≤ segEnd L := by
  rw [segOff_add_eq, segEnd]
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

lemma segOff_succ {n : ℕ} (h : n + 1 < m) :
    segOff L ⟨n + 1, h⟩ = segOff L ⟨n, by omega⟩ + L ⟨n, by omega⟩ := by
  rw [segOff_add_eq, segOff]
  congr 1

lemma segOff_zero (h : 0 < m) : segOff L ⟨0, h⟩ = 0 := by
  rw [segOff]; apply Finset.sum_eq_zero; intro k; simp [Fin.lt_def]

lemma segEnd_eq (h : 0 < m) : segEnd L = segOff L ⟨m - 1, by omega⟩ + L ⟨m - 1, by omega⟩ := by
  rw [segOff_add_eq, segEnd]
  congr 1; ext k; simp [Fin.le_def]; omega

lemma exists_seg_of_lt_end {t : ℕ} (ht : t < segEnd L) : ∃ i, segOff L i ≤ t ∧ t < segOff L i + L i := by
  by_contra hne
  push Not at hne
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [segEnd] at ht
  have key : ∀ n (h : n < m), segOff L ⟨n, h⟩ + L ⟨n, h⟩ ≤ t := by
    intro n
    induction n with
    | zero => intro h; exact hne _ (by rw [segOff_zero L h]; omega)
    | succ n ih =>
      intro h
      exact hne _ (by rw [segOff_succ L h]; exact ih (by omega))
  have := key (m - 1) (by omega)
  rw [← segEnd_eq L hm] at this
  omega

lemma seg_unique {i i' : Fin m} {t : ℕ} (h1 : segOff L i ≤ t) (h2 : t < segOff L i + L i)
    (h1' : segOff L i' ≤ t) (h2' : t < segOff L i' + L i') : i = i' := by
  rcases lt_trichotomy i i' with h | h | h
  · have := segOff_add_le L h; omega
  · exact h
  · have := segOff_add_le L h; omega

lemma catRun_seg {i : Fin m} {t : ℕ} (h1 : segOff L i ≤ t) (h2 : t < segOff L i + L i) :
    catRun A B pars L fin t = prun A B (pars i) (segOff L i) (t - segOff L i) := by
  have he : ∃ i, segOff L i ≤ t ∧ t < segOff L i + L i := ⟨i, h1, h2⟩
  rw [catRun, dite_eq_left_of_eq_true (eq_true he)]
  have := seg_unique L he.choose_spec.1 he.choose_spec.2 h1 h2
  rw [this]

lemma catRun_fin {t : ℕ} (h : segEnd L ≤ t) :
    catRun A B pars L fin t = prun A B fin (segEnd L) (t - segEnd L) := by
  have hne : ¬ ∃ i, segOff L i ≤ t ∧ t < segOff L i + L i := by
    rintro ⟨i, -, h2⟩
    have := segOff_add_le_end L i
    omega
  rw [catRun, dite_eq_right_of_eq_false (eq_false hne)]

/-- The processes of the segments and the final process are pairwise distinct. -/
def Distinct : Prop :=
  Function.Injective (fun i => (pars i).p) ∧ ∀ i, (pars i).p ≠ fin.p

/-- The full local history of the process of segment `i` in the concatenation. -/
lemma catRun_proc' {t : ℕ} {s : CStep P (Msg C) X O W} (h : catRun A B pars L fin t = some s) :
    (∃ i, segOff L i ≤ t ∧ t < segOff L i + L i ∧ s.proc = (pars i).p) ∨
      (segEnd L ≤ t ∧ s.proc = fin.p) := by
  by_cases ht : t < segEnd L
  · obtain ⟨i, h1, h2⟩ := exists_seg_of_lt_end L ht
    rw [catRun_seg A B pars L fin h1 h2] at h
    exact Or.inl ⟨i, h1, h2, prun_proc A B _ h⟩
  · rw [catRun_fin A B pars L fin (by omega)] at h
    exact Or.inr ⟨by omega, prun_proc A B _ h⟩

omit [DecidableEq C] in
lemma fhist_eq_nil {α : CExec P (Msg C) X O W} {p : P} {t : ℕ}
    (h : ∀ t' < t, ∀ s, α t' = some s → s.proc ≠ p) : fhist α p t = [] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [fhist, ih (fun t' ht' => h t' (by omega))]
    rcases hs : α t with _ | s
    · rfl
    · simp [h t (by omega) s hs]

omit [DecidableEq C] in
lemma fhist_succ_of {α : CExec P (Msg C) X O W} {p : P} {t : ℕ}
    (h : ∀ s, α t = some s → s.proc = p) :
    fhist α p (t + 1) = fhist α p t ++ ((α t).map CStep.floc).toList := by
  rw [fhist]
  rcases hs : α t with _ | s
  · rfl
  · simp [h s hs]

lemma fhist_catRun_seg (hd : Distinct pars fin) (i : Fin m) {j : ℕ} (hj : j ≤ L i) :
    fhist (catRun A B pars L fin) (pars i).p (segOff L i + j) = (lst A B (pars i) j).h := by
  induction j with
  | zero =>
    apply fhist_eq_nil
    intro t' ht' s hs heq
    rcases catRun_proc' A B pars L fin hs with ⟨i', h1, h2, h3⟩ | ⟨h1, -⟩
    · have hii : i' = i := hd.1 (h3.symm.trans heq)
      subst hii; omega
    · have := segOff_add_le_end L i; omega
  | succ j ih =>
    rw [← add_assoc, fhist_succ_of, ih (by omega), lst_h_succ A B _ (segOff L i),
      catRun_seg A B pars L fin (i := i) (by omega) (by omega), Nat.add_sub_cancel_left]
    intro s hs
    rw [catRun_seg A B pars L fin (i := i) (by omega) (by omega)] at hs
    exact prun_proc A B _ hs

/-- The full local history of the final process. -/
lemma fhist_catRun_fin (hd : Distinct pars fin) (j : ℕ) :
    fhist (catRun A B pars L fin) fin.p (segEnd L + j) = (lst A B fin j).h := by
  induction j with
  | zero =>
    apply fhist_eq_nil
    intro t' ht' s hs heq
    rcases catRun_proc' A B pars L fin hs with ⟨i', h1, h2, h3⟩ | ⟨h1, -⟩
    · exact hd.2 i' (h3.symm.trans heq)
    · omega
  | succ j ih =>
    rw [← add_assoc, fhist_succ_of, ih, lst_h_succ A B _ (segEnd L),
      catRun_fin A B pars L fin (by omega), Nat.add_sub_cancel_left]
    intro s hs
    rw [catRun_fin A B pars L fin (by omega)] at hs
    exact prun_proc A B _ hs

/-- The process of segment `i` takes no step outside its segment. -/
lemma catRun_proc_seg (hd : Distinct pars fin) {i : Fin m} {t : ℕ}
    {s : CStep P (Msg C) X O W} (h : catRun A B pars L fin t = some s) (hs : s.proc = (pars i).p) :
    segOff L i ≤ t ∧ t < segOff L i + L i := by
  rcases catRun_proc' A B pars L fin h with ⟨i', h1, h2, h3⟩ | ⟨-, h3⟩
  · have hii : i' = i := hd.1 (h3.symm.trans hs)
    subst hii; exact ⟨h1, h2⟩
  · exact absurd (h3.symm.trans hs) (hd.2 i).symm

/-- The final process takes no step before the end of the segments. -/
lemma catRun_proc_fin (hd : Distinct pars fin) {t : ℕ}
    {s : CStep P (Msg C) X O W} (h : catRun A B pars L fin t = some s) (hs : s.proc = fin.p) :
    segEnd L ≤ t := by
  rcases catRun_proc' A B pars L fin h with ⟨i', -, -, h3⟩ | ⟨h1, -⟩
  · exact absurd (h3.symm.trans hs) (hd.2 i')
  · exact h1


/-- Every time lies in the run of some process of the concatenation. -/
lemma catRun_loc (hd : Distinct pars fin) (t : ℕ) : ∃ par off j, t = off + j ∧
    catRun A B pars L fin t = prun A B par off j ∧
    (1 ≤ j → catRun A B pars L fin (t - 1) = prun A B par off (j - 1)) ∧
    fhist (catRun A B pars L fin) par.p t = (lst A B par j).h ∧
    ((∃ i, par = pars i) ∨ (par = fin ∧ off = segEnd L)) := by
  by_cases ht : t < segEnd L
  · obtain ⟨i, h1, h2⟩ := exists_seg_of_lt_end L ht
    refine ⟨pars i, segOff L i, t - segOff L i, by omega, catRun_seg A B pars L fin h1 h2,
      fun hj => ?_, ?_, Or.inl ⟨i, rfl⟩⟩
    · rw [catRun_seg A B pars L fin (i := i) (by omega) (by omega)]; congr 1; omega
    · have := fhist_catRun_seg A B pars L fin hd i (j := t - segOff L i) (by omega)
      rwa [Nat.add_sub_cancel' h1] at this
  · refine ⟨fin, segEnd L, t - segEnd L, by omega, catRun_fin A B pars L fin (by omega),
      fun hj => ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
    · rw [catRun_fin A B pars L fin (by omega)]; congr 1; omega
    · have := fhist_catRun_fin A B pars L fin hd (t - segEnd L)
      rwa [Nat.add_sub_cancel' (by omega)] at this

lemma catRun_cons (hd : Distinct pars fin) (t : ℕ) (p : P) (a : BAct P (Msg C) X O W)
    (h : catRun A B pars L fin t = some (.act p a)) :
    a = B.next p (bhist (catRun A B pars L fin) p t) := by
  obtain ⟨par, off, j, rfl, hstep, -, hh, -⟩ := catRun_loc A B pars L fin hd t
  rw [hstep] at h
  rcases prun_cases A B par h with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, x, -, he⟩ | ⟨-, o, w, -, he⟩ |
    ⟨-, q, x, s, he, -⟩
  · rcases upperStep_cases A par (lst A B par j).h with h' | ⟨-, c, h'⟩ <;> rw [h'] at he <;> cases he
  · cases he; rw [bhist_eq_bview, hh]
  · cases he
  · cases he
  · cases he

lemma catRun_inv (hd : Distinct pars fin) (t : ℕ) (p : P) (m : Msg C)
    (h : catRun A B pars L fin t = some (.inv p m)) :
    (∃ c, m = (nInv (fhist (catRun A B pars L fin) p t), c)) ∧
      noPend (fhist (catRun A B pars L fin) p t) := by
  obtain ⟨par, off, j, rfl, hstep, -, hh, -⟩ := catRun_loc A B pars L fin hd t
  rw [hstep] at h
  rcases prun_cases A B par h with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, x, -, he⟩ | ⟨-, o, w, -, he⟩ |
    ⟨-, q, x, s, he, -⟩
  · rcases upperStep_cases A par (lst A B par j).h with h' | ⟨hn, c, h'⟩ <;> rw [h'] at he <;>
      cases he
    rw [hh]; exact ⟨⟨c, rfl⟩, hn⟩
  · cases he
  · cases he
  · cases he
  · cases he

lemma catRun_dec (hd : Distinct pars fin) (hresp : ∀ i o w, (pars i).resp o w = w)
    (t : ℕ) (p : P) (o : O) (w : W) (h : catRun A B pars L fin t = some (.dec p o w)) :
    1 ≤ t ∧ ∃ w0, catRun A B pars L fin (t - 1) = some (.act p (.propose o w0)) ∧
      (w = w0 ∨ (p = fin.p ∧ segEnd L ≤ t - 1 ∧ w = fin.resp o w0)) := by
  obtain ⟨par, off, j, rfl, hstep, hprev, -, hkind⟩ := catRun_loc A B pars L fin hd t
  rw [hstep] at h
  rcases prun_cases A B par h with ⟨-, he⟩ | ⟨-, he⟩ | ⟨-, x, -, he⟩ | ⟨hj, o', w0, hb, he⟩ |
    ⟨-, q, x, s, he, -⟩
  · rcases upperStep_cases A par (lst A B par j).h with h' | ⟨-, c, h'⟩ <;> rw [h'] at he <;> cases he
  · cases he
  · cases he
  · cases he
    have hj1 : 1 ≤ j := by omega
    refine ⟨by omega, w0, ?_, ?_⟩
    · rw [hprev hj1, prun_slot1 A B par off (j - 1) (by omega), hb]
    · rcases hkind with ⟨i, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (hresp i o w0)
      · exact Or.inr ⟨rfl, by omega, rfl⟩
  · cases he

lemma catRun_recv (hd : Distinct pars fin) (hpend : ∀ i, (pars i).pendNow = [] ∧ (pars i).pendLater = [])
    (t : ℕ) (p q : P) (x : X) (s : ℕ) (h : catRun A B pars L fin t = some (.recv p q x s)) :
    (t = s + 1 ∧ q = p ∧ catRun A B pars L fin s = some (.act p (.send p x)) ∧
      (p = fin.p → segEnd L ≤ s)) ∨
    (p = fin.p ∧ segEnd L ≤ t ∧ (t - segEnd L) % 4 = 3 ∧
      prun A B fin (segEnd L) (t - segEnd L) = some (.recv p q x s) ∧
      (q, x, s) ∈ fin.pendNow ++ fin.pendLater) := by
  obtain ⟨par, off, j, rfl, hstep, hprev, -, hkind⟩ := catRun_loc A B pars L fin hd t
  rw [hstep] at h
  rcases prun_cases A B par h with ⟨-, he⟩ | ⟨-, he⟩ | ⟨hj, x', hb, he⟩ | ⟨-, o', w0, -, he⟩ |
    ⟨hj, q', x', s', he, hmem⟩
  · rcases upperStep_cases A par (lst A B par j).h with h' | ⟨-, c, h'⟩ <;> rw [h'] at he <;> cases he
  · cases he
  · cases he
    have hj1 : 1 ≤ j := by omega
    refine Or.inl ⟨by omega, rfl, ?_, ?_⟩
    · have := hprev hj1
      rw [this, prun_slot1 A B par off (j - 1) (by omega), hb]
    · intro hp
      rcases hkind with ⟨i, rfl⟩ | ⟨rfl, rfl⟩
      · exact absurd hp (hd.2 i)
      · omega
  · cases he
  · cases he
    rcases hkind with ⟨i, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨h1, h2⟩ := hpend i
      rw [h1, h2] at hmem; simp at hmem
    · refine Or.inr ⟨rfl, by omega, by rwa [Nat.add_sub_cancel_left], ?_, ?_⟩
      · rw [Nat.add_sub_cancel_left]; exact h
      · rcases hmem with hm | ⟨hm, -⟩
        · exact List.mem_append_left _ hm
        · exact List.mem_append_right _ hm


/-- Admissibility of a concatenation, given the well-formedness of its upper layer. -/
theorem catRun_adm_of_invWF {k : ℕ} (hB : B.OneShot) (hd : Distinct pars fin)
    (hresp : ∀ i o w, (pars i).resp o w = w)
    (hpend : ∀ i, (pars i).pendNow = [] ∧ (pars i).pendLater = [])
    (hfresp : ∀ o w, fin.resp o w = w ∨
      ∃ t < segEnd L, ∃ q, catRun A B pars L fin t = some (.act q (.propose o (fin.resp o w))))
    (hfpend1 : ∀ q x s, (q, x, s) ∈ fin.pendNow ++ fin.pendLater ↔
      s < segEnd L ∧ catRun A B pars L fin s = some (.act q (.send fin.p x)))
    (hfpend2 : ((fin.pendNow ++ fin.pendLater).map fun e => e.2.2).Nodup)
    (hfdec : fin.pendLater ≠ [] →
      ∃ j, (simView A fin.p fin.v fin.R fin.F (lst A B fin j).h).any isDecL)
    (hagree : ∀ (o : O) (f : Fin (k + 1) → W), Function.Injective f →
      ¬ ∀ i, ∃ t p, catRun A B pars L fin t = some (.dec p o (f i)))
    (hw : ∀ (t : ℕ) (p : P) (m : Msg C), catRun A B pars L fin t = some (.inv p m) → ∀ s < t, ∀ m',
      catRun A B pars L fin s = some (.inv p m') →
        m' ≠ m ∧ ∃ s', s < s' ∧ s' < t ∧ catRun A B pars L fin s' = some (.act p (.ret m'))) :
    Adm B k {fin.p} (catRun A B pars L fin) := by
  have hfinE : ∀ j, catRun A B pars L fin (segEnd L + j) = prun A B fin (segEnd L) j := by
    intro j; rw [catRun_fin A B pars L fin (by omega), Nat.add_sub_cancel_left]
  have hcons := catRun_cons A B pars L fin hd
  refine ⟨hcons, ?fair, ?crash, ?srValid, ?srNoDup, ?srTerm, ?ksaPend, ?ksaOnce, ?ksaValid,
    hagree, ?ksaTerm, hw⟩
  case fair =>
    intro p hp t
    rw [Set.mem_singleton_iff] at hp; subst hp
    exact ⟨segEnd L + (4 * t + 1), by omega, _, by
      rw [hfinE, prun_slot1 A B fin _ _ (by omega)]⟩
  case crash =>
    intro p hp
    by_cases hex : ∃ i, (pars i).p = p
    · obtain ⟨i, rfl⟩ := hex
      refine ⟨segOff L i + L i, fun t ht s hs hsp => ?_⟩
      have := catRun_proc_seg A B pars L fin hd hs hsp
      omega
    · refine ⟨0, fun t _ s hs hsp => ?_⟩
      rcases catRun_proc' A B pars L fin hs with ⟨i, -, -, h3⟩ | ⟨-, h3⟩
      · exact hex ⟨i, h3.symm.trans hsp⟩
      · exact hp (Set.mem_singleton_iff.2 (hsp.symm.trans h3))
  case srValid =>
    intro t p q x s h
    rcases catRun_recv A B pars L fin hd hpend t p q x s h with ⟨rfl, rfl, h1, -⟩ |
      ⟨rfl, ht, -, -, hmem⟩
    · exact ⟨by omega, h1⟩
    · obtain ⟨h1, h2⟩ := (hfpend1 q x s).1 hmem
      exact ⟨by omega, h2⟩
  case srNoDup =>
    intro t t' p q x x' s h h'
    rcases catRun_recv A B pars L fin hd hpend t p q x s h with ⟨rfl, -, -, hA⟩ |
      ⟨hp, ht, hj, hpr, hmem⟩ <;>
    rcases catRun_recv A B pars L fin hd hpend t' p q x' s h' with ⟨ht', -, -, hA'⟩ |
      ⟨hp', ht', hj', hpr', hmem'⟩
    · omega
    · have := hA hp'; have := ((hfpend1 q x' s).1 hmem').1; omega
    · have := hA' hp; have := ((hfpend1 q x s).1 hmem).1; omega
    · obtain ⟨i1, c1⟩ := recv_idx A B fin hj hpr
      obtain ⟨i2, c2⟩ := recv_idx A B fin hj' hpr'
      have heq := nodup_map_idx hfpend2 i1 i2 rfl
      rcases lt_trichotomy (t - segEnd L) (t' - segEnd L) with hlt | hlt | hlt
      · have := cnt_mono A B fin (a := t - segEnd L + 1) (b := t' - segEnd L) (by omega); omega
      · omega
      · have := cnt_mono A B fin (a := t' - segEnd L + 1) (b := t - segEnd L) (by omega); omega
  case srTerm =>
    intro p hp s q x h
    rw [Set.mem_singleton_iff] at hp; subst hp
    by_cases hs : s < segEnd L
    · have hmem := (hfpend1 q x s).2 ⟨hs, h⟩
      obtain ⟨idx, hidx⟩ := List.mem_iff_getElem?.1 hmem
      obtain ⟨j, -, -, q', x', s', h1, h2⟩ :=
        recv_all A B fin hfdec (segEnd L) (List.getElem?_eq_some_iff.1 hidx).1
      rw [hidx] at h1; cases h1
      exact ⟨segEnd L + j, by rw [hfinE]; exact h2⟩
    · obtain ⟨j, rfl⟩ : ∃ j, s = segEnd L + j := ⟨s - segEnd L, by omega⟩
      rw [hfinE] at h
      obtain ⟨hj, rfl, hb⟩ := prun_act A B fin h
      refine ⟨segEnd L + (j + 1), ?_⟩
      rw [hfinE, prun_slot2 A B fin _ _ (by omega), Nat.add_sub_cancel, ← hb]
      simp
  case ksaPend =>
    intro t p o w h
    obtain ⟨h1, w0, h2, -⟩ := catRun_dec A B pars L fin hd hresp t p o w h
    exact ⟨t - 1, by omega, w0, h2⟩
  case ksaOnce =>
    intro t t' p o w w' h h'
    obtain ⟨h1, w0, h2, -⟩ := catRun_dec A B pars L fin hd hresp t p o w h
    obtain ⟨h1', w0', h2', -⟩ := catRun_dec A B pars L fin hd hresp t' p o w' h'
    by_contra hne
    have key : ∀ a b wa wb, a < b → catRun A B pars L fin a = some (.act p (.propose o wa)) →
        catRun A B pars L fin b = some (.act p (.propose o wb)) → False := by
      intro a b wa wb hab ha hb
      have := hcons b p _ hb
      exact hB p _ o wb this.symm wa (mem_bhist.2 ⟨a, hab, _, ha, rfl, rfl⟩)
    rcases lt_trichotomy (t - 1) (t' - 1) with hlt | hlt | hlt
    · exact key _ _ _ _ hlt h2 h2'
    · omega
    · exact key _ _ _ _ hlt h2' h2
  case ksaValid =>
    intro t p o w h
    obtain ⟨h1, w0, h2, hw0⟩ := catRun_dec A B pars L fin hd hresp t p o w h
    rcases hw0 with rfl | ⟨rfl, hle, rfl⟩
    · exact ⟨t - 1, by omega, p, h2⟩
    · rcases hfresp o w0 with he | ⟨t0, ht0, q, hq⟩
      · rw [he]; exact ⟨t - 1, by omega, _, h2⟩
      · exact ⟨t0, by omega, q, hq⟩
  case ksaTerm =>
    intro p hp s o w h
    rw [Set.mem_singleton_iff] at hp; subst hp
    have hs := catRun_proc_fin A B pars L fin hd h rfl
    obtain ⟨j, rfl⟩ : ∃ j, s = segEnd L + j := ⟨s - segEnd L, by omega⟩
    rw [hfinE] at h
    obtain ⟨hj, -, hb⟩ := prun_act A B fin h
    refine ⟨segEnd L + (j + 1), by omega, fin.resp o w, ?_⟩
    rw [hfinE, prun_slot2 A B fin _ _ (by omega), Nat.add_sub_cancel, ← hb]

/-- **Admissibility of a concatenation.** The hypotheses: the processes are distinct; the k-SA
objects answer their own proposal to the processes of the segments, and to the final process
either its own proposal or a value proposed to the same object during the segments; the
segments have no pending messages; the pending messages of the final process are exactly the
messages sent to it during the segments, without repetition; if some must wait for the final
copy to decide, then it decides; and k-SA agreement holds. -/
theorem catRun_adm {k : ℕ} (hk : 1 ≤ k) (hB : B.OneShot) (hd : Distinct pars fin)
    (hresp : ∀ i o w, (pars i).resp o w = w)
    (hpend : ∀ i, (pars i).pendNow = [] ∧ (pars i).pendLater = [])
    (hfresp : ∀ o w, fin.resp o w = w ∨
      ∃ t < segEnd L, ∃ q, catRun A B pars L fin t = some (.act q (.propose o (fin.resp o w))))
    (hfpend1 : ∀ q x s, (q, x, s) ∈ fin.pendNow ++ fin.pendLater ↔
      s < segEnd L ∧ catRun A B pars L fin s = some (.act q (.send fin.p x)))
    (hfpend2 : ((fin.pendNow ++ fin.pendLater).map fun e => e.2.2).Nodup)
    (hfdec : fin.pendLater ≠ [] →
      ∃ j, (simView A fin.p fin.v fin.R fin.F (lst A B fin j).h).any isDecL)
    (hagree : ∀ (o : O) (f : Fin (k + 1) → W), Function.Injective f →
      ¬ ∀ i, ∃ t p, catRun A B pars L fin t = some (.dec p o (f i))) :
    Adm B k {fin.p} (catRun A B pars L fin) := by
  have _hk := hk
  exact catRun_adm_of_invWF A B pars L fin hB hd hresp hpend hfresp hfpend1 hfpend2 hfdec hagree
    (invWF_of (catRun_inv A B pars L fin hd))

end Cat

end Podc.NoBroadcastKSA.Camp
