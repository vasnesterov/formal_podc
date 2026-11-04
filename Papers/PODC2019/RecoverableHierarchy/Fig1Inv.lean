import Papers.PODC2019.RecoverableHierarchy.Fig1Alg

/-!
# Figure 1 of Golab (PODC 2019): the invariant

An invariant `Inv` of the abstract view `St` (preserved by every event: `Inv.sstep`), and the
"forced value" predicate `Good s v`:
* it holds for the value of every return state (`good_of_ret`),
* it is preserved by every event (`Good.sstep`), so it holds at the end of an execution for every
  value output at some point of it (also by incarnations that crashed afterwards),
* it determines `v` (`Good.unique`), and `v` is an input (`Good.valid`).

`Good s v` has three cases, matching the paper's case analysis:
(a) `D = v` (decided through `C` and recorded at line 5; Lemma 9);
(b) exactly one proposal `P[j] = v` is recorded and the other process cannot record its proposal
    any more (Lemma 10, Case 2);
(c) both proposals are recorded, `D = ⊥` and nobody is in lines 3–5, so `D` stays `⊥` forever
    and every return is at line 14 (Lemma 10, Case 3).
-/

namespace Podc.RecoverableHierarchy.Fig1

open PC

/-- The local part of the invariant for process `k` at program counter `c`. -/
def LP (s : St) (k : Fin 2) : PC → Prop
  | .l2a => True
  | .l2b a => a = s.P k
  | .l3 => s.P k = none
  | .l4 => s.P k ≠ none
  | .l5 d => s.P k ≠ none ∧ s.C = some d
  | .l7 => s.P k ≠ none ∨ s.P (oth k) ≠ none
  | .l9a => (s.P k ≠ none ∨ s.P (oth k) ≠ none) ∧ (s.P k ≠ none → s.D = none)
  | .l9b a => a = s.P k ∧ (s.P k ≠ none ∨ s.P (oth k) ≠ none) ∧ (s.P k ≠ none → s.D = none)
  | .l11a => s.P (oth k) ≠ none ∧ (s.P k ≠ none → s.D = none)
  | .l11b a => a = s.P k ∧ s.P (oth k) ≠ none ∧ (s.P k ≠ none → s.D = none)
  | .l13 => s.P k ≠ none ∧ s.P (oth k) ≠ none ∧ s.D = none
  | .r6 d => s.D = some d
  | .r8 d => s.D = some d
  | .r10 d => s.P k = some d ∧ s.P (oth k) = none
  | .r12 d => s.P k = none ∧ s.P (oth k) = some d
  | .r14 d => s.P 0 = some d ∧ s.P 1 ≠ none ∧ s.D = none

/-- The invariant. `quiet`: a process outside lines 3–6 whose proposal is recorded is in a later
epoch than the one in which proposals were recorded, so nobody is in lines 3–5. -/
structure Inv (s : St) : Prop where
  px : ∀ k a, s.P k = some a → a = s.x k
  cP : ∀ w, s.C = some w → ∃ k, s.P k = some w
  dC : ∀ w, s.D = some w → s.C = some w
  quiet : ∀ k, (s.pc k).idle → s.P k ≠ none → ∀ j, ¬ (s.pc j).busy
  loc : ∀ k, LP s k (s.pc k)

/-- `LP` does not depend on the program counters. -/
@[simp] lemma LP_pc (s : St) (f : Fin 2 → PC) (k : Fin 2) (c : PC) :
    LP { s with pc := f } k c ↔ LP s k c := Iff.rfl

/-- The initial view. -/
def s0 (x : Fin 2 → Bool) : St := ⟨fun _ => .l2a, fun _ => none, none, none, x⟩

lemma inv_s0 (x : Fin 2 → Bool) : Inv (s0 x) where
  px := by simp [s0]
  cP := by simp [s0]
  dC := by simp [s0]
  quiet := by simp [s0, busy]
  loc := by simp [s0, LP]

variable {s : St}

lemma Inv.loc' (h : Inv s) {k : Fin 2} {c : PC} (hc : s.pc k = c) : LP s k c := hc ▸ h.loc k

/-- If some process is in lines 3–5, every idle process has an unrecorded proposal. -/
lemma Inv.idle_none (h : Inv s) {m : Fin 2} (hm : (s.pc m).busy) {k : Fin 2}
    (hk : (s.pc k).idle) : s.P k = none := by
  by_contra hP
  exact h.quiet k hk hP m hm

/-- Steps that only read (memory unchanged, the process stays outside lines 3–6). -/
lemma Inv.read (h : Inv s) {m : Fin 2} {c : PC} (hi : (s.pc m).idle) (hc : ¬ c.busy)
    (hl : LP s m c) : Inv { s with pc := Function.update s.pc m c } where
  px := h.px
  cP := h.cP
  dC := h.dC
  quiet k hk hP j := by
    have hall : ∀ j, ¬ (s.pc j).busy := by
      by_cases hkm : k = m
      · subst hkm; exact h.quiet k hi hP
      · exact h.quiet k (by simpa [Function.update_of_ne hkm] using hk) hP
    by_cases hjm : j = m
    · subst hjm; simpa using hc
    · simpa [Function.update_of_ne hjm] using hall j
  loc k := by
    by_cases hkm : k = m
    · subst hkm; simpa using hl
    · simpa [Function.update_of_ne hkm] using h.loc k

lemma Inv.crash (h : Inv s) : Inv { s with pc := fun _ => .l2a } where
  px := h.px
  cP := h.cP
  dC := h.dC
  quiet := by simp [busy]
  loc := by simp [LP]


/-! ### Transfer of `LP` to the other process when memory changes -/

/-- Process `oth k` records its proposal (line 3) while `k` is idle with `P k = ⊥` or busy. -/
lemma LP_writeP {s s' : St} {k : Fin 2} {c : PC} {b : Bool} (hidle : c.idle → s.P k = none)
    (hPo : s.P (oth k) = none) (hP : s'.P k = s.P k) (hP' : s'.P (oth k) = some b)
    (hD : s'.D = s.D) (hC : s'.C = s.C) (h : LP s k c) : LP s' k c := by
  fin_cases k <;> cases c <;> simp_all [LP, idle]

/-- Process `oth k` writes `C` (line 4). -/
lemma LP_writeC {s s' : St} {k : Fin 2} {c : PC} (hC : ∀ d, s.C = some d → s'.C = some d)
    (hP : s'.P = s.P) (hD : s'.D = s.D) (h : LP s k c) : LP s' k c := by
  cases c <;> simp only [LP, hP, hD] at h ⊢ <;> first | exact h | exact ⟨h.1, hC _ h.2⟩

/-- Process `oth k` writes `D := d` (line 5). -/
lemma LP_writeD {s s' : St} {k : Fin 2} {c : PC} {d : Bool} (hidle : c.idle → s.P k = none)
    (hD : s.D = none ∨ s.D = some d) (hP : s'.P = s.P) (hD' : s'.D = some d) (hC : s'.C = s.C)
    (h : LP s k c) : LP s' k c := by
  fin_cases k <;> cases c <;> simp_all [LP, idle]


/-! ### Preservation -/

/-- Line 2 succeeds: `p_m` moves to line 3. -/
lemma Inv.enter3 (h : Inv s) {m : Fin 2} (hPm : s.P m = none) (hPo : s.P (oth m) = none) :
    Inv { s with pc := Function.update s.pc m .l3 } where
  px := h.px
  cP := h.cP
  dC := h.dC
  quiet k hk hP := by
    by_cases hkm : k = m
    · subst hkm; simp [idle] at hk
    · rw [eq_oth_of_ne hkm] at hP; exact absurd hPo hP
  loc k := by
    by_cases hkm : k = m
    · subst hkm; simpa [LP] using hPm
    · simpa [Function.update_of_ne hkm] using h.loc k

/-- Line 3: `P[m] := v`. -/
lemma Inv.write3 (h : Inv s) {m : Fin 2} (hpc : s.pc m = .l3) :
    Inv { s with pc := Function.update s.pc m .l4,
                 P := Function.update s.P m (some (s.x m)) } where
  px k a hk := by
    by_cases hkm : k = m
    · subst hkm; simp at hk; simp [hk]
    · simp [Function.update_of_ne hkm] at hk; exact h.px k a hk
  cP w hw := by
    obtain ⟨k, hk⟩ := h.cP w hw
    have hPm : s.P m = none := h.loc' hpc
    have hkm : k ≠ m := by rintro rfl; simp_all
    exact ⟨k, by simpa [Function.update_of_ne hkm] using hk⟩
  dC := h.dC
  quiet k hk hP := by
    by_cases hkm : k = m
    · subst hkm; simp [idle] at hk
    · simp only [Function.update_of_ne hkm] at hk hP
      exact absurd (h.idle_none (m := m) (by simp [hpc, busy]) hk) hP
  loc k := by
    by_cases hkm : k = m
    · subst hkm; simp [LP]
    · have hk := eq_oth_of_ne hkm
      simp only [Function.update_of_ne hkm]
      subst hk
      refine LP_writeP (s := s) (b := s.x m) (fun hi => h.idle_none (m := m) (by simp [hpc, busy]) hi)
        (by simpa [LP] using h.loc' hpc) (by simp [Function.update_of_ne hkm])
        (by simp) rfl rfl (h.loc _)

/-- Line 4: `d := C.Decide(v)`. -/
lemma Inv.write4 (h : Inv s) {m : Fin 2} (hpc : s.pc m = .l4) :
    Inv { s with pc := Function.update s.pc m (.l5 (s.C.getD (s.x m))),
                 C := some (s.C.getD (s.x m)) } where
  px := h.px
  cP w hw := by
    simp only [Option.some.injEq] at hw
    rcases hC : s.C with _ | c
    · rw [hC] at hw
      simp only [Option.getD_none] at hw
      have hPm : s.P m ≠ none := h.loc' hpc
      obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hPm
      exact ⟨m, by rw [ha, h.px m a ha, hw]⟩
    · rw [hC] at hw
      simp only [Option.getD_some] at hw
      exact h.cP w (hw ▸ hC)
  dC w hw := by
    have := h.dC w hw
    simp [this]
  quiet k hk hP := by
    by_cases hkm : k = m
    · subst hkm; simp [idle] at hk
    · simp only [Function.update_of_ne hkm] at hk hP
      exact absurd (h.idle_none (m := m) (by simp [hpc, busy]) hk) hP
  loc k := by
    by_cases hkm : k = m
    · subst hkm; simpa [LP] using (h.loc' hpc : s.P k ≠ none)
    · simp only [Function.update_of_ne hkm]
      exact LP_writeC (s := s) (fun d hd => by simp [hd]) rfl rfl (h.loc k)

/-- Line 5: `D := d`. -/
lemma Inv.write5 (h : Inv s) {m : Fin 2} {d : Bool} (hpc : s.pc m = .l5 d) :
    Inv { s with pc := Function.update s.pc m (.r6 d), D := some d } where
  px := h.px
  cP := h.cP
  dC w hw := by
    simp only [Option.some.injEq] at hw
    exact hw ▸ (h.loc' hpc).2
  quiet k hk hP := by
    by_cases hkm : k = m
    · subst hkm; simp [idle] at hk
    · simp only [Function.update_of_ne hkm] at hk hP
      exact absurd (h.idle_none (m := m) (by simp [hpc, busy]) hk) hP
  loc k := by
    by_cases hkm : k = m
    · subst hkm; simp [LP]
    · simp only [Function.update_of_ne hkm]
      have hD : s.D = none ∨ s.D = some d := by
        rcases hD : s.D with _ | d'
        · exact Or.inl rfl
        · have h1 := h.dC d' hD
          rw [(h.loc' hpc).2] at h1
          simp at h1; simp [h1]
      exact LP_writeD (s := s) (fun hi => h.idle_none (m := m) (by simp [hpc, busy]) hi)
        hD rfl rfl rfl (h.loc k)

lemma Inv.astep (h : Inv s) (m : Fin 2) : Inv (astep s m) := by
  rcases hpc : s.pc m with _ | a | _ | _ | d | _ | _ | a | _ | a | _ | d | d | d | d | d <;>
    simp only [Fig1.astep, hpc]
  · exact h.read (by simp [hpc, idle]) (by simp [busy]) rfl
  · have ha : a = s.P m := h.loc' hpc
    by_cases hn : a = none ∧ s.P (oth m) = none
    · have : k2 a (s.P (oth m)) = .l3 := by simp [k2, hn]
      rw [this]; exact h.enter3 (ha ▸ hn.1) hn.2
    · have : k2 a (s.P (oth m)) = .l7 := by simp [k2, hn]
      rw [this]
      refine h.read (by simp [hpc, idle]) (by simp [busy]) ?_
      simp only [LP]
      subst ha
      tauto
  · exact h.write3 hpc
  · exact h.write4 hpc
  · exact h.write5 hpc
  · have hl : LP s m .l7 := h.loc' hpc
    refine h.read (m := m) (by simp [hpc, idle]) ?_ ?_ <;> rcases hD : s.D with _ | d <;>
      simp_all [k7, busy, LP]
  · have hl : LP s m .l9a := h.loc' hpc
    exact h.read (by simp [hpc, idle]) (by simp [busy]) (by simpa [LP] using hl)
  · have hl : LP s m (.l9b a) := h.loc' hpc
    simp only [LP] at hl
    obtain ⟨rfl, h1, h2⟩ := hl
    refine h.read (by simp [hpc, idle]) (by unfold k9; split_ifs <;> cases s.P m <;> simp [busy]) ?_
    unfold k9
    split_ifs with ho
    · rcases hm : s.P m with _ | b
      · simp_all
      · simp [LP, hm, ho]
    · exact ⟨ho, h2⟩
  · have hl : LP s m .l11a := h.loc' hpc
    exact h.read (by simp [hpc, idle]) (by simp [busy]) (by simpa [LP] using hl)
  · have hl : LP s m (.l11b a) := h.loc' hpc
    simp only [LP] at hl
    obtain ⟨rfl, h1, h2⟩ := hl
    refine h.read (by simp [hpc, idle])
      (by unfold k11; split_ifs <;> cases s.P (oth m) <;> simp [busy]) ?_
    unfold k11
    split_ifs with hm
    · rcases ho : s.P (oth m) with _ | b
      · exact absurd ho h1
      · simp [LP, hm, ho]
    · simp [LP, hm, h1, h2 hm]
  · have hl : LP s m .l13 := h.loc' hpc
    simp only [LP] at hl
    refine h.read (by simp [hpc, idle]) (by simp [k13, busy]) ?_
    obtain ⟨h1, h2, h3⟩ := hl
    have h0 : s.P 0 ≠ none := by fin_cases m <;> simpa using ‹_›
    have h1' : s.P 1 ≠ none := by fin_cases m <;> simpa using ‹_›
    obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp h0
    simp [k13, LP, hb, h1', h3]
  all_goals exact h

lemma Inv.sstep (h : Inv s) : ∀ e, Inv (Fig1.sstep s e)
  | .step m => h.astep m
  | .crashAll => h.crash

lemma Inv.foldl (h : Inv s) (α : List (SEv 2)) : Inv (α.foldl Fig1.sstep s) := by
  induction α generalizing s with
  | nil => exact h
  | cons e α ih => exact ih (h.sstep e)


/-! ### The forced value -/

/-- `Good s v`: every output, past or future, has value `v` (see the module docstring). -/
def Good (s : St) (v : Bool) : Prop :=
  s.D = some v ∨ (∃ j, s.P j = some v ∧ s.P (oth j) = none ∧ s.pc (oth j) ≠ .l3) ∨
    (s.P 0 = some v ∧ s.P 1 ≠ none ∧ s.D = none ∧ ∀ k, ¬ (s.pc k).busy)

/-- If `C` holds `w` and only `P j = v` is recorded, then `w = v`. -/
lemma Inv.C_eq (h : Inv s) {w v : Bool} {j : Fin 2} (hC : s.C = some w) (hj : s.P j = some v)
    (ho : s.P (oth j) = none) : w = v := by
  obtain ⟨k, hk⟩ := h.cP w hC
  by_cases hkj : k = j
  · subst hkj; simpa [hj] using hk.symm
  · rw [eq_oth_of_ne hkj, ho] at hk; simp at hk

lemma Good.unique (h : Inv s) {v w : Bool} (hv : Good s v) (hw : Good s w) : v = w := by
  have key : ∀ {v w : Bool}, s.D = some v → ∀ j, s.P j = some w → s.P (oth j) = none →
      v = w := fun hD j hj ho => h.C_eq (h.dC _ hD) hj ho
  rcases hv with hv | ⟨j, hj, ho, -⟩ | ⟨hv0, hv1, hvD, -⟩ <;>
    rcases hw with hw | ⟨j', hj', ho', -⟩ | ⟨hw0, hw1, hwD, -⟩
  · rw [hv] at hw; simpa using hw
  · exact key hv j' hj' ho'
  · rw [hv] at hwD; simp at hwD
  · exact (key hw j hj ho).symm
  · by_cases hjj : j' = j
    · subst hjj; rw [hj] at hj'; simpa using hj'
    · rw [eq_oth_of_ne hjj, ho] at hj'; simp at hj'
  · fin_cases j <;> simp_all
  · rw [hw] at hvD; simp at hvD
  · fin_cases j' <;> simp_all
  · rw [hv0] at hw0; simpa using hw0

lemma Good.valid (h : Inv s) {v : Bool} (hv : Good s v) : ∃ k, s.x k = v := by
  rcases hv with hv | ⟨j, hj, -, -⟩ | ⟨hv0, -, -, -⟩
  · obtain ⟨k, hk⟩ := h.cP v (h.dC v hv)
    exact ⟨k, (h.px k v hk).symm⟩
  · exact ⟨j, (h.px j v hj).symm⟩
  · exact ⟨0, (h.px 0 v hv0).symm⟩

/-- Every return state satisfies `Good`. -/
lemma good_of_ret (h : Inv s) {k : Fin 2} {v : Bool} (hk : (s.pc k).ret = some v) :
    Good s v := by
  have hl := h.loc k
  rcases hpc : s.pc k with _ | a | _ | _ | d | _ | _ | a | _ | a | _ | d | d | d | d | d <;>
    rw [hpc] at hk hl <;> simp only [PC.ret, reduceCtorEq, Option.some.injEq] at hk <;>
    subst hk <;> simp only [LP] at hl
  · exact Or.inl hl
  · exact Or.inl hl
  · refine Or.inr (Or.inl ⟨k, hl.1, hl.2, ?_⟩)
    have := h.quiet k (by simp [hpc, idle]) (by simp [hl.1]) (oth k)
    intro h3; simp [h3, busy] at this
  · refine Or.inr (Or.inl ⟨oth k, hl.2, by simpa using hl.1, by simp [hpc]⟩)
  · refine Or.inr (Or.inr ⟨hl.1, hl.2.1, hl.2.2, ?_⟩)
    refine h.quiet k (by simp [hpc, idle]) ?_
    fin_cases k <;> simp_all

lemma Good.read {v : Bool} (hg : Good s v) {m : Fin 2} {c : PC} (hc : ¬ c.busy) :
    Good { s with pc := Function.update s.pc m c } v := by
  have hc3 : c ≠ .l3 := by rintro rfl; simp [busy] at hc
  rcases hg with hg | ⟨j, hj, ho, h3⟩ | ⟨h0, h1, hD, hb⟩
  · exact Or.inl hg
  · refine Or.inr (Or.inl ⟨j, hj, ho, ?_⟩)
    by_cases hjm : oth j = m
    · simp [hjm, hc3]
    · simpa [Function.update_of_ne hjm] using h3
  · refine Or.inr (Or.inr ⟨h0, h1, hD, fun k => ?_⟩)
    by_cases hkm : k = m
    · simpa [hkm] using hc
    · simpa [Function.update_of_ne hkm] using hb k

lemma Good.astep {v : Bool} (hg : Good s v) (h : Inv s) (m : Fin 2) :
    Good (Fig1.astep s m) v := by
  rcases hpc : s.pc m with _ | a | _ | _ | d | _ | _ | a | _ | a | _ | d | d | d | d | d <;>
    simp only [Fig1.astep, hpc]
  · exact hg.read (by simp [busy])
  · have ha : a = s.P m := h.loc' hpc
    by_cases hn : a = none ∧ s.P (oth m) = none
    · have : k2 a (s.P (oth m)) = .l3 := by simp [k2, hn]
      rw [this]
      rcases hg with hg | ⟨j, hj, ho, h3⟩ | ⟨h0, h1, hD, hb⟩
      · exact Or.inl hg
      · exfalso
        by_cases hjm : j = m
        · subst hjm; rw [← ha, hn.1] at hj; simp at hj
        · rw [eq_oth_of_ne hjm, hn.2] at hj; simp at hj
      · exfalso; fin_cases m <;> simp_all
    · have : k2 a (s.P (oth m)) = .l7 := by simp [k2, hn]
      rw [this]; exact hg.read (by simp [busy])
  · have hPm : s.P m = none := h.loc' hpc
    rcases hg with hg | ⟨j, hj, ho, h3⟩ | ⟨h0, h1, hD, hb⟩
    · exact Or.inl hg
    · exfalso
      by_cases hjm : j = m
      · subst hjm; simp_all
      · rw [eq_oth_of_ne hjm, oth_oth] at h3; exact h3 hpc
    · exact absurd (by simp [hpc, busy]) (hb m)
  · rcases hg with hg | ⟨j, hj, ho, h3⟩ | ⟨h0, h1, hD, hb⟩
    · exact Or.inl hg
    · refine Or.inr (Or.inl ⟨j, hj, ho, ?_⟩)
      by_cases hjm : oth j = m
      · simp [hjm]
      · simpa [Function.update_of_ne hjm] using h3
    · exact absurd (by simp [hpc, busy]) (hb m)
  · have hl : LP s m (.l5 d) := h.loc' hpc
    simp only [LP] at hl
    left
    show some d = some v
    rcases hg with hg | ⟨j, hj, ho, h3⟩ | ⟨h0, h1, hD, hb⟩
    · have := h.dC v hg; rw [hl.2] at this; exact this
    · rw [h.C_eq hl.2 hj ho]
    · exact absurd (by simp [hpc, busy]) (hb m)
  all_goals first
    | exact hg
    | (refine hg.read ?_; first
        | (simp [busy]; done)
        | (unfold k7; cases s.D <;> simp [busy])
        | (unfold k9; split_ifs <;> cases a <;> simp [busy])
        | (unfold k11; split_ifs <;> cases s.P (oth m) <;> simp [busy])
        | simp [k13, busy])

lemma Good.sstep (h : Inv s) {v : Bool} (hg : Good s v) : ∀ e, Good (Fig1.sstep s e) v
  | .step m => hg.astep h m
  | .crashAll => by
    rcases hg with hg | ⟨j, hj, ho, -⟩ | ⟨h0, h1, hD, -⟩
    · exact Or.inl hg
    · exact Or.inr (Or.inl ⟨j, hj, ho, by simp [Fig1.sstep]⟩)
    · exact Or.inr (Or.inr ⟨h0, h1, hD, by simp [Fig1.sstep, busy]⟩)

lemma Good.foldl (h : Inv s) {v : Bool} (hg : Good s v) (α : List (SEv 2)) :
    Good (α.foldl Fig1.sstep s) v := by
  induction α generalizing s with
  | nil => exact hg
  | cons e α ih => exact ih (h.sstep e) (hg.sstep h e)

end Podc.RecoverableHierarchy.Fig1
