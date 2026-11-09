import Papers.PODC2012.OptimismConcurrency.Basic

/-!
# Positions of the events kept by `complete`

`lfIdx f H` lists the positions (in `H`) of the events kept by `lookFilter f H`; `kidx f H a` is
the position of the `a`-th kept event. Lemmas: kept events are the events at these positions,
positions are strictly increasing, and every position whose event passes the filter occurs.
Then, for `complete`, a *window lemma*: between two kept events of an operation of `p` with no
kept response of `p` in between, every event of `p` is kept.
-/

namespace Podc.OptimismConcurrency

section LF

variable {α : Type*} (f : α → List α → Bool)

/-- Positions of the events kept by `lookFilter f`. -/
def lfIdx : List α → List ℕ
  | [] => []
  | e :: l => if f e l then 0 :: (lfIdx l).map (· + 1) else (lfIdx l).map (· + 1)

/-- Position of the `a`-th kept event. -/
def kidx (H : List α) (a : ℕ) : ℕ := (lfIdx f H).getD a 0

lemma length_lfIdx (H : List α) : (lfIdx f H).length = (lookFilter f H).length := by
  induction H with
  | nil => rfl
  | cons e l ih => simp only [lfIdx, lookFilter]; split <;> simp [ih]

lemma getElem?_lookFilter (H : List α) (a : ℕ) (ha : a < (lookFilter f H).length) :
    (lookFilter f H)[a]? = H[kidx f H a]? ∧ kidx f H a < H.length := by
  induction H generalizing a with
  | nil => simp [lookFilter] at ha
  | cons e l ih =>
    simp only [lookFilter, kidx, lfIdx] at ha ⊢
    by_cases hfe : f e l = true
    · simp only [hfe, if_true] at ha ⊢
      cases a with
      | zero => simp
      | succ a =>
        simp only [List.length_cons, Nat.add_lt_add_iff_right] at ha
        obtain ⟨h1, h2⟩ := ih a ha
        simp only [kidx] at h1 h2
        have hl : a < (lfIdx f l).length := by rw [length_lfIdx]; exact ha
        simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl] at h1 h2 ⊢
        exact ⟨h1, h2⟩
    · simp only [hfe] at ha ⊢
      obtain ⟨h1, h2⟩ := ih a ha
      simp only [kidx] at h1 h2
      have hl : a < (lfIdx f l).length := by rw [length_lfIdx]; exact ha
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl] at h1 h2 ⊢
      exact ⟨h1, h2⟩

lemma lfIdx_sorted (H : List α) : (lfIdx f H).Pairwise (· < ·) := by
  induction H with
  | nil => simp [lfIdx]
  | cons e l ih =>
    simp only [lfIdx]
    have hm : ((lfIdx f l).map (· + 1)).Pairwise (· < ·) := by
      rw [List.pairwise_map]; exact ih.imp (by omega)
    split
    · exact List.Pairwise.cons (by simp) hm
    · exact hm

lemma kidx_strictMono (H : List α) {a b : ℕ} (hab : a < b) (hb : b < (lookFilter f H).length) :
    kidx f H a < kidx f H b := by
  have hs := lfIdx_sorted f H
  have hb' : b < (lfIdx f H).length := by rw [length_lfIdx]; exact hb
  unfold kidx
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hb']
  exact List.pairwise_iff_getElem.1 hs a b (by omega) hb' hab

lemma kidx_lt_iff (H : List α) {a b : ℕ} (ha : a < (lookFilter f H).length)
    (hb : b < (lookFilter f H).length) : kidx f H a < kidx f H b ↔ a < b := by
  constructor
  · intro h; by_contra h'; push Not at h'
    rcases h'.lt_or_eq with h' | rfl
    · exact absurd (kidx_strictMono f H h' ha) (by omega)
    · omega
  · intro h; exact kidx_strictMono f H h hb

lemma mem_lfIdx (H : List α) (m : ℕ) (hm : m < H.length) (hf : f H[m] (H.drop (m + 1)) = true) :
    ∃ a, a < (lookFilter f H).length ∧ kidx f H a = m := by
  induction H generalizing m with
  | nil => simp at hm
  | cons e l ih =>
    cases m with
    | zero =>
      have hf' : f e l = true := by simpa using hf
      refine ⟨0, ?_, ?_⟩
      · simp [lookFilter, hf']
      · simp [kidx, lfIdx, hf']
    | succ m =>
      simp only [List.getElem_cons_succ, List.drop_succ_cons] at hf
      obtain ⟨a, ha, hka⟩ := ih m (by simpa using hm) hf
      have hl : a < (lfIdx f l).length := by rw [length_lfIdx]; exact ha
      by_cases he : f e l = true
      · refine ⟨a + 1, by simp [lookFilter, he, ha], ?_⟩
        simp only [kidx, lfIdx, he, if_true] at hka ⊢
        rw [List.getD_eq_getElem _ _ hl] at hka
        rw [List.getD_eq_getElem _ _ (by simpa using hl)]
        simp [hka]
      · refine ⟨a, by simp [lookFilter, he, ha], ?_⟩
        simp only [kidx, lfIdx, he] at hka ⊢
        rw [List.getD_eq_getElem _ _ hl] at hka
        rw [List.getD_eq_getElem _ _ (by simpa using hl)]
        simp [hka]

lemma kidx_kept (H : List α) (a : ℕ) (ha : a < (lookFilter f H).length) :
    ∃ hk : kidx f H a < H.length, f H[kidx f H a] (H.drop (kidx f H a + 1)) = true := by
  induction H generalizing a with
  | nil => simp [lookFilter] at ha
  | cons e l ih =>
    by_cases hfe : f e l = true
    · cases a with
      | zero => exact ⟨by simp [kidx, lfIdx, hfe], by simpa [kidx, lfIdx, hfe] using hfe⟩
      | succ a =>
        simp only [lookFilter, hfe, if_true, List.length_cons, Nat.add_lt_add_iff_right] at ha
        obtain ⟨hk, h⟩ := ih a ha
        have hl : a < (lfIdx f l).length := by rw [length_lfIdx]; exact ha
        have e1 : kidx f (e :: l) (a + 1) = kidx f l a + 1 := by
          simp only [kidx, lfIdx, hfe, if_true]
          rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl]; simp
        refine ⟨by rw [e1]; simpa using hk, ?_⟩
        simp only [e1, List.getElem_cons_succ, List.drop_succ_cons]; exact h
    · simp only [lookFilter, hfe] at ha
      obtain ⟨hk, h⟩ := ih a ha
      have hl : a < (lfIdx f l).length := by rw [length_lfIdx]; exact ha
      have e1 : kidx f (e :: l) a = kidx f l a + 1 := by
        simp only [kidx, lfIdx, hfe]
        rw [List.getD_eq_getElem _ _ (by simpa using hl), List.getD_eq_getElem _ _ hl]; simp
      refine ⟨by rw [e1]; simpa using hk, ?_⟩
      simp only [e1, List.getElem_cons_succ, List.drop_succ_cons]; exact h

end LF

section Find

variable {α : Type*}

lemma find?_drop_some {l : List α} {q : α → Bool} {i : ℕ} {t : α}
    (h : (l.drop i).find? q = some t) :
    ∃ T, i ≤ T ∧ ∃ hT : T < l.length, l[T] = t ∧ q t = true ∧
      ∀ m (hm : m < l.length), i ≤ m → m < T → q l[m] = false := by
  rw [List.find?_eq_some_iff_getElem] at h
  obtain ⟨hq, k, hk, hkt, hbefore⟩ := h
  simp only [List.length_drop] at hk
  refine ⟨i + k, by omega, by omega, by simpa using hkt, hq, fun m hm him hmT => ?_⟩
  have := hbefore (m - i) (by omega)
  simp only [List.getElem_drop, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  have e : l[i + (m - i)] = l[m] := by congr 1; omega
  rwa [e] at this

lemma find?_drop_of {l : List α} {q : α → Bool} {i T : ℕ} (hT : T < l.length) (hiT : i ≤ T)
    (hq : q l[T] = true) (hno : ∀ m (hm : m < l.length), i ≤ m → m < T → q l[m] = false) :
    (l.drop i).find? q = some l[T] := by
  rw [List.find?_eq_some_iff_getElem]
  refine ⟨hq, T - i, by simp; omega, by simp [show i + (T - i) = T by omega], fun j hj => ?_⟩
  simp only [List.getElem_drop]
  rw [hno (i + j) (by omega) (by omega) (by omega)]; rfl

end Find

section Window

variable {P X Op Res Obj Val : Type} [DecidableEq P] [DecidableEq X]

/-- The terminal-event predicate of `termOf`. -/
def isTermOf (p : P) (x : X) (e : Ev P X Op Res Obj Val) : Bool :=
  decide (e.proc = p) && decide (e.obj = x) && e.isTerm

lemma termOf_eq (p : P) (x : X) (l : Hist P X Op Res Obj Val) :
    termOf p x l = l.find? (isTermOf p x) := rfl

lemma keepC_iff (H : Hist P X Op Res Obj Val) (m : ℕ) (hm : m < H.length) :
    keepC H[m] (H.drop (m + 1)) = ((H.drop m).find? (isTermOf H[m].proc H[m].obj)).any Ev.isRes := by
  simp only [keepC, termOf_eq]
  rw [← List.getElem_cons_drop_succ_eq_drop hm]

/-- A kept event is not an abort. -/
lemma kept_not_abort {e : Ev P X Op Res Obj Val} {later : Hist P X Op Res Obj Val}
    (h : keepC e later = true) : e.isAbort = false := by
  by_contra ha
  simp only [Bool.not_eq_false] at ha
  have : e.isRes = false := by cases e <;> simp_all [Ev.isAbort, Ev.isRes]
  simp [keepC, termOf, List.find?_cons, Ev.isTerm, ha, this] at h

/-- A response is kept. -/
lemma keepC_res {e : Ev P X Op Res Obj Val} (he : e.isRes = true)
    (later : Hist P X Op Res Obj Val) : keepC e later = true := by
  simp [keepC, termOf, List.find?_cons, Ev.isTerm, he]

/-- **Window lemma.** Let the `a`-th and `b`-th events of `complete H` (`a < b`) be at positions
`kidx a < kidx b`, the former an event of an operation of `p` on `x` that is not its response,
and suppose no response of `p` on `x` is kept between them. Then every event of `p` on `x` strictly
between the two positions is kept. -/
lemma window (H : Hist P X Op Res Obj Val) {a b : ℕ} (hab : a < b) (hb : b < (complete H).length)
    {p : P} {x : X} (hpa : ∀ e, H[kidx keepC H a]? = some e → e.proc = p ∧ e.obj = x ∧ e.isRes = false)
    (hno : ∀ c, a < c → c < b → ∀ e, (complete H)[c]? = some e →
      ¬ (e.proc = p ∧ e.obj = x ∧ e.isRes = true))
    (m : ℕ) (hm : m < H.length) (h1 : kidx keepC H a < m) (h2 : m < kidx keepC H b)
    (hpm : H[m].proc = p) (hxm : H[m].obj = x) :
    ∃ c, a < c ∧ c < b ∧ kidx keepC H c = m := by
  have hcl : complete H = lookFilter keepC H := rfl
  have haL : a < (lookFilter keepC H).length := by rw [← hcl]; omega
  have hbL : b < (lookFilter keepC H).length := by rw [← hcl]; omega
  obtain ⟨ha2, hka⟩ := kidx_kept keepC H a haL
  set ka := kidx keepC H a with hka_def
  obtain ⟨hpa1, hxa1, hra⟩ := hpa H[ka] (List.getElem?_eq_getElem ha2)
  rw [keepC_iff H ka ha2] at hka
  obtain ⟨t, ht⟩ : ∃ t, (H.drop ka).find? (isTermOf H[ka].proc H[ka].obj) = some t := by
    cases h : (H.drop ka).find? (isTermOf H[ka].proc H[ka].obj) with
    | none => rw [h] at hka; simp at hka
    | some t => exact ⟨t, rfl⟩
  rw [ht] at hka; simp only [Option.any_some] at hka
  obtain ⟨T, hkaT, hT, hTt, hqt, hbefore⟩ := find?_drop_some ht
  rw [hpa1, hxa1] at hbefore hqt
  have hqt' := hqt
  simp only [isTermOf, Bool.and_eq_true, decide_eq_true_eq] at hqt'
  obtain ⟨⟨htp, htx⟩, -⟩ := hqt'
  have hTne : ka < T := by
    rcases hkaT.lt_or_eq with h | h
    · exact h
    · exfalso; subst h; rw [hTt] at hra; rw [hra] at hka; exact absurd hka (by simp)
  have hTk : keepC H[T] (H.drop (T + 1)) = true := keepC_res (by rw [hTt]; exact hka) _
  obtain ⟨c, hc, hkc⟩ := mem_lfIdx keepC H T hT hTk
  have hac : a < c := (kidx_lt_iff keepC H haL hc).1 (by rw [hkc]; exact hTne)
  have hbc : b ≤ c := by
    by_contra hcb; push Not at hcb
    have hcT : (complete H)[c]? = some H[T] := by
      rw [hcl, (getElem?_lookFilter keepC H c hc).1, hkc, List.getElem?_eq_getElem hT]
    exact hno c hac hcb H[T] hcT ⟨by rw [hTt]; exact htp, by rw [hTt]; exact htx,
      by rw [hTt]; exact hka⟩
  have hTb : kidx keepC H b ≤ T := by
    rcases hbc.lt_or_eq with h | h
    · rw [← hkc]; exact (kidx_strictMono keepC H h hc).le
    · rw [← hkc, h]
  have hmk : keepC H[m] (H.drop (m + 1)) = true := by
    rw [keepC_iff H m hm, hpm, hxm,
      find?_drop_of hT (by omega) (by rw [hTt]; exact hqt)
        (fun m' hm' h1' h2' => hbefore m' hm' (by omega) h2')]
    simpa [hTt] using hka
  obtain ⟨c', hc', hkc'⟩ := mem_lfIdx keepC H m hm hmk
  refine ⟨c', (kidx_lt_iff keepC H haL hc').1 (by rw [hkc']; exact h1),
    (kidx_lt_iff keepC H hc' hbL).1 (by rw [hkc']; exact h2), hkc'⟩

end Window

end Podc.OptimismConcurrency
