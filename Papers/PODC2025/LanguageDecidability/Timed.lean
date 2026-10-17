import Papers.PODC2025.LanguageDecidability.Canonical

/-!
# The timed adversary `A_τ` and predictive decidability (Section 6)

## Model

An algorithm `V` runs against the timed adversary `A_τ` (Figure 6). When process `p` sends `v`
to `A_τ` (Line 03 of Figure 1, event `send`), `A_τ` announces `v` in `M[p]` (event `tw`, Lines
01–02 of Figure 6), the black box `A` answers `w`, and `A_τ` takes a snapshot of `M` (event
`ts`, Lines 04–06); `p` then receives `(w, view)` (Line 04 of Figure 1, event `recv`). Each of
these events is a separate step, so other processes can take steps in between.

* Views: `View I O = Fin n → List (Sym I O)`, the announced invocations of each process in
  announcement order (the paper uses the set of announced invocations; lists carry at least as
  much information).
* An algorithm against `A_τ` is an `Alg n I (TO I O) R`, whose responses are pairs
  `(w, view)`.
* `x(E)`: the symbols of the `send`/`recv` events (`THasInput`). The *sketch* `x~(E)`
  (Appendix B): the history obtained by moving every invocation forward to its `tw` and every
  response backward to its `ts`, i.e. the symbols of the `tw`/`ts` events (`THasSketch`). The
  paper builds `x~(E)` from the views, up to the order of invocations (responses) with the same
  view; in the executions used below (`tcanon`) all these orders coincide.
* Executions are fair and failure-free.

## Predictive decidability

`PSDecides`/`PWDecides` are Definitions 6.1/6.2 **without** the conjunct "there is an execution
`E' ≡ E` with `x(E') = x~(E)`" in the escape clause. Dropping it makes the definitions weaker, so
the impossibility results proved for them (`lemma_6_2_*`) hold a fortiori for the paper's
definitions; and the counterexample to Figure 9 violates them for a tight execution
(`x~(E) = x(E)`), where that conjunct is irrelevant.

`tcanon x` is the tight canonical execution (proof of Lemma 6.2: each process executes Lines
01–03 of `V` together with Lines 01–02 of `A_τ`, and Lines 04–06 together with Lines 04–07 of
`A_τ`); its input and its sketch are both `x`, and it is causal.
-/

namespace Podc2025.LanguageDecidability.Timed

open Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type} {R : Type}

/-- Views: the announced invocations of every process. -/
abbrev View (I O : Fin n → Type) := Fin n → List (Sym I O)

/-- Responses of `A_τ`: a response of `A` and a view. -/
abbrev TO (I O : Fin n → Type) : Fin n → Type := fun p => O p × View I O

/-- Program counter of a process running against `A_τ`. -/
inductive TPhase (A B Vw : Type)
  | idle
  | ready (v : A)
  | sent (v : A)
  | written
  | snapped (w : B) (vw : Vw)
  | got (w : B) (vw : Vw)

/-- Events of an execution against `A_τ`. -/
inductive TEv (I O : Fin n → Type)
  /-- Lines 01–02 of `V`. -/
  | pre (p : Fin n) (v : I p)
  /-- Line 03 of `V`: invocation of `A_τ`. -/
  | send (p : Fin n) (v : I p)
  /-- Lines 01–02 of `A_τ`: `M[p].write(sₚ ∪ {v})`. -/
  | tw (p : Fin n) (v : I p)
  /-- Lines 03–06 of `A_τ`: `A` responds `w`; snapshot of `M`. -/
  | ts (p : Fin n) (w : O p)
  /-- Line 04 of `V`: response `(w, view)` of `A_τ`. -/
  | recv (p : Fin n) (w : O p) (vw : View I O)
  /-- Lines 05–06 of `V`. -/
  | post (p : Fin n) (w : O p) (vw : View I O)

/-- Program counters of all processes and the contents of `M`. -/
structure TSt (I O : Fin n → Type) where
  ph : (p : Fin n) → TPhase (I p) (O p) (View I O)
  ann : View I O

/-- The event is enabled. -/
def TEnabled (st : TSt I O) : TEv I O → Prop
  | .pre p _ => st.ph p = .idle
  | .send p v => st.ph p = .ready v
  | .tw p v => st.ph p = .sent v
  | .ts p _ => st.ph p = .written
  | .recv p w vw => st.ph p = .snapped w vw
  | .post p w vw => st.ph p = .got w vw

/-- Effect of an event on the program counters and on `M`. -/
def tStepSt (st : TSt I O) : TEv I O → TSt I O
  | .pre p v => ⟨Function.update st.ph p (.ready v), st.ann⟩
  | .send p v => ⟨Function.update st.ph p (.sent v), st.ann⟩
  | .tw p v => ⟨Function.update st.ph p .written,
      Function.update st.ann p (st.ann p ++ [⟨p, .inl v⟩])⟩
  | .ts p w => ⟨Function.update st.ph p (.snapped w st.ann), st.ann⟩
  | .recv p w vw => ⟨Function.update st.ph p (.got w vw), st.ann⟩
  | .post p _ _ => ⟨Function.update st.ph p .idle, st.ann⟩

/-- Program counters and `M` along a schedule. -/
def tst (s : ℕ → TEv I O) : ℕ → TSt I O
  | 0 => ⟨fun _ => .idle, fun _ => []⟩
  | t + 1 => tStepSt (tst s t) (s t)

/-- A fair failure-free execution against `A_τ`. -/
structure TIsExec (s : ℕ → TEv I O) : Prop where
  valid : ∀ t, TEnabled (tst s t) (s t)
  fair : ∀ p N, ∃ t, N ≤ t ∧ ∃ w vw, s t = .post p w vw

/-- The block of `V` executed by an event, if any. -/
def TEv.toEv : TEv I O → Option (Ev I (TO I O))
  | .pre p v => some (.pre p v)
  | .post p w vw => some (.post p (w, vw))
  | _ => none

/-- Configurations of `V` along a schedule. -/
def trun (V : Alg n I (TO I O) R) (s : ℕ → TEv I O) : ℕ → Cfg V
  | 0 => ⟨V.m0, V.l0⟩
  | t + 1 => match (s t).toEv with
    | none => trun V s t
    | some e => (V.next t (trun V s t) e).1

/-- The report trace along a schedule. -/
def touts (V : Alg n I (TO I O) R) (s : ℕ → TEv I O) (t : ℕ) : Option (Fin n × R) :=
  match (s t).toEv with
  | none => none
  | some e => (V.next t (trun V s t) e).2

/-- Symbol of the input `x(E)` (events `send`, `recv`). -/
def TEv.sym : TEv I O → Option (Sym I O)
  | .send p v => some ⟨p, .inl v⟩
  | .recv p w _ => some ⟨p, .inr w⟩
  | _ => none

/-- Symbol of the sketch `x~(E)` (events `tw`, `ts`). -/
def TEv.ssym : TEv I O → Option (Sym I O)
  | .tw p v => some ⟨p, .inl v⟩
  | .ts p w => some ⟨p, .inr w⟩
  | _ => none

/-- `x` is the subsequence of the defined values of `σ`. -/
def HasSeq (σ : ℕ → Option (Sym I O)) (x : Word I O) : Prop :=
  ∃ ι : ℕ → ℕ, StrictMono ι ∧ (∀ t, (σ t).isSome → ∃ k, ι k = t) ∧ ∀ k, σ (ι k) = some (x k)

/-- The input `x(E)` of an execution against `A_τ`. -/
def THasInput (s : ℕ → TEv I O) (x : Word I O) : Prop := HasSeq (fun t => (s t).sym) x

/-- The sketch `x~(E)` of an execution against `A_τ`. -/
def THasSketch (s : ℕ → TEv I O) (y : Word I O) : Prop := HasSeq (fun t => (s t).ssym) y

/-- **Definition 6.1** (predictive strong decidability), without the conjunct "`∃ E' ≡ E` with
`x(E') = x~(E)`" (a weaker requirement). -/
def PSDecides (V : Alg n I (TO I O) Verdict) (L : Set (Word I O)) : Prop :=
  ∀ s x y, TIsExec s → THasInput s x → THasSketch s y →
    (x ∈ L → (∀ p, NoSet (touts V s) p = ∅) ∨ ((∃ p, NoSet (touts V s) p ≠ ∅) ∧ y ∉ L)) ∧
    (x ∉ L → ∃ p, NoSet (touts V s) p ≠ ∅)

/-- **Definition 6.2** (predictive weak decidability), without the conjunct "`∃ E' ≡ E` with
`x(E') = x~(E)`" (a weaker requirement). -/
def PWDecides (V : Alg n I (TO I O) Verdict) (L : Set (Word I O)) : Prop :=
  ∀ s x y, TIsExec s → THasInput s x → THasSketch s y →
    (x ∈ L → (∀ p, (NoSet (touts V s) p).Finite) ∨
      ((∃ p, (NoSet (touts V s) p).Infinite) ∧ y ∉ L)) ∧
    (x ∉ L → ∀ p, (NoSet (touts V s) p).Infinite)

/-- The class `PSD` (with the weaker Definition 6.1). -/
def PSD (L : Set (Word I O)) : Prop := ∃ V : Alg n I (TO I O) Verdict, PSDecides V L

/-- The class `PWD` (with the weaker Definition 6.2). -/
def PWD (L : Set (Word I O)) : Prop := ∃ V : Alg n I (TO I O) Verdict, PWDecides V L

/-! ### Causality -/

lemma tst_congr {s s' : ℕ → TEv I O} {T : ℕ} (h : ∀ t < T, s t = s' t) :
    ∀ t ≤ T, tst s t = tst s' t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => simp only [tst]; rw [ih (by omega), h t (by omega)]

lemma trun_congr (V : Alg n I (TO I O) R) {s s' : ℕ → TEv I O} {T : ℕ}
    (h : ∀ t < T, s t = s' t) : ∀ t ≤ T, trun V s t = trun V s' t := by
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih => simp only [trun]; rw [ih (by omega), h t (by omega)]

lemma touts_congr (V : Alg n I (TO I O) R) {s s' : ℕ → TEv I O} {T : ℕ}
    (h : ∀ t < T, s t = s' t) : ∀ t < T, touts V s t = touts V s' t := by
  intro t ht
  simp only [touts]; rw [trun_congr V h t ht.le, h t ht]

/-! ### The tight canonical execution -/

/-- Invocations of `q` among the first `k` symbols of `x` (the contents of `M[q]`). -/
def annOf (x : Word I O) (k : ℕ) : View I O :=
  fun q => (pfx x k).filter fun a => decide (a.1 = q) && a.2.isLeft

/-- Events of the segment (three slots) of the `k`-th symbol. -/
def tseg (x : Word I O) (k : ℕ) : ℕ → TEv I O :=
  match x k with
  | ⟨p, .inl v⟩ => fun j => if j = 0 then .pre p v else if j = 1 then .send p v else .tw p v
  | ⟨p, .inr w⟩ => fun j =>
      if j = 0 then .ts p w else if j = 1 then .recv p w (annOf x k) else .post p w (annOf x k)

/-- The tight canonical execution with input `x`. -/
def tcanon (x : Word I O) (t : ℕ) : TEv I O := tseg x (t / 3) (t % 3)

lemma tcanon_eq (x : Word I O) (k j : ℕ) (hj : j < 3) : tcanon x (3 * k + j) = tseg x k j := by
  simp only [tcanon]; congr 1 <;> omega

lemma annOf_congr {x y : Word I O} {k : ℕ} (h : ∀ m < k, x m = y m) : annOf x k = annOf y k := by
  funext q
  simp only [annOf, pfx]
  congr 1
  exact List.map_congr_left fun m hm => h m (List.mem_range.1 hm)

lemma tcanon_congr {x y : Word I O} {k : ℕ} (h : ∀ m < k, x m = y m) :
    ∀ t < 3 * k, tcanon x t = tcanon y t := by
  intro t ht
  simp only [tcanon, tseg]
  rw [h (t / 3) (by omega), annOf_congr fun m hm => h m (by omega)]

/-- Program counters and `M` at the start of segment `k`. -/
def tInv (x : Word I O) (k : ℕ) : TSt I O :=
  ⟨fun p => if Even (cnt x p k) then .idle else .written, annOf x k⟩

lemma annOf_succ (x : Word I O) (k : ℕ) (q : Fin n) :
    annOf x (k + 1) q = annOf x k q ++ if (x k).1 = q ∧ (x k).2.isLeft then [x k] else [] := by
  simp only [annOf, pfx, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.filter_append, List.filter_cons, List.filter_nil, Bool.and_eq_true, decide_eq_true_eq]

lemma tseg_ok {x : Word I O} (wf : WF x) (k : ℕ) (h : tst (tcanon x) (3 * k) = tInv x k) :
    (∀ j < 3, TEnabled (tst (tcanon x) (3 * k + j)) (tcanon x (3 * k + j))) ∧
      tst (tcanon x) (3 * k + 3) = tInv x (k + 1) := by
  have h1 : tst (tcanon x) (3 * k + 1) = tStepSt (tst (tcanon x) (3 * k)) (tcanon x (3 * k)) :=
    rfl
  have h2 : tst (tcanon x) (3 * k + 2) =
    tStepSt (tst (tcanon x) (3 * k + 1)) (tcanon x (3 * k + 1)) := rfl
  have h3 : tst (tcanon x) (3 * k + 3) =
    tStepSt (tst (tcanon x) (3 * k + 2)) (tcanon x (3 * k + 2)) := rfl
  have e0 : tcanon x (3 * k) = tseg x k 0 := by simpa using tcanon_eq x k 0 (by norm_num)
  have e1 := tcanon_eq x k 1 (by norm_num)
  have e2 := tcanon_eq x k 2 (by norm_num)
  have hann := annOf_succ x k
  have hc1 := @cnt_succ_eq _ _ _ x k
  have hn1 : ∀ q, (x k).1 ≠ q → cnt x q (k + 1) = cnt x q k := fun q h => cnt_succ_ne h
  rcases hxk : x k with ⟨p, v | w⟩
  · have he := wf_seq_inl wf hxk
    have hL : (x k).2.isLeft = true := by rw [hxk]; rfl
    simp only [hxk] at hc1 hn1 hann
    simp [tseg, hxk] at e0 e1 e2
    refine ⟨fun j hj => ?_, ?_⟩
    · interval_cases j
      · rw [add_zero, h, e0]; simp [TEnabled, tInv, he]
      · rw [h1, h, e0, e1]; simp [TEnabled, tStepSt]
      · rw [h2, h1, h, e0, e1, e2]; simp [TEnabled, tStepSt]
    · rw [h3, h2, h1, h, e0, e1, e2]
      simp only [tStepSt, tInv, TSt.mk.injEq]
      constructor
      · funext q
        by_cases hq : q = p
        · subst hq; simp [hc1, Nat.even_add_one, he]
        · simp [Function.update_of_ne hq, hn1 q (Ne.symm hq)]
      · funext q
        by_cases hq : q = p
        · subst hq; simp [hann, hL]
        · simp [Function.update_of_ne hq, hann, Ne.symm hq]
  · have he := wf_seq_inr wf hxk
    have hR : (x k).2.isRight = true := by rw [hxk]; rfl
    simp only [hxk] at hc1 hn1 hann
    simp [tseg, hxk] at e0 e1 e2
    refine ⟨fun j hj => ?_, ?_⟩
    · interval_cases j
      · rw [add_zero, h, e0]; simp [TEnabled, tInv, he]
      · rw [h1, h, e0, e1]; simp [TEnabled, tStepSt, tInv, hxk]
      · rw [h2, h1, h, e0, e1, e2]; simp [TEnabled, tStepSt]
    · rw [h3, h2, h1, h, e0, e1, e2]
      simp only [tStepSt, tInv, TSt.mk.injEq]
      constructor
      · funext q
        by_cases hq : q = p
        · subst hq; simp [hc1, Nat.even_add_one, he]
        · simp [Function.update_of_ne hq, hn1 q (Ne.symm hq)]
      · funext q
        simp [hann, hR]

lemma tst_tcanon {x : Word I O} (wf : WF x) : ∀ k, tst (tcanon x) (3 * k) = tInv x k
  | 0 => by
    simp only [Nat.mul_zero, tst, tInv, TSt.mk.injEq]
    exact ⟨by funext p; simp [cnt], by funext q; simp [annOf, pfx]⟩
  | k + 1 => by
    rw [show 3 * (k + 1) = 3 * k + 3 by ring]
    exact (tseg_ok wf k (tst_tcanon wf k)).2

/-- The tight canonical execution is a fair failure-free execution. -/
theorem tIsExec_tcanon {x : Word I O} (wf : WF x) : TIsExec (tcanon x) where
  valid t := by
    obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 ∧ t = 3 * k + j := ⟨t / 3, t % 3, by omega, by omega⟩
    exact (tseg_ok wf k (tst_tcanon wf k)).1 j hj
  fair p N := by
    obtain ⟨m, hm, w, hw⟩ := wf.exists_res p N
    refine ⟨3 * m + 2, by omega, w, annOf x m, ?_⟩
    rw [tcanon_eq x m 2 (by norm_num)]
    simp [tseg, hw]

lemma tseg_sym (x : Word I O) (k j : ℕ) (hj : j < 3) :
    (tseg x k j).sym = if j = 1 then some (x k) else none := by
  rcases hxk : x k with ⟨p, v | w⟩ <;> interval_cases j <;> simp [tseg, hxk, TEv.sym]

lemma tseg_ssym (x : Word I O) (k j : ℕ) (hj : j < 3) :
    (tseg x k j).ssym = if j = (if (x k).2.isLeft then 2 else 0) then some (x k) else none := by
  rcases hxk : x k with ⟨p, v | w⟩ <;> interval_cases j <;> simp [tseg, hxk, TEv.ssym]

/-- The input of the tight canonical execution is `x`. -/
theorem tHasInput_tcanon (x : Word I O) : THasInput (tcanon x) x := by
  refine ⟨fun k => 3 * k + 1, strictMono_nat_of_lt_succ fun k => by omega, fun t ht => ?_,
    fun k => ?_⟩
  · obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 ∧ t = 3 * k + j := ⟨t / 3, t % 3, by omega, by omega⟩
    simp only [tcanon_eq x k j hj, tseg_sym x k j hj] at ht
    split_ifs at ht with h
    · exact ⟨k, by dsimp only; omega⟩
    · simp at ht
  · dsimp only
    simp only [tcanon_eq x k 1 (by norm_num), tseg_sym x k 1 (by norm_num)]; rfl

/-- The sketch of the tight canonical execution is `x` (it is a tight execution). -/
theorem tHasSketch_tcanon (x : Word I O) : THasSketch (tcanon x) x := by
  refine ⟨fun k => 3 * k + if (x k).2.isLeft then 2 else 0,
    strictMono_nat_of_lt_succ fun k => by split_ifs <;> omega, fun t ht => ?_, fun k => ?_⟩
  · obtain ⟨k, j, hj, rfl⟩ : ∃ k j, j < 3 ∧ t = 3 * k + j := ⟨t / 3, t % 3, by omega, by omega⟩
    simp only [tcanon_eq x k j hj, tseg_ssym x k j hj] at ht
    split_ifs at ht with h h'
    · exact ⟨k, by simp [h]; omega⟩
    · simp at ht
    · exact ⟨k, by simp [h]; omega⟩
    · simp at ht
  · dsimp only
    rw [tcanon_eq x k _ (by split_ifs <;> omega), tseg_ssym x k _ (by split_ifs <;> omega)]
    simp

/-! ### Impossibility for limits of words of the language -/

/-- If `V` predictively strongly decides `L`, then no word outside `L` is a limit of words of
`L`: on tight executions, predictive strong decidability is strong decidability. -/
theorem psd_closed {V : Alg n I (TO I O) Verdict} {L : Set (Word I O)} (hV : PSDecides V L)
    (hL : IsDistLang L) {x : Word I O} (wf : WF x) (hx : x ∉ L)
    (happrox : ∀ k, ∃ y ∈ L, ∀ m < k, y m = x m) : False := by
  obtain ⟨p, hp⟩ := (hV _ x x (tIsExec_tcanon wf) (tHasInput_tcanon x) (tHasSketch_tcanon x)).2 hx
  obtain ⟨t, ht⟩ := Set.nonempty_iff_ne_empty.2 hp
  obtain ⟨y, hy, hyx⟩ := happrox (t / 3 + 1)
  have hty : touts V (tcanon y) t = some (p, .no) := by
    rw [touts_congr V (tcanon_congr (k := t / 3 + 1) hyx) t (by omega)]; exact ht
  have := (hV _ y y (tIsExec_tcanon (hL y hy)) (tHasInput_tcanon y) (tHasSketch_tcanon y)).1 hy
  rcases this with h | ⟨-, h⟩
  · have := h p; rw [Set.eq_empty_iff_forall_notMem] at this; exact this t hty
  · exact h hy

end Podc2025.LanguageDecidability.Timed
