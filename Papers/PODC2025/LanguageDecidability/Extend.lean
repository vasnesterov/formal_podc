import Papers.PODC2025.LanguageDecidability.Model

/-!
# Post-processing the reports of an algorithm (the transformations of Lemmas 4.1–4.3)

The algorithms `W` of Figures 2–4 run an algorithm `V` unchanged and only modify Line 06: the
value `d` that `V` is to report is post-processed with extra local variables (`A`) and extra
shared variables (`N`). `Alg.extend V a₀ n₀ f` is this algorithm; its executions are the
executions of `V` (the schedule is the same), and its reports are obtained from the reports of
`V` by a transducer (`tRun`, `tOut`; `outs_extend`).

In our model a block is atomic, so the extra code in Line 06 (register reads/writes and a
snapshot in the paper) is part of the same atomic block.
-/

namespace Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type} {R : Type}

/-- `V` with Line 06 replaced by: compute the value `d` that `V` reports, then run `f` on the
extra local state, the extra shared memory and `d`, and report the result of `f`. -/
def Alg.extend (V : Alg n I O R) {A N R' : Type} (a₀ : Fin n → A) (n₀ : N)
    (f : Fin n → A → N → R → A × N × R') : Alg n I O R' where
  L := V.L × A
  M := V.M × N
  m0 := (V.m0, n₀)
  l0 p := (V.l0 p, a₀ p)
  pre t p l v m := (((V.pre t p l.1 v m.1).1, l.2), ((V.pre t p l.1 v m.1).2, m.2))
  post t p l w m :=
    (((V.post t p l.1 w m.1).1, (f p l.2 m.2 (V.post t p l.1 w m.1).2.2).1),
     ((V.post t p l.1 w m.1).2.1, (f p l.2 m.2 (V.post t p l.1 w m.1).2.2).2.1),
     (f p l.2 m.2 (V.post t p l.1 w m.1).2.2).2.2)

section transducer

variable {A N R' : Type} (f : Fin n → A → N → R → A × N × R') (a₀ : Fin n → A) (n₀ : N)

/-- One step of the transducer on an optional report. -/
def tStep (st : (Fin n → A) × N) : Option (Fin n × R) → (Fin n → A) × N
  | none => st
  | some (p, d) => (Function.update st.1 p (f p (st.1 p) st.2 d).1, (f p (st.1 p) st.2 d).2.1)

/-- The state of the transducer along a report trace. -/
def tRun (o : ℕ → Option (Fin n × R)) : ℕ → (Fin n → A) × N
  | 0 => (a₀, n₀)
  | t + 1 => tStep f (tRun o t) (o t)

/-- The transduced report trace. -/
def tOut (o : ℕ → Option (Fin n × R)) (t : ℕ) : Option (Fin n × R') :=
  (o t).map fun pd => (pd.1, (f pd.1 ((tRun f a₀ n₀ o t).1 pd.1) (tRun f a₀ n₀ o t).2 pd.2).2.2)

end transducer

section lemmas

variable (V : Alg n I O R) (s : ℕ → Ev I O)

lemma outs_pre {t : ℕ} {p : Fin n} {v : I p} (h : s t = .pre p v) : V.outs s t = none := by
  simp [Alg.outs, h, Alg.next]

lemma outs_of_sym {t : ℕ} (h : (s t).sym.isSome) : V.outs s t = none := by
  simp [Alg.outs, V.next_of_sym h]

lemma outs_post {t : ℕ} {p : Fin n} {w : O p} (h : s t = .post p w) :
    V.outs s t = some (p, (V.post t p ((V.run s t).loc p) w (V.run s t).mem).2.2) := by
  simp [Alg.outs, h, Alg.next]

lemma outs_eq_none_or {t : ℕ} :
    V.outs s t = none ∨ ∃ p w, s t = .post p w ∧
      V.outs s t = some (p, (V.post t p ((V.run s t).loc p) w (V.run s t).mem).2.2) := by
  rcases h : s t with ⟨p, v⟩ | ⟨p, v⟩ | ⟨p, w⟩ | ⟨p, w⟩
  · exact Or.inl (outs_pre V s h)
  · exact Or.inl (outs_of_sym V s (by simp [h, Ev.sym]))
  · exact Or.inl (outs_of_sym V s (by simp [h, Ev.sym]))
  · exact Or.inr ⟨p, w, rfl, outs_post V s h⟩

/-- In a fair execution every process reports infinitely often. -/
def FairTrace {R : Type} (o : ℕ → Option (Fin n × R)) : Prop :=
  ∀ p N, ∃ t, N ≤ t ∧ ∃ d, o t = some (p, d)

lemma IsExec.fairTrace {s : ℕ → Ev I O} (hs : IsExec s) : FairTrace (V.outs s) := by
  intro p N
  obtain ⟨t, ht, w, hw⟩ := hs.fair p N
  exact ⟨t, ht, _, outs_post V s hw⟩

variable {A N R' : Type} (f : Fin n → A → N → R → A × N × R') (a₀ : Fin n → A) (n₀ : N)

lemma run_extend : ∀ t, ((V.extend a₀ n₀ f).run s t).mem =
      ((V.run s t).mem, (tRun f a₀ n₀ (V.outs s) t).2) ∧
    ∀ p, ((V.extend a₀ n₀ f).run s t).loc p = ((V.run s t).loc p, (tRun f a₀ n₀ (V.outs s) t).1 p)
  | 0 => ⟨rfl, fun _ => rfl⟩
  | t + 1 => by
    obtain ⟨ihm, ihl⟩ := run_extend t
    rcases h : s t with ⟨p, v⟩ | ⟨p, v⟩ | ⟨p, w⟩ | ⟨p, w⟩
    · have ho := outs_pre V s h
      simp only [Alg.run, h, Alg.next, tRun, ho, tStep, ihm, ihl]
      refine ⟨rfl, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp [Alg.extend]
      · simp [Function.update_of_ne hq, ihl]; rfl
    · have ho := outs_of_sym V s (t := t) (by simp [h, Ev.sym])
      simp only [Alg.run, h, Alg.next, tRun, ho, tStep, ihm, ihl]
      exact ⟨rfl, fun q => rfl⟩
    · have ho := outs_of_sym V s (t := t) (by simp [h, Ev.sym])
      simp only [Alg.run, h, Alg.next, tRun, ho, tStep, ihm, ihl]
      exact ⟨rfl, fun q => rfl⟩
    · have ho := outs_post V s h
      simp only [Alg.run, h, Alg.next, tRun, ho, tStep, ihm, ihl]
      refine ⟨rfl, fun q => ?_⟩
      by_cases hq : q = p
      · subst hq; simp [Alg.extend]
      · simp [Function.update_of_ne hq, ihl]; rfl

/-- The reports of the extended algorithm are the transduced reports of `V`. -/
theorem outs_extend : (V.extend a₀ n₀ f).outs s = tOut f a₀ n₀ (V.outs s) := by
  funext t
  obtain ⟨hm, hl⟩ := run_extend V s f a₀ n₀ t
  rcases h : s t with ⟨p, v⟩ | ⟨p, v⟩ | ⟨p, w⟩ | ⟨p, w⟩
  · rw [outs_pre _ s h, tOut, outs_pre V s h]; rfl
  · rw [outs_of_sym _ s (by simp [h, Ev.sym]), tOut, outs_of_sym V s (by simp [h, Ev.sym])]; rfl
  · rw [outs_of_sym _ s (by simp [h, Ev.sym]), tOut, outs_of_sym V s (by simp [h, Ev.sym])]; rfl
  · rw [outs_post _ s h, tOut, outs_post V s h, hl p, hm]
    rfl

end lemmas

end Podc2025.LanguageDecidability
