import Podc.Computability.Distributed.NIS.Game

-- CSLib candidate: Cslib/Computability/Distributed/NIS/Simulation.lean (staged by Papers/PODC2021/ExtensionBasedReductions)
/-!
# Simulating one prover by another

A generic construction behind both "extension-based ⇒ augmented extension-based" (Section 4) and
Theorem 1 (Section 7): a *target* prover runs a *source* prover `σs` and answers each source move by
an adaptive, finite, non-empty dialogue with its own opponent (a `Prog`), whose result is the response
handed back to the source prover.

The main result `simulate_spec`: every play of the simulating prover splits into consecutive non-empty
windows; the `j`-th window is a run of the handler program for the `j`-th move of an induced play of the
source prover, which is consistent with `σs`.

This file does not depend on the NIS model. -- CSLib candidate (generic interactive simulation)
-/

namespace Cslib.NIS

/-- Interactive programs: ask a move, continue with the full history including its response. -/
inductive Prog (M R A : Type) where
  | done : A → Prog M R A
  | ask : M → (List (M × R) → Prog M R A) → Prog M R A

/-- `ProgRun h p w a`: started after history `h`, the program `p` asks exactly the moves of `w`
(which also lists their responses) and returns `a`. -/
inductive ProgRun {M R A : Type} : List (M × R) → Prog M R A → List (M × R) → A → Prop
  | done (h : List (M × R)) (a : A) : ProgRun h (.done a) [] a
  | ask (h : List (M × R)) (m : M) (f : List (M × R) → Prog M R A) (r : R) (w : List (M × R))
      (a : A) : ProgRun (h ++ [(m, r)]) (f (h ++ [(m, r)])) w a →
      ProgRun h (.ask m f) ((m, r) :: w) a

/-- Sequential composition of programs. -/
def Prog.bind {Mv R A B : Type} : Prog Mv R A → (A → Prog Mv R B) → Prog Mv R B
  | .done a, f => f a
  | .ask m k, f => .ask m (fun h => (k h).bind f)

lemma progRun_bind {Mv R A B : Type} (p : Prog Mv R A) (f : A → Prog Mv R B) :
    ∀ {h w b}, ProgRun h (p.bind f) w b →
      ∃ w1 w2 a, w = w1 ++ w2 ∧ ProgRun h p w1 a ∧ ProgRun (h ++ w1) (f a) w2 b := by
  induction p with
  | done a => intro h w b hr; exact ⟨[], w, a, rfl, ProgRun.done _ _, by simpa [Prog.bind] using hr⟩
  | ask m k ih =>
    intro h w b hr
    cases hr with
    | ask _ _ _ r w' _ hr' =>
      obtain ⟨w1, w2, a, rfl, h1, h2⟩ := ih _ hr'
      exact ⟨(m, r) :: w1, w2, a, rfl, ProgRun.ask _ _ _ _ _ _ h1, by simpa using h2⟩

section Sim

variable {Ms Rs Mt Rt : Type}

/-- State of the simulation: the induced source history, the current source move being handled,
the next target move, and the continuation of the handler program. -/
structure SimSt (Ms Rs Mt Rt : Type) where
  hs : List (Ms × Rs)
  ms : Ms
  mt : Mt
  k : List (Mt × Rt) → Prog Mt Rt Rs

variable (σs : List (Ms × Rs) → Ms)
  (H : List (Ms × Rs) → List (Mt × Rt) → Ms → Mt × (List (Mt × Rt) → Prog Mt Rt Rs))

/-- Start handling the next source move. -/
def simStart (hs : List (Ms × Rs)) (ht : List (Mt × Rt)) : SimSt Ms Rs Mt Rt :=
  ⟨hs, σs hs, (H hs ht (σs hs)).1, (H hs ht (σs hs)).2⟩

/-- Advance the simulation by one target move (`ht'` is the target history including it). -/
def adv (st : SimSt Ms Rs Mt Rt) (ht' : List (Mt × Rt)) : SimSt Ms Rs Mt Rt :=
  match st.k ht' with
  | .ask m f => ⟨st.hs, st.ms, m, f⟩
  | .done r => simStart σs H (st.hs ++ [(st.ms, r)]) ht'

/-- The simulation state after a target history. -/
def simOf (ht : List (Mt × Rt)) : SimSt Ms Rs Mt Rt :=
  (ht.foldl (fun (p : SimSt Ms Rs Mt Rt × List (Mt × Rt)) e => (adv σs H p.1 (p.2 ++ [e]), p.2 ++ [e]))
    (simStart σs H [] [], [])).1

/-- The simulating prover. -/
def simulate (ht : List (Mt × Rt)) : Mt := (simOf σs H ht).mt

lemma simOf_aux (ht : List (Mt × Rt)) :
    (ht.foldl (fun (p : SimSt Ms Rs Mt Rt × List (Mt × Rt)) e => (adv σs H p.1 (p.2 ++ [e]), p.2 ++ [e]))
      (simStart σs H [] [], [])).2 = ht := by
  suffices ∀ (ht : List (Mt × Rt)) (st : SimSt Ms Rs Mt Rt) (h0 : List (Mt × Rt)),
      (ht.foldl (fun (p : SimSt Ms Rs Mt Rt × List (Mt × Rt)) e => (adv σs H p.1 (p.2 ++ [e]), p.2 ++ [e]))
        (st, h0)).2 = h0 ++ ht from by simpa using this ht _ []
  intro ht
  induction ht with
  | nil => simp
  | cons e ht ih => intro st h0; simp [List.foldl_cons, ih]

lemma simOf_concat (ht : List (Mt × Rt)) (e : Mt × Rt) :
    simOf σs H (ht ++ [e]) = adv σs H (simOf σs H ht) (ht ++ [e]) := by
  unfold simOf
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [simOf_aux]

@[simp] lemma simOf_nil : simOf σs H ([] : List (Mt × Rt)) = simStart σs H [] [] := rfl

lemma simOf_ms (ht : List (Mt × Rt)) : (simOf σs H ht).ms = σs (simOf σs H ht).hs := by
  induction ht using List.reverseRecOn with
  | nil => rfl
  | append_singleton ht e ih =>
    rw [simOf_concat]; unfold adv
    split
    · exact ih
    · rfl

/-! ### Plays of the simulating prover -/

variable (pl : ℕ → Mt × Rt)

/-- Simulation state at time `k` of a target play. -/
def S (k : ℕ) : SimSt Ms Rs Mt Rt := simOf σs H (hist pl k)

lemma S_succ (k : ℕ) : S σs H pl (k + 1) = adv σs H (S σs H pl k) (hist pl (k + 1)) := by
  unfold S; rw [hist_succ, simOf_concat]

/-- The source response produced at time `k`, if the handler program finishes there. -/
def res (k : ℕ) : Option Rs :=
  match (S σs H pl k).k (hist pl (k + 1)) with
  | .done r => some r
  | .ask _ _ => none

/-- The handler finishes at time `k`. -/
def IsDone (k : ℕ) : Prop := (res σs H pl k).isSome

instance (k : ℕ) : Decidable (IsDone σs H pl k) := by
  unfold IsDone; infer_instance

lemma S_succ_of_ask {k : ℕ} {m : Mt} {f : List (Mt × Rt) → Prog Mt Rt Rs}
    (h : (S σs H pl k).k (hist pl (k + 1)) = .ask m f) :
    S σs H pl (k + 1) = ⟨(S σs H pl k).hs, (S σs H pl k).ms, m, f⟩ := by
  rw [S_succ]; unfold adv; rw [h]

lemma S_succ_of_done {k : ℕ} {r : Rs}
    (h : (S σs H pl k).k (hist pl (k + 1)) = .done r) :
    S σs H pl (k + 1) = simStart σs H ((S σs H pl k).hs ++ [((S σs H pl k).ms, r)]) (hist pl (k + 1)) := by
  rw [S_succ]; unfold adv; rw [h]

lemma exists_done (k : ℕ) : ∃ k' ≥ k, IsDone σs H pl k' := by
  suffices ∀ p : Prog Mt Rt Rs, ∀ k, (S σs H pl k).k (hist pl (k + 1)) = p →
      ∃ k' ≥ k, IsDone σs H pl k' from this _ k rfl
  intro p
  induction p with
  | done r => intro k hk; exact ⟨k, le_rfl, by simp [IsDone, res, hk]⟩
  | ask m f ih =>
    intro k hk
    obtain ⟨k', hk', hd⟩ := ih (hist pl (k + 2)) (k + 1) (by rw [S_succ_of_ask σs H pl hk])
    exact ⟨k', by omega, hd⟩

lemma infinite_done : {k | IsDone σs H pl k}.Infinite := by
  refine Set.infinite_of_not_bddAbove fun ⟨b, hb⟩ => ?_
  obtain ⟨k', hk', hd⟩ := exists_done σs H pl (b + 1)
  have := hb hd; omega

/-- The time of the `j`-th completed handler run. -/
noncomputable def dT (j : ℕ) : ℕ := Nat.nth (IsDone σs H pl) j

/-- Start of the `j`-th window. -/
noncomputable def aT : ℕ → ℕ
  | 0 => 0
  | j + 1 => dT σs H pl j + 1

lemma isDone_dT (j : ℕ) : IsDone σs H pl (dT σs H pl j) :=
  Nat.nth_mem_of_infinite (infinite_done σs H pl) j

lemma dT_strictMono : StrictMono (dT σs H pl) :=
  Nat.nth_strictMono (infinite_done σs H pl)

/-- The induced source play. -/
noncomputable def srcPlay (j : ℕ) : Ms × Rs :=
  ((S σs H pl (dT σs H pl j)).ms, (res σs H pl (dT σs H pl j)).get (isDone_dT σs H pl j))

lemma srcPlay_eq {j k : ℕ} (hk : dT σs H pl j = k) {r : Rs}
    (hr : (S σs H pl k).k (hist pl (k + 1)) = .done r) : srcPlay σs H pl j = ((S σs H pl k).ms, r) := by
  subst hk; simp [srcPlay, res, hr]

lemma count_isDone (k : ℕ) :
    (S σs H pl k).hs = hist (srcPlay σs H pl)
      (Nat.count (IsDone σs H pl) k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.count_succ]
    by_cases hd : IsDone σs H pl k
    · simp only [hd, if_true]
      obtain ⟨r, hr⟩ : ∃ r, (S σs H pl k).k (hist pl (k + 1)) = .done r := by
        unfold IsDone res at hd; split at hd
        · next r h => exact ⟨r, h⟩
        · simp at hd
      rw [S_succ_of_done σs H pl hr]
      simp only [simStart]
      rw [hist_succ, ih, srcPlay_eq σs H pl (Nat.nth_count hd) hr]
    · simp only [hd, if_false, add_zero]
      obtain ⟨m, f, hr⟩ : ∃ m f, (S σs H pl k).k (hist pl (k + 1)) = .ask m f := by
        unfold IsDone res at hd; split at hd
        · simp at hd
        · next m f h => exact ⟨m, f, h⟩
      rw [S_succ_of_ask σs H pl hr]; exact ih

lemma count_aT (j : ℕ) : Nat.count (IsDone σs H pl) (aT σs H pl j) = j := by
  cases j with
  | zero => simp [aT]
  | succ j =>
    simp only [aT, dT]
    rw [Nat.count_succ, Nat.count_nth_of_infinite (infinite_done σs H pl)]
    simp [Nat.nth_mem_of_infinite (infinite_done σs H pl) j]

lemma S_aT (j : ℕ) :
    S σs H pl (aT σs H pl j) = simStart σs H (hist (srcPlay σs H pl) j) (hist pl (aT σs H pl j)) := by
  cases j with
  | zero => rfl
  | succ j =>
    have hd := isDone_dT σs H pl j
    obtain ⟨r, hr⟩ : ∃ r, (S σs H pl (dT σs H pl j)).k (hist pl (dT σs H pl j + 1)) = .done r := by
      unfold IsDone res at hd; split at hd
      · next r h => exact ⟨r, h⟩
      · simp at hd
    simp only [aT]
    rw [S_succ_of_done σs H pl hr]
    congr 1
    have := count_isDone σs H pl (dT σs H pl j + 1)
    rw [S_succ_of_done σs H pl hr] at this
    have hc := count_aT σs H pl (j + 1)
    simp only [aT] at hc
    rw [hc] at this
    simpa [simStart] using this

lemma aT_lt (j : ℕ) : aT σs H pl j < aT σs H pl (j + 1) := by
  cases j with
  | zero => simp [aT]
  | succ j =>
    show dT σs H pl j + 1 < dT σs H pl (j + 1) + 1
    have := dT_strictMono σs H pl (show j < j + 1 by omega); omega

lemma aT_le_dT (j : ℕ) : aT σs H pl j ≤ dT σs H pl j := by
  cases j with
  | zero => simp [aT]
  | succ j =>
    show dT σs H pl j + 1 ≤ dT σs H pl (j + 1)
    exact dT_strictMono σs H pl (show j < j + 1 by omega)

lemma not_isDone_of_lt {j k : ℕ} (h1 : aT σs H pl j ≤ k) (h2 : k < dT σs H pl j) :
    ¬ IsDone σs H pl k := by
  intro hd
  have hmono : j ≤ Nat.count (IsDone σs H pl) k := by
    have := Nat.count_monotone (IsDone σs H pl) h1; rwa [count_aT] at this
  have h3 := (dT_strictMono σs H pl).monotone hmono
  have h4 : dT σs H pl (Nat.count (IsDone σs H pl) k) = k := Nat.nth_count hd
  omega

lemma srcPlay_consistent (j : ℕ) : (srcPlay σs H pl j).1 = σs (hist (srcPlay σs H pl) j) := by
  have h1 : (srcPlay σs H pl j).1 = (S σs H pl (dT σs H pl j)).ms := rfl
  have h2 : (S σs H pl (dT σs H pl j)).ms = σs (S σs H pl (dT σs H pl j)).hs := simOf_ms σs H _
  have h3 : Nat.count (IsDone σs H pl) (dT σs H pl j) = j :=
    Nat.count_nth_of_infinite (infinite_done σs H pl) j
  rw [h1, h2, count_isDone, h3]

/-- The target moves and responses in `[a, b)`. -/
def window {α : Type} (pl : ℕ → α) (a b : ℕ) : List α := (List.range' a (b - a)).map pl

lemma hist_add_window {α : Type} (pl : ℕ → α) {a b : ℕ} (h : a ≤ b) :
    hist pl b = hist pl a ++ window pl a b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [window, hist, Nat.add_sub_cancel_left]
  rw [List.range_add]; simp [List.map_map, Function.comp_def, List.range'_eq_map_range]

lemma window_cons {α : Type} (pl : ℕ → α) {a b : ℕ} (h : a < b) :
    window pl a b = pl a :: window pl (a + 1) b := by
  simp only [window]
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show a + c + 1 - a = c + 1 by omega, show a + c + 1 - (a + 1) = c by omega, List.range'_succ]
  simp

variable (hc : ∀ k, (pl k).1 = simulate σs H (hist pl k))
include hc

lemma progRun_window (j : ℕ) :
    ProgRun (hist pl (aT σs H pl j))
      (.ask (H (hist (srcPlay σs H pl) j) (hist pl (aT σs H pl j)) (srcPlay σs H pl j).1).1
            (H (hist (srcPlay σs H pl) j) (hist pl (aT σs H pl j)) (srcPlay σs H pl j).1).2)
      (window pl (aT σs H pl j) (aT σs H pl (j + 1))) (srcPlay σs H pl j).2 := by
  have key : ∀ i, i ≤ dT σs H pl j - aT σs H pl j →
      ProgRun (hist pl (dT σs H pl j - i))
        (.ask (S σs H pl (dT σs H pl j - i)).mt (S σs H pl (dT σs H pl j - i)).k)
        (window pl (dT σs H pl j - i) (aT σs H pl (j + 1))) (srcPlay σs H pl j).2 := by
    intro i
    induction i with
    | zero =>
      intro _
      have hd := isDone_dT σs H pl j
      obtain ⟨r, hr⟩ : ∃ r, (S σs H pl (dT σs H pl j)).k (hist pl (dT σs H pl j + 1)) = .done r := by
        unfold IsDone res at hd; split at hd
        · next r h => exact ⟨r, h⟩
        · simp at hd
      simp only [Nat.sub_zero, aT]
      rw [window_cons pl (Nat.lt_succ_self _), show window pl (dT σs H pl j + 1)
        (dT σs H pl j + 1) = [] by simp [window]]
      have hpl : pl (dT σs H pl j) = ((S σs H pl (dT σs H pl j)).mt, (pl (dT σs H pl j)).2) := by
        ext
        · exact hc _
        · rfl
      rw [hpl]
      refine ProgRun.ask _ _ _ _ _ _ ?_
      rw [← hpl, ← hist_succ, hr]
      have : (srcPlay σs H pl j).2 = r := by simp [srcPlay, res, hr]
      rw [this]; exact ProgRun.done _ _
    | succ i ih =>
      intro hi
      have hle := aT_le_dT σs H pl j
      have ih' := ih (by omega)
      set k := dT σs H pl j - (i + 1) with hk
      have hk1 : dT σs H pl j - i = k + 1 := by omega
      rw [hk1] at ih'
      have hnd := not_isDone_of_lt σs H pl (j := j) (k := k) (by omega) (by omega)
      obtain ⟨m, f, hr⟩ : ∃ m f, (S σs H pl k).k (hist pl (k + 1)) = .ask m f := by
        unfold IsDone res at hnd; split at hnd
        · simp at hnd
        · next m f h => exact ⟨m, f, h⟩
      rw [S_succ_of_ask σs H pl hr] at ih'
      have hlt : k < aT σs H pl (j + 1) := by simp only [aT]; omega
      rw [window_cons pl hlt]
      have hpl : pl k = ((S σs H pl k).mt, (pl k).2) := by
        ext
        · exact hc _
        · rfl
      rw [hpl]
      refine ProgRun.ask _ _ _ _ _ _ ?_
      rw [← hpl, ← hist_succ, hr]
      exact ih'
  have := key (dT σs H pl j - aT σs H pl j) le_rfl
  rw [show dT σs H pl j - (dT σs H pl j - aT σs H pl j) = aT σs H pl j by
    have := aT_le_dT σs H pl j; omega] at this
  rw [S_aT] at this
  simp only [simStart] at this
  rw [← srcPlay_consistent σs H pl j] at this
  exact this

end Sim

/-- **Simulation lemma.** Every play consistent with `simulate σs H` decomposes into consecutive
non-empty windows `[a j, a (j+1))`, `a 0 = 0`; the `j`-th window is a complete run of the handler
program for the `j`-th move of a play `ps` that is consistent with `σs`, and returns its response. -/
theorem simulate_spec {Ms Rs Mt Rt : Type} (σs : List (Ms × Rs) → Ms)
    (H : List (Ms × Rs) → List (Mt × Rt) → Ms → Mt × (List (Mt × Rt) → Prog Mt Rt Rs))
    (pl : ℕ → Mt × Rt) (hc : ∀ k, (pl k).1 = simulate σs H (hist pl k)) :
    ∃ (ps : ℕ → Ms × Rs) (a : ℕ → ℕ), a 0 = 0 ∧ (∀ j, a j < a (j + 1)) ∧
      (∀ j, (ps j).1 = σs (hist ps j)) ∧
      ∀ j, ProgRun (hist pl (a j))
        (.ask (H (hist ps j) (hist pl (a j)) (ps j).1).1 (H (hist ps j) (hist pl (a j)) (ps j).1).2)
        (window pl (a j) (a (j + 1))) (ps j).2 :=
  ⟨srcPlay σs H pl, aT σs H pl, rfl, aT_lt σs H pl,
    srcPlay_consistent σs H pl, progRun_window σs H pl hc⟩

end Cslib.NIS
