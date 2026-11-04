import Papers.PODC2014.RandomizationTwoHop.AStar

-- CSLib candidate (paper-local for now; see README)

/-!
# Full-information flooding algorithms

A deterministic anonymous algorithm that floods truncated walk languages: after `t` rounds node
`v` knows `trunc t (⟪X⟫ v)` (its view of tree depth `t`, i.e. `L_{t+1}(v)`), and in round `t` it
outputs `F t (trunc t (⟪X⟫ v))` if this is `some` and it has not output before. This turns any
"view-based" output rule `F` into a genuine port-numbering algorithm (`floodAlg`), for every
port numbering (ports are only used to receive the neighbours' languages).
-/

namespace Podc.RandomizationTwoHop

open SimpleGraph Cslib.PortNumbering

variable {L O : Type}

/-- The first output of the rule `F` on the truncations of `T` up to depth `t`. -/
def firstOut (F : ℕ → Set (List L) → Option O) (T : Set (List L)) : ℕ → Option O
  | 0 => F 0 (trunc 0 T)
  | t + 1 => (firstOut F T t).or (F (t + 1) (trunc (t + 1) T))

/-- The flooding algorithm with output rule `F`. State: own label, round number, current
truncated language, output so far. -/
def floodAlg (F : ℕ → Set (List L) → Option O) : RAlg L O where
  State := L × ℕ × Set (List L) × Option O
  Msg := Set (List L)
  init _ a := (a, 0, {[a]}, F 0 {[a]})
  send s _ := s.2.2.1
  recv s _ m :=
    let W' := {w | w = [s.1] ∨ ∃ i M w', m i = some M ∧ w' ∈ M ∧ w = s.1 :: w'}
    (s.1, s.2.1 + 1, W', s.2.2.2.or (F (s.2.1 + 1) W'))
  out s := s.2.2.2

theorem floodAlg_isDeterministic (F : ℕ → Set (List L) → Option O) :
    (floodAlg F).IsDeterministic := fun _ _ _ _ => rfl

theorem trunc_zero_lang (X : LGraph L) (v : X.V) : trunc 0 (⟪X⟫ v) = {[X.lab v]} := by
  ext w
  simp only [mem_trunc, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hw, hl⟩
    rcases mem_lang_iff.1 hw with rfl | ⟨u, w', _, hw', rfl⟩
    · rfl
    · have := lang_nonempty_word hw'
      cases w' with
      | nil => exact absurd rfl this
      | cons a w'' => simp at hl
  · rintro rfl
    exact ⟨single_mem_lang v, by simp⟩

/-- The state of the flooding algorithm after `t` rounds. -/
theorem floodAlg_state (F : ℕ → Set (List L) → Option O) (X : LGraph L) (P : PNGraph X.V)
    (hP : P.IsSimple) (hPG : P.toSimpleGraph = X.G) (β : X.V → ℕ → Bool) (t : ℕ) (v : X.V) :
    (floodAlg F).state P X.lab β t v = (X.lab v, t, trunc t (⟪X⟫ v), firstOut F (⟪X⟫ v) t) := by
  induction t generalizing v with
  | zero => simp only [RAlg.state, floodAlg, firstOut, trunc_zero_lang]
  | succ t ih =>
    have hW : {w | w = [X.lab v] ∨ ∃ (i : ℕ) (M : Set (List L)) (w' : List L), (floodAlg F).inbox P ((floodAlg F).state P X.lab β t)
        v i = some M ∧ w' ∈ M ∧ w = X.lab v :: w'} = trunc (t + 1) (⟪X⟫ v) := by
      ext w
      simp only [Set.mem_ofPred_eq, mem_trunc, RAlg.inbox]
      constructor
      · rintro (rfl | ⟨i, M, w', hM, hw', rfl⟩)
        · exact ⟨single_mem_lang v, by simp⟩
        · split_ifs at hM with hi
          cases hM
          have hw2 : w' ∈ trunc t (⟪X⟫ (P.nbr v i)) := by rw [ih] at hw'; exact hw'
          refine ⟨mem_lang_iff.2 (Or.inr ⟨_, w', ?_, hw2.1, rfl⟩), by simp; have := hw2.2; omega⟩
          rw [← hPG]; exact P.adj_nbr hP hi
      · rintro ⟨hw, hl⟩
        rcases mem_lang_iff.1 hw with rfl | ⟨u, w', hu, hw', rfl⟩
        · exact Or.inl rfl
        · right
          rw [← hPG] at hu
          obtain ⟨i, hi, rfl⟩ := P.exists_port_of_adj hu
          refine ⟨i, trunc t (⟪X⟫ (P.nbr v i)), w', by simp only [hi, ↓reduceIte, ih]; rfl, ⟨hw', ?_⟩, rfl⟩
          simp at hl; omega
    simp only [RAlg.state, ih]
    simp only [floodAlg] at hW ⊢
    rw [hW]
    rfl

/-- The flooding algorithm computes `firstOut`, on every simple port numbering. -/
theorem floodAlg_decided (F : ℕ → Set (List L) → Option O) (X : LGraph L) (P : PNGraph X.V)
    (hP : P.IsSimple) (hPG : P.toSimpleGraph = X.G) (β : X.V → ℕ → Bool) (t : ℕ) (v : X.V) :
    (floodAlg F).decided P X.lab β t v = firstOut F (⟪X⟫ v) t := by
  induction t with
  | zero => simp only [RAlg.decided, floodAlg_state F X P hP hPG]; rfl
  | succ t ih =>
    simp only [RAlg.decided, ih, floodAlg_state F X P hP hPG]
    change (firstOut F (⟪X⟫ v) t).or ((firstOut F (⟪X⟫ v) t).or _) =
      (firstOut F (⟪X⟫ v) t).or _
    cases firstOut F (⟪X⟫ v) t <;> rfl

theorem firstOut_isSome {F : ℕ → Set (List L) → Option O} {T : Set (List L)} {k t : ℕ}
    (hkt : k ≤ t) (h : (F k (trunc k T)).isSome) : (firstOut F T t).isSome := by
  induction hkt with
  | refl =>
    cases k with
    | zero => exact h
    | succ k => simp only [firstOut, Option.isSome_or, h, Bool.or_true]
  | step _ ih => simp only [firstOut, Option.isSome_or, ih, Bool.true_or]

/-- The first output is produced by the first `k` with `F k (trunc k T) ≠ none`. -/
theorem firstOut_eq_some {F : ℕ → Set (List L) → Option O} {T : Set (List L)} {t : ℕ} {o : O}
    (h : firstOut F T t = some o) :
    ∃ k ≤ t, F k (trunc k T) = some o ∧ ∀ j < k, F j (trunc j T) = none := by
  induction t generalizing o with
  | zero => exact ⟨0, le_rfl, h, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | succ t ih =>
    simp only [firstOut] at h
    cases hf : firstOut F T t with
    | some o' =>
      rw [hf] at h
      cases h
      obtain ⟨k, hk, h1, h2⟩ := ih hf
      exact ⟨k, by omega, h1, h2⟩
    | none =>
      rw [hf] at h
      refine ⟨t + 1, le_rfl, h, fun j hj => ?_⟩
      cases e : F j (trunc j T) with
      | none => rfl
      | some _ =>
        have := firstOut_isSome (F := F) (T := T) (Nat.lt_succ_iff.1 hj) (by simp [e])
        simp [hf] at this

end Podc.RandomizationTwoHop
