import Papers.PODC2015.StabilizingByzStorage.Atomic

/-!
# An executable step function for Fig. 3

`Atomic.apply σ a` performs the action `a` (a server delivery, a client step with the adversary's
choices) if it is enabled, and `apply_sound` shows that it is a step of `Atomic.Step`. Used to check the
concrete counterexample execution by evaluation.
-/

namespace Podc.StabilizingByzStorage

variable {n : ℕ}

namespace Atomic

variable {m : ℕ} [NeZero m] {V : Type} [DecidableEq V]

/-- An action of the adversary / scheduler. Collections give the quorum `Q`, the replies of the
Byzantine servers (`byz`, only used on `B`), and the value chosen at a threshold test. -/
inductive Act (n m : ℕ) (V : Type) where
  | dW (s : Fin n)
  | dR (s : Fin n)
  | invW (v : V)
  | endW
  | ack (Q : Finset (Fin n)) (byz : Fin n → Option (Fin m × V))
  | endH
  | invR
  | endPre
  | preAdopt (Q : Finset (Fin n)) (byz : Fin n → (Fin m × V) × Option (Fin m × V)) (d : Fin m × V)
  | preNone (Q : Finset (Fin n)) (byz : Fin n → (Fin m × V) × Option (Fin m × V))
  | endLoop
  | retLast (Q : Finset (Fin n)) (byz : Fin n → (Fin m × V) × Option (Fin m × V)) (d : Fin m × V)
  | retHelp (Q : Finset (Fin n)) (byz : Fin n → (Fin m × V) × Option (Fin m × V)) (d : Fin m × V)
  | retry (Q : Finset (Fin n)) (byz : Fin n → (Fin m × V) × Option (Fin m × V))

variable (t : ℕ) (B : Finset (Fin n))

/-- Write acks seen in a collection. -/
def ackVec (σ : State n m V) (byz : Fin n → Option (Fin m × V)) (s : Fin n) :
    Option (Fin m × V) :=
  if s ∈ B then byz s else ((σ.srv s).wack).getD none

/-- Read replies seen in a collection. -/
def repVec (σ : State n m V) (byz : Fin n → (Fin m × V) × Option (Fin m × V)) (s : Fin n) :
    (Fin m × V) × Option (Fin m × V) :=
  if s ∈ B then byz s else ((σ.srv s).rack).getD (byz s)

instance decHelpMaj (Q : Finset (Fin n)) (f : Fin n → Option (Fin m × V)) (k : ℕ) :
    Decidable (∃ a, k + 1 ≤ cnt Q f (some a)) :=
  decidable_of_iff _ (exists_le_cnt_some_iff Q f (Nat.le_add_left 1 k)).symm

instance decLastMaj (Q : Finset (Fin n)) (f : Fin n → Fin m × V) (k : ℕ) :
    Decidable (∃ a, k + 1 ≤ cnt Q f a) :=
  decidable_of_iff _ (exists_le_cnt_iff Q f (Nat.le_add_left 1 k)).symm

/-- The quorum condition of a read collection. -/
def okR (σ : State n m V) (Q : Finset (Fin n)) : Prop :=
  Q.card = n - t ∧ ∀ s ∈ Q, s ∉ B → (σ.srv s).rack ≠ none

instance (σ : State n m V) (Q : Finset (Fin n)) : Decidable (okR t B σ Q) := by
  unfold okR; infer_instance

/-- Executable version of `Step`. -/
def apply (σ : State n m V) : Act n m V → Option (Label V × State n m V)
  | .dW s => if (σ.srv s).wq ≠ [] then
      some (.tau, { σ with srv := Function.update σ.srv s (σ.srv s).deliverW }) else none
  | .dR s => if (σ.srv s).rq ≠ [] then
      some (.tau, { σ with srv := Function.update σ.srv s (σ.srv s).deliverR }) else none
  | .invW v => if σ.w.phase = .idle then
      some (.invWrite v,
        { σ with w := ⟨σ.w.wsn + 1, .bcastWrite v⟩, srv := σ.bcastW (.write (σ.w.wsn + 1, v)) })
      else none
  | .endW => match σ.w.phase with
      | .bcastWrite v => if n - 2 * t ≤ syncW B σ.srv then
          some (.tau, { σ with w := ⟨σ.w.wsn, .waitAck v⟩ }) else none
      | _ => none
  | .ack Q byz => match σ.w.phase with
      | .waitAck v =>
        if Q.card = n - t ∧ ∀ s ∈ Q, s ∉ B → (σ.srv s).wack ≠ none then
          if ∃ w, 4 * t + 1 ≤ cnt Q (ackVec B σ byz) (some w) then
            some (.retWrite, { σ with w := ⟨σ.w.wsn, .idle⟩ })
          else some (.tau,
            { σ with w := ⟨σ.w.wsn, .bcastHelp⟩, srv := σ.bcastW (.newHelp (σ.w.wsn, v)) })
        else none
      | _ => none
  | .endH => if σ.w.phase = .bcastHelp ∧ n - 2 * t ≤ syncW B σ.srv then
      some (.retWrite, { σ with w := ⟨σ.w.wsn, .idle⟩ }) else none
  | .invR => if σ.r.phase = .idle then
      some (.invRead, { σ with r := { σ.r with phase := .bcastPre }, srv := σ.bcastR false })
      else none
  | .endPre => if σ.r.phase = .bcastPre ∧ n - 2 * t ≤ syncR B σ.srv then
      some (.tau, { σ with r := { σ.r with phase := .waitPre } }) else none
  | .preAdopt Q byz d =>
    if σ.r.phase = .waitPre ∧ okR t B σ Q ∧
        2 * t + 1 ≤ cnt Q (fun s => (repVec B σ byz s).2) (some d) then
      some (.tau, { σ with
        r := if gtcd σ.r.pwsn d.1 then ⟨d.1, d.2, .bcastLoop⟩ else { σ.r with phase := .bcastLoop }
        srv := σ.bcastR true })
    else none
  | .preNone Q byz =>
    if σ.r.phase = .waitPre ∧ okR t B σ Q ∧
        ¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (repVec B σ byz s).2) (some d) then
      some (.tau, { σ with r := { σ.r with phase := .bcastLoop }, srv := σ.bcastR true })
    else none
  | .endLoop => if σ.r.phase = .bcastLoop ∧ n - 2 * t ≤ syncR B σ.srv then
      some (.tau, { σ with r := { σ.r with phase := .waitLoop } }) else none
  | .retLast Q byz d =>
    if σ.r.phase = .waitLoop ∧ okR t B σ Q ∧
        2 * t + 1 ≤ cnt Q (fun s => (repVec B σ byz s).1) d then
      some (.retRead (if gtcd d.1 σ.r.pwsn then d.2 else σ.r.pv),
        { σ with r := if gtcd d.1 σ.r.pwsn then ⟨d.1, d.2, .idle⟩ else { σ.r with phase := .idle } })
    else none
  | .retHelp Q byz d =>
    if σ.r.phase = .waitLoop ∧ okR t B σ Q ∧
        (¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (repVec B σ byz s).1) d) ∧
        2 * t + 1 ≤ cnt Q (fun s => (repVec B σ byz s).2) (some d) then
      some (.retRead d.2, { σ with r := ⟨d.1, d.2, .idle⟩ })
    else none
  | .retry Q byz =>
    if σ.r.phase = .waitLoop ∧ okR t B σ Q ∧
        (¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (repVec B σ byz s).1) d) ∧
        (¬ ∃ d, 2 * t + 1 ≤ cnt Q (fun s => (repVec B σ byz s).2) (some d)) then
      some (.tau, { σ with r := { σ.r with phase := .bcastLoop }, srv := σ.bcastR false })
    else none

omit [NeZero m] [DecidableEq V] in
lemma ackVec_spec (σ : State n m V) (byz : Fin n → Option (Fin m × V)) (s : Fin n) (hs : s ∉ B)
    (h : (σ.srv s).wack ≠ none) : (σ.srv s).wack = some (ackVec B σ byz s) := by
  unfold ackVec; simp only [hs, ite_false]; cases h' : (σ.srv s).wack <;> simp_all

omit [NeZero m] [DecidableEq V] in
lemma repVec_spec (σ : State n m V) (byz : Fin n → (Fin m × V) × Option (Fin m × V)) (s : Fin n)
    (hs : s ∉ B) (h : (σ.srv s).rack ≠ none) : (σ.srv s).rack = some (repVec B σ byz s) := by
  unfold repVec; simp only [hs, ite_false]; cases h' : (σ.srv s).rack <;> simp_all

/-- Every action performed by `apply` is a step of the model. -/
theorem apply_sound (σ σ' : State n m V) (a : Act n m V) (ℓ : Label V)
    (h : apply t B σ a = some (ℓ, σ')) : Step t B σ ℓ σ' := by
  cases a with
  | dW s =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; exact .delivW σ s h1
  | dR s =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; exact .delivR σ s h1
  | invW v =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; exact .invWrite σ v h1
  | endW =>
    simp only [apply] at h
    split at h
    · rename_i v hv
      split at h <;> rename_i h1
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h; exact .endWrite σ v hv h1
      · simp at h
    · simp at h
  | ack Q byz =>
    simp only [apply] at h
    split at h
    · rename_i v hv
      split at h <;> rename_i h1
      · split at h <;> rename_i h2 <;> simp only [Option.some.injEq, Prod.mk.injEq] at h <;>
          obtain ⟨rfl, rfl⟩ := h
        · exact .ackDone σ v hv Q (ackVec B σ byz) h1.1
            (fun s hs hb => ackVec_spec B σ byz s hb (h1.2 s hs hb)) h2
        · exact .ackHelp σ v hv Q (ackVec B σ byz) h1.1
            (fun s hs hb => ackVec_spec B σ byz s hb (h1.2 s hs hb)) h2
      · simp at h
    · simp at h
  | endH =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; exact .endHelp σ h1.1 h1.2
  | invR =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; exact .invRead σ h1
  | endPre =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; exact .endPre σ h1.1 h1.2
  | preAdopt Q byz d =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp only [Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .preAdopt σ h1.1 Q (repVec B σ byz) h1.2.1.1
      (fun s hs hb => repVec_spec B σ byz s hb (h1.2.1.2 s hs hb)) d h1.2.2
  | preNone Q byz =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp only [Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .preNone σ h1.1 Q (repVec B σ byz) h1.2.1.1
      (fun s hs hb => repVec_spec B σ byz s hb (h1.2.1.2 s hs hb)) h1.2.2
  | endLoop =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp at h
    obtain ⟨rfl, rfl⟩ := h; exact .endLoop σ h1.1 h1.2
  | retLast Q byz d =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp only [Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .retLast σ h1.1 Q (repVec B σ byz) h1.2.1.1
      (fun s hs hb => repVec_spec B σ byz s hb (h1.2.1.2 s hs hb)) d h1.2.2
  | retHelp Q byz d =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp only [Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .retHelp σ h1.1 Q (repVec B σ byz) h1.2.1.1
      (fun s hs hb => repVec_spec B σ byz s hb (h1.2.1.2 s hs hb)) h1.2.2.1 d h1.2.2.2
  | retry Q byz =>
    simp only [apply] at h; split at h <;> rename_i h1 <;> simp only [Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .retry σ h1.1 Q (repVec B σ byz) h1.2.1.1
      (fun s hs hb => repVec_spec B σ byz s hb (h1.2.1.2 s hs hb)) h1.2.2.1 h1.2.2.2

/-- Run a list of actions; returns the list of (label, state after) pairs. -/
def run (σ : State n m V) : List (Act n m V) → Option (List (Label V × State n m V))
  | [] => some []
  | a :: as => match apply t B σ a with
    | none => none
    | some (ℓ, σ') => (run σ' as).map ((ℓ, σ') :: ·)

/-- The trace produced by `run` is a sequence of steps. -/
theorem run_spec : ∀ (σ : State n m V) (as : List (Act n m V)) (tr : List (Label V × State n m V)),
    run t B σ as = some tr → ∀ j < tr.length,
      Step t B ((σ :: tr.map Prod.snd).getD j σ) ((tr.map Prod.fst).getD j .tau)
        ((tr.map Prod.snd).getD j σ)
  | σ, [], tr, h => by simp [run] at h; subst h; simp
  | σ, a :: as, tr, h => by
    simp only [run] at h
    split at h
    · simp at h
    · rename_i ℓ σ' ha
      obtain ⟨tr', h', rfl⟩ := Option.map_eq_some_iff.1 h
      intro j hj
      cases j with
      | zero => simpa using apply_sound t B σ σ' a ℓ ha
      | succ j =>
        have hj' : j < tr'.length := by simpa using hj
        have := run_spec σ' as tr' h' j hj'
        cases j with
        | zero =>
          simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
            List.getElem?_map, List.getElem?_eq_getElem hj', List.map_cons] at this ⊢
          simpa using this
        | succ j =>
          have hj'' : j < tr'.length := by omega
          simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, List.getElem?_map,
            List.getElem?_eq_getElem hj', List.getElem?_eq_getElem hj'', List.map_cons] at this ⊢
          simpa using this

end Atomic
end Podc.StabilizingByzStorage
