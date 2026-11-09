import Papers.PODC2015.StabilizingByzStorage.Regular

/-!
# Fig. 2: termination of `write()` and `read()` (Lemmas 1 and 2)

Infinite executions of the system `Regular.Step t B` of Fig. 2 (`Exec`), and weak fairness (`Fair`):

* *eventual delivery*: every correct server eventually delivers the oldest message of each of its
  two links (as long as the link is non-empty); this is the `Termination` property of
  `ss-broadcast` together with reliable FIFO links;
* *client weak fairness*: a client step that stays enabled is eventually taken. The end of a
  broadcast (`endWrite`, `endHelp`, `endLoop`) is enabled when `n - 2t` correct servers have
  delivered it (synchronized delivery); a collection (lines 02, 11) is enabled when `n - t` servers
  can answer (Byzantine servers can always answer, correct ones once they answered the current
  broadcast). Since the client's phase changes exactly when the client takes a step, "taken" is
  expressed as "the phase changes".

Initial states are arbitrary (no `Init` is assumed): the results hold after any transient failure.

* `lemma1_write_terminates` (Lemma 1): every `write` invocation is followed by its return
  (`B.card ≤ t`).
* `lemma2_read_terminates` (Lemma 2): if a `write` is invoked at least once (assumption (b) of
  the paper), every `read` invocation is followed by a return (`B.card ≤ t`, `6t < n`; the paper
  assumes `8t < n`). The proof differs from the paper's: either the writer eventually stops
  writing, and then all correct servers eventually hold the same `last_val` forever, or it writes
  forever, and then (after the current read has reset the helping values) at most one write
  executes line 04, after which the helping values of correct servers are frozen and the next
  write that returns at line 03 certifies `3t + 1` equal frozen helping values; in both cases a
  late iteration of the read loop must succeed.
-/

namespace Podc.StabilizingByzStorage.Regular

open Podc.StabilizingByzStorage

/-! ## Potentials on queues -/

/-- `upto p q`: length of the shortest prefix of `q` containing all elements satisfying `p`
(the number of deliveries until no `p`-message is pending). -/
def upto {α : Type} (p : α → Bool) : List α → ℕ
  | [] => 0
  | x :: q => if upto p q = 0 ∧ p x = false then 0 else upto p q + 1

lemma upto_tail {α : Type} (p : α → Bool) (q : List α) : upto p q.tail = upto p q - 1 := by
  cases q with
  | nil => simp [upto]
  | cons x q =>
    simp only [upto, List.tail_cons]
    split_ifs with h
    · simp [h.1]
    · simp

lemma upto_append {α : Type} (p : α → Bool) (q : List α) (x : α) (hx : p x = false) :
    upto p (q ++ [x]) = upto p q := by
  induction q with
  | nil => simp [upto, hx]
  | cons y q ih => simp only [List.cons_append, upto, ih]

lemma upto_eq_zero {α : Type} (p : α → Bool) (q : List α) :
    upto p q = 0 ↔ ∀ x ∈ q, p x = false := by
  induction q with
  | nil => simp [upto]
  | cons y q ih =>
    simp only [upto, List.mem_cons, forall_eq_or_imp]
    split_ifs with h
    · simp [h.2, ← ih, h.1]
    · constructor
      · intro h'; exact h'.elim
      · rintro ⟨h1, h2⟩; exact absurd ⟨ih.2 h2, h1⟩ h

lemma upto_true {α : Type} (q : List α) : upto (fun _ => true) q = 0 ↔ q = [] := by
  rw [upto_eq_zero]; cases q with
  | nil => simp
  | cons x q => simp only [List.mem_cons, Bool.true_eq_false, imp_false, not_forall, reduceCtorEq,
      iff_false]; exact ⟨x, by simp⟩

/-! ## Server-level facts -/

namespace Srv

variable {D : Type}

@[simp] lemma deliverW_rq (s : Server D) : s.deliverW.rq = s.rq := by
  unfold Server.deliverW; split <;> rfl
@[simp] lemma deliverW_rack (s : Server D) : s.deliverW.rack = s.rack := by
  unfold Server.deliverW; split <;> rfl
lemma deliverW_wq (s : Server D) : s.deliverW.wq = s.wq.tail := by
  unfold Server.deliverW; split <;> simp_all
@[simp] lemma deliverR_wq (s : Server D) : s.deliverR.wq = s.wq := by
  unfold Server.deliverR; split <;> rfl
@[simp] lemma deliverR_wack (s : Server D) : s.deliverR.wack = s.wack := by
  unfold Server.deliverR; split <;> rfl
@[simp] lemma deliverR_last (s : Server D) : s.deliverR.last = s.last := by
  unfold Server.deliverR; split <;> rfl
lemma deliverR_rq (s : Server D) : s.deliverR.rq = s.rq.tail := by
  unfold Server.deliverR; split <;> simp_all
lemma deliverR_help (s : Server D) : s.deliverR.help = if s.rq.headD false then none else s.help := by
  unfold Server.deliverR; split <;> simp_all
lemma deliverR_rack (s : Server D) : s.deliverR.rack = s.rack ∨
    s.deliverR.rack = some (s.last, if s.rq.headD false then none else s.help) := by
  unfold Server.deliverR; split
  · simp
  · split_ifs <;> simp_all

@[simp] lemma bcastW_wq (m : WMsg D) (s : Server D) : (s.bcastW m).wq = s.wq ++ [m] := rfl
@[simp] lemma bcastW_rq (m : WMsg D) (s : Server D) : (s.bcastW m).rq = s.rq := rfl
@[simp] lemma bcastW_wack (m : WMsg D) (s : Server D) : (s.bcastW m).wack = none := rfl
@[simp] lemma bcastW_rack (m : WMsg D) (s : Server D) : (s.bcastW m).rack = s.rack := rfl
@[simp] lemma bcastW_help (m : WMsg D) (s : Server D) : (s.bcastW m).help = s.help := rfl
@[simp] lemma bcastW_last (m : WMsg D) (s : Server D) : (s.bcastW m).last = s.last := rfl
@[simp] lemma bcastR_wq (b : Bool) (s : Server D) : (s.bcastR b).wq = s.wq := rfl
@[simp] lemma bcastR_rq (b : Bool) (s : Server D) : (s.bcastR b).rq = s.rq ++ [b] := rfl
@[simp] lemma bcastR_wack (b : Bool) (s : Server D) : (s.bcastR b).wack = s.wack := rfl
@[simp] lemma bcastR_rack (b : Bool) (s : Server D) : (s.bcastR b).rack = none := rfl
@[simp] lemma bcastR_help (b : Bool) (s : Server D) : (s.bcastR b).help = s.help := rfl
@[simp] lemma bcastR_last (b : Bool) (s : Server D) : (s.bcastR b).last = s.last := rfl

/-- `last_val` once all pending writer messages are delivered. -/
def lastW (s : Server D) : D :=
  s.wq.foldl (fun acc m => match m with | .write d => d | .newHelp _ => acc) s.last

/-- `helping_val` once all pending writer messages are delivered (no `READ(true)` assumed). -/
def helpW (s : Server D) : Option D :=
  s.wq.foldl (fun acc m => match m with | .newHelp d => some d | .write _ => acc) s.help

def isWrite : WMsg D → Bool
  | .write _ => true
  | .newHelp _ => false

def isHelp : WMsg D → Bool
  | .write _ => false
  | .newHelp _ => true

lemma lastW_deliverW (s : Server D) : lastW s.deliverW = lastW s := by
  unfold Server.deliverW lastW; split <;> simp_all

@[simp] lemma lastW_deliverR (s : Server D) : lastW s.deliverR = lastW s := by
  simp [lastW]

@[simp] lemma lastW_bcastR (b : Bool) (s : Server D) : lastW (s.bcastR b) = lastW s := rfl

lemma lastW_bcastW (m : WMsg D) (s : Server D) :
    lastW (s.bcastW m) = match m with | .write d => d | .newHelp _ => lastW s := by
  cases m <;> simp [lastW, Server.bcastW]

lemma foldl_lastW_of_noWrite (q : List (WMsg D)) (h : ∀ x ∈ q, isWrite x = false) (a : D) :
    q.foldl (fun acc m => match m with | .write d => d | .newHelp _ => acc) a = a := by
  induction q with
  | nil => rfl
  | cons m q ih =>
    cases m with
    | write d => simp [isWrite] at h
    | newHelp d => exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

lemma lastW_of_noWrite (s : Server D) (h : upto isWrite s.wq = 0) : lastW s = s.last :=
  foldl_lastW_of_noWrite _ ((upto_eq_zero _ _).1 h) _

lemma helpW_deliverW (s : Server D) : helpW s.deliverW = helpW s := by
  unfold Server.deliverW helpW; split <;> simp_all

lemma helpW_bcastW_write (d : D) (s : Server D) : helpW (s.bcastW (.write d)) = helpW s := by
  simp [helpW, Server.bcastW]

/-- The reply slot of the writer after a delivery. -/
lemma deliverW_wack (s : Server D) : s.deliverW.wack = s.wack ∨
    (s.deliverW.wack = some s.help ∧ helpW s = s.help ∧ s.deliverW.help = s.help) := by
  unfold Server.deliverW; split
  · simp
  · rename_i d rest h
    split_ifs with hr
    · subst hr; right; simp [helpW, h]
    · simp
  · simp

lemma deliverW_help_of_noHelp (s : Server D) (h : upto isHelp s.wq = 0) :
    s.deliverW.help = s.help := by
  rw [upto_eq_zero] at h
  unfold Server.deliverW; split
  · rfl
  · rfl
  · rename_i d rest hq; simp [hq, isHelp] at h

lemma helpW_deliverR (s : Server D) (h : s.rq.headD false = false) :
    helpW s.deliverR = helpW s := by
  unfold helpW; rw [deliverR_wq, deliverR_help, h]; simp

@[simp] lemma helpW_bcastR (b : Bool) (s : Server D) : helpW (s.bcastR b) = helpW s := rfl

lemma helpW_bcastW_newHelp (z : D) (s : Server D) : helpW (s.bcastW (.newHelp z)) = some z := by
  simp [helpW, Server.bcastW]

lemma headD_of_upto (q : List Bool) (h : upto (fun b => b) q = 0) : q.headD false = false := by
  rw [upto_eq_zero] at h
  cases q with
  | nil => rfl
  | cons b q => exact h b (by simp)

end Srv

/-! ## Steps -/

variable {n : ℕ} {V : Type} [DecidableEq V] (t : ℕ) (B : Finset (Fin n))


/-- The writer `ss_broadcast`s `m` in the step `σ → σ'` (line 01 or line 04). -/
def WBcast (σ σ' : State n V) (m : WMsg V) : Prop :=
  (∃ v, σ.w = .idle ∧ σ'.w = .bcastWrite v ∧ m = .write v) ∨
  (∃ v, σ.w = .waitAck v ∧ σ'.w = .bcastHelp ∧ m = .newHelp v)

/-- The reader `ss_broadcast`s `READ(b)` in the step `σ → σ'` (line 09). -/
def RBcast (σ σ' : State n V) (b : Bool) : Prop :=
  (σ.r = .idle ∧ σ'.r = .bcastLoop ∧ b = true) ∨ (σ.r = .waitLoop ∧ σ'.r = .bcastLoop ∧ b = false)

variable {t B}

lemma next_srv {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ') (s : Fin n) :
    σ'.srv s = σ.srv s ∨ σ'.srv s = (σ.srv s).deliverW ∨ σ'.srv s = (σ.srv s).deliverR ∨
    (∃ m, WBcast σ σ' m ∧ σ'.srv s = (σ.srv s).bcastW m) ∨
    (∃ b, RBcast σ σ' b ∧ σ'.srv s = (σ.srv s).bcastR b) := by
  rcases h with h | ⟨rfl, -⟩
  · cases h with
    | delivW s' _ =>
      by_cases hs : s = s'
      · subst hs; simp
      · simp [hs]
    | delivR s' _ =>
      by_cases hs : s = s'
      · subst hs; simp
      · simp [hs]
    | invWrite v hw => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, Or.inl ⟨v, hw, rfl, rfl⟩, rfl⟩)))
    | ackHelp v hw => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, Or.inr ⟨v, hw, rfl, rfl⟩, rfl⟩)))
    | invRead hr => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨true, Or.inl ⟨hr, rfl, rfl⟩, rfl⟩)))
    | retry hr => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨false, Or.inr ⟨hr, rfl, rfl⟩, rfl⟩)))
    | _ => exact Or.inl rfl
  · exact Or.inl rfl

lemma next_wbcast {σ σ' : State n V} {ℓ : Label V} {m : WMsg V} (h : Next t B σ ℓ σ')
    (hb : WBcast σ σ' m) (s : Fin n) : σ'.srv s = (σ.srv s).bcastW m := by
  rcases h with h | ⟨rfl, -⟩
  · cases h <;> rcases hb with ⟨v, h1, h2, rfl⟩ | ⟨v, h1, h2, rfl⟩ <;> simp_all
  · rcases hb with ⟨v, h1, h2, rfl⟩ | ⟨v, h1, h2, rfl⟩ <;> simp_all

lemma next_rbcast {σ σ' : State n V} {ℓ : Label V} {b : Bool} (h : Next t B σ ℓ σ')
    (hb : RBcast σ σ' b) (s : Fin n) : σ'.srv s = (σ.srv s).bcastR b := by
  rcases h with h | ⟨rfl, -⟩
  · cases h <;> rcases hb with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ <;> simp_all
  · rcases hb with ⟨h1, h2, rfl⟩ | ⟨h1, h2, rfl⟩ <;> simp_all

lemma next_invWrite {σ σ' : State n V} {v : V} (h : Next t B σ (.invWrite v) σ') :
    WBcast σ σ' (.write v) := by
  rcases h with h | ⟨-, h⟩
  · cases h with
    | invWrite v hw => exact Or.inl ⟨v, hw, rfl, rfl⟩
  · cases h

lemma next_invRead {σ σ' : State n V} (h : Next t B σ .invRead σ') : RBcast σ σ' true := by
  rcases h with h | ⟨-, h⟩
  · cases h with
    | invRead hr => exact Or.inl ⟨hr, rfl, rfl⟩
  · cases h

lemma next_r_idle {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ') (hr : σ.r ≠ .idle)
    (hr' : σ'.r = .idle) : ∃ v, ℓ = .retRead v := by
  rcases h with h | ⟨rfl, -⟩
  · cases h <;> simp_all
  · exact absurd hr' hr

lemma next_w_bcastWrite {σ σ' : State n V} {ℓ : Label V} {v : V} (h : Next t B σ ℓ σ')
    (hw : σ.w = .bcastWrite v) (hw' : σ'.w ≠ σ.w) : σ'.w = .waitAck v ∧ σ'.srv = σ.srv := by
  rcases h with h | ⟨rfl, -⟩
  · cases h <;> simp_all
  · exact absurd rfl hw'

lemma next_w_bcastHelp {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ')
    (hw : σ.w = .bcastHelp) (hw' : σ'.w ≠ σ.w) : ℓ = .retWrite := by
  rcases h with h | ⟨rfl, -⟩
  · cases h <;> simp_all
  · exact absurd rfl hw'

lemma next_w_waitAck {σ σ' : State n V} {ℓ : Label V} {v : V} (h : Next t B σ ℓ σ')
    (hw : σ.w = .waitAck v) (hw' : σ'.w ≠ σ.w) :
    ∃ (Q : Finset (Fin n)) (acks : Fin n → Option V), Q.card = n - t ∧
      (∀ s ∈ Q, s ∉ B → (σ.srv s).wack = some (acks s)) ∧
      (((∃ w, 4 * t + 1 ≤ cnt Q acks (some w)) ∧ ℓ = .retWrite ∧ σ'.w = .idle) ∨
       ((¬ ∃ w, 4 * t + 1 ≤ cnt Q acks (some w)) ∧ σ'.w = .bcastHelp)) := by
  rcases h with h | ⟨rfl, -⟩
  · cases h with
    | ackDone v h Q acks hQ hacks hc => exact ⟨Q, acks, hQ, hacks, Or.inl ⟨hc, rfl, rfl⟩⟩
    | ackHelp v h Q acks hQ hacks hc => exact ⟨Q, acks, hQ, hacks, Or.inr ⟨hc, rfl⟩⟩
    | _ => simp_all
  · exact absurd rfl hw'

lemma next_r_bcastLoop {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ')
    (hr : σ.r = .bcastLoop) (hr' : σ'.r ≠ σ.r) : σ'.r = .waitLoop := by
  rcases h with h | ⟨rfl, -⟩
  · cases h <;> simp_all
  · exact absurd rfl hr'

lemma next_r_waitLoop {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ')
    (hr : σ.r = .waitLoop) (hr' : σ'.r ≠ σ.r) : (∃ v, ℓ = .retRead v) ∨ σ'.r = .bcastLoop := by
  rcases h with h | ⟨rfl, -⟩
  · cases h <;> simp_all
  · exact absurd rfl hr'

lemma next_retry {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ')
    (hr : σ.r = .waitLoop) (hr' : σ'.r = .bcastLoop) :
    ∃ (Q : Finset (Fin n)) (reps : Fin n → V × Option V), Q.card = n - t ∧
      (∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (reps s)) ∧
      (¬ ∃ v, 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) v) ∧
      (¬ ∃ v, 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some v)) := by
  rcases h with h | ⟨rfl, -⟩
  · cases h with
    | retry h Q reps hQ hreps hl hh => exact ⟨Q, reps, hQ, hreps, hl, hh⟩
    | _ => simp_all
  · simp_all

omit [DecidableEq V] in
lemma WBcast.w_ne {σ σ' : State n V} {m : WMsg V} (h : WBcast σ σ' m) : σ'.w ≠ σ.w := by
  rcases h with ⟨v, h1, h2, -⟩ | ⟨v, h1, h2, -⟩ <;> simp [h1, h2]

omit [DecidableEq V] in
lemma RBcast.r_ne {σ σ' : State n V} {b : Bool} (h : RBcast σ σ' b) : σ'.r ≠ σ.r := by
  rcases h with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩ <;> simp [h1, h2]

omit [DecidableEq V] in
lemma WBcast.w_src {σ σ' : State n V} {m : WMsg V} (h : WBcast σ σ' m) :
    σ.w = .idle ∨ ∃ v, σ.w = .waitAck v := by
  rcases h with ⟨v, h1, -⟩ | ⟨v, h1, -⟩
  · exact Or.inl h1
  · exact Or.inr ⟨v, h1⟩

/-! ## Executions and fairness -/

variable (t B) in
/-- An infinite execution of the system of Fig. 2, from an arbitrary state: every step is a step of
`Step t B` or a stutter. -/
def Exec (e : ℕ → State n V) (lab : ℕ → Label V) : Prop :=
  ∀ i, Next t B (e i) (lab i) (e (i + 1))

variable (t B) in
/-- A step of the writer is enabled (`writer_step_of_enabled`): the end of a broadcast once `n - 2t`
correct servers delivered it, a collection (line 02) once `n - t` servers can answer. -/
def WEnabled (σ : State n V) : Prop :=
  match σ.w with
  | .idle => False
  | .bcastWrite _ => n - 2 * t ≤ syncW B σ.srv
  | .waitAck _ => n - t ≤ (Finset.univ.filter fun s => s ∈ B ∨ (σ.srv s).wack ≠ none).card
  | .bcastHelp => n - 2 * t ≤ syncW B σ.srv

variable (t B) in
/-- A step of the reader is enabled (`reader_step_of_enabled`). -/
def REnabled (σ : State n V) : Prop :=
  match σ.r with
  | .idle => False
  | .bcastLoop => n - 2 * t ≤ syncR B σ.srv
  | .waitLoop => n - t ≤ (Finset.univ.filter fun s => s ∈ B ∨ (σ.srv s).rack ≠ none).card

variable (t B) in
/-- Weak fairness of an infinite execution: every correct server eventually delivers the oldest
pending message of each link, and a client step that is continuously enabled is eventually taken
(the client's phase changes exactly at its own steps). -/
structure Fair (e : ℕ → State n V) : Prop where
  delivW : ∀ s ∉ B, ∀ i, ∃ j ≥ i, ((e j).srv s).wq = [] ∨
    ((e (j + 1)).srv s).wq.length < ((e j).srv s).wq.length
  delivR : ∀ s ∉ B, ∀ i, ∃ j ≥ i, ((e j).srv s).rq = [] ∨
    ((e (j + 1)).srv s).rq.length < ((e j).srv s).rq.length
  writer : ∀ i, ∃ j ≥ i, ¬ WEnabled t B (e j) ∨ (e (j + 1)).w ≠ (e j).w
  reader : ∀ i, ∃ j ≥ i, ¬ REnabled t B (e j) ∨ (e (j + 1)).r ≠ (e j).r

/-- `WEnabled` is exactly "some step of the writer is possible": it implies a `Step` changing the
writer's phase. -/
lemma writer_step_of_enabled (σ : State n V) (h : WEnabled t B σ) :
    ∃ ℓ σ', Step t B σ ℓ σ' ∧ σ'.w ≠ σ.w := by
  classical
  unfold WEnabled at h
  split at h
  · exact h.elim
  · rename_i v hw
    exact ⟨_, _, .endWrite σ v hw h, by simp [hw]⟩
  · rename_i v hw
    obtain ⟨Q, hQS, hQ⟩ := Finset.exists_subset_card_eq h
    have hacks : ∀ s ∈ Q, s ∉ B → (σ.srv s).wack = some (((σ.srv s).wack).getD none) := by
      intro s hs hsB
      have := (Finset.mem_filter.1 (hQS hs)).2
      rcases this with h' | h'
      · exact absurd h' hsB
      · cases hx : (σ.srv s).wack with
        | none => exact absurd hx h'
        | some x => rfl
    by_cases hc : ∃ w, 4 * t + 1 ≤ cnt Q (fun s => ((σ.srv s).wack).getD none) (some w)
    · exact ⟨_, _, .ackDone σ v hw Q _ hQ hacks hc, by simp [hw]⟩
    · exact ⟨_, _, .ackHelp σ v hw Q _ hQ hacks hc, by simp [hw]⟩
  · rename_i hw
    exact ⟨_, _, .endHelp σ hw h, by simp [hw]⟩

/-- `REnabled` is exactly "some step of the reader is possible". -/
lemma reader_step_of_enabled [Inhabited V] (σ : State n V) (h : REnabled t B σ) :
    ∃ ℓ σ', Step t B σ ℓ σ' ∧ σ'.r ≠ σ.r := by
  classical
  unfold REnabled at h
  split at h
  · exact h.elim
  · rename_i hr
    exact ⟨_, _, .endLoop σ hr h, by simp [hr]⟩
  · rename_i hr
    obtain ⟨Q, hQS, hQ⟩ := Finset.exists_subset_card_eq h
    have hreps : ∀ s ∈ Q, s ∉ B → (σ.srv s).rack = some (((σ.srv s).rack).getD default) := by
      intro s hs hsB
      have := (Finset.mem_filter.1 (hQS hs)).2
      rcases this with h' | h'
      · exact absurd h' hsB
      · cases hx : (σ.srv s).rack with
        | none => exact absurd hx h'
        | some x => rfl
    set reps := fun s => ((σ.srv s).rack).getD default
    by_cases hl : ∃ v, 2 * t + 1 ≤ cnt Q (fun s => (reps s).1) v
    · obtain ⟨v, hv⟩ := hl
      exact ⟨_, _, .retLast σ hr Q reps hQ hreps v hv, by simp [hr]⟩
    · by_cases hh : ∃ v, 2 * t + 1 ≤ cnt Q (fun s => (reps s).2) (some v)
      · obtain ⟨v, hv⟩ := hh
        exact ⟨_, _, .retHelp σ hr Q reps hQ hreps hl v hv, by simp [hr]⟩
      · exact ⟨_, _, .retry σ hr Q reps hQ hreps hl hh, by simp [hr]⟩

/-- Non-vacuity: a quiescent state (empty links, idle clients) repeated forever is a fair
execution. -/
example (σ : State n V) (hw : σ.w = .idle) (hr : σ.r = .idle)
    (hq : ∀ s, (σ.srv s).wq = [] ∧ (σ.srv s).rq = []) :
    Exec t B (fun _ => σ) (fun _ => .tau) ∧ Fair t B (fun _ => σ) :=
  ⟨fun _ => Or.inr ⟨rfl, rfl⟩,
   { delivW := fun s _ i => ⟨i, le_rfl, Or.inl (hq s).1⟩
     delivR := fun s _ i => ⟨i, le_rfl, Or.inl (hq s).2⟩
     writer := fun i => ⟨i, le_rfl, Or.inl (by simp [WEnabled, hw])⟩
     reader := fun i => ⟨i, le_rfl, Or.inl (by simp [REnabled, hr])⟩ }⟩

/-! ## Generic eventuality lemmas -/

omit [DecidableEq V] in
lemma ev_zero (μ : ℕ → ℕ) (i0 : ℕ) (hmono : ∀ j ≥ i0, μ (j + 1) ≤ μ j)
    (hprog : ∀ i ≥ i0, ∃ j ≥ i, μ j = 0 ∨ μ (j + 1) < μ j) : ∃ K ≥ i0, ∀ j ≥ K, μ j = 0 := by
  have mono : ∀ k ≥ i0, ∀ j ≥ k, μ j ≤ μ k := by
    intro k hk j hj
    induction j, hj using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih => exact (hmono j (by omega)).trans ih
  have key : ∀ m, ∀ i ≥ i0, μ i ≤ m → ∃ K ≥ i, μ K = 0 := by
    intro m
    induction m with
    | zero => intro i _ h; exact ⟨i, le_rfl, by omega⟩
    | succ m ih =>
      intro i hi h
      obtain ⟨j, hj, h0 | hlt⟩ := hprog i hi
      · exact ⟨j, hj, h0⟩
      · obtain ⟨K, hK, hK0⟩ := ih (j + 1) (by omega) (by have := mono i hi j hj; omega)
        exact ⟨K, by omega, hK0⟩
  obtain ⟨K, hK, hK0⟩ := key _ i0 le_rfl le_rfl
  exact ⟨K, hK, fun j hj => by have := mono K hK j hj; omega⟩

lemma exists_exit {P : ℕ → Prop} {i : ℕ} (hi : P i) (h : ¬ ∀ j ≥ i, P j) :
    ∃ k ≥ i, (∀ j, i ≤ j → j ≤ k → P j) ∧ ¬ P (k + 1) := by
  by_contra hc
  push Not at hc
  apply h
  have : ∀ k ≥ i, ∀ j, i ≤ j → j ≤ k → P j := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro j h1 h2; rwa [show j = i by omega]
    | succ k hk ih =>
      intro j h1 h2
      rcases (show j ≤ k ∨ j = k + 1 by omega) with h3 | rfl
      · exact ih j h1 h3
      · exact hc k hk ih
  exact fun j hj => this j hj j hj le_rfl

lemma ev_forall {P : Fin n → ℕ → Prop} (h : ∀ s ∉ B, ∃ K, ∀ j ≥ K, P s j) (i0 : ℕ) :
    ∃ K ≥ i0, ∀ j ≥ K, ∀ s ∉ B, P s j := by
  classical
  choose! K hK using h
  exact ⟨max i0 (Finset.univ.sup K), le_max_left _ _, fun j hj s hs =>
    hK s hs j (le_trans (Finset.le_sup (Finset.mem_univ s)) (le_trans (le_max_right _ _) hj))⟩

/-! ## Eventual delivery -/

section Exec

variable {e : ℕ → State n V} {lab : ℕ → Label V}

/-- If no `p`-message is broadcast by the writer after `i0`, every correct server eventually has
no pending `p`-message from the writer. -/
lemma ev_wq (hE : Exec t B e lab) (hF : Fair t B e) {s : Fin n} (hs : s ∉ B)
    (p : WMsg V → Bool) (i0 : ℕ) (hno : ∀ j ≥ i0, ∀ m, WBcast (e j) (e (j + 1)) m → p m = false) :
    ∃ K ≥ i0, ∀ j ≥ K, upto p ((e j).srv s).wq = 0 := by
  apply ev_zero (fun j => upto p ((e j).srv s).wq) i0
  · intro j hj
    rcases next_srv (hE j) s with h | h | h | ⟨m, hm, h⟩ | ⟨b, hb, h⟩ <;> simp only [h]
    · exact le_rfl
    · rw [Srv.deliverW_wq, upto_tail]; omega
    · simp
    · rw [Srv.bcastW_wq, upto_append _ _ _ (hno j hj m hm)]
    · simp
  · intro i _
    obtain ⟨j, hj, h0 | hlt⟩ := hF.delivW s hs i
    · exact ⟨j, hj, Or.inl (by simp [h0, upto])⟩
    · refine ⟨j, hj, ?_⟩
      rcases next_srv (hE j) s with h | h | h | ⟨m, hm, h⟩ | ⟨b, hb, h⟩ <;> rw [h] at hlt ⊢
      · omega
      · rw [Srv.deliverW_wq, upto_tail]; omega
      · simp at hlt
      · simp at hlt
      · simp at hlt

/-- If the reader broadcasts no `p`-message after `i0`, every correct server eventually has no
pending `p`-message from the reader. -/
lemma ev_rq (hE : Exec t B e lab) (hF : Fair t B e) {s : Fin n} (hs : s ∉ B)
    (p : Bool → Bool) (i0 : ℕ) (hno : ∀ j ≥ i0, ∀ b, RBcast (e j) (e (j + 1)) b → p b = false) :
    ∃ K ≥ i0, ∀ j ≥ K, upto p ((e j).srv s).rq = 0 := by
  apply ev_zero (fun j => upto p ((e j).srv s).rq) i0
  · intro j hj
    rcases next_srv (hE j) s with h | h | h | ⟨m, hm, h⟩ | ⟨b, hb, h⟩ <;> simp only [h]
    · exact le_rfl
    · simp
    · rw [Srv.deliverR_rq, upto_tail]; omega
    · simp
    · rw [Srv.bcastR_rq, upto_append _ _ _ (hno j hj b hb)]
  · intro i _
    obtain ⟨j, hj, h0 | hlt⟩ := hF.delivR s hs i
    · exact ⟨j, hj, Or.inl (by simp [h0, upto])⟩
    · refine ⟨j, hj, ?_⟩
      rcases next_srv (hE j) s with h | h | h | ⟨m, hm, h⟩ | ⟨b, hb, h⟩ <;> rw [h] at hlt ⊢
      · omega
      · simp at hlt
      · rw [Srv.deliverR_rq, upto_tail]; omega
      · simp at hlt
      · simp at hlt

lemma ev_wq_all (hE : Exec t B e lab) (hF : Fair t B e) (p : WMsg V → Bool) (i0 : ℕ)
    (hno : ∀ j ≥ i0, ∀ m, WBcast (e j) (e (j + 1)) m → p m = false) :
    ∃ K ≥ i0, ∀ j ≥ K, ∀ s ∉ B, upto p ((e j).srv s).wq = 0 :=
  ev_forall (fun _ hs => (ev_wq hE hF hs p i0 hno).imp fun _ hK => hK.2) i0

lemma ev_rq_all (hE : Exec t B e lab) (hF : Fair t B e) (p : Bool → Bool) (i0 : ℕ)
    (hno : ∀ j ≥ i0, ∀ b, RBcast (e j) (e (j + 1)) b → p b = false) :
    ∃ K ≥ i0, ∀ j ≥ K, ∀ s ∉ B, upto p ((e j).srv s).rq = 0 :=
  ev_forall (fun _ hs => (ev_rq hE hF hs p i0 hno).imp fun _ hK => hK.2) i0

lemma card_compl_ge (hB : B.card ≤ t) : n - 2 * t ≤ (Finset.univ.filter fun s => s ∉ B).card := by
  have : (Finset.univ.filter fun s => s ∉ B) = Bᶜ := by ext; simp
  rw [this, Finset.card_compl, Fintype.card_fin]
  omega

/-! ## Clients cannot stay in a phase forever -/

/-- During `write(v)`: the last pending writer message is `WRITE(v)`, or it has been delivered and
answered. -/
def WInv (v : V) (x : Server V) : Prop := (x.wq = [] ∧ x.wack ≠ none) ∨ ∃ q, x.wq = q ++ [.write v]

omit [DecidableEq V] in
lemma WInv_deliverW {v : V} {x : Server V} (h : WInv v x) : WInv v x.deliverW := by
  rcases h with ⟨h1, h2⟩ | ⟨q, hq⟩
  · left; simp only [Server.deliverW, h1]; exact ⟨trivial, h2⟩
  · rcases q with _ | ⟨y, q⟩
    · left; simp only [List.nil_append] at hq; simp [Server.deliverW, hq]
    · right; exact ⟨q, by rw [Srv.deliverW_wq, hq]; rfl⟩

lemma WInv_next {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ')
    (hno : ∀ m, ¬ WBcast σ σ' m) {v : V} (hI : ∀ s, WInv v (σ.srv s)) (s : Fin n) :
    WInv v (σ'.srv s) := by
  rcases next_srv h s with h | h | h | ⟨m, hm, h⟩ | ⟨b, hb, h⟩ <;> rw [h]
  · exact hI s
  · exact WInv_deliverW (hI s)
  · simpa [WInv] using hI s
  · exact absurd hm (hno m)
  · simpa [WInv] using hI s

/-- After the reader's first broadcast: a correct server that delivered the reader's current
broadcast has answered it. -/
def RInv (x : Server V) : Prop := x.rq = [] → x.rack ≠ none

omit [DecidableEq V] in
lemma RInv_deliverR {x : Server V} (h : RInv x) : RInv x.deliverR := by
  unfold RInv Server.deliverR
  split
  · exact h
  · intro hr; simp only at hr; simp [hr]

lemma RInv_next {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ')
    (hI : ∀ s, RInv (σ.srv s)) (s : Fin n) : RInv (σ'.srv s) := by
  rcases next_srv h s with h | h | h | ⟨m, hm, h⟩ | ⟨b, hb, h⟩ <;> rw [h]
  · exact hI s
  · simpa [RInv] using hI s
  · exact RInv_deliverR (hI s)
  · simpa [RInv] using hI s
  · simp [RInv]

lemma writer_stuck_bcast (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t) {i : ℕ}
    {P : WPhase V} (hP : (∃ v, P = .bcastWrite v) ∨ P = .bcastHelp)
    (hst : ∀ j ≥ i, (e j).w = P) : False := by
  have hno : ∀ j ≥ i, ∀ m, WBcast (e j) (e (j + 1)) m → (fun _ => true) m = false := by
    intro j hj m hm
    exact absurd (by rw [hst j hj, hst (j + 1) (by omega)]) hm.w_ne
  obtain ⟨K, hK, hK'⟩ := ev_wq_all hE hF _ i hno
  obtain ⟨j, hj, hen | hch⟩ := hF.writer K
  · apply hen
    have hsync : n - 2 * t ≤ syncW B (e j).srv := by
      unfold syncW
      have : (Finset.univ.filter fun s => s ∉ B ∧ ((e j).srv s).wq = []) =
          Finset.univ.filter fun s => s ∉ B := by
        ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
        exact fun hs => (upto_true _).1 (hK' j hj s hs)
      rw [this]; exact card_compl_ge hB
    rcases hP with ⟨v, rfl⟩ | rfl <;> simp [WEnabled, hst j (by omega), hsync]
  · exact hch (by rw [hst j (by omega), hst (j + 1) (by omega)])

lemma writer_stuck_wait (hE : Exec t B e lab) (hF : Fair t B e) {i : ℕ} {v : V}
    (hst : ∀ j ≥ i, (e j).w = .waitAck v) (hI : ∀ s, WInv v ((e i).srv s)) : False := by
  have hno' : ∀ j ≥ i, ∀ m, ¬ WBcast (e j) (e (j + 1)) m := by
    intro j hj m hm
    exact hm.w_ne (by rw [hst j hj, hst (j + 1) (by omega)])
  have hI' : ∀ j ≥ i, ∀ s, WInv v ((e j).srv s) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hI
    | succ j hj ih => exact WInv_next (hE j) (hno' j hj) ih
  obtain ⟨K, hK, hK'⟩ := ev_wq_all hE hF (fun _ => true) i (fun j hj m hm => absurd hm (hno' j hj m))
  obtain ⟨j, hj, hen | hch⟩ := hF.writer K
  · apply hen
    have : (Finset.univ.filter fun s => s ∈ B ∨ ((e j).srv s).wack ≠ none) = Finset.univ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      by_cases hs : s ∈ B
      · exact Or.inl hs
      · right
        have h0 := (upto_true _).1 (hK' j hj s hs)
        rcases hI' j (by omega) s with ⟨-, h⟩ | ⟨q, hq⟩
        · exact h
        · simp [h0] at hq
    simp only [WEnabled, hst j (by omega), this, Finset.card_univ, Fintype.card_fin]
    omega
  · exact hch (by rw [hst j (by omega), hst (j + 1) (by omega)])

lemma reader_stuck_bcast (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t) {i : ℕ}
    (hst : ∀ j ≥ i, (e j).r = .bcastLoop) : False := by
  have hno : ∀ j ≥ i, ∀ b, RBcast (e j) (e (j + 1)) b → (fun _ => true) b = false := by
    intro j hj b hb
    exact absurd (by rw [hst j hj, hst (j + 1) (by omega)]) hb.r_ne
  obtain ⟨K, hK, hK'⟩ := ev_rq_all hE hF _ i hno
  obtain ⟨j, hj, hen | hch⟩ := hF.reader K
  · apply hen
    have hsync : n - 2 * t ≤ syncR B (e j).srv := by
      unfold syncR
      have : (Finset.univ.filter fun s => s ∉ B ∧ ((e j).srv s).rq = []) =
          Finset.univ.filter fun s => s ∉ B := by
        ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_iff_left_iff_imp]
        exact fun hs => (upto_true _).1 (hK' j hj s hs)
      rw [this]; exact card_compl_ge hB
    simp [REnabled, hst j (by omega), hsync]
  · exact hch (by rw [hst j (by omega), hst (j + 1) (by omega)])

lemma reader_stuck_wait (hE : Exec t B e lab) (hF : Fair t B e) {i : ℕ}
    (hst : ∀ j ≥ i, (e j).r = .waitLoop) (hI : ∀ s, RInv ((e i).srv s)) : False := by
  have hno' : ∀ j ≥ i, ∀ b, ¬ RBcast (e j) (e (j + 1)) b := by
    intro j hj b hb
    exact hb.r_ne (by rw [hst j hj, hst (j + 1) (by omega)])
  have hI' : ∀ j ≥ i, ∀ s, RInv ((e j).srv s) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hI
    | succ j hj ih => exact RInv_next (hE j) ih
  obtain ⟨K, hK, hK'⟩ := ev_rq_all hE hF (fun _ => true) i (fun j hj b hb => absurd hb (hno' j hj b))
  obtain ⟨j, hj, hen | hch⟩ := hF.reader K
  · apply hen
    have : (Finset.univ.filter fun s => s ∈ B ∨ ((e j).srv s).rack ≠ none) = Finset.univ := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      by_cases hs : s ∈ B
      · exact Or.inl hs
      · exact Or.inr (hI' j (by omega) s ((upto_true _).1 (hK' j hj s hs)))
    simp only [REnabled, hst j (by omega), this, Finset.card_univ, Fintype.card_fin]
    omega
  · exact hch (by rw [hst j (by omega), hst (j + 1) (by omega)])

/-- A `write(v)` whose `WRITE(v)` is broadcast at step `i` reaches its collection (line 02), and
later leaves it. -/
lemma write_progress (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t) {i : ℕ} {v : V}
    (hw : WBcast (e i) (e (i + 1)) (.write v)) :
    ∃ k > i, (e k).w = .waitAck v ∧ (e (k + 1)).w ≠ .waitAck v := by
  have hw1 : (e (i + 1)).w = .bcastWrite v := by
    rcases hw with ⟨v', -, h2, hm⟩ | ⟨v', -, -, hm⟩
    · cases hm; exact h2
    · cases hm
  have hI1 : ∀ s, WInv v ((e (i + 1)).srv s) := fun s =>
    Or.inr ⟨_, by rw [next_wbcast (hE i) hw s]; rfl⟩
  obtain ⟨k1, hk1, hP1, hn1⟩ := exists_exit (P := fun j => (e j).w = .bcastWrite v) hw1
    (fun h => writer_stuck_bcast hE hF hB (Or.inl ⟨v, rfl⟩) h)
  obtain ⟨hw2, hsrv⟩ := next_w_bcastWrite (hE k1) (hP1 k1 hk1 le_rfl)
    (by rw [hP1 k1 hk1 le_rfl]; exact hn1)
  have hI2 : ∀ j, i + 1 ≤ j → j ≤ k1 → ∀ s, WInv v ((e j).srv s) := by
    intro j hj hjk
    induction j, hj using Nat.le_induction with
    | base => exact hI1
    | succ j hj ih =>
      refine WInv_next (hE j) (fun m hm => ?_) (ih (by omega))
      rcases hm.w_src with h | ⟨u, h⟩ <;> rw [hP1 j hj (by omega)] at h <;> cases h
  have hI3 : ∀ s, WInv v ((e (k1 + 1)).srv s) := by
    rw [hsrv]; exact hI2 k1 hk1 le_rfl
  obtain ⟨k, hk, hPk, hnk⟩ := exists_exit (P := fun j => (e j).w = .waitAck v) hw2
    (fun h => writer_stuck_wait hE hF h hI3)
  exact ⟨k, by omega, hPk k hk le_rfl, hnk⟩

/-- **Lemma 1** of [Bonomi–Dolev–Potop-Butucaru–Raynal, PODC 2015] (termination of `write()`,
Fig. 2): in a fair execution with at most `t` Byzantine servers, every invocation of `write(v)` is
followed by its return. -/
theorem lemma1_write_terminates (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t)
    {a : ℕ} {v : V} (ha : lab a = .invWrite v) : ∃ j > a, lab j = .retWrite := by
  have hw : WBcast (e a) (e (a + 1)) (.write v) := by
    have := hE a; rw [ha] at this; exact next_invWrite this
  obtain ⟨k, hk, hwk, hnk⟩ := write_progress hE hF hB hw
  obtain ⟨Q, acks, -, -, ⟨-, hl, -⟩ | ⟨-, hbh⟩⟩ :=
    next_w_waitAck (hE k) hwk (by rw [hwk]; exact hnk)
  · exact ⟨k, hk, hl⟩
  · obtain ⟨k2, hk2, hP2, hn2⟩ := exists_exit (P := fun j => (e j).w = .bcastHelp) hbh
      (fun h => writer_stuck_bcast hE hF hB (Or.inr rfl) h)
    exact ⟨k2, by omega, next_w_bcastHelp (hE k2) (hP2 k2 hk2 le_rfl)
      (by rw [hP2 k2 hk2 le_rfl]; exact hn2)⟩

/-! ## Lemma 2 -/

lemma card_correct_ge (hB : B.card ≤ t) (Q : Finset (Fin n)) (hQ : Q.card = n - t) :
    n - 2 * t ≤ (Q.filter fun s => s ∉ B).card := by
  have h1 := Finset.card_filter_add_card_filter_not (s := Q) (fun s => s ∈ B)
  have h2 : (Q.filter fun s => s ∈ B).card ≤ B.card :=
    Finset.card_le_card (fun s hs => (Finset.mem_filter.1 hs).2)
  omega

lemma correct_le_cnt {α : Type} [DecidableEq α] (Q : Finset (Fin n)) (f : Fin n → α) (x : α)
    (h : ∀ s ∈ Q, s ∉ B → f s = x) : (Q.filter fun s => s ∉ B).card ≤ cnt Q f x := by
  unfold cnt
  apply Finset.card_le_card
  intro s hs
  rw [Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, h s hs.1 hs.2⟩

section Read

variable {a : ℕ}

lemma read_r_ne_idle (hE : Exec t B e lab) (ha : lab a = .invRead)
    (hno : ∀ j > a, ∀ v, lab j ≠ .retRead v) : ∀ j ≥ a + 1, (e j).r ≠ .idle := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have := hE a; rw [ha] at this
    rcases next_invRead this with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> simp [h]
  | succ j hj ih =>
    intro h
    obtain ⟨v, hv⟩ := next_r_idle (hE j) ih h
    exact hno j (by omega) v hv

lemma read_RInv (hE : Exec t B e lab) (ha : lab a = .invRead) :
    ∀ j ≥ a + 1, ∀ s, RInv ((e j).srv s) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    have := hE a; rw [ha] at this
    intro s
    rw [next_rbcast this (next_invRead this) s]
    simp [RInv]
  | succ j hj ih => exact RInv_next (hE j) ih

lemma read_retries (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t)
    (ha : lab a = .invRead) (hno : ∀ j > a, ∀ v, lab j ≠ .retRead v) :
    ∀ T, ∃ m ≥ T, (e m).r = .waitLoop ∧ (e (m + 1)).r = .bcastLoop := by
  have waitCase : ∀ i ≥ a + 1, (e i).r = .waitLoop →
      ∃ m ≥ i, (e m).r = .waitLoop ∧ (e (m + 1)).r = .bcastLoop := by
    intro i hi hw
    obtain ⟨k, hk, hP, hn⟩ := exists_exit (P := fun j => (e j).r = .waitLoop) hw
      (fun h => reader_stuck_wait hE hF h (read_RInv hE ha i hi))
    rcases next_r_waitLoop (hE k) (hP k hk le_rfl) (by rw [hP k hk le_rfl]; exact hn) with
      ⟨v, hv⟩ | h
    · exact absurd hv (hno k (by omega) v)
    · exact ⟨k, hk, hP k hk le_rfl, h⟩
  intro T
  have hi := read_r_ne_idle hE ha hno (max T (a + 1)) (le_max_right _ _)
  cases hr : (e (max T (a + 1))).r with
  | idle => exact absurd hr hi
  | bcastLoop =>
    obtain ⟨k, hk, hP, hn⟩ := exists_exit (P := fun j => (e j).r = .bcastLoop) hr
      (fun h => reader_stuck_bcast hE hF hB h)
    have := next_r_bcastLoop (hE k) (hP k hk le_rfl) (by rw [hP k hk le_rfl]; exact hn)
    obtain ⟨m, hm, h⟩ := waitCase (k + 1) (by omega) this
    exact ⟨m, by omega, h⟩
  | waitLoop =>
    obtain ⟨m, hm, h⟩ := waitCase _ (le_max_right _ _) hr
    exact ⟨m, by omega, h⟩

/-- All reply slots are cleared by a retry (a `READ(false)` broadcast). -/
lemma rack_none_of_retry (hE : Exec t B e lab) {m : ℕ} (hm : (e m).r = .waitLoop)
    (hm' : (e (m + 1)).r = .bcastLoop) (s : Fin n) : ((e (m + 1)).srv s).rack = none := by
  rw [next_rbcast (hE m) (Or.inr ⟨hm, hm', rfl⟩) s]; rfl

lemma lastW_next {σ σ' : State n V} {ℓ : Label V} (h : Next t B σ ℓ σ')
    (hno : ∀ v, ¬ WBcast σ σ' (.write v)) (s : Fin n) :
    Srv.lastW (σ'.srv s) = Srv.lastW (σ.srv s) := by
  rcases next_srv h s with h | h | h | ⟨m, hm, h⟩ | ⟨b, hb, h⟩ <;> rw [h]
  · exact Srv.lastW_deliverW _
  · exact Srv.lastW_deliverR _
  · cases m with
    | write v => exact absurd hm (hno v)
    | newHelp v => exact Srv.lastW_bcastW _ _
  · rfl

/-- Lemma 2, case where the writer eventually stops writing. -/
lemma read_caseF (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t) (hn : 4 * t < n)
    (hret : ∀ T, ∃ m ≥ T, (e m).r = .waitLoop ∧ (e (m + 1)).r = .bcastLoop)
    {i0 : ℕ} {v0 : V} (hw0 : WBcast (e i0) (e (i0 + 1)) (.write v0))
    {T : ℕ} (hT : ∀ j ≥ T, ∀ v, ¬ WBcast (e j) (e (j + 1)) (.write v)) : False := by
  -- all servers agree on their eventual `last_val` after the first write
  have hagree : ∀ j ≥ i0 + 1, ∃ c, ∀ s, Srv.lastW ((e j).srv s) = c := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact ⟨v0, fun s => by rw [next_wbcast (hE i0) hw0 s, Srv.lastW_bcastW]⟩
    | succ j hj ih =>
      by_cases hb : ∃ v, WBcast (e j) (e (j + 1)) (.write v)
      · obtain ⟨v, hv⟩ := hb
        exact ⟨v, fun s => by rw [next_wbcast (hE j) hv s, Srv.lastW_bcastW]⟩
      · push Not at hb
        obtain ⟨c, hc⟩ := ih
        exact ⟨c, fun s => by rw [lastW_next (hE j) hb s, hc]⟩
  obtain ⟨c, hc⟩ := hagree (max T (i0 + 1)) (le_max_right _ _)
  have hc' : ∀ j ≥ max T (i0 + 1), ∀ s, Srv.lastW ((e j).srv s) = c := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact hc
    | succ j hj ih => intro s; rw [lastW_next (hE j) (hT j (by omega)) s, ih s]
  obtain ⟨K, hK, hK'⟩ := ev_wq_all hE hF Srv.isWrite (max T (i0 + 1)) (by
    intro j hj m hm
    cases m with
    | write v => exact absurd hm (hT j (by omega) v)
    | newHelp v => rfl)
  have hlast : ∀ j ≥ K, ∀ s ∉ B, ((e j).srv s).last = c := fun j hj s hs => by
    rw [← Srv.lastW_of_noWrite _ (hK' j hj s hs), hc' j (by omega) s]
  -- after a retry following `K`, every correct reply carries `last_val = c`
  obtain ⟨m, hm, hm1, hm2⟩ := hret K
  have hRL : ∀ j ≥ m + 1, ∀ s ∉ B, ∀ p, ((e j).srv s).rack = some p → p.1 = c := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro s _ p hp; rw [rack_none_of_retry hE hm1 hm2 s] at hp; cases hp
    | succ j hj ih =>
      intro s hs p hp
      rcases next_srv (hE j) s with h | h | h | ⟨w, -, h⟩ | ⟨b, -, h⟩ <;> rw [h] at hp
      · exact ih s hs p hp
      · rw [Srv.deliverW_rack] at hp; exact ih s hs p hp
      · rcases Srv.deliverR_rack ((e j).srv s) with h' | h' <;> rw [h'] at hp
        · exact ih s hs p hp
        · cases hp; exact hlast j (by omega) s hs
      · exact ih s hs p hp
      · cases hp
  obtain ⟨m', hm', hm1', hm2'⟩ := hret (m + 1)
  obtain ⟨Q, reps, hQ, hreps, hl, -⟩ := next_retry (hE m') hm1' hm2'
  apply hl
  refine ⟨c, ?_⟩
  have := card_correct_ge hB Q hQ
  have := correct_le_cnt Q (fun s => (reps s).1) c
    (fun s hsQ hs => hRL m' hm' s hs _ (hreps s hsQ hs))
  omega

/-- Invariant after a `NEW_HELP_VAL(z)` broadcast (once no `READ(true)` is pending): the eventual
`helping_val` is `z` and the writer's reply slot holds `z` if set. -/
def HInv (z : V) (x : Server V) : Prop :=
  Srv.helpW x = some z ∧ (x.wack = none ∨ x.wack = some (some z))

/-- Lemma 2, case where the writer writes forever. -/
lemma read_caseI (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t) (hn : 6 * t < n)
    (ha : lab a = .invRead) (hno : ∀ j > a, ∀ v, lab j ≠ .retRead v)
    (hret : ∀ T, ∃ m ≥ T, (e m).r = .waitLoop ∧ (e (m + 1)).r = .bcastLoop)
    (hinf : ∀ T, ∃ j ≥ T, ∃ v, WBcast (e j) (e (j + 1)) (.write v)) : False := by
  have hr := read_r_ne_idle hE ha hno
  -- T1: no `READ(true)` pending at correct servers any more
  obtain ⟨T1, hT1, hT1'⟩ := ev_rq_all hE hF (fun b => b) (a + 1) (by
    intro j hj b hb
    rcases hb with ⟨h, -, -⟩ | ⟨-, -, rfl⟩
    · exact absurd h (hr j hj)
    · rfl)
  have hhd : ∀ j ≥ T1, ∀ s ∉ B, ((e j).srv s).rq.headD false = false :=
    fun j hj s hs => Srv.headD_of_upto _ (hT1' j hj s hs)
  -- Claim A: after `T1`, at most one `NEW_HELP_VAL` broadcast
  have hA : ∀ h ≥ T1, ∀ z, WBcast (e h) (e (h + 1)) (.newHelp z) →
      ∀ j > h, ∀ z', ¬ WBcast (e j) (e (j + 1)) (.newHelp z') := by
    intro h hh z hz
    have noHelp : ∀ j, (∀ s ∉ B, HInv z ((e j).srv s)) → ∀ z',
        ¬ WBcast (e j) (e (j + 1)) (.newHelp z') := by
      intro j hI z' hb
      rcases hb with ⟨v, -, -, hm⟩ | ⟨v, hw, hw', -⟩
      · cases hm
      obtain ⟨Q, acks, hQ, hacks, ⟨-, -, hid⟩ | ⟨hc, -⟩⟩ :=
        next_w_waitAck (hE j) hw (by rw [hw, hw']; simp)
      · rw [hw'] at hid; cases hid
      apply hc
      refine ⟨z, ?_⟩
      have := card_correct_ge hB Q hQ
      have := correct_le_cnt Q acks (some z) (fun s hsQ hs => by
        have h1 := hacks s hsQ hs
        rcases (hI s hs).2 with h2 | h2 <;> rw [h2] at h1
        · cases h1
        · exact (Option.some.inj h1).symm)
      omega
    have hI : ∀ j ≥ h + 1, ∀ s ∉ B, HInv z ((e j).srv s) := by
      intro j hj
      induction j, hj using Nat.le_induction with
      | base =>
        intro s _
        rw [next_wbcast (hE h) hz s]
        exact ⟨Srv.helpW_bcastW_newHelp _ _, Or.inl rfl⟩
      | succ j hj ih =>
        intro s hs
        have hnb := noHelp j ih
        obtain ⟨ih1, ih2⟩ := ih s hs
        rcases next_srv (hE j) s with h' | h' | h' | ⟨m, hm, h'⟩ | ⟨b, -, h'⟩ <;> rw [h']
        · exact ih s hs
        · refine ⟨by rw [Srv.helpW_deliverW, ih1], ?_⟩
          rcases Srv.deliverW_wack ((e j).srv s) with h2 | ⟨h2, h3, -⟩
          · rw [h2]; exact ih2
          · rw [h2, ← h3, ih1]; exact Or.inr rfl
        · refine ⟨by rw [Srv.helpW_deliverR _ (hhd j (by omega) s hs), ih1], ?_⟩
          rw [Srv.deliverR_wack]; exact ih2
        · cases m with
          | write v => exact ⟨by rw [Srv.helpW_bcastW_write, ih1], Or.inl rfl⟩
          | newHelp v => exact absurd hm (hnb v)
        · exact ⟨by rw [Srv.helpW_bcastR, ih1], ih2⟩
    intro j hj z'
    exact noHelp j (hI j hj) z'
  obtain ⟨T3', hT3', hT3''⟩ : ∃ T3' ≥ T1, ∀ j ≥ T3', ∀ z, ¬ WBcast (e j) (e (j + 1)) (.newHelp z) := by
    by_cases hex : ∃ h ≥ T1, ∃ z, WBcast (e h) (e (h + 1)) (.newHelp z)
    · obtain ⟨h, hh, z, hz⟩ := hex
      exact ⟨h + 1, by omega, fun j hj => hA h hh z hz j (by omega)⟩
    · push Not at hex
      exact ⟨T1, le_rfl, hex⟩
  -- T3: no `NEW_HELP_VAL` pending at correct servers any more; helping values are frozen
  obtain ⟨T3, hT3, hT3'⟩ := ev_wq_all hE hF Srv.isHelp T3' (by
    intro j hj m hm
    cases m with
    | write v => rfl
    | newHelp v => exact absurd hm (hT3'' j hj v))
  have hfrozen : ∀ j ≥ T3, ∀ s ∉ B, ((e j).srv s).help = ((e T3).srv s).help := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro s _; rfl
    | succ j hj ih =>
      intro s hs
      rw [← ih s hs]
      rcases next_srv (hE j) s with h' | h' | h' | ⟨m, -, h'⟩ | ⟨b, -, h'⟩ <;> rw [h']
      · exact Srv.deliverW_help_of_noHelp _ (hT3' j hj s hs)
      · rw [Srv.deliverR_help, hhd j (by omega) s hs]; rfl
      · rfl
      · rfl
  set hv : Fin n → Option V := fun s => ((e T3).srv s).help with hv_def
  -- a write invoked after `T3` returns at line 03 with `4t + 1` acks of some `w`
  obtain ⟨i, hi, v, hiw⟩ := hinf T3
  have hWI : ∀ j ≥ i + 1, ∀ s ∉ B, ((e j).srv s).wack = none ∨ ((e j).srv s).wack = some (hv s) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro s _; rw [next_wbcast (hE i) hiw s]; exact Or.inl rfl
    | succ j hj ih =>
      intro s hs
      rcases next_srv (hE j) s with h' | h' | h' | ⟨m, -, h'⟩ | ⟨b, -, h'⟩ <;> rw [h']
      · exact ih s hs
      · rcases Srv.deliverW_wack ((e j).srv s) with h2 | ⟨h2, -, -⟩
        · rw [h2]; exact ih s hs
        · rw [h2, hfrozen j (by omega) s hs]; exact Or.inr rfl
      · rw [Srv.deliverR_wack]; exact ih s hs
      · exact Or.inl rfl
      · exact ih s hs
  obtain ⟨k, hk, hwk, hnk⟩ := write_progress hE hF hB hiw
  obtain ⟨Q, acks, -, hacks, ⟨⟨w, hcw⟩, -⟩ | ⟨-, hbh⟩⟩ :=
    next_w_waitAck (hE k) hwk (by rw [hwk]; exact hnk)
  swap
  · exact hT3'' k (by omega) v (Or.inr ⟨v, hwk, hbh, rfl⟩)
  set C := Finset.univ.filter fun s => s ∉ B ∧ hv s = some w with hC
  have hCcard : 3 * t + 1 ≤ C.card := by
    have hsub : (Q.filter fun s => acks s = some w) ⊆ B ∪ C := by
      intro s hs
      rw [Finset.mem_filter] at hs
      rw [Finset.mem_union]
      by_cases hsB : s ∈ B
      · exact Or.inl hsB
      · right
        have h1 := hacks s hs.1 hsB
        rcases hWI k (by omega) s hsB with h2 | h2 <;> rw [h2] at h1
        · cases h1
        · have h3 := Option.some.inj h1
          simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hsB, h3.trans hs.2⟩
    have := (Finset.card_le_card hsub).trans (Finset.card_union_le B C)
    unfold cnt at hcw
    omega
  -- a read iteration started after `T3` then sees `2t + 1` helping values `w`
  obtain ⟨m, hm, hm1, hm2⟩ := hret T3
  have hRH : ∀ j ≥ m + 1, ∀ s ∉ B, ∀ p, ((e j).srv s).rack = some p → p.2 = hv s := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => intro s _ p hp; rw [rack_none_of_retry hE hm1 hm2 s] at hp; cases hp
    | succ j hj ih =>
      intro s hs p hp
      rcases next_srv (hE j) s with h | h | h | ⟨u, -, h⟩ | ⟨b, -, h⟩ <;> rw [h] at hp
      · exact ih s hs p hp
      · rw [Srv.deliverW_rack] at hp; exact ih s hs p hp
      · rcases Srv.deliverR_rack ((e j).srv s) with h' | h' <;> rw [h'] at hp
        · exact ih s hs p hp
        · cases hp
          rw [hhd j (by omega) s hs]
          exact hfrozen j (by omega) s hs
      · exact ih s hs p hp
      · cases hp
  obtain ⟨m', hm', hm1', hm2'⟩ := hret (m + 1)
  obtain ⟨Q', reps, hQ', hreps, -, hh⟩ := next_retry (hE m') hm1' hm2'
  apply hh
  refine ⟨w, ?_⟩
  have hsub : Q' ∩ C ⊆ Q'.filter fun s => (reps s).2 = some w := by
    intro s hs
    rw [Finset.mem_inter] at hs
    have hsC := hs.2
    simp only [hC, Finset.mem_filter, Finset.mem_univ, true_and] at hsC
    rw [Finset.mem_filter]
    exact ⟨hs.1, by rw [hRH m' hm' s hsC.1 _ (hreps s hs.1 hsC.1)]; exact hsC.2⟩
  have h1 := Finset.card_union_add_card_inter Q' C
  have h2 : (Q' ∪ C).card ≤ n := by simpa using Finset.card_le_univ (Q' ∪ C)
  have h3 := Finset.card_le_card hsub
  show 2 * t + 1 ≤ (Q'.filter fun s => (reps s).2 = some w).card
  omega

/-- **Lemma 2** of [Bonomi–Dolev–Potop-Butucaru–Raynal, PODC 2015] (termination of `read()`,
Fig. 2): in a fair execution with at most `t` Byzantine servers, `6t < n` (the paper assumes
`8t < n`), and at least one invocation of `write()` (the paper's assumption (b)), every invocation
of `read()` is followed by a return. -/
theorem lemma2_read_terminates (hE : Exec t B e lab) (hF : Fair t B e) (hB : B.card ≤ t)
    (hn : 6 * t < n) (hw : ∃ i v, lab i = .invWrite v) (ha : lab a = .invRead) :
    ∃ j > a, ∃ v, lab j = .retRead v := by
  by_contra hno
  push Not at hno
  have hret := read_retries hE hF hB ha hno
  by_cases hfin : ∃ T, ∀ j ≥ T, ∀ v, ¬ WBcast (e j) (e (j + 1)) (.write v)
  · obtain ⟨T, hT⟩ := hfin
    obtain ⟨i0, v0, h0⟩ := hw
    have hw0 : WBcast (e i0) (e (i0 + 1)) (.write v0) := by
      have := hE i0; rw [h0] at this; exact next_invWrite this
    exact read_caseF hE hF hB (by omega) hret hw0 hT
  · push Not at hfin
    exact read_caseI hE hF hB hn ha hno hret hfin

end Read

end Exec

end Podc.StabilizingByzStorage.Regular
