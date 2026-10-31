import Papers.PODC2014.SignatureFreeBA.Model

/-!
# One round of the attack, as a finite (decidable) computation

Mostéfaoui, Moumen, Raynal, PODC 2014: the counterexample to Lemma 5 for `n = 4`, `t = 1`.
Processes `0, 1, 2` are correct, `3` is Byzantine.

This file describes the messages of *one* round `r` of the algorithm (Figures 1–2) and the
adversary's schedule for that round as a finite state machine whose guards are decidable, so
that the whole schedule is checked by `decide`. `Counterexample.lean` embeds it into the
asynchronous model `Cslib.Byzantine.AsyncBroadcast` and glues the rounds together.

At the start of a round, processes `0, 1` have estimate `a` and process `2` has `¬a`. The
schedule (the coin of the round is `s`, revealed when process `0` calls `random()`):
1. `3` sends `B_VAL(¬a)` to everybody; `0`, `1`, `2` all echo the value they lack, so both values
   reach every `bin_values`, but in a chosen order;
2. `0` gets `bin_values = {a}` first and broadcasts `AUX(a)`; `1` gets `{¬a}` first and broadcasts
   `AUX(¬a)`;
3. `0` receives `AUX(a)` (own), `AUX(¬a)` (from `1`), `AUX(a)` (from `3`): `values = {0, 1}`; it
   calls `random()` and adopts `s`;
4. `1` gets `bin_values = {0, 1}`, receives the same three `AUX` values, calls `random()` and
   adopts `s`. **Only now does the adversary use `s`** (with a threshold coin that needs
   `n − t = 3` shares, the shares of `0`, `1` and `3` reveal it);
5. `2` gets `bin_values = {¬s}` first, broadcasts `AUX(¬s)`, and receives `AUX(¬s)` from itself,
   from `3` and from the one of `0`, `1` that sent `¬s`: `values = {¬s}`, but the coin is `s`, so
   it does not decide and adopts `¬s`;
6. all remaining messages of the round are delivered.

The next round starts with `0, 1` at `s` and `2` at `¬s`: the same situation.
-/

namespace Podc.SignatureFreeBA.Local

/-- Messages of one round: `bval v tag` (`B_VAL[r](v)`) and `aux v` (`AUX[r](v)`). -/
inductive LM
  | bval (v : Bool) (d : Option Bool)
  | aux (v : Bool)
  deriving DecidableEq, Fintype

/-- The state of one round: broadcasts, receptions (`rcv q s m`: `q` received `m` from `s`),
and the estimates for the next round computed in this round (`nxt p = some (v, single)`). -/
structure LS where
  sent : Fin 4 → LM → Bool
  rcv : Fin 4 → Fin 4 → LM → Bool
  nxt : Fin 4 → Option (Bool × Bool)

/-- The round starts: processes `0, 1` with estimate `a` (tag `false`), process `2` with `¬a`
(tag `d2`). -/
def start (a d2 : Bool) : LS where
  sent p m := match p, m with
    | 0, .bval v (some false) => v == a
    | 1, .bval v (some false) => v == a
    | 2, .bval v (some d) => v == !a && d == d2
    | _, _ => false
  rcv _ _ _ := false
  nxt _ := none

/-- Events of the round. -/
inductive LE
  | dlv (q s : Fin 4) (m : LM)
  | inj (q : Fin 4) (m : LM)
  | echo (p : Fin 4) (v : Bool)
  | aux (p : Fin 4) (w : Bool)
  | est (p : Fin 4) (V : Finset Bool)
  | skip

/-- Number of processes from which `p` received `B_VAL(v)`. -/
def lcnt (ℓ : LS) (p : Fin 4) (v : Bool) : ℕ :=
  (Finset.univ.filter fun s => ∃ d, ℓ.rcv p s (.bval v d) = true).card

/-- `v ∈ bin_values` at `p` (`2t + 1 = 3`). -/
def lbin (ℓ : LS) (p : Fin 4) (v : Bool) : Prop := 3 ≤ lcnt ℓ p v

/-- The predicate of line 05 at `p` with `values = V` (`n − t = 3`). -/
def lquorum (ℓ : LS) (p : Fin 4) (V : Finset Bool) : Prop :=
  ∃ (S : Finset (Fin 4)) (f : Fin 4 → Bool), S.card = 3 ∧
    (∀ s ∈ S, ℓ.rcv p s (.aux (f s)) = true ∧ lbin ℓ p (f s)) ∧ S.image f = V

/-- `t + 1 = 2` copies of `B_VAL(v)` (the echo threshold). -/
def lecho (ℓ : LS) (p : Fin 4) (v : Bool) : Prop := 2 ≤ lcnt ℓ p v

/-! Fast decision procedures (the kernel evaluates these instead of `Finset` operations). -/

/-- `p` received `B_VAL(v)` from `s`. -/
def hasB (ℓ : LS) (p s : Fin 4) (v : Bool) : Bool :=
  ℓ.rcv p s (.bval v none) || ℓ.rcv p s (.bval v (some false)) || ℓ.rcv p s (.bval v (some true))

/-- `lcnt` as an explicit sum. -/
def lcntF (ℓ : LS) (p : Fin 4) (v : Bool) : ℕ :=
  (if hasB ℓ p 0 v then 1 else 0) + (if hasB ℓ p 1 v then 1 else 0) +
    (if hasB ℓ p 2 v then 1 else 0) + (if hasB ℓ p 3 v then 1 else 0)

theorem lcnt_eq (ℓ : LS) (p : Fin 4) (v : Bool) : lcnt ℓ p v = lcntF ℓ p v := by
  unfold lcnt lcntF
  rw [Finset.card_filter, Fin.sum_univ_four]
  have h : ∀ s, (∃ d, ℓ.rcv p s (.bval v d) = true) ↔ hasB ℓ p s v = true := by
    intro s
    simp only [hasB, Option.exists, Bool.exists_bool, Bool.or_eq_true]
    tauto
  simp only [h]

instance (ℓ : LS) (p : Fin 4) (v : Bool) : Decidable (lbin ℓ p v) :=
  decidable_of_iff (3 ≤ lcntF ℓ p v) (by rw [lbin, lcnt_eq])

instance (ℓ : LS) (p : Fin 4) (v : Bool) : Decidable (lecho ℓ p v) :=
  decidable_of_iff (2 ≤ lcntF ℓ p v) (by rw [lecho, lcnt_eq])

/-- Admissible senders `Fin 4 \ {x}` with values `f` for line 05. -/
def QF (ℓ : LS) (p x : Fin 4) (f : Fin 4 → Bool) : Prop :=
  ∀ s : Fin 4, s ≠ x → ℓ.rcv p s (.aux (f s)) = true ∧ 3 ≤ lcntF ℓ p (f s)

/-- The values of `f` on `Fin 4 \ {x}`. -/
def ImgF (x : Fin 4) (f : Fin 4 → Bool) (v : Bool) : Prop := ∃ s : Fin 4, s ≠ x ∧ f s = v

instance (ℓ : LS) (p x : Fin 4) (f : Fin 4 → Bool) : Decidable (QF ℓ p x f) := by
  unfold QF; infer_instance

instance (x : Fin 4) (f : Fin 4 → Bool) (v : Bool) : Decidable (ImgF x f v) := by
  unfold ImgF; infer_instance

theorem fun_four (f : Fin 4 → Bool) : ![f 0, f 1, f 2, f 3] = f := by
  funext s; fin_cases s <;> rfl

theorem card_three (S : Finset (Fin 4)) (h : S.card = 3) : ∃ x, ∀ s, s ∈ S ↔ s ≠ x := by
  have h1 : Sᶜ.card = 1 := by rw [Finset.card_compl, h]; rfl
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h1
  refine ⟨x, fun s => ?_⟩
  rw [← Finset.notMem_compl, hx, Finset.mem_singleton]

theorem lquorum_iff (ℓ : LS) (p : Fin 4) (V : Finset Bool) :
    lquorum ℓ p V ↔ ∃ x : Fin 4, ∃ b0 b1 b2 b3 : Bool, QF ℓ p x ![b0, b1, b2, b3] ∧
      ∀ v, v ∈ V ↔ ImgF x ![b0, b1, b2, b3] v := by
  constructor
  · rintro ⟨S, f, hS, hf, rfl⟩
    obtain ⟨x, hx⟩ := card_three S hS
    refine ⟨x, f 0, f 1, f 2, f 3, ?_, ?_⟩
    · rw [fun_four]
      intro s hs
      have := hf s ((hx s).2 hs)
      exact ⟨this.1, by rw [← lcnt_eq]; exact this.2⟩
    · intro v
      rw [fun_four, Finset.mem_image]
      simp only [ImgF, hx]
  · rintro ⟨x, b0, b1, b2, b3, hQ, hV⟩
    refine ⟨Finset.univ.erase x, ![b0, b1, b2, b3], by simp, fun s hs => ?_, ?_⟩
    · have := hQ s (Finset.ne_of_mem_erase hs)
      exact ⟨this.1, by unfold lbin; rw [lcnt_eq]; exact this.2⟩
    · ext v
      rw [hV, Finset.mem_image]
      simp only [ImgF, Finset.mem_erase, Finset.mem_univ, and_true]

instance (ℓ : LS) (p : Fin 4) (V : Finset Bool) : Decidable (lquorum ℓ p V) :=
  decidable_of_iff _ (lquorum_iff ℓ p V).symm

/-- Guards (`t = 1`, the Byzantine process is `3`). -/
def guard (ℓ : LS) : LE → Prop
  | .dlv _ s m => s ≠ 3 ∧ ℓ.sent s m = true
  | .inj _ _ => True
  | .echo p v => p ≠ 3 ∧ lecho ℓ p v ∧ ∀ d, ℓ.sent p (.bval v d) = false
  | .aux p w => p ≠ 3 ∧ (∃ v d, ℓ.sent p (.bval v (some d)) = true) ∧ lbin ℓ p w ∧
      ∀ w', ℓ.sent p (.aux w') = false
  | .est p V => p ≠ 3 ∧ (∃ w, ℓ.sent p (.aux w) = true) ∧ ℓ.nxt p = none ∧ lquorum ℓ p V
  | .skip => True

instance (ℓ : LS) (e : LE) : Decidable (guard ℓ e) := by
  cases e <;> unfold guard <;> infer_instance

/-- Effect of an event (the coin of the round is `s`). -/
def step (s : Bool) (ℓ : LS) : LE → LS
  | .dlv q s' m => { ℓ with rcv := fun a b c => (a == q && b == s' && c == m) || ℓ.rcv a b c }
  | .inj q m => { ℓ with rcv := fun a b c => (a == q && b == 3 && c == m) || ℓ.rcv a b c }
  | .echo p v => { ℓ with sent := fun a c => (a == p && c == .bval v none) || ℓ.sent a c }
  | .aux p w => { ℓ with sent := fun a c => (a == p && c == .aux w) || ℓ.sent a c }
  | .est p V => { ℓ with nxt := fun a => if a = p then some (nextEst V s) else ℓ.nxt a }
  | .skip => ℓ

/-- Run a list of events. -/
def run (s : Bool) (ℓ : LS) : List LE → LS
  | [] => ℓ
  | e :: es => run s (step s ℓ e) es

/-- All events of the list are enabled when they occur. -/
def Valid (s : Bool) : LS → List LE → Prop
  | _, [] => True
  | ℓ, e :: es => guard ℓ e ∧ Valid s (step s ℓ e) es

instance (s : Bool) (ℓ : LS) (es : List LE) : Decidable (Valid s ℓ es) := by
  induction es generalizing ℓ with
  | nil => unfold Valid; infer_instance
  | cons e es ih => unfold Valid; exact @instDecidableAnd _ _ _ (ih _)

/-- Part of the schedule before the coin is used by the adversary (depends on `a`, `d2` only).
It ends when processes `0` and `1` (and, in a threshold-coin implementation, the Byzantine
process) have called `random()`. -/
def pre (a d2 : Bool) : List LE :=
  [ .inj 0 (.bval (!a) none), .inj 1 (.bval (!a) none), .inj 2 (.bval (!a) none),
    -- `2` echoes `a`
    .dlv 2 0 (.bval a (some false)), .dlv 2 1 (.bval a (some false)), .echo 2 a,
    -- `0` gets `bin_values = {a}`, sends `AUX(a)`
    .dlv 0 0 (.bval a (some false)), .dlv 0 1 (.bval a (some false)), .dlv 0 2 (.bval a none),
    .aux 0 a,
    -- `1` echoes `¬a`, gets `bin_values = {¬a}`, sends `AUX(¬a)`
    .dlv 1 2 (.bval (!a) (some d2)), .echo 1 (!a), .dlv 1 1 (.bval (!a) none), .aux 1 (!a),
    -- `0` echoes `¬a` and gets `bin_values = {0, 1}`
    .dlv 0 2 (.bval (!a) (some d2)), .echo 0 (!a), .dlv 0 0 (.bval (!a) none),
    -- `0` gets `values = {0, 1}` and calls `random()`
    .dlv 0 0 (.aux a), .dlv 0 1 (.aux (!a)), .inj 0 (.aux a), .est 0 {false, true},
    -- `1` gets `bin_values = {0, 1}` and `values = {0, 1}`, and calls `random()`
    .dlv 1 0 (.bval a (some false)), .dlv 1 1 (.bval a (some false)), .dlv 1 2 (.bval a none),
    .dlv 1 0 (.aux a), .dlv 1 1 (.aux (!a)), .inj 1 (.aux a), .est 1 {false, true} ]

/-- The correct messages of the round (`u` is the `AUX` value of process `2`). -/
def msgs (a d2 u : Bool) : List (Fin 4 × LM) :=
  [ (0, .bval a (some false)), (1, .bval a (some false)), (2, .bval (!a) (some d2)),
    (2, .bval a none), (1, .bval (!a) none), (0, .bval (!a) none),
    (0, .aux a), (1, .aux (!a)), (2, .aux u) ]

/-- Part of the schedule after the coin `s` is revealed. -/
def post (a d2 s : Bool) : List LE :=
  -- `2` gets `bin_values = {¬s}` first
  (if !s = a then [.dlv 2 2 (.bval a none), .skip]
    else [.dlv 2 2 (.bval (!a) (some d2)), .dlv 2 0 (.bval (!a) none)]) ++
  [ .aux 2 (!s),
    -- `2` gets `values = {¬s}` (coin `s`: no decision)
    .dlv 2 2 (.aux (!s)), .inj 2 (.aux (!s)), .dlv 2 (if !s = a then 0 else 1) (.aux (!s)),
    .est 2 {!s} ] ++
  -- deliver everything
  ((msgs a d2 (!s)).flatMap fun m => [.dlv 0 m.1 m.2, .dlv 1 m.1 m.2, .dlv 2 m.1 m.2])

/-- The schedule of a round. -/
def script (a d2 s : Bool) : List LE := pre a d2 ++ post a d2 s

/-- The final state of a round. -/
def final (a d2 s : Bool) : LS := run s (start a d2) (script a d2 s)

/-- The empty round. -/
def empty : LS := ⟨fun _ _ => false, fun _ _ _ => false, fun _ => none⟩

/-! ### General facts -/

/-- A property of every event of a run, together with the state in which it occurs. -/
def AllSteps (Q : LS → LE → Prop) (s : Bool) : LS → List LE → Prop
  | _, [] => True
  | ℓ, e :: es => Q ℓ e ∧ AllSteps Q s (step s ℓ e) es

instance (Q : LS → LE → Prop) [∀ ℓ e, Decidable (Q ℓ e)] (s : Bool) (ℓ : LS) (es : List LE) :
    Decidable (AllSteps Q s ℓ es) := by
  induction es generalizing ℓ with
  | nil => unfold AllSteps; infer_instance
  | cons e es ih => unfold AllSteps; exact @instDecidableAnd _ _ _ (ih _)

theorem step_sent_own (s : Bool) (ℓ : LS) (e : LE) (p : Fin 4) (v d : Bool) :
    (step s ℓ e).sent p (.bval v (some d)) = ℓ.sent p (.bval v (some d)) := by
  cases e <;> simp [step]

theorem run_sent_own (s : Bool) (ℓ : LS) (es : List LE) (p : Fin 4) (v d : Bool) :
    (run s ℓ es).sent p (.bval v (some d)) = ℓ.sent p (.bval v (some d)) := by
  induction es generalizing ℓ with
  | nil => rfl
  | cons e es ih => simp only [run]; rw [ih, step_sent_own]

theorem run_nxt_ne_none (s : Bool) (ℓ : LS) (es : List LE) (p : Fin 4) (h : ℓ.nxt p ≠ none) :
    (run s ℓ es).nxt p ≠ none := by
  induction es generalizing ℓ with
  | nil => exact h
  | cons e es ih =>
    refine ih _ ?_
    cases e <;> simp only [step] <;> try exact h
    split_ifs <;> simp_all

theorem run_append (s : Bool) (ℓ : LS) (es fs : List LE) :
    run s ℓ (es ++ fs) = run s (run s ℓ es) fs := by
  induction es generalizing ℓ with
  | nil => rfl
  | cons e es ih => exact ih _

theorem run_take_succ (s : Bool) (ℓ : LS) (es : List LE) (k : ℕ) (hk : k < es.length) :
    run s ℓ (es.take (k + 1)) = step s (run s ℓ (es.take k)) es[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, run_append]
  rfl

theorem AllSteps.get {Q : LS → LE → Prop} {s : Bool} {ℓ : LS} {es : List LE}
    (h : AllSteps Q s ℓ es) (k : ℕ) (hk : k < es.length) : Q (run s ℓ (es.take k)) es[k] := by
  induction es generalizing ℓ k with
  | nil => simp at hk
  | cons e es ih =>
    cases k with
    | zero => exact h.1
    | succ k => exact ih h.2 k (by simpa using hk)

theorem AllSteps.getD {Q : LS → LE → Prop} {s : Bool} {ℓ : LS} {es : List LE}
    (h : AllSteps Q s ℓ es) (k : ℕ) (hk : k < es.length) :
    Q (run s ℓ (es.take k)) (es.getD k .skip) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h.get k hk

theorem Valid.guard (s : Bool) (ℓ : LS) (es : List LE) (h : Valid s ℓ es) (k : ℕ)
    (hk : k < es.length) : guard (run s ℓ (es.take k)) es[k] := by
  induction es generalizing ℓ k with
  | nil => simp at hk
  | cons e es ih =>
    cases k with
    | zero => exact h.1
    | succ k => exact ih _ h.2 k (by simpa using hk)

/-! ### Checks of the schedule (by `decide`) -/

theorem valid_script : ∀ a d2 s, Valid s (start a d2) (script a d2 s) := by decide +kernel

theorem script_length : ∀ a d2 s, (script a d2 s).length = 62 := by decide

theorem pre_length : ∀ a d2, (pre a d2).length = 28 := by decide

theorem script_getElem_pre (a d2 s : Bool) (k : ℕ) (hk : k < 28) :
    (script a d2 s)[k]'(by rw [script_length]; omega) = (pre a d2)[k]'(by rw [pre_length]; omega) := by
  unfold script
  rw [List.getElem_append_left]

/-- At the end of the round every message between correct processes has been delivered. -/
theorem final_delivered : ∀ a d2 s (q s' : Fin 4) (m : LM), q ≠ 3 → s' ≠ 3 →
    (final a d2 s).sent s' m = true → (final a d2 s).rcv q s' m = true := by decide +kernel

/-- The estimates for the next round: `0, 1` adopt the coin `s`, `2` adopts `¬s` after a
singleton `values`. -/
theorem final_nxt : ∀ a d2 s, (final a d2 s).nxt 0 = some (s, false) ∧
    (final a d2 s).nxt 1 = some (s, false) ∧ (final a d2 s).nxt 2 = some (!s, true) ∧
    (final a d2 s).nxt 3 = none := by decide +kernel

/-- At the end of the round every correct process has broadcast `B_VAL(v)` for both `v`. -/
theorem final_bval : ∀ a d2 s (p : Fin 4) (v : Bool), p ≠ 3 →
    ∃ d, (final a d2 s).sent p (.bval v d) = true := by decide +kernel

/-- At the end of the round every correct process has broadcast an `AUX` message. -/
theorem final_aux : ∀ a d2 s (p : Fin 4), p ≠ 3 → ∃ w, (final a d2 s).sent p (.aux w) = true := by
  decide +kernel

/-- The estimates computed in a round. -/
def expNxt (s : Bool) : Fin 4 → Option (Bool × Bool)
  | 0 => some (s, false)
  | 1 => some (s, false)
  | 2 => some (!s, true)
  | 3 => none

theorem final_nxt_eq (a d2 s : Bool) (p : Fin 4) : (final a d2 s).nxt p = expNxt s p := by
  obtain ⟨h0, h1, h2, h3⟩ := final_nxt a d2 s
  fin_cases p <;> assumption

theorem nxt_steps : ∀ a d2 s, AllSteps (fun ℓ _ => ∀ p, ℓ.nxt p = none ∨ ℓ.nxt p = expNxt s p) s
    (start a d2) (script a d2 s) := by decide +kernel

/-- During the round, estimates for the next round are either not yet computed or final. -/
theorem prefix_nxt (a d2 s : Bool) (k : ℕ) (hk : k ≤ 62) (p : Fin 4) :
    (run s (start a d2) ((script a d2 s).take k)).nxt p = none ∨
    (run s (start a d2) ((script a d2 s).take k)).nxt p = (final a d2 s).nxt p := by
  rw [final_nxt_eq]
  rcases lt_or_eq_of_le hk with hk | rfl
  · exact (nxt_steps a d2 s).get k (by rw [script_length]; exact hk) p
  · rw [← script_length a d2 s, List.take_length]
    exact Or.inr (final_nxt_eq a d2 s p)

theorem nxt_at_21 : ∀ a d2 s, (run s (start a d2) ((script a d2 s).take 21)).nxt 0 ≠ none := by
  decide +kernel

theorem nxt_at_28 : ∀ a d2 s, (run s (start a d2) ((script a d2 s).take 28)).nxt 1 ≠ none := by
  decide +kernel

theorem prefix_nxt_of_le (a d2 s : Bool) (j k : ℕ) (hjk : j ≤ k) (p : Fin 4)
    (h : (run s (start a d2) ((script a d2 s).take j)).nxt p ≠ none) :
    (run s (start a d2) ((script a d2 s).take k)).nxt p ≠ none := by
  have : (script a d2 s).take k = (script a d2 s).take j ++ ((script a d2 s).take k).drop j := by
    conv_lhs => rw [← List.take_append_drop j ((script a d2 s).take k)]
    rw [List.take_take, Nat.min_eq_left hjk]
  rw [this, run_append]
  exact run_nxt_ne_none _ _ _ _ h

/-- Process `1` has called `random()` after the first 28 events. -/
theorem prefix_nxt1 (a d2 s : Bool) (k : ℕ) (hk : k ≤ 62) (hk' : 28 ≤ k) :
    (run s (start a d2) ((script a d2 s).take k)).nxt 1 = some (s, false) := by
  have h := prefix_nxt_of_le a d2 s 28 k hk' 1 (nxt_at_28 a d2 s)
  rcases prefix_nxt a d2 s k hk 1 with h' | h'
  · exact absurd h' h
  · rw [h', final_nxt_eq]; rfl

/-- Process `0` has called `random()` after the first 21 events. -/
theorem prefix_nxt0 (a d2 s : Bool) (k : ℕ) (hk : k ≤ 62) (hk' : 21 ≤ k) :
    (run s (start a d2) ((script a d2 s).take k)).nxt 0 = some (s, false) := by
  have h := prefix_nxt_of_le a d2 s 21 k hk' 0 (nxt_at_21 a d2 s)
  rcases prefix_nxt a d2 s k hk 0 with h' | h'
  · exact absurd h' h
  · rw [h', final_nxt_eq]; rfl

/-! ### The schedule is an execution of the deterministic code

The model's guards are liberal: a process may pass a `wait until` later than possible, and
choose any set of `n − t` messages. The schedule does not use this freedom:
* `eager`: whenever a message is delivered, no correct process has a pending step (processes
  react immediately, as the code does);
* `forced`: when line 04 is executed, `bin_values` is a singleton (no choice of `w`), and when
  line 05 is passed, `values` is determined (every admissible set of `n − t` messages gives the
  same `values`);
* `quiet_final`: at the end of a round no step of the round is enabled any more. -/

/-- No correct process has an enabled step. -/
def Quiet (ℓ : LS) : Prop :=
  ∀ p : Fin 4, p ≠ 3 → (∀ v, ¬ guard ℓ (.echo p v)) ∧ (∀ w, ¬ guard ℓ (.aux p w)) ∧
    ∀ V : Finset Bool, ¬ guard ℓ (.est p V)

theorem exists_lquorum_iff (ℓ : LS) (p : Fin 4) :
    (∃ V, lquorum ℓ p V) ↔ ∃ x : Fin 4, ∃ b0 b1 b2 b3 : Bool, QF ℓ p x ![b0, b1, b2, b3] := by
  constructor
  · rintro ⟨V, hV⟩
    obtain ⟨x, b0, b1, b2, b3, h, -⟩ := (lquorum_iff ℓ p V).1 hV
    exact ⟨x, b0, b1, b2, b3, h⟩
  · rintro ⟨x, b0, b1, b2, b3, h⟩
    classical
    exact ⟨(Finset.univ.filter fun v => ImgF x ![b0, b1, b2, b3] v),
      (lquorum_iff ℓ p _).2 ⟨x, b0, b1, b2, b3, h, fun v => by simp⟩⟩

theorem quiet_iff (ℓ : LS) : Quiet ℓ ↔ ∀ p : Fin 4, p ≠ 3 → (∀ v, ¬ guard ℓ (.echo p v)) ∧
    (∀ w, ¬ guard ℓ (.aux p w)) ∧
    ¬ ((∃ w, ℓ.sent p (.aux w) = true) ∧ ℓ.nxt p = none ∧
      ∃ x : Fin 4, ∃ b0 b1 b2 b3 : Bool, QF ℓ p x ![b0, b1, b2, b3]) := by
  unfold Quiet
  refine forall_congr' fun p => imp_congr_right fun hp => and_congr_right' (and_congr_right'
    ?_)
  rw [← exists_lquorum_iff]
  simp only [guard]
  constructor
  · rintro h ⟨hw, hn, V, hV⟩; exact h V ⟨hp, hw, hn, hV⟩
  · rintro h V ⟨-, hw, hn, hV⟩; exact h ⟨hw, hn, V, hV⟩

instance (ℓ : LS) : Decidable (Quiet ℓ) := decidable_of_iff _ (quiet_iff ℓ).symm

/-- Deliveries (of correct or Byzantine messages). -/
def IsDelivery : LE → Prop
  | .dlv _ _ _ => True
  | .inj _ _ => True
  | _ => False

instance : DecidablePred IsDelivery := fun e => by cases e <;> unfold IsDelivery <;> infer_instance

/-- The choices of lines 04 and 05 are forced. -/
def Forced (ℓ : LS) : LE → Prop
  | .aux p w => ∀ w', lbin ℓ p w' → w' = w
  | .est p V => ∀ V', lquorum ℓ p V' → V' = V
  | _ => True

theorem forced_est_iff (ℓ : LS) (p : Fin 4) (V : Finset Bool) :
    Forced ℓ (.est p V) ↔ ∀ x : Fin 4, ∀ b0 b1 b2 b3 : Bool, QF ℓ p x ![b0, b1, b2, b3] →
      ∀ v, v ∈ V ↔ ImgF x ![b0, b1, b2, b3] v := by
  unfold Forced
  constructor
  · intro h x b0 b1 b2 b3 hQ v
    classical
    have := h (Finset.univ.filter fun v => ImgF x ![b0, b1, b2, b3] v)
      ((lquorum_iff ℓ p _).2 ⟨x, b0, b1, b2, b3, hQ, fun v => by simp⟩)
    rw [← this]; simp
  · intro h V' hV'
    obtain ⟨x, b0, b1, b2, b3, hQ, hV⟩ := (lquorum_iff ℓ p V').1 hV'
    ext v
    rw [hV, h x b0 b1 b2 b3 hQ v]

instance (ℓ : LS) (e : LE) : Decidable (Forced ℓ e) := by
  cases e with
  | est p V => exact decidable_of_iff _ (forced_est_iff ℓ p V).symm
  | _ => unfold Forced; infer_instance

theorem eager_steps : ∀ a d2 s, AllSteps (fun ℓ e => IsDelivery e → Quiet ℓ) s (start a d2)
    (script a d2 s) := by decide +kernel

theorem forced_steps : ∀ a d2 s, AllSteps Forced s (start a d2) (script a d2 s) := by
  decide +kernel

/-- Whenever a message is delivered, no correct process has a pending step. -/
theorem eager (a d2 s : Bool) (k : ℕ) (hk : k < 62)
    (hd : IsDelivery ((script a d2 s).getD k .skip)) :
    Quiet (run s (start a d2) ((script a d2 s).take k)) :=
  (eager_steps a d2 s).getD k (by rw [script_length]; exact hk) hd

/-- The choices of lines 04 and 05 are forced whenever they are made. -/
theorem forced (a d2 s : Bool) (k : ℕ) (hk : k < 62) :
    Forced (run s (start a d2) ((script a d2 s).take k)) ((script a d2 s).getD k .skip) :=
  (forced_steps a d2 s).getD k (by rw [script_length]; exact hk)

theorem quiet_final : ∀ a d2 s, Quiet (final a d2 s) := by decide +kernel

end Podc.SignatureFreeBA.Local
