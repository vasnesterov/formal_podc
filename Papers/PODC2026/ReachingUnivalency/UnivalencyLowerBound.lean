import Cslib.Computability.Distributed.Byzantine.PartialSync.Omission

/-!
# Reaching Univalency — Appendix B: reaching univalency requires `Ω(f)` messages

Appendix B of [Lewis-Pye, *Reaching Univalency with Subquadratic Communication*, PODC 2026].

**Model.** Synchronous (lock-step) message passing with **crash** faults, as executions of CSLib's
`OmExec` (inputs + delivered batches; message batches sent at time `τ` are received at time `τ`
and processed into the state at time `τ + 1`). `CrashAdm E F`: every omitted batch is sent by a
process `q ∈ F` to another process, and after its first omitted batch (its crash) `q` delivers
nothing any more. So a process crashing at time `τ` sends an arbitrary subset of its time-`τ`
messages and nothing afterwards, as in the paper. (Crashed processes keep computing states in
`OmExec`; this is irrelevant since nobody receives from them.)

The paper composes a protocol `P₁` (univalency) that ends at time `t*` with a dissemination protocol
`P₂`. We model the composition as a single deterministic algorithm `A` with binary inputs and
outputs whose first phase consists of the times `< t*`:

* `CrashBA f A` : `A` solves binary Byzantine Agreement with at most `f` crash faults;
* `ReachesUnivalency A f t*` : for every admissible execution `E`, all correct processes decide the
  same value `v` in *every* admissible execution that agrees with `E` at all times `< t*` (same
  inputs, same deliveries) — "`P₁` achieves univalency".

**Result** (`appendixB`): at least `f` processes send or receive a message during the first phase
of one of the two fault-free executions with uniform inputs (all-`0` and all-`1`); hence one of them
has `≥ f/2` such processes (the paper's statement) and `≥ f/4` messages before `t*`
(`appendixB_messages`), i.e. message complexity `Ω(f)`.
-/

namespace ReachingUnivalency

open Finset Cslib.Byzantine.PartialSync

variable {P M S VI : Type*} [Fintype P] [DecidableEq P]

/-- `F` is a legal set of **crash**-faulty processes for `E`: omitted batches are sent by a process
of `F` to another process, and after the first omitted batch of `q` (its crash) all later batches of
`q` are omitted. -/
def CrashAdm (E : OmExec P VI) (F : Finset P) : Prop :=
  ∀ τ q p, E.ok τ q p = false → q ≠ p ∧ q ∈ F ∧ ∀ τ' > τ, ∀ p', p' ≠ q → E.ok τ' q p' = false

/-- Binary Byzantine Agreement in the synchronous crash model with at most `f` faults. -/
structure CrashBA (f : ℕ) (A : Algorithm P M S Bool Bool) : Prop where
  /-- Every correct process decides. -/
  termination : ∀ (E : OmExec P Bool) (F : Finset P), CrashAdm E F → F.card ≤ f →
    ∀ p ∉ F, ∃ v, E.Decides A p v
  /-- No two correct processes decide differently. -/
  agreement : ∀ (E : OmExec P Bool) (F : Finset P), CrashAdm E F → F.card ≤ f →
    ∀ p ∉ F, ∀ q ∉ F, ∀ v w, E.Decides A p v → E.Decides A q w → v = w
  /-- If all correct processes have input `v`, then `v` is their decision. -/
  validity : ∀ (E : OmExec P Bool) (F : Finset P), CrashAdm E F → F.card ≤ f →
    ∀ v, (∀ p ∉ F, E.inp p = v) → ∀ p ∉ F, ∀ w, E.Decides A p w → w = v

/-- `E'` extends the prefix of `E` before time `k` (the paper's "`E'` extends the run `r`"): same
inputs and the same deliveries at all times `< k`. -/
def Extends (E' E : OmExec P VI) (k : ℕ) : Prop :=
  E'.inp = E.inp ∧ ∀ τ < k, E'.ok τ = E.ok τ

/-- The prefix of `E` before time `k` is **univalent**: some `v` is the only value decided by
correct processes in all admissible executions extending it. -/
def UnivalentAt (A : Algorithm P M S Bool Bool) (f k : ℕ) (E : OmExec P Bool) : Prop :=
  ∃ v, ∀ (E' : OmExec P Bool) (F' : Finset P), CrashAdm E' F' → F'.card ≤ f → Extends E' E k →
    ∀ p ∉ F', ∀ w, E'.Decides A p w → w = v

/-- The first phase (times `< t*`) of `A` **reaches univalency**: the prefix before `t*` of every
admissible execution is univalent. -/
def ReachesUnivalency (A : Algorithm P M S Bool Bool) (f tstar : ℕ) : Prop :=
  ∀ (E : OmExec P Bool) (F : Finset P), CrashAdm E F → F.card ≤ f → UnivalentAt A f tstar E

/-- The fault-free execution with all inputs equal to `b`. -/
abbrev ffExec (b : Bool) : OmExec P Bool := OmExec.ff fun _ => b

/-- Processes that send a message to, or receive a message from, another process at some time
`< k` in `E` (non-empty batches; in fault-free executions every batch is delivered). -/
def active {VO : Type*} (A : Algorithm P M S VI VO) (E : OmExec P VI) (k : ℕ) : Finset P :=
  univ.filter fun p => ∃ τ < k, ∃ q, q ≠ p ∧
    (A.send p (E.st A τ p) q ≠ [] ∨ A.send q (E.st A τ q) p ≠ [])

section proof

variable {A : Algorithm P M S Bool Bool} {f tstar : ℕ}

/-- Executions of the proof: the processes of `Z` crash at time `0` sending nothing; optionally the
process `x` crashes at time `t*` sending nothing. -/
def zExec (Z : Finset P) (inp : P → Bool) (x : Option P) (tstar : ℕ) : OmExec P Bool where
  inp := inp
  ok τ q p := !decide (q ≠ p ∧ (q ∈ Z ∨ (x = some q ∧ tstar ≤ τ)))

omit [Fintype P] in
lemma zExec_crashAdm (Z : Finset P) (inp : P → Bool) (x : Option P) :
    CrashAdm (zExec Z inp x tstar) (match x with | none => Z | some x => insert x Z) := by
  intro τ q p h
  simp only [zExec, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq] at h
  obtain ⟨hqp, h⟩ := h
  refine ⟨hqp, ?_, fun τ' hτ' p' hp' => ?_⟩
  · rcases h with h | ⟨rfl, -⟩
    · cases x <;> simp [h]
    · simp
  · simp only [zExec, Bool.not_eq_eq_eq_not, Bool.not_false, decide_eq_true_eq]
    exact ⟨Ne.symm hp', h.imp id fun h => ⟨h.1, by omega⟩⟩

/-- Processes outside `Z := active(all-0) ∪ active(all-1)` behave, before `t*`, exactly as in the
fault-free execution with uniform input equal to their own input, as long as `Z` is silent. -/
lemma st_eq_ff (Z : Finset P) (hZ : active A (ffExec false) tstar ∪ active A (ffExec true) tstar ⊆ Z)
    (E : OmExec P Bool) (hsil : ∀ τ q p, q ∈ Z → q ≠ p → E.ok τ q p = false)
    (hself : ∀ τ q, E.ok τ q q = true) (hout : ∀ τ q p, q ∉ Z → E.ok τ q p = true) :
    ∀ τ ≤ tstar, ∀ r ∉ Z, E.st A τ r = (ffExec (E.inp r)).st A τ r := by
  -- outside `Z`, nobody sends or receives anything before `t*` in the uniform executions
  have quiet : ∀ b : Bool, ∀ τ < tstar, ∀ r ∉ Z, ∀ q, q ≠ r →
      A.send r ((ffExec b).st A τ r) q = [] ∧ A.send q ((ffExec b).st A τ q) r = [] := by
    intro b τ hτ r hr q hq
    have hna : r ∉ active A (ffExec b) tstar := fun h =>
      hr (hZ (by cases b <;> simp [h]))
    simp only [active, mem_filter, mem_univ, true_and, not_exists, not_and, not_or,
      not_not] at hna
    exact hna τ hτ q hq
  intro τ
  induction τ with
  | zero => intro _ r _; rfl
  | succ τ ih =>
    intro hτ r hr
    rw [OmExec.st_succ, OmExec.st_succ, ih (by omega) r hr]
    congr 1
    funext q
    unfold OmExec.inbox
    by_cases hqr : q = r
    · subst hqr
      simp [hself, ffExec, ih (by omega) q hr]
    · have h2 := (quiet (E.inp r) τ (by omega) r hr q hqr).2
      have hff : (ffExec (P := P) (E.inp r)).ok τ q r = true := rfl
      simp only [hff, ↓reduceIte, h2]
      by_cases hqZ : q ∈ Z
      · simp [hsil τ q r hqZ hqr]
      · simp only [hout τ q r hqZ, ↓reduceIte, ih (by omega) q hqZ]
        exact (quiet (E.inp q) τ (by omega) q hqZ r (Ne.symm hqr)).1

end proof

/-- **Appendix B** of the paper. If `A` solves binary BA with `f < n` crash faults and its first
phase (times `< t*`) reaches univalency, then at least `f` processes send or receive a message
before `t*` in one of the two fault-free executions with uniform inputs.
(The paper phrases the contrapositive: "fewer than `f/2` correct processors send or receive a
message in every execution of `P₁`" is impossible; only these two executions are needed.) -/
theorem appendixB (A : Algorithm P M S Bool Bool) {f tstar : ℕ} (hf : f < Fintype.card P)
    (hBA : CrashBA f A) (hU : ReachesUnivalency A f tstar) :
    f ≤ (active A (ffExec false) tstar ∪ active A (ffExec true) tstar).card := by
  classical
  obtain ⟨Z, hZdef⟩ : ∃ Z, Z = active A (ffExec false) tstar ∪ active A (ffExec true) tstar :=
    ⟨_, rfl⟩
  rw [← hZdef]
  by_contra hlt
  push Not at hlt
  set O := univ \ Z with hO
  have hOcard : O.card + Z.card = Fintype.card P := by
    rw [hO, card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_univ Z
    omega
  -- the executions `E_S`: inputs `1` exactly on `S ⊆ O`, `Z` crashed at time `0`
  let ES : Finset P → OmExec P Bool := fun S => zExec Z (fun p => decide (p ∈ S)) none tstar
  have hESadm : ∀ S, CrashAdm (ES S) Z := fun S => zExec_crashAdm (tstar := tstar) Z _ none
  have hval : ∀ S, UnivalentAt A f tstar (ES S) := fun S => hU _ Z (hESadm S) hlt.le
  choose v hv using hval
  -- generic facts on the executions `zExec Z inp x`
  have props : ∀ (inp : P → Bool) (x : Option P),
      (∀ τ q p, q ∈ Z → q ≠ p → (zExec Z inp x tstar).ok τ q p = false) ∧
      (∀ τ q, (zExec Z inp x tstar).ok τ q q = true) := by
    intro inp x
    refine ⟨fun τ q p hq hqp => ?_, fun τ q => ?_⟩
    · simp [zExec, hq, hqp]
    · simp [zExec]
  -- before `t*`, processes outside `Z` are in the same state as in a uniform execution
  have early : ∀ (inp : P → Bool) (x : Option P), ∀ τ ≤ tstar, ∀ r ∉ Z,
      (zExec Z inp x tstar).st A τ r = (ffExec (inp r)).st A τ r := by
    intro inp x τ hτ r hr
    -- the prefix before `t*` does not depend on the crash of `x` at `t*`
    have hpre : ∀ τ ≤ tstar, ∀ r, (zExec Z inp x tstar).st A τ r =
        (zExec Z inp none tstar).st A τ r := by
      intro τ hτ
      induction τ with
      | zero => intro r; rfl
      | succ τ ih =>
        intro r
        rw [OmExec.st_succ, OmExec.st_succ]
        have ih' := ih (by omega)
        rw [ih' r]
        congr 1
        funext q
        unfold OmExec.inbox
        have : (zExec Z inp x tstar).ok τ q r = (zExec Z inp none tstar).ok τ q r := by
          simp only [zExec]
          congr 2
          apply propext
          constructor
          · rintro ⟨h1, h2 | ⟨-, h3⟩⟩
            · exact ⟨h1, Or.inl h2⟩
            · omega
          · rintro ⟨h1, h2 | ⟨h3, -⟩⟩
            · exact ⟨h1, Or.inl h2⟩
            · simp at h3
        rw [this, ih' q]
    rw [hpre τ hτ r]
    refine st_eq_ff Z hZdef.symm.subset _ (props inp none).1 (props inp none).2 ?_ τ hτ r hr
    intro τ q p hq
    simp [zExec, hq]
  -- outside `Z`, nobody sends to another process before `t*`
  have quiet : ∀ (inp : P → Bool) (x : Option P), ∀ τ < tstar, ∀ r ∉ Z, ∀ q, q ≠ r →
      A.send r ((zExec Z inp x tstar).st A τ r) q = [] := by
    intro inp x τ hτ r hr q hq
    rw [early inp x τ hτ.le r hr]
    have hna : r ∉ active A (ffExec (inp r)) tstar := fun h => by
      apply hr
      rw [hZdef]
      cases hb : inp r <;> rw [hb] at h <;> simp [h]
    simp only [active, mem_filter, mem_univ, true_and, not_exists, not_and, not_or,
      not_not] at hna
    exact (hna τ hτ q hq).1
  -- key step: adding one process of `O` to `S` does not change the valency
  have step : ∀ S ⊆ O, ∀ x ∈ O, x ∉ S → v S = v (insert x S) := by
    intro S hS x hxO hxS
    have hxZ : x ∉ Z := (mem_sdiff.mp hxO).2
    -- a correct process other than `x`
    obtain ⟨r, hr⟩ : ∃ r, r ∉ insert x Z := by
      by_contra h
      push Not at h
      have : (insert x Z).card = Fintype.card P := by
        rw [← card_univ]; congr 1; ext p; simp [h p]
      have := card_insert_le x Z
      omega
    have hrZ : r ∉ Z := fun h => hr (mem_insert_of_mem h)
    have hrx : r ≠ x := fun h => hr (h ▸ mem_insert_self _ _)
    let E₁ := zExec Z (fun p => decide (p ∈ S)) (some x) tstar
    let E₂ := zExec Z (fun p => decide (p ∈ insert x S)) (some x) tstar
    have hadm₁ : CrashAdm E₁ (insert x Z) := zExec_crashAdm Z _ (some x)
    have hadm₂ : CrashAdm E₂ (insert x Z) := zExec_crashAdm Z _ (some x)
    have hcard : (insert x Z).card ≤ f := (card_insert_le x Z).trans (by omega)
    have hext₁ : Extends E₁ (ES S) tstar := by
      refine ⟨rfl, fun τ hτ => ?_⟩
      funext q p
      simp only [E₁, ES, zExec]
      congr 2; apply propext
      constructor
      · rintro ⟨h1, h2 | ⟨-, h3⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · omega
      · rintro ⟨h1, h2 | ⟨h3, -⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · simp at h3
    have hext₂ : Extends E₂ (ES (insert x S)) tstar := by
      refine ⟨rfl, fun τ hτ => ?_⟩
      funext q p
      simp only [E₂, ES, zExec]
      congr 2; apply propext
      constructor
      · rintro ⟨h1, h2 | ⟨-, h3⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · omega
      · rintro ⟨h1, h2 | ⟨h3, -⟩⟩
        · exact ⟨h1, Or.inl h2⟩
        · simp at h3
    -- `r` cannot distinguish `E₁` from `E₂`
    have hind : ∀ τ, ∀ p ∈ ({p | p ∉ insert x Z} : Set P), E₁.st A τ p = E₂.st A τ p := by
      refine OmExec.st_eq_of_inbox_eq (fun _ => subset_rfl) ?_ ?_
      · intro p hp
        simp only [Set.mem_ofPred_eq, mem_insert, not_or] at hp
        simp [E₁, E₂, zExec, hp.1]
      · intro τ hst p hp
        simp only [Set.mem_ofPred_eq, mem_insert, not_or] at hp
        funext q
        unfold OmExec.inbox
        by_cases hqp : q = p
        · subst hqp
          rw [(props _ _).2, (props _ _).2, hst q (by simp [hp.1, hp.2])]
        by_cases hqZ : q ∈ Z
        · rw [(props _ _).1 τ q p hqZ hqp, (props _ _).1 τ q p hqZ hqp]
          simp
        by_cases hqx : q = x
        · subst hqx
          by_cases hτ : tstar ≤ τ
          · have h1 : E₁.ok τ q p = false := by simp [E₁, zExec, hqp, hτ]
            have h2 : E₂.ok τ q p = false := by simp [E₂, zExec, hqp, hτ]
            rw [h1, h2]
            simp
          · push Not at hτ
            rw [quiet _ _ τ hτ q hqZ p (Ne.symm hqp), quiet _ _ τ hτ q hqZ p (Ne.symm hqp)]
            simp
        · have hxq : ¬x = q := fun h => hqx h.symm
          have h1 : E₁.ok τ q p = true := by simp [E₁, zExec, hqZ, hxq]
          have h2 : E₂.ok τ q p = true := by simp [E₂, zExec, hqZ, hxq]
          simp only [h1, h2, ↓reduceIte, hst q (by simp [hqZ, hqx])]
    obtain ⟨w, hw⟩ := hBA.termination E₁ _ hadm₁ hcard r hr
    have hw₂ : E₂.Decides A r w := by
      obtain ⟨τ, hτ⟩ := hw
      exact ⟨τ, by rw [← hind τ r hr]; exact hτ⟩
    have e₁ := hv S E₁ _ hadm₁ hcard hext₁ r hr w hw
    have e₂ := hv (insert x S) E₂ _ hadm₂ hcard hext₂ r hr w hw₂
    rw [← e₁, ← e₂]
  -- all valencies are equal ...
  have hall : ∀ S ⊆ O, v S = v ∅ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; rfl
    | insert x S hxS ih =>
      intro hsub
      rw [← step S ((subset_insert x S).trans hsub) x (hsub (mem_insert_self x S)) hxS]
      exact ih ((subset_insert x S).trans hsub)
  -- ... but validity forces `v ∅ = false` and `v O = true`
  obtain ⟨r, hrO⟩ : O.Nonempty := by
    rw [← card_pos]; omega
  have hrZ : r ∉ Z := (mem_sdiff.mp hrO).2
  have valency : ∀ S ⊆ O, ∀ b : Bool, (∀ p ∉ Z, decide (p ∈ S) = b) → v S = b := by
    intro S _ b hb
    obtain ⟨w, hw⟩ := hBA.termination (ES S) Z (hESadm S) hlt.le r hrZ
    have h1 := hBA.validity (ES S) Z (hESadm S) hlt.le b hb r hrZ w hw
    have h2 := hv S (ES S) Z (hESadm S) hlt.le ⟨rfl, fun _ _ => rfl⟩ r hrZ w hw
    rw [← h2, h1]
  have h0 := valency ∅ (empty_subset _) false (fun p _ => by simp)
  have h1 := valency O subset_rfl true (fun p hp => by simp [hO, hp])
  have := hall O subset_rfl
  rw [h1, h0] at this
  exact Bool.noConfusion this

/-- Each message has one sender and one receiver: the number of processes that send or receive a
message before time `k` is at most twice the number of messages sent before `k`. -/
theorem card_active_le {VO : Type*} (A : Algorithm P M S VI VO) (E : OmExec P VI) (k : ℕ) :
    (active A E k).card ≤ 2 * E.msgsUpTo A ∅ k := by
  classical
  let len : ℕ → P → P → ℕ := fun τ q p => (A.send q (E.st A τ q) p).length
  -- the message count, summed by sender and by receiver
  have hsend : E.msgsUpTo A ∅ k = ∑ q : P, ∑ τ ∈ range k, ∑ p ∈ univ.filter (· ≠ q), len τ q p := by
    unfold OmExec.msgsUpTo
    rw [sum_comm]
    simp [len]
  have hrecv : E.msgsUpTo A ∅ k = ∑ p : P, ∑ τ ∈ range k, ∑ q ∈ univ.filter (· ≠ p), len τ q p := by
    unfold OmExec.msgsUpTo
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun τ _ => ?_
    rw [sum_comm' (t' := univ.filter (· ∉ (∅ : Finset P))) (s' := fun q => univ.filter (· ≠ q))]
    · simp [len]
    · intro p q
      simp [ne_comm]
  -- a process with a non-empty batch contributes at least one to the corresponding sum
  have one : ∀ (g : P → ℕ → P → ℕ) (p : P), (∃ τ < k, ∃ q, q ≠ p ∧ g p τ q ≠ 0) →
      1 ≤ ∑ τ ∈ range k, ∑ q ∈ univ.filter (· ≠ p), g p τ q := by
    rintro g p ⟨τ, hτ, q, hq, hne⟩
    calc 1 ≤ g p τ q := Nat.one_le_iff_ne_zero.mpr hne
      _ ≤ ∑ q ∈ univ.filter (· ≠ p), g p τ q :=
          single_le_sum (f := fun q => g p τ q) (fun _ _ => Nat.zero_le _) (by simp [hq])
      _ ≤ _ := single_le_sum (f := fun τ => ∑ q ∈ univ.filter (· ≠ p), g p τ q)
          (fun _ _ => Nat.zero_le _) (mem_range.mpr hτ)
  let Snd := univ.filter fun p => ∃ τ < k, ∃ q, q ≠ p ∧ len τ p q ≠ 0
  let Rcv := univ.filter fun p => ∃ τ < k, ∃ q, q ≠ p ∧ len τ q p ≠ 0
  have hsub : active A E k ⊆ Snd ∪ Rcv := by
    intro p hp
    simp only [active, mem_filter, mem_univ, true_and] at hp
    obtain ⟨τ, hτ, q, hq, h | h⟩ := hp
    · exact mem_union_left _ (by simp [Snd, len]; exact ⟨τ, hτ, q, hq, h⟩)
    · exact mem_union_right _ (by simp [Rcv, len]; exact ⟨τ, hτ, q, hq, h⟩)
  have hS : Snd.card ≤ E.msgsUpTo A ∅ k := by
    rw [hsend, card_eq_sum_ones]
    calc ∑ _p ∈ Snd, 1 ≤ ∑ p ∈ Snd, ∑ τ ∈ range k, ∑ q ∈ univ.filter (· ≠ p), len τ p q :=
          sum_le_sum fun p hp => one (fun p τ q => len τ p q) p (mem_filter.mp hp).2
      _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
  have hR : Rcv.card ≤ E.msgsUpTo A ∅ k := by
    rw [hrecv, card_eq_sum_ones]
    calc ∑ _p ∈ Rcv, 1 ≤ ∑ p ∈ Rcv, ∑ τ ∈ range k, ∑ q ∈ univ.filter (· ≠ p), len τ q p :=
          sum_le_sum fun p hp => one (fun p τ q => len τ q p) p (mem_filter.mp hp).2
      _ ≤ _ := sum_le_sum_of_subset (subset_univ _)
  calc (active A E k).card ≤ (Snd ∪ Rcv).card := card_le_card hsub
    _ ≤ Snd.card + Rcv.card := card_union_le _ _
    _ ≤ _ := by omega

/-- **Appendix B, as stated in the paper**: in one of the two fault-free executions with uniform
inputs, at least `f/2` processes send or receive a message during the first phase. -/
theorem appendixB_half (A : Algorithm P M S Bool Bool) {f tstar : ℕ} (hf : f < Fintype.card P)
    (hBA : CrashBA f A) (hU : ReachesUnivalency A f tstar) :
    ∃ b : Bool, f ≤ 2 * (active A (ffExec b) tstar).card := by
  have h := appendixB A hf hBA hU
  have := card_union_le (active A (ffExec false) tstar) (active A (ffExec true) tstar)
  by_cases h0 : f ≤ 2 * (active A (ffExec false) tstar).card
  · exact ⟨false, h0⟩
  · exact ⟨true, by omega⟩

/-- **Appendix B: reaching univalency requires `Ω(f)` messages.** Some fault-free execution sends at
least `f/4` messages during the first phase (times `< t*`). -/
theorem appendixB_messages (A : Algorithm P M S Bool Bool) {f tstar : ℕ}
    (hf : f < Fintype.card P) (hBA : CrashBA f A) (hU : ReachesUnivalency A f tstar) :
    ∃ b : Bool, f ≤ 4 * (ffExec b).msgsUpTo A ∅ tstar := by
  obtain ⟨b, hb⟩ := appendixB_half A hf hBA hU
  exact ⟨b, by have := card_active_le A (ffExec (P := P) b) tstar; omega⟩

end ReachingUnivalency
