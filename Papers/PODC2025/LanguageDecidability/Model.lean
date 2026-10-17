import Papers.PODC2025.LanguageDecidability.Words

/-!
# The computation model (Section 3) and the decidability notions (Sections 4, 5.2)

## Algorithms (Figure 1)

`n` asynchronous processes run an algorithm `V`. Each process repeats forever:
* Lines 01–02: the adversary chooses the next invocation symbol `v ∈ Σᵢ<`; the process runs a
  block of code on its local state and the shared memory (`Alg.pre`, event `Ev.pre`);
* Line 03: it sends `v` to the adversary `A` (event `Ev.send`);
* Line 04: it receives a response symbol `w ∈ Σᵢ>` chosen by the adversary (event `Ev.recv`);
* Lines 05–06: it runs a block of code and reports a value (`Alg.post`, event `Ev.post`).

Modelling choices (they make the impossibility results stronger):
* the shared memory is an arbitrary type `M` and each block is one atomic transition on it, so any
  base objects (of any consensus number, even an atomic snapshot-and-update of the whole memory)
  are allowed; a wait-free block run solo is a function of the local state and memory, and our
  executions are allowed to run blocks solo;
* every block may also read a perfectly synchronized global clock (the global step number `t`);
* report values are an arbitrary type `R`.

An execution is a schedule `s : ℕ → Ev I O` (it does not depend on `V`): every event must be
enabled by the program counter (`Phase`) of its process (`IsExec.valid`), and every process
completes infinitely many iterations (`IsExec.fair`: fair, failure-free executions). The
configurations `Alg.run` and the reports `Alg.outs` of `V` along `s` are then determined.
The input `x(E)` is the subsequence of send/receive events (`HasInput`); it is unique
(`HasInput.unique`).

## Decidability

* `Decides V L P` — Definition 5.1 (`P`-decidability) for a predicate `P` of the *report trace*
  `ℕ → Option (Fin n × R)` (the report emitted at each step, with the reporting process); this
  includes every predicate of the reported values, as intended by the paper.
* `SD`, `WAD`, `WOD`, `WD` — Definitions 4.1–4.4 with `R = Verdict`.
* `decides_literal` — if `P` could depend on the execution itself (in particular on its input),
  every language would be decidable; so `P` must only see what processes report.
-/

namespace Podc2025.LanguageDecidability

variable {n : ℕ} {I O : Fin n → Type} {R : Type}

/-- An algorithm with the structure of Figure 1, for `n` processes, invocation alphabets `I`,
response alphabets `O` and report values `R`. -/
structure Alg (n : ℕ) (I O : Fin n → Type) (R : Type) where
  /-- Local states. -/
  L : Type
  /-- Shared memory (arbitrary base objects). -/
  M : Type
  /-- Initial memory. -/
  m0 : M
  /-- Initial local states. -/
  l0 : Fin n → L
  /-- Lines 01–02 at time `t` by process `p` with the invocation `v` chosen by the adversary. -/
  pre : ℕ → (p : Fin n) → L → I p → M → L × M
  /-- Lines 05–06 at time `t` by process `p` with the response `w`; the last component is the
  reported value. -/
  post : ℕ → (p : Fin n) → L → O p → M → L × M × R

/-- Program counter of a process. -/
inductive Phase (A B : Type)
  /-- at Line 01 -/
  | idle
  /-- at Line 03, about to send `v` -/
  | ready (v : A)
  /-- at Line 04, waiting for the response -/
  | waiting
  /-- at Line 05, with the response `w` -/
  | got (w : B)

/-- Scheduling events. -/
inductive Ev (I O : Fin n → Type)
  /-- Lines 01–02. -/
  | pre (p : Fin n) (v : I p)
  /-- Line 03: send `v` to the adversary. -/
  | send (p : Fin n) (v : I p)
  /-- Line 04: receive `w` from the adversary. -/
  | recv (p : Fin n) (w : O p)
  /-- Lines 05–06. -/
  | post (p : Fin n) (w : O p)

/-- Program counters of all processes. -/
abbrev Phases (I O : Fin n → Type) := (p : Fin n) → Phase (I p) (O p)

namespace Ev

/-- The process taking the step. -/
def proc : Ev I O → Fin n
  | .pre p _ | .send p _ | .recv p _ | .post p _ => p

/-- The symbol of the input word produced by the event (Lines 03 and 04). -/
def sym : Ev I O → Option (Sym I O)
  | .send p v => some ⟨p, .inl v⟩
  | .recv p w => some ⟨p, .inr w⟩
  | _ => none

/-- The program counter required by the event. -/
def need : (e : Ev I O) → Phase (I e.proc) (O e.proc)
  | .pre _ _ => .idle
  | .send _ v => .ready v
  | .recv _ _ => .waiting
  | .post _ w => .got w

/-- The program counter after the event. -/
def newPh : (e : Ev I O) → Phase (I e.proc) (O e.proc)
  | .pre _ v => .ready v
  | .send _ _ => .waiting
  | .recv _ w => .got w
  | .post _ _ => .idle

end Ev

/-- The event is enabled. -/
def Enabled (φ : Phases I O) (e : Ev I O) : Prop := φ e.proc = e.need

/-- Program counters after the event. -/
def phStep (φ : Phases I O) (e : Ev I O) : Phases I O := Function.update φ e.proc e.newPh

@[simp] lemma Ev.proc_pre (p : Fin n) (v : I p) : (Ev.pre (O := O) p v).proc = p := rfl
@[simp] lemma Ev.proc_send (p : Fin n) (v : I p) : (Ev.send (O := O) p v).proc = p := rfl
@[simp] lemma Ev.proc_recv (p : Fin n) (w : O p) : (Ev.recv (I := I) p w).proc = p := rfl
@[simp] lemma Ev.proc_post (p : Fin n) (w : O p) : (Ev.post (I := I) p w).proc = p := rfl

lemma phStep_of_ne {φ : Phases I O} {e : Ev I O} {q : Fin n} (h : q ≠ e.proc) :
    phStep φ e q = φ q := Function.update_of_ne h _ _

@[simp] lemma phStep_pre_self (φ : Phases I O) (p : Fin n) (v : I p) :
    phStep φ (.pre p v) p = .ready v := Function.update_self _ _ _
@[simp] lemma phStep_send_self (φ : Phases I O) (p : Fin n) (v : I p) :
    phStep φ (.send p v) p = .waiting := Function.update_self _ _ _
@[simp] lemma phStep_recv_self (φ : Phases I O) (p : Fin n) (w : O p) :
    phStep φ (.recv p w) p = .got w := Function.update_self _ _ _
@[simp] lemma phStep_post_self (φ : Phases I O) (p : Fin n) (w : O p) :
    phStep φ (.post p w) p = .idle := Function.update_self _ _ _

@[simp] lemma phStep_pre_ne (φ : Phases I O) {p q : Fin n} (v : I p) (h : q ≠ p) :
    phStep φ (.pre p v) q = φ q := Function.update_of_ne h _ _
@[simp] lemma phStep_send_ne (φ : Phases I O) {p q : Fin n} (v : I p) (h : q ≠ p) :
    phStep φ (.send p v) q = φ q := Function.update_of_ne h _ _
@[simp] lemma phStep_recv_ne (φ : Phases I O) {p q : Fin n} (w : O p) (h : q ≠ p) :
    phStep φ (.recv p w) q = φ q := Function.update_of_ne h _ _
@[simp] lemma phStep_post_ne (φ : Phases I O) {p q : Fin n} (w : O p) (h : q ≠ p) :
    phStep φ (.post p w) q = φ q := Function.update_of_ne h _ _

@[simp] lemma enabled_pre {φ : Phases I O} {p : Fin n} {v : I p} :
    Enabled φ (.pre p v) ↔ φ p = .idle := Iff.rfl
@[simp] lemma enabled_send {φ : Phases I O} {p : Fin n} {v : I p} :
    Enabled φ (.send p v) ↔ φ p = .ready v := Iff.rfl
@[simp] lemma enabled_recv {φ : Phases I O} {p : Fin n} {w : O p} :
    Enabled φ (.recv p w) ↔ φ p = .waiting := Iff.rfl
@[simp] lemma enabled_post {φ : Phases I O} {p : Fin n} {w : O p} :
    Enabled φ (.post p w) ↔ φ p = .got w := Iff.rfl

/-- Program counters along a schedule. -/
def phs (s : ℕ → Ev I O) : ℕ → Phases I O
  | 0 => fun _ => .idle
  | t + 1 => phStep (phs s t) (s t)

/-- A fair failure-free execution: every event is enabled and every process completes infinitely
many iterations. -/
structure IsExec (s : ℕ → Ev I O) : Prop where
  valid : ∀ t, Enabled (phs s t) (s t)
  fair : ∀ p N, ∃ t, N ≤ t ∧ ∃ w, s t = .post p w

/-- Configurations: shared memory and local states. -/
structure Cfg (V : Alg n I O R) where
  mem : V.M
  loc : Fin n → V.L

namespace Alg

variable (V : Alg n I O R)

/-- One step at time `t`: the new configuration and the report, if any. -/
def next (t : ℕ) (c : Cfg V) : Ev I O → Cfg V × Option (Fin n × R)
  | .pre p v => (⟨(V.pre t p (c.loc p) v c.mem).2,
      Function.update c.loc p (V.pre t p (c.loc p) v c.mem).1⟩, none)
  | .send _ _ => (c, none)
  | .recv _ _ => (c, none)
  | .post p w => (⟨(V.post t p (c.loc p) w c.mem).2.1,
      Function.update c.loc p (V.post t p (c.loc p) w c.mem).1⟩,
      some (p, (V.post t p (c.loc p) w c.mem).2.2))

/-- Configurations along a schedule. -/
def run (s : ℕ → Ev I O) : ℕ → Cfg V
  | 0 => ⟨V.m0, V.l0⟩
  | t + 1 => (V.next t (run s t) (s t)).1

/-- The report trace along a schedule: `outs s t = some (p, r)` iff `p` reports `r` at step `t`. -/
def outs (s : ℕ → Ev I O) (t : ℕ) : Option (Fin n × R) := (V.next t (V.run s t) (s t)).2

lemma next_of_sym {t : ℕ} {c : Cfg V} {e : Ev I O} (he : e.sym.isSome) :
    V.next t c e = (c, none) := by
  cases e <;> simp_all [Ev.sym, next]

end Alg

/-- `x` is the input `x(E)` of the schedule `s`: the subsequence of its send/receive events. -/
def HasInput (s : ℕ → Ev I O) (x : Word I O) : Prop :=
  ∃ ι : ℕ → ℕ, StrictMono ι ∧ (∀ t, (s t).sym.isSome → ∃ k, ι k = t) ∧
    ∀ k, (s (ι k)).sym = some (x k)

/-- The input of an execution is unique. -/
theorem HasInput.unique {s : ℕ → Ev I O} {x y : Word I O} (hx : HasInput s x)
    (hy : HasInput s y) : x = y := by
  obtain ⟨ι, hι, hιa, hιb⟩ := hx
  obtain ⟨κ, hκ, hκa, hκb⟩ := hy
  have hr : Set.range ι = Set.range κ := by
    ext t; constructor
    · rintro ⟨k, rfl⟩; exact hκa _ (by simp [hιb k])
    · rintro ⟨k, rfl⟩; exact hιa _ (by simp [hκb k])
  have : ι = κ := (StrictMono.range_inj_of_wellFoundedLT hι hκ).1 hr
  subst this
  funext k
  have := (hιb k).symm.trans (hκb k)
  simpa using this

/-- **Definition 5.1** (`P`-decidability): in every (fair, failure-free) execution `E`,
`x(E) ∈ L ↔ P(E)`, where `P` is a predicate of the report trace. -/
def Decides (V : Alg n I O R) (L : Set (Word I O)) (P : (ℕ → Option (Fin n × R)) → Prop) :
    Prop :=
  ∀ s x, IsExec s → HasInput s x → (x ∈ L ↔ P (V.outs s))

/-- `L` is `P`-decidable. -/
def PDecidable (P : (ℕ → Option (Fin n × R)) → Prop) (L : Set (Word I O)) : Prop :=
  ∃ V : Alg n I O R, Decides V L P

/-- Under the literal reading of Definition 5.1, where `P(E)` may be any predicate of the
execution `E`, every language is `P`-decidable (by every algorithm) for `P(E) := x(E) ∈ L`. -/
theorem decides_literal (L : Set (Word I O)) :
    ∀ s x, IsExec s → HasInput s x → (x ∈ L ↔ ∃ y, HasInput s y ∧ y ∈ L) := by
  intro s x _ hx
  exact ⟨fun h => ⟨x, hx, h⟩, fun ⟨y, hy, hyL⟩ => (hx.unique hy) ▸ hyL⟩

/-! ### Two-valued decidability (Section 4) -/

/-- Report values `YES` and `NO`. -/
inductive Verdict
  | yes
  | no
  deriving DecidableEq

/-- The steps at which process `p` reports `NO`. -/
def NoSet (o : ℕ → Option (Fin n × Verdict)) (p : Fin n) : Set ℕ := {t | o t = some (p, .no)}

/-- Strong decidability predicate: `∀ p, NO(E, p) = 0`. -/
def PSD (o : ℕ → Option (Fin n × Verdict)) : Prop := ∀ p, NoSet o p = ∅

/-- Weak-all decidability predicate: `∀ p, NO(E, p) < ∞`. -/
def PWAD (o : ℕ → Option (Fin n × Verdict)) : Prop := ∀ p, (NoSet o p).Finite

/-- Weak-one decidability predicate: `∃ p, NO(E, p) < ∞`. -/
def PWOD (o : ℕ → Option (Fin n × Verdict)) : Prop := ∃ p, (NoSet o p).Finite

/-- **Definition 4.1**: `V` strongly decides `L`. -/
def StronglyDecides (V : Alg n I O Verdict) (L : Set (Word I O)) : Prop := Decides V L PSD

/-- **Definition 4.2**: `V` weakly-all decides `L`. -/
def WeakAllDecides (V : Alg n I O Verdict) (L : Set (Word I O)) : Prop := Decides V L PWAD

/-- **Definition 4.3**: `V` weakly-one decides `L`. -/
def WeakOneDecides (V : Alg n I O Verdict) (L : Set (Word I O)) : Prop := Decides V L PWOD

/-- **Definition 4.4**: `V` weakly decides `L`. -/
def WeaklyDecides (V : Alg n I O Verdict) (L : Set (Word I O)) : Prop :=
  ∀ s x, IsExec s → HasInput s x →
    (x ∈ L → ∀ p, (NoSet (V.outs s) p).Finite) ∧ (x ∉ L → ∀ p, (NoSet (V.outs s) p).Infinite)

/-- The class `SD`. -/
def SD (L : Set (Word I O)) : Prop := ∃ V : Alg n I O Verdict, StronglyDecides V L
/-- The class `WAD`. -/
def WAD (L : Set (Word I O)) : Prop := ∃ V : Alg n I O Verdict, WeakAllDecides V L
/-- The class `WOD`. -/
def WOD (L : Set (Word I O)) : Prop := ∃ V : Alg n I O Verdict, WeakOneDecides V L
/-- The class `WD`. -/
def WD (L : Set (Word I O)) : Prop := ∃ V : Alg n I O Verdict, WeaklyDecides V L

/-! ### Swapping two adjacent send/receive events of different processes -/

lemma enabled_update_ne {φ : Phases I O} {e : Ev I O} {q : Fin n} (h : e.proc ≠ q)
    (a : Phase (I q) (O q)) : Enabled (Function.update φ q a) e ↔ Enabled φ e := by
  unfold Enabled; rw [Function.update_of_ne h]

lemma phStep_comm {φ : Phases I O} {e₁ e₂ : Ev I O} (h : e₁.proc ≠ e₂.proc) :
    phStep (phStep φ e₁) e₂ = phStep (phStep φ e₂) e₁ := by
  simp only [phStep]; exact Function.update_comm h _ _ _

/-- The schedule with the events at `t₀` and `t₀ + 1` transposed. -/
def swapSched (s : ℕ → Ev I O) (t₀ : ℕ) : ℕ → Ev I O := fun t => s (Equiv.swap t₀ (t₀ + 1) t)

section swap

variable {s : ℕ → Ev I O} {t₀ : ℕ}

lemma swapSched_of_ne {t : ℕ} (h1 : t ≠ t₀) (h2 : t ≠ t₀ + 1) : swapSched s t₀ t = s t := by
  simp [swapSched, Equiv.swap_apply_of_ne_of_ne h1 h2]

@[simp] lemma swapSched_left : swapSched s t₀ t₀ = s (t₀ + 1) := by simp [swapSched]
@[simp] lemma swapSched_right : swapSched s t₀ (t₀ + 1) = s t₀ := by simp [swapSched]

lemma phs_swapSched (hp : (s t₀).proc ≠ (s (t₀ + 1)).proc) :
    ∀ t, t ≠ t₀ + 1 → phs (swapSched s t₀) t = phs s t := by
  have hle : ∀ t, t ≤ t₀ → phs (swapSched s t₀) t = phs s t := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [phs]; rw [ih (by omega), swapSched_of_ne (by omega) (by omega)]
  intro t ht
  induction t with
  | zero => rfl
  | succ t ih =>
    rcases Nat.lt_or_ge t (t₀ + 1) with h | h
    · exact hle _ (by omega)
    · rcases h.eq_or_lt with h | h
      · subst h
        simp only [phs]
        rw [hle t₀ le_rfl, swapSched_right, swapSched_left, phStep_comm hp.symm]
      · simp only [phs]; rw [ih (by omega), swapSched_of_ne (by omega) (by omega)]

/-- Transposing two adjacent send/receive events of different processes gives an execution. -/
theorem IsExec.swapSched (hs : IsExec s) (h1 : (s t₀).sym.isSome) (h2 : (s (t₀ + 1)).sym.isSome)
    (hp : (s t₀).proc ≠ (s (t₀ + 1)).proc) : IsExec (swapSched s t₀) where
  valid t := by
    by_cases ht : t = t₀
    · subst ht
      rw [phs_swapSched hp _ (by omega), swapSched_left]
      have := hs.valid (t + 1)
      simp only [phs, phStep] at this
      exact (enabled_update_ne hp.symm _).1 this
    by_cases ht' : t = t₀ + 1
    · subst ht'
      simp only [phs]
      rw [phs_swapSched hp _ (by omega), swapSched_left, swapSched_right, phStep,
        enabled_update_ne hp]
      exact hs.valid t₀
    · rw [phs_swapSched hp _ ht', swapSched_of_ne ht ht']; exact hs.valid t
  fair p N := by
    obtain ⟨t, ht, w, hw⟩ := hs.fair p N
    refine ⟨t, ht, w, ?_⟩
    have h1' : t ≠ t₀ := by rintro rfl; simp [hw, Ev.sym] at h1
    have h2' : t ≠ t₀ + 1 := by rintro rfl; simp [hw, Ev.sym] at h2
    rw [swapSched_of_ne h1' h2', hw]

/-- Transposing two adjacent send/receive events changes no configuration. -/
theorem run_swapSched (V : Alg n I O R) (h1 : (s t₀).sym.isSome)
    (h2 : (s (t₀ + 1)).sym.isSome) : ∀ t, V.run (swapSched s t₀) t = V.run s t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [Alg.run]; rw [ih]
    by_cases ht : t = t₀
    · subst ht; rw [swapSched_left, V.next_of_sym h1, V.next_of_sym h2]
    by_cases ht' : t = t₀ + 1
    · subst ht'; rw [swapSched_right, V.next_of_sym h1, V.next_of_sym h2]
    · rw [swapSched_of_ne ht ht']

/-- Transposing two adjacent send/receive events changes no report. -/
theorem outs_swapSched (V : Alg n I O R) (h1 : (s t₀).sym.isSome)
    (h2 : (s (t₀ + 1)).sym.isSome) : V.outs (swapSched s t₀) = V.outs s := by
  funext t
  simp only [Alg.outs]; rw [run_swapSched V h1 h2]
  by_cases ht : t = t₀
  · subst ht; rw [swapSched_left, V.next_of_sym h1, V.next_of_sym h2]
  by_cases ht' : t = t₀ + 1
  · subst ht'; rw [swapSched_right, V.next_of_sym h1, V.next_of_sym h2]
  · rw [swapSched_of_ne ht ht']

/-- Transposing the send/receive events of the `k`-th and `(k+1)`-th input symbols transposes
these symbols in the input. -/
theorem HasInput.swapSched {x : Word I O} {ι : ℕ → ℕ} (hι : StrictMono ι)
    (ha : ∀ t, (s t).sym.isSome → ∃ k, ι k = t) (hb : ∀ k, (s (ι k)).sym = some (x k)) {k : ℕ}
    (hk : ι k = t₀) (hk' : ι (k + 1) = t₀ + 1) :
    HasInput (LanguageDecidability.swapSched s t₀) (swapAt x k) := by
  refine ⟨ι, hι, fun t ht => ?_, fun m => ?_⟩
  · by_cases h1 : t = t₀
    · exact ⟨k, hk.trans h1.symm⟩
    by_cases h2 : t = t₀ + 1
    · exact ⟨k + 1, hk'.trans h2.symm⟩
    · rw [swapSched_of_ne h1 h2] at ht; exact ha t ht
  · by_cases h1 : m = k
    · subst h1; rw [hk, swapSched_left, ← hk', hb, swapAt_apply_left]
    by_cases h2 : m = k + 1
    · subst h2; rw [hk', swapSched_right, ← hk, hb, swapAt_apply_right]
    · have e1 : ι m ≠ t₀ := fun h => h1 (hι.injective (h.trans hk.symm))
      have e2 : ι m ≠ t₀ + 1 := fun h => h2 (hι.injective (h.trans hk'.symm))
      rw [swapSched_of_ne e1 e2, hb, swapAt_apply_of_ne _ h1 h2]

end swap

end Podc2025.LanguageDecidability
