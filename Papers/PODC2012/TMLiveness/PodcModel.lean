import Papers.PODC2012.TMLiveness.Main

/-!
# The PODC paper's own framework is too weak: a TM that never answers

In the PODC version (§2.2–§3.1), a TM implementation is an I/O automaton whose actions are the
invocation and response events; histories are the sequences of events of its runs; the liveness
notions are evaluated on its *infinite histories*, and a process crashes in an infinite history
`H` iff `H|p_k` is finite and non-empty. There are no internal steps and no fairness requirement,
so nothing forces the automaton to answer an invocation: a process whose invocation is never
answered simply has a finite projection, i.e. counts as crashed.

We formalize this framework (with the well-formedness condition of the chapter version, which
allows a final pending invocation; the PODC version requires `H|p_k ∈ Σ_k^∞`, which, histories being
prefix-closed, would forbid accepting any invocation at all) and show that the *silent* TM, which
accepts every well-formed invocation and never responds, ensures opacity and local progress in
every fault-prone system (`silent_ensures`): with finitely many processes it has no infinite
history, so the liveness requirement is vacuous. Hence Theorem 1 is false if read literally in the
PODC formalism. The intended statement — in the step-based model of the chapter version, where a
process that keeps taking steps inside an operation that never returns is correct — is
`theorem_1`.
-/

namespace Podc.TMLiveness

namespace PodcModel

variable {P X V St : Type*} [DecidableEq P]

/-- A TM implementation of the PODC version: an automaton whose actions are the events. -/
structure Automaton (P X V St : Type*) where
  init : St
  trans : St → Ev P X V → St → Prop

/-- The finite histories of an automaton. -/
def Automaton.Hist (F : Automaton P X V St) (h : List (Ev P X V)) : Prop :=
  ∃ s : ℕ → St, s 0 = F.init ∧ ∀ i (hi : i < h.length), F.trans (s i) h[i] (s (i + 1))

/-- The infinite histories of an automaton. -/
def Automaton.InfHist (F : Automaton P X V St) (H : ℕ → Ev P X V) : Prop :=
  ∃ s : ℕ → St, s 0 = F.init ∧ ∀ i, F.trans (s i) (H i) (s (i + 1))

/-- PODC §2.3: `p_k` crashes in `H` iff `H|p_k` is finite and non-empty. -/
def Crashes (H : ℕ → Ev P X V) (k : P) : Prop :=
  {t | (H t).proc = k}.Finite ∧ {t | (H t).proc = k}.Nonempty

/-- PODC §2.3: `p_k` is parasitic iff `H|p_k` is infinite with finitely many `tryC` and aborts. -/
def Parasitic (H : ℕ → Ev P X V) (k : P) : Prop :=
  {t | (H t).proc = k}.Infinite ∧ {t | H t = .inv k .tryC}.Finite ∧
    {t | ∃ i, H t = .res k i .abort}.Finite

/-- PODC §2.3: correct processes. -/
def Correct (H : ℕ → Ev P X V) (k : P) : Prop := ¬ Crashes H k ∧ ¬ Parasitic H k

/-- PODC §3.1: progress. -/
def Progress (H : ℕ → Ev P X V) (k : P) : Prop := {t | ∃ i, H t = .res k i .commit}.Infinite

/-- PODC §3.2.1: local progress. -/
def LocalProgress (H : ℕ → Ev P X V) : Prop := ∀ k, Correct H k → Progress H k

/-- PODC §2.3: the histories a fault-prone system admits. -/
def Admissible : FaultProne → (ℕ → Ev P X V) → Prop
  | .crashOrParasitic, _ => True
  | .parasiticFree, H => ∀ k, ¬ Parasitic H k
  | .crashFree, H => ∀ k, ¬ Crashes H k

/-- Definition 3: the automaton ensures `L` (in the system `sys`). -/
def EnsuresLiveness (F : Automaton P X V St) (sys : FaultProne) (L : (ℕ → Ev P X V) → Prop) :
    Prop :=
  ∀ H, F.InfHist H → Admissible sys H → L H

/-- §2.4: the automaton ensures a safety property. -/
def EnsuresSafety (F : Automaton P X V St) (S : List (Ev P X V) → Prop) : Prop :=
  ∀ h, F.Hist h → S h

/-- The silent TM: it accepts one invocation per process and never responds. -/
def silent : Automaton P X V (P → Bool) where
  init := fun _ => false
  trans s e s' := ∃ k i, e = .inv k i ∧ s k = false ∧ s' = Function.update s k true

/-- Its histories are well formed (each projection is at most one pending invocation). -/
theorem silent_hist_inv {h : List (Ev P X V)} (hh : (silent (P := P) (X := X) (V := V)).Hist h) :
    ∀ e ∈ h, ∃ k i, e = .inv k i := by
  obtain ⟨s, -, hs⟩ := hh
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  obtain ⟨k, i', h1, -⟩ := hs i hi
  exact ⟨k, i', h1⟩

/-- With finitely many processes the silent TM has no infinite history. -/
theorem silent_no_infHist [Fintype P] (H : ℕ → Ev P X V) :
    ¬ (silent (P := P) (X := X) (V := V)).InfHist H := by
  rintro ⟨s, hs0, hs⟩
  have hcount : ∀ n, (Finset.univ.filter (fun k => s n k = true)).card = n := by
    intro n
    induction n with
    | zero => simp [hs0, silent]
    | succ n ih =>
      obtain ⟨k, i, -, hk, hs'⟩ := hs n
      rw [hs']
      have : Finset.univ.filter (fun k' => Function.update (s n) k true k' = true) =
          insert k (Finset.univ.filter (fun k' => s n k' = true)) := by
        ext k'; by_cases h : k' = k <;> simp [h, Function.update_of_ne]
      rw [this, Finset.card_insert_of_notMem (by simp [hk]), ih]
  have := hcount (Fintype.card P + 1)
  have hle := Finset.card_filter_le (Finset.univ : Finset P) (fun k => s (Fintype.card P + 1) k = true)
  rw [Finset.card_univ] at hle
  omega

omit [DecidableEq P] in
theorem legalSeq_nil_ops [DecidableEq X] [DecidableEq V] {T : Type*} {ops : T → List (Op X V)}
    {cm : T → Bool} (hops : ∀ t, ops t = []) : ∀ (σ : List T) (s : X → V), LegalSeq ops cm σ s
  | [], _ => trivial
  | t :: σ, s => ⟨s, by simp [hops t, runOps], by
      split_ifs <;> exact legalSeq_nil_ops hops σ s⟩

/-- Information of a history of invocations only. -/
theorem info_of_invs :
    ∀ h : List (Ev P X V), (∀ e ∈ h, ∃ k i, e = .inv k i) →
      (∀ k, (info h).cnt k = 0) ∧ (∀ t, (info h).ops t = []) ∧ (∀ t, (info h).committed t = false) ∧
        (∀ t, (info h).began t = true → t.2 = 0) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _; simp [HInfo.init]
  | append_singleton h e ih =>
    intro hall
    obtain ⟨h1, h2, h3, h4⟩ := ih (fun e' he' => hall e' (by simp [he']))
    obtain ⟨k, i, rfl⟩ := hall e (by simp)
    refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, ?_⟩
    intro t ht
    simp only [info_append_single, step_inv_began, Bool.or_eq_true, decide_eq_true_eq] at ht
    rcases ht with ht | rfl
    · exact h4 t ht
    · simp [h1 k]

/-- **The PODC framework is too weak.** The silent TM ensures opacity and local progress in every
fault-prone system (with finitely many processes). -/
theorem silent_ensures [Fintype P] [DecidableEq X] [DecidableEq V] (init : X → V)
    (sys : FaultProne) :
    EnsuresLiveness (silent (P := P) (X := X) (V := V)) sys LocalProgress ∧
      EnsuresSafety (silent (P := P) (X := X) (V := V)) (Opaque init) := by
  refine ⟨fun H hH => absurd hH (silent_no_infHist H), fun h hh => ?_⟩
  obtain ⟨hcnt, hops, -, hbeg⟩ := info_of_invs h (silent_hist_inv hh)
  refine ⟨(Finset.univ.filter (fun k => (info h).began (k, 0))).toList.map (fun k => (k, 0)),
    fun _ => false, ?_, ?_, by simp, ?_, legalSeq_nil_ops hops _ _⟩
  · exact (Finset.nodup_toList _).map (fun a b hab => by simpa using hab)
  · rintro ⟨k, j⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.mk.injEq, Started]
    constructor
    · rintro ⟨k', hk', rfl, rfl⟩; exact hk'
    · intro hb
      have := hbeg _ hb
      simp only at this
      subst this
      exact ⟨k, hb, rfl, rfl⟩
  · rintro t₁ - t₂ - ⟨u, v, rfl, hc, -, -⟩
    have := (info_of_invs u (fun e he => silent_hist_inv hh e (by simp [he]))).1 t₁.1
    simp [Complete, this] at hc

end PodcModel

/-! ### Non-vacuity of the step-based model

`theorem_1` and `theorem_2` say that no TM has certain properties; this is not vacuous: TMs exist,
and opacity can be ensured. The TM that never answers ensures
opacity (it violates local progress: a process waiting forever inside its operation is correct). -/

variable {P X V : Type*} [DecidableEq P]

/-- The step-based TM whose steps are all internal: it never answers. -/
def silentTM : TM P X V where
  next _ _ := {none}
  next_nonempty _ _ := ⟨none, rfl⟩
  next_fits _ _ _ _ _ h := by simp at h

theorem silentTM_hist {h : List (Step P X V)} (hr : Reachable (silentTM (P := P) (X := X) (V := V)) h) :
    ∀ e ∈ hist h, ∃ k i, e = .inv k i := by
  induction hr with
  | nil => simp
  | @snoc h s _ hv ih =>
    cases s with
    | tau k => simpa using ih
    | ev e =>
      intro e' he'
      simp only [hist_append_ev, List.mem_append, List.mem_singleton] at he'
      rcases he' with he' | rfl
      · exact ih e' he'
      · cases e' with
        | inv k i => exact ⟨k, i, rfl⟩
        | res k i r => simp [ValidStep, silentTM] at hv

/-- The silent step-based TM ensures opacity. -/
theorem silentTM_opaque [Fintype P] [DecidableEq X] [DecidableEq V] (init : X → V) :
    EnsuresSafety (silentTM (P := P) (X := X) (V := V)) (Opaque init) := by
  intro h hr
  have hinv := silentTM_hist hr
  obtain ⟨hcnt, hops, -, hbeg⟩ := PodcModel.info_of_invs (hist h) hinv
  refine ⟨(Finset.univ.filter (fun k => (info (hist h)).began (k, 0))).toList.map (fun k => (k, 0)),
    fun _ => false, ?_, ?_, by simp, ?_, PodcModel.legalSeq_nil_ops hops _ _⟩
  · exact (Finset.nodup_toList _).map (fun a b hab => by simpa using hab)
  · rintro ⟨k, j⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.mk.injEq, Started]
    constructor
    · rintro ⟨k', hk', rfl, rfl⟩; exact hk'
    · intro hb
      have := hbeg _ hb
      simp only at this
      subst this
      exact ⟨k, hb, rfl, rfl⟩
  · rintro t₁ - t₂ - ⟨u, v, huv, hc, -, -⟩
    have := (PodcModel.info_of_invs u (fun e he => hinv e (by rw [huv]; simp [he]))).1 t₁.1
    simp [Complete, this] at hc

/-- TMs exist. -/
example : Nonempty (TM P X V) := ⟨silentTM⟩

end Podc.TMLiveness
