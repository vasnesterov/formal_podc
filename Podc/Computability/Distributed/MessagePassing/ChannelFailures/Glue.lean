import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Solo
import Podc.Computability.Distributed.MessagePassing.ChannelFailures.Restrict

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/ChannelFailures/Glue.lean

/-!
# Gluing two solo executions

The core of the partitioning lower bounds of Naser-Pastoriza et al. (PODC 2025, §6 and App. C).

Let `α` be a solo execution of `p₁` under `f` (its operation returns), and let `X₁ ∋ p₁` and
`A₁ ⊆ X₁` (with `p₁ ∉ A₁`) be closed under predecessors in `G \ f`. Let `β` be the solo execution of
`p₂` under `g` that starts with `α` restricted to `A₁`, and let `X₂ ∋ p₂` be closed under
predecessors in `G \ g` with `X₂ ∩ X₁ ⊆ A₁`. Then `σ = α|X₁ · δ|X₂` (where `β = α|A₁ · δ`) is a
finite (failure-free) execution in which the operation of `p₁` completes and then the operation of
`p₂` runs and completes, each process of `X₁ ∪ X₂` being unable to distinguish `σ` from `α` or
`β` (`glue`).

Consequently (`false_of_conflict`), if every finite execution satisfies a safety specification
`Spec` for which these three histories are incompatible (`Conflict`), the two solo runs cannot
both terminate.
-/

namespace Cslib.ChannelFailures

open Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} {M L : Type} [DecidableEq P]

/-! ### Clock readings of the canonical continuation -/

section Clocks

variable {Alg : Algorithm P A M L} [Fintype P] {f : FailurePattern P} {K : ℕ} {p₀ : P}

lemma canonAux_round_succ (C₀ : Config P A M L) (t : ℕ) :
    (canonAux Alg f K p₀ C₀ t).round ≤ (canonAux Alg f K p₀ C₀ (t + 1)).round := by
  simp only [canonAux]
  split_ifs <;> simp

lemma canonAux_round_mono (C₀ : Config P A M L) :
    Monotone fun t => (canonAux Alg f K p₀ C₀ t).round :=
  monotone_nat_of_le_succ (canonAux_round_succ C₀)

lemma canonAux_rest_tick (C₀ : Config P A M L) (t : ℕ) :
    ∀ e ∈ (canonAux Alg f K p₀ C₀ t).rest, ∀ p c, e = .tick p c →
      c = K + (canonAux Alg f K p₀ C₀ t).round + 1 := by
  have hplan : ∀ r (C : Config P A M L), ∀ e ∈ plan f K r C, ∀ p c, e = .tick p c →
      c = K + r + 1 := by
    intro r C e he p c hpc
    subst hpc
    simp only [plan, List.mem_append, List.mem_map, List.mem_flatMap, List.mem_replicate] at he
    rcases he with ⟨_, _, h⟩ | ⟨_, _, _, h⟩ <;> cases h; rfl
  induction t with
  | zero => exact hplan 0 C₀
  | succ t ih =>
    simp only [canonAux]
    split_ifs
    · exact hplan _ _
    · exact fun e he => ih e (List.mem_of_mem_tail he)

lemma canon_clock (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) (t : ℕ) {p : P} {c : ℕ}
    (h : canon Alg f K p₀ C₀ t = .tick p c) : c = K + (canonAux Alg f K p₀ C₀ t).round + 1 := by
  have hne := canonAux_rest_ne_nil (Alg := Alg) (K := K) hp₀ C₀ t
  obtain ⟨e, l, hel⟩ := List.exists_cons_of_ne_nil hne
  have hmem : e ∈ (canonAux Alg f K p₀ C₀ t).rest := by rw [hel]; simp
  have he : canon Alg f K p₀ C₀ t = e := by simp [canon, hel]
  exact canonAux_rest_tick C₀ t e hmem p c (he ▸ h)

lemma pre_canon_pairwise (hp₀ : p₀ ∉ f.procs) (C₀ : Config P A M L) (N : ℕ) :
    (Algorithm.pre (canon Alg f K p₀ C₀) N).Pairwise ClockLe := by
  rw [Algorithm.pre, List.pairwise_map]
  refine (List.pairwise_lt_range (n := N)).imp fun {i j} hij => ?_
  intro p c c' hi hj
  rw [canon_clock hp₀ C₀ i hi, canon_clock hp₀ C₀ j hj]
  have := canonAux_round_mono (Alg := Alg) (f := f) (K := K) (p₀ := p₀) C₀ hij.le
  simp only at this
  omega

lemma soloEvents_pairwise (Alg : Algorithm P A M L) (hp : p₀ ∉ f.procs) (E₀ : List (Event P A))
    (o : A.Op) (N : ℕ) : (soloEvents Alg f K E₀ p₀ o N).Pairwise ClockLe := by
  rw [soloEvents, List.pairwise_cons]
  exact ⟨fun _ _ p c c' h _ => (by cases h), pre_canon_pairwise hp _ N⟩

end Clocks

/-- The clock reading of a tick (`0` for other events). -/
def Event.clock : Event P A → ℕ
  | .tick _ c => c
  | _ => 0

omit [DecidableEq P] in
lemma clockBound_sum (E : List (Event P A)) : ClockBound E (E.map Event.clock).sum := by
  intro e he p c hpc
  subst hpc
  exact List.le_sum_of_mem (List.mem_map.2 ⟨_, he, rfl⟩)

/-! ### Gluing -/

variable (Alg : Algorithm P A M L) [Fintype P]

/-- Deliveries of a solo execution under `f` are along edges of `G \ f`. -/
lemma soloEvents_deliver {f : FailurePattern P} {K : ℕ} {E₀ : List (Event P A)} {p : P}
    (hp : p ∉ f.procs) {o : A.Op} {N : ℕ} {q a : P}
    (h : Event.deliver q a ∈ soloEvents Alg f K E₀ p o N) : f.Edge q a := by
  simp only [soloEvents, List.mem_cons, Algorithm.pre, List.mem_map] at h
  rcases h with h | ⟨i, -, hi⟩
  · cases h
  · have := canon_spec (Alg := Alg) (K := K) hp (Alg.run Alg.initCfg (E₀ ++ [.invoke p o])) i
    rw [hi] at this; exact this

/-- **Gluing lemma.** -/
theorem glue {f g : FailurePattern P} {X₁ A₁ X₂ : Set P} {p₁ p₂ : P} {o₁ o₂ : A.Op}
    (hX₁ : f.Closed X₁) (hA₁ : f.Closed A₁) (hA₁X₁ : A₁ ⊆ X₁) (hp₁X : p₁ ∈ X₁) (hp₁A : p₁ ∉ A₁)
    (hp₁ : p₁ ∉ f.procs) (hX₂ : g.Closed X₂) (hp₂X : p₂ ∈ X₂) (hp₂ : p₂ ∉ g.procs)
    (hX : X₂ ∩ X₁ ⊆ A₁) (h₁ : SoloTerm Alg f p₁ o₁) (h₂ : SoloTerm Alg g p₂ o₂) :
    ∃ r₁ r₂, (∃ E, Alg.hist Alg.initCfg E = [.inv p₁ o₁, .ret p₁ r₁]) ∧
      (∃ E, Alg.hist Alg.initCfg E = [.inv p₂ o₂, .ret p₂ r₂]) ∧
      ∃ E, Alg.hist Alg.initCfg E = [.inv p₁ o₁, .ret p₁ r₁, .inv p₂ o₂, .ret p₂ r₂] := by
  classical
  -- the solo execution `α` of `p₁` under `f`
  obtain ⟨N₁, r₁, hr₁⟩ := h₁ [] (by simp) List.Pairwise.nil 0 (by simp [ClockBound])
  set α := soloEvents Alg f 0 [] p₁ o₁ N₁ with hα
  have hhα : Alg.hist Alg.initCfg α = [.inv p₁ o₁, .ret p₁ r₁] :=
    hist_soloEvents Alg hp₁ (by simp) hr₁
  -- its restriction to `A₁` is the prefix of `β`
  set E₀ := α.filter fun e => decide (e.owner ∈ A₁) with hE₀
  have hE₀inv : ∀ e ∈ E₀, ¬ e.IsInvoke := by
    intro e he
    rw [hE₀, List.mem_filter] at he
    obtain ⟨he, hown⟩ := he
    rw [hα, soloEvents, List.mem_cons] at he
    rcases he with rfl | he
    · exact absurd (of_decide_eq_true hown) hp₁A
    · exact soloEvents_not_invoke Alg (E₀ := []) (K := 0) (o := o₁) (N := N₁) hp₁ e
        (by simpa [soloEvents] using he)
  have hE₀pw : E₀.Pairwise ClockLe := (soloEvents_pairwise Alg hp₁ [] o₁ N₁).filter _
  obtain ⟨N₂, r₂, hr₂⟩ := h₂ E₀ hE₀inv hE₀pw _ (clockBound_sum E₀)
  set δ := soloEvents Alg g (E₀.map Event.clock).sum E₀ p₂ o₂ N₂ with hδ
  have hhδ : Alg.hist (Alg.run Alg.initCfg E₀) δ = [.inv p₂ o₂, .ret p₂ r₂] :=
    hist_soloEvents Alg hp₂ hE₀inv hr₂
  refine ⟨r₁, r₂, ⟨α, hhα⟩, ⟨E₀ ++ δ, ?_⟩, ?_⟩
  · rw [Algorithm.hist_append, (run_noPend Alg (noPend_initCfg Alg) hE₀inv).2, hhδ]; rfl
  -- the glued execution `σ = α|X₁ · δ|X₂`
  have hαX₁ : ∀ q p, Event.deliver q p ∈ α → p ∈ X₁ → q ∈ X₁ :=
    fun q p h hp => hX₁ q p (soloEvents_deliver Alg hp₁ h) hp
  obtain ⟨-, hh1⟩ := agree_run_filter Alg X₁ α hαX₁ (Agree.refl (Alg.initCfg))
  -- agreement of `α|X₁` and `α|A₁ = E₀` on `X' = A₁ ∪ X₁ᶜ ⊇ X₂`
  set X' : Set P := A₁ ∪ X₁ᶜ
  have hX'd : ∀ q p, Event.deliver q p ∈ α.filter (fun e => decide (e.owner ∈ X₁)) →
      p ∈ X' → q ∈ X' := by
    intro q p h hp
    rw [List.mem_filter] at h
    have hpX₁ : p ∈ X₁ := by simpa using of_decide_eq_true h.2
    rcases hp with hp | hp
    · exact Or.inl (hA₁ q p (soloEvents_deliver Alg hp₁ h.1) hp)
    · exact absurd hpX₁ hp
  obtain ⟨hag, -⟩ := agree_run_filter Alg X' (α.filter fun e => decide (e.owner ∈ X₁)) hX'd
    (Agree.refl (Alg.initCfg))
  have hff : (α.filter fun e => decide (e.owner ∈ X₁)).filter (fun e => decide (e.owner ∈ X'))
      = E₀ := by
    rw [List.filter_filter, hE₀]
    apply List.filter_congr
    intro e _
    by_cases h1 : e.owner ∈ A₁
    · simp [X', h1, hA₁X₁ h1]
    · by_cases h2 : e.owner ∈ X₁ <;> simp [X', h1, h2]
  rw [hff] at hag
  have hX₂X' : X₂ ⊆ X' := by
    intro x hx
    by_cases hx₁ : x ∈ X₁
    · exact Or.inl (hX ⟨hx, hx₁⟩)
    · exact Or.inr hx₁
  have hag₂ : Agree X₂ (Alg.run Alg.initCfg E₀)
      (Alg.run Alg.initCfg (α.filter fun e => decide (e.owner ∈ X₁))) :=
    (hag.mono hX₂X').symm
  have hδX₂ : ∀ q p, Event.deliver q p ∈ δ → p ∈ X₂ → q ∈ X₂ :=
    fun q p h hp => hX₂ q p (soloEvents_deliver Alg hp₂ h) hp
  obtain ⟨-, hh2⟩ := agree_run_filter Alg X₂ δ hδX₂ hag₂
  refine ⟨(α.filter fun e => decide (e.owner ∈ X₁)) ++ δ.filter fun e => decide (e.owner ∈ X₂), ?_⟩
  rw [Algorithm.hist_append, hh1, hh2, hhα, hhδ]
  simp [Label.proc, hp₁X, hp₂X]

/-- Three histories that no execution of a correct implementation can all produce: two solo
histories and their sequential composition. -/
def Conflict (Spec : List (Label P A) → Prop) (p₁ p₂ : P) : Prop :=
  ∃ o₁ o₂, ∀ r₁ r₂, Spec [.inv p₁ o₁, .ret p₁ r₁] → Spec [.inv p₂ o₂, .ret p₂ r₂] →
    ¬ Spec [.inv p₁ o₁, .ret p₁ r₁, .inv p₂ o₂, .ret p₂ r₂]

/-- **Partitioning argument.** If every finite execution satisfies `Spec` and `Spec` has
conflicting operations for `p₁, p₂`, then the configuration of the gluing lemma is impossible:
not both solo runs can terminate for all operations. -/
theorem false_of_conflict {Spec : List (Label P A) → Prop} (hsafe : Alg.Satisfies Spec)
    {f g : FailurePattern P} {X₁ A₁ X₂ : Set P} {p₁ p₂ : P} (hconf : Conflict Spec p₁ p₂)
    (hX₁ : f.Closed X₁) (hA₁ : f.Closed A₁) (hA₁X₁ : A₁ ⊆ X₁) (hp₁X : p₁ ∈ X₁) (hp₁A : p₁ ∉ A₁)
    (hp₁ : p₁ ∉ f.procs) (hX₂ : g.Closed X₂) (hp₂X : p₂ ∈ X₂) (hp₂ : p₂ ∉ g.procs)
    (hX : X₂ ∩ X₁ ⊆ A₁) (h₁ : ∀ o, SoloTerm Alg f p₁ o) (h₂ : ∀ o, SoloTerm Alg g p₂ o) : False := by
  obtain ⟨o₁, o₂, hc⟩ := hconf
  obtain ⟨r₁, r₂, ⟨E₁, hE₁⟩, ⟨E₂, hE₂⟩, ⟨E, hE⟩⟩ :=
    glue Alg hX₁ hA₁ hA₁X₁ hp₁X hp₁A hp₁ hX₂ hp₂X hp₂ hX (h₁ o₁) (h₂ o₂)
  exact hc r₁ r₂ (hE₁ ▸ hsafe E₁) (hE₂ ▸ hsafe E₂) (hE ▸ hsafe E)

end Cslib.ChannelFailures
