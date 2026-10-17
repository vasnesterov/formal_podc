import Papers.PODC2024.SSLeaderElectionDirected.PELCorrect

/-!
# The necessary condition for leader election (Section 4.2) and Corollary 3

* `LEAlg G ID Q`: an arbitrary deterministic algorithm in the atomic-state model on `G` whose code
  may use the identifiers (inputs `ι : V → ID`) of a process and of its predecessors, together with
  an output `L(p)` computed from the input and the state of `p`. Being a function of `ι`, the
  algorithm is "insensitive to its inputs": it must work for every assignment of unique
  identifiers.
* `SPLE`: the specification `SP_L` of leader election (on executions in Ext∞ form; Lemma 11 says
  that this does not change the specification).
* `lemma13`: in a legitimate configuration, the leader belongs to every source component.
* `corollary2`: if an algorithm is self-stabilizing for leader election under the synchronous
  daemon for all identifier assignments, and `|IDSET| > |V|`, then `G` has exactly one source
  component.
* `corollary3`: a silent self-stabilizing leader election algorithm exists under the distributed
  unfair daemon (resp. the synchronous daemon) iff `G` has exactly one source component.
-/

set_option linter.unusedSectionVars false

universe u

open Cslib.SelfStabilization Relation

namespace Papers.PODC2024.SSLeaderElectionDirected

variable {V : Type*} [Fintype V] {G : Digraph V} {ID Q : Type*}

/-- A deterministic local algorithm with an identifier-valued output (leader election). -/
structure LEAlg (G : Digraph V) (ID Q : Type*) where
  /-- the next state of `p` in configuration `γ`, given the identifier assignment `ι` -/
  next : (V → ID) → (V → Q) → V → Q
  /-- `L(p)`: the leader appointed by `p` -/
  out : (V → ID) → (V → Q) → V → ID
  local_next : IsLocal G next
  local_out : ∀ ι ι' γ γ' p, ι p = ι' p → γ p = γ' p → out ι γ p = out ι' γ' p

/-- The specification `SP_L` of leader election (Section 4.1), for an execution in Ext∞ form:
(1) all processes agree in the first configuration, (2) on the identifier of some process, and
(3) the outputs never change along non-terminal steps. -/
def SPLE (next : (V → Q) → V → Q) (out : (V → Q) → V → ID) (ι : V → ID) (e : ℕ → V → Q) :
    Prop :=
  (∀ p q, out (e 0) p = out (e 0) q) ∧ (∃ q, out (e 0) q = ι q) ∧
    ∀ i p, ¬ Terminal next (e i) → out (e (i + 1)) p = out (e i) p

/-- The predicate of silent leader election: all processes appoint the identifier of one process. -/
def LEPredicate (out : (V → Q) → V → ID) (ι : V → ID) (γ : V → Q) : Prop :=
  ∃ ℓ, ∀ p, out γ p = ι ℓ

/-- Along an execution satisfying `SP_L`, the outputs are constant (for Ext∞ executions). -/
theorem SPLE.out_const {next : (V → Q) → V → Q} {out : (V → Q) → V → ID} {ι : V → ID}
    {e : ℕ → V → Q} (he : IsSyncExec next e) (h : SPLE next out ι e) :
    ∀ t p, out (e t) p = out (e 0) p := by
  intro t p
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases ht : Terminal next (e t)
    · rw [he t, show next (e t) = e t from funext ht, ih]
    · rw [h.2.2 t p ht, ih]

theorem injective_update [DecidableEq V] {ι : V → ID} (hι : Function.Injective ι) {i : ID} (hi : i ∉ Set.range ι)
    (ℓ : V) : Function.Injective (Function.update ι ℓ i) := by
  classical
  intro a b hab
  by_cases ha : a = ℓ <;> by_cases hb : b = ℓ
  · rw [ha, hb]
  · subst ha; simp [Function.update_of_ne hb] at hab; exact absurd ⟨b, hab.symm⟩ hi
  · subst hb; simp [Function.update_of_ne ha] at hab; exact absurd ⟨a, hab⟩ hi
  · simp [Function.update_of_ne ha, Function.update_of_ne hb] at hab; exact hι hab

/-- **Lemma 13.** Let `A` be self-stabilizing for leader election under the synchronous daemon (for
every assignment of unique identifiers), and let `γ` be a legitimate configuration for `ι`, in
which the leader is `ℓ`. If some identifier is unused by `ι`, then `ℓ` belongs to every source
component. -/
theorem lemma13 (A : LEAlg G ID Q) {ι : V → ID} (hι : Function.Injective ι)
    (hfresh : ∃ i, i ∉ Set.range ι)
    (hss : ∀ ι', Function.Injective ι' →
      SelfStab (IsSyncExec (A.next ι')) (SPLE (A.next ι') (A.out ι') ι'))
    {L : Set (V → Q)} (hL : ∀ e, IsSyncExec (A.next ι) e → e 0 ∈ L → SPLE (A.next ι) (A.out ι) ι e)
    {γ : V → Q} (hγ : γ ∈ L) {ℓ : V} (hℓ : ∀ p, A.out ι γ p = ι ℓ) {SC : Set V}
    (hSC : G.IsSourceComponent SC) : ℓ ∈ SC := by
  classical
  by_contra hℓSC
  obtain ⟨i₀, hi₀⟩ := hfresh
  -- the synchronous execution from `γ`
  let e : ℕ → V → Q := fun t => (A.next ι)^[t] γ
  have he : IsSyncExec (A.next ι) e := isSyncExec_iterate γ
  have hconst := (hL e he hγ).out_const he
  -- change the identifier of `ℓ` to a fresh one
  let ι' := Function.update ι ℓ i₀
  have hι' : Function.Injective ι' := injective_update hι hi₀ ℓ
  have hιSC : ∀ p ∈ SC, ι p = ι' p := fun p hp => by
    simp only [ι']; rw [Function.update_of_ne (by rintro rfl; exact hℓSC hp)]
  let e' : ℕ → V → Q := fun t => (A.next ι')^[t] γ
  have he' : IsSyncExec (A.next ι') e' := isSyncExec_iterate γ
  have hagree := syncExec_agree A.local_next hSC.closed hιSC he he' (fun _ _ => rfl)
  -- on `SC`, the processes still appoint the old identifier of `ℓ`
  have hout : ∀ t, ∀ p ∈ SC, A.out ι' (e' t) p = ι ℓ := fun t p hp => by
    rw [← A.local_out ι ι' (e t) (e' t) p (hιSC p hp) (hagree t p hp), hconst t p]
    exact hℓ p
  obtain ⟨L', -, hconv, hcorr⟩ := hss ι' hι'
  obtain ⟨t₀, ht₀⟩ := hconv e' he'
  have hsp := hcorr (fun t => e' (t₀ + t)) (he'.shift t₀) ht₀
  obtain ⟨q, hq⟩ := hsp.2.1
  obtain ⟨p₀, hp₀⟩ := hSC.nonempty
  have : ι' q = ι ℓ := by
    rw [← hq, hsp.1 q p₀]; exact hout _ p₀ hp₀
  by_cases hqℓ : q = ℓ
  · subst hqℓ; simp only [ι', Function.update_self] at this; exact hi₀ ⟨q, this.symm⟩
  · simp only [ι', Function.update_of_ne hqℓ] at this; exact hqℓ (hι this)

/-- From `|IDSET| > |V|` (an injection `Option V ↪ ID`), every `ι : V → ID` misses an
identifier. -/
theorem exists_fresh (hcard : Nonempty (Option V ↪ ID)) (ι : V → ID) :
    ∃ i, i ∉ Set.range ι := by
  classical
  obtain ⟨f⟩ := hcard
  by_contra h
  push Not at h
  -- `f` would inject `Option V` into the range of `ι`, which has `|V|` elements
  have : Fintype.card (Option V) ≤ Fintype.card V := by
    choose g hg using h
    refine Fintype.card_le_of_injective (fun x => g (f x)) fun x y hxy => f.injective ?_
    simp only at hxy
    rw [← hg (f x), ← hg (f y), hxy]
  simp at this

/-- **Corollary 2.** Assume `|IDSET| > |V|`. If an algorithm is self-stabilizing for leader election
under the synchronous daemon in `G` for every assignment of unique identifiers, then `G` has at
most one source component (exactly one if `G` is nonempty, `Digraph.exists_isSourceComponent`). -/
theorem corollary2 (hcard : Nonempty (Option V ↪ ID)) (A : LEAlg G ID Q)
    (hss : ∀ ι, Function.Injective ι →
      SelfStab (IsSyncExec (A.next ι)) (SPLE (A.next ι) (A.out ι) ι))
    {S₁ S₂ : Set V} (h₁ : G.IsSourceComponent S₁) (h₂ : G.IsSourceComponent S₂) : S₁ = S₂ := by
  obtain ⟨f⟩ := hcard
  let ι : V → ID := fun v => f (some v)
  have hι : Function.Injective ι := fun a b h => Option.some_injective _ (f.injective h)
  obtain ⟨L, ⟨γ, hγ⟩, -, hcorr⟩ := hss ι hι
  let e : ℕ → V → Q := fun t => (A.next ι)^[t] γ
  have hsp := hcorr e (isSyncExec_iterate γ) hγ
  obtain ⟨ℓ, hℓ⟩ := hsp.2.1
  have hℓ' : ∀ p, A.out ι γ p = ι ℓ := fun p => (hsp.1 p ℓ).trans hℓ
  have hfresh := exists_fresh ⟨f⟩ ι
  have m₁ := lemma13 A hι hfresh hss (fun e he h0 => hcorr e he h0) hγ hℓ' h₁
  have m₂ := lemma13 A hι hfresh hss (fun e he h0 => hcorr e he h0) hγ hℓ' h₂
  exact h₁.eq_of_mem h₂ m₁ m₂

/-- Silent self-stabilization for the leader election predicate implies self-stabilization for
`SP_L` under the synchronous daemon. -/
theorem selfStab_of_silent [Nonempty Q] {next : (V → Q) → V → Q} {out : (V → Q) → V → ID}
    {ι : V → ID} (h : SilentSelfStabilizing next (IsSyncExec next) (LEPredicate out ι)) :
    SelfStab (IsSyncExec next) (SPLE next out ι) := by
  refine selfStab_iff.2 (h.selfStabilizing fun e he h0 hP => ?_)
  obtain ⟨ℓ, hℓ⟩ := hP
  have hconst : ∀ t, e t = e 0 := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => rw [he t, ih]; exact funext h0
  refine ⟨fun p q => by rw [hℓ, hℓ], ⟨ℓ, hℓ ℓ⟩, fun i p hi => absurd (hconst i ▸ h0) hi⟩

/-! ### PEL as an `LEAlg` and Corollary 3 -/

namespace PEL

variable {ID : Type*} [LinearOrder ID]

theorem isLocal (α : ℕ) (fixed : Bool) :
    IsLocal G (fun ι : V → ID => next G α fixed ι) := by
  intro ι ι' γ γ' p h
  have hp := h p (Or.inl rfl)
  have hq : ∀ q, G.Adj q p → ι q = ι' q ∧ γ q = γ' q := fun q hq => h q (Or.inr hq)
  -- the three layers see the same data
  have hmi : CMAI.next G α ι (miC α γ) p = CMAI.next G α ι' (miC α γ') p := by
    apply Subtype.ext
    exact CMAI.bestKey_congr hp.1 fun q hq' => by simp [miC, (hq q hq').2]
  have hIA : IA G γ p = IA G γ' p := by
    simp only [IA]
    congr 1
    apply propext
    exact forall_congr' fun q => imp_congr_right fun hq' => by rw [(hq q hq').2, hp.2]
  have ha : CMAI.next G α (IA G γ) (aC α γ) p = CMAI.next G α (IA G γ') (aC α γ') p := by
    apply Subtype.ext
    exact CMAI.bestKey_congr hIA fun q hq' => by simp [aC, (hq q hq').2]
  have hIE : IE fixed ι γ p = IE fixed ι' γ' p := by simp [IE, hp.1, hp.2]
  have he : CMAI.next G α (IE fixed ι γ) (eC α γ) p = CMAI.next G α (IE fixed ι' γ') (eC α γ') p := by
    apply Subtype.ext
    exact CMAI.bestKey_congr hIE fun q hq' => by simp [eC, (hq q hq').2]
  have hEnMI : EnMI G α ι γ p ↔ EnMI G α ι' γ' p := by
    simp only [EnMI, Enabled, hmi, miC, hp.2]
  have hEnA : EnA G α γ p ↔ EnA G α γ' p := by
    simp only [EnA, Enabled, ha, aC, hp.2]
  show next G α fixed ι γ p = next G α fixed ι' γ' p
  unfold next
  by_cases h1 : EnMI G α ι γ p
  · rw [ite_eq_left h1, ite_eq_left (hEnMI.mp h1), hmi, hp.2]
  · rw [ite_eq_right h1, ite_eq_right (mt hEnMI.mpr h1)]
    by_cases h2 : EnA G α γ p
    · rw [ite_eq_left h2, ite_eq_left (hEnA.mp h2), ha, hp.2]
    · rw [ite_eq_right h2, ite_eq_right (mt hEnA.mpr h2), he, hp.2]

/-- PEL as a leader-election algorithm in the sense of `LEAlg`. -/
noncomputable def toLEAlg (G : Digraph V) (α : ℕ) (fixed : Bool) : LEAlg G ID (PState ID α) where
  next ι := next G α fixed ι
  out _ γ p := leader γ p
  local_next := isLocal α fixed
  local_out _ _ γ γ' p _ h := by simp [leader, h]

end PEL

/-- **Corollary 3.** Assume `|IDSET| > |V|`, `IDSET` totally ordered, `V` nonempty and
`α ≥ MAD`. There is a silent self-stabilizing leader election algorithm under the distributed
unfair daemon (for every assignment of unique identifiers) iff `G` has exactly one source
component. -/
theorem corollary3 {ID : Type u} [LinearOrder ID] [Nonempty V] (hcard : Nonempty (Option V ↪ ID))
    {α : ℕ} (hα : MADLe G α) :
    (∃ (Q : Type u) (_ : Nonempty Q) (A : LEAlg G ID Q), ∀ ι, Function.Injective ι →
      SilentSelfStabilizing (A.next ι) (IsUnfairExec (A.next ι)) (LEPredicate (A.out ι) ι)) ↔
    ∃! SC, G.IsSourceComponent SC := by
  constructor
  · rintro ⟨Q, hQ, A, hA⟩
    obtain ⟨SC, hSC⟩ := Digraph.exists_isSourceComponent (G := G)
    refine ⟨SC, hSC, fun S hS => corollary2 hcard A (fun ι hι => ?_) hS hSC⟩
    exact selfStab_of_silent ((hA ι hι).mono fun _ he => IsSyncExec.isUnfairExec he)
  · rintro ⟨SC, hSC, huniq⟩
    refine ⟨PState ID α, ?_, PEL.toLEAlg G α false, fun ι _ => ?_⟩
    · obtain ⟨f⟩ := hcard
      exact ⟨⟨⟨⟨f none, 0⟩, Nat.zero_le _⟩, ⟨⟨true, 0⟩, Nat.zero_le _⟩,
        ⟨⟨toLex (true, f none), 0⟩, Nat.zero_le _⟩⟩⟩
    · exact PEL.theorem3 hα hSC huniq

/-- **Corollary 3 (synchronous daemon).** Same statement under the synchronous daemon. -/
theorem corollary3_sync {ID : Type u} [LinearOrder ID] [Nonempty V]
    (hcard : Nonempty (Option V ↪ ID)) {α : ℕ} (hα : MADLe G α) :
    (∃ (Q : Type u) (_ : Nonempty Q) (A : LEAlg G ID Q), ∀ ι, Function.Injective ι →
      SilentSelfStabilizing (A.next ι) (IsSyncExec (A.next ι)) (LEPredicate (A.out ι) ι)) ↔
    ∃! SC, G.IsSourceComponent SC := by
  constructor
  · rintro ⟨Q, hQ, A, hA⟩
    obtain ⟨SC, hSC⟩ := Digraph.exists_isSourceComponent (G := G)
    exact ⟨SC, hSC, fun S hS => corollary2 hcard A (fun ι hι => selfStab_of_silent (hA ι hι)) hS hSC⟩
  · intro h
    obtain ⟨Q, hQ, A, hA⟩ := (corollary3 hcard hα).mpr h
    exact ⟨Q, hQ, A, fun ι hι => (hA ι hι).mono fun _ he => IsSyncExec.isUnfairExec he⟩

end Papers.PODC2024.SSLeaderElectionDirected
