import Papers.PODC2025.GeneralizedQuorums.LowerBound

/-!
# The objects of the paper and their conflicting operations

Safety specifications (§6, §7 and Appendix A):

* lattice agreement over a partial order `V` (`laSafe`): Comparability, Downward validity and
  Upward validity (`y ≤ ⨆ X` is stated as "`y` is below every upper bound of the proposed values",
  which needs no `⊥`), for single-shot histories;
* consensus over `V` (`consSafe`): Agreement and Validity, for single-shot histories;
* MWMR atomic registers (`regSafe`): linearizability w.r.t. CSLib's `register V v₀`;
* SWMR atomic snapshots (`snapSafe`): linearizability w.r.t. `snapObj P V v₀`, for histories in
  which every process only updates its own segment.

Each has conflicting operations for any two distinct processes, provided the value domain is not
trivial (two incomparable elements for lattice agreement, two distinct values otherwise). Plugging
this into the generic lower bound gives Lemma 2 and Theorem 2 for each object.
-/

namespace Podc.GeneralizedQuorums

open Cslib.ChannelFailures Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-! ### Linearizations of one or two sequential operations -/

section Lin

variable {A : ObjSpec}

/-- A linearization of a single completed operation. -/
lemma lin_one {p : P} {o : A.Op} {a : A.Resp} {L : List (OpId P × A.Op)}
    (hL : IsLinearization [.inv p o, .ret p a] L) : (A.δ A.init o).2 = a := by
  have hc : Completed ([.inv p o, .ret p a] : List (Label P A)) (p, 0) := by simp [Completed]
  obtain ⟨y, hy, hy1⟩ := List.mem_map.1 (hL.complete _ hc)
  have hop := hL.op_eq y hy
  rw [hy1] at hop
  simp [opOf] at hop
  -- `L` contains only `(p, 0)`
  have hall : ∀ z ∈ L, z = ((p, 0), o) := by
    intro z hz
    have h := hL.op_eq z hz
    obtain ⟨⟨q, k⟩, o'⟩ := z
    simp only [opOf] at h
    by_cases hq : p = q
    · subst hq
      cases k with
      | zero => simp at h; simp [h]
      | succ k => simp at h
    · simp [hq] at h
  have hLy : L = [y] := by
    have hnd := hL.nodup
    rcases L with _ | ⟨z, L'⟩
    · simp at hy
    · rcases L' with _ | ⟨z', L''⟩
      · simp at hy; simp [hy]
      · have h1 := hall z (by simp)
        have h2 := hall z' (by simp)
        simp [h1, h2] at hnd
  have hseq := hL.seq
  rw [hLy] at hseq
  obtain ⟨⟨q, k⟩, o'⟩ := y
  simp only at hy1; obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy1
  simp only [SeqOK] at hseq
  have := hseq.1 a (by simp [respOf])
  simp only at hop; rw [hop]; exact this

/-- A linearization of two operations, the first completing before the second is invoked. -/
lemma lin_two {p₁ p₂ : P} (hne : p₁ ≠ p₂) {o₁ o₂ : A.Op} {a b : A.Resp}
    {L : List (OpId P × A.Op)}
    (hL : IsLinearization [.inv p₁ o₁, .ret p₁ a, .inv p₂ o₂, .ret p₂ b] L) :
    (A.δ A.init o₁).2 = a ∧ (A.δ (A.δ A.init o₁).1 o₂).2 = b := by
  set h : List (Label P A) := [.inv p₁ o₁, .ret p₁ a, .inv p₂ o₂, .ret p₂ b]
  have hne' : p₂ ≠ p₁ := Ne.symm hne
  have hop : ∀ z ∈ L, z = ((p₁, 0), o₁) ∨ z = ((p₂, 0), o₂) := by
    intro z hz
    have hz' := hL.op_eq z hz
    obtain ⟨⟨q, k⟩, o'⟩ := z
    simp only [opOf, h] at hz'
    by_cases hq₁ : p₁ = q
    · subst hq₁
      cases k with
      | zero => simp [hne'] at hz'; simp [hz']
      | succ k => simp [hne'] at hz'
    · by_cases hq₂ : p₂ = q
      · subst hq₂
        cases k with
        | zero => simp [hne] at hz'; simp [hz']
        | succ k => simp [hne] at hz'
      · simp [hq₁, hq₂] at hz'
  have hpre : Precedes h (p₁, 0) (p₂, 0) :=
    ⟨[.inv p₁ o₁, .ret p₁ a], [.inv p₂ o₂, .ret p₂ b], rfl, by simp [Completed],
      by simp [Invoked, hne]⟩
  have hc₂ : Completed h (p₂, 0) := by simp [Completed, h, hne]
  have hsub := hL.realtime _ _ hpre (hL.complete _ hc₂)
  have hsubset : L.map Prod.fst ⊆ [(p₁, 0), (p₂, 0)] := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hx
    rcases hop z hz with rfl | rfl <;> simp
  have hlen : (L.map Prod.fst).length ≤ 2 := (hL.nodup.subperm hsubset).length_le
  have hids : L.map Prod.fst = [(p₁, 0), (p₂, 0)] :=
    (hsub.eq_of_length_le hlen).symm
  rcases L with _ | ⟨z₁, _ | ⟨z₂, _ | ⟨z₃, L⟩⟩⟩ <;> simp at hids
  obtain ⟨h1, h2⟩ := hids
  have hz₁ : z₁ = ((p₁, 0), o₁) := by
    rcases hop z₁ (by simp) with h | h
    · exact h
    · rw [h] at h1; simp at h1; exact absurd h1.symm hne
  have hz₂ : z₂ = ((p₂, 0), o₂) := by
    rcases hop z₂ (by simp) with h | h
    · rw [h] at h2; simp at h2; exact absurd h2 hne
    · exact h
  have hseq := hL.seq
  rw [hz₁, hz₂] at hseq
  simp only [SeqOK] at hseq
  exact ⟨hseq.1 a (by simp [respOf, h]), hseq.2.1 b (by simp [respOf, h, hne])⟩

end Lin

/-- No process invokes two operations (single-shot objects). -/
def SingleShot {A : ObjSpec} (h : List (Label P A)) : Prop :=
  h.Pairwise fun l l' => ∀ p x x', l = .inv p x → l' = .inv p x' → False

/-! ### Lattice agreement -/

/-- The interface of lattice agreement over `V`: `propose(x)` returns a value of `V`. -/
abbrev laObj (V : Type) : ObjSpec where
  State := Unit
  Op := V
  Resp := V
  init := ()
  δ _ v := ((), v)

/-- Safety of (single-shot) lattice agreement: Comparability, Downward validity, Upward
validity. -/
def laSafe (V : Type) [PartialOrder V] (h : List (Label P (laObj V))) : Prop :=
  SingleShot h →
    (∀ p q (y y' : V), Label.ret p y ∈ h → Label.ret q y' ∈ h → y ≤ y' ∨ y' ≤ y) ∧
    (∀ p (y : V), Label.ret p y ∈ h → ∃ x : V, Label.inv p x ∈ h ∧ x ≤ y) ∧
    (∀ p (y : V), Label.ret p y ∈ h → ∀ z : V, (∀ q (x : V), Label.inv q x ∈ h → x ≤ z) → y ≤ z)

omit [DecidableEq P] in
lemma laSafe_solo {V : Type} [PartialOrder V] {p : P} {x y : V}
    (h : laSafe V [.inv p x, .ret p y]) : y = x := by
  obtain ⟨-, hd, hu⟩ := h (by simp [SingleShot])
  obtain ⟨x', hx', hle⟩ := hd p y (by simp)
  simp at hx'; subst hx'
  exact le_antisymm (hu p y (by simp) x' (by
    intro q x hx; simp at hx; rw [hx.2])) hle

omit [DecidableEq P] in
/-- Lattice agreement over a partial order with two incomparable elements has conflicting
operations. -/
theorem conflict_la {V : Type} [PartialOrder V] {x₁ x₂ : V} (h₁ : ¬ x₁ ≤ x₂) (h₂ : ¬ x₂ ≤ x₁)
    {p₁ p₂ : P} (hne : p₁ ≠ p₂) : Conflict (laSafe V) p₁ p₂ := by
  refine ⟨(x₁ : V), (x₂ : V), fun r₁ r₂ hs₁ hs₂ hs => ?_⟩
  have e₁ := laSafe_solo hs₁
  have e₂ := laSafe_solo hs₂
  have hss : SingleShot ([.inv p₁ x₁, .ret p₁ r₁, .inv p₂ x₂, .ret p₂ r₂] :
      List (Label P (laObj V))) := by
    simp only [SingleShot, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, ?_, ?_, by simp⟩ <;> intro l hl <;> rcases hl with rfl | rfl | rfl <;>
      intro p x x' h₁ h₂ <;> (try cases h₁) <;> (try cases h₂); exact hne rfl
  obtain ⟨hcmp, -, -⟩ := hs hss
  rcases hcmp p₁ p₂ r₁ r₂ (by simp) (by simp) with h | h
  · exact h₁ (e₁ ▸ e₂ ▸ h)
  · exact h₂ (e₁ ▸ e₂ ▸ h)

/-! ### Consensus -/

/-- The interface of consensus over `V`. -/
abbrev consObj (V : Type) : ObjSpec where
  State := Unit
  Op := V
  Resp := V
  init := ()
  δ _ v := ((), v)

/-- Safety of (single-shot) consensus: Agreement and Validity. -/
def consSafe (V : Type) (h : List (Label P (consObj V))) : Prop :=
  SingleShot h →
    (∀ p q (y y' : V), Label.ret p y ∈ h → Label.ret q y' ∈ h → y = y') ∧
    (∀ p (y : V), Label.ret p y ∈ h → ∃ q, Label.inv q y ∈ h)

omit [DecidableEq P] in
lemma consSafe_solo {V : Type} {p : P} {x y : V} (h : consSafe V [.inv p x, .ret p y]) :
    y = x := by
  obtain ⟨-, hv⟩ := h (by simp [SingleShot])
  obtain ⟨q, hq⟩ := hv p y (by simp)
  simp at hq; exact hq.2

omit [DecidableEq P] in
/-- Consensus over a set with two distinct values has conflicting operations. -/
theorem conflict_cons {V : Type} {x₁ x₂ : V} (hx : x₁ ≠ x₂) {p₁ p₂ : P} (hne : p₁ ≠ p₂) :
    Conflict (consSafe V) p₁ p₂ := by
  refine ⟨(x₁ : V), (x₂ : V), fun r₁ r₂ hs₁ hs₂ hs => ?_⟩
  have e₁ := consSafe_solo hs₁
  have e₂ := consSafe_solo hs₂
  have hss : SingleShot ([.inv p₁ x₁, .ret p₁ r₁, .inv p₂ x₂, .ret p₂ r₂] :
      List (Label P (consObj V))) := by
    simp only [SingleShot, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, ?_, ?_, by simp⟩ <;> intro l hl <;> rcases hl with rfl | rfl | rfl <;>
      intro p x x' h₁ h₂ <;> (try cases h₁) <;> (try cases h₂); exact hne rfl
  obtain ⟨hag, -⟩ := hs hss
  exact hx (e₁ ▸ e₂ ▸ hag p₁ p₂ r₁ r₂ (by simp) (by simp))

/-! ### MWMR atomic registers -/

/-- Safety of MWMR atomic registers: linearizability. -/
def regSafe (V : Type) (v₀ : V) (h : List (Label P (register V v₀))) : Prop :=
  ∃ L, IsLinearization h L

/-- A register with two distinct values has conflicting operations (a write, then a read). -/
theorem conflict_reg {V : Type} {v₀ x : V} (hx : x ≠ v₀) {p₁ p₂ : P} (hne : p₁ ≠ p₂) :
    Conflict (regSafe V v₀) p₁ p₂ := by
  refine ⟨RWOp.write x, RWOp.read, fun r₁ r₂ _ ⟨L₂, hL₂⟩ ⟨L, hL⟩ => ?_⟩
  have e₂ := lin_one hL₂
  have e := (lin_two hne hL).2
  exact hx (e.trans e₂.symm)

/-! ### SWMR atomic snapshots -/

/-- Operations of a snapshot object with one segment per process. -/
inductive SnapOp (P V : Type) where
  /-- Write `v` into segment `i`. -/
  | update (i : P) (v : V)
  /-- Read all segments. -/
  | scan

/-- An atomic snapshot object with segments indexed by `P` (initially `v₀`); `update` returns the
constant view `fun _ => v₀` (a dummy acknowledgement, independent of the state, so that `update`
carries no information beyond an `ack`). -/
abbrev snapObj (P V : Type) [DecidableEq P] (v₀ : V) : ObjSpec where
  State := P → V
  Op := SnapOp P V
  Resp := P → V
  init := fun _ => v₀
  δ s
    | .update i v => (Function.update s i v, fun _ => v₀)
    | .scan => (s, s)

/-- Safety of SWMR atomic snapshots: linearizability of the histories in which every process only
updates its own segment. -/
def snapSafe (V : Type) (v₀ : V) (h : List (Label P (snapObj P V v₀))) : Prop :=
  (∀ p i (v : V), Label.inv p (SnapOp.update i v : (snapObj P V v₀).Op) ∈ h → i = p) →
    ∃ L, IsLinearization h L

/-- A snapshot with two distinct values has conflicting operations (an update, then a scan). -/
theorem conflict_snap {V : Type} {v₀ x : V} (hx : x ≠ v₀) {p₁ p₂ : P} (hne : p₁ ≠ p₂) :
    Conflict (snapSafe V v₀) p₁ p₂ := by
  refine ⟨(SnapOp.update p₁ x : (snapObj P V v₀).Op), (SnapOp.scan : (snapObj P V v₀).Op),
    fun r₁ r₂ _ hs₂ hs => ?_⟩
  obtain ⟨L₂, hL₂⟩ := hs₂ (by intro p i v h; simp at h)
  obtain ⟨L, hL⟩ := hs (by
    intro p i v h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h <;> cases h; rfl)
  have e₂ := lin_one hL₂
  have e := (lin_two hne hL).2
  simp only [snapObj] at e e₂
  have := congrFun (e.trans e₂.symm) p₁
  simp at this
  exact hx this

end Podc.GeneralizedQuorums
