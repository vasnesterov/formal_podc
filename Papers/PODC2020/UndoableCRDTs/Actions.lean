import Papers.PODC2020.UndoableCRDTs.Defs

/-!
# Actions of a CRDT (Dolan, PODC 2020, Section 2.1 and Facts 1–6 of Section 2.4)

Propositions 1 and 2 (commutativity and undoability of actions) and Facts 1–6.
-/

namespace UndoableCRDTs.OpSystem

variable {C : OpSystem.{u, v}}

lemma ok_iff_isSome {s : C.S} {a : List C.P} : C.Ok s a ↔ (C.act s a).isSome :=
  Option.isSome_iff_exists.symm

lemma ok_of_act {s t : C.S} {a : List C.P} (h : C.act s a = some t) : C.Ok s a := ⟨t, h⟩

lemma ok_nil (s : C.S) : C.Ok s [] := ⟨s, rfl⟩

/-- `s · ab ok` iff `s · a ok` and `(s · a) · b ok`. -/
lemma ok_append_iff {s : C.S} {a b : List C.P} :
    C.Ok s (a ++ b) ↔ ∃ t, C.act s a = some t ∧ C.Ok t b := by
  rw [Ok, act_append]
  constructor
  · rintro ⟨u, hu⟩
    cases h : C.act s a with
    | none => simp [h] at hu
    | some t => exact ⟨t, rfl, u, by simpa [h] using hu⟩
  · rintro ⟨t, ht, u, hu⟩
    exact ⟨u, by simp [ht, hu]⟩

lemma ok_cons_iff {s : C.S} {p : C.P} {a : List C.P} :
    C.Ok s (p :: a) ↔ ∃ t, C.app p s = some t ∧ C.Ok t a := by
  simpa using ok_append_iff (C := C) (s := s) (a := [p]) (b := a)

/-- `s · ab ok` implies `s · a ok`. -/
lemma Ok.of_append_left {s : C.S} {a b : List C.P} (h : C.Ok s (a ++ b)) : C.Ok s a := by
  obtain ⟨t, ht, -⟩ := ok_append_iff.1 h
  exact ⟨t, ht⟩

/-- Auxiliary step of Proposition 1: a primitive operation commutes with an action. -/
lemma comm_cons (hc : C.Commutative) :
    ∀ (a : List C.P) (s : C.S) (p : C.P), C.Ok s [p] → C.Ok s a →
      C.Ok s (p :: a) ∧ C.act s (p :: a) = C.act s (a ++ [p]) := by
  intro a
  induction a with
  | nil => intro s p hp _; simpa using hp
  | cons q b ih =>
    intro s p hp ha
    obtain ⟨t₂, ht₂, hb⟩ := ok_cons_iff.1 ha
    obtain ⟨t₁, ht₁⟩ := hp
    simp only [act_singleton] at ht₁
    obtain ⟨-, -, hpq⟩ := hc s p q ⟨t₁, by simpa using ht₁⟩ ⟨t₂, by simpa using ht₂⟩
    have hqp : C.app p t₂ = C.app q t₁ := by
      simpa [act_cons, ht₁, ht₂] using hpq.symm
    -- `t₂ · p ok`
    have hp₂ : C.Ok t₂ [p] := by
      obtain ⟨⟨r, hr⟩, -⟩ := hc s p q ⟨t₁, by simpa using ht₁⟩ ⟨t₂, by simpa using ht₂⟩
      refine ⟨r, ?_⟩
      simp only [act_cons, ht₁, Option.bind_some] at hr
      simpa [hqp] using hr
    obtain ⟨hok, heq⟩ := ih t₂ p hp₂ hb
    obtain ⟨r, hr, hrb⟩ := ok_cons_iff.1 hok
    have hqr : C.app q t₁ = some r := hqp ▸ hr
    refine ⟨?_, ?_⟩
    · exact ok_cons_iff.2 ⟨t₁, ht₁, ok_cons_iff.2 ⟨r, hqr, hrb⟩⟩
    · rw [act_cons_of _ ht₁, act_cons_of _ hqr, List.cons_append, act_cons_of _ ht₂, ← heq,
        act_cons_of _ hr]

/-- **Proposition 1 (Commutativity of actions).** If `s · a ok` and `s · b ok`, then `s · ab`
and `s · ba` are well defined and equal. -/
theorem prop1 (hc : C.Commutative) {s : C.S} {a b : List C.P} (ha : C.Ok s a)
    (hb : C.Ok s b) : C.Ok s (a ++ b) ∧ C.Ok s (b ++ a) ∧ C.act s (a ++ b) = C.act s (b ++ a) := by
  suffices H : ∀ (b : List C.P) (s : C.S) (a : List C.P), C.Ok s a → C.Ok s b →
      C.Ok s (a ++ b) ∧ C.act s (a ++ b) = C.act s (b ++ a) by
    obtain ⟨h1, h2⟩ := H b s a ha hb
    exact ⟨h1, by rw [ok_iff_isSome, ← h2, ← ok_iff_isSome]; exact h1, h2⟩
  intro b
  induction b with
  | nil => intro s a ha _; simpa using ha
  | cons p c ih =>
    intro s a ha hb
    obtain ⟨t, ht, hc'⟩ := ok_cons_iff.1 hb
    obtain ⟨hpa, hpa_eq⟩ := comm_cons hc a s p ⟨t, by simpa using ht⟩ ha
    have hta : C.Ok t a := by
      obtain ⟨u, hu⟩ := hpa
      exact ⟨u, by rwa [act_cons_of _ ht] at hu⟩
    obtain ⟨hok, heq⟩ := ih t a hta hc'
    have key : C.act s (a ++ p :: c) = C.act t (a ++ c) := by
      have : a ++ p :: c = (a ++ [p]) ++ c := by simp
      rw [this, act_append, ← hpa_eq, ← act_append, List.cons_append, act_cons_of _ ht]
    refine ⟨?_, ?_⟩
    · rw [ok_iff_isSome, key, ← ok_iff_isSome]; exact hok
    · rw [key, heq, List.cons_append, act_cons_of _ ht]

/-- **Proposition 2 (Undoability of actions).** If `s · a ok`, there is an action `a⁻¹ₛ`
with `s · a a⁻¹ₛ = s`. -/
theorem prop2 (hu : C.Undoable) {s : C.S} {a : List C.P} (ha : C.Ok s a) :
    ∃ a', C.act s (a ++ a') = some s := by
  induction a generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons p b ih =>
    obtain ⟨t, ht, hb⟩ := ok_cons_iff.1 ha
    obtain ⟨b', hb'⟩ := ih hb
    obtain ⟨qs, hqs⟩ := hu s p ⟨t, by simpa using ht⟩
    refine ⟨b' ++ qs, ?_⟩
    rw [List.cons_append, act_cons_of _ ht, ← List.append_assoc, act_append_of _ hb',
      ← act_cons_of _ ht, hqs]

/-- **Fact 1.** If `a₁ ≡ₛ b₁` and `a₂ ≡ₛ b₂` then `a₁a₂ ≡ₛ b₁b₂` (here `a ≡ₛ b` means
`s · a ok`, `s · b ok`, `s · a = s · b`). -/
theorem fact1 (hc : C.Commutative) {s : C.S} {a₁ b₁ a₂ b₂ : List C.P}
    (_ha₁ : C.Ok s a₁) (hb₁ : C.Ok s b₁) (ha₂ : C.Ok s a₂) (hb₂ : C.Ok s b₂)
    (h₁ : C.act s a₁ = C.act s b₁) (h₂ : C.act s a₂ = C.act s b₂) :
    C.act s (a₁ ++ a₂) = C.act s (b₁ ++ b₂) := by
  calc C.act s (a₁ ++ a₂) = C.act s (b₁ ++ a₂) := by rw [act_append, act_append, h₁]
    _ = C.act s (a₂ ++ b₁) := (prop1 hc hb₁ ha₂).2.2
    _ = C.act s (b₂ ++ b₁) := by rw [act_append, act_append, h₂]
    _ = C.act s (b₁ ++ b₂) := (prop1 hc hb₂ hb₁).2.2

/-- **Fact 2.** If `s · a ok`, then `s · aa ok`. -/
theorem fact2 (hc : C.Commutative) {s : C.S} {a : List C.P} (ha : C.Ok s a) :
    C.Ok s (a ++ a) := (prop1 hc ha ha).1

/-- **Fact 3.** If `s · a ok` and `s · a a' = s` (`a' = a⁻¹ₛ`), then `(s · a) · a'a' ok`. -/
theorem fact3 (hc : C.Commutative) {s t : C.S} {a a' : List C.P} (ht : C.act s a = some t)
    (ha' : C.act s (a ++ a') = some s) : C.Ok t (a' ++ a') :=
  fact2 hc ⟨s, by rwa [act_append_of _ ht] at ha'⟩

/-- **Fact 4.** If `s · a ok` and `s · a a' = s`, then `s · a' ok`: actions can be undone
before they are performed. -/
theorem fact4 (hc : C.Commutative) {s : C.S} {a a' : List C.P} (ha : C.Ok s a)
    (ha' : C.act s (a ++ a') = some s) : C.Ok s a' := by
  obtain ⟨t, ht⟩ := ha
  have h3 := fact3 hc ht ha'
  have h1 : C.act t a' = some s := by rwa [act_append_of _ ht] at ha'
  rwa [ok_iff_isSome, act_append_of _ h1, ← ok_iff_isSome] at h3

/-- **Fact 5.** If `s · a ok` and `s · a a' = s`, then `a'a ≡ₛ aa' ≡ₛ ε`. -/
theorem fact5 (hc : C.Commutative) {s : C.S} {a a' : List C.P} (ha : C.Ok s a)
    (ha' : C.act s (a ++ a') = some s) : C.act s (a' ++ a) = some s := by
  rw [← (prop1 hc ha (fact4 hc ha ha')).2.2, ha']

/-- **Fact 6.** If `s · ab ok`, then `s · b ok` (any action that can be performed later can be
performed now). -/
theorem fact6 (hc : C.Commutative) (hu : C.Undoable) {s : C.S} {a b : List C.P}
    (hab : C.Ok s (a ++ b)) : C.Ok s b := by
  have ha := hab.of_append_left
  obtain ⟨a', ha'⟩ := prop2 hu ha
  have hinv := fact4 hc ha ha'
  -- `s · a⁻¹ (a b) ok` by Proposition 1, and `s · a⁻¹ a = s`.
  have h := (prop1 hc hinv hab).1
  rwa [← List.append_assoc, ok_iff_isSome, act_append_of _ (fact5 hc ha ha'),
    ← ok_iff_isSome] at h

/-- Consequence of Fact 6 and reachability: an action that is well defined in some state is
well defined in the initial state. -/
theorem ok_s0_of_ok (hc : C.Commutative) (hu : C.Undoable) (hr : C.Reachable) {s : C.S}
    {a : List C.P} (h : C.Ok s a) : C.Ok C.s0 a := by
  obtain ⟨b, hb⟩ := hr s
  exact fact6 hc hu (a := b) (by rwa [ok_iff_isSome, act_append_of _ hb, ← ok_iff_isSome])

/-- If `s · a ok` and `s · b ok`, then `(s · a) · b ok`. -/
theorem ok_act_of_ok (hc : C.Commutative) {s t : C.S} {a b : List C.P}
    (ht : C.act s a = some t) (hb : C.Ok s b) : C.Ok t b := by
  have h := (prop1 hc ⟨t, ht⟩ hb).1
  rwa [ok_iff_isSome, act_append_of _ ht, ← ok_iff_isSome] at h

/-- In an undoable CRDT, an action that applies in some state applies in every state
(Section 3, "All operations are always valid", for operations that apply somewhere). -/
theorem ok_of_ok (hc : C.Commutative) (hu : C.Undoable) (hr : C.Reachable) {s : C.S}
    {a : List C.P} (h : C.Ok s a) (t : C.S) : C.Ok t a := by
  obtain ⟨b, hb⟩ := hr t
  exact ok_act_of_ok hc hb (ok_s0_of_ok hc hu hr h)

end UndoableCRDTs.OpSystem
