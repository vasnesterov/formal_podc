import Papers.PODC2020.BezoutElection.Alg1

/-!
# Algorithm 1: steps of the implementation

The configurations of `(alg1 Id n out).impl ids π` (`Cfg`), the content of the single register
(`reg`), and a classification of all steps (`step_cases`): an invocation, a read (line 2 followed
by the local computation `afterRead`), a write, or a response.
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection.Alg1

variable {Id : Type} [DecidableEq Id] {R : Type} [Inhabited R] {P : Type} [DecidableEq P]

/-- Configurations of Algorithm 1. -/
abbrev Cfg (Id R P : Type) [Inhabited R] :=
  Config (elecObj R) (fun _ : Unit => memObj 1 (Reg Id) Reg.init) P (St Id)

/-- The content of the register `REG`. -/
def reg (C : Cfg Id R P) : Reg Id := C.mem () 0

lemma fin1_eq (x : Fin 1) : x = 0 := Subsingleton.elim _ _

/-- The invocation of `elect()`. -/
lemma alg1_invoke (n : ℕ) (out : Id → Id → R) (s : St Id) (o : Unit) :
    (alg1 Id n out).invoke s o = if s.pc = .idle then { s with pc := .read } else s := by
  simp only [alg1]
  cases s.pc <;> simp

/-- Classification of the steps of Algorithm 1. -/
theorem step_cases {n : ℕ} {out : Id → Id → R} {ids : P → Id} {π : P → Equiv.Perm (Fin 1)}
    {C C' : Cfg Id R P} {ℓ : Label P (elecObj R)}
    (h : ((alg1 Id n out).impl ids π).step C ℓ = some C') :
    (∃ p o, ℓ = .inv p o ∧ C.pend p = none ∧
        C'.loc = Function.update C.loc p
          (if (C.loc p).pc = .idle then { C.loc p with pc := .read } else C.loc p) ∧
        C'.pend = Function.update C.pend p (some o) ∧ reg C' = reg C) ∨
    (∃ p, ℓ = .tau p ∧ C.pend p ≠ none ∧ (C.loc p).pc = .read ∧
        C'.loc = Function.update C.loc p (afterRead n (C.loc p) (reg C)) ∧
        C'.pend = C.pend ∧ reg C' = reg C) ∨
    (∃ p w, ℓ = .tau p ∧ C.pend p ≠ none ∧ (C.loc p).pc = .write w ∧
        C'.loc = Function.update C.loc p { C.loc p with pc := .read } ∧
        C'.pend = C.pend ∧ reg C' = w) ∨
    (∃ p r, ℓ = .ret p r ∧ C.pend p ≠ none ∧ C'.pend = Function.update C.pend p none ∧
        reg C' = reg C ∧
        ((∃ a, (C.loc p).pc = .ret a ∧ r = out (C.loc p).me a ∧
            C'.loc = Function.update C.loc p { C.loc p with pc := .fin }) ∨
         (((C.loc p).pc = .idle ∨ (C.loc p).pc = .fin) ∧ C'.loc = C.loc))) := by
  cases ℓ with
  | inv p o =>
    obtain ⟨hp, rfl⟩ := SymAlg.impl_step_inv_cases h
    refine Or.inl ⟨p, o, rfl, hp, ?_, rfl, rfl⟩
    simp only [alg1_invoke]
  | tau p =>
    obtain ⟨hp, ⟨x, f, k, hact, rfl⟩ | ⟨k, hact, -⟩⟩ := SymAlg.impl_step_tau_cases h
    · have hx : x = 0 := fin1_eq x
      subst hx
      have h0 : (π p) 0 = 0 := fin1_eq _
      cases hpc : (C.loc p).pc with
      | read =>
        simp only [alg1, hpc, SymAction.rmw.injEq] at hact
        obtain ⟨-, rfl, rfl⟩ := hact
        refine Or.inr (Or.inl ⟨p, rfl, hp, hpc, ?_, rfl, ?_⟩)
        · simp only [h0]; rfl
        · simp [reg, h0]
      | write w =>
        simp only [alg1, hpc, SymAction.rmw.injEq] at hact
        obtain ⟨-, rfl, rfl⟩ := hact
        refine Or.inr (Or.inr (Or.inl ⟨p, w, rfl, hp, hpc, rfl, rfl, ?_⟩))
        simp [reg, h0]
      | _ => simp [alg1, hpc] at hact
    · cases hpc : (C.loc p).pc <;> simp [alg1, hpc] at hact
  | ret p r =>
    obtain ⟨hp, s, hact, rfl⟩ := SymAlg.impl_step_ret_cases h
    refine Or.inr (Or.inr (Or.inr ⟨p, r, rfl, hp, rfl, rfl, ?_⟩))
    cases hpc : (C.loc p).pc with
    | ret a =>
      simp only [alg1, hpc, SymAction.ret.injEq] at hact
      obtain ⟨rfl, rfl⟩ := hact
      exact Or.inl ⟨a, rfl, rfl, rfl⟩
    | idle =>
      simp only [alg1, hpc, SymAction.ret.injEq] at hact
      obtain ⟨-, rfl⟩ := hact
      exact Or.inr ⟨Or.inl rfl, by simp⟩
    | fin =>
      simp only [alg1, hpc, SymAction.ret.injEq] at hact
      obtain ⟨-, rfl⟩ := hact
      exact Or.inr ⟨Or.inr rfl, by simp⟩
    | _ => simp [alg1, hpc] at hact


/-! ### The local computation after a read -/

section AfterRead

variable (n : ℕ) (s : St Id) (r : Reg Id)

/-- The six outcomes of lines 3–18. -/
theorem afterRead_cases :
    (r.phase = .committing ∧ s.phase = .electing ∧
      afterRead n s r = { s with pc := .read, phase := .committing, disc := ∅ }) ∨
    (¬(r.phase = .committing ∧ s.phase = .electing) ∧ ∃ a, r.id = some a ∧
      r.disc.card = n - 1 ∧ r.phase = .committing ∧ afterRead n s r = { s with pc := .ret a }) ∨
    (¬(r.phase = .committing ∧ s.phase = .electing) ∧ ∃ a, r.id = some a ∧
      r.disc.card = n - 1 ∧ r.phase = .electing ∧
      afterRead n s r = { s with pc := .write ⟨none, ∅, .committing⟩ }) ∨
    (¬(r.phase = .committing ∧ s.phase = .electing) ∧ r.id = none ∧ s.loser = false ∧
      afterRead n s r =
        { s with pc := .write ⟨some s.me, if r.phase = s.phase then s.disc ∪ r.disc else s.disc,
                   s.phase⟩,
                 disc := if r.phase = s.phase then s.disc ∪ r.disc else s.disc }) ∨
    (¬(r.phase = .committing ∧ s.phase = .electing) ∧ ∃ a, r.id = some a ∧
      r.disc.card ≠ n - 1 ∧ a ≠ s.me ∧ s.me ∉ r.disc ∧
      afterRead n s r =
        { s with pc := .write ⟨none, insert s.me r.disc, s.phase⟩, loser := true,
                 disc := insert s.me r.disc }) ∨
    (afterRead n s r = { s with pc := .read } ∧ ¬(r.phase = .committing ∧ s.phase = .electing) ∧
      (r.id = none → s.loser = true) ∧
      ∀ a, r.id = some a → r.disc.card ≠ n - 1 ∧ (a = s.me ∨ s.me ∈ r.disc)) := by
  unfold afterRead
  by_cases hA : r.phase = .committing ∧ s.phase = .electing
  · exact Or.inl ⟨hA.1, hA.2, by rw [ite_eq_left hA]⟩
  rw [ite_eq_right hA]
  by_cases hB : r.disc.card = n - 1 ∧ r.id ≠ none
  · rw [ite_eq_left hB]
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hB.2
    by_cases hph : r.phase = .committing
    · refine Or.inr (Or.inl ⟨hA, a, ha, hB.1, hph, ?_⟩)
      simp [ha, hph]
    · have hph' : r.phase = .electing := by cases h : r.phase <;> simp_all
      exact Or.inr (Or.inr (Or.inl ⟨hA, a, ha, hB.1, hph', by simp [hph']⟩))
  rw [ite_eq_right hB]
  by_cases hC : r.id = none ∧ s.loser = false
  · rw [ite_eq_left hC]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hA, hC.1, hC.2, rfl⟩)))
  rw [ite_eq_right hC]
  by_cases hD : r.id ≠ none ∧ r.id ≠ some s.me ∧ s.me ∉ r.disc
  · rw [ite_eq_left hD]
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hD.1
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hA, a, ha, ?_, ?_, hD.2.2, rfl⟩))))
    · intro hc; exact hB ⟨hc, hD.1⟩
    · intro h; exact hD.2.1 (by rw [ha, h])
  rw [ite_eq_right hD]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, hA, ?_, ?_⟩))))
  · intro h; cases hl : s.loser
    · exact absurd ⟨h, hl⟩ hC
    · rfl
  · intro a ha
    refine ⟨fun hc => hB ⟨hc, by simp [ha]⟩, ?_⟩
    by_contra h'
    push Not at h'
    exact hD ⟨by simp [ha], by simp [ha, h'.1], h'.2⟩

@[simp] lemma afterRead_me : (afterRead n s r).me = s.me := by
  rcases afterRead_cases n s r with ⟨-, -, h⟩ | ⟨-, a, -, -, -, h⟩ | ⟨-, a, -, -, -, h⟩ |
    ⟨-, -, -, h⟩ | ⟨-, a, -, -, -, -, h⟩ | ⟨h, -⟩ <;> rw [h]

lemma afterRead_loser_of (h : s.loser = true) : (afterRead n s r).loser = true := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, a, -, -, -, -, h'⟩ | ⟨h', -⟩ <;> rw [h'] <;> simp [h]

lemma afterRead_phase_of (h : s.phase = .committing) :
    (afterRead n s r).phase = .committing := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, a, -, -, -, -, h'⟩ | ⟨h', -⟩ <;> rw [h'] <;> simp [h]

/-- A process becomes a loser only after reading a foreign identifier. -/
lemma afterRead_loser_new (h : (afterRead n s r).loser = true) :
    s.loser = true ∨ ∃ a, r.id = some a ∧ a ≠ s.me := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, a, ha, -, hne, -, h'⟩ | ⟨h', -⟩ <;> rw [h'] at h <;> simp_all

lemma afterRead_disc (x : Id) (hx : x ∈ (afterRead n s r).disc) :
    x ∈ s.disc ∨ x ∈ r.disc ∨ (x = s.me ∧ (afterRead n s r).loser = true) := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, a, ha, -, hne, -, h'⟩ | ⟨h', -⟩ <;> rw [h'] at hx ⊢
  · simp at hx
  · exact Or.inl hx
  · exact Or.inl hx
  · dsimp only at hx; split_ifs at hx
    · rcases Finset.mem_union.1 hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inl hx
  · rcases Finset.mem_insert.1 hx with h | h
    · exact Or.inr (Or.inr ⟨h, rfl⟩)
    · exact Or.inr (Or.inl h)
  · exact Or.inl hx

/-- What a process may decide to write. -/
lemma afterRead_write {w : Reg Id} (h : (afterRead n s r).pc = .write w) :
    w = ⟨none, ∅, .committing⟩ ∨
    (w = ⟨some s.me, (afterRead n s r).disc, (afterRead n s r).phase⟩ ∧
      (afterRead n s r).loser = false) ∨
    (w = ⟨none, (afterRead n s r).disc, (afterRead n s r).phase⟩ ∧
      (afterRead n s r).loser = true) := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, hl, h'⟩ | ⟨-, a, ha, -, hne, -, h'⟩ | ⟨h', -⟩ <;> rw [h'] at h ⊢ <;>
    simp only [PC.write.injEq, reduceCtorEq] at h <;> subst h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨rfl, hl⟩)
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- A process decides to return only after reading a committing value with `n - 1` discarded
identifiers. -/
lemma afterRead_ret {a : Id} (h : (afterRead n s r).pc = .ret a) :
    r.id = some a ∧ r.disc.card = n - 1 ∧ r.phase = .committing := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, b, hb, hc, hph, h'⟩ | ⟨-, b, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, b, -, -, -, -, h'⟩ | ⟨h', -⟩ <;> rw [h'] at h <;>
    simp only [PC.ret.injEq, reduceCtorEq] at h
  subst h; exact ⟨hb, hc, hph⟩

lemma afterRead_pc : (afterRead n s r).pc = .read ∨ (∃ w, (afterRead n s r).pc = .write w) ∨
    ∃ a, (afterRead n s r).pc = .ret a := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, a, -, -, -, -, h'⟩ | ⟨h', -⟩ <;> rw [h'] <;> simp

/-- A non-loser that stays a non-loser in the same phase only adds identifiers to its
`discarded` set. -/
lemma afterRead_disc_mono (h2 : (afterRead n s r).loser = false)
    (h3 : (afterRead n s r).phase = s.phase) : s.disc ⊆ (afterRead n s r).disc := by
  rcases afterRead_cases n s r with ⟨-, hs, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, a, -, -, -, -, h'⟩ | ⟨h', -⟩
  · rw [h', hs] at h3; simp at h3
  · rw [h']; try exact Finset.Subset.refl _
  · rw [h']; try exact Finset.Subset.refl _
  · rw [h']; dsimp only; split_ifs
    · exact Finset.subset_union_left
    · exact Finset.Subset.refl _
  · rw [h'] at h2; simp at h2
  · rw [h']; try exact Finset.Subset.refl _

/-- The only phase change is line 4. -/
lemma afterRead_phase_change (h1 : s.phase = .electing)
    (h2 : (afterRead n s r).phase = .committing) :
    r.phase = .committing ∧ afterRead n s r = { s with pc := .read, phase := .committing, disc := ∅ } := by
  rcases afterRead_cases n s r with ⟨hr, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨-, a, -, -, -, -, h'⟩ | ⟨h', -⟩
  · exact ⟨hr, h'⟩
  all_goals rw [h'] at h2; simp [h1] at h2

/-- What a process may decide to write as a `⊥`-value: line 8 or line 17. -/
lemma afterRead_write_none {Y : Finset Id} {ph : Phase}
    (h : (afterRead n s r).pc = .write ⟨none, Y, ph⟩) :
    (Y = ∅ ∧ ph = .committing ∧ ∃ a, r.id = some a ∧ r.disc.card = n - 1 ∧
      r.phase = .electing) ∨
    (∃ a, r.id = some a ∧ a ≠ s.me ∧ s.me ∉ r.disc ∧ Y = insert s.me r.disc ∧ ph = s.phase ∧
      ¬(r.phase = .committing ∧ s.phase = .electing)) := by
  rcases afterRead_cases n s r with ⟨-, -, h'⟩ | ⟨-, a, -, -, -, h'⟩ | ⟨-, a, ha, hc, hph, h'⟩ |
    ⟨-, -, -, h'⟩ | ⟨hnA, a, ha, -, hne, hni, h'⟩ | ⟨h', -⟩ <;> rw [h'] at h <;>
    simp only [PC.write.injEq, Reg.mk.injEq, reduceCtorEq, false_and] at h
  · obtain ⟨-, rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl, a, ha, hc, hph⟩
  · obtain ⟨-, rfl, rfl⟩ := h
    exact Or.inr ⟨a, ha, hne, hni, rfl, rfl, hnA⟩

end AfterRead

end BezoutElection.Alg1
