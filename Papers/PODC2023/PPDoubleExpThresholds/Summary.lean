import Papers.PODC2023.PPDoubleExpThresholds.Program

/-!
# Procedure-level semantics of population programs

The paper analyses procedures through the outcomes of a call (Section 4, "Notation"):
`C, f → C', b` (`f` may return `b` with registers `C'`), `C, f → restart`, `C, f → ⊥` (`f` may hang
or not terminate), and `post(C, f)` is the set of these outcomes.

We define them from the instruction-level semantics `Program.Step₀` (steps other than `restart`):

* `Returns p C OF C' OF' b`: from the call of `p` (stack `[(p, 0)]`), a `return b` of `p` with
  registers `C'` and flag `OF'` is reachable;
* `Restarts p C OF`: a `restart` instruction is reachable during the call;
* `Terminates p C OF`: from every configuration reachable during the call, a `return` of `p` or a
  `restart` is reachable. Under (global) fairness this is exactly "the call cannot hang and cannot
  run forever", so `⊥ ∈ post(C, f)` iff `¬ Terminates`.

The *abstract step* `AStep p` executes one instruction of `p` and treats calls as single steps
using `Returns` of the callee. `reach_cases` decomposes every configuration reachable during a call
of `p` into an abstract configuration of `p`, possibly inside a call of a callee. The lemmas
`returns_iff`, `restarts_iff`, `terminates_of` and `agef` reduce the analysis of a procedure to its
abstract steps.
-/

namespace Podc.PPDoubleExpThresholds

open Cslib.TransitionSystem

variable {R P : Type*} [DecidableEq R]

namespace Program

variable (prog : Program R P)

/-- Reachability through non-`restart` steps. -/
abbrev Reach₀ : Cfg R P → Cfg R P → Prop := Reach prog.Step₀

/-- The configuration at the beginning of a call of `p`. -/
def start (p : P) (C : R → ℕ) (OF : Bool) : Cfg R P := ⟨C, OF, [(p, 0)]⟩

/-- `C, p → C', b`: a call of `p` may return `b` with registers `C'` (and output flag `OF'`). -/
def Returns (p : P) (C : R → ℕ) (OF : Bool) (C' : R → ℕ) (OF' : Bool) (b : Bool) : Prop :=
  ∃ pc, prog.Reach₀ (start p C OF) ⟨C', OF', [(p, pc)]⟩ ∧ prog.instr p pc = some (.ret b)

/-- `C, p → restart`. -/
def Restarts (p : P) (C : R → ℕ) (OF : Bool) : Prop :=
  ∃ s, prog.Reach₀ (start p C OF) s ∧ prog.AtRestart s

/-- A configuration in which the call of `p` (bottom frame) is done: it returns or restarts. -/
def IsDone (p : P) (s : Cfg R P) : Prop :=
  prog.AtRestart s ∨ ∃ pc b, s.stk = [(p, pc)] ∧ prog.instr p pc = some (.ret b)

/-- The call of `p` terminates: from every configuration reachable during the call, a return or a
restart is reachable (`⊥ ∉ post(C, p)`). -/
def Terminates (p : P) (C : R → ℕ) (OF : Bool) : Prop :=
  ∀ s, prog.Reach₀ (start p C OF) s → ∃ s', prog.Reach₀ s s' ∧ prog.IsDone p s'

/-- From `s` a `restart` is reachable without restarting before. -/
def CanRestart (s : Cfg R P) : Prop := ∃ s', prog.Reach₀ s s' ∧ prog.AtRestart s'

end Program

/-- Possible outcomes of a procedure call. -/
inductive Outcome (R : Type*)
  /-- Return `b` with register configuration `C`. -/
  | ret (C : R → ℕ) (b : Bool)
  /-- Initiate a restart. -/
  | restart
  /-- Hang or run forever. -/
  | bot

namespace Program

variable (prog : Program R P)

/-- `post(C, p)` (Section 4), for a call with output flag `OF` (all procedures except `Main` leave
`OF` unchanged). -/
def post (p : P) (C : R → ℕ) (OF : Bool) : Set (Outcome R) :=
  {o | match o with
    | .ret C' b => prog.Returns p C OF C' OF b
    | .restart => prog.Restarts p C OF
    | .bot => ¬ prog.Terminates p C OF}

/-! ### Frames -/

variable {prog}

theorem Step₀.append {s s' : Cfg R P} (h : prog.Step₀ s s') (τ : List (P × ℕ)) :
    prog.Step₀ ⟨s.C, s.OF, s.stk ++ τ⟩ ⟨s'.C, s'.OF, s'.stk ++ τ⟩ := by
  cases h with
  | move h hx => exact .move h hx
  | swap h => exact .swap h
  | setOF h => exact .setOF h
  | detectT h hx => exact .detectT h hx
  | detectF h => exact .detectF h
  | goto h => exact .goto h
  | call h => exact .call h
  | ret h h' => exact .ret h h'

theorem Reach₀.append {s s' : Cfg R P} (h : prog.Reach₀ s s') (τ : List (P × ℕ)) :
    prog.Reach₀ ⟨s.C, s.OF, s.stk ++ τ⟩ ⟨s'.C, s'.OF, s'.stk ++ τ⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail (h.append τ)

/-- A step from a stack `σ ++ τ` that does not return from the bottom frame of `σ` is a step of
`σ`. -/
theorem Step₀.of_append {s d : Cfg R P} (h : prog.Step₀ s d) {σ τ : List (P × ℕ)}
    (hs : s.stk = σ ++ τ) (hσ : σ ≠ [])
    (hret : ∀ q pc b, σ = [(q, pc)] → prog.instr q pc ≠ some (.ret b)) :
    ∃ σ', σ' ≠ [] ∧ d.stk = σ' ++ τ ∧ prog.Step₀ ⟨s.C, s.OF, σ⟩ ⟨d.C, d.OF, σ'⟩ := by
  obtain _ | ⟨⟨p, pc⟩, σ₁⟩ := σ
  · exact absurd rfl hσ
  cases h with
  | move h hx => simp at hs; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs; exact ⟨_, by simp, rfl, .move h hx⟩
  | swap h => simp at hs; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs; exact ⟨_, by simp, rfl, .swap h⟩
  | setOF h => simp at hs; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs; exact ⟨_, by simp, rfl, .setOF h⟩
  | detectT h hx => simp at hs; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs; exact ⟨_, by simp, rfl, .detectT h hx⟩
  | detectF h => simp at hs; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs; exact ⟨_, by simp, rfl, .detectF h⟩
  | goto h => simp at hs; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs; exact ⟨_, by simp, rfl, .goto h⟩
  | call h => simp at hs; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs; exact ⟨_ :: _ :: σ₁, by simp, rfl, .call h⟩
  | ret h h' =>
    simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq] at hs
    obtain ⟨⟨rfl, rfl⟩, hs⟩ := hs
    obtain _ | ⟨⟨p', pc'⟩, σ₂⟩ := σ₁
    · exact absurd h (hret _ _ _ rfl)
    · simp only [List.cons_append, List.cons.injEq, Prod.mk.injEq] at hs
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hs
      exact ⟨_, by simp, rfl, .ret h h'⟩

theorem cons_eq_append_aux {p q : P} {pc pc'' r : ℕ} {σ₀ σ : List (P × ℕ)}
    (h : (p, pc) :: σ₀ = σ ++ [(q, r)]) : ∃ σ' r', (p, pc'') :: σ₀ = σ' ++ [(q, r')] := by
  cases σ with
  | nil => simp at h; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h; exact ⟨[], pc'', rfl⟩
  | cons a σ => simp at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨(p, pc'') :: σ, r, rfl⟩

/-- The bottom frame keeps its procedure. -/
theorem Reach₀.bottom {C OF} {q : P} {pc : ℕ} {s : Cfg R P}
    (h : prog.Reach₀ ⟨C, OF, [(q, pc)]⟩ s) : ∃ σ pc', s.stk = σ ++ [(q, pc')] := by
  induction h with
  | refl => exact ⟨[], pc, rfl⟩
  | tail _ h ih =>
    obtain ⟨σ, pc', hσ⟩ := ih
    cases h with
    | move => exact cons_eq_append_aux hσ
    | swap => exact cons_eq_append_aux hσ
    | setOF => exact cons_eq_append_aux hσ
    | detectT => exact cons_eq_append_aux hσ
    | detectF => exact cons_eq_append_aux hσ
    | goto => exact cons_eq_append_aux hσ
    | call => exact ⟨_ :: σ, pc', by simp only at hσ ⊢; rw [hσ]; rfl⟩
    | ret =>
      obtain _ | ⟨_, σ⟩ := σ
      · simp at hσ
      · simp only [List.cons_append, List.cons.injEq] at hσ
        exact cons_eq_append_aux hσ.2

/-! ### Abstract steps -/

/-- Abstract configurations of a procedure: program counter, registers, output flag. -/
structure Loc (R : Type*) where
  /-- Program counter. -/
  pc : ℕ
  /-- Registers. -/
  C : R → ℕ
  /-- Output flag. -/
  OF : Bool

variable (prog)

/-- The configuration of a call of `p` at abstract configuration `a`. -/
def atLoc (p : P) (a : Loc R) : Cfg R P := ⟨a.C, a.OF, [(p, a.pc)]⟩

/-- Abstract steps of procedure `p`: one instruction of `p`, a call being one step to one of the
callee's returns. -/
inductive AStep (p : P) : Loc R → Loc R → Prop
  | move {pc C OF x y} (h : prog.instr p pc = some (.move x y)) (hx : 0 < C x) :
      AStep p ⟨pc, C, OF⟩ ⟨pc + 1, mv C x y, OF⟩
  | swap {pc C OF x y} (h : prog.instr p pc = some (.swap x y)) :
      AStep p ⟨pc, C, OF⟩ ⟨pc + 1, swp C x y, OF⟩
  | setOF {pc C OF b} (h : prog.instr p pc = some (.setOF b)) :
      AStep p ⟨pc, C, OF⟩ ⟨pc + 1, C, b⟩
  | detectT {pc C OF x tT tF} (h : prog.instr p pc = some (.detect x tT tF)) (hx : 0 < C x) :
      AStep p ⟨pc, C, OF⟩ ⟨tT, C, OF⟩
  | detectF {pc C OF x tT tF} (h : prog.instr p pc = some (.detect x tT tF)) :
      AStep p ⟨pc, C, OF⟩ ⟨tF, C, OF⟩
  | goto {pc C OF t} (h : prog.instr p pc = some (.goto t)) :
      AStep p ⟨pc, C, OF⟩ ⟨t, C, OF⟩
  | call {pc C OF q tT tF C' OF' b} (h : prog.instr p pc = some (.call q tT tF))
      (hr : prog.Returns q C OF C' OF' b) :
      AStep p ⟨pc, C, OF⟩ ⟨cond b tT tF, C', OF'⟩

/-- Abstract reachability. -/
abbrev AReach (p : P) : Loc R → Loc R → Prop := Reach (prog.AStep p)

variable {prog}

theorem AStep.reach₀ {p : P} {a a' : Loc R} (h : prog.AStep p a a') (τ : List (P × ℕ)) :
    prog.Reach₀ ⟨a.C, a.OF, (p, a.pc) :: τ⟩ ⟨a'.C, a'.OF, (p, a'.pc) :: τ⟩ := by
  cases h with
  | move h hx => exact .single (.move h hx)
  | swap h => exact .single (.swap h)
  | setOF h => exact .single (.setOF h)
  | detectT h hx => exact .single (.detectT h hx)
  | detectF h => exact .single (.detectF h)
  | goto h => exact .single (.goto h)
  | call h hr =>
    rename_i pc C OF q tT tF C' OF' b
    obtain ⟨pc', hr, hret⟩ := hr
    have := Reach₀.append hr ((p, pc) :: τ)
    exact (Relation.ReflTransGen.single (.call h)).trans (this.tail (.ret hret h))

theorem AReach.reach₀ {p : P} {a a' : Loc R} (h : prog.AReach p a a') (τ : List (P × ℕ)) :
    prog.Reach₀ ⟨a.C, a.OF, (p, a.pc) :: τ⟩ ⟨a'.C, a'.OF, (p, a'.pc) :: τ⟩ := by
  induction h with
  | refl => exact .refl
  | tail _ h ih => exact ih.trans (h.reach₀ τ)

/-- **Decomposition of a call.** Every configuration reachable during a call of `p` is either an
abstract configuration of `p`, or inside a call of a callee `q` made from an abstract configuration
of `p`. -/
theorem reach_cases {p : P} {a₀ : Loc R} {s : Cfg R P} (h : prog.Reach₀ (atLoc p a₀) s) :
    (∃ a, prog.AReach p a₀ a ∧ s = atLoc p a) ∨
    (∃ a q tT tF σ, prog.AReach p a₀ a ∧ prog.instr p a.pc = some (.call q tT tF) ∧ σ ≠ [] ∧
      prog.Reach₀ (start q a.C a.OF) ⟨s.C, s.OF, σ⟩ ∧ s.stk = σ ++ [(p, a.pc)]) := by
  induction h with
  | refl => exact .inl ⟨a₀, .refl, rfl⟩
  | @tail s d _ hsd ih =>
    rcases ih with ⟨a, ha, rfl⟩ | ⟨a, q, tT, tF, σ, ha, hcall, hσ, hreach, hstk⟩
    · obtain ⟨pc, C, OF⟩ := a
      cases hsd with
      | move h hx => exact .inl ⟨_, ha.tail (.move h hx), rfl⟩
      | swap h => exact .inl ⟨_, ha.tail (.swap h), rfl⟩
      | setOF h => exact .inl ⟨_, ha.tail (.setOF h), rfl⟩
      | detectT h hx => exact .inl ⟨_, ha.tail (.detectT h hx), rfl⟩
      | detectF h => exact .inl ⟨_, ha.tail (.detectF h), rfl⟩
      | goto h => exact .inl ⟨_, ha.tail (.goto h), rfl⟩
      | call h => exact .inr ⟨_, _, _, _, _, ha, h, by simp, .refl, rfl⟩
    · by_cases hret : ∃ q' pc' b, σ = [(q', pc')] ∧ prog.instr q' pc' = some (.ret b)
      · obtain ⟨q', pc', b, rfl, hb⟩ := hret
        obtain ⟨σ', pc'', hσ'⟩ := Reach₀.bottom hreach
        have hq : q' = q := by
          obtain _ | ⟨_, σ'⟩ := σ' <;> simp_all
        subst hq
        obtain ⟨C, OF, stk⟩ := s
        simp only at hstk
        subst hstk
        cases hsd with
        | move h => simp_all
        | swap h => simp_all
        | setOF h => simp_all
        | detectT h => simp_all
        | detectF h => simp_all
        | goto h => simp_all
        | call h => simp_all
        | ret h h' =>
          rw [hcall] at h'
          cases h'
          rw [hb] at h
          cases h
          exact .inl ⟨_, ha.tail (.call hcall ⟨pc', hreach, hb⟩), rfl⟩
      · push Not at hret
        obtain ⟨σ', hσ', hd, hstep⟩ := hsd.of_append hstk hσ fun q pc b h => hret q pc b h
        exact .inr ⟨a, q, tT, tF, σ', ha, hcall, hσ', hreach.tail hstep, hd⟩

omit [DecidableEq R] in
/-- The abstract configuration at the start of a call. -/
theorem start_eq_atLoc (p : P) (C : R → ℕ) (OF : Bool) :
    (start p C OF : Cfg R P) = atLoc p ⟨0, C, OF⟩ := rfl

/-- `Returns` through abstract steps. -/
theorem returns_iff {p : P} {C C' : R → ℕ} {OF OF' : Bool} {b : Bool} :
    prog.Returns p C OF C' OF' b ↔
      ∃ a, prog.AReach p ⟨0, C, OF⟩ a ∧ a.C = C' ∧ a.OF = OF' ∧ prog.instr p a.pc = some (.ret b) := by
  constructor
  · rintro ⟨pc, h, hb⟩
    rcases reach_cases (a₀ := ⟨0, C, OF⟩) h with ⟨a, ha, he⟩ | ⟨a, q, tT, tF, σ, -, -, hσ, -, hstk⟩
    · simp only [atLoc, Cfg.mk.injEq, List.cons.injEq, Prod.mk.injEq, and_true] at he
      obtain ⟨rfl, rfl, -, rfl⟩ := he
      exact ⟨a, ha, rfl, rfl, hb⟩
    · obtain _ | ⟨_, _ | ⟨_, _⟩⟩ := σ <;> simp_all
  · rintro ⟨a, ha, rfl, rfl, hb⟩
    exact ⟨a.pc, ha.reach₀ [], hb⟩

/-- `Restarts` through abstract steps: a reachable `restart`, or a reachable call that may
restart. -/
theorem restarts_iff {p : P} {C : R → ℕ} {OF : Bool} :
    prog.Restarts p C OF ↔
      ∃ a, prog.AReach p ⟨0, C, OF⟩ a ∧ (prog.instr p a.pc = some .restart ∨
        ∃ q tT tF, prog.instr p a.pc = some (.call q tT tF) ∧ prog.Restarts q a.C a.OF) := by
  constructor
  · rintro ⟨s, h, p', pc', σ', hs, hr⟩
    rcases reach_cases (a₀ := ⟨0, C, OF⟩) h with ⟨a, ha, rfl⟩ | ⟨a, q, tT, tF, σ, ha, hcall, hσ, hreach, hstk⟩
    · simp only [atLoc, List.cons.injEq, Prod.mk.injEq] at hs
      obtain ⟨⟨rfl, rfl⟩, -⟩ := hs
      exact ⟨a, ha, .inl hr⟩
    · obtain _ | ⟨f, σ₁⟩ := σ
      · exact absurd rfl hσ
      · rw [hstk] at hs; simp only [List.cons_append, List.cons.injEq] at hs
        exact ⟨a, ha, .inr ⟨q, tT, tF, hcall, ⟨_, hreach, p', pc', σ₁, by simp [hs.1], hr⟩⟩⟩
  · rintro ⟨a, ha, hr | ⟨q, tT, tF, hcall, s, hs, hr⟩⟩
    · exact ⟨_, ha.reach₀ [], p, a.pc, [], rfl, hr⟩
    · refine ⟨⟨s.C, s.OF, s.stk ++ [(p, a.pc)]⟩, (ha.reach₀ []).trans ?_, ?_⟩
      · exact (Relation.ReflTransGen.single (.call hcall)).trans (Reach₀.append hs [(p, a.pc)])
      · obtain ⟨p', pc', σ', h1, h2⟩ := hr
        exact ⟨p', pc', σ' ++ [(p, a.pc)], by simp [h1], h2⟩

/-- **Reachability of a target from everywhere.** If every callee call from a reachable abstract
configuration terminates, and from every reachable abstract configuration a target configuration is
reachable, then from every configuration reachable during the call a target configuration is
reachable. The target must contain all configurations about to restart. -/
theorem agef {p : P} {a₀ : Loc R} {G : Cfg R P → Prop} (hG : ∀ s, prog.AtRestart s → G s)
    (hterm : ∀ a, prog.AReach p a₀ a → ∀ q tT tF, prog.instr p a.pc = some (.call q tT tF) →
      prog.Terminates q a.C a.OF)
    (h : ∀ a, prog.AReach p a₀ a → ∃ s', prog.Reach₀ (atLoc p a) s' ∧ G s') :
    ∀ s, prog.Reach₀ (atLoc p a₀) s → ∃ s', prog.Reach₀ s s' ∧ G s' := by
  intro s hs
  rcases reach_cases hs with ⟨a, ha, rfl⟩ | ⟨a, q, tT, tF, σ, ha, hcall, hσ, hreach, hstk⟩
  · exact h a ha
  · obtain ⟨s', hs', hdone⟩ := hterm a ha q tT tF hcall _ hreach
    have hlift := Reach₀.append hs' [(p, a.pc)]
    have hs_eq : (⟨s.C, s.OF, s.stk⟩ : Cfg R P) = s := rfl
    rw [hstk] at hs_eq
    rcases hdone with ⟨p', pc', σ', h1, h2⟩ | ⟨pc', b, h1, h2⟩
    · refine ⟨_, hs_eq ▸ hlift, hG _ ⟨p', pc', σ' ++ [(p, a.pc)], by simp [h1], h2⟩⟩
    · -- the callee returns: one more step back to `p`
      obtain ⟨C', OF', stk'⟩ := s'
      simp only at h1
      subst h1
      have hret : prog.Returns q a.C a.OF C' OF' b := ⟨pc', hreach.trans hs', h2⟩
      have ha' : prog.AReach p a₀ ⟨cond b tT tF, C', OF'⟩ := ha.tail (.call hcall hret)
      obtain ⟨s'', hs'', hG''⟩ := h _ ha'
      refine ⟨s'', ?_, hG''⟩
      rw [← hs_eq]
      exact (hlift.tail (.ret h2 hcall)).trans hs''


variable (prog) in
/-- An abstract configuration from which a `restart` is immediately reachable: a `restart`
instruction, or a call that may restart. -/
def ARst (p : P) (a : Loc R) : Prop :=
  prog.instr p a.pc = some .restart ∨
    ∃ q tT tF, prog.instr p a.pc = some (.call q tT tF) ∧ prog.Restarts q a.C a.OF

variable (prog) in
/-- An abstract configuration at which the call of `p` may end: a `return`, or `ARst`. -/
def ADone (p : P) (a : Loc R) : Prop :=
  (∃ b, prog.instr p a.pc = some (.ret b)) ∨ prog.ARst p a

theorem ARst.reach {p : P} {a : Loc R} (h : prog.ARst p a) :
    ∃ s', prog.Reach₀ (atLoc p a) s' ∧ prog.AtRestart s' := by
  rcases h with hr | ⟨q, tT, tF, hcall, s, hs, p', pc', σ', h1, h2⟩
  · exact ⟨_, .refl, p, a.pc, [], rfl, hr⟩
  · refine ⟨⟨s.C, s.OF, s.stk ++ [(p, a.pc)]⟩, ?_, p', pc', σ' ++ [(p, a.pc)], by simp [h1], h2⟩
    exact (Relation.ReflTransGen.single (.call hcall)).trans (Reach₀.append hs [(p, a.pc)])

/-- **Termination through abstract steps.** If all calls made from reachable abstract
configurations terminate, and from every reachable abstract configuration one can reach a `return`
or a (possible) `restart`, the call terminates. -/
theorem terminates_of {p : P} {C : R → ℕ} {OF : Bool}
    (hterm : ∀ a, prog.AReach p ⟨0, C, OF⟩ a → ∀ q tT tF,
      prog.instr p a.pc = some (.call q tT tF) → prog.Terminates q a.C a.OF)
    (h : ∀ a, prog.AReach p ⟨0, C, OF⟩ a → ∃ a', prog.AReach p a a' ∧ prog.ADone p a') :
    prog.Terminates p C OF := by
  refine agef (a₀ := ⟨0, C, OF⟩) (G := prog.IsDone p) (fun s hs => .inl hs) hterm ?_
  intro a ha
  obtain ⟨a', haa', hd⟩ := h a ha
  rcases hd with ⟨b, hb⟩ | hr
  · exact ⟨_, haa'.reach₀ [], .inr ⟨a'.pc, b, rfl, hb⟩⟩
  · obtain ⟨s', hs', hr'⟩ := hr.reach
    exact ⟨s', (haa'.reach₀ []).trans hs', .inl hr'⟩

/-- **Restarts everywhere.** If all calls made from reachable abstract configurations terminate
and from every reachable abstract configuration a (possible) `restart` is reachable, then from
every configuration reachable during the call a `restart` is reachable. -/
theorem canRestart_of {p : P} {a₀ : Loc R}
    (hterm : ∀ a, prog.AReach p a₀ a → ∀ q tT tF,
      prog.instr p a.pc = some (.call q tT tF) → prog.Terminates q a.C a.OF)
    (h : ∀ a, prog.AReach p a₀ a → ∃ a', prog.AReach p a a' ∧ prog.ARst p a') :
    ∀ s, prog.Reach₀ (atLoc p a₀) s → prog.CanRestart s := by
  refine agef (G := prog.AtRestart) (fun s hs => hs) hterm ?_
  intro a ha
  obtain ⟨a', haa', hr⟩ := h a ha
  obtain ⟨s', hs', hr'⟩ := hr.reach
  exact ⟨s', (haa'.reach₀ []).trans hs', hr'⟩

/-- Inversion of abstract steps according to the current instruction. -/
theorem astep_iff {p : P} {pc : ℕ} {C : R → ℕ} {OF : Bool} {a' : Loc R} :
    prog.AStep p ⟨pc, C, OF⟩ a' ↔
      match prog.instr p pc with
      | some (.move x y) => 0 < C x ∧ a' = ⟨pc + 1, mv C x y, OF⟩
      | some (.swap x y) => a' = ⟨pc + 1, swp C x y, OF⟩
      | some (.setOF b) => a' = ⟨pc + 1, C, b⟩
      | some (.detect x tT tF) => (0 < C x ∧ a' = ⟨tT, C, OF⟩) ∨ a' = ⟨tF, C, OF⟩
      | some (.goto t) => a' = ⟨t, C, OF⟩
      | some (.call q tT tF) =>
          ∃ C' OF' b, prog.Returns q C OF C' OF' b ∧ a' = ⟨cond b tT tF, C', OF'⟩
      | _ => False := by
  constructor
  · intro h
    cases h with
    | move h hx => rw [h]; exact ⟨hx, rfl⟩
    | swap h => rw [h]
    | setOF h => rw [h]
    | detectT h hx => rw [h]; exact .inl ⟨hx, rfl⟩
    | detectF h => rw [h]; exact .inr rfl
    | goto h => rw [h]
    | call h hr => rw [h]; exact ⟨_, _, _, hr, rfl⟩
  · intro h
    split at h
    · next h' => obtain ⟨hx, rfl⟩ := h; exact .move h' hx
    · next h' => subst h; exact .swap h'
    · next h' => subst h; exact .setOF h'
    · next h' => rcases h with ⟨hx, rfl⟩ | rfl; exacts [.detectT h' hx, .detectF h']
    · next h' => subst h; exact .goto h'
    · next h' => obtain ⟨C', OF', b, hr, rfl⟩ := h; exact .call h' hr
    · exact h.elim

/-- Invariants of abstract reachability. -/
theorem AReach.inv {p : P} {I : Loc R → Prop} (hI : ∀ a a', I a → prog.AStep p a a' → I a')
    {a a' : Loc R} (h : prog.AReach p a a') (ha : I a) : I a' := by
  induction h with
  | refl => exact ha
  | tail _ h ih => exact hI _ _ ih h


/-- A terminating call returns or restarts. -/
theorem Terminates.returns_or_restarts {p : P} {C : R → ℕ} {OF : Bool}
    (h : prog.Terminates p C OF) :
    (∃ C' OF' b, prog.Returns p C OF C' OF' b) ∨ prog.Restarts p C OF := by
  obtain ⟨s', hs', hd⟩ := h _ .refl
  rcases hd with hr | ⟨pc, b, h1, h2⟩
  · exact .inr ⟨s', hs', hr⟩
  · refine .inl ⟨s'.C, s'.OF, b, pc, ?_, h2⟩
    rw [← h1]; exact hs'

/-- **Ranking argument.** If every abstract configuration reachable from `a₀` is a target, or has a
step to an abstract configuration of smaller rank, then a target is reachable from every reachable
abstract configuration. -/
theorem exists_target_of_rank {p : P} {a₀ : Loc R} {T : Loc R → Prop} (rk : Loc R → ℕ)
    (h : ∀ a, prog.AReach p a₀ a → T a ∨ ∃ a', prog.AStep p a a' ∧ rk a' < rk a) :
    ∀ a, prog.AReach p a₀ a → ∃ a', prog.AReach p a a' ∧ T a' := by
  intro a ha
  induction hr : rk a using Nat.strong_induction_on generalizing a with
  | _ r ih =>
    rcases h a ha with hT | ⟨a', hs, hlt⟩
    · exact ⟨a, .refl, hT⟩
    · obtain ⟨b, hb, hT⟩ := ih (rk a') (hr ▸ hlt) a' (ha.tail hs) rfl
      exact ⟨b, .head hs hb, hT⟩


variable (prog) in
/-- An instruction at `pc` that never changes registers or `OF` and only jumps forward, below `L`. -/
def FwdOK (L pc : ℕ) : Instr R P → Prop
  | .detect _ tT tF => pc < tT ∧ pc < tF ∧ tT < L ∧ tF < L
  | .call _ tT tF => pc < tT ∧ pc < tF ∧ tT < L ∧ tF < L
  | .goto t => pc < t ∧ t < L
  | .ret _ => True
  | .restart => True
  | _ => False

/-- **Straight-line procedures preserve what their callees preserve.** If the code of `p` only
detects, calls, jumps forward, returns and restarts, and every callee preserves a property `Pr` of
the registers (terminating, keeping `OF`), then so does `p`. -/
theorem forward_preserve {p : P} (Pr : (R → ℕ) → Prop) (hL : 0 < (prog.code p).length)
    (hcode : ∀ pc ins, prog.instr p pc = some ins → FwdOK (prog.code p).length pc ins)
    (hcall : ∀ pc q tT tF, prog.instr p pc = some (.call q tT tF) → ∀ C OF, Pr C →
      prog.Terminates q C OF ∧ ∀ C' OF' b, prog.Returns q C OF C' OF' b → OF' = OF ∧ Pr C')
    {C : R → ℕ} {OF : Bool} (hC : Pr C) :
    prog.Terminates p C OF ∧ ∀ C' OF' b, prog.Returns p C OF C' OF' b → OF' = OF ∧ Pr C' := by
  set L := (prog.code p).length
  let I : Loc R → Prop := fun a => Pr a.C ∧ a.OF = OF ∧ a.pc < L
  have hI : ∀ a a', I a → prog.AStep p a a' → I a' := by
    rintro ⟨pc, D, OF₁⟩ a' ⟨hP, rfl, hpc⟩ hs
    rw [astep_iff] at hs
    rcases h : prog.instr p pc with _ | ins
    · rw [h] at hs; exact hs.elim
    have hok := hcode pc ins h
    rw [h] at hs
    cases ins with
    | detect x tT tF =>
      obtain ⟨-, -, h1, h2⟩ := hok
      rcases hs with ⟨-, rfl⟩ | rfl
      exacts [⟨hP, rfl, h1⟩, ⟨hP, rfl, h2⟩]
    | call q tT tF =>
      obtain ⟨-, -, h1, h2⟩ := hok
      obtain ⟨C', OF', b, hr, rfl⟩ := hs
      obtain ⟨hOF, hP'⟩ := (hcall pc q tT tF h D OF₁ hP).2 _ _ _ hr
      refine ⟨hP', hOF, ?_⟩
      cases b <;> simpa
    | goto t => subst hs; exact ⟨hP, rfl, hok.2⟩
    | move => exact hok.elim
    | swap => exact hok.elim
    | setOF => exact hok.elim
    | ret => exact hs.elim
    | restart => exact hs.elim
  have hreach : ∀ a, prog.AReach p ⟨0, C, OF⟩ a → I a :=
    fun a ha => AReach.inv hI ha ⟨hC, rfl, hL⟩
  refine ⟨terminates_of (fun a ha q tT tF hq => (hcall _ q tT tF hq a.C a.OF (hreach a ha).1).1)
    (fun a ha => ?_), fun C' OF' b h => ?_⟩
  · refine exists_target_of_rank (T := prog.ADone p) (fun a => L - a.pc) (fun a ha => ?_) a ha
    obtain ⟨hP, hOF, hpc⟩ := hreach a ha
    obtain ⟨pc, D, OF₁⟩ := a
    simp only at hP hOF hpc ⊢
    rcases h : prog.instr p pc with _ | ins
    · exact absurd h (by rw [Program.instr]; simp; omega)
    have hok := hcode pc ins h
    cases ins with
    | detect x tT tF =>
      obtain ⟨-, h2, -, -⟩ := hok
      exact .inr ⟨_, .detectF h, by simp; omega⟩
    | call q tT tF =>
      obtain ⟨h1, h2, -, -⟩ := hok
      rcases (hcall pc q tT tF h D OF₁ hP).1.returns_or_restarts with ⟨C', OF', b, hr⟩ | hr
      · exact .inr ⟨_, .call h hr, by cases b <;> simp <;> omega⟩
      · exact .inl (.inr (.inr ⟨q, tT, tF, h, hr⟩))
    | goto t =>
      obtain ⟨h1, -⟩ := hok
      exact .inr ⟨_, .goto h, by simp; omega⟩
    | ret b => exact .inl (.inl ⟨b, h⟩)
    | restart => exact .inl (.inr (.inl h))
    | move => exact hok.elim
    | swap => exact hok.elim
    | setOF => exact hok.elim
  · obtain ⟨a, ha, rfl, rfl, -⟩ := returns_iff.1 h
    obtain ⟨hP, hOF, -⟩ := hreach a ha
    exact ⟨hOF, hP⟩


/-- A return value occurs in a `return` instruction of the code. -/
theorem Returns.mem_code {p : P} {C C' : R → ℕ} {OF OF' : Bool} {b : Bool}
    (h : prog.Returns p C OF C' OF' b) : Instr.ret b ∈ prog.code p := by
  obtain ⟨pc, -, hb⟩ := h
  exact List.mem_of_getElem? hb

end Program

end Podc.PPDoubleExpThresholds
