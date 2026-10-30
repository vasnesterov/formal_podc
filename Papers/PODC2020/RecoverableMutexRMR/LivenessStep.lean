import Papers.PODC2020.RecoverableMutexRMR.InvDefs
import Papers.PODC2020.RecoverableMutexRMR.Spec

/-!
# Liveness, part 1: effects of a single step

State-level facts about `Cfg.step` used in the liveness proof (`Liveness.lean`): which shared
variables a step of `r` may change, and how.
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

namespace Live

lemma step_pc_ne (s : Cfg P) {r q : P} (h : q ≠ r) : (s.step r).pc q = s.pc q := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp [Cfg.setPc, Function.update_of_ne h]

lemma step_C (s : Cfg P) (r : P) :
    (s.step r).C = s.C ∨ (s.pc r = .l4 ∧ (s.step r).C = s.C + 1) := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]

lemma step_D (s : Cfg P) (r : P) :
    (s.step r).D = s.D ∨ ((s.pc r = .r15 ∨ ∃ w, s.pc r = .w28 w) ∧ (s.step r).D = s.D + 1) := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]

lemma step_T (s : Cfg P) (r : P) :
    (s.step r).T = s.T ∨ ((s.step r).T = s.T + 1 ∧ ∃ ρ, (s.step r).pc r = .m34 ρ) := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]

lemma step_A (s : Cfg P) (r : P) (x : ℕ) :
    (s.step r).A x = s.A x ∨ (s.A x = .empty ∧
      ((s.pc r = .w24 x ∧ (s.step r).A x = .claimed r) ∨
       ((∃ ρ ℓ, s.pc r = .m46 ρ ℓ ∧ x = ℓ + 1) ∧ (s.step r).A x = .skipped))) := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]
  all_goals (simp only [Function.update_apply]; split_ifs <;> simp_all)

lemma step_W (s : Cfg P) (r q : P) :
    (s.step r).W q = s.W q ∨
      (r = q ∧ ((∃ c, s.pc q = .l5 c) ∨ s.pc q = .w26 ∨ s.pc q = .x10)) ∨
      (∃ ρ ℓ, s.pc r = .m40 ρ ℓ q ∧ s.W q = (ℓ + 1, false) ∧ (s.step r).W q = (ℓ + 1, true)) := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]
  all_goals (simp only [Function.update_apply]; split_ifs <;> simp_all)

lemma step_X (s : Cfg P) (r q : P) : (s.step r).X q = s.X q ∨ r = q := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]
  all_goals (simp only [Function.update_apply]; split_ifs <;> simp_all)

lemma ghost_cur_step (g : Ghost P) (s : Cfg P) (r q : P) :
    (g.next s (.step r)).cur q = g.cur q ∨
      (r = q ∧ s.pc q = .l4 ∧ (g.next s (.step r)).cur q = s.C + 1) := by
  simp only [Ghost.next]
  split <;> simp_all [Function.update_apply]
  all_goals (rcases eq_or_ne q r with rfl | h <;> simp_all)

/-! ### Classes of program counters -/

/-- Program counters from which a process reaches `rem` or `w31` only through a call of
`Move_Token()` (a step into line 34). -/
def Pre : PC P → Prop
  | .l3 | .l4 | .l5 _ | .w23 | .w24 _ | .w25 _ | .w26 | .w28 _ | .cs | .x9 | .x10
  | .r15 | .r16 | .r18 => True
  | _ => False

/-- Program counters inside a `Move_Token()` call or right after it (`w31`, `x12`). -/
def MW : PC P → Prop
  | .m34 _ | .m35 _ _ | .m36 _ _ _ | .m38 _ _ _ _ | .m40 _ _ _ | .m41 _ _ _ | .m42 _ _
  | .m46 _ _ | .m47 _ _ | .m48 _ _ | .w31 _ | .x12 => True
  | _ => False

/-- `k` is line 34 (the start of a `Move_Token()` call). -/
def IsM34 (k : PC P) : Prop := ∃ ρ, k = .m34 ρ

/-- Base rank: decreases along every forward edge of the program outside `Enter()`'s doorway. -/
def rk0 : PC P → ℕ
  | .rem => 0
  | .w31 _ => 1
  | .x12 => 1
  | .m42 _ _ => 2
  | .m48 _ _ => 2
  | .m41 _ _ _ => 3
  | .m47 _ _ => 3
  | .m40 _ _ _ => 4
  | .m46 _ _ => 4
  | .m38 _ _ _ _ => 5
  | .m36 _ _ _ => 6
  | .m35 _ _ => 7
  | .m34 _ => 8
  | .w28 _ => 9
  | .x10 => 9
  | .x9 => 10
  | .cs => 11
  | .r18 => 30
  | .r16 => 31
  | .r15 => 32
  | _ => 0

/-- Weight of a return address in the call potential. -/
def retW : Ret → ℕ
  | .wr _ => 0
  | .ex => 1

/-- Call potential: `2` before line 10 of `Exit()` (or in `Recover()` before line 18), `0` after
the call of `Move_Token()` of line 29, `1` otherwise. -/
def cp : PC P → ℕ
  | .cs | .x9 | .x10 | .r15 | .r16 => 2
  | .w31 _ => 0
  | .m34 ρ | .m35 ρ _ | .m36 ρ _ _ | .m38 ρ _ _ _ | .m40 ρ _ _ | .m41 ρ _ _ | .m42 ρ _
  | .m46 ρ _ | .m47 ρ _ | .m48 ρ _ => retW ρ
  | _ => 1

@[simp] lemma cp_retpc (ρ : Ret) : cp (ρ.pc : PC P) = retW ρ := by cases ρ <;> rfl
@[simp] lemma rk0_retpc (ρ : Ret) : rk0 (ρ.pc : PC P) = 1 := by cases ρ <;> rfl
@[simp] lemma Pre_retpc (ρ : Ret) : ¬ Pre (ρ.pc : PC P) := by cases ρ <;> simp [Ret.pc, Pre]
@[simp] lemma MW_retpc (ρ : Ret) : MW (ρ.pc : PC P) := by cases ρ <;> simp [Ret.pc, MW]
@[simp] lemma retpc_ne_cs (ρ : Ret) : (ρ.pc : PC P) ≠ .cs := by cases ρ <;> simp [Ret.pc]
@[simp] lemma retpc_ne_m34 (ρ ρ' : Ret) : (ρ.pc : PC P) ≠ .m34 ρ' := by cases ρ <;> simp [Ret.pc]
@[simp] lemma OnTrack_retpc (s : Cfg P) (q : P) (ρ : Ret) (h : s.pc q = ρ.pc) :
    ¬ OnTrack s q := by
  cases ρ <;> simp_all [Ret.pc, OnTrack]

/-- `q` is in the critical section, about to execute line 9 or 10, or `OnTrack`. -/
def OT (s : Cfg P) (q : P) : Prop :=
  s.pc q = .cs ∨ s.pc q = .x9 ∨ s.pc q = .x10 ∨ OnTrack s q

lemma pre_step (s : Cfg P) (r : P) (h : s.pc r = .rem ∨ Pre (s.pc r)) :
    Pre ((s.step r).pc r) ∨ IsM34 ((s.step r).pc r) := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc, Pre, IsM34]

lemma mw_entry (s : Cfg P) (r : P) (h : ¬ MW (s.pc r)) (h' : MW ((s.step r).pc r)) :
    IsM34 ((s.step r).pc r) := by
  revert h h'
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc, MW, IsM34]

lemma spin (s : Cfg P) (r : P) (h : (s.step r).pc r = s.pc r) :
    ∃ w, s.pc r = .w31 w ∧ s.W r ≠ (w, true) := by
  revert h
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]
  all_goals (try split) <;> (cases ‹Ret› <;> simp [Ret.pc])

/-- The control-flow graph of the algorithm (ignoring data). -/
inductive Succ : PC P → PC P → Prop
  | rem : Succ .rem .l3
  | l3a : Succ .l3 .l4
  | l3b : Succ .l3 .w23
  | l4 (c : ℕ) : Succ .l4 (.l5 c)
  | l5 (c : ℕ) : Succ (.l5 c) .w23
  | w23 (w : ℕ) : Succ .w23 (.w24 w)
  | w24 (w : ℕ) : Succ (.w24 w) (.w25 w)
  | w25a (w : ℕ) : Succ (.w25 w) (.w28 w)
  | w25b (w : ℕ) : Succ (.w25 w) .w26
  | w26 : Succ .w26 .l3
  | w28 (w : ℕ) : Succ (.w28 w) (.m34 (.wr w))
  | w31a (w : ℕ) : Succ (.w31 w) .cs
  | w31b (w : ℕ) : Succ (.w31 w) (.w31 w)
  | cs : Succ .cs .x9
  | x9 : Succ .x9 .x10
  | x10 : Succ .x10 (.m34 .ex)
  | x12 : Succ .x12 .rem
  | r15 : Succ .r15 .r16
  | r16a : Succ .r16 .x9
  | r16b : Succ .r16 .r18
  | r18a : Succ .r18 .cs
  | r18b : Succ .r18 .l3
  | m34 (ρ : Ret) (ℓ : ℕ) : Succ (.m34 ρ) (.m35 ρ ℓ)
  | m35 (ρ : Ret) (ℓ d : ℕ) : Succ (.m35 ρ ℓ) (.m36 ρ ℓ d)
  | m36a (ρ : Ret) (ℓ c d : ℕ) : Succ (.m36 ρ ℓ d) (.m38 ρ ℓ c d)
  | m36b (ρ : Ret) (ℓ d : ℕ) : Succ (.m36 ρ ℓ d) ρ.pc
  | m38a (ρ : Ret) (ℓ c d : ℕ) (q : P) : Succ (.m38 ρ ℓ c d) (.m40 ρ ℓ q)
  | m38b (ρ : Ret) (ℓ c d : ℕ) : Succ (.m38 ρ ℓ c d) (.m46 ρ ℓ)
  | m38c (ρ : Ret) (ℓ c d : ℕ) : Succ (.m38 ρ ℓ c d) ρ.pc
  | m40 (ρ : Ret) (ℓ : ℕ) (q : P) : Succ (.m40 ρ ℓ q) (.m41 ρ ℓ q)
  | m41a (ρ : Ret) (ℓ : ℕ) (q : P) : Succ (.m41 ρ ℓ q) (.m42 ρ ℓ)
  | m41b (ρ : Ret) (ℓ : ℕ) (q : P) : Succ (.m41 ρ ℓ q) ρ.pc
  | m42a (ρ : Ret) (ℓ : ℕ) : Succ (.m42 ρ ℓ) (.m34 ρ)
  | m42b (ρ : Ret) (ℓ : ℕ) : Succ (.m42 ρ ℓ) ρ.pc
  | m46 (ρ : Ret) (ℓ : ℕ) : Succ (.m46 ρ ℓ) (.m47 ρ ℓ)
  | m47a (ρ : Ret) (ℓ : ℕ) : Succ (.m47 ρ ℓ) (.m48 ρ ℓ)
  | m47b (ρ : Ret) (ℓ : ℕ) : Succ (.m47 ρ ℓ) ρ.pc
  | m48a (ρ : Ret) (ℓ : ℕ) : Succ (.m48 ρ ℓ) (.m34 ρ)
  | m48b (ρ : Ret) (ℓ : ℕ) : Succ (.m48 ρ ℓ) ρ.pc

lemma succ_step (s : Cfg P) (r : P) : Succ (s.pc r) ((s.step r).pc r) := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp_all [Cfg.setPc]
  all_goals first
    | constructor
    | (split <;> constructor)

/-- A "back edge": a successful `Token.CAS` (lines 42, 48) followed by the recursive call. -/
def Back (k k' : PC P) : Prop := IsM34 k' ∧ ∃ ρ ℓ, k = .m42 ρ ℓ ∨ k = .m48 ρ ℓ

lemma step_T_of_back (s : Cfg P) (r : P) (h : Back (s.pc r) ((s.step r).pc r)) :
    (s.step r).T = s.T + 1 := by
  obtain ⟨⟨ρ', h1⟩, ρ, ℓ, h2 | h2⟩ := h <;> revert h1 <;>
    simp only [Cfg.step, h2] <;> split_ifs <;> simp_all [Cfg.setPc]

/-- The call potential does not increase along steps that neither enter the critical section
nor move `Token`, and it decreases at every call of `Move_Token()`. -/
lemma cp_succ {k k' : PC P} (h : Succ k k') (hcs : k' ≠ .cs) (hb : ¬ Back k k') :
    cp k' ≤ cp k ∧ (IsM34 k' → cp k' < cp k) := by
  cases h <;> (try cases ‹Ret›) <;> simp_all [cp, retW, Ret.pc, IsM34, Back]

/-- `OT` at the level of program counters. -/
def OTpc (T : ℕ) (q : P) : PC P → Prop
  | .cs | .x9 | .x10 | .r15 | .r16 | .m34 .ex => True
  | .m35 .ex ℓ | .m36 .ex ℓ _ | .m38 .ex ℓ _ _ | .m42 .ex ℓ => ℓ = T
  | .m40 .ex ℓ q' | .m41 .ex ℓ q' => ℓ = T ∧ q' = q
  | _ => False

lemma OT_iff (s : Cfg P) (q : P) : OT s q ↔ OTpc s.T q (s.pc q) := by
  unfold OT OnTrack
  cases s.pc q <;> (try cases ‹Ret›) <;> simp [OTpc]

/-- Along `OT` states, the base rank strictly decreases (except at back edges). -/
lemma rk0_succ {T : ℕ} {q : P} {k k' : PC P} (h : Succ k k') (h1 : OTpc T q k)
    (h2 : OTpc T q k') (hb : ¬ Back k k') : rk0 k' < rk0 k := by
  cases h <;> (try cases ‹Ret›) <;> simp_all [rk0, OTpc, Ret.pc, IsM34, Back]

end Live

end Podc.RecoverableMutexRMR
