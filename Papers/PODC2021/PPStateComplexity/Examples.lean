import Papers.PODC2021.PPStateComplexity.Model
import Mathlib.Algebra.BigOperators.Fin

/-!
# Example protocols (Section 2.2 of Czerner–Esparza–Leroux)

* `majority4 ℓ`: a **4-state protocol with `ℓ` leaders deciding `x ≥ ℓ`**, for every `ℓ`
  (`majority4_computesGe`). Hence, with unboundedly many leaders, a fixed number of states
  decides `x ≥ η` for every `η` (`exists_protocol_computesGe`): the busy-beaver function
  `BB_L(n)` for protocols with leaders is infinite as soon as `n ≥ 4` unless the number of
  leaders is bounded.
* `exampleP' k`: the leaderless protocol `P'_k` of **Example 2.1**, with states
  `{0, 2^0, …, 2^k}`, computing `x ≥ 2^k` (`exampleP'_computesGe`, `exampleP'_leaderless`).

The proofs go through the reachability characterization `Protocol.computesGe_iff`.
-/

namespace Podc.PPStateComplexity

open Cslib Cslib.PopulationProtocol

/-! ### General helpers -/

section General

variable {Q : Type*} [DecidableEq Q]

theorem ex_mstep_of_le {T : Set (Transition Q)} {t : Transition Q} (ht : t ∈ T) {C : Multiset Q}
    (h : t.pre ≤ C) : MStep T C (C - t.pre + t.post) := ⟨t, ht, And.intro h rfl⟩

theorem ex_count_fire {t : Transition Q} {C : Multiset Q} (_h : t.pre ≤ C) (s : Q) :
    (C - t.pre + t.post).count s = C.count s - t.pre.count s + t.post.count s := by
  rw [Multiset.count_add, Multiset.count_sub]

/-- Two distinct present states can interact. -/
theorem ex_pre_le_of_mem {t : Transition Q} {C : Multiset Q} (hne : t.p ≠ t.q) (hp : t.p ∈ C)
    (hq : t.q ∈ C) : t.pre ≤ C := by
  rw [Multiset.le_iff_count]
  intro s
  have h1 := Multiset.count_pos.2 hp
  have h2 := Multiset.count_pos.2 hq
  simp only [Transition.pre, Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  by_cases e1 : s = t.p
  · subst e1; simp [hne]; omega
  · by_cases e2 : s = t.q
    · subst e2; simp [e1]; omega
    · simp [e1, e2]

/-- `ex_pre_le_of_mem` for an explicit transition, with count hypotheses. -/
theorem ex_pre_le {p q p' q' : Q} {C : Multiset Q} (hne : p ≠ q) (hp : 0 < C.count p)
    (hq : 0 < C.count q) : (⟨p, q, p', q'⟩ : Transition Q).pre ≤ C :=
  ex_pre_le_of_mem hne (Multiset.count_pos.1 hp) (Multiset.count_pos.1 hq)

/-- Two agents in the same state can interact. -/
theorem ex_pre_le_of_two_le {t : Transition Q} {C : Multiset Q} (he : t.q = t.p)
    (h : 2 ≤ C.count t.p) : t.pre ≤ C := by
  rw [Multiset.le_iff_count]
  intro s
  simp only [Transition.pre, he, Multiset.insert_eq_cons, Multiset.count_cons,
    Multiset.count_singleton]
  by_cases e1 : s = t.p
  · subst e1; simp; omega
  · simp [e1]

/-- If transitions of `T` cannot leave a set `S` of states, then configurations inside `S` stay
inside `S`. -/
theorem ex_mreach_closed {T : Set (Transition Q)} (S : Q → Prop)
    (hT : ∀ t ∈ T, S t.p → S t.q → S t.p' ∧ S t.q') {C C' : Multiset Q} (hC : ∀ q ∈ C, S q)
    (h : MReach T C C') : ∀ q ∈ C', S q := by
  induction h with
  | refl => exact hC
  | tail _ hs ih =>
    obtain ⟨t, ht, hle, rfl⟩ := hs
    have hp := ih t.p (Multiset.mem_of_le hle (by simp [Transition.pre]))
    have hq := ih t.q (Multiset.mem_of_le hle (by simp [Transition.pre]))
    have h' := hT t ht hp hq
    intro q hq'
    rcases Multiset.mem_add.1 hq' with h1 | h1
    · exact ih _ (Multiset.mem_of_le (Multiset.sub_le_self _ _) h1)
    · simp only [Transition.post, Multiset.insert_eq_cons, Multiset.mem_cons,
        Multiset.mem_singleton] at h1
      rcases h1 with rfl | rfl
      · exact h'.1
      · exact h'.2

theorem ex_lt_of_count {C C' : Multiset Q} (s : Q) (hc : Multiset.card C' = Multiset.card C)
    (h : C'.count s = C.count s + 1) :
    Multiset.card C' - C'.count s < Multiset.card C - C.count s := by
  have := Multiset.count_le_card s C'
  omega

/-- Reaching a goal by a decreasing measure. -/
theorem ex_mreach_descent {T : Set (Transition Q)} (Inv Goal : Multiset Q → Prop)
    (f : Multiset Q → ℕ)
    (h : ∀ C, Inv C → ¬ Goal C → ∃ C', MStep T C C' ∧ Inv C' ∧ f C' < f C) :
    ∀ C, Inv C → ∃ C', MReach T C C' ∧ Inv C' ∧ Goal C' := by
  intro C
  induction hn : f C using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    intro hC
    by_cases hg : Goal C
    · exact ⟨C, .refl, hC, hg⟩
    · obtain ⟨C', hs, hC', hf⟩ := h C hC hg
      obtain ⟨C'', h1, h2, h3⟩ := ih _ (hn ▸ hf) C' rfl hC'
      exact ⟨C'', Relation.ReflTransGen.head hs h1, h2, h3⟩

/-- Invariants of steps hold on reachable configurations. -/
theorem ex_mreach_inv {T : Set (Transition Q)} (Inv : Multiset Q → Prop)
    (hs : ∀ C C', Inv C → MStep T C C' → Inv C') {C C' : Multiset Q} (hC : Inv C)
    (h : MReach T C C') : Inv C' := by
  induction h with
  | refl => exact hC
  | tail _ h ih => exact hs _ _ ih h

end General

/-! ### A 4-state protocol with `ℓ` leaders deciding `x ≥ ℓ` -/

/-- The states of `majority4`: `A` (leader, strong 0), `B` (input, strong 1), and the weak
states `a` (output 0) and `b` (output 1). -/
inductive St4
  | A
  | B
  | a
  | b
  deriving DecidableEq, Repr

instance : Fintype St4 :=
  ⟨{.A, .B, .a, .b}, fun x => by cases x <;> decide⟩

/-- The rules of `majority4` (both orientations): `{A,B} ↦ {a,b}`, `{A,b} ↦ {A,a}`,
`{B,a} ↦ {B,b}`, `{a,b} ↦ {b,b}`; all other pairs are idle. -/
def rule4 : St4 → St4 → St4 × St4
  | .A, .B => (.a, .b)
  | .B, .A => (.b, .a)
  | .A, .b => (.A, .a)
  | .b, .A => (.a, .A)
  | .B, .a => (.B, .b)
  | .a, .B => (.b, .B)
  | .a, .b => (.b, .b)
  | .b, .a => (.b, .b)
  | p, q => (p, q)

/-- The output map of `majority4`. -/
def out4 : St4 → Bool
  | .A => false
  | .a => false
  | .B => true
  | .b => true

/-- A 4-state population protocol with `ℓ` leaders (in state `A`) and input state `B` that
decides `x ≥ ℓ` (`majority4_computesGe`): it is the classical majority protocol comparing the
`ℓ` leaders with the `x` input agents. -/
def majority4 (ℓ : ℕ) : Protocol St4 where
  T := {t | rule4 t.p t.q = (t.p', t.q')}
  total p q := ⟨(rule4 p q).1, (rule4 p q).2, rfl⟩
  L := Multiset.replicate ℓ .A
  x := .B
  O := out4

/-- The invariant of `majority4`: `#B − #A = i − ℓ` and some agent is in `A`, `B` or `b`. -/
def Inv4 (ℓ i : ℕ) (C : Multiset St4) : Prop :=
  (C.count .B : ℤ) - C.count .A = i - ℓ ∧ 1 ≤ C.count .A + C.count .B + C.count .b

theorem inv4_step {ℓ i : ℕ} {C C' : Multiset St4} (hC : Inv4 ℓ i C)
    (h : (majority4 ℓ).Step C C') : Inv4 ℓ i C' := by
  obtain ⟨⟨p, q, p', q'⟩, ht, hf⟩ := h
  have cA := hf.count_eq .A
  have cB := hf.count_eq .B
  have cb := hf.count_eq .b
  have lA := Multiset.count_le_of_le .A hf.1
  have lB := Multiset.count_le_of_le .B hf.1
  have lb := Multiset.count_le_of_le .b hf.1
  obtain ⟨h1, h2⟩ := hC
  simp only [majority4, Set.mem_ofPred_eq] at ht
  cases p <;> cases q <;> simp only [rule4, Prod.mk.injEq] at ht <;> obtain ⟨rfl, rfl⟩ := ht <;>
    simp [Transition.delta, Transition.pre, Transition.post] at cA cB cb lA lB lb <;>
    constructor <;> omega

theorem inv4_reach {ℓ i : ℕ} (hi : 2 ≤ i) {C : Multiset St4}
    (h : (majority4 ℓ).Reach ((majority4 ℓ).IC i) C) : Inv4 ℓ i C := by
  refine ex_mreach_inv _ (fun _ _ h1 h2 => inv4_step h1 h2) ?_ h
  simp [Inv4, Protocol.IC, majority4, Multiset.count_replicate]
  omega

theorem stable4 {ℓ : ℕ} (S : St4 → Prop) (b : Bool) (hS : ∀ s, S s → out4 s = b)
    (hT : ∀ p q, S p → S q → rule4 p q = (p, q)) {C : Multiset St4} (hC : ∀ q ∈ C, S q) :
    (majority4 ℓ).Stable b C := by
  intro C' hC' q hq
  refine hS q (ex_mreach_closed S ?_ hC hC' q hq)
  rintro ⟨p, q, p', q'⟩ ht hp hq
  simp only [majority4, Set.mem_ofPred_eq, hT p q hp hq, Prod.mk.injEq] at ht
  obtain ⟨rfl, rfl⟩ := ht
  exact ⟨hp, hq⟩

theorem mem4 {ℓ : ℕ} {p q p' q' : St4} (h : rule4 p q = (p', q') := by rfl) :
    (⟨p, q, p', q'⟩ : Transition St4) ∈ (majority4 ℓ).T := h

/-- The 4-state protocol `majority4 ℓ` (with `ℓ` leaders) computes `x ≥ ℓ`. -/
theorem majority4_computesGe (ℓ : ℕ) : (majority4 ℓ).ComputesGe ℓ := by
  rw [Protocol.computesGe_iff]
  intro i hi C hC
  have hInv := inv4_reach hi hC
  by_cases hℓ : ℓ ≤ i
  · rw [decide_eq_true hℓ]
    -- Phase 1: cancel all leaders.
    obtain ⟨C₁, h₁, hI₁, hA₁⟩ := ex_mreach_descent (T := (majority4 ℓ).T) (Inv4 ℓ i)
      (fun C => C.count .A = 0) (fun C => C.count .A) (fun C hC hg => by
        have hle : (⟨.A, .B, .a, .b⟩ : Transition St4).pre ≤ C :=
          ex_pre_le (by decide) (by omega)
            (by have := hC.1; omega)
        refine ⟨_, ex_mstep_of_le mem4 hle, inv4_step hC (ex_mstep_of_le (mem4 (ℓ := ℓ)) hle), ?_⟩
        rw [ex_count_fire hle]
        simp [Transition.pre, Transition.post, -Multiset.count_eq_zero]
        omega) C hInv
    -- Phase 2: turn all `a` into `b`.
    obtain ⟨C₂, h₂, ⟨hI₂, hA₂⟩, ha₂⟩ := ex_mreach_descent (T := (majority4 ℓ).T)
      (fun C => Inv4 ℓ i C ∧ C.count .A = 0)
      (fun C => C.count .a = 0) (fun C => C.count .a) (fun C hC hg => by
        obtain ⟨hC, hA⟩ := hC
        by_cases hB : 0 < C.count .B
        · have hle : (⟨.B, .a, .B, .b⟩ : Transition St4).pre ≤ C :=
            ex_pre_le (by decide) hB
              (by omega)
          refine ⟨_, ex_mstep_of_le mem4 hle,
            ⟨inv4_step hC (ex_mstep_of_le (mem4 (ℓ := ℓ)) hle), ?_⟩, ?_⟩ <;>
          · rw [ex_count_fire hle]
            simp [Transition.pre, Transition.post, -Multiset.count_eq_zero]
            omega
        · have hle : (⟨.a, .b, .b, .b⟩ : Transition St4).pre ≤ C :=
            ex_pre_le (by decide) (by omega)
              (by have := hC.2; omega)
          refine ⟨_, ex_mstep_of_le mem4 hle,
            ⟨inv4_step hC (ex_mstep_of_le (mem4 (ℓ := ℓ)) hle), ?_⟩, ?_⟩ <;>
          · rw [ex_count_fire hle]
            simp [Transition.pre, Transition.post, -Multiset.count_eq_zero]
            omega) C₁ ⟨hI₁, hA₁⟩
    refine ⟨C₂, h₁.trans h₂, stable4 (fun s => s = .B ∨ s = .b) true ?_ ?_ ?_⟩
    · rintro s (rfl | rfl) <;> rfl
    · rintro p q (rfl | rfl) (rfl | rfl) <;> rfl
    · intro s hs
      cases s
      · exact absurd (Multiset.count_pos.2 hs) (by omega)
      · simp
      · exact absurd (Multiset.count_pos.2 hs) (by omega)
      · simp
  · rw [decide_eq_false hℓ]
    -- Phase 1: cancel all inputs.
    obtain ⟨C₁, h₁, hI₁, hB₁⟩ := ex_mreach_descent (T := (majority4 ℓ).T) (Inv4 ℓ i)
      (fun C => C.count .B = 0) (fun C => C.count .B) (fun C hC hg => by
        have hle : (⟨.A, .B, .a, .b⟩ : Transition St4).pre ≤ C :=
          ex_pre_le (by decide) (by have := hC.1; omega)
            (by omega)
        refine ⟨_, ex_mstep_of_le mem4 hle, inv4_step hC (ex_mstep_of_le (mem4 (ℓ := ℓ)) hle), ?_⟩
        rw [ex_count_fire hle]
        simp [Transition.pre, Transition.post, -Multiset.count_eq_zero]
        omega) C hInv
    -- Phase 2: turn all `b` into `a`.
    obtain ⟨C₂, h₂, ⟨hI₂, hB₂⟩, hb₂⟩ := ex_mreach_descent (T := (majority4 ℓ).T)
      (fun C => Inv4 ℓ i C ∧ C.count .B = 0)
      (fun C => C.count .b = 0) (fun C => C.count .b) (fun C hC hg => by
        obtain ⟨hC, hB⟩ := hC
        have hle : (⟨.A, .b, .A, .a⟩ : Transition St4).pre ≤ C :=
          ex_pre_le (by decide) (by have := hC.1; omega)
            (by omega)
        refine ⟨_, ex_mstep_of_le mem4 hle,
          ⟨inv4_step hC (ex_mstep_of_le (mem4 (ℓ := ℓ)) hle), ?_⟩, ?_⟩ <;>
        · rw [ex_count_fire hle]
          simp [Transition.pre, Transition.post, -Multiset.count_eq_zero]
          omega) C₁ ⟨hI₁, hB₁⟩
    refine ⟨C₂, h₁.trans h₂, stable4 (fun s => s = .A ∨ s = .a) false ?_ ?_ ?_⟩
    · rintro s (rfl | rfl) <;> rfl
    · rintro p q (rfl | rfl) (rfl | rfl) <;> rfl
    · intro s hs
      cases s
      · simp
      · exact absurd (Multiset.count_pos.2 hs) (by omega)
      · simp
      · exact absurd (Multiset.count_pos.2 hs) (by omega)

/-- For every threshold `η` there is a **4-state** protocol (with `η` leaders) computing
`x ≥ η`. Hence the number of states needed to decide `x ≥ η` with leaders cannot grow with `η`
unless the number of leaders is bounded. -/
theorem exists_protocol_computesGe (η : ℕ) : ∃ P : Protocol St4, P.ComputesGe η :=
  ⟨majority4 η, majority4_computesGe η⟩

/-! ### Example 2.1: the leaderless protocol `P'_k` -/

/-- The state `2^k` of `P'_k` (states are `Option (Fin (k+1))`: `none` is `0`, `some j` is
`2^j`). -/
def topP' (k : ℕ) : Option (Fin (k + 1)) := some (Fin.last k)

/-- The value of a state of `P'_k`: `0` for `none`, `2^j` for `some j`. -/
def valP' {k : ℕ} : Option (Fin (k + 1)) → ℕ
  | none => 0
  | some j => 2 ^ (j : ℕ)

/-- The rules of `P'_k`: `{2^i, 2^i} ↦ {0, 2^(i+1)}` for `i < k`, `{q, 2^k} ↦ {2^k, 2^k}` for
all `q` (both orientations), all other pairs idle. -/
def ruleP' (k : ℕ) : Option (Fin (k + 1)) → Option (Fin (k + 1)) →
    Option (Fin (k + 1)) × Option (Fin (k + 1))
  | some j, some j' =>
    if h : j = Fin.last k ∨ j' = Fin.last k then (topP' k, topP' k)
    else if j = j' then
      (none, some ⟨j + 1, by have := Fin.val_lt_last (fun e => h (Or.inl e)); omega⟩)
    else (some j, some j')
  | none, some j' => if j' = Fin.last k then (topP' k, topP' k) else (none, some j')
  | some j, none => if j = Fin.last k then (topP' k, topP' k) else (some j, none)
  | none, none => (none, none)

/-- **Example 2.1.** The leaderless protocol `P'_k` with states `{0, 2^0, …, 2^k}`, input state
`2^0` and output `1` exactly in `2^k`. It computes `x ≥ 2^k` (`exampleP'_computesGe`). -/
def exampleP' (k : ℕ) : Protocol (Option (Fin (k + 1))) where
  T := {t | ruleP' k t.p t.q = (t.p', t.q')}
  total p q := ⟨(ruleP' k p q).1, (ruleP' k p q).2, rfl⟩
  L := 0
  x := some 0
  O q := decide (q = topP' k)

/-- `P'_k` is leaderless. -/
theorem exampleP'_leaderless (k : ℕ) : (exampleP' k).Leaderless := rfl

theorem ruleP'_top_right (k : ℕ) (q : Option (Fin (k + 1))) :
    ruleP' k q (topP' k) = (topP' k, topP' k) := by
  cases q <;> simp [ruleP', topP']

theorem ruleP'_top_left (k : ℕ) (q : Option (Fin (k + 1))) :
    ruleP' k (topP' k) q = (topP' k, topP' k) := by
  rcases q with _ | q <;> simp [ruleP', topP']

/-- Transitions of `P'_k` not involving `2^k` preserve the sum of values. -/
theorem ruleP'_sum {k : ℕ} {p q : Option (Fin (k + 1))} (hp : p ≠ topP' k) (hq : q ≠ topP' k) :
    valP' (ruleP' k p q).1 + valP' (ruleP' k p q).2 = valP' p + valP' q := by
  rcases p with _ | j <;> rcases q with _ | j'
  · rfl
  · have : j' ≠ Fin.last k := fun e => hq (by rw [e]; rfl)
    simp [ruleP', this]
  · have : j ≠ Fin.last k := fun e => hp (by rw [e]; rfl)
    simp [ruleP', this]
  · have h1 : j ≠ Fin.last k := fun e => hp (by rw [e]; rfl)
    have h2 : j' ≠ Fin.last k := fun e => hq (by rw [e]; rfl)
    by_cases e : j = j'
    · subst e
      simp [ruleP', h1, valP', pow_succ]
      ring
    · simp [ruleP', h1, h2, e]

/-- The sum of values of a configuration. -/
def sumP' {k : ℕ} (C : Multiset (Option (Fin (k + 1)))) : ℕ := (C.map valP').sum

theorem exampleP'_step {k : ℕ} {C C' : Multiset (Option (Fin (k + 1)))}
    (h : (exampleP' k).Step C C') :
    (topP' k ∈ C → topP' k ∈ C') ∧ (topP' k ∉ C → sumP' C' = sumP' C) := by
  obtain ⟨⟨p, q, p', q'⟩, ht, hf⟩ := h
  simp only [exampleP', Set.mem_ofPred_eq] at ht
  have hpC : p ∈ C := Multiset.mem_of_le hf.1 (by simp [Transition.pre])
  have hqC : q ∈ C := Multiset.mem_of_le hf.1 (by simp [Transition.pre])
  by_cases htop : p = topP' k ∨ q = topP' k
  · have hp' : p' = topP' k := by
      rcases htop with rfl | rfl
      · rw [ruleP'_top_left] at ht; exact (Prod.mk.inj ht).1.symm
      · rw [ruleP'_top_right] at ht; exact (Prod.mk.inj ht).1.symm
    refine ⟨fun _ => ?_, fun h => ?_⟩
    · rw [hf.2]; exact Multiset.mem_add.2 (Or.inr (by simp [Transition.post, hp']))
    · rcases htop with rfl | rfl
      · exact absurd hpC h
      · exact absurd hqC h
  · push Not at htop
    refine ⟨fun h => ?_, fun _ => ?_⟩
    · rw [hf.2]
      refine Multiset.mem_add.2 (Or.inl (Multiset.count_pos.1 ?_))
      rw [Multiset.count_sub]
      have : (⟨p, q, p', q'⟩ : Transition _).pre.count (topP' k) = 0 := by
        simp [Transition.pre, htop.1.symm, htop.2.symm]
      rw [this]
      simpa using Multiset.count_pos.2 h
    · have hs := hf.sum_map valP'
      have := ruleP'_sum htop.1 htop.2
      rw [ht] at this
      simp only at this
      simp [Transition.pre, Transition.post] at hs
      unfold sumP'
      omega

theorem sum_two_pow_lt (k : ℕ) : ∑ j ∈ Finset.range k, 2 ^ j < 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

/-- If no state below `2^k` occurs twice and `2^k` does not occur, the sum is `< 2^k`. -/
theorem sumP'_lt {k : ℕ} {C : Multiset (Option (Fin (k + 1)))} (htop : topP' k ∉ C)
    (h : ∀ j : Fin (k + 1), j ≠ Fin.last k → C.count (some j) ≤ 1) : sumP' C < 2 ^ k := by
  have e : sumP' C = ∑ q, C.count q * valP' q := by
    unfold sumP'
    rw [Finset.sum_multiset_map_count]
    refine (Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => by
      simp [Multiset.count_eq_zero.2 (by simpa using hq)])).trans ?_
    simp
  rw [e, Fintype.sum_option, Fin.sum_univ_castSucc]
  have hl : C.count (some (Fin.last k)) = 0 := Multiset.count_eq_zero.2 htop
  simp only [valP', mul_zero, zero_add, hl, zero_mul, add_zero]
  refine lt_of_le_of_lt ?_ (sum_two_pow_lt k)
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_le_sum fun j _ => ?_
  have := h j.castSucc (Fin.castSucc_ne_last j)
  simp only [Fin.val_castSucc]
  nlinarith [Nat.one_le_two_pow (n := (j : ℕ))]

theorem le_sumP' {k : ℕ} {C : Multiset (Option (Fin (k + 1)))} (htop : topP' k ∈ C) :
    2 ^ k ≤ sumP' C := by
  have := Multiset.le_sum_of_mem (Multiset.mem_map_of_mem valP' htop)
  simpa [topP', valP', sumP'] using this

/-- **Example 2.1.** `P'_k` computes `x ≥ 2^k`. -/
theorem exampleP'_computesGe (k : ℕ) : (exampleP' k).ComputesGe (2 ^ k) := by
  rw [Protocol.computesGe_iff]
  intro i hi C hC
  have hIC : (exampleP' k).IC i = Multiset.replicate i (some 0) := by
    simp [Protocol.IC, exampleP']
  have hsum0 : sumP' ((exampleP' k).IC i) = i := by
    simp [hIC, sumP', valP']
  by_cases hk : 2 ^ k ≤ i
  · rw [decide_eq_true hk]
    have hInv : topP' k ∈ C ∨ sumP' C = i := by
      refine ex_mreach_inv (fun C => topP' k ∈ C ∨ sumP' C = i) (fun C C' h1 h2 => ?_)
        (Or.inr hsum0) hC
      have := exampleP'_step h2
      by_cases ht : topP' k ∈ C
      · exact Or.inl (this.1 ht)
      · exact Or.inr ((this.2 ht).trans (h1.resolve_left ht))
    -- Phase 1: merge until `2^k` appears.
    obtain ⟨C₁, h₁, -, ht₁⟩ := ex_mreach_descent (T := (exampleP' k).T)
      (fun C => topP' k ∈ C ∨ sumP' C = i) (fun C => topP' k ∈ C)
      (fun C => Multiset.card C - C.count none) (fun C hC hg => by
        have hs := hC.resolve_left hg
        obtain ⟨j, hj, h2⟩ : ∃ j : Fin (k + 1), j ≠ Fin.last k ∧ 2 ≤ C.count (some j) := by
          by_contra hcon
          push Not at hcon
          have := sumP'_lt hg (fun j hj => by have := hcon j hj; omega)
          omega
        have hjk : (j : ℕ) + 1 < k + 1 := by have := Fin.val_lt_last hj; omega
        have hmem : (⟨some j, some j, none, some ⟨j + 1, hjk⟩⟩ : Transition _) ∈
            (exampleP' k).T := by
          show ruleP' k _ _ = _
          simp [ruleP', hj]
        have hle := ex_pre_le_of_two_le (C := C) (t := ⟨some j, some j, none, some ⟨j + 1, hjk⟩⟩)
          rfl h2
        have hst := ex_mstep_of_le hmem hle
        refine ⟨_, hst, ?_, ?_⟩
        · have := exampleP'_step hst
          exact Or.inr ((this.2 hg).trans hs)
        · refine ex_lt_of_count none hst.card_eq ?_
          rw [ex_count_fire hle]
          simp [Transition.pre, Transition.post, -Multiset.count_eq_zero]) C hInv
    -- Phase 2: everybody becomes `2^k`.
    obtain ⟨C₂, h₂, -, ht₂⟩ := ex_mreach_descent (T := (exampleP' k).T)
      (fun C => topP' k ∈ C) (fun C => ∀ q ∈ C, q = topP' k)
      (fun C => Multiset.card C - C.count (topP' k)) (fun C hC hg => by
        push Not at hg
        obtain ⟨q, hq, hne⟩ := hg
        have hmem : (⟨q, topP' k, topP' k, topP' k⟩ : Transition _) ∈ (exampleP' k).T := by
          show ruleP' k _ _ = _
          rw [ruleP'_top_right]
        have hle := ex_pre_le (p' := topP' k) (q' := topP' k) hne (Multiset.count_pos.2 hq)
          (Multiset.count_pos.2 hC)
        have hst := ex_mstep_of_le hmem hle
        refine ⟨_, hst, (exampleP'_step hst).1 hC, ?_⟩
        refine ex_lt_of_count (topP' k) hst.card_eq ?_
        rw [ex_count_fire hle]
        have := Multiset.count_pos.2 hC
        simp only [Transition.pre, Transition.post, Multiset.insert_eq_cons, Multiset.count_cons,
          Multiset.count_singleton, hne.symm, ↓reduceIte]
        omega) C₁ ht₁
    refine ⟨C₂, h₁.trans h₂, fun C' hC' q hq => ?_⟩
    have := ex_mreach_closed (fun s => s = topP' k) (fun t ht hp hq => ?_) ht₂ hC' q hq
    · simp [exampleP', this]
    · obtain ⟨p, q, p', q'⟩ := t
      simp only at hp hq
      subst hp hq
      simp only [exampleP', Set.mem_ofPred_eq, ruleP'_top_left, Prod.mk.injEq] at ht
      exact ⟨ht.1.symm, ht.2.symm⟩
  · rw [decide_eq_false hk]
    have hInv : ∀ C, (exampleP' k).Reach ((exampleP' k).IC i) C → topP' k ∉ C ∧ sumP' C = i := by
      intro C hC
      refine ex_mreach_inv (fun C => topP' k ∉ C ∧ sumP' C = i) (fun C C' h1 h2 => ?_)
        ⟨fun h => by have := le_sumP' h; omega, hsum0⟩ hC
      have hs := ((exampleP'_step h2).2 h1.1).trans h1.2
      exact ⟨fun h => by have := le_sumP' h; omega, hs⟩
    refine ⟨C, .refl, fun C' hC' q hq => ?_⟩
    have := (hInv C' (hC.trans hC')).1
    have hq' : q ≠ topP' k := fun e => this (e ▸ hq)
    simp [exampleP', hq']

end Podc.PPStateComplexity
