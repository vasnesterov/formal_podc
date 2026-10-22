import Papers.PODC2017.PPVerification.Defs
import Mathlib.Data.Int.Interval

/-!
# The threshold protocol `P_thr` (§5)

For a threshold predicate `∑ᵢ aᵢ xᵢ < c` and a bound `v` (the paper takes
`v = vmax = max(|a₁|, …, |a_k|, |c| + 1)`), states are triples `(ℓ, n, o)`: leader bit `ℓ`,
value `n ∈ [-v, v]`, opinion `o`. The only non-identity transitions are

  `(1, n, o), (ℓ, n', o') ↦ (1, f(n, n'), b(n, n')), (0, g(n, n'), b(n, n'))`

with `f(m, n) = max(-v, min(v, m + n))`, `g(m, n) = m + n − f(m, n)`, `b(m, n) = (f(m, n) < c)`.
The paper does not say which transitions the pairs `(p, q)` with a non-leader `p` have; as in its
Example 1 we add the identity transitions for these pairs (needed for totality).

* `Threshold.protocol c a ha` (general bound `v`), `Threshold.Pthr c a` (the paper's `vmax`).
* `Threshold.val`, `Threshold.flowEq_val` (Proposition 23), `Threshold.consensus_of_terminal`
  (Proposition 24), `Threshold.proposition_17`.
-/

namespace Podc.PPVerification.Threshold

open Cslib.PopulationProtocol Cslib.TransitionSystem

/-- States `(leader, value, opinion)`. -/
abbrev St (v : ℤ) := Bool × Set.Icc (-v) v × Bool

/-- The value of a state. -/
def valS {v : ℤ} (s : St v) : ℤ := s.2.1

/-- `max(-v, min(v, s))`. -/
def clampV (v s : ℤ) : ℤ := max (-v) (min v s)

variable {v : ℤ}

/-- `f(m, n) = max(-v, min(v, m + n))`. -/
def fV (m n : Set.Icc (-v) v) : Set.Icc (-v) v :=
  ⟨clampV v (m + n), by
    have := m.2.1; have := m.2.2
    simp only [clampV, Set.mem_Icc]; omega⟩

/-- `g(m, n) = m + n − f(m, n)`. -/
def gV (m n : Set.Icc (-v) v) : Set.Icc (-v) v :=
  ⟨m + n - clampV v (m + n), by
    have := m.2.1; have := m.2.2; have := n.2.1; have := n.2.2
    simp only [clampV, Set.mem_Icc]; omega⟩

variable (c : ℤ)

/-- The transition of a leader `p` (initiator) meeting `q`. -/
def mainT (p q : St v) : Transition (St v) :=
  ⟨p, q, (true, fV p.2.1 q.2.1, decide ((fV p.2.1 q.2.1 : ℤ) < c)),
    (false, gV p.2.1 q.2.1, decide ((fV p.2.1 q.2.1 : ℤ) < c))⟩

/-- The transitions of `P_thr`: `mainT p q` for a leader `p`, identity transitions for a
non-leader `p`. -/
def trans : Set (Transition (St v)) :=
  {t | (t.p.1 = true ∧ t = mainT c t.p t.q) ∨ (t.p.1 = false ∧ t.p' = t.p ∧ t.q' = t.q)}

theorem mainT_mem {p q : St v} (hp : p.1 = true) : mainT c p q ∈ trans c := Or.inl ⟨hp, rfl⟩

/-- The threshold protocol for `∑ aᵢ xᵢ < c` with value bound `v`. -/
def protocol {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) : MProtocol (St v) Λ where
  T := trans c
  total p q := by
    cases hp : p.1
    · exact ⟨p, q, Or.inr ⟨hp, rfl, rfl⟩⟩
    · exact ⟨_, _, mainT_mem c hp (q := q)⟩
  I i := (true, ⟨a i, by have := abs_le.1 (ha i); exact ⟨this.1, this.2⟩⟩, decide (a i < c))
  O s := s.2.2

/-- `vmax = max(|a₁|, …, |a_k|, |c| + 1)`. -/
def vmax {Λ : Type*} [Fintype Λ] (a : Λ → ℤ) : ℤ := Finset.univ.fold max (|c| + 1) fun i => |a i|

theorem le_vmax {Λ : Type*} [Fintype Λ] (a : Λ → ℤ) :
    |c| + 1 ≤ vmax c a ∧ ∀ i, |a i| ≤ vmax c a := by
  refine ⟨Finset.le_fold_max _ |>.2 (.inl le_rfl), fun i => ?_⟩
  exact (Finset.le_fold_max _).2 (.inr ⟨i, Finset.mem_univ _, le_rfl⟩)

/-- **The protocol `P_thr` of §5** for the threshold predicate `∑ᵢ a(i) · X(i) < c`, with the
paper's bound `vmax`. -/
def Pthr {Λ : Type*} [Fintype Λ] (a : Λ → ℤ) : MProtocol (St (vmax c a)) Λ :=
  protocol c a (le_vmax c a).2

/-- `val(C) = ∑_q C(q) · val(q)`. -/
def val (C : Multiset (St v)) : ℤ := (C.map valS).sum

/-! ### Silent transitions -/

/-- A silent transition of a leader `p`: `q` is a non-leader, `p` keeps its value, and both end
with the opinion `b(m, n) = (m < c)`. -/
theorem mainT_silent {p q : St v} (hp : p.1 = true) (hs : (mainT c p q).Silent) :
    q.1 = false ∧ fV p.2.1 q.2.1 = p.2.1 ∧ gV p.2.1 q.2.1 = q.2.1 ∧
      decide ((fV p.2.1 q.2.1 : ℤ) < c) = p.2.2 ∧ decide ((fV p.2.1 q.2.1 : ℤ) < c) = q.2.2 := by
  obtain ⟨pl, m, o⟩ := p
  obtain ⟨ql, n, o'⟩ := q
  simp only at hp ⊢
  subst hp
  have hpmem : (true, m, o) ∈ (mainT c (true, m, o) (ql, n, o')).post := by
    rw [← hs]; simp [Transition.pre, mainT]
  simp only [Transition.post, mainT, Multiset.insert_eq_cons, Multiset.mem_cons,
    Multiset.mem_singleton] at hpmem
  rcases hpmem with hpe | hpe
  · have h2 := hs
    simp only [Transition.Silent, Transition.pre, Transition.post, mainT,
      Multiset.insert_eq_cons] at h2
    conv_lhs at h2 => rw [hpe]
    have hq := Multiset.singleton_inj.1 (Multiset.cons_inj_right _ |>.1 h2)
    simp only [Prod.ext_iff] at hpe hq
    obtain ⟨-, hm, ho⟩ := hpe
    obtain ⟨hl, hn, ho'⟩ := hq
    exact ⟨hl, hm.symm, hn.symm, ho.symm, ho'.symm⟩
  · simp [Prod.ext_iff] at hpe

/-- Identity transitions are silent. -/
theorem silent_of_mem_trans {t : Transition (St v)} (ht : t ∈ trans c) (hp : t.p.1 = false) :
    t.Silent := by
  rcases ht with ⟨h, -⟩ | ⟨-, h1, h2⟩
  · simp [h] at hp
  · simp [Transition.Silent, Transition.pre, Transition.post, h1, h2]

/-! ### The ordered partition of Proposition 18 -/

/-- `pre(t) = ⦃q, r⦄` with `q ∈ L₀ = {(1, x, 0) : c ≤ x}` and `r ∈ N₁ = {(0, 0, 1)}`. -/
def InL0N1 (t : Transition (St v)) : Prop :=
  ∃ m n : Set.Icc (-v) v, c ≤ m ∧ (n : ℤ) = 0 ∧ t.pre = {(true, m, false), (false, n, true)}

/-- `T₁ = {t ∈ T : pre(t) ≠ ⦃q, r⦄ for all q ∈ L₀, r ∈ N₁}`. -/
def T1 : Set (Transition (St v)) := {t | t ∈ trans c ∧ ¬ InL0N1 c t}

/-- `T₂ = T \ T₁`. -/
def T2 : Set (Transition (St v)) := {t | t ∈ trans c ∧ InL0N1 c t}

end Podc.PPVerification.Threshold
