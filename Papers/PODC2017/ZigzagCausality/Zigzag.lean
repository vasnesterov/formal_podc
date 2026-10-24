import Papers.PODC2017.ZigzagCausality.Basic

/-!
# Two-legged forks, zigzag patterns, Theorem 1 (zigzag sufficiency) — Section 3

* `Fork` — a two-legged fork `F = ⟨θ₀, θ₀·p₁, θ₀·p₂⟩` (Definition 5), with `head = θ₀·p₁`,
  `tail = θ₀·p₂` and weight `wt(F) = L(p₁) − U(p₂)`.
* `IsZigzag γ r Z θ θ'` — `Z = (F₁, …, F_c)` is a zigzag pattern from `θ` to `θ'` in `r`
  (Definition 6): `tail(F₁) = θ`, `head(F_c) = θ'`, and the head of each fork and the tail of the
  next one are on the same process, the head not later than the tail.
* `wtZ` — `wt(Z) = Σ wt(F_k) + S(Z)`, where `S(Z)` counts consecutive forks that are not joined
  (head and next tail are different basic nodes).
* `zigzag_sufficiency` — **Theorem 1**.
* `Visible` — σ-visible zigzag patterns (Definition 7).
-/

set_option linter.unusedSectionVars false

namespace Podc.ZigzagCausality

open Classical

variable {P S M E : Type*}

/-- A two-legged fork `⟨θ₀, θ₀·p₁, θ₀·p₂⟩` (Definition 5). -/
structure Fork (P S M E : Type*) where
  /-- The base `θ₀`. -/
  base : GNode P S M E
  /-- The continuation from the base to the head. -/
  p1 : List P
  /-- The continuation from the base to the tail. -/
  p2 : List P

namespace Fork

/-- `head(F) = θ₀·p₁`. -/
def head (F : Fork P S M E) : GNode P S M E := F.base.ext F.p1

/-- `tail(F) = θ₀·p₂`. -/
def tail (F : Fork P S M E) : GNode P S M E := F.base.ext F.p2

/-- `wt(F) = L(p₁) − U(p₂)` (the paths start at the process of the base). -/
def wt (N : Net P) (F : Fork P S M E) : ℤ := N.Lp F.base.proc F.p1 - N.Up F.base.proc F.p2

/-- The trivial fork `⟨θ, θ, θ⟩` (weight `0`). -/
def triv (θ : GNode P S M E) : Fork P S M E := ⟨θ, [], []⟩

@[simp] theorem triv_head (θ : GNode P S M E) : (triv θ).head = θ := by simp [triv, head]
@[simp] theorem triv_tail (θ : GNode P S M E) : (triv θ).tail = θ := by simp [triv, tail]
@[simp] theorem triv_wt (N : Net P) (θ : GNode P S M E) : (triv θ).wt N = 0 := by
  simp [triv, wt]

end Fork

namespace Sys

variable (γ : Sys P S M E) (r : Sched P S E) [Finite P]

/-- The fork is a fork *in `r`*: its nodes appear in `r`. -/
def ForkIn (F : Fork P S M E) : Prop := γ.appearsG r F.head ∧ γ.appearsG r F.tail

/-- `θ` and `θ'` correspond to nodes of the same process, `θ` not later than `θ'`. -/
def Adj (θ θ' : GNode P S M E) : Prop :=
  ∃ σ σ', γ.basic r θ = some σ ∧ γ.basic r θ' = some σ' ∧ σ.1 = σ'.1 ∧
    γ.timer r σ ≤ γ.timer r σ'

/-- Contribution of a junction to `S(Z)`: `0` if the head and the next tail are the same basic
node (the forks are *joined*), `1` otherwise. -/
noncomputable def gap (θ θ' : GNode P S M E) : ℤ := if γ.basic r θ = γ.basic r θ' then 0 else 1

/-- `Z` is a zigzag pattern from `θ` to `θ'` in `r` (Definition 6). -/
def IsZigzag : List (Fork P S M E) → GNode P S M E → GNode P S M E → Prop
  | [], _, _ => False
  | [F], θ, θ' => γ.ForkIn r F ∧ F.tail = θ ∧ F.head = θ'
  | F :: G :: Z, θ, θ' =>
      γ.ForkIn r F ∧ F.tail = θ ∧ γ.Adj r F.head G.tail ∧ IsZigzag (G :: Z) G.tail θ'

/-- The weight `wt(Z) = Σ_k wt(F_k) + S(Z)` of a zigzag pattern. -/
noncomputable def wtZ : List (Fork P S M E) → ℤ
  | [] => 0
  | [F] => F.wt γ.net
  | F :: G :: Z => F.wt γ.net + γ.gap r F.head G.tail + wtZ (G :: Z)

/-- `θ` is σ-recognized: its root is in the past of `σ`. -/
def Recognized (σ : BNode P S M E) (θ : GNode P S M E) : Prop := γ.HB r θ.root σ

/-- `Z` is σ-visible (Definition 7): (i) the heads of all forks but the last are in the past of
`σ`, and (ii) the base of the last fork is σ-recognized. -/
def Visible (σ : BNode P S M E) : List (Fork P S M E) → Prop
  | [] => False
  | [F] => γ.HB r F.base.root σ
  | F :: G :: Z => (∃ τ, γ.basic r F.head = some τ ∧ γ.HB r τ σ) ∧ Visible σ (G :: Z)

variable {γ r}

theorem prec_trans {θ₁ θ₂ θ₃ : GNode P S M E} {x y : ℤ} (h : γ.Prec r θ₁ x θ₂)
    (h' : γ.Prec r θ₂ y θ₃) : γ.Prec r θ₁ (x + y) θ₃ := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  obtain ⟨b', c, hb', hc, hbc⟩ := h'
  rw [hb] at hb'; cases hb'
  exact ⟨a, c, ha, hc, by omega⟩

/-- A fork in `r` implies `tail(F) --wt(F)--> head(F)`. -/
theorem prec_fork (hr : γ.Valid r) {F : Fork P S M E} (hF : γ.ForkIn r F) :
    γ.Prec r F.tail (F.wt γ.net) F.head := by
  obtain ⟨σh, hh⟩ := Option.isSome_iff_exists.1 hF.1
  obtain ⟨σt, ht⟩ := Option.isSome_iff_exists.1 hF.2
  refine ⟨σt, σh, ht, hh, ?_⟩
  simp only [Fork.head, Fork.tail, basic_ext] at hh ht
  obtain ⟨τ, hτ, hh⟩ := Option.bind_eq_some_iff.1 hh
  obtain ⟨τ', hτ', ht⟩ := Option.bind_eq_some_iff.1 ht
  rw [hτ] at hτ'; cases hτ'
  have h1 := gbasic_timer hr hh
  have h2 := gbasic_timer hr ht
  rw [γ.basic_proc r hτ] at h1 h2
  simp only [Fork.wt]
  omega

/-- A junction of a zigzag pattern gives a precedence of weight `gap`. -/
theorem prec_adj {θ θ' : GNode P S M E} (h : γ.Adj r θ θ') : γ.Prec r θ (γ.gap r θ θ') θ' := by
  obtain ⟨σ, σ', h1, h2, hp, ht⟩ := h
  refine ⟨σ, σ', h1, h2, ?_⟩
  simp only [gap, h1, h2]
  split_ifs with he
  · cases he; simp
  · have hne : σ ≠ σ' := fun e => he (by rw [e])
    have := γ.timer_lt_of_ne r hp (gbasic_appears γ r h1).2 (gbasic_appears γ r h2).2 ht hne
    omega

/-- **Theorem 1 (Zigzag Sufficiency).** A zigzag pattern `Z` from `θ₁` to `θ₂` in `r` implies
`(R, r) ⊨ θ₁ --wt(Z)--> θ₂`. -/
theorem zigzag_sufficiency (hr : γ.Valid r) :
    ∀ {Z : List (Fork P S M E)} {θ₁ θ₂ : GNode P S M E}, γ.IsZigzag r Z θ₁ θ₂ →
      γ.Prec r θ₁ (γ.wtZ r Z) θ₂
  | [], _, _, h => h.elim
  | [F], _, _, ⟨hF, rfl, rfl⟩ => prec_fork hr hF
  | F :: G :: Z, _, _, ⟨hF, rfl, hadj, hZ⟩ => by
      have := prec_trans (prec_trans (prec_fork hr hF) (prec_adj hadj))
        (zigzag_sufficiency hr hZ)
      simpa [wtZ, add_assoc] using this

end Sys

end Podc.ZigzagCausality
