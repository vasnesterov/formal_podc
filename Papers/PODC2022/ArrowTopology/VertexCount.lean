import Papers.PODC2022.ArrowTopology.Complexes

/-!
# Number of vertices of `N_I` and `N_O` (Section 2.3.2)

"`N_O` has `|X|(|X| − 1)` vertices … `N_I` has `|X|(|X| − 1) 2^{n−1}` vertices."
We prove `2 · #V(N_I) = |X| (|X| − 1) 2^n` (for `n ≥ 1` voters) and `#V(N_O) = |X| (|X| − 1)`, for
any finite `X`: each vertex `U^σ_{ab}` has exactly the two names `(a, b, σ)` and `(b, a, ¬σ)`.
-/

namespace Podc.ArrowTopology

open Cslib.SocialChoice

/-- If `g : D → V` is surjective, `sw : D → D` has no fixed points, `g ∘ sw = g`, and every fibre
`g⁻¹(g p)` is `{p, sw p}`, then `D ≃ V × Bool`. -/
theorem nonempty_equiv_prod_bool {D V : Type*} (g : D → V) (hg : Function.Surjective g)
    (sw : D → D) (hfix : ∀ p, sw p ≠ p) (hgsw : ∀ p, g (sw p) = g p)
    (hfib : ∀ p q, g p = g q → q = p ∨ q = sw p) : Nonempty (D ≃ V × Bool) := by
  choose sec hsec using hg
  let e : V × Bool → D := fun x => if x.2 then sec x.1 else sw (sec x.1)
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨v, b⟩ ⟨w, c⟩ h
      have hv : v = w := by
        have := congrArg g h
        cases b <;> cases c <;> simpa [e, hgsw, hsec] using this
      subst hv
      cases b <;> cases c
      · rfl
      · simp only [e] at h; exact absurd h (hfix _)
      · simp only [e] at h; exact absurd h.symm (hfix _)
      · rfl
    · intro p
      rcases hfib (sec (g p)) p (hsec _) with h | h
      · exact ⟨(g p, true), h.symm⟩
      · exact ⟨(g p, false), h.symm⟩
  exact ⟨(Equiv.ofBijective e he).symm⟩

variable {ι X : Type*}

/-- Names of vertices: `(a, b, σ)` with `a ≠ b`. -/
abbrev Names (ι X : Type*) := {p : X × X × (ι → Bool) // p.1 ≠ p.2.1}

/-- **Section 2.3.2**: `N_I` has `|X| (|X| − 1) 2^{n − 1}` vertices (stated as
`2 · #V(N_I) = |X| (|X| − 1) 2^n`), for `n ≥ 1` voters and finite `X`. -/
theorem card_VI [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype X] [DecidableEq X] :
    2 * Nat.card (VI ι X) = Fintype.card X * (Fintype.card X - 1) * 2 ^ Fintype.card ι := by
  obtain ⟨e⟩ := nonempty_equiv_prod_bool (D := Names ι X) (V := VI ι X)
    (fun p => vI p.1.1 p.1.2.1 p.1.2.2 p.2)
    (by rintro ⟨_, a, b, σ, h, rfl⟩; exact ⟨⟨(a, b, σ), h⟩, rfl⟩)
    (fun p => ⟨(p.1.2.1, p.1.1, fun i => !p.1.2.2 i), p.2.symm⟩)
    (by rintro ⟨⟨a, b, σ⟩, h⟩ e; simp only [Subtype.mk.injEq, Prod.mk.injEq] at e; exact h e.2.1)
    (by rintro ⟨⟨a, b, σ⟩, h⟩; exact vI_swap a b σ h)
    (by
      rintro ⟨⟨a, b, σ⟩, h⟩ ⟨⟨c, d, τ⟩, h'⟩ e
      rcases U_eq_U h h' (congrArg Subtype.val e) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left; apply Subtype.ext; simp only at h1 h2 h3 ⊢; rw [h1, h2, h3]
      · right; apply Subtype.ext; simp only at h1 h2 h3 ⊢; rw [h1, h2, h3])
  have h1 : Nat.card (Names ι X) = Nat.card (VI ι X) * 2 := by
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  have h2 : Nat.card (Names ι X) = Fintype.card X * (Fintype.card X - 1) * 2 ^ Fintype.card ι := by
    have : Names ι X ≃ {q : X × X // q.1 ≠ q.2} × (ι → Bool) :=
      { toFun := fun p => (⟨(p.1.1, p.1.2.1), p.2⟩, p.1.2.2)
        invFun := fun x => ⟨(x.1.1.1, x.1.1.2, x.2), x.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr this, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_fun, Fintype.card_bool]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_prod]
    have hd : Fintype.card {x : X × X // x.1 = x.2} = Fintype.card X :=
      Fintype.card_congr
        { toFun := fun x => x.1.1
          invFun := fun a => ⟨(a, a), rfl⟩
          left_inv := by rintro ⟨⟨a, b⟩, h⟩; simp only at h; subst h; rfl
          right_inv := fun _ => rfl }
    rw [hd, Nat.mul_sub_one]
  omega

theorem Uo_eq_Uo {a b c d : X} {s t : Bool} (hab : a ≠ b) (hcd : c ≠ d)
    (e : Uo a b s = Uo c d t) : (c = a ∧ d = b ∧ t = s) ∨ (c = b ∧ d = a ∧ t = !s) := by
  have e' : U (ι := Unit) a b (fun _ => s) = U c d (fun _ => t) := by
    ext R
    simp only [U, Set.mem_ofPred_eq]
    constructor
    · intro h i; have : R i ∈ Uo c d t := e ▸ h i; exact this
    · intro h i; have : R i ∈ Uo a b s := e.symm ▸ h i; exact this
  rcases U_eq_U hab hcd e' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, congrFun h3 ()⟩
  · exact Or.inr ⟨h1, h2, congrFun h3 ()⟩

/-- **Section 2.3.2**: `N_O` has `|X| (|X| − 1)` vertices (finite `X`). -/
theorem card_VO [Fintype X] [DecidableEq X] :
    Nat.card (VO X) = Fintype.card X * (Fintype.card X - 1) := by
  obtain ⟨e⟩ := nonempty_equiv_prod_bool (D := {p : X × X × Bool // p.1 ≠ p.2.1}) (V := VO X)
    (fun p => vO p.1.1 p.1.2.1 p.1.2.2 p.2)
    (by rintro ⟨_, a, b, s, h, rfl⟩; exact ⟨⟨(a, b, s), h⟩, rfl⟩)
    (fun p => ⟨(p.1.2.1, p.1.1, !p.1.2.2), p.2.symm⟩)
    (by rintro ⟨⟨a, b, s⟩, h⟩ e; simp only [Subtype.mk.injEq, Prod.mk.injEq] at e; exact h e.2.1)
    (by rintro ⟨⟨a, b, s⟩, h⟩; exact vO_swap a b s h)
    (by
      rintro ⟨⟨a, b, s⟩, h⟩ ⟨⟨c, d, t⟩, h'⟩ e
      rcases Uo_eq_Uo h h' (congrArg Subtype.val e) with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left; apply Subtype.ext; simp only at h1 h2 h3 ⊢; rw [h1, h2, h3]
      · right; apply Subtype.ext; simp only at h1 h2 h3 ⊢; rw [h1, h2, h3])
  have h1 : Nat.card {p : X × X × Bool // p.1 ≠ p.2.1} = Nat.card (VO X) * 2 := by
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
  have h2 : Nat.card {p : X × X × Bool // p.1 ≠ p.2.1} =
      Fintype.card X * (Fintype.card X - 1) * 2 := by
    have : {p : X × X × Bool // p.1 ≠ p.2.1} ≃ {q : X × X // q.1 ≠ q.2} × Bool :=
      { toFun := fun p => (⟨(p.1.1, p.1.2.1), p.2⟩, p.1.2.2)
        invFun := fun x => ⟨(x.1.1.1, x.1.1.2, x.2), x.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr this, Nat.card_prod, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_bool]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_prod]
    have hd : Fintype.card {x : X × X // x.1 = x.2} = Fintype.card X :=
      Fintype.card_congr
        { toFun := fun x => x.1.1
          invFun := fun a => ⟨(a, a), rfl⟩
          left_inv := by rintro ⟨⟨a, b⟩, h⟩; simp only at h; subst h; rfl
          right_inv := fun _ => rfl }
    rw [hd, Nat.mul_sub_one]
  omega

end Podc.ArrowTopology
