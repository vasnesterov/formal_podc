import Papers.PODC2011.CompactPolicyRouting.Algebra

/-!
# Lexicographic products of routing algebras (Proposition 4.4, Table 4.2)

* `OrdSemigroup F`: a totally ordered commutative semigroup (no infinity element), with the properties of
  Definition 4.3 (Gurney–Griffin style).
* `OrdSemigroup.withTop S`: the delimited routing algebra obtained by adjoining an absorbing maximal `φ = ⊤`;
  transfer lemmas `withTop_isMonotone_iff`, ….
* `OrdSemigroup.lex S T`: the lexicographic product, and Proposition 4.4 for it (`lex_isMonotone_iff`,
  `lex_isIsotone_iff`, `lex_isStrictlyMonotone_iff`); lifted to delimited routing algebras via their finite parts
  (`RoutingAlgebra.lexProd`, `lexProd_isMonotone_iff`, …).
* The paper's literal product on `W_A × W_B` with `φ = (φ_A, φ_B)` (`RoutingAlgebra.litProd`) is not delimited
  and violates the (M) rule of Proposition 4.4.
* Table 4.2: `shortestPath`, `widestPath`, `usablePath`, `mostReliable`, `widestShortest`, `shortestWidest`,
  `mostReliableWS`, with their properties; two slips of the table (`mostReliable_not_isStrictlyMonotone`,
  `mostReliableWS_isIsotone`).
* Condition (4.2) of Theorem 4.17 for shortest-widest path (`shortestWidest_condition_4_2`), and its
  incompatibility with regularity (`not_condition_4_2_of_regular`).
-/

namespace Podc.CompactPolicyRouting

open OrderDual

universe u v

/-- A totally ordered commutative semigroup `(F, ⊕, ⪯)` (the finite part of a delimited routing algebra). -/
structure OrdSemigroup (F : Type u) [LinearOrder F] where
  /-- Composition `⊕`. -/
  op : F → F → F
  op_assoc : ∀ a b c, op (op a b) c = op a (op b c)
  op_comm : ∀ a b, op a b = op b a

namespace OrdSemigroup

variable {F : Type u} [LinearOrder F] {G : Type v} [LinearOrder G]

section Props

variable (S : OrdSemigroup F)

/-- Monotone (M): `a ⪯ b ⊕ a`. -/
def IsMonotone : Prop := ∀ a b : F, a ≤ S.op b a
/-- Isotone (I): `a ⪯ b → c ⊕ a ⪯ c ⊕ b`. -/
def IsIsotone : Prop := ∀ a b c : F, a ≤ b → S.op c a ≤ S.op c b
/-- Strictly monotone (SM): `a ≺ b ⊕ a`. -/
def IsStrictlyMonotone : Prop := ∀ a b : F, a < S.op b a
/-- Selective (S): `a ⊕ b ∈ {a, b}`. -/
def IsSelective : Prop := ∀ a b : F, S.op a b = a ∨ S.op a b = b
/-- Cancellative (N): `a ⊕ b = a ⊕ c → b = c`. -/
def IsCancellative : Prop := ∀ a b c : F, S.op a b = S.op a c → b = c
/-- Condensed (C): `a ⊕ b = a ⊕ c`. -/
def IsCondensed : Prop := ∀ a b c : F, S.op a b = S.op a c

theorem IsStrictlyMonotone.isMonotone {S : OrdSemigroup F} (h : S.IsStrictlyMonotone) :
    S.IsMonotone := fun a b => (h a b).le

end Props

/-! ### Adjoining `φ = ⊤` -/

/-- The delimited routing algebra `(F ∪ {φ}, φ, ⊕, ⪯)` with `φ = ⊤` absorbing. -/
def withTop (S : OrdSemigroup F) : RoutingAlgebra (WithTop F) where
  op := Option.map₂ S.op
  op_assoc a b c := by
    rcases a with _ | a <;> rcases b with _ | b <;> rcases c with _ | c <;> try rfl
    exact congrArg some (S.op_assoc a b c)
  op_comm a b := by
    rcases a with _ | a <;> rcases b with _ | b <;> try rfl
    exact congrArg some (S.op_comm a b)
  phi := ⊤
  op_phi a := by rcases a with _ | a <;> rfl
  le_phi a := le_top

variable (S : OrdSemigroup F)

@[simp] theorem withTop_phi : S.withTop.phi = ⊤ := rfl

@[simp] theorem withTop_op_coe (a b : F) : S.withTop.op (a : WithTop F) b = (S.op a b : F) := rfl

@[simp] theorem withTop_op_top (x : WithTop F) : S.withTop.op x ⊤ = ⊤ := S.withTop.op_phi x

@[simp] theorem withTop_top_op (x : WithTop F) : S.withTop.op ⊤ x = ⊤ := S.withTop.phi_op x

theorem withTop_isDelimited : S.withTop.IsDelimited := by
  intro a b ha hb
  rcases a with _ | a
  · exact absurd rfl ha
  rcases b with _ | b
  · exact absurd rfl hb
  exact WithTop.coe_ne_top

theorem withTop_isMonotone_iff : S.withTop.IsMonotone ↔ S.IsMonotone := by
  constructor
  · intro h a b; exact WithTop.coe_le_coe.1 (h a b)
  · intro h a b
    induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;> simp
    exact h _ _

theorem withTop_isStrictlyMonotone_iff : S.withTop.IsStrictlyMonotone ↔ S.IsStrictlyMonotone := by
  constructor
  · intro h a b; exact WithTop.coe_lt_coe.1 (h a b WithTop.coe_ne_top)
  · intro h a b ha
    induction a using WithTop.recTopCoe
    · exact absurd rfl ha
    induction b using WithTop.recTopCoe
    · simp
    · exact WithTop.coe_lt_coe.2 (h _ _)

theorem withTop_isIsotone_iff : S.withTop.IsIsotone ↔ S.IsIsotone := by
  constructor
  · intro h a b c hab; exact WithTop.coe_le_coe.1 (h a b c (WithTop.coe_le_coe.2 hab))
  · intro h a b c hab
    induction c using WithTop.recTopCoe
    · simp
    induction b using WithTop.recTopCoe
    · simp
    induction a using WithTop.recTopCoe
    · exact absurd hab (by simp)
    exact WithTop.coe_le_coe.2 (h _ _ _ (WithTop.coe_le_coe.1 hab))

theorem withTop_isSelective_iff : S.withTop.IsSelective ↔ S.IsSelective := by
  constructor
  · intro h a b
    rcases h a b with h' | h'
    · exact Or.inl (WithTop.coe_inj.1 h')
    · exact Or.inr (WithTop.coe_inj.1 h')
  · intro h a b
    induction a using WithTop.recTopCoe
    · simp
    induction b using WithTop.recTopCoe
    · simp
    simpa using h _ _

theorem withTop_isCancellative_iff : S.withTop.IsCancellative ↔ S.IsCancellative := by
  constructor
  · intro h a b c hab
    exact WithTop.coe_inj.1 (h a b c WithTop.coe_ne_top (by simp [hab]))
  · intro h a b c ha hab
    induction a using WithTop.recTopCoe
    · exact absurd rfl ha
    induction b using WithTop.recTopCoe <;> induction c using WithTop.recTopCoe <;> simp at hab ⊢
    exact h _ _ _ hab

theorem withTop_isCondensed_iff : S.withTop.IsCondensed ↔ S.IsCondensed := by
  constructor
  · intro h a b c
    exact WithTop.coe_inj.1 (h a b c WithTop.coe_ne_top WithTop.coe_ne_top WithTop.coe_ne_top)
  · intro h a b c ha hb hc
    induction a using WithTop.recTopCoe
    · exact absurd rfl ha
    induction b using WithTop.recTopCoe
    · exact absurd rfl hb
    induction c using WithTop.recTopCoe
    · exact absurd rfl hc
    simp [h _ _ ‹F›]

/-! ### Lexicographic product (Proposition 4.4) -/

/-- The lexicographic product `S × T`: componentwise composition, lexicographic order. -/
def lex (S : OrdSemigroup F) (T : OrdSemigroup G) : OrdSemigroup (Lex (F × G)) where
  op x y := toLex (S.op (ofLex x).1 (ofLex y).1, T.op (ofLex x).2 (ofLex y).2)
  op_assoc x y z := by simp [S.op_assoc, T.op_assoc]
  op_comm x y := by simp [S.op_comm, T.op_comm]

variable {S} {T : OrdSemigroup G}

@[simp] theorem lex_op (a b : F) (x y : G) :
    (S.lex T).op (toLex (a, x)) (toLex (b, y)) = toLex (S.op a b, T.op x y) := rfl

private theorem lex_le {a b : F} {x y : G} :
    toLex (a, x) ≤ toLex (b, y) ↔ a < b ∨ a = b ∧ x ≤ y := Prod.Lex.toLex_le_toLex

private theorem lex_lt {a b : F} {x y : G} :
    toLex (a, x) < toLex (b, y) ↔ a < b ∨ a = b ∧ x < y := Prod.Lex.toLex_lt_toLex

omit [LinearOrder F] [LinearOrder G] in
private theorem lex_forall {P : Lex (F × G) → Prop} : (∀ p, P p) ↔ ∀ a x, P (toLex (a, x)) :=
  ⟨fun h _ _ => h _, fun h p => h (ofLex p).1 (ofLex p).2⟩

/-- Proposition 4.4 (M rule) of [Rétvári et al., *Compact policy routing*], after Gurney–Griffin:
`M(A × B) ⇔ SM(A) ∨ (M(A) ∧ M(B))`, for ordered commutative semigroups with `B` nonempty. -/
theorem lex_isMonotone_iff [Nonempty G] :
    (S.lex T).IsMonotone ↔ S.IsStrictlyMonotone ∨ (S.IsMonotone ∧ T.IsMonotone) := by
  simp only [IsMonotone, IsStrictlyMonotone, lex_forall, lex_op, lex_le]
  constructor
  · intro h
    have hM : ∀ a b : F, a ≤ S.op b a := fun a b => by
      obtain ⟨x⟩ := ‹Nonempty G›
      rcases h a x b x with h' | ⟨h', -⟩
      · exact h'.le
      · exact h'.le
    by_cases hSM : ∀ a b : F, a < S.op b a
    · exact Or.inl hSM
    · push Not at hSM
      obtain ⟨a, b, hab⟩ := hSM
      have heq : a = S.op b a := le_antisymm (hM a b) hab
      refine Or.inr ⟨hM, fun x y => ?_⟩
      rcases h a x b y with h' | ⟨-, h'⟩
      · exact absurd heq h'.ne
      · exact h'
  · rintro (h | ⟨hA, hB⟩) a x b y
    · exact Or.inl (h a b)
    · rcases (hA a b).lt_or_eq with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', hB x y⟩

/-- Proposition 4.4 (SM rule) of [Rétvári et al., *Compact policy routing*], after Gurney–Griffin:
`SM(A × B) ⇔ SM(A) ∨ (M(A) ∧ SM(B))`, for ordered commutative semigroups with `B` nonempty. -/
theorem lex_isStrictlyMonotone_iff [Nonempty G] :
    (S.lex T).IsStrictlyMonotone ↔ S.IsStrictlyMonotone ∨ (S.IsMonotone ∧ T.IsStrictlyMonotone) := by
  simp only [IsMonotone, IsStrictlyMonotone, lex_forall, lex_op, lex_lt]
  constructor
  · intro h
    have hM : ∀ a b : F, a ≤ S.op b a := fun a b => by
      obtain ⟨x⟩ := ‹Nonempty G›
      rcases h a x b x with h' | ⟨h', -⟩
      · exact h'.le
      · exact h'.le
    by_cases hSM : ∀ a b : F, a < S.op b a
    · exact Or.inl hSM
    · push Not at hSM
      obtain ⟨a, b, hab⟩ := hSM
      have heq : a = S.op b a := le_antisymm (hM a b) hab
      refine Or.inr ⟨hM, fun x y => ?_⟩
      rcases h a x b y with h' | ⟨-, h'⟩
      · exact absurd heq h'.ne
      · exact h'
  · rintro (h | ⟨hA, hB⟩) a x b y
    · exact Or.inl (h a b)
    · rcases (hA a b).lt_or_eq with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨h', hB x y⟩

/-- Proposition 4.4 (I rule) of [Rétvári et al., *Compact policy routing*], after Gurney–Griffin:
`I(A × B) ⇔ I(A) ∧ I(B) ∧ (N(A) ∨ C(B))`, for ordered commutative semigroups with nonempty carriers. -/
theorem lex_isIsotone_iff [Nonempty F] [Nonempty G] :
    (S.lex T).IsIsotone ↔ S.IsIsotone ∧ T.IsIsotone ∧ (S.IsCancellative ∨ T.IsCondensed) := by
  simp only [IsIsotone, IsCancellative, IsCondensed, lex_forall, lex_op, lex_le]
  constructor
  · intro h
    refine ⟨fun a b c hab => ?_, fun x y z hxy => ?_, ?_⟩
    · obtain ⟨x⟩ := ‹Nonempty G›
      rcases hab.lt_or_eq with hab | rfl
      · rcases h a x b x c x (Or.inl hab) with h' | ⟨h', -⟩
        · exact h'.le
        · exact h'.le
      · exact le_rfl
    · obtain ⟨a⟩ := ‹Nonempty F›
      rcases h a x a y a z (Or.inr ⟨rfl, hxy⟩) with h' | ⟨-, h'⟩
      · exact absurd h' (lt_irrefl _)
      · exact h'
    · by_cases hC : ∀ z x y : G, T.op z x = T.op z y
      · exact Or.inr hC
      · push Not at hC
        obtain ⟨z, x, y, hxy⟩ := hC
        -- a pair `x', y'` with `z ⊕ y' ≺ z ⊕ x'`
        obtain ⟨x', y', hlt⟩ : ∃ x' y', T.op z y' < T.op z x' := by
          rcases lt_or_gt_of_ne hxy with h' | h'
          · exact ⟨y, x, h'⟩
          · exact ⟨x, y, h'⟩
        refine Or.inl fun c a b hcab => ?_
        by_contra hab
        have key : ∀ a b : F, a < b → S.op c a = S.op c b → False := fun a b hab hcab => by
          rcases h a x' b y' c z (Or.inl hab) with h' | ⟨-, h'⟩
          · exact h'.ne hcab
          · exact absurd h' (not_le.2 hlt)
        rcases lt_or_gt_of_ne hab with h' | h'
        · exact key a b h' hcab
        · exact key b a h' hcab.symm
  · rintro ⟨hA, hB, hNC⟩ a x b y c z (hab | ⟨rfl, hxy⟩)
    · rcases (hA a b c hab.le).lt_or_eq with h' | h'
      · exact Or.inl h'
      · refine Or.inr ⟨h', ?_⟩
        rcases hNC with hN | hC
        · exact absurd (hN c a b h') hab.ne
        · exact (hC z x y).le
    · exact Or.inr ⟨rfl, hB x y z hxy⟩

end OrdSemigroup

/-! ### Lifting to delimited routing algebras -/

namespace RoutingAlgebra

variable {W : Type u} [LinearOrder W] {V : Type v} [LinearOrder V]

/-- The finite part `{w // w ≠ φ}` of a delimited routing algebra is an ordered commutative semigroup. -/
def fin (A : RoutingAlgebra W) (hA : A.IsDelimited) : OrdSemigroup {a : W // a ≠ A.phi} where
  op a b := ⟨A.op a b, hA _ _ a.2 b.2⟩
  op_assoc a b c := Subtype.ext (A.op_assoc a b c)
  op_comm a b := Subtype.ext (A.op_comm a b)

variable (A : RoutingAlgebra W) (hA : A.IsDelimited)

theorem fin_isMonotone_iff : (A.fin hA).IsMonotone ↔ A.IsMonotone := by
  constructor
  · intro h a b
    by_cases ha : a = A.phi
    · subst ha; rw [A.op_phi]
    by_cases hb : b = A.phi
    · subst hb; rw [A.phi_op]; exact A.le_phi a
    exact h ⟨a, ha⟩ ⟨b, hb⟩
  · intro h a b; exact h a b

theorem fin_isStrictlyMonotone_iff : (A.fin hA).IsStrictlyMonotone ↔ A.IsStrictlyMonotone := by
  constructor
  · intro h a b ha
    by_cases hb : b = A.phi
    · subst hb; rw [A.phi_op]; exact A.lt_phi ha
    exact h ⟨a, ha⟩ ⟨b, hb⟩
  · intro h a b; exact h a b a.2

theorem fin_isIsotone_iff : (A.fin hA).IsIsotone ↔ A.IsIsotone := by
  constructor
  · intro h a b c hab
    by_cases hc : c = A.phi
    · subst hc; rw [A.phi_op, A.phi_op]
    by_cases hb : b = A.phi
    · subst hb; rw [A.op_phi]; exact A.le_phi _
    have ha : a ≠ A.phi := fun ha => hb (le_antisymm (A.le_phi b) (ha ▸ hab))
    exact h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ hab
  · intro h a b c hab; exact h a b c hab

theorem fin_isCancellative_iff : (A.fin hA).IsCancellative ↔ A.IsCancellative := by
  constructor
  · intro h a b c ha habc
    by_cases hb : b = A.phi
    · by_contra hc
      subst hb; rw [A.op_phi] at habc; exact hA a c ha (fun e => hc e.symm) habc.symm
    by_cases hc : c = A.phi
    · subst hc; rw [A.op_phi] at habc; exact absurd habc (hA a b ha hb)
    exact congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ (Subtype.ext habc))
  · intro h a b c habc
    exact Subtype.ext (h a b c a.2 (congrArg Subtype.val habc))

theorem fin_isCondensed_iff : (A.fin hA).IsCondensed ↔ A.IsCondensed := by
  constructor
  · intro h a b c ha hb hc; exact congrArg Subtype.val (h ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩)
  · intro h a b c; exact Subtype.ext (h a b c a.2 b.2 c.2)

/-- The lexicographic product of two delimited routing algebras: the lexicographic product of their finite parts,
with a fresh absorbing maximal `φ = ⊤`. -/
def lexProd (A : RoutingAlgebra W) (B : RoutingAlgebra V) (hA : A.IsDelimited) (hB : B.IsDelimited) :
    RoutingAlgebra (WithTop (Lex ({a : W // a ≠ A.phi} × {b : V // b ≠ B.phi}))) :=
  ((A.fin hA).lex (B.fin hB)).withTop

variable (B : RoutingAlgebra V) (hB : B.IsDelimited)

theorem lexProd_isDelimited : (A.lexProd B hA hB).IsDelimited :=
  OrdSemigroup.withTop_isDelimited _

/-- Proposition 4.4 (M rule) of [Rétvári et al., *Compact policy routing*] for delimited routing algebras:
`M(A × B) ⇔ SM(A) ∨ (M(A) ∧ M(B))`, provided `B` has a finite weight. -/
theorem lexProd_isMonotone_iff (hB' : ∃ b, b ≠ B.phi) :
    (A.lexProd B hA hB).IsMonotone ↔ A.IsStrictlyMonotone ∨ (A.IsMonotone ∧ B.IsMonotone) := by
  have : Nonempty {b : V // b ≠ B.phi} := let ⟨b, hb⟩ := hB'; ⟨⟨b, hb⟩⟩
  rw [lexProd, OrdSemigroup.withTop_isMonotone_iff, OrdSemigroup.lex_isMonotone_iff,
    fin_isStrictlyMonotone_iff, fin_isMonotone_iff, fin_isMonotone_iff]

/-- Proposition 4.4 (SM rule) of [Rétvári et al., *Compact policy routing*] for delimited routing algebras:
`SM(A × B) ⇔ SM(A) ∨ (M(A) ∧ SM(B))`, provided `B` has a finite weight. -/
theorem lexProd_isStrictlyMonotone_iff (hB' : ∃ b, b ≠ B.phi) :
    (A.lexProd B hA hB).IsStrictlyMonotone ↔
      A.IsStrictlyMonotone ∨ (A.IsMonotone ∧ B.IsStrictlyMonotone) := by
  have : Nonempty {b : V // b ≠ B.phi} := let ⟨b, hb⟩ := hB'; ⟨⟨b, hb⟩⟩
  rw [lexProd, OrdSemigroup.withTop_isStrictlyMonotone_iff, OrdSemigroup.lex_isStrictlyMonotone_iff,
    fin_isStrictlyMonotone_iff, fin_isMonotone_iff, fin_isStrictlyMonotone_iff]

/-- Proposition 4.4 (I rule) of [Rétvári et al., *Compact policy routing*] for delimited routing algebras:
`I(A × B) ⇔ I(A) ∧ I(B) ∧ (N(A) ∨ C(B))`, provided `A` and `B` have finite weights. -/
theorem lexProd_isIsotone_iff (hA' : ∃ a, a ≠ A.phi) (hB' : ∃ b, b ≠ B.phi) :
    (A.lexProd B hA hB).IsIsotone ↔
      A.IsIsotone ∧ B.IsIsotone ∧ (A.IsCancellative ∨ B.IsCondensed) := by
  have : Nonempty {a : W // a ≠ A.phi} := let ⟨a, ha⟩ := hA'; ⟨⟨a, ha⟩⟩
  have : Nonempty {b : V // b ≠ B.phi} := let ⟨b, hb⟩ := hB'; ⟨⟨b, hb⟩⟩
  rw [lexProd, OrdSemigroup.withTop_isIsotone_iff, OrdSemigroup.lex_isIsotone_iff,
    fin_isIsotone_iff, fin_isIsotone_iff, fin_isCancellative_iff, fin_isCondensed_iff]

/-! ### The paper's literal product is degenerate -/

/-- The lexicographic product exactly as defined in Section 4.2: weights `W_A × W_B`, componentwise `⊕`,
lexicographic order, and `φ = (φ_A, φ_B)`. -/
def litProd (A : RoutingAlgebra W) (B : RoutingAlgebra V) : RoutingAlgebra (Lex (W × V)) where
  op x y := toLex (A.op (ofLex x).1 (ofLex y).1, B.op (ofLex x).2 (ofLex y).2)
  op_assoc x y z := by simp [A.op_assoc, B.op_assoc]
  op_comm x y := by simp [A.op_comm, B.op_comm]
  phi := toLex (A.phi, B.phi)
  op_phi x := by simp [A.op_phi, B.op_phi]
  le_phi x := Prod.Lex.toLex_le_toLex.2 <| by
    rcases (A.le_phi (ofLex x).1).lt_or_eq with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, B.le_phi _⟩

/-- The literal product of Section 4.2 is never delimited when `A` and `B` have finite weights:
`(φ_A, b) ⊕ (a, φ_B) = (φ_A, φ_B) = φ`. -/
theorem litProd_not_isDelimited {a : W} {b : V} (ha : a ≠ A.phi) (hb : b ≠ B.phi) :
    ¬ (A.litProd B).IsDelimited := fun h =>
  h (toLex (A.phi, b)) (toLex (a, B.phi)) (by simp [litProd, hb]) (by simp [litProd, ha])
    (by simp [litProd, A.phi_op, B.op_phi])

/-- The (M) rule of Proposition 4.4 fails for the literal product: if `B` is not monotone then `A × B` is not
monotone, whatever `A` is (e.g. strictly monotone): the weight `(φ_A, x)` is not monotone. -/
theorem litProd_not_isMonotone (hB : ¬ B.IsMonotone) : ¬ (A.litProd B).IsMonotone := by
  intro h
  apply hB
  intro x y
  have := h (toLex (A.phi, x)) (toLex (A.phi, y))
  simp only [litProd, ofLex_toLex, A.op_phi, Prod.Lex.toLex_le_toLex, lt_self_iff_false, true_and,
    false_or] at this
  exact this

end RoutingAlgebra

/-! ### Table 4.2 -/

namespace OrdSemigroup

/-- Costs `(ℤ⁺, +, ≤)` (finite part of shortest-path routing). -/
def cost : OrdSemigroup ℕ+ := ⟨(· + ·), add_assoc, add_comm⟩

/-- `(F, max, ≤)`: the bottleneck semigroup on a linear order. On `ℕ+ᵒᵈ` this is capacities `(ℤ⁺, min, ≥)`
(finite part of widest-path routing; larger capacity = preferred). -/
def maxSG (F : Type u) [LinearOrder F] : OrdSemigroup F := ⟨max, max_assoc, max_comm⟩

/-- Capacities `(ℤ⁺, min, ≥)`. -/
abbrev capacity : OrdSemigroup ℕ+ᵒᵈ := maxSG ℕ+ᵒᵈ

/-- The trivial semigroup `({1}, ∗)` (finite part of usable-path routing). -/
def unit : OrdSemigroup Unit := ⟨fun _ _ => (), fun _ _ _ => rfl, fun _ _ => rfl⟩

/-- Reliabilities `((0,1], ∗, ≥)` (finite part of most-reliable-path routing; larger = preferred). -/
def reliability : OrdSemigroup (Set.Ioc (0 : ℚ) 1)ᵒᵈ where
  op a b := toDual ⟨(ofDual a).1 * (ofDual b).1,
    mul_pos (ofDual a).2.1 (ofDual b).2.1, (mul_le_of_le_one_left (ofDual b).2.1.le (ofDual a).2.2).trans (ofDual b).2.2⟩
  op_assoc a b c := by simp [mul_assoc]
  op_comm a b := by simp [mul_comm]

/-- Reliabilities `((0,1), ∗, ≥)`, the strictly monotone subalgebra of `reliability` used in Section 4.3.2. -/
def reliabilityOpen : OrdSemigroup (Set.Ioo (0 : ℚ) 1)ᵒᵈ where
  op a b := toDual ⟨(ofDual a).1 * (ofDual b).1,
    mul_pos (ofDual a).2.1 (ofDual b).2.1, (mul_le_of_le_one_left (ofDual b).2.1.le
      (ofDual a).2.2.le).trans_lt (ofDual b).2.2⟩
  op_assoc a b c := by simp [mul_assoc]
  op_comm a b := by simp [mul_comm]

/-! #### Properties of the primitive semigroups -/

theorem cost_isStrictlyMonotone : cost.IsStrictlyMonotone := fun a b => by
  show a < b + a; exact PNat.lt_add_left a b

theorem cost_isIsotone : cost.IsIsotone := fun a b c h => by
  show c + a ≤ c + b; gcongr

theorem cost_isCancellative : cost.IsCancellative := fun a _ _ h => add_left_cancel (a := a) h

theorem cost_not_isCondensed : ¬ cost.IsCondensed := fun h => by
  have := h 1 1 2; simp [cost] at this

theorem cost_not_isSelective : ¬ cost.IsSelective := fun h => by
  rcases h 1 1 with h' | h' <;> exact absurd h' (by decide)

variable (F : Type u) [LinearOrder F]

theorem maxSG_isSelective : (maxSG F).IsSelective := fun a b => by
  rcases le_total a b with h | h
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left h)

theorem maxSG_isMonotone : (maxSG F).IsMonotone := fun a b => le_max_right b a

theorem maxSG_isIsotone : (maxSG F).IsIsotone := fun _ _ c h => max_le_max_left c h

theorem maxSG_not_isStrictlyMonotone [Nonempty F] : ¬ (maxSG F).IsStrictlyMonotone := fun h => by
  obtain ⟨a⟩ := ‹Nonempty F›
  exact lt_irrefl a (by simpa [maxSG] using h a a)

theorem capacity_not_isCancellative : ¬ capacity.IsCancellative := fun h => by
  have e : capacity.op (toDual (1 : ℕ+)) (toDual 1) = capacity.op (toDual 1) (toDual 2) := by
    show max _ _ = max _ _
    rw [max_self]; exact (max_eq_left (toDual_le_toDual.2 (by decide))).symm
  exact absurd (congrArg ofDual (h _ _ _ e)) (by decide)

theorem capacity_not_isCondensed : ¬ capacity.IsCondensed := fun h => by
  have := h (toDual (2 : ℕ+)) (toDual 1) (toDual 3)
  rw [show capacity.op (toDual (2 : ℕ+)) (toDual 1) = toDual 1 from
      max_eq_right (toDual_le_toDual.2 (by decide)),
    show capacity.op (toDual (2 : ℕ+)) (toDual 3) = toDual 2 from
      max_eq_left (toDual_le_toDual.2 (by decide))] at this
  exact absurd (congrArg ofDual this) (by decide)

theorem unit_isSelective : unit.IsSelective := fun _ _ => Or.inl rfl
theorem unit_isMonotone : unit.IsMonotone := fun _ _ => le_rfl
theorem unit_isIsotone : unit.IsIsotone := fun _ _ _ _ => le_rfl
theorem unit_isCancellative : unit.IsCancellative := fun _ _ _ _ => rfl
theorem unit_isCondensed : unit.IsCondensed := fun _ _ _ => rfl
theorem unit_not_isStrictlyMonotone : ¬ unit.IsStrictlyMonotone := fun h => lt_irrefl _ (h () ())

theorem reliability_isMonotone : reliability.IsMonotone := fun a b => by
  show (ofDual (reliability.op b a)).1 ≤ ofDual a
  exact mul_le_of_le_one_left (ofDual a).2.1.le (ofDual b).2.2

theorem reliability_isIsotone : reliability.IsIsotone := fun a b c h => by
  show (ofDual (reliability.op c b)).1 ≤ ofDual (reliability.op c a)
  exact mul_le_mul_of_nonneg_left (show (ofDual b).1 ≤ ofDual a from h) (ofDual c).2.1.le

theorem reliability_isCancellative : reliability.IsCancellative := fun a b c h => by
  have h' : (ofDual a).1 * ofDual b = (ofDual a).1 * ofDual c :=
    congrArg (fun x => (ofDual x).1) h
  exact ofDual.injective (Subtype.ext (mul_left_cancel₀ (ofDual a).2.1.ne' h'))

/-- `1 ∗ 1 = 1`: reliabilities in `(0,1]` are not strictly monotone. -/
theorem reliability_not_isStrictlyMonotone : ¬ reliability.IsStrictlyMonotone := fun h => by
  let one : (Set.Ioc (0 : ℚ) 1)ᵒᵈ := toDual ⟨1, by norm_num, le_rfl⟩
  have h' : reliability.op one one = one := congrArg toDual (Subtype.ext (one_mul (1 : ℚ)))
  have := h one one
  rw [h'] at this
  exact lt_irrefl one this

theorem reliabilityOpen_isStrictlyMonotone : reliabilityOpen.IsStrictlyMonotone := fun a b => by
  show (ofDual (reliabilityOpen.op b a)).1 < ofDual a
  exact mul_lt_of_lt_one_left (ofDual a).2.1 (ofDual b).2.2

end OrdSemigroup

open OrdSemigroup

/-- Shortest path `S = (ℤ⁺, ∞, +, ≤)` (Table 4.2). -/
def shortestPath : RoutingAlgebra (WithTop ℕ+) := cost.withTop

/-- Widest path `W = (ℤ⁺, 0, min, ≥)` (Table 4.2, with integer capacities): weights `ℕ+ᵒᵈ`, `φ = ⊤`
(capacity `0`). -/
def widestPath : RoutingAlgebra (WithTop ℕ+ᵒᵈ) := capacity.withTop

/-- Usable path `U = ({1}, 0, ∗, ≥)` (Table 4.2). -/
def usablePath : RoutingAlgebra (WithTop Unit) := unit.withTop

/-- Most reliable path `R = ((0,1], 0, ∗, ≥)` (Table 4.2, rational reliabilities). -/
def mostReliable : RoutingAlgebra (WithTop (Set.Ioc (0 : ℚ) 1)ᵒᵈ) := reliability.withTop

/-- The subalgebra `((0,1), 0, ∗, ≥)` of `R` (Section 4.3.2). -/
def mostReliableOpen : RoutingAlgebra (WithTop (Set.Ioo (0 : ℚ) 1)ᵒᵈ) := reliabilityOpen.withTop

/-- Widest-shortest path `WS = S × W` (Table 4.2). -/
def widestShortest : RoutingAlgebra (WithTop (Lex (ℕ+ × ℕ+ᵒᵈ))) := (cost.lex capacity).withTop

/-- Shortest-widest path `SW = W × S` (Table 4.2): weights `(capacity, cost)`, capacity first. -/
def shortestWidest : RoutingAlgebra (WithTop (Lex (ℕ+ᵒᵈ × ℕ+))) := (capacity.lex cost).withTop

/-- Most reliable widest-shortest path `MRWS = R × WS` (Table 4.2). -/
def mostReliableWS : RoutingAlgebra (WithTop (Lex ((Set.Ioc (0 : ℚ) 1)ᵒᵈ × Lex (ℕ+ × ℕ+ᵒᵈ)))) :=
  (reliability.lex (cost.lex capacity)).withTop

instance : Nonempty (Set.Ioc (0 : ℚ) 1)ᵒᵈ := ⟨toDual ⟨1, by norm_num, le_rfl⟩⟩

/-! #### Product properties via Proposition 4.4 (semigroup level) -/

theorem ws_isStrictlyMonotone : (cost.lex capacity).IsStrictlyMonotone :=
  lex_isStrictlyMonotone_iff.2 (Or.inl cost_isStrictlyMonotone)

theorem ws_isIsotone : (cost.lex capacity).IsIsotone :=
  lex_isIsotone_iff.2 ⟨cost_isIsotone, maxSG_isIsotone _, Or.inl cost_isCancellative⟩

theorem sw_isStrictlyMonotone : (capacity.lex cost).IsStrictlyMonotone :=
  lex_isStrictlyMonotone_iff.2 (Or.inr ⟨maxSG_isMonotone _, cost_isStrictlyMonotone⟩)

theorem sw_not_isIsotone : ¬ (capacity.lex cost).IsIsotone := fun h => by
  obtain ⟨-, -, h | h⟩ := lex_isIsotone_iff.1 h
  · exact capacity_not_isCancellative h
  · exact cost_not_isCondensed h

theorem mrws_isStrictlyMonotone : (reliability.lex (cost.lex capacity)).IsStrictlyMonotone :=
  lex_isStrictlyMonotone_iff.2 (Or.inr ⟨reliability_isMonotone, ws_isStrictlyMonotone⟩)

theorem mrws_isIsotone : (reliability.lex (cost.lex capacity)).IsIsotone :=
  lex_isIsotone_iff.2 ⟨reliability_isIsotone, ws_isIsotone, Or.inl reliability_isCancellative⟩

/-! #### The "Properties" column of Table 4.2 -/

/-- Table 4.2, row S: delimited, `SM`, `I`. -/
theorem shortestPath_props : shortestPath.IsDelimited ∧ shortestPath.IsStrictlyMonotone ∧
    shortestPath.IsIsotone :=
  ⟨withTop_isDelimited _, (withTop_isStrictlyMonotone_iff _).2 cost_isStrictlyMonotone,
    (withTop_isIsotone_iff _).2 cost_isIsotone⟩

/-- Table 4.2, row W: delimited, `S`, `I`, `M` (and not `SM`). -/
theorem widestPath_props : widestPath.IsDelimited ∧ widestPath.IsSelective ∧ widestPath.IsIsotone ∧
    widestPath.IsMonotone ∧ ¬ widestPath.IsStrictlyMonotone :=
  ⟨withTop_isDelimited _, (withTop_isSelective_iff _).2 (maxSG_isSelective _),
    (withTop_isIsotone_iff _).2 (maxSG_isIsotone _), (withTop_isMonotone_iff _).2 (maxSG_isMonotone _),
    fun h => maxSG_not_isStrictlyMonotone _ ((withTop_isStrictlyMonotone_iff _).1 h)⟩

/-- Table 4.2, row U: delimited, `S`, `I`, `M` (and not `SM`). -/
theorem usablePath_props : usablePath.IsDelimited ∧ usablePath.IsSelective ∧ usablePath.IsIsotone ∧
    usablePath.IsMonotone ∧ ¬ usablePath.IsStrictlyMonotone :=
  ⟨withTop_isDelimited _, (withTop_isSelective_iff _).2 unit_isSelective,
    (withTop_isIsotone_iff _).2 unit_isIsotone, (withTop_isMonotone_iff _).2 unit_isMonotone,
    fun h => unit_not_isStrictlyMonotone ((withTop_isStrictlyMonotone_iff _).1 h)⟩

/-- Table 4.2, row R: delimited, `I`, `M`, `N` — but **not** `SM` as the table claims (`1 ∗ 1 = 1`). -/
theorem mostReliable_props : mostReliable.IsDelimited ∧ mostReliable.IsIsotone ∧
    mostReliable.IsMonotone ∧ mostReliable.IsCancellative :=
  ⟨withTop_isDelimited _, (withTop_isIsotone_iff _).2 reliability_isIsotone,
    (withTop_isMonotone_iff _).2 reliability_isMonotone,
    (withTop_isCancellative_iff _).2 reliability_isCancellative⟩

/-- Table 4.2 lists `R = ((0,1], 0, ∗, ≥)` as strictly monotone; it is not: `1 ∗ 1 = 1`. -/
theorem mostReliable_not_isStrictlyMonotone : ¬ mostReliable.IsStrictlyMonotone := fun h =>
  reliability_not_isStrictlyMonotone ((withTop_isStrictlyMonotone_iff _).1 h)

/-- Section 4.3.2: the subalgebra `((0,1), 0, ∗, ≥)` of `R` is delimited and strictly monotone. -/
theorem mostReliableOpen_props : mostReliableOpen.IsDelimited ∧ mostReliableOpen.IsStrictlyMonotone :=
  ⟨withTop_isDelimited _, (withTop_isStrictlyMonotone_iff _).2 reliabilityOpen_isStrictlyMonotone⟩

/-- Table 4.2, row WS: delimited, `SM`, `I` (by Proposition 4.4). -/
theorem widestShortest_props : widestShortest.IsDelimited ∧ widestShortest.IsStrictlyMonotone ∧
    widestShortest.IsIsotone :=
  ⟨withTop_isDelimited _, (withTop_isStrictlyMonotone_iff _).2 ws_isStrictlyMonotone,
    (withTop_isIsotone_iff _).2 ws_isIsotone⟩

/-- Table 4.2, row SW: delimited, `M`, `SM`, `¬I` (by Proposition 4.4). -/
theorem shortestWidest_props : shortestWidest.IsDelimited ∧ shortestWidest.IsMonotone ∧
    shortestWidest.IsStrictlyMonotone ∧ ¬ shortestWidest.IsIsotone :=
  ⟨withTop_isDelimited _, (withTop_isMonotone_iff _).2 sw_isStrictlyMonotone.isMonotone,
    (withTop_isStrictlyMonotone_iff _).2 sw_isStrictlyMonotone,
    fun h => sw_not_isIsotone ((withTop_isIsotone_iff _).1 h)⟩

/-- Table 4.2, row MRWS: delimited and `SM` as listed (by Proposition 4.4, via `M(R) ∧ SM(WS)`). -/
theorem mostReliableWS_props : mostReliableWS.IsDelimited ∧ mostReliableWS.IsStrictlyMonotone :=
  ⟨withTop_isDelimited _, (withTop_isStrictlyMonotone_iff _).2 mrws_isStrictlyMonotone⟩

/-- Table 4.2 lists `MRWS = R × WS` as non-isotone (`¬I`); by Proposition 4.4 it **is** isotone, since `R` is
isotone and cancellative and `WS` is isotone. -/
theorem mostReliableWS_isIsotone : mostReliableWS.IsIsotone :=
  (withTop_isIsotone_iff _).2 mrws_isIsotone

/-- Non-vacuity of the routing-algebra form of Proposition 4.4: `W × S` built with `lexProd` from the routing
algebras `widestPath` and `shortestPath` is strictly monotone and not isotone. -/
example : (widestPath.lexProd shortestPath widestPath_props.1 shortestPath_props.1).IsStrictlyMonotone ∧
    ¬ (widestPath.lexProd shortestPath widestPath_props.1 shortestPath_props.1).IsIsotone := by
  have hW : ∃ a, a ≠ widestPath.phi := ⟨((toDual (1 : ℕ+) : ℕ+ᵒᵈ) : WithTop ℕ+ᵒᵈ), WithTop.coe_ne_top⟩
  have hS : ∃ a, a ≠ shortestPath.phi := ⟨((1 : ℕ+) : WithTop ℕ+), WithTop.coe_ne_top⟩
  rw [RoutingAlgebra.lexProd_isStrictlyMonotone_iff _ _ _ _ hS,
    RoutingAlgebra.lexProd_isIsotone_iff _ _ _ _ hW hS]
  refine ⟨Or.inr ⟨widestPath_props.2.2.2.1, shortestPath_props.2.1⟩, ?_⟩
  rintro ⟨-, -, h | h⟩
  · exact capacity_not_isCancellative ((withTop_isCancellative_iff _).1 h)
  · exact cost_not_isCondensed ((withTop_isCondensed_iff _).1 h)

/-! ### Condition (4.2) of Theorem 4.17 -/

/-- A shortest-widest-path weight `(capacity b, cost c)`. -/
def swWeight (b c : ℕ+) : WithTop (Lex (ℕ+ᵒᵈ × ℕ+)) := ((toLex (toDual b, c) : Lex (ℕ+ᵒᵈ × ℕ+)) : WithTop _)

theorem shortestWidest_op_swWeight (b c b' c' : ℕ+) :
    shortestWidest.op (swWeight b c) (swWeight b' c') = swWeight (min b b') (c + c') := rfl

theorem shortestWidest_spow_swWeight (b c : ℕ+) (m : ℕ) :
    shortestWidest.spow (swWeight b c) m = swWeight b (m.succPNat * c) := by
  induction m with
  | zero => simp only [RoutingAlgebra.spow]; congr 1; apply PNat.eq; simp
  | succ m ih =>
    rw [RoutingAlgebra.spow, ih, shortestWidest_op_swWeight, min_self]
    congr 1
    apply PNat.eq
    simp only [PNat.add_coe, PNat.mul_coe, Nat.succPNat_coe, Nat.succ_eq_add_one]
    ring

theorem swWeight_lt_swWeight {b c b' c' : ℕ+} :
    swWeight b c < swWeight b' c' ↔ b' < b ∨ b = b' ∧ c < c' := by
  simp [swWeight, Prod.Lex.toLex_lt_toLex]

/-- Theorem 4.17, condition (4.2), for shortest-widest path (end of Section 4.4.2): for `k ≥ 1` and any `p`, the
weights `wᵢ = (bᵢ, cᵢ)` with capacity `bᵢ = i` and cost `cᵢ = (2k)^(i-1)` satisfy `wᵢ ⊕ wⱼ ≻ wᵢ^(2k)` for all
`i ≠ j` (the second inequality `wᵢ ⊕ wⱼ ≻ wⱼ^(2k)` of (4.2) is the instance `(j, i)`). Indices are `0`-based. -/
theorem shortestWidest_condition_4_2 (k : ℕ) (hk : 1 ≤ k) (p : ℕ) :
    ∃ w : Fin p → WithTop (Lex (ℕ+ᵒᵈ × ℕ+)), (∀ i, w i ≠ shortestWidest.phi) ∧
      ∀ i j, i ≠ j →
        shortestWidest.emb (w i) ^ (2 * k) < shortestWidest.emb (shortestWidest.op (w i) (w j)) := by
  let K : ℕ+ := ⟨2 * k, by omega⟩
  refine ⟨fun i => swWeight (Nat.succPNat i) (K ^ (i : ℕ)), fun i => WithTop.coe_ne_top,
    fun i j hij => ?_⟩
  have hpos : ∀ n : ℕ, 0 < (2 * k) ^ n := fun n => pow_pos (by omega) n
  obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 1 := ⟨2 * k - 1, by omega⟩
  have e : ∀ x : shortestWidest.Ext, x ^ (2 * k) = x ^ (m + 1) := fun x => by rw [hm]
  rw [e, RoutingAlgebra.emb_pow_succ, RoutingAlgebra.emb_lt_emb, shortestWidest_spow_swWeight,
    shortestWidest_op_swWeight, swWeight_lt_swWeight]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · right
    refine ⟨(min_eq_left (by simpa using h.le)).symm, ?_⟩
    rw [← PNat.coe_lt_coe]
    have hK : ∀ n : ℕ, ((K ^ n : ℕ+) : ℕ) = (2 * k) ^ n := fun n => by rw [PNat.pow_coe]; rfl
    simp only [PNat.add_coe, PNat.mul_coe, Nat.succPNat_coe, hK, Nat.succ_eq_add_one, ← hm]
    have h1 : (2 * k) ^ ((i : ℕ) + 1) ≤ (2 * k) ^ (j : ℕ) := Nat.pow_le_pow_right (by omega) h
    rw [pow_succ] at h1
    have := hpos i
    nlinarith
  · left
    rw [min_eq_right (by simpa using h.le)]
    simpa using h

/-- Remark after Theorem 4.17: condition (4.2) is incompatible with regularity — in a monotone isotone algebra no
two finite weights `w₁ ≠ w₂`-indexed satisfy (4.2), for any `k ≥ 1` (the text says "for `k ≥ 2`"). -/
theorem not_condition_4_2_of_regular {W : Type u} [LinearOrder W] {A : RoutingAlgebra W}
    (hR : A.IsRegular) (k : ℕ) (hk : 1 ≤ k) (p : ℕ) (hp : 2 ≤ p) :
    ¬ ∃ w : Fin p → W, (∀ i, w i ≠ A.phi) ∧
      ∀ i j, i ≠ j → A.emb (w i) ^ (2 * k) < A.emb (A.op (w i) (w j)) := by
  rintro ⟨w, -, hw⟩
  -- the key inequality: if `w j ⪯ w i` then `w i ⊕ w j ⪯ w i ⊕ w i ⪯ w i ^ (2k)`
  have key : ∀ i j, w j ≤ w i → A.emb (A.op (w i) (w j)) ≤ A.emb (w i) ^ (2 * k) := by
    intro i j hji
    have h1 : A.emb (A.op (w i) (w j)) ≤ A.emb (w i) ^ 2 := by
      rw [sq, RoutingAlgebra.emb_mul_emb, RoutingAlgebra.emb_le_emb]
      exact hR.2 _ _ _ hji
    have h2 : A.emb (w i) ^ 2 ≤ A.emb (w i) ^ (2 * k) := by
      obtain ⟨m, hm⟩ : ∃ m, 2 * k = m + 2 := ⟨2 * k - 2, by omega⟩
      rw [hm, pow_add]
      exact hR.1.le_mul _ _
    exact h1.trans h2
  let i₀ : Fin p := ⟨0, by omega⟩
  let i₁ : Fin p := ⟨1, by omega⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  rcases le_total (w i₁) (w i₀) with h | h
  · exact absurd (key i₀ i₁ h) (not_le.2 (hw i₀ i₁ hne))
  · exact absurd (key i₁ i₀ h) (not_le.2 (hw i₁ i₀ hne.symm))

end Podc.CompactPolicyRouting
