import Papers.PODC2018.PPNaming.Model

/-!
# Proposition 13: symmetric self-stabilizing naming with `P + 1` states under global fairness

Burman, Beauquier, Sohier, *Space-Optimal Naming in Population Protocols*, Proposition 13 and
its proof in the appendix.

States `Fin (P + 1)`; the state `P` (`Fin.last P`) is special. Rules (`s ≠ P`):
1. `(s, P) → (s, (s + 1) mod P)` and symmetrically `(P, s) → ((s + 1) mod P, s)`;
2. `(s, s) → (P, P)`;
3. `(P, P) → (1, 1)`;
all other interactions are null.

* `prop13_isSymmetric`: the protocol is symmetric.
* `prop13_solvesGlobal`: for `3 ≤ n ≤ P`, from every configuration, every globally fair execution
  solves naming. Proof as in the paper: from every configuration a configuration in which all
  agents hold distinct states `≠ P` (silent) is reachable (`prop13_reach_final`).
* `not_solvesGlobal_of_card_two`, `not_solvesWeak_of_card_two`: the remark that `n > 2` is
  needed. For *every* symmetric protocol without leader and two agents, uniform configurations
  stay uniform, so naming fails from a uniform configuration (in particular without
  initialization).
-/

namespace Podc.PPNaming

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol

-- CSLib candidate (`Function.update` form of CSLib's `Protocol.interact_eq_upd`, which lives in
-- `Nondet.lean`; would belong next to `Protocol.interact` in `PopulationProtocols/Basic.lean`)
lemma interact_eq_update {Q Ag : Type*} [DecidableEq Ag] (Pr : Protocol Q) (C : Config Ag Q)
    {a b : Ag} (hab : a ≠ b) :
    Pr.interact C a b = Function.update (Function.update C a (Pr.δ (C a) (C b)).1) b
      (Pr.δ (C a) (C b)).2 := by
  funext x
  by_cases hxb : x = b
  · subst hxb; simp [Protocol.interact, Ne.symm hab]
  · by_cases hxa : x = a
    · subst hxa; simp [Protocol.interact, hxb]
    · simp [Protocol.interact, hxa, hxb]

variable {P : ℕ}

/-- `(s + 1) mod P`, for a state `s < P`. -/
def nxt13 (P : ℕ) (s : Fin (P + 1)) : Fin (P + 1) :=
  if h : s.val + 1 < P then ⟨s.val + 1, by omega⟩ else 0

/-- The transition function of Proposition 13. -/
def prop13δ (P : ℕ) (x y : Fin (P + 1)) : Fin (P + 1) × Fin (P + 1) :=
  if x = Fin.last P then
    if y = Fin.last P then (1, 1) else (nxt13 P y, y)
  else if y = Fin.last P then (x, nxt13 P x)
  else if x = y then (Fin.last P, Fin.last P) else (x, y)

/-- The symmetric protocol of Proposition 13, with `P + 1` states. -/
def prop13Protocol (P : ℕ) : Protocol (Fin (P + 1)) where
  δ := prop13δ P

/-- The protocol of Proposition 13 is symmetric. -/
theorem prop13_isSymmetric : IsSymmetric (prop13Protocol P) := by
  intro p q
  simp only [prop13Protocol, prop13δ]
  by_cases hpq : p = q
  · subst hpq; by_cases hp : p = Fin.last P <;> simp [hp]
  · by_cases hp : p = Fin.last P <;> by_cases hq : q = Fin.last P <;>
      simp [hp, hq, hpq, Ne.symm hpq]

lemma nxt13_val (s : Fin (P + 1)) (hs : s ≠ Fin.last P) : (nxt13 P s).val = (s.val + 1) % P := by
  have hlt : s.val < P := Fin.val_lt_last hs
  unfold nxt13
  split_ifs with h
  · simp [Nat.mod_eq_of_lt h]
  · have : s.val + 1 = P := by omega
    simp [this]

lemma nxt13_ne_last (hP : 1 ≤ P) (s : Fin (P + 1)) : nxt13 P s ≠ Fin.last P := by
  intro h
  have := congrArg Fin.val h
  unfold nxt13 at this
  split_ifs at this with h' <;> simp at this <;> omega

lemma ne_last_iff_val_lt (s : Fin (P + 1)) : s ≠ Fin.last P ↔ s.val < P := by
  constructor
  · exact Fin.val_lt_last
  · intro h h'; rw [h'] at h; simp at h

section

variable {A : Type*} [DecidableEq A] [Fintype A]

/-- The only homonyms are in the special state `P`. -/
def GoodIsh (C : Config A (Fin (P + 1))) : Prop :=
  ∀ a b, C a = C b → C a ≠ Fin.last P → a = b

/-- The final configurations: all agents hold distinct states different from `P`. -/
def Final13 (C : Config A (Fin (P + 1))) : Prop :=
  Function.Injective C ∧ ∀ a, C a ≠ Fin.last P

omit [Fintype A] in
lemma final13_silent {C : Config A (Fin (P + 1))} (hC : Final13 C) {a b : A} (hab : a ≠ b) :
    (prop13Protocol P).interact C a b = C := by
  have hδ : (prop13Protocol P).δ (C a) (C b) = (C a, C b) := by
    have hne : C a ≠ C b := fun h => hab (hC.1 h)
    simp [prop13Protocol, prop13δ, hC.2 a, hC.2 b, hne]
  rw [interact_eq_update _ _ hab, hδ]
  simp

omit [Fintype A] in
lemma final13_stablyNamed {C : Config A (Fin (P + 1))} (hC : Final13 C) :
    StablyNamed (prop13Protocol P) (nameOut id) C := by
  refine ⟨hC.1, fun D hD => ?_⟩
  have : D = C := by
    induction hD with
    | refl => rfl
    | tail _ hst ih =>
      obtain ⟨a, b, hab, rfl⟩ := hst
      subst ih
      exact final13_silent hC hab
  rw [this]

/-- Rule 2 applied repeatedly: a configuration whose only homonyms are in state `P` is
reachable. -/
lemma prop13_reach_goodIsh (C : Config A (Fin (P + 1))) :
    ∃ D, (prop13Protocol P).Reachable C D ∧ GoodIsh D := by
  induction hV : (Finset.univ.filter fun x => C x ≠ Fin.last P).card
    using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases hg : GoodIsh C
    · exact ⟨C, .refl, hg⟩
    · simp only [GoodIsh, not_forall] at hg
      obtain ⟨a, b, heq, hne, hab⟩ := hg
      set C' := (prop13Protocol P).interact C a b
      have hC' : C' = Function.update (Function.update C a (Fin.last P)) b (Fin.last P) := by
        simp only [C']; rw [interact_eq_update _ _ hab]
        have hne' : C b ≠ Fin.last P := heq ▸ hne
        simp [prop13Protocol, prop13δ, heq, hne']
      have hlt : (Finset.univ.filter fun x => C' x ≠ Fin.last P).card <
          (Finset.univ.filter fun x => C x ≠ Fin.last P).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨a, by simp [hne], by simp [hC', hab]⟩
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hC'] at hx ⊢
          by_cases hxb : x = b
          · subst hxb; simp at hx
          · by_cases hxa : x = a
            · subst hxa; simp [hxb] at hx
            · simpa [hxa, hxb] using hx
      obtain ⟨D, hD, hDg⟩ := ih _ (hV ▸ hlt) C' rfl
      exact ⟨D, Relation.ReflTransGen.head ⟨a, b, hab, rfl⟩ hD, hDg⟩

omit [DecidableEq A] in
/-- In a configuration with an agent in state `P` and `n ≤ P` agents, some present state
`s ≠ P` has its successor `(s + 1) mod P` absent. -/
lemma exists_free_succ (hAP : Fintype.card A ≤ P) {C : Config A (Fin (P + 1))}
    {z : A} (hz : C z = Fin.last P) {a₀ : A} (ha₀ : C a₀ ≠ Fin.last P) :
    ∃ a, C a ≠ Fin.last P ∧ ∀ x, C x ≠ nxt13 P (C a) := by
  by_contra hno
  push Not at hno
  have hP : 1 ≤ P := by have := (ne_last_iff_val_lt _).1 ha₀; omega
  -- the present states `≠ P` are closed under `+1 mod P`, hence all of them are present
  have hcl : ∀ j, ∃ x, C x ≠ Fin.last P ∧ (C x).val = ((C a₀).val + j) % P := by
    intro j
    induction j with
    | zero =>
      exact ⟨a₀, ha₀, by simp only [Nat.add_zero]; exact (Nat.mod_eq_of_lt ((ne_last_iff_val_lt _).1 ha₀)).symm⟩
    | succ j ih =>
      obtain ⟨x, hx, hxv⟩ := ih
      obtain ⟨y, hy⟩ := hno x hx
      refine ⟨y, hy ▸ nxt13_ne_last hP _, ?_⟩
      rw [hy, nxt13_val _ hx, hxv, Nat.mod_add_mod, Nat.add_assoc]
  have hall : ∀ v : Fin P, ∃ x, (C x).val = v.val := by
    intro v
    obtain ⟨x, -, hx⟩ := hcl (v.val + P - (C a₀).val)
    have hlt := (ne_last_iff_val_lt _).1 ha₀
    refine ⟨x, ?_⟩
    rw [hx, show (C a₀).val + (v.val + P - (C a₀).val) = v.val + P by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt v.isLt]
  choose g hg' using hall
  let f : Option (Fin P) → A := fun o => o.elim z g
  have hf : Function.Injective f := by
    intro o o' h
    rcases o with _ | v <;> rcases o' with _ | v'
    · rfl
    · have := hg' v'; simp only [f, Option.elim] at h; rw [← h, hz] at this; simp at this; omega
    · have := hg' v; simp only [f, Option.elim] at h; rw [h, hz] at this; simp at this; omega
    · simp only [f, Option.elim] at h
      have h1 := hg' v; have h2 := hg' v'
      rw [h] at h1; rw [h1] at h2
      exact congrArg some (Fin.ext h2)
  have := Fintype.card_le_of_injective f hf
  simp at this
  omega

/-- Rule 1 applied repeatedly: from a configuration whose only homonyms are in state `P` and
with some agent not in state `P`, a final configuration is reachable. -/
lemma prop13_reach_final_of_goodIsh (hAP : Fintype.card A ≤ P) (C : Config A (Fin (P + 1)))
    (hg : GoodIsh C) {a₀ : A} (ha₀ : C a₀ ≠ Fin.last P) :
    ∃ D, (prop13Protocol P).Reachable C D ∧ Final13 D := by
  induction hV : (Finset.univ.filter fun x => C x = Fin.last P).card
    using Nat.strong_induction_on generalizing C a₀ with
  | _ n ih =>
    by_cases hz : ∃ z, C z = Fin.last P
    · obtain ⟨z, hz⟩ := hz
      have hP : 1 ≤ P := by have := (ne_last_iff_val_lt _).1 ha₀; omega
      obtain ⟨a, ha, hfree⟩ := exists_free_succ hAP hz ha₀
      have haz : a ≠ z := fun h => ha (h ▸ hz)
      set C' := (prop13Protocol P).interact C a z
      have hC' : C' = Function.update C z (nxt13 P (C a)) := by
        simp only [C']; rw [interact_eq_update _ _ haz]
        simp [prop13Protocol, prop13δ, ha, hz]
      have hg' : GoodIsh C' := by
        intro x y hxy hx
        rw [hC'] at hxy hx
        by_cases hxz : x = z
        · subst hxz
          by_cases hyz : y = x
          · exact hyz.symm
          · simp [hyz] at hxy; exact absurd hxy.symm (hfree y)
        · by_cases hyz : y = z
          · subst hyz; simp [hxz] at hxy; exact absurd hxy (hfree x)
          · simp only [Function.update_of_ne hxz, Function.update_of_ne hyz] at hxy hx
            exact hg x y hxy hx
      have ha₀' : C' a ≠ Fin.last P := by rw [hC', Function.update_of_ne haz]; exact ha
      have hlt : (Finset.univ.filter fun x => C' x = Fin.last P).card <
          (Finset.univ.filter fun x => C x = Fin.last P).card := by
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨z, by simp [hz], by simp [hC', nxt13_ne_last hP]⟩
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, hC'] at hx ⊢
          by_cases hxz : x = z
          · subst hxz; simp [nxt13_ne_last hP] at hx
          · simpa [hxz] using hx
      obtain ⟨D, hD, hDf⟩ := ih _ (hV ▸ hlt) C' hg' ha₀' rfl
      exact ⟨D, Relation.ReflTransGen.head ⟨a, z, haz, rfl⟩ hD, hDf⟩
    · push Not at hz
      exact ⟨C, .refl, fun x y hxy => hg x y hxy (hz x), hz⟩

omit [Fintype A] in
/-- Rules 3, 1, 2 on three agents `x, y, z` all in state `P`. -/
lemma prop13_reach_from_all_last (hP : 2 ≤ P) {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) :
    (prop13Protocol P).Reachable (fun _ => Fin.last P)
      (Function.update (fun _ => Fin.last P) z (nxt13 P 1)) := by
  have h1 : (1 : Fin (P + 1)) ≠ Fin.last P := by
    rw [ne_last_iff_val_lt, Fin.val_one', Nat.mod_eq_of_lt (by omega)]; omega
  set C₀ : Config A (Fin (P + 1)) := fun _ => Fin.last P
  set C₁ := Function.update (Function.update C₀ x 1) y 1
  set C₂ := Function.update C₁ z (nxt13 P 1)
  have s1 : (prop13Protocol P).interact C₀ x y = C₁ := by
    rw [interact_eq_update _ _ hxy]; simp [C₀, C₁, prop13Protocol, prop13δ]
  have s2 : (prop13Protocol P).interact C₁ y z = C₂ := by
    rw [interact_eq_update _ _ hyz]
    have hz1 : C₁ z = Fin.last P := by simp [C₁, C₀, Ne.symm hxz, Ne.symm hyz]
    have hy1 : C₁ y = 1 := by simp [C₁]
    rw [hz1, hy1]
    simp only [prop13Protocol, prop13δ, h1, ↓reduceIte]
    simp only [C₂]; congr 1; exact Function.update_eq_self_iff.2 hy1.symm
  have s3 : (prop13Protocol P).interact C₂ x y = Function.update C₀ z (nxt13 P 1) := by
    rw [interact_eq_update _ _ hxy]
    have hx2 : C₂ x = 1 := by simp [C₂, C₁, hxz, hxy]
    have hy2 : C₂ y = 1 := by simp [C₂, C₁, hyz]
    rw [hx2, hy2]
    simp only [prop13Protocol, prop13δ, h1, ↓reduceIte]
    funext w
    by_cases hwy : w = y
    · subst hwy; simp [hyz, C₀]
    · by_cases hwx : w = x
      · subst hwx; simp [hxz, C₀, hwy]
      · by_cases hwz : w = z
        · subst hwz; simp [C₂, hwx, hwy]
        · simp [C₂, C₁, C₀, hwx, hwy, hwz]
  rw [← s3, ← s2, ← s1]
  exact (((Relation.ReflTransGen.single ⟨x, y, hxy, rfl⟩).tail ⟨y, z, hyz, rfl⟩).tail
    ⟨x, y, hxy, rfl⟩)

/-- From every configuration of `3 ≤ n ≤ P` agents a final configuration is reachable. -/
lemma prop13_reach_final (hA3 : 3 ≤ Fintype.card A) (hAP : Fintype.card A ≤ P)
    (C : Config A (Fin (P + 1))) : ∃ D, (prop13Protocol P).Reachable C D ∧ Final13 D := by
  obtain ⟨C', hC', hg⟩ := prop13_reach_goodIsh C
  by_cases hex : ∃ a, C' a ≠ Fin.last P
  · obtain ⟨a, ha⟩ := hex
    obtain ⟨D, hD, hDf⟩ := prop13_reach_final_of_goodIsh hAP C' hg ha
    exact ⟨D, hC'.trans hD, hDf⟩
  · push Not at hex
    have hC'eq : C' = fun _ => Fin.last P := funext hex
    obtain ⟨x, y, z, hxy, hxz, hyz⟩ : ∃ x y z : A, x ≠ y ∧ x ≠ z ∧ y ≠ z := by
      obtain ⟨s, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset A)) hA3
      obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := Finset.card_eq_three.1 hs.2
      exact ⟨x, y, z, hxy, hxz, hyz⟩
    have hP : 1 ≤ P := by omega
    set C'' := Function.update (fun _ : A => Fin.last P) z (nxt13 P 1)
    have hR := prop13_reach_from_all_last (P := P) (by omega) hxy hxz hyz
    have hg'' : GoodIsh C'' := by
      intro u v huv hu
      by_cases huz : u = z
      · by_cases hvz : v = z
        · rw [huz, hvz]
        · simp [C'', huz, hvz] at huv; exact absurd huv (nxt13_ne_last hP _)
      · simp [C'', huz] at hu
    obtain ⟨D, hD, hDf⟩ := prop13_reach_final_of_goodIsh hAP C'' hg''
      (a₀ := z) (by simp [C'', nxt13_ne_last hP])
    exact ⟨D, hC'.trans (hC'eq ▸ hR.trans hD), hDf⟩

end

/-- **Proposition 13** of [Burman–Beauquier–Sohier]. Without leader and without initialization
(from every configuration), the symmetric protocol `prop13Protocol P` with `P + 1` states solves
naming under global fairness for every population of size `n` with `3 ≤ n ≤ P`. -/
theorem prop13_solvesGlobal (A : Type*) [Fintype A] [DecidableEq A]
    (hA3 : 3 ≤ Fintype.card A) (hAP : Fintype.card A ≤ P) :
    SolvesGlobal (prop13Protocol P) (Set.univ : Set (Config A (Fin (P + 1)))) (nameOut id) := by
  intro E hE0 hE
  refine stabilizes_of_globallyFair (fun _ _ C _ => ?_) E hE0 hE
  obtain ⟨D, hD, hDf⟩ := prop13_reach_final hA3 hAP C
  exact ⟨D, hD, final13_stablyNamed hDf⟩

/-! ### `n > 2` is necessary -/

section Two

variable {Q A N : Type*} [Fintype A] [DecidableEq A]

lemma eq_or_eq_of_card_two (hA : Fintype.card A = 2) {u v : A} (huv : u ≠ v) (w : A) :
    w = u ∨ w = v := by
  by_contra h
  push Not at h
  have : ({u, v, w} : Finset A).card = 3 := by
    rw [Finset.card_eq_three]; exact ⟨u, v, w, huv, Ne.symm h.1, Ne.symm h.2, rfl⟩
  have := Finset.card_le_univ ({u, v, w} : Finset A)
  omega

/-- With two agents, a symmetric protocol keeps uniform configurations uniform. -/
lemma uniform_closed (Pr : Protocol Q) (hP : IsSymmetric Pr) (hA : Fintype.card A = 2) :
    Pr.Closed (fun C : Config A Q => ∃ q, C = fun _ => q) := by
  rintro C C' ⟨q, rfl⟩ ⟨u, v, huv, rfl⟩
  refine ⟨(Pr.δ q q).1, funext fun w => ?_⟩
  rcases eq_or_eq_of_card_two hA huv w with rfl | rfl
  · simp
  · rw [Pr.interact_self_right _ huv]; exact hP.diag q

lemma not_stablyNamed_uniform (Pr : Protocol Q) (hP : IsSymmetric Pr) (hA : Fintype.card A = 2)
    (name : Q → N) (q₀ : Q) {D : Config A Q} (hD : Pr.Reachable (fun _ => q₀) D) :
    ¬ StablyNamed Pr (nameOut name) D := by
  obtain ⟨q, rfl⟩ := (uniform_closed Pr hP hA).reachable ⟨q₀, rfl⟩ hD
  intro h
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card A)
  exact huv (h.1 rfl)

/-- Remark after **Proposition 13** of [Burman–Beauquier–Sohier] (global fairness): with `n = 2`
agents, no symmetric protocol without leader solves naming under global fairness from a uniform
initial configuration. -/
theorem not_solvesGlobal_of_card_two [Finite Q] (Pr : Protocol Q) (hP : IsSymmetric Pr)
    (hA : Fintype.card A = 2) (name : Q → N) (q₀ : Q) :
    ¬ SolvesGlobal Pr {fun _ : A => q₀} (nameOut name) := by
  intro h
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card A)
  obtain ⟨D, hD, hDs⟩ := exists_stablyGood_of_globallyFair huv h rfl .refl
  exact not_stablyNamed_uniform Pr hP hA name q₀ hD hDs

/-- Remark after **Proposition 13** of [Burman–Beauquier–Sohier] (weak fairness): with `n = 2`
agents, no symmetric protocol without leader solves naming under weak fairness from a uniform
initial configuration. -/
theorem not_solvesWeak_of_card_two (Pr : Protocol Q) (hP : IsSymmetric Pr)
    (hA : Fintype.card A = 2) (name : Q → N) (q₀ : Q) :
    ¬ SolvesWeak Pr {fun _ : A => q₀} (nameOut name) := by
  intro h
  obtain ⟨u, v, huv⟩ := Fintype.one_lt_card_iff.1 (by omega : 1 < Fintype.card A)
  obtain ⟨D, hD, hDs⟩ := exists_stablyGood_of_weaklyFair huv h rfl .refl
  exact not_stablyNamed_uniform Pr hP hA name q₀ hD hDs

/-- In particular, for `n = 2`, symmetric self-stabilizing naming without leader is impossible
under global fairness. -/
theorem not_solvesGlobal_univ_of_card_two [Finite Q] [Nonempty Q] (Pr : Protocol Q)
    (hP : IsSymmetric Pr) (hA : Fintype.card A = 2) (name : Q → N) :
    ¬ SolvesGlobal Pr (Set.univ : Set (Config A Q)) (nameOut name) := fun h =>
  not_solvesGlobal_of_card_two Pr hP hA name (Classical.arbitrary Q)
    fun E _ hE => h E trivial hE

end Two

end Podc.PPNaming
