import Papers.PODC2018.CausalRecordReplay.Model

/-!
# Lemma C.5: completing partial orders to strongly causal views

R. L. Jones, M. S. Khan, N. H. Vaidya. *Optimal Record and Replay under Causal Consistency.*
PODC 2018; full version arXiv:1805.08804v2, Appendix C.

Definition C.4 extends the strong causal order to a family of partial orders `U = {U_m}`:
`(w₁, w₂) ∈ SCO(U)` iff both are writes and `(w₁, w₂) ∈ U_{proc w₂}`; this is `π.SCO U`.

Lemma C.5: if every `U_m` is a strict partial order on `Obs m` containing `PO|Obs m` and
`SCO(U)`, then `U` extends to strongly causal views.

Our proof differs from the paper's (which orders pairs of writes of two processes for all
processes simultaneously): each process is completed independently by the generic
`exists_strictTotal_extension`, which never adds new pairs `(x, y)` with `x` a write and `y` a
write of the process itself. Hence `SCO` does not grow and the completed views stay strongly
causal.
-/

namespace Podc.CausalRecordReplay

open Relation

section Generic

variable {α : Type*}

/-- Linear extension avoiding new pairs into a chain. Let `U` be a strict partial order on the
finite set `S` in which any two distinct elements of `T` are comparable. Then `U` extends to a
strict total order `W` on `S` that adds no new pair `(x, y)` with `Q x` and `T y`.

-- CSLib candidate: Cslib/Foundations/Order/LinearExtension.lean -/
theorem exists_strictTotal_extension [Finite α] {S Q T : α → Prop} {U : α → α → Prop}
    (hU : IsStrictPO U) (hsupp : ∀ {a b}, U a b → S a ∧ S b)
    (hT : ∀ {a b}, T a → T b → a ≠ b → U a b ∨ U b a) :
    ∃ W : α → α → Prop, IsStrictTotalOn S W ∧ (∀ a b, U a b → W a b) ∧
      (∀ a b, Q a → T b → W a b → U a b) := by
  suffices H : ∀ U' : α → α → Prop, IsStrictPO U' → (∀ {a b}, U' a b → S a ∧ S b) →
      (∀ a b, U a b → U' a b) → (∀ a b, Q a → T b → U' a b → U a b) →
      ∃ W : α → α → Prop, IsStrictTotalOn S W ∧ (∀ a b, U' a b → W a b) ∧
        (∀ a b, Q a → T b → W a b → U a b) from
    H U hU hsupp (fun _ _ h => h) (fun _ _ _ _ h => h)
  intro U'
  induction U' using WellFoundedGT.induction with
  | _ U' ih =>
  intro hU' hs' hle hgood
  have htr : TransRel U' := hU'.transitive
  by_cases htot : ∀ a b, S a → S b → a ≠ b → U' a b ∨ U' b a
  · exact ⟨U', ⟨hs', hU'.irrefl, hU'.trans, htot _ _⟩, fun _ _ h => h, hgood⟩
  push Not at htot
  obtain ⟨a, b, ha, hb, hab, hnab, hnba⟩ := htot
  -- one orientation is safe: it adds no new pair `(x, y)` with `Q x`, `T y`
  have hsafe : (∀ u v, Q u → T v → addPair U' a b u v → U u v) ∨
      (∀ u v, Q u → T v → addPair U' b a u v → U u v) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨x₁, y₁, hq₁, ht₁, h₁, hn₁⟩, ⟨x₂, y₂, hq₂, ht₂, h₂, hn₂⟩⟩ := hcon
    rcases h₁ with h₁ | ⟨hx₁a, hby₁⟩
    · exact hn₁ (hgood _ _ hq₁ ht₁ h₁)
    rcases h₂ with h₂ | ⟨hx₂b, hay₂⟩
    · exact hn₂ (hgood _ _ hq₂ ht₂ h₂)
    have hcmp : ReflGen U' y₁ y₂ ∨ U' y₂ y₁ := by
      by_cases hy : y₁ = y₂
      · exact Or.inl (hy ▸ ReflGen.refl)
      · rcases hT ht₁ ht₂ hy with h | h
        · exact Or.inl (ReflGen.single (hle _ _ h))
        · exact Or.inr (hle _ _ h)
    rcases hcmp with h | h
    · rcases reflGen_trans htr (reflGen_trans htr hx₂b hby₁) h with _ | h'
      · exact hnab (reflGen_of_ne (reflGen_trans htr hay₂ hx₂b) hab)
      · exact hn₂ (hgood _ _ hq₂ ht₂ h')
    · rcases reflGen_trans htr (reflGen_trans htr hx₁a hay₂) (ReflGen.single h) with _ | h'
      · exact hnba (reflGen_of_ne (reflGen_trans htr hby₁ hx₁a) (Ne.symm hab))
      · exact hn₁ (hgood _ _ hq₁ ht₁ h')
  have step : ∀ x y, S x → S y → x ≠ y → ¬ U' x y → ¬ U' y x →
      (∀ u v, Q u → T v → addPair U' x y u v → U u v) →
      ∃ W : α → α → Prop, IsStrictTotalOn S W ∧ (∀ a b, U' a b → W a b) ∧
        (∀ a b, Q a → T b → W a b → U a b) := by
    intro x y hx hy hxy hnxy hnyx hs
    have hlt : U' < addPair U' x y :=
      lt_of_le_of_ne (fun u v h => le_addPair h)
        (fun heq => hnxy (heq ▸ addPair_self (r := U') x y))
    have hsupp' : ∀ {u v}, addPair U' x y u v → S u ∧ S v := by
      intro u v h
      rcases h with h | ⟨hux, hyv⟩
      · exact hs' h
      · refine ⟨?_, ?_⟩
        · rcases hux with _ | h
          · exact hx
          · exact (hs' h).1
        · rcases hyv with _ | h
          · exact hy
          · exact (hs' h).2
    obtain ⟨W, hW1, hW2, hW3⟩ := ih _ hlt (addPair_strictPO hU' hxy hnyx) hsupp'
      (fun u v h => le_addPair (hle u v h)) hs
    exact ⟨W, hW1, fun u v h => hW2 u v (le_addPair h), hW3⟩
  rcases hsafe with h | h
  · exact step a b ha hb hab hnab hnba h
  · exact step b a hb ha (Ne.symm hab) hnba hnab h

end Generic

variable {P Op X : Type*} (π : Program P Op X)

namespace Program

/-- **Lemma C.5.** Let `U = {U_m}` be a family of strict partial orders, `U_m` on
`Obs m = (∗,m,∗,∗) ∪ (w,∗,∗,∗)`, each respecting `SCO(U) ∪ PO|Obs m` (Definition C.4:
`SCO(U)` is `π.SCO U`). Then there are strongly causal views `W` with `U_m ⊆ W_m` for all `m`. -/
theorem lemma_C_5 [Finite Op] (U : P → Op → Op → Prop) (hU : ∀ m, IsStrictPO (U m))
    (hsupp : ∀ m a b, U m a b → π.Obs m a ∧ π.Obs m b)
    (hpo : ∀ m a b, π.poOn m a b → U m a b) (hsco : ∀ m a b, π.SCO U a b → U m a b) :
    ∃ W : P → Op → Op → Prop, π.StronglyCausal W ∧ ∀ m a b, U m a b → W m a b := by
  have hex : ∀ m, ∃ W : Op → Op → Prop, IsStrictTotalOn (π.Obs m) W ∧ (∀ a b, U m a b → W a b) ∧
      (∀ a b, π.IsWrite a → (π.IsWrite b ∧ π.proc b = m) → W a b → U m a b) := by
    intro m
    refine exists_strictTotal_extension (hU m) (fun h => hsupp m _ _ h) ?_
    intro a b ha hb hne
    rcases π.po_total (ha.2.trans hb.2.symm) hne with h | h
    · exact Or.inl (hpo m a b ⟨h, π.write_obs ha.1 m, π.write_obs hb.1 m⟩)
    · exact Or.inr (hpo m b a ⟨h, π.write_obs hb.1 m, π.write_obs ha.1 m⟩)
  choose W hW1 hW2 hW3 using hex
  refine ⟨W, stronglyCausal_iff.mpr fun m => ⟨hW1 m, fun a b h => ?_, fun a b h => ?_⟩,
    hW2⟩
  · obtain ⟨ha, hb, hab⟩ := h
    exact hW2 m a b (hsco m a b ⟨ha, hb, hW3 _ a b ha ⟨hb, rfl⟩ hab⟩)
  · exact hW2 m a b (hpo m a b h)

end Program

end Podc.CausalRecordReplay
