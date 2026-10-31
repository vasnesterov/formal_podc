import Papers.PODC2025.HidingColoringCertification.Model

/-!
# Lemma 3.2: hiding ⇔ the accepting neighbourhood graph is not `k`-colourable

`Compat S bound H π n μ₁ μ₂` (yes-instance compatibility): `μ₁, μ₂` are the (projected) views of
two adjacent nodes in an admissible, admissibly labelled, everywhere-accepted instance of `H`
with at most `n` nodes. The accepting neighbourhood graph `V(D,n)` has these pairs as edges (a
pair `μ, μ` is a loop: then `V(D,n)` is not colourable). `NbhdColorable … n` says that `V(D,n)`
is `k`-colourable.

`lemma_3_2`: `D` is hiding (against extraction algorithms that see the projection `π` of the
view) iff `V(D,n)` is not `k`-colourable for some `n`. We do this for any projection `π` that
retains `N` (identity: `Hiding`; `View.anon`: `AnonHiding`). The direction "colourable for all `n`
⇒ not hiding" uses that every node knows `N ≥ n` (it colours its view with a colouring of
`V(D,N)`); extraction algorithms are arbitrary functions (the paper requires computable ones and
proves computability of `V(D,n)`, Lemma 3.1; not formalized).
-/

namespace Podc.HidingColoringCertification

namespace LCP

variable {L W : Type} (S : LCP L) (bound : ℕ → ℕ) (H : GraphClass) (π : View L → W)

/-- Hiding against extraction algorithms that only see `π` of the view. -/
def HidingVia (k : ℕ) : Prop :=
  ∀ A : W → Fin k, ∃ P : PortGraph, P.Admissible bound ∧ H P.V P.G ∧
    ∃ ℓ : P.V → L, S.SizeOK P ℓ ∧ (∀ v, S.Acc P ℓ v) ∧ Fails (A ∘ π) P ℓ

lemma hiding_iff_hidingVia (k : ℕ) : S.Hiding bound H k ↔ S.HidingVia bound H id k := Iff.rfl

lemma anonHiding_iff_hidingVia (k : ℕ) :
    S.AnonHiding bound H k ↔ S.HidingVia bound H View.anon k := Iff.rfl

/-- Yes-instance compatibility of (projected) views, in instances with at most `n` nodes. -/
def Compat (n : ℕ) (μ₁ μ₂ : W) : Prop :=
  ∃ P : PortGraph, P.Admissible bound ∧ Fintype.card P.V ≤ n ∧ H P.V P.G ∧
    ∃ ℓ : P.V → L, S.SizeOK P ℓ ∧ (∀ v, S.Acc P ℓ v) ∧
      ∃ u v, P.G.Adj u v ∧ π (P.view ℓ u) = μ₁ ∧ π (P.view ℓ v) = μ₂

/-- `V(D,n)` is `k`-colourable. -/
def NbhdColorable (k n : ℕ) : Prop :=
  ∃ c : W → Fin k, ∀ μ₁ μ₂, S.Compat bound H π n μ₁ μ₂ → c μ₁ ≠ c μ₂

/-- **Lemma 3.2** of [MMR25]: `D` hides a `k`-colouring iff `V(D,n)` is not `k`-colourable for
some `n`. The projection `π` must retain the value `N` known to the nodes. -/
theorem lemma_3_2 (getN : W → ℕ) (hN : ∀ μ, getN (π μ) = μ.N) (k : ℕ) :
    S.HidingVia bound H π k ↔ ∃ n, ¬ S.NbhdColorable bound H π k n := by
  constructor
  · intro hid
    by_contra hcol
    push Not at hcol
    choose c hc using hcol
    obtain ⟨P, hP, hH, ℓ, hsz, hacc, u, v, huv, heq⟩ := hid (fun μ => c (getN μ) μ)
    simp only [Function.comp, hN] at heq
    exact hc P.N _ _ ⟨P, hP, P.card_le_N, hH, ℓ, hsz, hacc, u, v, huv, rfl, rfl⟩
      (by simpa [PortGraph.view] using heq)
  · rintro ⟨n, hn⟩ A
    by_contra hcon
    apply hn
    refine ⟨A, fun μ₁ μ₂ hc heq => ?_⟩
    obtain ⟨P, hP, -, hH, ℓ, hsz, hacc, u, v, huv, rfl, rfl⟩ := hc
    exact hcon ⟨P, hP, hH, ℓ, hsz, hacc, u, v, huv, heq⟩

/-- Lemma 3.2 for identifier-aware extraction algorithms. -/
theorem lemma_3_2_hiding (k : ℕ) :
    S.Hiding bound H k ↔ ∃ n, ¬ S.NbhdColorable bound H id k n :=
  S.lemma_3_2 bound H id View.N (fun _ => rfl) k

/-- Lemma 3.2 for anonymous extraction algorithms. -/
theorem lemma_3_2_anon (k : ℕ) :
    S.AnonHiding bound H k ↔ ∃ n, ¬ S.NbhdColorable bound H View.anon k n :=
  S.lemma_3_2 bound H View.anon AnonView.N (fun _ => rfl) k

end LCP

end Podc.HidingColoringCertification
