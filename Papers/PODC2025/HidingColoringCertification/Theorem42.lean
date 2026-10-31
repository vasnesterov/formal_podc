import Papers.PODC2025.HidingColoringCertification.Forgetful

/-!
# Theorem 4.2 is false

Theorem 4.2 of the brief announcement (= Theorem 1.2 of arXiv:2502.13854v1): *Let `r ≥ 1` and let
`H` be a class of graphs containing at least one `r`-forgetful (connected) graph that is neither
an even cycle nor has minimum degree 1. Then there is no strong and hiding `r`-round LCP for
`2-col_H`, no matter the certificate size; this holds even if the LCP is not anonymous.*

We state its `r = 1` instance in our one-round model (`BATheorem42`; with the hypotheses on the
special graph *strengthened*: strict forgetfulness, connected, not 2-regular) and refute it
(`baTheorem42_false`) with the counter LCP (`ModCounter.lean`) on `H = ` all bipartite graphs,
which contain `θ(5,5,5)`: the counter LCP is complete, sound, strongly sound on every graph, uses
`O(log n)`-bit certificates, is anonymous, and is hiding even against identifier-aware
extraction algorithms.

The authors' corrected version (arXiv v3, Theorems 2(1), 3(1), 4: classes of `r`-forgetful
bipartite graphs avoiding minimum degree 1 and even cycles; anonymous or order-invariant LCPs;
any certificate size) is refuted as well (`v3Theorem4_false`), with the class `{θ(5,5,5)}`.
The gap in the proof: Lemma 5.3 (v3: Lemma 21) needs the odd closed walk to have at most
`√(N/Δ^r)` views, but the odd cycles of `V(D,n)` can be much longer than `N` — for the counter
LCP every odd cycle of `V(D,n)` has length `≥ M > 2N`.
-/

namespace Podc.HidingColoringCertification

open SimpleGraph

/-- Theorem 4.2 of [MMR25] for `r = 1`, in the one-round model, with strengthened hypotheses on
the special graph (so that this statement is implied by the paper's). -/
def BATheorem42 (bound : ℕ → ℕ) : Prop :=
  ∀ (L : Type) (H : GraphClass), (∀ V G, H V G → G.Colorable 2) →
    (∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
        H V G ∧ IsForgetful G 1 ∧ G.Connected ∧ ¬ IsCycleLike G ∧ G.minDegree ≠ 1) →
    ∀ S : LCP L, ¬ (S.Complete bound H ∧ S.Sound bound 2 ∧ S.StronglySound bound 2 ∧
      S.Hiding bound H 2)

variable {bound : ℕ → ℕ}

/-- The counter LCP: complete, sound, strongly sound (on every graph), anonymous, and hiding on
every class of bipartite graphs containing `θ(5,5,5)`. -/
theorem counterLCP_strong_hiding (hb : 14 ≤ bound 14) (H : GraphClass)
    (hHbip : ∀ V G, H V G → G.Colorable 2) (hθ : H (Fin 14) thetaG) :
    (counterLCP bound).Complete bound H ∧ (counterLCP bound).Sound bound 2 ∧
      (counterLCP bound).StronglySound bound 2 ∧ (counterLCP bound).Hiding bound H 2 ∧
      (counterLCP bound).StronglySoundAll 2 ∧ (counterLCP bound).Anonymous := by
  refine ⟨fun P hP hH => counterLCP_complete P hP (hHbip _ _ hH),
    counterLCP_stronglySoundAll.stronglySound.sound, counterLCP_stronglySoundAll.stronglySound,
    counterLCP_hiding hb H hθ, counterLCP_stronglySoundAll, counterLCP_anonymous⟩

/-- **Theorem 4.2 of the brief announcement is false** (already for `r = 1`, `H` = all bipartite
graphs), for every choice of the polynomial `N = bound n ≥ n`. -/
theorem baTheorem42_false (hb : 14 ≤ bound 14) : ¬ BATheorem42 bound := by
  intro h
  apply h ℕ Bipartite (fun _ _ hG => hG)
    ⟨Fin 14, inferInstance, thetaG, inferInstance, thetaG_colorable, thetaG_isForgetful,
      thetaG_connected, thetaG_not_cycleLike, thetaG_minDegree⟩ (counterLCP bound)
  obtain ⟨h1, h2, h3, h4, -⟩ :=
    counterLCP_strong_hiding hb Bipartite (fun _ _ hG => hG) thetaG_colorable
  exact ⟨h1, h2, h3, h4⟩

/-- The corrected statement of arXiv:2502.13854v3 (Theorem 4, and part 1 of Theorems 2 and 3),
for `r = 1`: for a class `G` of 1-forgetful (Definition 22) bipartite graphs avoiding minimum
degree 1 and even cycles, no *anonymous* LCP for `2-col_G` is hiding and strongly sound,
regardless of certificate size. (We state it with hiding against all extraction algorithms,
which makes the statement weaker, hence its refutation stronger.) -/
def V3Theorem4 (bound : ℕ → ℕ) : Prop :=
  ∀ (L : Type) (G : GraphClass),
    (∀ V Gr, G V Gr → ∃ (_ : Fintype V) (_ : DecidableRel Gr.Adj),
      Gr.Colorable 2 ∧ IsForgetfulV3 Gr 1 ∧ Gr.minDegree ≠ 1 ∧ ¬ IsCycleLike Gr) →
    ∀ S : LCP L, S.Anonymous →
      ¬ (S.Complete bound G ∧ S.StronglySound bound 2 ∧ S.Hiding bound G 2)

/-- The class consisting of `θ(5,5,5)` only. -/
def thetaClass : GraphClass := fun V Gr => ∃ h : V = Fin 14, h ▸ Gr = thetaG

/-- **The corrected lower bound of arXiv v3 is false as well** (anonymous LCPs, any certificate
size, `r = 1`, the class `{θ(5,5,5)}`). -/
theorem v3Theorem4_false (hb : 14 ≤ bound 14) : ¬ V3Theorem4 bound := by
  intro h
  have hmem : ∀ V Gr, thetaClass V Gr → Gr.Colorable 2 := by
    rintro V Gr ⟨rfl, rfl⟩; exact thetaG_colorable
  apply h ℕ thetaClass ?_ (counterLCP bound) counterLCP_anonymous
  · obtain ⟨h1, -, h3, h4, -⟩ := counterLCP_strong_hiding hb thetaClass hmem ⟨rfl, rfl⟩
    exact ⟨h1, h3, h4⟩
  · rintro V Gr ⟨rfl, rfl⟩
    exact ⟨inferInstance, inferInstance, thetaG_colorable, thetaG_isForgetfulV3,
      thetaG_minDegree, thetaG_not_cycleLike⟩

end Podc.HidingColoringCertification
