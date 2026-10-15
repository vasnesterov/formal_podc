import Papers.PODC2026.RankingOpinions.RankingSwap

/-!
# The Ranking protocol: Theorem 1.2

Breitkopf, Dallot, El-Hayek, Schmid, *Ranking Opinions with Few States in Population Protocols*,
PODC 2026 (arXiv:2605.18707), Section 6.

* `Final` is the set `X` of Definition 6.4 (as a predicate on labelled configurations: the
  configuration is only determined up to which of the diagonal agents `⟨i,0|0,i⟩` of the majority
  color holds its token, rule (6) moves this token between them).
* `final_closed`: Lemma 6.5 (`X` is closed).
* `reach_final`: Proposition 6.6 (`X` is reachable from every reachable configuration).
* `ranking_correct`: Theorem 1.2 (for the protocol with self-synchronisation, see
  `RankingProtocol.lean`; the literal protocol is wrong, see `RankingCounterexample.lean`).
-/

set_option linter.unusedSectionVars false

namespace RankingOpinions.Ranking

open Cslib.PopulationProtocol Cslib.PopulationProtocol.Protocol Finset

variable {k : ℕ} [NeZero k] {A : Type*} [DecidableEq A] [Fintype A]

/-- The set `X` of Definition 6.4: one token per color, all rankings correct and consistent,
Circles stabilized, and the token of the majority color (ranking `0`) on a diagonal braket. -/
def Final (input : A → Fin k) (C : Config A (RState k)) : Prop :=
  Inv input C ∧ OneTok C ∧ Cons (rnk (inputCount input)) C ∧ Stable (brk C) ∧
    ∀ a, (C a).tok → (C a).kr = 0 → (C a).bc = (C a).kc

/-- In `X`, every ket of ranking `m ≠ 0` is attached to a bra of ranking `m - 1`. -/
lemma Final.br_succ {input : A → Fin k} (hx : Function.Injective (inputCount input))
    {C : Config A (RState k)} (hF : Final input C) (z : A) (hz : (C z).kr ≠ 0) :
    ((C z).br : ℕ) + 1 = (C z).kr := by
  obtain ⟨hC, -, h2, hs, -⟩ := hF
  set x := inputCount input
  have hσ := rnk_injective hx
  have hz' : ((C z).kr : ℕ) ≠ 0 := fun e => hz (Fin.ext e)
  obtain ⟨g, hg⟩ : ∃ g : Fin k, (g : ℕ) = (C z).kr - 1 := ⟨⟨(C z).kr - 1, by omega⟩, rfl⟩
  obtain ⟨c', hc'⟩ := rnk_surjective hx g
  have hbd : (g : ℕ) ≤ (C z).br ∧ ((C z).br : ℕ) < (C z).kr :=
    bra_bound_layers (brk_mem_layers hC h2 hs z) (g := g) (by simp only; omega)
      (by
        simp only
        rw [(h2 z).2, ycount_apply input hσ, ← hc', ycount_apply input hσ]
        apply lt_of_rnk_lt hx
        rw [hc', Fin.lt_def, ← (h2 z).2]; omega)
  omega

/-- Moving the token of the majority color between diagonal brakets stays in `X`. -/
lemma Final.move {input : A → Fin k} {C C1 : Config A (RState k)} (hF : Final input C)
    (hI : Inv input C1) {t h : A} (hth : t ≠ h) (htt : (C t).tok = false) (hht : (C h).tok)
    (hkc : (C t).kc = (C h).kc) (hd : (C t).bc = (C t).kc)
    (h1 : C1 t = {C t with tok := true}) (h2 : C1 h = {C h with tok := false})
    (h3 : ∀ x, x ≠ t → x ≠ h → C1 x = C x) : Final input C1 := by
  obtain ⟨-, o, c, s, d⟩ := hF
  have hb : brk C1 = brk C := by
    funext x; simp only [brk]
    by_cases hxt : x = t
    · subst hxt; rw [h1]
    by_cases hxh : x = h
    · subst hxh; rw [h2]
    · rw [h3 x hxt hxh]
  refine ⟨hI, ?_, fun x => ?_, by rw [hb]; exact s, fun x hx hx0 => ?_⟩
  · apply o.of_swap (a := t) (b := h); intro x
    by_cases hxt : x = t
    · subst hxt; rw [h1]; simp [hht, hkc]
    by_cases hxh : x = h
    · subst hxh; rw [h2]; simp [htt, hkc]
    · rw [h3 x hxt hxh, Equiv.swap_apply_of_ne_of_ne hxt hxh]; exact ⟨rfl, rfl⟩
  · by_cases hxt : x = t
    · subst hxt; rw [h1]; exact c x
    by_cases hxh : x = h
    · subst hxh; rw [h2]; exact c x
    · rw [h3 x hxt hxh]; exact c x
  · by_cases hxt : x = t
    · subst hxt; rw [h1]; exact hd
    by_cases hxh : x = h
    · subst hxh; rw [h2] at hx; simp at hx
    · rw [h3 x hxt hxh] at hx hx0 ⊢; exact d x hx hx0

/-- **Lemma 6.5**: `X` is closed (stable). The only possible interactions move the token of the
majority color between identical diagonal agents `⟨i,0|0,i⟩`. -/
theorem final_closed {input : A → Fin k} (hx : Function.Injective (inputCount input)) :
    (ranking k).Closed (Final input) := by
  rintro C C' hF ⟨a, b, hab, rfl⟩
  have hF' := hF
  obtain ⟨hC, o, c, s, d⟩ := hF'
  have hσ := rnk_injective hx
  set p := C a
  set q := C b
  have hpq : ∀ {X Y : RState k}, (X = p ∧ Y = q) ∨ (X = q ∧ Y = p) → ¬ (X.tok ∧ Y.tok ∧
      X.kc = Y.kc) := by
    rintro X Y hXY ⟨h1, h2, h3⟩
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab (o a b h1 h2 h3)
    · exact hab (o b a h1 h2 h3).symm
  have hkr : ∀ {X Y : RState k}, (X = p ∧ Y = q) ∨ (X = q ∧ Y = p) → X.kr = Y.kr →
      X.kc = Y.kc := by
    rintro X Y hXY e
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hσ (by rw [← (c a).2, ← (c b).2, e])
    · exact hσ (by rw [← (c a).2, ← (c b).2, e])
  have pq : (p = p ∧ q = q) ∨ (p = q ∧ q = p) := Or.inl ⟨rfl, rfl⟩
  have qp : (q = p ∧ p = q) ∨ (q = q ∧ p = p) := Or.inr ⟨rfl, rfl⟩
  have hcons : ∀ {X : RState k}, X = p ∨ X = q → SCons (rnk (inputCount input)) X := by
    rintro X (rfl | rfl)
    · exact c a
    · exact c b
  have hdiag : ∀ {X : RState k}, X = p ∨ X = q → X.tok → X.kr = 0 → X.bc = X.kc := by
    rintro X (rfl | rfl)
    · exact d a
    · exact d b
  have hsucc : ∀ {X : RState k}, X = p ∨ X = q → X.kr ≠ 0 → (X.br : ℕ) + 1 = X.kr := by
    rintro X (rfl | rfl)
    · exact hF.br_succ hx a
    · exact hF.br_succ hx b
  -- the rules other than rule (6), first bullet, do not apply
  have S : ∀ {X Y : RState k} (hXY : (X = p ∧ Y = q) ∨ (X = q ∧ Y = p)),
      r2 X Y = (X, Y) ∧ r3 X Y = (X, Y) ∧ r4a X Y = (X, Y) ∧ r4b X Y = (X, Y) ∧
      r5 X Y = (X, Y) ∧ r6b X Y = (X, Y) ∧ r7a X Y = (X, Y) ∧ r7b X Y = (X, Y) := by
    intro X Y hXY
    have hX : X = p ∨ X = q := by rcases hXY with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
    have hY : Y = p ∨ Y = q := by rcases hXY with ⟨-, h⟩ | ⟨-, h⟩ <;> simp [h]
    refine ⟨r2_eq (hpq hXY), r3_eq (fun h => hpq hXY ⟨h.1, h.2.1, hkr hXY h.2.2⟩),
      r4a_eq (fun _ _ e => by rw [(hcons hX).2, (hcons hY).2, e]),
      r4b_eq (fun _ e => by rw [(hcons hY).1, (hcons hX).2, e]), r5_eq ?_, r6b_eq ?_,
      r7a_eq ?_, r7b_eq ?_⟩
    · rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact s a b hab
      · exact s b a hab.symm
    · rintro ⟨-, hYt, -, hkr', -, hYd, hlt⟩
      by_cases h0 : Y.kr = 0
      · exact hYd (hdiag hY hYt h0)
      · have e1 := hsucc hY h0
        have e2 := hsucc hX (hkr' ▸ h0)
        rw [hkr'] at e2
        rw [Fin.lt_def] at hlt; omega
    · rintro ⟨-, -, -, hbr, -, -, hne⟩
      have e := hsucc hX (hbr ▸ hne)
      rw [hbr] at e; omega
    · intro hXt hYt _ hbr hXd hYd
      have hX0 : X.kr ≠ 0 := fun h0 => hXd (hdiag hX hXt h0).symm
      have hY0 : Y.kr ≠ 0 := fun h0 => hYd (hdiag hY hYt h0).symm
      have e1 := hsucc hX hX0
      have e2 := hsucc hY hY0
      rw [hbr] at e1
      exact Fin.ext (by omega)
  obtain ⟨a2, a3, a4a, a4b, a5, a6b, a7a, a7b⟩ := S pq
  obtain ⟨b2, b3, b4a, b4b, b5, b6b, b7a, b7b⟩ := S qp
  by_cases h6 : Still r6a p q
  · have hr := rδ_still ⟨a2, b2⟩ ⟨a3, b3⟩ ⟨a4a, b4a⟩ ⟨a4b, b4b⟩ ⟨a5, b5⟩ h6 ⟨a6b, b6b⟩
      ⟨a7a, b7a⟩ ⟨a7b, b7b⟩ (hC.normal a) (hC.normal b)
    have : (ranking k).interact C a b = C := by
      rw [interact_eq hr]; funext x; split_ifs with h1 h2
      · subst h1; rfl
      · subst h2; rfl
      · rfl
    rw [this]; exact hF
  have hI := hC.step ⟨a, b, hab, rfl⟩
  simp only [Still, not_and_or] at h6
  rcases h6 with h6 | h6
  · -- `a` receives the token
    have g : p.tok = false ∧ p.bc = p.kc ∧ p.br = p.kr ∧ q.tok ∧ q.kc = p.kc ∧ q.kr = p.kr := by
      by_contra hg; exact h6 (r6a_eq hg)
    have hr := rδ_r6a g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2
    have hI' := interact_eq hr
    exact hF.move hI hab g.1 g.2.2.2.1 g.2.2.2.2.1.symm g.2.1 (by rw [hI']; simp [p])
      (by rw [hI']; simp [q, hab.symm]) (fun x h1 h2 => by rw [hI']; simp [h1, h2])
  · -- `b` receives the token
    have g : q.tok = false ∧ q.bc = q.kc ∧ q.br = q.kr ∧ p.tok ∧ p.kc = q.kc ∧ p.kr = q.kr := by
      by_contra hg; exact h6 (r6a_eq hg)
    have hr := rδ_r6a' g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2
    have hI' := interact_eq hr
    exact hF.move hI hab.symm g.1 g.2.2.2.1 g.2.2.2.2.1.symm g.2.1
      (by rw [hI']; simp [q, hab.symm]) (by rw [hI']; simp [p])
      (fun x h1 h2 => by rw [hI']; simp [h1, h2])

/-- Last step of Proposition 6.6: with the correct ranking, put the token of the majority color
on a diagonal braket. -/
lemma phase6 {input : A → Fin k} (hx : Function.Injective (inputCount input))
    {C : Config A (RState k)} (hC : Inv input C) (h1 : OneTok C)
    (h2 : Cons (rnk (inputCount input)) C) (hs : Stable (brk C)) :
    ∃ C', Final input C' ∧ (ranking k).Reachable C C' := by
  have hσ := rnk_injective hx
  obtain ⟨u, hu⟩ := rnk_surjective hx 0
  have htop := rnk_eq_zero hx (u := u) (by rw [hu]; rfl)
  obtain ⟨C1, r1, i1, o1, c1, s1, H, hH, hHu, hHb⟩ := top_on_diag hσ hC h1 h2 hs htop
  refine ⟨C1, ⟨i1, o1, c1, s1, fun z hz hz0 => ?_⟩, r1⟩
  have : (C1 z).kc = u := hσ (by rw [← (c1 z).2, hz0, hu])
  rw [o1 z H hz hH (this.trans hHu.symm), hHb, hHu]

/-- **Proposition 6.6**: `X` is reachable from every configuration satisfying the global
invariants (in particular from every configuration reachable from the initial one). -/
theorem reach_final {input : A → Fin k} (hall : ∀ c, ∃ a, input a = c)
    (hx : Function.Injective (inputCount input)) (C : Config A (RState k)) (hC : Inv input C) :
    ∃ C', Final input C' ∧ (ranking k).Reachable C C' := by
  obtain ⟨C1, r1, i1, o1⟩ := phase1 input C hC
  obtain ⟨C2, σ, r2, i2, o2, t2, hσ⟩ := phase2 C1 i1 o1
  suffices loop : ∀ n (C : Config A (RState k)) (σ : Fin k → Fin k),
      wrong (inputCount input) σ = n → Inv input C → OneTok C → TR σ C →
      Function.Injective σ → ∃ C', Final input C' ∧ (ranking k).Reachable C C' by
    obtain ⟨C', hF, r'⟩ := loop _ C2 σ rfl i2 o2 t2 hσ
    exact ⟨C', hF, r1.trans (r2.trans r')⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C σ hn hC h1 h2 hσ
  obtain ⟨C3, r3, i3, o3, c3⟩ := phase3 hσ C hC h1 h2
  obtain ⟨C4, r4, i4, o4, c4, s4⟩ := phase4 C3 i3 o3 c3
  by_cases hw : ∃ c, σ c ≠ rnk (inputCount input) c
  · obtain ⟨C5, σ', r5, i5, o5, t5, hσ', hlt⟩ := phase5 hall hx hσ i4 o4 c4 s4 hw
    obtain ⟨C', hF, r'⟩ := ih _ (hn ▸ hlt) C5 σ' rfl i5 o5 t5 hσ'
    exact ⟨C', hF, r3.trans (r4.trans (r5.trans r'))⟩
  · push Not at hw
    have : σ = rnk (inputCount input) := funext hw
    subst this
    obtain ⟨C', hF, r'⟩ := phase6 hx i4 o4 c4 s4
    exact ⟨C', hF, r3.trans (r4.trans r')⟩

/-- **Theorem 1.2** (Ranking). Let every color be present in the input and no two colors have the
same number of supporters (Definition 6.1). Then in every globally fair execution of the Ranking
protocol (with self-synchronisation) from the initial configuration, eventually and forever every
agent with input `i` outputs `|{ℓ : x_ℓ > x_i}|`. The protocol has `2·k⁴` states
(`card_RState`). -/
theorem ranking_correct (input : A → Fin k) (hall : ∀ c, ∃ a, input a = c)
    (hx : Function.Injective (inputCount input)) (E : (ranking k).Execution A)
    (h0 : E.config 0 = initConfig input) (hE : E.GloballyFair) :
    ∃ T, ∀ t ≥ T, ∀ a, (output (E.config t a) : ℕ) =
      (univ.filter fun ℓ => inputCount input (input a) < inputCount input ℓ).card := by
  obtain ⟨T, hT⟩ := hE.eventually_mem (final_closed hx) (fun C hreach =>
    reach_final hall hx C ((inv_init input hall).reachable (h0 ▸ hreach)))
  refine ⟨T, fun t ht a => ?_⟩
  obtain ⟨hC, -, c, -, -⟩ := hT t ht
  rw [output, (c a).1, hC.bc a, rnk_val]

end RankingOpinions.Ranking
