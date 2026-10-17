import Papers.PODC2026.LocalComputable.ComputableEquiv

/-!
# Lemma 5.2: critical views are decidable

For a computable non-decreasing locality bound `T` and a computably listable family of networks
(all networks with at most `m` nodes, for every `m`), it is decidable whether a view of radius
`t` that actually occurs is `T`-critical. This is the paper's Lemma 5.2, for our corrected
notion of maximally safe neighbourhoods (`Model.Critical`).

As in the paper the decision procedure is non-uniform: it hard-codes the supremum `C` of `T` if
`T` is bounded (finite information that need not be computable from a program for `T`).
-/

namespace LocalComputable

open Computable

variable {Net View : Type*}

namespace Model

variable (M : Model Net View) [DecidableEq View] [Primcodable Net] [Primcodable View]

/-- **Lemma 5.2** of [Cruciani et al., PODC 2026] (for critical views). If `T` is computable and
non-decreasing and the networks with at most `m` nodes form a computable list `nets m`, there is
a computable test `p` that decides, for every view `x = view G v t` that occurs in some network,
whether `x` is `T`-critical at radius `t`. -/
theorem critical_decidable
    (hsize : Computable M.size) (hview : Computable fun p : Net × ℕ × ℕ => M.view p.1 p.2.1 p.2.2)
    {T : ℕ → ℕ} (hT : Computable T) (hmono : Monotone T)
    (nets : ℕ → List Net) (hnets : Computable nets) (hnetsG : ∀ m G, G ∈ nets m ↔ M.size G ≤ m) :
    ∃ p : View → ℕ → Bool, Computable₂ p ∧
      ∀ (G : Net) (v : Fin (M.size G)) (t : ℕ),
        p (M.view G v t) t = true ↔ M.Critical T (M.view G v t) t := by
  classical
  -- `q t = true` only if `T ≤ t` everywhere; `q t = false` only if `t < T m` for some `m`.
  obtain ⟨q, hq, hqtrue, hqfalse⟩ : ∃ q : ℕ → Bool, Computable q ∧
      (∀ t, q t = true → ∀ n, T n ≤ t) ∧ (∀ t, q t = false → ∃ m, t < T m) := by
    by_cases hb : ∃ C, ∀ n, T n ≤ C
    · refine ⟨fun t => decide (Nat.find hb ≤ t),
        Primrec.nat_le.decide.to_comp.comp (const _) .id, ?_, ?_⟩
      · intro t ht n
        exact (Nat.find_spec hb n).trans (of_decide_eq_true ht)
      · intro t ht
        have hlt : t < Nat.find hb := by simpa using ht
        have := Nat.find_min hb hlt
        push Not at this
        exact this
    · push Not at hb
      exact ⟨fun _ => false, const _, by simp, fun t _ => hb t⟩
  have hex : ∀ t, ∃ m, (q t || decide (t < T m)) = true := by
    intro t
    rcases h : q t
    · obtain ⟨m, hm⟩ := hqfalse t h
      exact ⟨m, by simp [hm]⟩
    · exact ⟨0, by simp⟩
  let mt : ℕ → ℕ := fun t => Nat.find (hex t)
  have hmt : Computable mt :=
    computable_nat_find (Primrec.or.to_comp.comp (hq.comp fst)
      (Primrec.nat_lt.decide.to_comp.comp fst (hT.comp snd))).to₂ hex
  let search : View → ℕ → Bool := fun x t => (nets (mt t)).any fun G =>
    (List.range (M.size G)).any fun v => decide (M.view G v t = x) && decide (T (M.size G) ≤ t)
  have hsearch : Computable₂ search := by
    refine Computable₂.mk ((computable_list_any (f := fun a : View × ℕ => nets (mt a.2))
      (p := fun a G => (List.range (M.size G)).any fun v =>
        decide (M.view G v a.2 = a.1) && decide (T (M.size G) ≤ a.2))
      (hnets.comp (hmt.comp snd)) ?_).of_eq fun a => rfl)
    refine Computable₂.mk ((computable_list_any
      (f := fun b : (View × ℕ) × Net => List.range (M.size b.2))
      (p := fun b v => decide (M.view b.2 v b.1.2 = b.1.1) && decide (T (M.size b.2) ≤ b.1.2))
      (Primrec.list_range.to_comp.comp (hsize.comp snd)) ?_).of_eq fun b => rfl)
    have h1 : Computable fun c : ((View × ℕ) × Net) × ℕ =>
        decide (M.view c.1.2 c.2 c.1.1.2 = c.1.1.1) := by
      have hv : Computable fun c : ((View × ℕ) × Net) × ℕ => M.view c.1.2 c.2 c.1.1.2 :=
        hview.comp (pair (snd.comp fst) (pair snd (snd.comp (fst.comp fst))))
      exact (Primrec.eq (α := View)).decide.to_comp.comp hv (fst.comp (fst.comp fst))
    have h2 : Computable fun c : ((View × ℕ) × Net) × ℕ =>
        decide (T (M.size c.1.2) ≤ c.1.1.2) :=
      Primrec.nat_le.decide.to_comp.comp (hT.comp (hsize.comp (snd.comp fst)))
        (snd.comp (fst.comp fst))
    exact (Primrec.and.to_comp.comp h1 h2).to₂
  refine ⟨fun x t => q t || search x t,
    (Primrec.or.to_comp.comp (hq.comp snd) hsearch).to₂, fun G v t => ?_⟩
  show (q t || search (M.view G v t) t) = true ↔ _
  constructor
  · intro h
    rcases hqt : q t
    · rw [hqt, Bool.false_or] at h
      simp only [search, List.any_eq_true, List.mem_range, Bool.and_eq_true,
        decide_eq_true_eq] at h
      obtain ⟨G', -, v', hv', hx, hT'⟩ := h
      exact ⟨G', v', hv', hx, hT'⟩
    · exact ⟨G, v, v.2, rfl, hqtrue t hqt _⟩
  · rintro ⟨G', v', hv', hx, hT'⟩
    rcases hqt : q t
    · simp only [Bool.false_or]
      have hm : t < T (mt t) := by
        have h0 := Nat.find_spec (hex t)
        have h1 : (q t || decide (t < T (mt t))) = true := h0
        simpa [hqt] using h1
      have hsz : M.size G' ≤ mt t := by
        by_contra hc
        push Not at hc
        have := hmono hc.le
        omega
      simp only [search, List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨G', (hnetsG _ _).mpr hsz, v', hv', hx, hT'⟩
    · rfl

end Model

end LocalComputable
