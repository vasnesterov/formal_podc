import Papers.PODC2010.KBakery.Invariant

/-!
# k-exclusion (Lemma 4 of the paper; Lemmas 5.4 and 5.15 of the thesis)

At most `k` processes are past the waiting loop (at line 23 or in the CS) at the same time, in
both variants of the algorithm. This is the k-exclusion property of Theorems 8 and 9.
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ}

/-- In every configuration satisfying the invariant, at most `k` processes are past the loop. -/
theorem card_qual_le_of_inv {s : Cfg P} (hI : Inv k s) :
    (univ.filter fun q => (s.pc q).Qual).card ≤ k := by
  classical
  set Y := univ.filter fun q => (s.pc q).Qual with hY
  rcases Y.eq_empty_or_nonempty with h | hne
  · simp [h]
  obtain ⟨p, hpY, hmax⟩ := Y.exists_max_image (fun q => toLex (s.ticket q, q)) hne
  have hpQ : (s.pc p).Qual := (mem_filter.1 hpY).2
  have hsub : Y.erase p ⊆ U s (s.ticket p) p := by
    intro q hq
    obtain ⟨hqp, hqY⟩ := mem_erase.1 hq
    have hqQ : (s.pc q).Qual := (mem_filter.1 hqY).2
    have hle := hmax q hqY
    rw [mem_U]
    refine ⟨hqp, fun hsafe => ?_⟩
    have hl : lexLt (s.ticket p) p (s.ticket q) q := by
      unfold Safe at hsafe
      rcases hpc : s.pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
        ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc, PC.Qual] at hqQ hsafe <;>
        exact hsafe
    rw [Prod.Lex.toLex_le_toLex] at hle
    rcases hl with hl | ⟨hl, hl'⟩
    · rcases hle with hle | ⟨hle, -⟩ <;> omega
    · rcases hle with hle | ⟨-, hle⟩
      · omega
      · exact absurd (lt_of_lt_of_le hl' hle) (lt_irrefl _)
  have h1 := card_le_card hsub
  have h2 := hI.s4 p hpQ
  have h3 := card_erase_add_one hpY
  omega

/-- **k-exclusion** (Lemma 4 / Lemma 5.15): in every reachable configuration at most `k`
processes are in the critical section. -/
theorem k_exclusion {s : Cfg P} (hs : Reachable fife k s) :
    (univ.filter fun q => s.pc q = .cs).card ≤ k := by
  refine le_trans (card_le_card ?_) (card_qual_le_of_inv hs.inv)
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq ⊢
  simp [hq, PC.Qual]

/-- k-exclusion along every execution. -/
theorem Run.k_exclusion (r : Run fife k P) (t : ℕ) :
    (univ.filter fun q => (r.s t).pc q = .cs).card ≤ k := by
  refine le_trans (card_le_card ?_) (card_qual_le_of_inv (r.inv t))
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq ⊢
  simp [hq, PC.Qual]

end Podc.KBakery
