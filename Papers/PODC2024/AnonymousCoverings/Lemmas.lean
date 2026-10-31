import Papers.PODC2024.AnonymousCoverings.Stable

/-!
# Lemmas 4.5–4.7 of the paper, as printed

In the rendered paper the three lemmas speak about a set `A` of processors and its complement
`Ā` (an overline, which plain-text extraction of the PDF drops):

* **Lemma 4.5.** If `A` is nonempty and live and, after `t`, every read of a member of `A` reads a
  register last written by a member of `A`, then at all times after `t` at most `|A|` registers are
  last written by `Ā`.
* **Lemma 4.6.** If at all times after `t` at most `|A|` registers are last written by `Ā`, and `Ā`
  is live, then some member of `Ā` eventually reads from `A`.
* **Lemma 4.7.** Under the hypotheses of Lemma 4.5, if `Ā` is live, then some member of `Ā`
  eventually reads from `A`.

All three hold for every write–scan algorithm of `Model.lean`. Lemmas 4.6 and 4.7 need at least
as many registers as processors (the paper's proof of Lemma 4.6 uses `N` registers); with fewer
registers Lemma 4.6 fails (`lemma_4_6_needs_registers` in `Counterexamples.lean`).

Our proof of Lemma 4.6 differs from the paper's case analysis: if no member of `Ā` read from `A`,
then, once every register has been written, `Ā` would read only from itself, so by Lemma 4.5 (for
`Ā`) at most `|Ā|` registers are *not* last written by `Ā`; with the hypothesis and `|R| ≥ N` both
counts are exact at all times, and the next write of a live member of `Ā` into a register not last
written by `Ā` breaks the count.
-/

namespace Podc.AnonymousCoverings

open Finset

variable {P R D X : Type*} [Fintype P] [DecidableEq P] [DecidableEq R] [Fintype R]

namespace Exec

variable {A : Algo R D X} (e : Exec (P := P) A)

/-- **Lemma 4.5 of the paper (as printed).** Let `A` be a set of processors with a live member
such that, from time `t` on, every read of a member of `A` reads a register last written by a
member of `A`. Then at all times after `t` at most `|A|` registers are last written by `Ā`. -/
theorem lemma_4_5 (h0 : ∀ r, (e.reg 0 r).writer = none) (S : Finset P) (t : ℕ)
    (hS : e.ReadsOnlyFrom S t) (hlive : ∃ a ∈ S, e.Live a) :
    ∀ t' ≥ t, (e.writtenBy Sᶜ t').card ≤ S.card := by
  intro t' ht'
  exact (card_le_card (e.writtenBy_subset_notWrittenBy disjoint_compl_left t')).trans
    (e.card_notWrittenBy_le S t' h0 (fun t'' ht'' => hS t'' (by omega)) hlive)

/-- **Lemma 4.6 of the paper (as printed, with `N ≤ |R|`).** If at all times after `t` at most
`|A|` registers are last written by `Ā`, and some member of `Ā` is live, then some member of `Ā`
reads from `A` at some time after `t`. -/
theorem lemma_4_6 (hPR : Fintype.card P ≤ Fintype.card R) (h0 : ∀ r, (e.reg 0 r).writer = none)
    (S : Finset P) (t : ℕ) (hcov : ∀ t' ≥ t, (e.writtenBy Sᶜ t').card ≤ S.card)
    (hlive : ∃ a ∈ Sᶜ, e.Live a) :
    ∃ t' ≥ t, ∃ a ∈ Sᶜ, ∃ r, e.act t' = .read a r ∧ ∃ b ∈ S, (e.reg t' r).writer = some b := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨a, ha, hla⟩ := hlive
  -- a time after which every register has been written
  have hw : ∀ r, ∃ w ≥ t, e.act w = .write a r := fun r => e.exists_write_reg_of_live hla r t
  choose w hw1 hw2 using hw
  set T₁ := t + univ.sup (fun r => w r + 1) with hT₁
  have hwr : ∀ t' ≥ T₁, ∀ r, ∃ q, (e.reg t' r).writer = some q := by
    intro t' ht' r
    have : w r + 1 ≤ univ.sup (fun r => w r + 1) := le_sup (f := fun r => w r + 1) (mem_univ r)
    exact e.writer_isSome_of_write (hw2 r) (by omega)
  have hclosed : e.ReadsOnlyFrom Sᶜ T₁ := by
    intro t' ht' b hb r hr
    obtain ⟨q, hq⟩ := hwr t' ht' r
    refine ⟨q, ?_, hq⟩
    rw [mem_compl]
    intro hqS
    exact hno t' (by omega) b hb r hr q hqS hq
  have heq : ∀ t' ≥ T₁, (e.notWrittenBy Sᶜ t').card = Sᶜ.card := by
    intro t' ht'
    have a1 := e.card_notWrittenBy_le Sᶜ t' h0 (fun t'' ht'' => hclosed t'' (by omega))
      ⟨a, ha, hla⟩
    have a2 := hcov t' (by omega)
    have a3 := e.card_writtenBy_add Sᶜ t'
    have a4 := card_compl_add_card S
    omega
  exact e.false_of_card_notWrittenBy_eq Sᶜ T₁ heq ha hla

/-- **Lemma 4.7 of the paper (as printed, with `N ≤ |R|`).** Let `A` have a live member and, from
time `t` on, read only registers last written by members of `A`. If some member of `Ā` is live,
then some member of `Ā` reads from `A` at some time after `t`. -/
theorem lemma_4_7 (hPR : Fintype.card P ≤ Fintype.card R) (h0 : ∀ r, (e.reg 0 r).writer = none)
    (S : Finset P) (t : ℕ) (hS : e.ReadsOnlyFrom S t) (hlive : ∃ a ∈ S, e.Live a)
    (hlive' : ∃ a ∈ Sᶜ, e.Live a) :
    ∃ t' ≥ t, ∃ a ∈ Sᶜ, ∃ r, e.act t' = .read a r ∧ ∃ b ∈ S, (e.reg t' r).writer = some b :=
  e.lemma_4_6 hPR h0 S t (e.lemma_4_5 h0 S t hS hlive) hlive'

end Exec

end Podc.AnonymousCoverings
