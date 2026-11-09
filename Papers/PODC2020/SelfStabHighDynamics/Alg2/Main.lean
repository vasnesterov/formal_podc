import Papers.PODC2020.SelfStabHighDynamics.Alg2.Legit

/-!
# Algorithm 2: paper-facing statements (Section 5)

Altisen, Devismes, Durand, Johnen, Petit, *Self-stabilizing Systems in Spite of High Dynamics*
(PODC 2020; full version TCS 2023), Section 5: self-stabilizing leader election for `TC_Q(Δ)`
with `n` and `Δ` known.

Conventions: rounds are 0-indexed, `(alg Δ).exec G γ t` is the configuration at the end of Round
`t` (the paper's "beginning of Round `t + 1`"); the paper's Round `Δ + i` (`i ≥ 1`) is the step
from time `t = Δ + i - 1 ≥ Δ` to `t + 1`. All statements hold for every order in which the
received pairs are processed (the `round` lemmas of `Alg2/Round.lean` are proved for an arbitrary
list of received pairs).
-/

namespace Podc.SelfStabHighDynamics.Alg2

open Cslib.HeardOf Cslib.DynNet
open StabilizingLEDynamic (DG IsDG JssQ JssB)

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ} {V : Finset ι} {G : DG ι} {γ : ι → MSt ι}

/-- The configurations of Algorithm 2 for `V` are invariant: `n = |V|`, at most `n` pairs in
`members(p)`, distinct identifiers, timestamps `≤ Δ`. -/
theorem cfg_invariant (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V) (t : ℕ) :
    (alg Δ).exec G γ t ∈ (alg Δ).Cfg V :=
  exec_cfg hG hγ t

/-- After every round, `⟨id(p), 0⟩ ∈ members(p)` (line 7; first remark in the proof of
Lemma 7). -/
theorem own_pair (G : DG ι) (γ : ι → MSt ι) (t : ℕ) (p : ι) :
    (p, 0) ∈ ((alg Δ).exec G γ (t + 1) p).mem :=
  self_mem G γ t p

/-- **Lemma 5** of [Altisen et al. 2020]. Let `f` be a fake identifier. At the beginning of
Round `t + 1`, every pair `⟨f, ts⟩ ∈ members(p)` has `ts ≥ min(Δ, t)`. (No assumption on the
initial configuration is needed.) -/
theorem lemma_5 (hG : IsDG V G) {f : ι} (hf : f ∉ V) :
    ∀ t, ∀ p ∈ V, ∀ x ∈ ((alg Δ).exec G γ t p).mem, x.1 = f → min Δ t ≤ x.2 :=
  fake_ge hG hf

/-- **Corollary 7** of [Altisen et al. 2020]. From time `Δ` on (i.e. in every Round `Δ + i`,
`i ≥ 1`), every pair sent by a process carries a real identifier. -/
theorem corollary_7 (hG : IsDG V G) {t : ℕ} (ht : Δ ≤ t) {p : ι} (hp : p ∈ V) {x : ι × ℕ}
    (hx : x ∈ sent Δ ((alg Δ).exec G γ t p)) : x.1 ∈ V :=
  sent_mem hG ht hp hx

/-- **Lemma 6** of [Altisen et al. 2020]. If `q` is inserted into `members(p)` in Round
`Δ + i`, `i ≥ 1` (0-indexed: the round from time `t ≥ Δ` to `t + 1`; `q` is received from an
in-neighbour, or `q = p`, line 7), then `q ∈ members(p)` forever after this round.

The paper's counting argument is not correct as written (see `lemma_6_suffix`); the proof uses
the invariant `lemma_6_suffix` instead. -/
theorem lemma_6 (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V) {t : ℕ} (ht : Δ ≤ t) {p q : ι}
    (hp : p ∈ V) (hins : q = p ∨ ∃ r, G t r p ∧ ∃ ts, (q, ts) ∈ sent Δ ((alg Δ).exec G γ t r)) :
    ∀ u > t, q ∈ keys ((alg Δ).exec G γ u p).mem :=
  persist hG hγ ht hp hins

/-- The invariant behind Lemma 6: from time `Δ` on, a suffix of `members(p)` consisting of real
identifiers is never cut (its identifiers stay in such a suffix, and their timestamps grow by at
most one per round). The head of the queue is removed (line i5) only when the queue is full and a
new identifier is inserted; if the head belonged to such a suffix, the queue would consist of
`n = |V|` distinct real identifiers, i.e. all of `V`, and no new identifier could be inserted
(Corollary 7). -/
theorem lemma_6_suffix (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V) {t : ℕ} (ht : Δ ≤ t) {p : ι}
    (hp : p ∈ V) {k : ι} {B : ℕ} (h : Tail V ((alg Δ).exec G γ t p).mem k B) (u : ℕ) :
    Tail V ((alg Δ).exec G γ (t + u) p).mem k (B + u) :=
  h.exec_add hG hγ ht hp u

/-- The paper's counting claim in the proof of Lemma 6 ("after `id` is inserted, it requires the
insertion of `n` distinct identifiers that are not in `members(p)` to get `id` at the head and
remove it") is false: re-insertions of identifiers that are ahead of `id` (lines i2–i3) also move
`id` towards the head. Here `n = 3`, `id = 5` was just inserted; the re-insertions of `1` and `2`
bring it to the head, and the first new identifier `7` evicts it. (In a real execution after
round `Δ` this cannot happen, since then `{1, 2, 5}` would be all of `V`.) -/
theorem lemma_6_counting_claim_false :
    insert 3 (insert 3 (insert 3 [((1 : ℕ), 0), (2, 0), (5, 0)] (1, 0)) (2, 0)) (7, 0) =
      [(1, 0), (2, 0), (7, 0)] := by
  decide

/-- **Lemma 7** of [Altisen et al. 2020] (0-indexed). Let `j ≥ Δ` (`Δ ≥ 1`) be such that
`d̂_{G_{j▷}}(q, p) ≤ Δ` (e.g. the paper's `t(q, p)`). Then `q ∈ members(p)` at the end of every
Round `t ≥ j + Δ`. -/
theorem lemma_7 (hΔ : 0 < Δ) (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V) {p q : ι} (hq : q ∈ V)
    {j : ℕ} (hj : Δ ≤ j) (hd : tdist G j q p ≤ Δ) :
    ∀ t ≥ j + Δ, q ∈ keys ((alg Δ).exec G γ t p).mem :=
  mem_of_tdist hG hγ hq hj (by omega) hd

/-- **Lemma 8** of [Altisen et al. 2020], with the closure remark before it. In an arbitrary
dynamic graph with vertex set `V`, the legitimate configurations (of Algorithm 2 for `V`) are
closed and every execution from them satisfies `SP_LE`. -/
theorem lemma_8 (hV : V.Nonempty) (hG : IsDG V G)
    (hγ : γ ∈ (alg Δ).Cfg V ∩ {γ | Legit V γ}) :
    (∀ t, (alg Δ).exec G γ t ∈ (alg Δ).Cfg V ∩ {γ | Legit V γ}) ∧
      spLE (alg Δ) V ((alg Δ).exec G γ) :=
  ⟨legit_exec hG hγ, V.min' hV, V.min'_mem hV, fun i q hq =>
    ((legit_iff hV).1 (legit_exec hG hγ i).2 q hq).1⟩

/-- **Lemma 9** of [Altisen et al. 2020]. In `TC_Q(Δ)`, there is `t ≥ Δ` such that the
configuration at the end of Round `t + Δ` is legitimate (in fact, all later ones are too). -/
theorem lemma_9 (hG : G ∈ JssQ Δ V) (hγ : γ ∈ (alg Δ).Cfg V) :
    ∃ t ≥ Δ, Legit V ((alg Δ).exec G γ (t + Δ)) := by
  obtain ⟨T, hT, h⟩ := legit_eventually hG hγ
  exact ⟨T, hT, h _ le_rfl⟩

/-- **Theorem 5** of [Altisen et al. 2020] (correctness part): for every nonempty `V`, the
legitimate configurations form a set of legitimate configurations of Algorithm 2 for `V` in
`TC_Q(Δ)` (Definition 1 / Remark 1). -/
theorem theorem_5_isLegit (hV : V.Nonempty) :
    IsLegit (alg Δ) (JssQ Δ) (spLE (alg Δ)) V ((alg Δ).Cfg V ∩ {γ | Legit V γ}) := by
  refine ⟨Set.inter_subset_left, fun G hG γ hγ => ?_, fun G hG γ hγ => (lemma_8 hV hG.1 hγ).2⟩
  obtain ⟨t, -, ht⟩ := lemma_9 hG hγ
  exact ⟨t + Δ, cfg_invariant hG.1 hγ _, ht⟩

/-- **Theorem 5** of [Altisen et al. 2020] (closure, remark before Lemma 8). -/
theorem theorem_5_closed :
    Closed (alg Δ) (JssQ Δ) V ((alg Δ).Cfg V ∩ {γ | Legit V γ}) :=
  fun _ hG _ hγ i => legit_exec hG.1 hγ i

/-- **Theorem 5** of [Altisen et al. 2020]. Algorithm 2 is a self-stabilizing leader election
algorithm for `TC_Q(Δ)`. -/
theorem theorem_5 : SelfStab (alg (ι := ι) Δ) (JssQ Δ) (spLE (alg Δ)) :=
  fun _ hV => ⟨_, theorem_5_isLegit hV⟩

/-- **Theorem 7** of [Altisen et al. 2020] (0-indexed). In `TC_B(Δ)` (`Δ ≥ 1`), the
configuration is legitimate from the end of Round `2Δ` on. -/
theorem theorem_7 (hΔ : 0 < Δ) (hG : G ∈ JssB Δ V) (hγ : γ ∈ (alg Δ).Cfg V) :
    ∀ t ≥ 2 * Δ, Legit V ((alg Δ).exec G γ t) :=
  legit_bounded hΔ hG hγ

/-- Algorithm 2 is not size-ambiguous (Definition 3): the input `n = |V|` is part of the local
state, so the possible local states differ for systems of different sizes (consistent with
Theorem 3). -/
theorem not_sizeAmbiguous : ¬ SizeAmbiguous (alg (ι := ι) Δ) := by
  rintro ⟨k, V, hk, hkV, h⟩
  obtain ⟨U, hUV, hU⟩ := Finset.exists_subset_card_eq hkV.le
  obtain ⟨p, hp⟩ := Finset.card_pos.1 (hU ▸ hk)
  have hs : (⟨U.card, [], p⟩ : MSt ι) ∈ (alg Δ).S U p := by simp [alg, keys]
  rw [h U hUV hU p hp] at hs
  have : U.card = V.card := hs.1
  omega

end Podc.SelfStabHighDynamics.Alg2
