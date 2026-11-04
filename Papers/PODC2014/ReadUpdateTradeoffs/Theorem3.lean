import Papers.PODC2014.ReadUpdateTradeoffs.Lemma4
import Papers.PODC2014.ReadUpdateTradeoffs.Asymptotics

/-!
# Theorems 3 and 4 of Hendler–Khait (PODC'14): the max-register tradeoff

Iterating Lemma 4 (with Lemma 6 bounding the number of finished processes) gives executions in
which many processes each take many steps in a single `WriteMax`:

* `ess_iter` — after `t` iterations the essential set has at least `gStep m^[t] |W|` processes,
  where `gStep m x = ⌊√(x − m)⌋/3 − 1` and `m` bounds the step complexity of `ReadMax`;
* `theorem3` — non-asymptotic form of Theorem 3: some execution has at least `max(2m, X₀)`
  processes each having taken `t ≥ log₃(log |W| / log max(2m, X₀)) − 1` steps within a single
  pending `WriteMax`;
* `theorem4` — Theorem 4: if `ReadMax` takes `O(log |W|)` steps then `WriteMax` takes
  `Ω(log log |W|)` steps;
* `theorem3_fin`, `theorem4_fin` — the paper's setting: `N` processes `Fin N`, an `M`-bounded
  max register, writers `p₁ … p_{K−1}` writing their index, `K = min(N, M)`, reader `p₀`.
-/

namespace Podc.ReadUpdateTradeoffs

open Cslib.SharedMemory Cslib.SharedMemory.Awareness

variable {P : Type} [Fintype P] [DecidableEq P]
variable {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
variable {I : Impl maxRegObj (RWC ι V v₀) P L} {W : Finset P} {val : P → ℕ}

/-- The size of the essential set after `t` iterations of the construction. -/
theorem ess_iter (hlin : I.Linearizable) {r : P} (hr : r ∉ W) (hval : ∀ p ∈ W, 1 ≤ val p)
    (hinj : Set.InjOn val W) (hall : ∀ p ∈ W, I.allowed p (.writeMax (val p))) {m : ℕ}
    (hm : SoloBound I r MaxOp.readMax m) :
    ∀ t, ∃ α C G E H, Ess I W val t α C G E H ∧ (gStep m)^[t] W.card ≤ E.card := by
  intro t
  induction t with
  | zero =>
    obtain ⟨α, C, G, hE⟩ := ess_zero (I := I) (val := val) hall
    exact ⟨α, C, G, W, ∅, hE, le_rfl⟩
  | succ t ih =>
    classical
    obtain ⟨α, C, G, E, H, hE, hcard⟩ := ih
    have h6 := lemma6 hlin hr hval hm hE
    obtain ⟨α', C', G', E', H', hE', -, h4⟩ := lemma4 hinj hE
    refine ⟨α', C', G', E', H', hE', ?_⟩
    set Ee := E.filter (fun e => ∃ j o k, I.act e (C.loc e) = Action.access j o k)
    set Ec := E.filter (fun e => ∃ x l, I.act e (C.loc e) = Action.ret x l)
    have hsplit : E.card ≤ Ee.card + Ec.card := by
      refine (Finset.card_le_card (t := Ee ∪ Ec) ?_).trans (Finset.card_union_le _ _)
      intro e he
      cases h : I.act e (C.loc e) with
      | access j o k => exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨he, j, o, k, h⟩)
      | ret x l => exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨he, x, l, h⟩)
    rw [Function.iterate_succ_apply']
    refine (gStep_mono m hcard).trans ?_
    unfold gStep
    have hsq : Nat.sqrt (E.card - m) ≤ Nat.sqrt Ee.card :=
      Nat.sqrt_le_sqrt (by omega)
    have := Nat.div_le_div_right (c := 3) (hsq.trans h4)
    rw [Nat.mul_div_cancel_left _ (by norm_num)] at this
    omega

/-- **Theorem 3 of Hendler–Khait, PODC'14 (non-asymptotic form).** Let `I` be a linearizable
implementation of a max register from read/write/CAS base objects; the writers `W` (not
containing the reader `r`) write pairwise distinct positive values `val p`, and a `ReadMax` of
`r` completes within `m` solo steps. If `|W| ≥ T := max(2m, X₀)`, then there is an execution in
which at least `T` writers each have taken exactly `t` steps in their single (still pending)
`WriteMax`, for some `t ≥ log₃(log |W| / log T) − 1`. With `m = O(f(K))` this is the paper's
"`Ω(f(K))` processes each take `Ω(log (log K / log f(K)))` steps". -/
theorem theorem3 (hlin : I.Linearizable) {r : P} (hr : r ∉ W) (hval : ∀ p ∈ W, 1 ≤ val p)
    (hinj : Set.InjOn val W) (hall : ∀ p ∈ W, I.allowed p (.writeMax (val p))) {m : ℕ}
    (hm : SoloBound I r MaxOp.readMax m) (hW : max (2 * m) X₀ ≤ W.card) :
    ∃ t : ℕ, Real.logb 3 (Real.log W.card / Real.log ((max (2 * m) X₀ : ℕ) : ℝ)) - 1 ≤ t ∧
      ∃ α, I.Valid α ∧ ∃ E ⊆ W, max (2 * m) X₀ ≤ E.card ∧
        ∀ e ∈ E, opsOf α e = [.writeMax (val e)] ∧ respsOf α e = [] ∧ tauCount α e = t := by
  obtain ⟨t, ht, hst⟩ := doubly_log_bound m (fun j => (gStep m)^[j] W.card)
    (fun j => by rw [Function.iterate_succ_apply']) hW
  obtain ⟨α, C, G, E, H, hE, hcard⟩ := ess_iter hlin hr hval hinj hall hm t
  refine ⟨t, by simpa using ht, α, ⟨C, arun_fst I hE.run⟩, E,
    (Finset.subset_union_left).trans hE.subW, hst.trans hcard, fun e he =>
      ⟨hE.ops e (Finset.mem_union_left _ he), hE.resps e, hE.steps e he⟩⟩

/-- **Theorem 4 of Hendler–Khait, PODC'14.** If `ReadMax` completes within `c · log |W|` solo
steps, then `WriteMax` needs `Ω(log log |W|)` steps: there are `K₀` and `c' > 0` (depending only
on `c`) such that for every such implementation with `|W| ≥ K₀` some execution has a writer that
has taken `t ≥ c' · log log |W|` steps in a single pending `WriteMax`. -/
theorem theorem4 (c : ℝ) : ∃ K₀ : ℕ, ∃ c' > (0 : ℝ),
    ∀ {P ι L V : Type} [Fintype P] [DecidableEq P] [DecidableEq ι] [DecidableEq V] {v₀ : V}
      {I : Impl maxRegObj (RWC ι V v₀) P L} {W : Finset P} {val : P → ℕ},
      I.Linearizable → ∀ {r : P}, r ∉ W → (∀ p ∈ W, 1 ≤ val p) → Set.InjOn val W →
      (∀ p ∈ W, I.allowed p (.writeMax (val p))) → ∀ {m : ℕ}, SoloBound I r MaxOp.readMax m →
      (m : ℝ) ≤ c * Real.log W.card → K₀ ≤ W.card →
      ∃ t : ℕ, c' * Real.log (Real.log W.card) ≤ t ∧ ∃ α, I.Valid α ∧ ∃ e ∈ W,
        opsOf α e = [.writeMax (val e)] ∧ respsOf α e = [] ∧ tauCount α e = t := by
  obtain ⟨K₀, c', hc', hK⟩ := loglog_bound c
  refine ⟨K₀, c', hc', ?_⟩
  intro P ι L V _ _ _ _ v₀ I W val hlin r hr hval hinj hall m hm hmc hK₀
  obtain ⟨t, ht, hst⟩ := hK m (fun j => (gStep m)^[j] W.card)
    (fun j => by rw [Function.iterate_succ_apply']) hK₀ (by simpa using hmc)
  obtain ⟨α, C, G, E, H, hE, hcard⟩ := ess_iter hlin hr hval hinj hall hm t
  have hne : E.Nonempty := Finset.card_pos.1 (by
    have := le_trans two_le_X₀ (le_max_right (2 * m) X₀)
    have := hst.trans hcard
    omega)
  obtain ⟨e, he⟩ := hne
  exact ⟨t, by simpa using ht, α, ⟨C, arun_fst I hE.run⟩, e,
    hE.subW (Finset.mem_union_left _ he), hE.ops e (Finset.mem_union_left _ he), hE.resps e,
    hE.steps e he⟩

/-- The writers `p₁ … p_{M−1}` among `N ≥ M` processes. -/
def writersFin (N M : ℕ) : Finset (Fin N) := Finset.univ.filter (fun p => 1 ≤ p.val ∧ p.val < M)

lemma card_writersFin {N M : ℕ} (hMN : M ≤ N) : (writersFin N M).card = M - 1 := by
  have : (writersFin N M).map Fin.valEmbedding = Finset.Ioo 0 M := by
    ext x
    simp only [writersFin, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ioo]
    constructor
    · rintro ⟨p, ⟨h1, h2⟩, rfl⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨x, by omega⟩, ⟨h1, h2⟩, rfl⟩
  rw [← Finset.card_map, this, Nat.card_Ioo]; omega

/-- **Theorem 4 of Hendler–Khait, PODC'14, in the paper's setting with `M ≤ N`.** Let `I` be a
linearizable implementation, for processes `Fin N`, of an `M`-bounded max register (`WriteMax(v)`
allowed for `v ≤ M`) from read/write/CAS. If a `ReadMax` of `p₀` completes within `c · log M`
solo steps, then (for `M ≥ K₀`) some `WriteMax` takes `≥ c' · log log (M − 1)` steps, i.e.
`WriteMax` takes `Ω(log log min(N, M))` steps. -/
theorem theorem4_fin (c : ℝ) (hc : 0 ≤ c) : ∃ K₀ : ℕ, ∃ c' > (0 : ℝ),
    ∀ {N M : ℕ} {ι L V : Type} [DecidableEq ι] [DecidableEq V] {v₀ : V}
      {I : Impl maxRegObj (RWC ι V v₀) (Fin N) L} (hN : 0 < N), I.Linearizable →
      (∀ p v, v ≤ M → I.allowed p (.writeMax v)) → ∀ {m : ℕ},
      SoloBound I ⟨0, hN⟩ MaxOp.readMax m → (m : ℝ) ≤ c * Real.log M → K₀ ≤ M → M ≤ N →
      ∃ t : ℕ, c' * Real.log (Real.log (M - 1 : ℕ)) ≤ t ∧ ∃ α, I.Valid α ∧ ∃ e : Fin N,
        opsOf α e = [.writeMax e.val] ∧ respsOf α e = [] ∧ tauCount α e = t := by
  obtain ⟨K₀, c', hc', hK⟩ := theorem4 (2 * c)
  refine ⟨max K₀ 3 + 1, c', hc', ?_⟩
  intro N M ι L V _ _ v₀ I hN hlin hall m hm hmc hK₀ hMN
  have hcard := card_writersFin (N := N) (M := M) hMN
  have hM3 : 3 ≤ M - 1 := by omega
  have hlog : Real.log M ≤ 2 * Real.log ((M - 1 : ℕ) : ℝ) := by
    have h1 : (M : ℝ) ≤ ((M - 1 : ℕ) : ℝ) ^ 2 := by
      have : M ≤ (M - 1) ^ 2 := by
        obtain ⟨k, hk⟩ : ∃ k, M = k + 1 := ⟨M - 1, by omega⟩
        subst hk
        simp only [Nat.add_sub_cancel] at hM3 ⊢
        nlinarith
      exact_mod_cast this
    have h2 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    calc Real.log M ≤ Real.log (((M - 1 : ℕ) : ℝ) ^ 2) := Real.log_le_log h2 h1
      _ = 2 * Real.log ((M - 1 : ℕ) : ℝ) := by rw [Real.log_pow]; norm_num
  obtain ⟨t, ht, α, hα, e, -, h1, h2, h3⟩ := hK (I := I) (W := writersFin N M)
    (val := fun p => p.val) hlin (r := ⟨0, hN⟩)
    (by simp [writersFin]) (fun p hp => (Finset.mem_filter.1 hp).2.1)
    (fun a _ b _ h => Fin.ext h)
    (fun p hp => hall p p.val (by have := (Finset.mem_filter.1 hp).2.2; omega)) hm
    (by rw [hcard]; nlinarith) (by rw [hcard]; omega)
  exact ⟨t, by rw [hcard] at ht; exact ht, α, hα, e, h1, h2, h3⟩

end Podc.ReadUpdateTradeoffs
