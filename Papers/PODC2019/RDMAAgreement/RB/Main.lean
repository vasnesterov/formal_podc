import Papers.PODC2019.RDMAAgreement.RB.NonVacuity

/-!
# Lemma 4.1 of "The Impact of RDMA on Agreement" (PODC 2019)

"Reliable broadcast can be solved in shared memory with SWMR regular registers with
`n ≥ 2f + 1` processes" — via (a charitably corrected) Algorithm 2. The model is described in
`Model.lean`: asynchronous shared memory of SWMR *regular* registers, `f` Byzantine processes,
unforgeable transferable signatures, fairness for liveness.

Safety (Properties 2 and 3) holds in every execution with `|F| ≤ f`, without fairness and without
`n ≥ 2f + 1` (`Exec.agreement`, `Exec.integrity`); liveness (Properties 1 and 4) needs fairness;
Property 1 also needs `n ≥ 2f + 1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

/-- **Lemma 4.1** (Definition 1, Properties (1)–(4)) for Algorithm 2, in every fair execution
with at most `f` Byzantine processes among `n ≥ 2f + 1`. `bc p k = some m`: `p` broadcast
`(k, m)`; `dlv p q k = some m`: `p` delivered `(k, m)` from `q`. -/
theorem lemma_4_1 [Inhabited P] (hF : F.card ≤ f) (hn : 2 * f + 1 ≤ Fintype.card P)
    (e : Exec (M := M) F f) (hfair : e.Fair) :
    -- (1) validity
    (∀ p ∉ F, ∀ k m t, (e.s t).bc p k = some m →
      ∀ r ∉ F, ∃ t', (e.s t').dlv r p k = some m) ∧
    -- (2) agreement
    (∀ p ∉ F, ∀ p' ∉ F, ∀ r k m m' t t', (e.s t).dlv p r k = some m →
      (e.s t').dlv p' r k = some m' → m = m') ∧
    -- (3) integrity
    (∀ p ∉ F, ∀ q ∉ F, ∀ k m t, (e.s t).dlv p q k = some m → (e.s t).bc q k = some m) ∧
    -- (4) totality
    (∀ p ∉ F, ∀ q k m t, (e.s t).dlv p q k = some m →
      ∀ r ∉ F, ∃ t' m', (e.s t').dlv r q k = some m') :=
  ⟨fun p hp k m t hb r hr => e.validity hF hn hfair hp k m t hb r hr,
   fun p hp p' hp' r k m m' t t' h1 h2 => e.agreement hF hp hp' h1 h2,
   fun p hp q hq k m t hd => e.integrity hF hp hq hd,
   fun p hp q k m t hd r hr => e.totality hF hfair hp hr hd⟩

/-- **Non-vacuity of Lemma 4.1.** For every admissible `F` with a correct process `p₀` and every
message `m₀`, there is a fair execution in which `p₀` broadcasts `(1, m₀)` and every correct
process delivers `(1, m₀)` from `p₀`. -/
theorem lemma_4_1_nonvacuous [Inhabited P] (hF : F.card ≤ f) (hn : 2 * f + 1 ≤ Fintype.card P)
    (p₀ : P) (hp₀ : p₀ ∉ F) (m₀ : M) :
    ∃ e : Exec (M := M) F f, e.Fair ∧ (e.s 1).bc p₀ 1 = some m₀ ∧
      ∀ r ∉ F, ∃ t, (e.s t).dlv r p₀ 1 = some m₀ := by
  obtain ⟨e, hfair, hb⟩ := exists_fair_exec (f := f) p₀ hp₀ m₀
  exact ⟨e, hfair, hb, fun r hr => (lemma_4_1 hF hn e hfair).1 p₀ hp₀ 1 m₀ 1 hb r hr⟩

end Podc.RDMAAgreement.RB
