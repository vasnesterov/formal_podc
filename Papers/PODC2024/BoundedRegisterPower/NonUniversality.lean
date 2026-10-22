import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Podc.Computability.Distributed.SWMR.Restrict

/-!
# Non-universality of bounded registers when a majority may crash (Section 3 / Section 4 of the
full version)

Proposition 4.1 (full version) / the proof of Theorem 1.1: if `n/2 < t < n`, then for every finite
register type there is a resolution `k` such that `1/k`-agreement with binary inputs cannot be
solved `t`-resiliently.

We work with an arbitrary finite set of processes `P` and a set `G` of "early" processes
(`p₁, …, p_{n-t+1}` in the paper) such that

* `2 ≤ |G|` (so that consensus among `G` is impossible),
* `|Gᶜ| + 1 ≤ t` (the processes outside `G` crash initially and one more process may crash),
* `|G| ≤ t` (all processes of `G` may crash),
* `Gᶜ` is nonempty.

For `P = Fin n` and `|G| = n - t + 1` these are exactly `n > 2` and `n/2 < t < n`.

The impossibility of `1`-resilient binary consensus (Lemma 2.1) is an explicit hypothesis `hFLP`
of the statements of this file; it is discharged in `Theorem11.lean` with
`Cslib.SWMR.Alg.not_solves_binConsensus`.
-/

namespace Podc.BoundedRegisterPower

open Cslib.SWMR

variable {P K : Type} {V : K → Type} [Fintype P] [DecidableEq P] [DecidableEq K]

/-- The consensus decision derived from an `ε`-agreement output `d` (numerator over `k`):
`0` if `d ≤ ℓ`, `1` otherwise. -/
def thr (ℓ : ℕ) (d : ℕ) : Bool := decide (ℓ < d)

/-- The statement of Claim 3.1 for `ℓ` (with the inputs outside `G` fixed to `z`): some execution
in which only processes of `G` take steps has the decisions `ℓ` and `ℓ + 1`. -/
def ClaimHolds (A : Alg P K V Bool ℕ) (G : Finset P) (z : P → Bool) (ℓ : ℕ) : Prop :=
  ∃ (xG : G → Bool) (τ : List G) (p q : P),
    (A.run (A.initCfg (liftIn xG z)) (τ.map Subtype.val)).out p = some ℓ ∧
    (A.run (A.initCfg (liftIn xG z)) (τ.map Subtype.val)).out q = some (ℓ + 1)

/-- The reduction in the proof of Claim 3.1: if no execution of `G` alone decides both `ℓ` and
`ℓ + 1`, then thresholding the decisions at `ℓ` solves binary consensus `1`-resiliently among the
processes of `G` (the others being initially crashed). -/
theorem solves_binConsensus_of_not_claim {A : Alg P K V Bool ℕ} {t k : ℕ}
    (hA : A.Solves t (epsAgreement k)) {G : Finset P} (hGt : Gᶜ.card + 1 ≤ t) (z : P → Bool)
    {ℓ : ℕ} (hℓ : ℓ < k) (hno : ¬ ClaimHolds A G z ℓ) :
    (A.restrictMap G (thr ℓ)).Solves 1 binConsensus := by
  refine ⟨fun xG τ => ⟨?_, ?_⟩, fun xG σ hσ p hp =>
    hA.restrictMap_termination hGt xG z σ hσ p hp⟩
  · -- validity: run the lifted execution with all inputs outside `G` equal to `b` as well
    intro b hb p c hc
    have hrel := ((Alg.run_restrictMap (A := A) (f := thr ℓ) xG (fun _ => b) τ).1 p).2.2
    rw [hrel] at hc
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hc
    have hx : liftIn xG (fun _ => b) = fun _ => b := by
      funext q; unfold liftIn; split_ifs with h
      · exact hb ⟨q, h⟩
      · rfl
    have hv := (hA.1 (liftIn xG fun _ => b) (τ.map Subtype.val)).2.1 b (by simp [hx]) p.1 m hm
    cases b <;> simp_all [thr]
  · -- agreement: two different consensus decisions would be `ℓ` and `ℓ + 1`
    intro p q c c' hc hc'
    have hrel := Alg.run_restrictMap (A := A) (f := thr ℓ) xG z τ
    rw [(hrel.1 p).2.2] at hc
    rw [(hrel.1 q).2.2] at hc'
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 hc
    obtain ⟨m', hm', rfl⟩ := Option.map_eq_some_iff.1 hc'
    have h1 := (hA.1 (liftIn xG z) (τ.map Subtype.val)).2.2 p.1 q.1 m m' hm hm'
    have h2 := (hA.1 (liftIn xG z) (τ.map Subtype.val)).2.2 q.1 p.1 m' m hm' hm
    by_contra hne
    apply hno
    simp only [thr] at hne
    by_cases hlm : ℓ < m
    · have hm'l : ¬ ℓ < m' := by intro h; exact hne (by simp [hlm, h])
      exact ⟨xG, τ, q.1, p.1, by rw [hm']; congr; omega, by rw [hm]; congr; omega⟩
    · have hm'l : ℓ < m' := by
        by_contra h; exact hne (by simp [hlm, h])
      exact ⟨xG, τ, p.1, q.1, by rw [hm]; congr; omega, by rw [hm']; congr; omega⟩

/-- **Claim 3.1** (Claim 4.1 of the full version): for every `ℓ < k` some execution in which only
the processes of `G` take steps decides both `ℓ / k` and `(ℓ + 1) / k`. Uses the impossibility of
`1`-resilient binary consensus among the processes of `G` (Lemma 2.1, hypothesis `hFLP`). -/
theorem claim_3_1 {A : Alg P K V Bool ℕ} {t k : ℕ} (hA : A.Solves t (epsAgreement k))
    {G : Finset P} (hGt : Gᶜ.card + 1 ≤ t)
    (hFLP : ∀ B : Alg G K V Bool Bool, ¬ B.Solves 1 binConsensus)
    (z : P → Bool) {ℓ : ℕ} (hℓ : ℓ < k) : ClaimHolds A G z ℓ := by
  by_contra hno
  exact hFLP _ (solves_binConsensus_of_not_claim hA hGt z hℓ hno)

/-- **Proposition 4.1** (full version; the core of Theorem 1.1): with `G` as above, no algorithm
whose register banks take at most `M` values (`Nat.card (∀ i, V i) = M`) solves `1/k`-agreement
`t`-resiliently as soon as `k > 2 M ^ |G|`. -/
theorem not_solves_epsAgreement [Finite (∀ i, V i)] (A : Alg P K V Bool ℕ) {t k : ℕ}
    {G : Finset P} (hGt : Gᶜ.card + 1 ≤ t) (hGt' : G.card ≤ t) (hGc : Gᶜ.Nonempty)
    (hFLP : ∀ B : Alg G K V Bool Bool, ¬ B.Solves 1 binConsensus)
    (hk : 2 * Nat.card (∀ i, V i) ^ G.card < k) :
    ¬ A.Solves t (epsAgreement k) := by
  intro hA
  classical
  have : Fintype (∀ i, V i) := Fintype.ofFinite _
  set M := Nat.card (∀ i, V i) ^ G.card with hM
  set z : P → Bool := fun _ => false
  -- the executions `E_{2i}` of Claim 3.1, `i ≤ M`
  have hcl : ∀ i : Fin (M + 1), ClaimHolds A G z (2 * i.1) := fun i =>
    claim_3_1 hA hGt hFLP z (by have := i.2; omega)
  choose xG τ p q hp hq using hcl
  set C : Fin (M + 1) → Config A := fun i =>
    A.run (A.initCfg (liftIn (xG i) z)) ((τ i).map Subtype.val)
  -- pigeonhole on the contents of the registers of `G`
  have hcard : Fintype.card (G → ∀ i, V i) < Fintype.card (Fin (M + 1)) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, hM, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨i, j, hij, hw⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i (g : G) => (C i).mem g.1) hcard
  -- the processes outside `G` cannot distinguish `E_{2i}` from `E_{2j}`
  have hnotin : ∀ (l : Fin (M + 1)) (r : P), r ∉ G → r ∉ (τ l).map Subtype.val := by
    intro l r hr hmem
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hmem
    exact hr g.2
  have hagree : AgreeOn (↑Gᶜ : Set P) (C i) (C j) := by
    refine ⟨fun r hr => ?_, ?_⟩
    · have hr' : r ∉ G := by simpa using hr
      simp only [C, Alg.run_loc_of_notMem _ _ (hnotin _ r hr'),
        Alg.run_out_of_notMem _ _ (hnotin _ r hr')]
      simp [Alg.initCfg, liftIn, hr']
    · funext r
      by_cases hr : r ∈ G
      · exact congrFun hw ⟨r, hr⟩
      · simp only [C, Alg.run_mem_of_notMem _ _ (hnotin _ r hr)]
        rfl
  -- the processes outside `G` run alone after `E_{2i}` until one of them decides `d`
  obtain ⟨u, hu⟩ := hGc
  have hcomp : (Gᶜ)ᶜ.card ≤ t := by simpa using hGt'
  obtain ⟨τ', hτ', hdec⟩ := hA.exists_decide Gᶜ hcomp (liftIn (xG i) z)
    ((τ i).map Subtype.val) hu
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 hdec
  rw [Alg.run_append] at hd
  have hag' := hagree.run (σ := τ') (fun r hr => by simpa using hτ' r hr)
  have hd' : (A.run (C j) τ').out u = some d := by
    rw [← (hag'.1 u (by simpa using hu)).2]; exact hd
  -- in both extended executions, `d` must be within `1` of `2i, 2i+1` resp. `2j, 2j+1`
  have hclose : ∀ l : Fin (M + 1), (A.run (C l) τ').out u = some d →
      2 * l.1 ≤ d ∧ d ≤ 2 * l.1 + 1 := by
    intro l hl
    have hs := (hA.1 (liftIn (xG l) z) ((τ l).map Subtype.val ++ τ')).2.2
    rw [Alg.run_append] at hs
    have h1 := hs _ _ _ _ hl (Alg.out_run_of_out _ τ' (hp l))
    have h2 := hs _ _ _ _ (Alg.out_run_of_out _ τ' (hq l)) hl
    have h3 := hs _ _ _ _ hl (Alg.out_run_of_out _ τ' (hq l))
    omega
  have hi := hclose i hd
  have hj := hclose j hd'
  exact hij (Fin.ext (by omega))

end Podc.BoundedRegisterPower
