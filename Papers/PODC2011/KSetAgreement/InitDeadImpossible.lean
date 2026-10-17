import Papers.PODC2011.KSetAgreement.Basic

/-!
# Theorem 8, "only if": impossibility with initially dead processes

If `k * n ≤ (k + 1) * f` (and `f < n`), then `k`-set agreement is impossible in an asynchronous
system of `n` processes of which up to `f` may be initially dead.

The paper proves this only for the border case `k * n = (k + 1) * f`, by a partitioning argument,
and otherwise refers to Theorem 2 — which however is about a *different* failure model (`f - 1`
initially dead processes plus one crash during the execution), stronger than initial crashes only,
so its impossibility does not transfer. The paper's partitioning argument works verbatim for all
`k * n ≤ (k + 1) * f`: split the processes into `k + 1` disjoint groups of size `n - f`; in the run
where only group `i` takes steps (everybody else is initially dead) group `i` decides on its own
input `w i`; merging these runs gives a run in which `k + 1` values are decided.
-/

namespace KSetAgreement

open Cslib Cslib.FLP

variable {P M S V : Type*} [DecidableEq P] [DecidableEq M]

/-- `m` pairwise disjoint groups of size `ℓ` exist as soon as `m * ℓ ≤ |P|`. -/
theorem exists_disjoint_groups [Fintype P] (m ℓ : ℕ) (h : m * ℓ ≤ Fintype.card P) :
    ∃ G : Fin m → Finset P, (∀ i, (G i).card = ℓ) ∧
      ∀ i j, i ≠ j → Disjoint (G i) (G j) := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨G', hcard, hdisj⟩ := ih (le_trans (Nat.mul_le_mul_right _ (Nat.le_succ m)) h)
    set U := Finset.univ.biUnion G'
    have hU : U.card ≤ m * ℓ := by
      refine le_trans Finset.card_biUnion_le ?_
      simp [hcard]
    have hc : ℓ ≤ Uᶜ.card := by
      rw [Finset.card_compl]
      have : (m + 1) * ℓ = m * ℓ + ℓ := by ring
      omega
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq hc
    refine ⟨Fin.cons t G', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using htc
      · simpa using hcard i
    · intro i j hij
      have key : ∀ i : Fin m, Disjoint t (G' i) := by
        intro i
        refine Finset.disjoint_left.2 fun p hp hpi => ?_
        have := ht hp
        rw [Finset.mem_compl] at this
        exact this (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hpi⟩)
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j => simpa using key j
      | succ i =>
        induction j using Fin.cases with
        | zero => simpa using (key i).symm
        | succ j =>
          simpa using hdisj i j (fun h => hij (by rw [h]))

omit [DecidableEq P] [DecidableEq M] in
/-- The set of decided values is finite. -/
theorem decVals_finite [Finite P] (s : State P M (Loc M S V)) : (decVals s).Finite := by
  refine ((Set.finite_range (fun p => dec s p)).preimage
    (Option.some_injective V).injOn).subset ?_
  rintro v ⟨p, hp⟩
  exact ⟨p, hp⟩

omit [DecidableEq P] [DecidableEq M] in
/-- If `m` distinct values are decided in `s`, then at least `m` values are decided. -/
theorem le_ncard_decVals [Finite P] {m : ℕ} (s : State P M (Loc M S V)) (w : Fin m → V)
    (hw : Function.Injective w) (hdec : ∀ i, w i ∈ decVals s) : m ≤ (decVals s).ncard := by
  have h1 : (Set.range w).ncard = m := by
    rw [Set.ncard_range_of_injective hw, Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [← h1]
  exact Set.ncard_le_ncard (by rintro _ ⟨i, rfl⟩; exact hdec i) (decVals_finite s)

/-- Validity for constant inputs: in a run where everybody has input `v`, only `v` is decided. -/
theorem dec_eq_of_const [Fintype P] {A : KAlgorithm P M S V} {k : ℕ} (hS : KSafe A k)
    {v : V} {inp : P → Bool} {xl : List (Action P M)} {s : State P M (Loc M S V)}
    (h : (A.algX (fun _ => v)).lts.MTr ((A.algX (fun _ => v)).start inp) xl s)
    {p : P} {u : V} (hu : dec s p = some u) : u = v := by
  obtain ⟨_, rfl⟩ := (hS _ inp s ⟨xl, h⟩).2 p u hu
  rfl

/-- **The partitioning argument.** If `A` is `k`-safe and, for `k + 1` pairwise disjoint nonempty
groups, every solo run of a group (all other processes never take a step, the group is correct)
is admissible, then `A` does not terminate. -/
theorem partition_argument [Fintype P] (A : KAlgorithm P M S V) (k : ℕ)
    (R : RunPred P M (Loc M S V)) (w : Fin (k + 1) → V) (hw : Function.Injective w)
    (G : Fin (k + 1) → Finset P) (hne : ∀ i, (G i).Nonempty)
    (hdisj : ∀ i j, i ≠ j → Disjoint (G i) (G j))
    (hR : ∀ i x inp ss xs, IsRun (A.algX x) inp ss xs → (∀ j, DestIn (↑(G i) : Set P) (xs j)) →
      (∀ p ∈ G i, ProcFair p ss xs) → R (A.algX x) inp ss xs) :
    ¬ SolvesKSA A k R := by
  rintro ⟨hS, hT⟩
  let inp : P → Bool := fun _ => false
  have hsolo := fun i => solo_prefix A R hT (fun _ => w i) inp (G i) (hR i _ inp)
  choose xl s hxl hdest hdec using hsolo
  -- the input assignment of the merged run
  classical
  let idx : P → Fin (k + 1) := fun p => if h : ∃ i, p ∈ G i then h.choose else 0
  have hidx : ∀ i, ∀ p ∈ G i, idx p = i := by
    intro i p hp
    have h : ∃ i, p ∈ G i := ⟨i, hp⟩
    simp only [idx, h, ↓reduceDIte]
    by_contra hne'
    exact Finset.disjoint_left.1 (hdisj _ _ hne') h.choose_spec hp
  let x : P → V := fun p => w (idx p)
  obtain ⟨zl, t, ht, -, hagree⟩ := merge A x inp (fun i => (↑(G i) : Set P)) (fun i _ => w i)
    (fun i p hp => by simp [x, hidx i p hp]) xl s hxl hdest (List.finRange (k + 1))
    (by
      refine List.Pairwise.imp_of_mem ?_ (List.nodup_finRange (k + 1))
      intro i j _ _ hij
      exact Finset.disjoint_coe.2 (hdisj i j hij))
  have hmem : ∀ i, w i ∈ decVals t := by
    intro i
    obtain ⟨p, hp⟩ := hne i
    obtain ⟨u, hu⟩ := hdec i p hp
    have hu' : u = w i := dec_eq_of_const hS (hxl i) hu
    refine ⟨p, ?_⟩
    rw [dec, hagree i (List.mem_finRange i) p hp, ← dec, hu, hu']
  have h1 := le_ncard_decVals t w hw hmem
  have h2 := (hS x inp t ⟨zl, ht⟩).1
  omega

/-- **Theorem 8 ("only if" direction)** of [BRS11]: in an asynchronous system of `n = |P|`
processes, up to `f < n` of which may be initially dead, `k`-set agreement is impossible if
`k * n ≤ (k + 1) * f` (provided there are `k + 1` distinct input values, e.g. `|V| ≥ n`). -/
theorem initDead_impossible [Fintype P] (A : KAlgorithm P M S V) {n f k : ℕ}
    (hn : Fintype.card P = n) (hf : f < n) (hk : k * n ≤ (k + 1) * f)
    (w : Fin (k + 1) → V) (hw : Function.Injective w) :
    ¬ SolvesKSA A k (InitDead f) := by
  have hgroups : (k + 1) * (n - f) ≤ Fintype.card P := by
    rw [hn, Nat.mul_sub]
    have : (k + 1) * n = k * n + n := by ring
    omega
  obtain ⟨G, hcard, hdisj⟩ := exists_disjoint_groups (k + 1) (n - f) hgroups
  refine partition_argument A k (InitDead f) w hw G (fun i => ?_) hdisj ?_
  · rw [← Finset.card_pos, hcard]; omega
  · intro i x inp ss xs hrun hdest hfair
    refine ⟨hrun, (G i)ᶜ, ?_, ?_, ?_⟩
    · rw [Finset.card_compl, hcard, hn]; omega
    · intro p hp j m hj hmp
      have := hdest j
      rw [hj] at this
      exact (Finset.mem_compl.1 hp) (hmp ▸ this)
    · intro p hp
      exact hfair p (by simpa using hp)

end KSetAgreement
