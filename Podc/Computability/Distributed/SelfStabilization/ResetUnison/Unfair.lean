import Podc.Computability.Distributed.SelfStabilization.ResetUnison.Basic
import Cslib.Foundations.Data.Nat.Descent

-- CSLib candidate: Cslib/Computability/Distributed/SelfStabilization/ResetUnison/Unfair.lean

/-!
# Reset-based unison under the distributed unfair daemon

Convergence and liveness of the Boulinier–Petit–Villain unison (`ResetUnison/Basic.lean`) under
the distributed unfair daemon, for a clock with `α ≥ n` and `K > n` (`n` the number of processes).
This is a self-contained proof for this range of parameters; it does not use the
`hole`/`cyclo` graph parameters of the original paper.

## Proof outline

* **Causes of resets** (`initial_or_cause`). When `v` executes `RA` at step `t`, its register has
  been positive and not `allCorrect` since some time `s + 1`, and either `s + 1 = 0`
  (`Initial`) or some neighbour `x` executed `RA` at step `s` (`Cause x s v t`).
* **Reset chains** (`IsChain`): `(w 0, τ 0) ← (w 1, τ 1) ← ⋯ ← (w L, τ L)`.
  While `w (k+1)` is positive, its neighbour `w k` cannot leave `-α`; afterwards `w k` stays at
  most one above `w (k+1)` (rule `CA` needs locally minimal values). Hence at time `τ m` the
  process `w (m-j)` is still in `init*` for `1 ≤ j ≤ α` (`chain_window`), so it is different from
  `w m`, which is positive. With `α ≥ n`, chains have fewer than `n` links (`chain_length_lt`).
* **Finitely many resets** (`eventually_no_reset`): resets with chains of length `j` are finite by
  induction on `j` (a reset causes at most one reset per neighbour).
* After the last reset, rule `CA` is executed finitely often (negative registers only increase),
  then only `NA` remains. If `Γ₁` were never reached, the non-`allCorrect` processes would be
  frozen forever; a process next to a frozen one moves at most twice (`evConst_of_adj`), and by
  connectivity every process eventually stops: a terminal configuration, impossible
  (`not_terminal`).

## Main results

* `exists_legit`: every run from a valid configuration reaches `Γ₁` (if `α ≥ n`, `K > n`, `G`
  connected);
* `live_of_legit`: in `Γ₁`, every process is activated infinitely often;
* `visits_of_legit`: in `Γ₁`, every process is activated infinitely often while its register
  holds any prescribed value `c ∈ stab`.
-/

namespace Cslib.SelfStabilization.ResetUnison

open Cslib.SelfStabilization

variable {V : Type*} {K α : ℕ} {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
  {e : ℕ → V → ℤ} {S : ℕ → Set V}

/-! ### Causes of resets -/

section Causes

variable (K G e S)

/-- A reset of `v` at `t` whose register has been frozen, positive and not `allCorrect`, since
time `0`. -/
def Initial (v : V) (t : ℕ) : Prop :=
  RA (K := K) (G := G) e S v t ∧ ∀ s ≤ t, e s v = e t v ∧ ¬ AllCorrect K G (e s) v

/-- The reset of `x` at `s` *causes* the reset of its neighbour `w` at `t > s`: the register of `w`
is frozen and `w` is not `allCorrect` during `(s, t]`. -/
def Cause (x : V) (s : ℕ) (w : V) (t : ℕ) : Prop :=
  RA (K := K) (G := G) e S x s ∧ RA (K := K) (G := G) e S w t ∧ s < t ∧ G.Adj w x ∧
    ∀ s', s < s' → s' ≤ t → e s' w = e t w ∧ ¬ AllCorrect K G (e s') w

variable {K G e S}

/-- Every reset is initial or caused by an earlier reset of a neighbour. -/
theorem initial_or_cause (hK : 3 ≤ K) (h : IsUnfairRun (next K α G) e S) {w : V} {t : ℕ}
    (hr : RA (K := K) (G := G) e S w t) : Initial K G e S w t ∨ ∃ x s, Cause K G e S x s w t := by
  let Q : ℕ → Prop := fun s => e s w = e t w ∧ ¬ AllCorrect K G (e s) w
  have hpos : 0 < e t w := hr.2.2
  have key : ∀ m, m ≤ t → (∀ s, m ≤ s → s ≤ t → Q s) →
      Initial K G e S w t ∨ ∃ x s, Cause K G e S x s w t := by
    intro m
    induction m with
    | zero => exact fun _ hQ => Or.inl ⟨hr, fun s hs => hQ s (Nat.zero_le _) hs⟩
    | succ m ih =>
      intro hm hQ
      by_cases hQm : Q m
      · exact ih (by omega) fun s h1 h2 => by
          rcases Nat.eq_or_lt_of_le h1 with rfl | h1
          · exact hQm
          · exact hQ s h1 h2
      · right
        obtain ⟨hv1, hac1⟩ := hQ (m + 1) le_rfl hm
        have hac : AllCorrect K G (e m) w := by
          rcases step_cases h m w with h1 | ⟨_, hn, _⟩ | ⟨_, hc, h1⟩ | ⟨_, h1⟩
          · by_contra hc; exact hQm ⟨h1.symm.trans hv1, hc⟩
          · exact hn.1
          · rw [phi_of_neg hc.1.2] at h1; have := hc.1.2; omega
          · omega
        obtain ⟨x, hx, hrx⟩ := exists_reset_of_allCorrect hK h hac hac1
        exact ⟨x, m, hrx, hr, by omega, hx, fun s' h1 h2 => hQ s' h1 h2⟩
  exact key t le_rfl fun s h1 h2 => by
    obtain rfl : s = t := le_antisymm h2 h1
    exact ⟨rfl, hr.2.1⟩

/-! ### Reset chains -/

variable (K G e S)

/-- A chain of resets `(w 0, τ 0) ← ⋯ ← (w L, τ L)`, starting from an initial reset. -/
def IsChain (w : ℕ → V) (τ : ℕ → ℕ) (L : ℕ) : Prop :=
  Initial K G e S (w 0) (τ 0) ∧ ∀ k < L, Cause K G e S (w k) (τ k) (w (k + 1)) (τ (k + 1))

variable {K G e S}

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsChain.ra {w : ℕ → V} {τ : ℕ → ℕ} {L : ℕ} (hc : IsChain K G e S w τ L) {k : ℕ}
    (hk : k ≤ L) : RA (K := K) (G := G) e S (w k) (τ k) := by
  rcases k with _ | k
  · exact hc.1.1
  · exact (hc.2 k (by omega)).2.1

omit [Fintype V] [DecidableRel G.Adj] in
theorem IsChain.lt {w : ℕ → V} {τ : ℕ → ℕ} {L : ℕ} (hc : IsChain K G e S w τ L) {k m : ℕ}
    (hkm : k < m) (hm : m ≤ L) : τ k < τ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    have h1 := (hc.2 m (by omega)).2.2.1
    rcases Nat.lt_succ_iff_lt_or_eq.1 hkm with h | rfl
    · exact (ih h (by omega)).trans h1
    · exact h1

/-- While `w (k+1)` is positive, its neighbour `w k`, reset at `τ k`, stays at `-α`. -/
theorem IsChain.frozen (hα : 1 ≤ α) (h : IsUnfairRun (next K α G) e S) {w : ℕ → V}
    {τ : ℕ → ℕ} {L : ℕ} (hc : IsChain K G e S w τ L) {k : ℕ} (hk : k < L) :
    ∀ s, τ k < s → s ≤ τ (k + 1) + 1 → e s (w k) = -(α : ℤ) := by
  have hC := hc.2 k hk
  have hpos : 0 < e (τ (k + 1)) (w (k + 1)) := hC.2.1.2.2
  intro s hs1 hs2
  induction s, hs1 using Nat.le_induction with
  | base => exact hC.1.succ h
  | succ s hs ih =>
    have hv := ih (by omega)
    rcases neg_cases h (show e s (w k) < 0 by rw [hv]; omega) with h1 | ⟨_, _, h1⟩
    · rw [h1, hv]
    · have := (h1 (w (k + 1)) hC.2.2.2.1.symm).1
      rw [(hC.2.2.2.2 s (by omega) (by omega)).1] at this
      omega

/-- The window lemma: the register of `w k` at times in `(τ k, τ (k+j+1) + 1]` is at most
`-α + j`. -/
theorem IsChain.window (hα : 1 ≤ α) (h : IsUnfairRun (next K α G) e S) {w : ℕ → V}
    {τ : ℕ → ℕ} {L : ℕ} (hc : IsChain K G e S w τ L) :
    ∀ j k, k + j + 1 ≤ L → j + 1 ≤ α →
      ∀ s, τ k < s → s ≤ τ (k + j + 1) + 1 → e s (w k) ≤ -(α : ℤ) + j := by
  intro j
  induction j with
  | zero =>
    intro k hk _ s h1 h2
    rw [hc.frozen hα h (by omega) s h1 h2]; simp
  | succ j ih =>
    intro k hk hjα s h1 h2
    by_cases hs : s ≤ τ (k + 1) + 1
    · rw [hc.frozen hα h (by omega) s h1 hs]; push_cast; omega
    · -- inner induction from `τ (k+1) + 1`
      have inner : ∀ s', τ (k + 1) + 1 ≤ s' → s' ≤ τ (k + (j + 1) + 1) + 1 →
          e s' (w k) ≤ -(α : ℤ) + (j + 1 : ℕ) := by
        intro s' hs1
        induction s', hs1 using Nat.le_induction with
        | base => intro _; rw [hc.frozen hα h (by omega) _ (by have := hc.lt (k := k) (m := k + 1) (by omega) (by omega); omega) le_rfl]; push_cast; omega
        | succ s' hs' ihs =>
          intro hs2
          have hv := ihs (by omega)
          have hneg : e s' (w k) < 0 := by push_cast at hv; omega
          rcases neg_cases h hneg with h1 | ⟨_, h1, hmin⟩
          · rw [h1]; exact hv
          · have hC := hc.2 k (by omega)
            have hle := (hmin (w (k + 1)) hC.2.2.2.1.symm).2
            have hnb := ih (k + 1) (by omega) (by omega) s' (by omega)
              (by rw [show k + 1 + j + 1 = k + (j + 1) + 1 by omega]; omega)
            rw [h1]; push_cast at hnb ⊢; omega
      exact inner s (by omega) h2

/-- Two resets of a chain at most `α` links apart are by different processes. -/
theorem IsChain.ne (hα : 1 ≤ α) (h : IsUnfairRun (next K α G) e S) {w : ℕ → V} {τ : ℕ → ℕ}
    {L : ℕ} (hc : IsChain K G e S w τ L) {k m : ℕ} (hkm : k < m) (hm : m ≤ L)
    (hmk : m - k ≤ α) : w k ≠ w m := by
  intro heq
  have h1 := hc.window hα h (m - k - 1) k (by omega) (by omega) (τ m) (hc.lt hkm hm)
    (by rw [show k + (m - k - 1) + 1 = m by omega]; omega)
  have h2 : 0 < e (τ m) (w m) := (hc.ra hm).2.2
  rw [← heq] at h2
  have : ((m - k - 1 : ℕ) : ℤ) = (m : ℤ) - k - 1 := by push_cast [Nat.sub_sub]; omega
  omega

/-- With `α ≥ n`, reset chains have fewer than `n` links. -/
theorem IsChain.length_lt (hα : Fintype.card V ≤ α) (hα1 : 1 ≤ α)
    (h : IsUnfairRun (next K α G) e S) {w : ℕ → V} {τ : ℕ → ℕ} {L : ℕ}
    (hc : IsChain K G e S w τ L) : L < Fintype.card V := by
  by_contra hL
  push Not at hL
  obtain ⟨i, j, hij, hw⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Fin (Fintype.card V + 1) => w k) (by simp)
  have hi := i.2
  have hj := j.2
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hl | hl
  · exact hc.ne hα1 h hl (by omega) (by omega) hw
  · exact hc.ne hα1 h hl (by omega) (by omega) hw.symm

/-! ### Finitely many resets -/

variable (K G e S) in
/-- Resets that end a chain of length `j`. -/
def chainEnds (j : ℕ) : Set (V × ℕ) :=
  {p | ∃ w τ, IsChain K G e S w τ j ∧ w j = p.1 ∧ τ j = p.2}

theorem mem_chainEnds_of_RA (hK : 3 ≤ K) (h : IsUnfairRun (next K α G) e S) :
    ∀ t v, RA (K := K) (G := G) e S v t → ∃ j, (v, t) ∈ chainEnds K G e S j := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hr
    rcases initial_or_cause hK h hr with hi | ⟨x, s, hC⟩
    · exact ⟨0, fun _ => v, fun _ => t, ⟨hi, fun k hk => absurd hk (Nat.not_lt_zero _)⟩, rfl, rfl⟩
    · obtain ⟨j, w, τ, hc, hw, hτ⟩ := ih s hC.2.2.1 x hC.1
      refine ⟨j + 1, fun k => if k ≤ j then w k else v, fun k => if k ≤ j then τ k else t,
        ⟨by simpa using hc.1, fun k hk => ?_⟩, by simp, by simp⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · simpa [show k ≤ j by omega, show k + 1 ≤ j by omega] using hc.2 k hk
      · simpa [hw, hτ] using hC

theorem chainEnds_finite (h : IsUnfairRun (next K α G) e S) (j : ℕ) :
    (chainEnds K G e S j).Finite := by
  induction j with
  | zero =>
    apply Set.Finite.of_finite_image (f := Prod.fst) (Set.toFinite _)
    rintro ⟨v, t⟩ ⟨w, τ, hc, hw, hτ⟩ ⟨v', t'⟩ ⟨w', τ', hc', hw', hτ'⟩ hfst
    simp only at hw hτ hw' hτ' hfst
    have hi : Initial K G e S v t := hw ▸ hτ ▸ hc.1
    have hi' : Initial K G e S v t' := hfst ▸ hw' ▸ hτ' ▸ hc'.1
    simp only [Prod.mk.injEq]
    refine ⟨hfst, ?_⟩
    by_contra hne
    -- two initial resets of the same process
    have key : ∀ a b, Initial K G e S v a → Initial K G e S v b → a < b → False := by
      intro a b ha hb hab
      have h1 := (hb.2 a hab.le).1
      have h2 := (hb.2 (a + 1) hab).1
      rw [ha.1.succ h] at h2
      have := ha.1.2.2
      omega
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact key _ _ hi hi' hl
    · exact key _ _ hi' hi hl
  | succ j ih =>
    have hsub : chainEnds K G e S (j + 1) ⊆
        ⋃ p ∈ chainEnds K G e S j, ⋃ v : V, {q | q.1 = v ∧ Cause K G e S p.1 p.2 q.1 q.2} := by
      rintro ⟨v, t⟩ ⟨w, τ, hc, hw, hτ⟩
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
      refine ⟨(w j, τ j), ⟨w, τ, ⟨hc.1, fun k hk => hc.2 k (by omega)⟩, rfl, rfl⟩, v, rfl, ?_⟩
      simpa [hw, hτ] using hc.2 j (by omega)
    refine Set.Finite.subset (Set.Finite.biUnion ih fun p _ => Set.finite_iUnion fun v => ?_) hsub
    apply Set.Subsingleton.finite
    rintro ⟨v1, t1⟩ ⟨hv1, hc1⟩ ⟨v2, t2⟩ ⟨hv2, hc2⟩
    simp only at hv1 hv2 hc1 hc2
    have h12 : v2 = v1 := hv2.trans hv1.symm
    subst h12
    simp only [Prod.mk.injEq, true_and]
    by_contra hne
    have key : ∀ (x : V) a b, Cause K G e S p.1 p.2 x a → Cause K G e S p.1 p.2 x b → a < b →
        False := by
      intro x a b ha hb hab
      have h1 := (hb.2.2.2.2 a ha.2.2.1 hab.le).1
      have h2 := (hb.2.2.2.2 (a + 1) (by have := ha.2.2.1; omega) hab).1
      rw [ha.2.1.succ h] at h2
      have := ha.2.1.2.2
      omega
    rcases lt_or_gt_of_ne hne with hl | hl
    · exact key _ _ _ hc1 hc2 hl
    · exact key _ _ _ hc2 hc1 hl

/-- With `α ≥ n`, a run executes `RA` only finitely often. -/
theorem eventually_no_reset (hK : 3 ≤ K) (hα : Fintype.card V ≤ α) (hα1 : 1 ≤ α)
    (h : IsUnfairRun (next K α G) e S) :
    ∃ T, ∀ t, T ≤ t → ∀ v, ¬ RA (K := K) (G := G) e S v t := by
  have hfin : (⋃ j ∈ Finset.range (Fintype.card V), chainEnds K G e S j).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun j _ => chainEnds_finite h j
  obtain ⟨M, hM⟩ := (hfin.image Prod.snd).bddAbove
  refine ⟨M + 1, fun t ht v hr => ?_⟩
  obtain ⟨j, hj⟩ := mem_chainEnds_of_RA hK h t v hr
  have hjn : j < Fintype.card V := by
    obtain ⟨w, τ, hc, -, -⟩ := hj
    exact hc.length_lt hα hα1 h
  have : t ≤ M := hM ⟨(v, t), Set.mem_biUnion (by simpa using hjn) hj, rfl⟩
  omega

end Causes

/-! ### Freezing and propagation of eventual constancy -/

section Freeze

/-- After finitely many `RA` and `CA`, every move is an `NA` increment. -/
theorem eventually_only_NA (hK : 3 ≤ K) (hα : Fintype.card V ≤ α) (hα1 : 1 ≤ α)
    (h : IsUnfairRun (next K α G) e S) :
    ∃ T, ∀ t, T ≤ t → ∀ v, ¬ RA (K := K) (G := G) e S v t ∧
      (e (t + 1) v = e t v ∨ (NormalStep K G (e t) v ∧ e (t + 1) v = succK K (e t v))) := by
  obtain ⟨T, hT⟩ := eventually_no_reset hK hα hα1 h
  -- negative registers stop moving
  have hneg : ∀ v, ∃ Tv, ∀ m ≥ Tv, ¬ (e m v < 0 ∧ e (m + 1) v ≠ e m v) := by
    intro v
    let f : ℕ → ℕ := fun t => (-e t v).toNat
    have hdec : ∀ m ≥ T, f (m + 1) ≤ f m := by
      intro m hm
      simp only [f]
      by_cases hv : e m v < 0
      · rcases neg_cases h hv with h1 | ⟨_, h1, _⟩ <;> rw [h1] <;> omega
      · rcases nonneg_cases h (not_lt.1 hv) (hT m hm v) with h1 | ⟨_, _, h1⟩ <;> rw [h1] <;>
          (try unfold succK) <;> (try split_ifs) <;> omega
    obtain ⟨Tv, -, hTv⟩ := Nat.eventually_not_of_succ_le hdec
      (p := fun m => e m v < 0 ∧ e (m + 1) v ≠ e m v) (fun m _ ⟨hv, hne⟩ => by
        simp only [f]
        rcases neg_cases h hv with h1 | ⟨_, h1, _⟩
        · exact absurd h1 hne
        · rw [h1]; omega)
    exact ⟨Tv, hTv⟩
  obtain ⟨T', hT'T, hT'⟩ := Nat.eventually_forall_of_finite hneg T
  refine ⟨T', fun t ht v => ⟨hT t (by omega) v, ?_⟩⟩
  by_cases hv : e t v < 0
  · exact Or.inl (by by_contra hne; exact hT' t ht v ⟨hv, hne⟩)
  · rcases nonneg_cases h (not_lt.1 hv) (hT t (by omega) v) with h1 | ⟨_, hn, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hn, h1⟩

omit [Fintype V] [DecidableRel G.Adj] in
/-- If `u` is eventually constant, its neighbour `w` only makes `NA` moves and is
`allCorrect` from `T` on, then `w` is eventually constant (it moves at most twice). -/
theorem evConst_of_adj (hK : 3 ≤ K) {T : ℕ}
    (hmove : ∀ t, T ≤ t → ∀ v, e (t + 1) v = e t v ∨
      (NormalStep K G (e t) v ∧ e (t + 1) v = succK K (e t v)))
    {u w : V} (hadj : G.Adj w u) {Tu : ℕ} (hTu : T ≤ Tu) (hu : ∀ t, Tu ≤ t → e t u = e Tu u)
    (hw : ∀ t, T ≤ t → AllCorrect K G (e t) w) : ∃ Tw, ∀ t, Tw ≤ t → e t w = e Tw w := by
  set c := e Tu u
  let rank : ℤ → ℕ := fun x => if x = c then 1 else if succK K x = c then 2 else 0
  have hcor : ∀ t, Tu ≤ t → Correct K (e t w) c := fun t ht => by
    rw [← hu t ht]; exact hw t (by omega) u hadj
  have hstep : ∀ t, Tu ≤ t → e (t + 1) w ≠ e t w → rank (e (t + 1) w) < rank (e t w) := by
    intro t ht hne
    rcases hmove t (by omega) w with h1 | ⟨hn, h1⟩
    · exact absurd h1 hne
    have hl := hn.2 u hadj
    rw [hu t ht] at hl
    obtain ⟨⟨hx0, hxK⟩, ⟨hc0, hcK⟩, -⟩ := hcor t ht
    have hss : succK K (succK K c) ≠ c :=
      succK_iterate_ne (m := 2) (by omega) hc0 hcK (by omega) (by omega)
    have hs := succK_ne_self (by omega) hc0 hcK
    rw [h1]
    rcases hl with hl | hl
    · rw [← hl]; simp [rank, hs, hss]
    · have hxc : e t w ≠ c := by
        intro hxc; rw [hxc] at hl; exact succK_ne_self (by omega) hc0 hcK hl.symm
      simp [rank, hxc, ← hl]
  have hdec : ∀ t ≥ Tu, rank (e (t + 1) w) ≤ rank (e t w) := by
    intro t ht
    by_cases hne : e (t + 1) w = e t w
    · rw [hne]
    · exact (hstep t ht hne).le
  obtain ⟨Tw, hTw1, hTw⟩ := Nat.eventually_not_of_succ_le (f := fun t => rank (e t w)) hdec
    (p := fun t => e (t + 1) w ≠ e t w) (fun t ht hne => hstep t ht hne)
  refine ⟨Tw, fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [← ih]; by_contra hne; exact hTw t ht hne

omit [Fintype V] [DecidableRel G.Adj] in
/-- Eventual constancy spreads from one process to the whole connected graph. -/
theorem evConst_all (hK : 3 ≤ K) (hconn : G.Connected) {T : ℕ}
    (hmove : ∀ t, T ≤ t → ∀ v, e (t + 1) v = e t v ∨
      (NormalStep K G (e t) v ∧ e (t + 1) v = succK K (e t v)))
    (hdich : ∀ v, (∀ t, T ≤ t → e t v = e T v) ∨ ∀ t, T ≤ t → AllCorrect K G (e t) v)
    {b : V} (hb : ∀ t, T ≤ t → e t b = e T b) :
    ∀ v, ∃ Tv, T ≤ Tv ∧ ∀ t, Tv ≤ t → e t v = e Tv v := by
  intro v
  obtain ⟨p⟩ := hconn.preconnected v b
  induction p with
  | nil => exact ⟨T, le_rfl, hb⟩
  | @cons w x _ hadj p ih =>
    obtain ⟨Tx, hTx, hx⟩ := ih hb
    rcases hdich w with hw | hw
    · exact ⟨T, le_rfl, hw⟩
    · obtain ⟨Tw, hTw⟩ := evConst_of_adj hK hmove hadj hTx hx hw
      refine ⟨max T Tw, le_max_left _ _, fun t ht => ?_⟩
      rw [hTw t (by omega), hTw (max T Tw) (le_max_right _ _)]

/-- If every process is eventually constant, the run reaches a terminal configuration. -/
theorem terminal_of_evConst (h : IsUnfairRun (next K α G) e S)
    (hc : ∀ v, ∃ Tv, ∀ t, Tv ≤ t → e t v = e Tv v) :
    ∃ T, Terminal (next K α G) (e T) := by
  obtain ⟨T, -, hT⟩ := Nat.eventually_forall_of_finite
    (p := fun v m => e m v = e (m + 1) v) (fun v => by
      obtain ⟨Tv, hTv⟩ := hc v
      exact ⟨Tv, fun m hm => by rw [hTv m hm, hTv (m + 1) (by omega)]⟩) 0
  refine ⟨T, h.terminal_of_const fun t ht => ?_⟩
  induction t, ht using Nat.le_induction with
  | base => rfl
  | succ t ht ih => rw [← ih]; funext v; exact (hT t ht v).symm

end Freeze

/-! ### Convergence and liveness -/

section Main

variable [Nonempty V]

/-- **Convergence under the distributed unfair daemon** (for `α ≥ n`, `K > n`): every run from a
valid configuration reaches `Γ₁`. -/
theorem exists_legit (hK : 3 ≤ K) (hα : Fintype.card V ≤ α) (hcard : Fintype.card V < K)
    (hconn : G.Connected) (h : IsUnfairRun (next K α G) e S) (h0 : Valid K α (e 0)) :
    ∃ t, Legit K G (e t) := by
  have hα1 : 1 ≤ α := le_trans Fintype.card_pos hα
  obtain ⟨T, hT⟩ := eventually_only_NA hK hα hα1 h
  by_contra hno
  push Not at hno
  have hmove := fun t ht v => (hT t ht v).2
  -- non-`allCorrect` processes are frozen, `allCorrect` ones stay `allCorrect`
  have hfrozen : ∀ v, ¬ AllCorrect K G (e T) v →
      ∀ t, T ≤ t → e t v = e T v ∧ ¬ AllCorrect K G (e t) v := by
    intro v hv t ht
    induction t, ht using Nat.le_induction with
    | base => exact ⟨rfl, hv⟩
    | succ t ht ih =>
      have hst : e (t + 1) v = e t v := by
        rcases hmove t ht v with h1 | ⟨hn, _⟩
        · exact h1
        · exact absurd hn.1 ih.2
      refine ⟨hst.trans ih.1, fun hac => ?_⟩
      apply ih.2
      intro u hu
      by_contra hnc
      have hc1 := hac u hu
      rw [hst] at hc1
      rcases hmove t ht u with h1 | ⟨hn, _⟩
      · rw [h1] at hc1; exact hnc hc1
      · exact hnc (hn.1 v hu.symm).symm
  have hkeep : ∀ v, AllCorrect K G (e T) v → ∀ t, T ≤ t → AllCorrect K G (e t) v := by
    intro v hv t ht
    induction t, ht using Nat.le_induction with
    | base => exact hv
    | succ t ht ih =>
      by_contra hac
      obtain ⟨u, -, hr⟩ := exists_reset_of_allCorrect hK h ih hac
      exact (hT t ht u).1 hr
  obtain ⟨b, hb⟩ : ∃ b, ¬ AllCorrect K G (e T) b := by
    by_contra hall; push Not at hall; exact hno T hall
  have hdich : ∀ v, (∀ t, T ≤ t → e t v = e T v) ∨ ∀ t, T ≤ t → AllCorrect K G (e t) v := by
    intro v
    by_cases hv : AllCorrect K G (e T) v
    · exact Or.inr (hkeep v hv)
    · exact Or.inl fun t ht => (hfrozen v hv t ht).1
  have hall := evConst_all hK hconn hmove hdich (fun t ht => (hfrozen b hb t ht).1)
  obtain ⟨T', hT'⟩ := terminal_of_evConst h fun v =>
    let ⟨Tv, _, h'⟩ := hall v; ⟨Tv, h'⟩
  exact not_terminal hcard (valid_run (by omega) h h0 T') hT'

/-- **Liveness in `Γ₁`**: once legitimate, every process is activated infinitely often. -/
theorem live_of_legit (hK : 3 ≤ K) (hcard : Fintype.card V < K) (hconn : G.Connected)
    (hdeg : ∀ v, ∃ u, G.Adj v u) (h : IsUnfairRun (next K α G) e S) (h0 : Valid K α (e 0))
    {T0 : ℕ} (hL : Legit K G (e T0)) : ∀ v T, ∃ t, T ≤ t ∧ v ∈ S t := by
  intro v T
  by_contra hno
  push Not at hno
  set T1 := max T T0
  have hLt : ∀ t, T1 ≤ t → Legit K G (e t) := fun t ht => legit_run hK h hL t (by omega)
  have hmove : ∀ t, T1 ≤ t → ∀ w, e (t + 1) w = e t w ∨
      (NormalStep K G (e t) w ∧ e (t + 1) w = succK K (e t w)) := by
    intro t ht w
    obtain ⟨u, hu⟩ := hdeg w
    have h0w : 0 ≤ e t w := (hLt t ht w u hu).1.1
    rcases nonneg_cases h h0w (fun hr => hr.2.1 (hLt t ht w)) with h1 | ⟨_, hn, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hn, h1⟩
  have hv : ∀ t, T1 ≤ t → e t v = e T1 v := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [h.stay t v (hno t (by omega)), ih]
  have hall := evConst_all hK hconn hmove (fun w => Or.inr fun t ht => hLt t ht w) hv
  obtain ⟨T', hT'⟩ := terminal_of_evConst h fun w =>
    let ⟨Tw, _, h'⟩ := hall w; ⟨Tw, h'⟩
  exact not_terminal hcard (valid_run (by omega) h h0 T') hT'

/-- **Liveness in `Γ₁`, value form**: once legitimate, every process `v` is activated infinitely
often while its register holds `c`, for every `c ∈ stab`. -/
theorem visits_of_legit (hK : 3 ≤ K) (hcard : Fintype.card V < K) (hconn : G.Connected)
    (hdeg : ∀ v, ∃ u, G.Adj v u) (h : IsUnfairRun (next K α G) e S) (h0 : Valid K α (e 0))
    {T0 : ℕ} (hL : Legit K G (e T0)) (v : V) {c : ℤ} (hc0 : 0 ≤ c) (hcK : c < K) :
    ∀ T, ∃ t, T ≤ t ∧ e t v = c ∧ v ∈ S t := by
  have hlive := live_of_legit hK hcard hconn hdeg h h0 hL
  obtain ⟨u, hu⟩ := hdeg v
  have hnn : ∀ t, T0 ≤ t → 0 ≤ e t v ∧ e t v < K := fun t ht =>
    ⟨(legit_run hK h hL t ht v u hu).1.1, (legit_run hK h hL t ht v u hu).1.2⟩
  -- the first activation of `v` after `T` happens with the register still at `e T v`
  have hfirst : ∀ T, T0 ≤ T → ∃ t, T ≤ t ∧ v ∈ S t ∧ e t v = e T v ∧
      e (t + 1) v = succK K (e T v) := by
    intro T hT
    classical
    have hex : ∃ t, T ≤ t ∧ v ∈ S t := hlive v T
    let t := Nat.find hex
    have ht := Nat.find_spec hex
    have hconst : ∀ s, T ≤ s → s ≤ t → e s v = e T v := by
      intro s hs1
      induction s, hs1 using Nat.le_induction with
      | base => intro _; rfl
      | succ s hs ih =>
        intro hs2
        have : v ∉ S s := fun hm => Nat.find_min hex (show s < t by omega) ⟨hs, hm⟩
        rw [h.stay s v this, ih (by omega)]
    have hvt := hconst t ht.1 le_rfl
    refine ⟨t, ht.1, ht.2, hvt, ?_⟩
    rcases nonneg_cases h (hnn t (by omega)).1
      (fun hr => hr.2.1 (legit_run hK h hL t (by omega) v)) with h1 | ⟨_, _, h1⟩
    · exact absurd (by rw [h.move t v ht.2] at h1; exact h1) (h.enabled t v ht.2)
    · rw [h1, hvt]
  have key : ∀ m T, T0 ≤ T → (succK K)^[m] (e T v) = c → ∃ t, T ≤ t ∧ e t v = c ∧ v ∈ S t := by
    intro m
    induction m with
    | zero =>
      intro T hT hm
      obtain ⟨t, ht, hS, hval, -⟩ := hfirst T hT
      exact ⟨t, ht, by rw [hval]; exact hm, hS⟩
    | succ m ih =>
      intro T hT hm
      obtain ⟨t, ht, -, -, hsucc⟩ := hfirst T hT
      obtain ⟨t', ht', h'⟩ := ih (t + 1) (by omega) (by rw [hsucc, ← Function.iterate_succ_apply]; exact hm)
      exact ⟨t', by omega, h'⟩
  intro T
  set T1 := max T T0
  obtain ⟨x0, xK⟩ := hnn T1 (le_max_right _ _)
  set x := e T1 v
  let m : ℕ := if x ≤ c then (c - x).toNat else (c - x + K).toNat
  have hm : m < K := by simp only [m]; split_ifs <;> omega
  have hit : (succK K)^[m] x = c := by
    rw [succK_iterate x0 xK hm]
    simp only [m]; split_ifs <;> omega
  obtain ⟨t, ht, h'⟩ := key m T1 (le_max_right _ _) hit
  exact ⟨t, by omega, h'⟩

end Main

end Cslib.SelfStabilization.ResetUnison
