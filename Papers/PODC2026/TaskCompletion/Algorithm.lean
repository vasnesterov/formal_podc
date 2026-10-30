import Papers.PODC2026.TaskCompletion.Basic

/-!
# Algorithm 1 (iterative task completion) and its analysis (Section 4.1–4.2)

Fischer, Gelles, *The Task Completion Problem and its Application to Crash-Resilient
Computation* (PODC 2026, arXiv:2605.17961), Section 4.

## Model (iteration level)

`n` nodes `Fin n`, `m` tasks `Fin m`. Algorithm 1 proceeds in iterations; iteration `j` of the
algorithm consists of a *task phase* of `2BR` rounds (line 11: node `v` completes the tasks of
`U_{j,v}` one after the other, each taking `R` rounds, so it completes all of them iff it does
not crash during the phase and `|U_{j,v}| ≤ 2B`) followed by one *broadcast round* (lines 12–17).
We model one iteration as one step; the round count is `2BR + 1` per iteration.

The (adaptive, deterministic-algorithm) crash adversary is a function of the node: `crashIter v`
is the (global) iteration in which `v` crashes (`none`: never); if `v` crashes in iteration `c`,
`fin v` says whether it survived the task phase of iteration `c` (so it completed its tasks and
sends its bit), and `reach v` is the set of nodes that receive its broadcast bit in iteration `c`
(an arbitrary subset, as in the paper's crash model: a node crashing during a round sends an
arbitrary subset of its messages of that round). A node crashed in an earlier iteration does
nothing. Since the algorithm is deterministic, quantifying over all such functions is the same as
quantifying over all adaptive adversaries.

The run starts at global iteration `s` (to compose batches, Section 4.3); `j` is the local
iteration index. All nodes agree on the families `F k` (the `(k,B,ε)`-load balancing covering
families of line 7, a parameter of the algorithm, existing by Lemma 3.1).

* `C j v` — `C_{j,v}`, the tasks `v` knows to be complete at the start of local iteration `j`;
* `Done j` — tasks *actually* completed during the first `j` iterations. We only count the tasks of
  `U_{j,u}` for nodes `u` that complete their whole list (an under-approximation of the
  completed tasks; the theorems say that all tasks are in `Done`, so this only strengthens them).
* `FV j t` — `t` is *fully verified* at the start of iteration `j`; `N j` — number of tasks not
  fully verified (`N_j` of the paper).

Indices: the paper's iteration `i` is our `j = i - 1`, so `k_i = ⌈(1-ε)^{i-1} m⌉` is our
`kk j = ⌈(1-ε)^j m⌉`.
-/

open Finset

namespace Podc.TaskCompletion.Alg

/-- A crash adversary for `n` nodes (see the module docstring). -/
structure Adversary (n : ℕ) where
  /-- The (global) iteration during which the node crashes, `none` if it never crashes. -/
  crashIter : Fin n → Option ℕ
  /-- For a node crashing in iteration `c`: whether it survived the task phase of iteration `c`. -/
  fin : Fin n → Prop
  /-- For a node crashing in iteration `c`: the receivers of its broadcast bit in iteration `c`. -/
  reach : Fin n → Set (Fin n)

namespace Adversary

variable {n : ℕ} (adv : Adversary n)

/-- `v` has not crashed before (global) iteration `i`. -/
def AliveAt (i : ℕ) (v : Fin n) : Prop := ∀ c, adv.crashIter v = some c → i ≤ c

open Classical in
/-- The nodes that crash at some point. -/
noncomputable def faulty : Finset (Fin n) := univ.filter fun v => adv.crashIter v ≠ none

/-- At most `α n` nodes crash. -/
def Admissible (α : ℝ) : Prop := (#adv.faulty : ℝ) ≤ α * n

variable {adv}

lemma AliveAt.mono {i i' : ℕ} {v : Fin n} (h : adv.AliveAt i v) (hi : i' ≤ i) :
    adv.AliveAt i' v := fun c hc => hi.trans (h c hc)

lemma mem_faulty_of_not_aliveAt {i : ℕ} {v : Fin n} (h : ¬ adv.AliveAt i v) :
    v ∈ adv.faulty := by
  classical
  simp only [AliveAt, not_forall] at h
  obtain ⟨c, hc, -⟩ := h
  simp [faulty, hc]

lemma aliveAt_of_not_mem_faulty {v : Fin n} (h : v ∉ adv.faulty) (i : ℕ) : adv.AliveAt i v :=
  by_contra fun h' => h (mem_faulty_of_not_aliveAt h')

end Adversary

/-- The parameters of Algorithm 1: `B`, `ε` and the agreed-upon covering families `F k`
(the family used in an iteration with `k_i = k`). -/
structure Params (n m : ℕ) where
  B : ℕ
  ε : ℝ
  F : ℕ → Fin m → Finset (Fin n)

open Classical

variable {n m : ℕ} (P : Params n m) (adv : Adversary n) (s : ℕ)

/-- `k_i = ⌈(1 - ε)^{i-1} m⌉` (line 3), with the local iteration `j = i - 1`. -/
noncomputable def kk (j : ℕ) : ℕ := ⌈(1 - P.ε) ^ j * m⌉₊

/-- `T_{j,v}` (lines 4–9): all tasks if `k ≤ 2B`, otherwise the tasks `t` with `v ∈ A_t`. -/
noncomputable def T (j : ℕ) (v : Fin n) : Finset (Fin m) :=
  if kk P j ≤ 2 * P.B then univ else univ.filter fun t => v ∈ P.F (kk P j) t

/-- Node `u` completes all of `U_{j,u} = T_{j,u} \ C_{j,u}` in the task phase of iteration `j`
(line 11) and therefore broadcasts `s_{j,u} = 1`: it survives the task phase and
`|U_{j,u}| ≤ 2B`. (`Cj` is the current knowledge `C_j`.) -/
def Succ (Cj : Fin n → Finset (Fin m)) (j : ℕ) (u : Fin n) : Prop :=
  (adv.AliveAt (s + j + 1) u ∨ adv.fin u) ∧ #(T P j u \ Cj u) ≤ 2 * P.B

/-- `v` receives `s_{j,u} = 1` (line 17): `u` was alive at the start of the iteration, succeeded,
and either survives the iteration or `v` is among the receivers of its last broadcast. -/
def Recv (Cj : Fin n → Finset (Fin m)) (j : ℕ) (u v : Fin n) : Prop :=
  adv.AliveAt (s + j) u ∧ Succ P adv s Cj j u ∧ (adv.AliveAt (s + j + 1) u ∨ v ∈ adv.reach u)

/-- `C_{j,v}` (lines 1 and 19). -/
noncomputable def C : ℕ → Fin n → Finset (Fin m)
  | 0 => fun _ => ∅
  | j + 1 => fun v => C j v ∪ (univ.filter fun u => Recv P adv s (C j) j u v).biUnion (T P j)

/-- The tasks completed during the first `j` iterations (under-approximation, see module doc). -/
noncomputable def Done : ℕ → Finset (Fin m)
  | 0 => ∅
  | j + 1 => Done j ∪ (univ.filter fun u => adv.AliveAt (s + j) u ∧ Succ P adv s (C P adv s j) j u).biUnion
      fun u => T P j u \ C P adv s j u

/-- Task `t` is *fully verified* at the start of iteration `j`: it belongs to `C_{j,v}` for every
node `v` that has not crashed by then. -/
def FV (j : ℕ) (t : Fin m) : Prop := ∀ v, adv.AliveAt (s + j) v → t ∈ C P adv s j v

/-- `N_j`: the number of tasks that are not fully verified at the start of iteration `j`. -/
noncomputable def N (j : ℕ) : ℕ := #(univ.filter fun t => ¬ FV P adv s j t)

/-! ### Basic properties -/

variable {P adv s}

lemma C_succ (j : ℕ) (v : Fin n) :
    C P adv s (j + 1) v =
      C P adv s j v ∪ (univ.filter fun u => Recv P adv s (C P adv s j) j u v).biUnion (T P j) :=
  rfl

lemma C_mono (j : ℕ) (v : Fin n) : C P adv s j v ⊆ C P adv s (j + 1) v := by
  rw [C_succ]; exact subset_union_left

lemma Done_mono (j : ℕ) : Done P adv s j ⊆ Done P adv s (j + 1) := by
  intro t ht; simp only [Done]; exact mem_union_left _ ht

lemma Done_mono' {j j' : ℕ} (h : j ≤ j') : Done P adv s j ⊆ Done P adv s j' := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (Done_mono _)

lemma FV.succ {j : ℕ} {t : Fin m} (h : FV P adv s j t) : FV P adv s (j + 1) t := fun v hv =>
  C_mono j v (h v (hv.mono (by omega)))

lemma N_succ_le (j : ℕ) : N P adv s (j + 1) ≤ N P adv s j := by
  unfold N
  exact card_le_card fun t ht => by
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    exact fun h => ht h.succ

/-- **Claim 4.2.** For every non-crashed `v`, `|C_{j,v}| ≥ m - N_j`. -/
theorem claim_4_2 (j : ℕ) {v : Fin n} (hv : adv.AliveAt (s + j) v) :
    m - N P adv s j ≤ #(C P adv s j v) := by
  have h : (univ.filter fun t => FV P adv s j t) ⊆ C P adv s j v := fun t ht => by
    simp only [mem_filter, mem_univ, true_and] at ht; exact ht v hv
  have h2 := card_le_card h
  have h3 := card_filter_add_card_filter_not (s := (univ : Finset (Fin m)))
    (fun t => FV P adv s j t)
  simp only [card_univ, Fintype.card_fin] at h3
  unfold N; omega

/-- **Lemma 4.4.** Every task in some `C_{j,v}` has been completed before iteration `j`. -/
theorem lemma_4_4 (j : ℕ) (v : Fin n) : C P adv s j v ⊆ Done P adv s j := by
  induction j generalizing v with
  | zero => simp [C]
  | succ j ih =>
    intro t ht
    rw [C_succ, mem_union] at ht
    rcases ht with ht | ht
    · exact Done_mono j (ih v ht)
    · obtain ⟨u, hu, htu⟩ := mem_biUnion.mp ht
      simp only [mem_filter, mem_univ, true_and] at hu
      by_cases hc : t ∈ C P adv s j u
      · exact Done_mono j (ih u hc)
      · simp only [Done]
        refine mem_union_right _ (mem_biUnion.mpr ⟨u, ?_, mem_sdiff.mpr ⟨htu, hc⟩⟩)
        simp only [mem_filter, mem_univ, true_and]
        exact ⟨hu.1, hu.2.1⟩

/-- Tasks not yet known to be complete by a live node are not fully verified. -/
lemma sdiff_subset_notFV {j : ℕ} {v : Fin n} (hv : adv.AliveAt (s + j) v) :
    T P j v \ C P adv s j v ⊆ (T P j v).filter fun t => ¬ FV P adv s j t := by
  intro t ht
  rw [mem_sdiff] at ht
  exact mem_filter.mpr ⟨ht.1, fun h => ht.2 (h v hv)⟩

/-- If a node survives iteration `j` and has at most `2B` tasks to do, all its tasks become fully
verified. -/
lemma FV_of_survivor {j : ℕ} {v : Fin n} (hv : adv.AliveAt (s + j + 1) v)
    (hU : #(T P j v \ C P adv s j v) ≤ 2 * P.B) {t : Fin m} (ht : t ∈ T P j v) :
    FV P adv s (j + 1) t := by
  intro w _
  rw [C_succ]
  refine mem_union_right _ (mem_biUnion.mpr ⟨v, ?_, ht⟩)
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨hv.mono (by omega), ⟨Or.inl hv, hU⟩, Or.inl hv⟩

/-! ### Lemma 4.5 -/

/-- Lemma 4.5, claim (b), first case: if `k_j ≤ 2B` (all tasks assigned to all nodes) and
`N_j ≤ k_j`, then all tasks are fully verified after the iteration. -/
theorem N_succ_eq_zero_of_small {j : ℕ} (hk : kk P j ≤ 2 * P.B) (hN : N P adv s j ≤ kk P j) :
    N P adv s (j + 1) = 0 := by
  unfold N
  rw [card_eq_zero, filter_eq_empty_iff]
  intro t _ hnot
  apply hnot
  intro w hw
  have hT : T P j w = univ := by simp [T, hk]
  have hU : #(T P j w \ C P adv s j w) ≤ 2 * P.B := by
    refine le_trans (card_le_card (sdiff_subset_notFV (hw.mono (by omega)))) ?_
    rw [hT]; unfold N at hN; omega
  exact FV_of_survivor (P := P) hw hU (by rw [hT]; exact mem_univ t) w hw

/-- Double counting of incidences. -/
lemma sum_card_filter_comm {α β : Type*} (X : Finset α) (Y : Finset β) (R : α → β → Prop)
    [∀ a b, Decidable (R a b)] :
    ∑ x ∈ X, #(Y.filter fun y => R x y) = ∑ y ∈ Y, #(X.filter fun x => R x y) := by
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- Lemma 4.5, claim (b), second case: if `k_j > 2B` and `(1-ε)k_j ≤ N_j ≤ k_j`, then at least
`ε k_j` tasks become fully verified in iteration `j`. Here `hprog` is our form of the paper's
choice "`(1 - 4ε - (1+ε)α)/2 ≥ ε`" (we count the crashed nodes of `J` slightly differently). -/
theorem N_succ_le_of_large {α : ℝ} (hadv : adv.Admissible α) (hn : 0 < n) (hB : 1 ≤ P.B)
    (hε0 : 0 < P.ε) (hε1 : P.ε ≤ 1) (hprog : 4 * P.ε ≤ (1 - P.ε - α) * (1 - P.ε))
    {j : ℕ} (hk : 2 * P.B < kk P j) (hkm : kk P j ≤ m)
    (hF : IsLBCF n m (kk P j) P.B P.ε (P.F (kk P j)))
    (hN1 : (1 - P.ε) * kk P j ≤ N P adv s j) (hN2 : N P adv s j ≤ kk P j) :
    (N P adv s (j + 1) : ℝ) ≤ N P adv s j - P.ε * kk P j := by
  set k := kk P j with hkdef
  set F := P.F k with hFdef
  set B := P.B
  set ε := P.ε
  set I := univ.filter fun t => ¬ FV P adv s j t with hI
  have hIcard : #I = N P adv s j := rfl
  obtain ⟨I', hII', hI'⟩ := exists_superset_card_eq (s := I) (n := k) (by omega)
    (by simpa using hkm)
  obtain ⟨J, hJ, hJload⟩ := hF.balanced I' hI'
  set G := J.filter fun v => adv.AliveAt (s + j + 1) v with hG
  set S := I.filter fun t => ∃ v ∈ G, v ∈ F t with hS
  have hTv : ∀ v, T P j v = univ.filter fun t => v ∈ F t := by
    intro v; simp only [T, show ¬ kk P j ≤ 2 * P.B by omega, ite_false]; rfl
  -- every task of `S` becomes fully verified
  have hSFV : ∀ t ∈ S, FV P adv s (j + 1) t := by
    intro t ht
    obtain ⟨-, v, hvG, hvt⟩ := mem_filter.mp ht
    obtain ⟨hvJ, hvA⟩ := mem_filter.mp hvG
    have hU : #(T P j v \ C P adv s j v) ≤ 2 * B := by
      have h1 := card_le_card (sdiff_subset_notFV (P := P) (hvA.mono (by omega) :
        adv.AliveAt (s + j) v))
      have h2 : (T P j v).filter (fun t => ¬ FV P adv s j t) ⊆ I'.filter fun t => v ∈ F t := by
        intro t ht
        rw [mem_filter, hTv, mem_filter] at ht
        exact mem_filter.mpr ⟨hII' (by simpa [hI] using ht.2), ht.1.2⟩
      have h3 := card_le_card h2
      have h4 := (hJload v hvJ).2
      have h5 : (load F I' v : ℝ) ≤ 2 * B := by
        have : (0 : ℝ) ≤ B := by positivity
        nlinarith
      have h6 : load F I' v ≤ 2 * B := by exact_mod_cast h5
      unfold load at h6
      omega
    exact FV_of_survivor hvA hU (by rw [hTv]; simpa using hvt)
  -- hence `N_{j+1} ≤ N_j - |S|`
  have hSI : S ⊆ I := filter_subset _ _
  have hN' : N P adv s (j + 1) + #S ≤ N P adv s j := by
    have hsub : (univ.filter fun t => ¬ FV P adv s (j + 1) t) ⊆ I \ S := by
      intro t ht
      simp only [mem_filter, mem_univ, true_and] at ht
      refine mem_sdiff.mpr ⟨?_, fun h => ht (hSFV t h)⟩
      simp only [hI, mem_filter, mem_univ, true_and]
      exact fun h => ht h.succ
    have h1 := card_le_card hsub
    rw [card_sdiff_of_subset hSI] at h1
    have h2 := card_le_card hSI
    have h3 : N P adv s (j + 1) = #(univ.filter fun t => ¬ FV P adv s (j + 1) t) := rfl
    omega
  -- counting
  have hkpos : (0 : ℝ) < k := by have : 0 < k := by omega
                                 exact_mod_cast this
  have hFle : ∀ t, (#(F t) : ℝ) ≤ 2 * n * B / k := hF.card_le
  -- (i) incidences between `I` and `G` are at most `|S| · 2nB/k`
  have hupper : (∑ t ∈ I, (#(G.filter fun v => v ∈ F t) : ℝ)) ≤ #S * (2 * n * B / k) := by
    have h1 : ∑ t ∈ I, (#(G.filter fun v => v ∈ F t) : ℝ) =
        ∑ t ∈ S, (#(G.filter fun v => v ∈ F t) : ℝ) := by
      refine (sum_subset hSI fun t htI htS => ?_).symm
      have : G.filter (fun v => v ∈ F t) = ∅ := by
        rw [filter_eq_empty_iff]
        intro v hv hvt
        exact htS (mem_filter.mpr ⟨htI, v, hv, hvt⟩)
      simp [this]
    rw [h1]
    calc ∑ t ∈ S, (#(G.filter fun v => v ∈ F t) : ℝ) ≤ ∑ _t ∈ S, (2 * n * B / k : ℝ) := by
          refine sum_le_sum fun t _ => le_trans ?_ (hFle t)
          exact_mod_cast card_le_card (fun v hv => (mem_filter.mp hv).2)
      _ = #S * (2 * n * B / k) := by simp
  -- (ii) incidences between `I' \ I` and `G` are at most `ε k · 2nB/k`
  have hdiff : (#(I' \ I) : ℝ) ≤ ε * k := by
    rw [card_sdiff_of_subset hII']
    have : #I' - #I = k - N P adv s j := by rw [hI', hIcard]
    rw [this, Nat.cast_sub hN2]
    linarith
  have hextra : (∑ t ∈ I' \ I, (#(G.filter fun v => v ∈ F t) : ℝ)) ≤ ε * k * (2 * n * B / k) := by
    calc (∑ t ∈ I' \ I, (#(G.filter fun v => v ∈ F t) : ℝ))
        ≤ ∑ _t ∈ I' \ I, (2 * n * B / k : ℝ) := by
          refine sum_le_sum fun t _ => le_trans ?_ (hFle t)
          exact_mod_cast card_le_card (fun v hv => (mem_filter.mp hv).2)
      _ = #(I' \ I) * (2 * n * B / k) := by simp
      _ ≤ ε * k * (2 * n * B / k) := by gcongr
  -- (iii) loads of the nodes of `G` (all in `J`)
  have hload : (#G : ℝ) * ((1 - ε) * B) ≤ ∑ v ∈ G, (load F I' v : ℝ) := by
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun v hv => (hJload v (mem_filter.mp hv).1).1
  have hsplit : ∀ v, load F I' v ≤ #(I.filter fun t => v ∈ F t) +
      #((I' \ I).filter fun t => v ∈ F t) := by
    intro v
    unfold load
    have : I' = I ∪ (I' \ I) := (union_sdiff_of_subset hII').symm
    calc #(I'.filter fun t => v ∈ F t)
        = #((I ∪ (I' \ I)).filter fun t => v ∈ F t) := by rw [← this]
      _ ≤ _ := by rw [filter_union]; exact card_union_le _ _
  have hcomm1 := sum_card_filter_comm I G (fun t v => v ∈ F t)
  have hcomm2 := sum_card_filter_comm (I' \ I) G (fun t v => v ∈ F t)
  have hsum : ∑ v ∈ G, (load F I' v : ℝ) ≤ ∑ t ∈ I, (#(G.filter fun v => v ∈ F t) : ℝ) +
      ∑ t ∈ I' \ I, (#(G.filter fun v => v ∈ F t) : ℝ) := by
    have h1 : ∑ v ∈ G, load F I' v ≤ ∑ v ∈ G, (#(I.filter fun t => v ∈ F t) +
        #((I' \ I).filter fun t => v ∈ F t)) := sum_le_sum fun v _ => hsplit v
    rw [sum_add_distrib, ← hcomm1, ← hcomm2] at h1
    exact_mod_cast h1
  -- (iv) `G` is large
  have hGcard : (1 - ε - α) * n ≤ #G := by
    have hJG : J ⊆ G ∪ adv.faulty := by
      intro v hv
      by_cases h : adv.AliveAt (s + j + 1) v
      · exact mem_union_left _ (mem_filter.mpr ⟨hv, h⟩)
      · exact mem_union_right _ (Adversary.mem_faulty_of_not_aliveAt h)
    have h1 := (card_le_card hJG).trans (card_union_le _ _)
    have h2 : (#J : ℝ) ≤ #G + #adv.faulty := by exact_mod_cast h1
    have h3 : (#adv.faulty : ℝ) ≤ α * n := hadv
    linarith
  -- conclusion
  have hS : ε * k ≤ #S := by
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hGB : (1 - ε - α) * n * ((1 - ε) * B) ≤ #G * ((1 - ε) * B) :=
      mul_le_mul_of_nonneg_right hGcard (by nlinarith)
    have key : (1 - ε - α) * n * ((1 - ε) * B) - ε * k * (2 * n * B / k) ≤
        #S * (2 * n * B / k) := by linarith
    have e1 : ε * k * (2 * n * B / k) = 2 * ε * n * B := by field_simp
    rw [e1] at key
    have key2 : 2 * ε * n * B ≤ #S * (2 * n * B / k) := by
      have : 4 * ε * n * B ≤ (1 - ε - α) * (1 - ε) * n * B := by
        have := mul_le_mul_of_nonneg_right hprog (le_of_lt (mul_pos hn' hB'))
        linarith
      nlinarith
    rw [mul_div_assoc', le_div_iff₀ hkpos] at key2
    have hnB : 0 < 2 * (n : ℝ) * B := by positivity
    nlinarith
  have : (N P adv s (j + 1) : ℝ) + #S ≤ N P adv s j := by exact_mod_cast hN'
  linarith

/-- The rounding step of Lemma 4.5 (the role of Lemma A.2): `(1-ε)⌈y⌉ < ⌈(1-ε)y⌉ + 1`. -/
lemma one_sub_mul_ceil_lt {ε y : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hy : 0 ≤ y) :
    (1 - ε) * ⌈y⌉₊ < ⌈(1 - ε) * y⌉₊ + 1 := by
  have h1 : (⌈y⌉₊ : ℝ) < y + 1 := Nat.ceil_lt_add_one hy
  have h2 : (1 - ε) * y ≤ ⌈(1 - ε) * y⌉₊ := Nat.le_ceil _
  have h3 : (1 - ε) * ⌈y⌉₊ < (1 - ε) * (y + 1) := mul_lt_mul_of_pos_left h1 (by linarith)
  linarith

/-- The hypotheses of the analysis of Algorithm 1: parameters `ε ∈ (0,1)`, `B ≥ 1`, the progress
condition on `ε` (our version of "`(1 - 4ε - (1+ε)α)/2 ≥ ε`"), and the agreed-upon families are
`(k, B, ε)`-load balancing covering families for every `k` with `2B < k ≤ m` that can occur. -/
structure Good (P : Params n m) (α : ℝ) : Prop where
  hB : 1 ≤ P.B
  hε0 : 0 < P.ε
  hε1 : P.ε < 1
  hprog : 4 * P.ε ≤ (1 - P.ε - α) * (1 - P.ε)
  hF : ∀ k, 2 * P.B < k → k ≤ m → IsLBCF n m k P.B P.ε (P.F k)

/-- **Lemma 4.5.** For every iteration `j`, `N_j ≤ k_j`. -/
theorem lemma_4_5 {α : ℝ} (hP : Good P α) (hadv : adv.Admissible α) (hn : 0 < n) (j : ℕ) :
    N P adv s j ≤ kk P j := by
  induction j with
  | zero =>
    have : kk P 0 = m := by simp [kk]
    rw [this]
    exact (card_filter_le _ _).trans (by simp)
  | succ j ih =>
    by_cases h : N P adv s j ≤ kk P (j + 1)
    · exact (N_succ_le j).trans h
    have hy : (0 : ℝ) ≤ (1 - P.ε) ^ j * m := by
      have := hP.hε1; positivity
    have hkk : kk P (j + 1) = ⌈(1 - P.ε) * ((1 - P.ε) ^ j * m)⌉₊ := by
      simp only [kk, pow_succ]; ring_nf
    have hlt : (1 - P.ε) * (kk P j : ℝ) < kk P (j + 1) + 1 := by
      rw [hkk]; exact one_sub_mul_ceil_lt hP.hε0.le hP.hε1 hy
    have hN1 : (1 - P.ε) * kk P j ≤ N P adv s j := by
      have : (kk P (j + 1) : ℝ) + 1 ≤ N P adv s j := by exact_mod_cast (not_le.mp h)
      exact le_of_lt (lt_of_lt_of_le hlt this)
    by_cases hk : kk P j ≤ 2 * P.B
    · rw [N_succ_eq_zero_of_small hk ih]; exact Nat.zero_le _
    have hkm : kk P j ≤ m := by
      apply Nat.ceil_le.mpr
      have : (1 - P.ε) ^ j ≤ 1 := pow_le_one₀ (by linarith [hP.hε1]) (by linarith [hP.hε0])
      have hm : (0 : ℝ) ≤ m := by positivity
      nlinarith
    have hdec := N_succ_le_of_large hadv hn hP.hB hP.hε0 hP.hε1.le hP.hprog (not_le.mp hk) hkm
      (hP.hF _ (not_le.mp hk) hkm) hN1 ih
    have hih : (N P adv s j : ℝ) ≤ kk P j := by exact_mod_cast ih
    have : (N P adv s (j + 1) : ℝ) < kk P (j + 1) + 1 := by
      have : (0 : ℝ) ≤ P.ε := hP.hε0.le
      nlinarith
    exact Nat.lt_add_one_iff.mp (by exact_mod_cast this)

/-! ### Lemma 4.3: termination -/

/-- Eventually `k_j ≤ 2B`. -/
lemma exists_kk_le (hP : P.ε ∈ Set.Ioo (0 : ℝ) 1) (hB : 1 ≤ P.B) : ∃ j, kk P j ≤ 2 * P.B := by
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (m + 1) by positivity)
    (show 1 - P.ε < 1 by linarith [hP.1])
  refine ⟨j, ?_⟩
  have h1 : (1 - P.ε) ^ j * m ≤ 1 := by
    have hm : (0 : ℝ) < m + 1 := by positivity
    rw [lt_div_iff₀ hm] at hj
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 - P.ε by linarith [hP.2]) j]
  have : kk P j ≤ 1 := Nat.ceil_le.mpr (by simpa using h1)
  omega

/-- The number of iterations Algorithm 1 runs: up to and including the first iteration with
`k_j ≤ 2B` (after it, all tasks are fully verified; see the footnote to the proof of
Lemma 4.3). -/
noncomputable def numIter (P : Params n m) : ℕ :=
  if h : ∃ j, kk P j ≤ 2 * P.B then Nat.find h + 1 else 0

/-- **Lemma 4.3 (1).** When Algorithm 1 terminates (after `numIter` iterations) all tasks are fully
verified and, in particular, all tasks have been completed — against every adversary crashing at
most `α n` nodes. -/
theorem lemma_4_3_1 {α : ℝ} (hP : Good P α) (hα : α < 1) (hadv : adv.Admissible α)
    (hn : 0 < n) :
    (∀ t, FV P adv s (numIter P) t) ∧ Done P adv s (numIter P) = univ := by
  have hex := exists_kk_le (P := P) ⟨hP.hε0, hP.hε1⟩ hP.hB
  have hnum : numIter P = Nat.find hex + 1 := by simp [numIter, hex]
  have hN0 : N P adv s (numIter P) = 0 := by
    rw [hnum]
    exact N_succ_eq_zero_of_small (Nat.find_spec hex) (lemma_4_5 hP hadv hn _)
  have hFV : ∀ t, FV P adv s (numIter P) t := by
    intro t
    by_contra h
    have : t ∈ univ.filter fun t => ¬ FV P adv s (numIter P) t := by simpa using h
    have := card_pos.mpr ⟨t, this⟩
    unfold N at hN0; omega
  refine ⟨hFV, ?_⟩
  -- some node never crashes
  obtain ⟨v, -, hv⟩ : ∃ v ∈ (univ : Finset (Fin n)), v ∉ adv.faulty := by
    refine exists_mem_notMem_of_card_lt_card ?_
    have h1 : (#adv.faulty : ℝ) < n := by
      have : (0 : ℝ) < n := by exact_mod_cast hn
      have h2 : (#adv.faulty : ℝ) ≤ α * n := hadv
      nlinarith
    simpa using (show #adv.faulty < n by exact_mod_cast h1)
  ext t
  simp only [mem_univ, iff_true]
  exact lemma_4_4 _ v (hFV t v (Adversary.aliveAt_of_not_mem_faulty hv _))

/-- **Lemma 4.3 (2)** (iteration count). Algorithm 1 runs at most `log m / log (1/(1-ε)) + 2`
iterations, i.e. `O(B R log n)` rounds at `2BR + 1` rounds per iteration. -/
theorem lemma_4_3_2 (hP : P.ε ∈ Set.Ioo (0 : ℝ) 1) (hB : 1 ≤ P.B) (hm : 1 ≤ m) :
    (numIter P : ℝ) ≤ Real.log m / (-Real.log (1 - P.ε)) + 2 := by
  have hex := exists_kk_le (P := P) hP hB
  have hnum : numIter P = Nat.find hex + 1 := by simp [numIter, hex]
  set L := -Real.log (1 - P.ε) with hL
  have hLpos : 0 < L := by
    have : Real.log (1 - P.ε) < 0 := Real.log_neg (by linarith [hP.2]) (by linarith [hP.1])
    linarith
  set j := ⌈Real.log m / L⌉₊ with hj
  have hjk : kk P j ≤ 2 * P.B := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have h1 : Real.log m ≤ j * L := by
      have := Nat.le_ceil (Real.log m / L)
      rwa [div_le_iff₀ hLpos] at this
    have h2 : Real.log ((1 - P.ε) ^ j * m) ≤ 0 := by
      rw [Real.log_mul (by have := hP.2; positivity) hmpos.ne', Real.log_pow]
      linarith
    have h3 : (1 - P.ε) ^ j * m ≤ 1 := by
      have hpos : 0 < (1 - P.ε) ^ j * m := by have := hP.2; have : 0 < 1 - P.ε := by linarith
                                              positivity
      rwa [Real.log_nonpos_iff hpos.le] at h2
    have : kk P j ≤ 1 := Nat.ceil_le.mpr (by simpa using h3)
    omega
  have hle : Nat.find hex ≤ j := Nat.find_min' hex hjk
  have hlt : (j : ℝ) < Real.log m / L + 1 := by
    apply Nat.ceil_lt_add_one
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hm)) hLpos.le
  rw [hnum]; push_cast
  have : (Nat.find hex : ℝ) ≤ j := by exact_mod_cast hle
  linarith

end Podc.TaskCompletion.Alg
