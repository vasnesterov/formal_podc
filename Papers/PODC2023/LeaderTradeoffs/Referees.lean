import Papers.PODC2023.LeaderTradeoffs.Model

/-!
# The improved Afek–Gafni algorithm (Section 3.3, Theorem 3.10)

Section 3.3 of Kutten, Robinson, Tan, Zhu, *Improved Tradeoffs for Leader Election* (PODC 2023).
Synchronous KT0 clique, simultaneous wake-up, deterministic.

The algorithm is parametrized by the number of iterations `K` (the paper's `k - 2`) and the
referee counts `d i` of the iterations `i = 1, …, K` (the paper's `⌈n^{i/(k-1)}⌉`). Initially every
node is a survivor. Iteration `i` (rounds `2(i-1)` and `2(i-1)+1`, 0-indexed):
1. every survivor sends its ID on its ports `0, …, d i - 1` (to `d i` distinct referees, or to all
   nodes if `d i ≥ n - 1`);
2. every node that received IDs replies (on the port of arrival) only to the highest ID received;
   a survivor stays a survivor iff it received replies on all of its ports `0, …, d i - 1`.

Final round `2K`: every survivor sends its ID on all ports; a survivor outputs "leader" iff its ID
exceeds all IDs it received, every other node outputs "non-leader". Time: `2K + 1`.

Main results:
* `electsBy`, `terminatesBy`: for every ID universe and every choice of `K`, `d`, the algorithm
  elects exactly one leader (the maximum ID) and terminates after `2K + 1` rounds;
* `card_S_mul_le` (survivor bound): after iteration `i ≥ 1` at most `n / min(d i, n-1)` survivors
  remain (the referee sets of the remaining survivors are pairwise disjoint);
* `msgs_le`: `msgs ≤ ∑_{i=1}^{K} 2·s_{i-1}·min(d i, n-1) + s_K·(n-1)` (`s_i` = #survivors after
  iteration `i`), `msgBound_general` (explicit worst-case bound);
* `msgBound_real`: if `1 ≤ q`, `q^{K+1} = n` and `q^i ≤ d i ≤ 2 q^i`, at most `8(K+1)·n·q`
  messages;
* `theorem_3_10`: for odd `ℓ = 2K + 1` and `d i = ⌈n^{i/(K+1)}⌉`, the algorithm elects a leader in
  `ℓ` rounds with at most `4(ℓ+1)·n^{1+2/(ℓ+1)}` messages.

Remark on the paper's analysis: after the last two-round iteration `K = k - 2` the survivor bound
only gives `n^{1/(k-1)}` survivors (not one); the last one-round "iteration" (the broadcast of the
remaining survivors) is what reduces them to a single leader, at a cost of `≤ n^{1/(k-1)}·(n-1)`
messages. This matches the paper's message count.
-/

open Classical Finset

namespace LeaderTradeoffs

namespace Referees

/-- Local state of a node. -/
structure St (m : ℕ) where
  /-- own ID -/
  id : ℕ
  /-- number of rounds executed so far -/
  rd : ℕ
  /-- still a survivor? -/
  surv : Bool
  /-- the messages received in the last round -/
  last : Fin m → Option ℕ
  /-- output (`none` = undecided) -/
  out : Option Bool

variable {m : ℕ}

/-- Port `j` carried the highest ID received in the last round. -/
def IsMaxPort (last : Fin m → Option ℕ) (j : Fin m) : Prop :=
  ∃ x, last j = some x ∧ ∀ j' y, last j' = some y → y ≤ x

variable (m) (K : ℕ) (d : ℕ → ℕ)

/-- The algorithm of Section 3.3 with `K` iterations and referee counts `d 1, …, d K`. -/
@[reducible] noncomputable def alg : Algorithm m where
  State := St m
  Msg := ℕ
  init x := ⟨x, 0, true, fun _ => none, none⟩
  send s j :=
    if s.rd < 2 * K then
      if s.rd % 2 = 0 then (if s.surv = true ∧ j.val < d (s.rd / 2 + 1) then some s.id else none)
      else (if IsMaxPort s.last j then some s.id else none)
    else if s.rd = 2 * K then (if s.surv = true then some s.id else none) else none
  step s v :=
    ⟨s.id, s.rd + 1,
      if s.rd < 2 * K ∧ s.rd % 2 = 1 then
        s.surv && decide (∀ j : Fin m, j.val < d (s.rd / 2 + 1) → (v j).isSome) else s.surv,
      v,
      if s.rd = 2 * K then some (s.surv && decide (∀ j y, v j = some y → y < s.id)) else s.out⟩
  output s := s.out

variable {m K d}

theorem alg_send (s : St m) (j : Fin m) : (alg m K d).send s j =
    if s.rd < 2 * K then
      if s.rd % 2 = 0 then (if s.surv = true ∧ j.val < d (s.rd / 2 + 1) then some s.id else none)
      else (if IsMaxPort s.last j then some s.id else none)
    else if s.rd = 2 * K then (if s.surv = true then some s.id else none) else none := rfl

theorem alg_output (s : St m) : (alg m K d).output s = s.out := rfl

theorem alg_step (s : St m) (v : Fin m → Option ℕ) : (alg m K d).step s v =
    (⟨s.id, s.rd + 1,
      if s.rd < 2 * K ∧ s.rd % 2 = 1 then
        s.surv && decide (∀ j : Fin m, j.val < d (s.rd / 2 + 1) → (v j).isSome) else s.surv,
      v,
      if s.rd = 2 * K then some (s.surv && decide (∀ j y, v j = some y → y < s.id)) else s.out⟩ :
      St m) := rfl

/-! ### The survivor sets -/

/-- `v` sends its ID to `w` in iteration `i` (via one of its ports `0, …, d i - 1`). -/
def Sends (d : ℕ → ℕ) (p : PortMap m) (i v w : ℕ) : Prop :=
  ∃ j : Fin m, j.val < d i ∧ p v j = some w

/-- The survivors after `t` iterations: `u` survives iteration `t + 1` iff for each of its ports
`j < d (t+1)` the referee `w` behind `j` received no higher ID from a survivor. -/
noncomputable def S (d : ℕ → ℕ) (p : PortMap m) (I : Finset ℕ) : ℕ → Finset ℕ
  | 0 => I
  | t + 1 => (S d p I t).filter fun u => ∀ j : Fin m, j.val < d (t + 1) →
      ∃ w, p u j = some w ∧ ∀ v ∈ S d p I t, Sends d p (t + 1) v w → v ≤ u

theorem mem_S_succ {p : PortMap m} {I : Finset ℕ} {t u : ℕ} : u ∈ S d p I (t + 1) ↔
    u ∈ S d p I t ∧ ∀ j : Fin m, j.val < d (t + 1) →
      ∃ w, p u j = some w ∧ ∀ v ∈ S d p I t, Sends d p (t + 1) v w → v ≤ u := by
  rw [S, Finset.mem_filter]

theorem S_subset {p : PortMap m} {I : Finset ℕ} : ∀ t, S d p I t ⊆ I
  | 0 => subset_rfl
  | t + 1 => (Finset.filter_subset _ _).trans (S_subset t)

/-- The referees of `v` in iteration `i`. -/
noncomputable def Ref (d : ℕ → ℕ) (p : PortMap m) (i v : ℕ) : Finset ℕ :=
  (univ.filter fun j : Fin m => j.val < d i).image fun j => (p v j).getD 0

/-- Helper: every port of a node of `I` leads to a node of `I` that has a port back. -/
theorem link {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I) {u : ℕ} (hu : u ∈ I)
    (j : Fin m) : ∃ v i, p u j = some v ∧ p v i = some u ∧ v ∈ I := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hp.2 u hu j)
  obtain ⟨i, hi⟩ := hp.1.symm u hu j v hv
  exact ⟨v, i, hv, hi, hp.1.mem u hu j v hv⟩

theorem inbox_of' {A : Algorithm m} {p : PortMap m} {I : Finset ℕ} (hp : WF p I) {u v : ℕ}
    (hu : u ∈ I) {j i : Fin m} (hj : p u j = some v) (hi : p v i = some u) (st : ℕ → A.State) :
    inbox A p st u j = A.send (st v) i := by
  have hv := hp.mem u hu j v hj
  simp [inbox, hj, backPort_eq hp hv hi]

theorem sends_iff {p : PortMap m} {I : Finset ℕ} (hp : WF p I) {k v u : ℕ} (hv : v ∈ I)
    {i : Fin m} (hi : p v i = some u) : Sends d p k v u ↔ i.val < d k := by
  constructor
  · rintro ⟨j, hj, hj'⟩
    rwa [hp.inj v hv i j u hi hj']
  · intro h
    exact ⟨i, h, hi⟩

theorem mem_Ref {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I) {i v w : ℕ} (hv : v ∈ I) :
    w ∈ Ref d p i v ↔ Sends d p i v w := by
  simp only [Ref, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hp.2 v hv j)
    exact ⟨j, hj, by rw [hx]; rfl⟩
  · rintro ⟨j, hj, hj'⟩
    exact ⟨j, hj, by rw [hj']; rfl⟩

theorem card_Ref_le {p : PortMap m} {i v : ℕ} : (Ref d p i v).card ≤ min m (d i) := by
  rw [← Fin.card_filter_val_lt]
  exact Finset.card_image_le

theorem card_Ref {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I) {i v : ℕ} (hv : v ∈ I) :
    (Ref d p i v).card = min m (d i) := by
  rw [← Fin.card_filter_val_lt, Ref]
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (hp.2 v hv a)
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (hp.2 v hv b)
  simp only [hx, hy, Option.getD_some] at hab
  subst hab
  exact hp.1.inj v hv a b x hx hy

/-- The node with the maximum ID survives every iteration. -/
theorem max_mem_S {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I) (hne : I.Nonempty) :
    ∀ t, I.max' hne ∈ S d p I t
  | 0 => I.max'_mem hne
  | t + 1 => by
    rw [mem_S_succ]
    refine ⟨max_mem_S hp hne t, fun j _ => ?_⟩
    obtain ⟨w, -, hw, -, -⟩ := link hp (I.max'_mem hne) j
    exact ⟨w, hw, fun v hv _ => I.le_max' v (S_subset t hv)⟩

/-- **Survivor bound.** The referee sets of the survivors of iteration `t + 1` are pairwise
disjoint, hence `#survivors · min(d (t+1), n - 1) ≤ n`. -/
theorem card_S_mul_le {p : PortMap m} {I : Finset ℕ} (hp : IsPortMap p I) (hI : I.card = m + 1)
    (t : ℕ) : (S d p I (t + 1)).card * min m (d (t + 1)) ≤ m + 1 := by
  have hsub : ∀ v ∈ S d p I (t + 1), v ∈ I := fun v hv => S_subset _ hv
  have hdisj : (S d p I (t + 1) : Set ℕ).PairwiseDisjoint (Ref d p (t + 1)) := by
    intro v₁ hv₁ v₂ hv₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro w hw₁ hw₂
    rw [mem_Ref hp (hsub v₁ hv₁)] at hw₁
    rw [mem_Ref hp (hsub v₂ hv₂)] at hw₂
    have key : ∀ a ∈ S d p I (t + 1), ∀ b ∈ S d p I (t + 1), Sends d p (t + 1) a w →
        Sends d p (t + 1) b w → b ≤ a := by
      intro a ha b hb hwa hwb
      obtain ⟨j, hj, hj'⟩ := hwa
      obtain ⟨-, hsurv⟩ := mem_S_succ.1 ha
      obtain ⟨w', hw', hmax⟩ := hsurv j hj
      rw [hj'] at hw'
      cases hw'
      exact hmax b (mem_S_succ.1 hb).1 hwb
    exact hne (le_antisymm (key _ hv₂ _ hv₁ hw₂ hw₁) (key _ hv₁ _ hv₂ hw₁ hw₂))
  have hcard := Finset.card_biUnion hdisj
  rw [Finset.sum_congr rfl fun v hv => card_Ref hp (hsub v hv), Finset.sum_const,
    smul_eq_mul] at hcard
  rw [← hcard, ← hI]
  apply Finset.card_le_card
  intro w hw
  obtain ⟨v, hv, hw⟩ := Finset.mem_biUnion.1 hw
  obtain ⟨j, -, hj⟩ := (mem_Ref hp (hsub v hv)).1 hw
  exact hp.1.mem v (hsub v hv) j w hj

theorem sendCount_post {s : St m} (hs : 2 * K < s.rd) : sendCount (alg m K d) s = 0 := by
  rw [sendCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j _
  simp only
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  simp

/-! ### The execution -/

/-- State invariant after `2t` rounds (`t ≤ K`). -/
def EvenInv (d : ℕ → ℕ) (p : PortMap m) (I : Finset ℕ) (t u : ℕ) (s : St m) : Prop :=
  s.id = u ∧ s.rd = 2 * t ∧ s.surv = decide (u ∈ S d p I t) ∧ s.out = none

/-- State invariant after `2t + 1` rounds (`t < K`): `last` records the IDs of the survivors that
chose `u` as a referee. -/
def OddInv (d : ℕ → ℕ) (p : PortMap m) (I : Finset ℕ) (t u : ℕ) (s : St m) : Prop :=
  s.id = u ∧ s.rd = 2 * t + 1 ∧ s.surv = decide (u ∈ S d p I t) ∧ s.out = none ∧
    ∀ j y, s.last j = some y ↔ p u j = some y ∧ y ∈ S d p I t ∧ Sends d p (t + 1) y u

section Exec

variable {I : Finset ℕ} {p : PortMap m} (hI : I.card = m + 1) (hp : IsPortMap p I)
include hI hp

set_option linter.unusedSectionVars false

theorem run_odd {t : ℕ} (ht : t < K)
    (h : ∀ v ∈ I, EvenInv d p I t v (run (alg m K d) p (2 * t) v)) :
    ∀ u ∈ I, OddInv d p I t u (run (alg m K d) p (2 * t + 1) u) := by
  intro u hu
  obtain ⟨h1, h2, h3, h4⟩ := h u hu
  show OddInv d p I t u ((alg m K d).step _ _)
  rw [alg_step]
  refine ⟨h1, by rw [h2], ?_, ?_, ?_⟩
  · dsimp only
    rw [ite_eq_right (by omega), h3]
  · dsimp only
    rw [ite_eq_right (by omega), h4]
  · intro j y
    dsimp only
    obtain ⟨v, i, hv, hi, hvI⟩ := link hp hu j
    obtain ⟨g1, g2, g3, -⟩ := h v hvI
    rw [inbox_of' hp.1 hu hv hi, alg_send, g2, g1, g3, ite_eq_left (by omega),
      ite_eq_left (by omega), show 2 * t / 2 = t by omega, hv]
    constructor
    · intro hx
      split_ifs at hx with hc
      cases hx
      exact ⟨rfl, by simpa using hc.1, (sends_iff hp.1 hvI hi).2 hc.2⟩
    · rintro ⟨hy, hyS, hs⟩
      cases hy
      rw [ite_eq_left ⟨by simpa using hyS, (sends_iff hp.1 hvI hi).1 hs⟩]

theorem run_even_succ {t : ℕ} (ht : t < K)
    (h : ∀ v ∈ I, OddInv d p I t v (run (alg m K d) p (2 * t + 1) v)) :
    ∀ u ∈ I, EvenInv d p I (t + 1) u (run (alg m K d) p (2 * (t + 1)) u) := by
  intro u hu
  obtain ⟨h1, h2, h3, h4, -⟩ := h u hu
  rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring]
  show EvenInv d p I (t + 1) u ((alg m K d).step _ _)
  rw [alg_step]
  refine ⟨h1, by rw [h2]; ring, ?_, ?_⟩
  · dsimp only
    rw [ite_eq_left (by omega), h3, h2, show (2 * t + 1) / 2 = t by omega, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    rw [mem_S_succ]
    apply and_congr_right
    intro huS
    apply forall_congr'
    intro j
    apply imp_congr_right
    intro hj
    obtain ⟨w, i, hw, hi, hwI⟩ := link hp hu j
    obtain ⟨o1, o2, -, -, o5⟩ := h w hwI
    rw [inbox_of' hp.1 hu hw hi, alg_send, o2, o1, ite_eq_left (by omega),
      ite_eq_right (by omega)]
    have hrhs : (∃ w', p u j = some w' ∧ ∀ v ∈ S d p I t, Sends d p (t + 1) v w' → v ≤ u) ↔
        ∀ v ∈ S d p I t, Sends d p (t + 1) v w → v ≤ u := by
      rw [hw]
      constructor
      · rintro ⟨w', hw', H⟩
        cases hw'
        exact H
      · intro H
        exact ⟨w, rfl, H⟩
    rw [hrhs]
    constructor
    · intro hs v hvS hvw
      split_ifs at hs with hmax
      · obtain ⟨x, hx, hle⟩ := hmax
        obtain ⟨hx1, -, -⟩ := (o5 i x).1 hx
        rw [hi] at hx1
        cases hx1
        have hvI : v ∈ I := S_subset t hvS
        have hvw' : v ≠ w := by
          rintro rfl
          obtain ⟨j'', -, hj''⟩ := hvw
          exact hp.1.ne v hvI j'' hj''
        obtain ⟨j', hj'⟩ := hp.surj hI hwI hvI hvw'
        exact hle j' v ((o5 j' v).2 ⟨hj', hvS, hvw⟩)
      · cases hs
    · intro H
      rw [ite_eq_left]
      · rfl
      · refine ⟨u, (o5 i u).2 ⟨hi, huS, j, hj, hw⟩, fun j' y hy => ?_⟩
        obtain ⟨-, hyS, hyw⟩ := (o5 j' y).1 hy
        exact H y hyS hyw
  · dsimp only
    rw [ite_eq_right (by omega), h4]

theorem run_even : ∀ t ≤ K, ∀ u ∈ I, EvenInv d p I t u (run (alg m K d) p (2 * t) u) := by
  intro t
  induction t with
  | zero =>
    intro _ u hu
    refine ⟨rfl, rfl, ?_, rfl⟩
    show true = decide (u ∈ I)
    simp [hu]
  | succ t ih =>
    intro ht
    exact run_even_succ hI hp (by omega) (run_odd hI hp (by omega) (ih (by omega)))

/-- The outcome of the final round. -/
theorem run_final : ∀ u ∈ I, (run (alg m K d) p (2 * K + 1) u).rd = 2 * K + 1 ∧
    (run (alg m K d) p (2 * K + 1) u).out =
      some (decide (u ∈ S d p I K ∧ ∀ v ∈ S d p I K, v ≠ u → v < u)) := by
  intro u hu
  have hK := run_even (d := d) hI hp K le_rfl
  obtain ⟨h1, h2, h3, -⟩ := hK u hu
  show ((alg m K d).step _ _).rd = _ ∧ ((alg m K d).step _ _).out = _
  rw [alg_step]
  refine ⟨by dsimp only; rw [h2], ?_⟩
  dsimp only
  rw [ite_eq_left h2, h3, h1, Option.some_inj, Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  apply and_congr_right
  intro _
  constructor
  · intro H v hvS hvu
    have hvI := S_subset K hvS
    obtain ⟨j, hj⟩ := hp.surj hI hu hvI hvu
    obtain ⟨i, hi⟩ := hp.1.symm u hu j v hj
    apply H j v
    obtain ⟨g1, g2, g3, -⟩ := hK v hvI
    rw [inbox_of' hp.1 hu hj hi, alg_send, g2, g1, g3, ite_eq_right (by omega), ite_eq_left rfl,
      ite_eq_left (by simpa using hvS)]
  · intro H j y hy
    obtain ⟨w, i, hw, hi, hwI⟩ := link hp hu j
    obtain ⟨g1, g2, g3, -⟩ := hK w hwI
    rw [inbox_of' hp.1 hu hw hi, alg_send, g2, g1, g3, ite_eq_right (by omega),
      ite_eq_left rfl] at hy
    split_ifs at hy with hc
    cases hy
    refine H y (by simpa using hc) ?_
    rintro rfl
    exact hp.1.ne y hu j hw

theorem run_post (t : ℕ) : ∀ u ∈ I, (run (alg m K d) p (2 * K + 1 + t) u).rd = 2 * K + 1 + t ∧
    (run (alg m K d) p (2 * K + 1 + t) u).out = (run (alg m K d) p (2 * K + 1) u).out := by
  induction t with
  | zero => intro u hu; exact ⟨(run_final hI hp u hu).1, rfl⟩
  | succ t ih =>
    intro u hu
    obtain ⟨h1, h2⟩ := ih u hu
    rw [show 2 * K + 1 + (t + 1) = 2 * K + 1 + t + 1 by ring]
    show ((alg m K d).step _ _).rd = _ ∧ ((alg m K d).step _ _).out = _
    rw [alg_step]
    dsimp only
    rw [h1, ite_eq_right (by omega), h2]
    exact ⟨rfl, rfl⟩

theorem leaders_eq (hne : I.Nonempty) :
    leaders (alg m K d) p (2 * K + 1) I = {I.max' hne} := by
  ext u
  rw [leaders, Finset.mem_filter, Finset.mem_singleton]
  have hM := max_mem_S (d := d) hp hne K
  constructor
  · rintro ⟨hu, h⟩
    rw [alg_output, (run_final hI hp u hu).2] at h
    simp only [Option.some.injEq, decide_eq_true_eq] at h
    by_contra hne'
    exact absurd (h.2 _ hM (Ne.symm hne')) (not_lt.2 (I.le_max' u hu))
  · rintro rfl
    refine ⟨I.max'_mem hne, ?_⟩
    rw [alg_output, (run_final hI hp _ (I.max'_mem hne)).2]
    simp only [Option.some.injEq, decide_eq_true_eq]
    exact ⟨hM, fun v hv hvu => lt_of_le_of_ne (I.le_max' v (S_subset K hv)) hvu⟩

/-! ### Message counting -/

/-- The nodes that are a referee of some survivor in iteration `t + 1`. -/
noncomputable def R (d : ℕ → ℕ) (p : PortMap m) (I : Finset ℕ) (t : ℕ) : Finset ℕ :=
  (S d p I t).biUnion (Ref d p (t + 1))

theorem roundMsgs_even {t : ℕ} (ht : t < K) :
    roundMsgs (alg m K d) p (2 * t) I = (S d p I t).card * min m (d (t + 1)) := by
  have hcount : ∀ u ∈ I, sendCount (alg m K d) (run (alg m K d) p (2 * t) u) =
      if u ∈ S d p I t then min m (d (t + 1)) else 0 := by
    intro u hu
    obtain ⟨h1, h2, h3, -⟩ := run_even hI hp t ht.le u hu
    rw [sendCount]
    split_ifs with huS
    · rw [← Fin.card_filter_val_lt]
      congr 1
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h2, h3, h1, ite_eq_left (by omega), ite_eq_left (by omega),
        show 2 * t / 2 = t by omega]
      simp [huS]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      rw [alg_send, h2, h3, h1, ite_eq_left (by omega), ite_eq_left (by omega)]
      simp [huS]
  rw [roundMsgs, Finset.sum_congr rfl hcount, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 (S_subset t), Finset.sum_const, smul_eq_mul]

theorem roundMsgs_odd {t : ℕ} (ht : t < K) :
    roundMsgs (alg m K d) p (2 * t + 1) I ≤ (S d p I t).card * min m (d (t + 1)) := by
  have hodd := run_odd hI hp ht (run_even (d := d) hI hp t ht.le)
  have hcount : ∀ u ∈ I, sendCount (alg m K d) (run (alg m K d) p (2 * t + 1) u) ≤
      if u ∈ R d p I t then 1 else 0 := by
    intro u hu
    obtain ⟨h1, h2, -, -, h5⟩ := hodd u hu
    have hfilt : (univ.filter fun j => ((alg m K d).send (run (alg m K d) p (2 * t + 1) u)
        j).isSome) = univ.filter fun j => IsMaxPort (run (alg m K d) p (2 * t + 1) u).last j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [h2, ite_eq_left (by omega), ite_eq_right (by omega)]
      split_ifs with hj <;> simp [hj]
    rw [sendCount, hfilt]
    split_ifs with hR
    · rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨xa, hxa, hma⟩ := ha
      obtain ⟨xb, hxb, hmb⟩ := hb
      have hab : xa = xb := le_antisymm (hmb a xa hxa) (hma b xb hxb)
      subst hab
      exact hp.1.inj u hu a b xa ((h5 a xa).1 hxa).1 ((h5 b xa).1 hxb).1
    · rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro j - ⟨x, hx, -⟩
      obtain ⟨-, hxS, hxu⟩ := (h5 j x).1 hx
      exact hR (Finset.mem_biUnion.2 ⟨x, hxS, (mem_Ref hp (S_subset t hxS)).2 hxu⟩)
  calc roundMsgs (alg m K d) p (2 * t + 1) I
      ≤ ∑ u ∈ I, if u ∈ R d p I t then 1 else 0 := Finset.sum_le_sum hcount
    _ = (I ∩ R d p I t).card := by rw [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ (R d p I t).card := Finset.card_le_card Finset.inter_subset_right
    _ ≤ ∑ v ∈ S d p I t, (Ref d p (t + 1) v).card := Finset.card_biUnion_le
    _ ≤ ∑ v ∈ S d p I t, min m (d (t + 1)) := Finset.sum_le_sum fun v _ => card_Ref_le
    _ = (S d p I t).card * min m (d (t + 1)) := by rw [Finset.sum_const, smul_eq_mul]

theorem roundMsgs_final : roundMsgs (alg m K d) p (2 * K) I = (S d p I K).card * m := by
  have hcount : ∀ u ∈ I, sendCount (alg m K d) (run (alg m K d) p (2 * K) u) =
      if u ∈ S d p I K then m else 0 := by
    intro u hu
    obtain ⟨h1, h2, h3, -⟩ := run_even (d := d) hI hp K le_rfl u hu
    rw [sendCount]
    split_ifs with huS
    · rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
      intro j _
      rw [alg_send, h2, h3, h1, ite_eq_right (by omega), ite_eq_left rfl]
      simp [huS]
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _
      rw [alg_send, h2, h3, h1, ite_eq_right (by omega), ite_eq_left rfl]
      simp [huS]
  rw [roundMsgs, Finset.sum_congr rfl hcount, Finset.sum_ite_mem,
    Finset.inter_eq_right.2 (S_subset K), Finset.sum_const, smul_eq_mul]

end Exec

theorem sum_range_two_mul (f : ℕ → ℕ) (K : ℕ) :
    ∑ r ∈ range (2 * K), f r = ∑ t ∈ range K, (f (2 * t) + f (2 * t + 1)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [show 2 * (K + 1) = 2 * K + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- **Message count** of the algorithm: iteration `t + 1` costs at most
`2 · s_t · min(d (t+1), n-1)` messages (requests and replies), the final round `s_K · (n-1)`, where
`s_t = (S d p I t).card` is the number of survivors after `t` iterations. -/
theorem msgs_le {I : Finset ℕ} {p : PortMap m} (hI : I.card = m + 1) (hp : IsPortMap p I) :
    msgs (alg m K d) p (2 * K + 1) I ≤
      ∑ t ∈ range K, 2 * (S d p I t).card * min m (d (t + 1)) + (S d p I K).card * m := by
  rw [msgs, Finset.sum_range_succ, sum_range_two_mul (fun r => roundMsgs (alg m K d) p r I),
    roundMsgs_final hI hp]
  gcongr with t ht
  have ht' := Finset.mem_range.1 ht
  rw [roundMsgs_even hI hp ht']
  have := roundMsgs_odd hI hp ht' (d := d)
  linarith

/-- **Theorem 3.10** (correctness): for every ID universe and all parameters `K`, `d`, exactly one
node (the one with the maximum ID) outputs "leader" after `2K + 1` rounds. -/
theorem electsBy (U : Finset ℕ) : ElectsBy (alg m K d) U (2 * K + 1) := by
  intro I _ hI p hp
  have hne : I.Nonempty := by rw [← Finset.card_pos, hI]; omega
  rw [leaders_eq hI hp hne, Finset.card_singleton]

/-- **Theorem 3.10** (time): the algorithm terminates after `2K + 1` rounds. -/
theorem terminatesBy (U : Finset ℕ) : TerminatesBy (alg m K d) U (2 * K + 1) := by
  intro I _ hI p hp u hu
  refine ⟨by rw [alg_output, (run_final hI hp u hu).2]; rfl, fun r hr => ?_⟩
  obtain ⟨t, rfl⟩ : ∃ t, r = 2 * K + 1 + t := ⟨r - (2 * K + 1), by omega⟩
  obtain ⟨h1, h2⟩ := run_post hI hp t u hu
  exact ⟨by rw [alg_output, alg_output, h2], sendCount_post (by rw [h1]; omega)⟩

/-- An explicit worst-case message bound: with `b 0 = n` and `b t = ⌊n / min(d t, n-1)⌋` (the
survivor bound) the algorithm sends at most `∑_{t<K} 2·b t·min(d (t+1), n-1) + b K·(n-1)`
messages, provided `d t ≥ 1` for `1 ≤ t ≤ K`. -/
theorem msgBound_general (hd : ∀ t, 1 ≤ t → t ≤ K → 1 ≤ d t) (U : Finset ℕ) :
    MsgBound (alg m K d) U (2 * K + 1)
      (∑ t ∈ range K, 2 * (if t = 0 then m + 1 else (m + 1) / min m (d t)) * min m (d (t + 1)) +
        (if K = 0 then m + 1 else (m + 1) / min m (d K)) * m : ℕ) := by
  intro I _ hI p hp
  have hb : ∀ t ≤ K, m ≠ 0 → (S d p I t).card ≤ if t = 0 then m + 1 else (m + 1) / min m (d t) := by
    intro t ht hm
    rcases t with _ | t
    · simp [S, hI]
    · rw [ite_eq_right (Nat.succ_ne_zero t), Nat.le_div_iff_mul_le]
      · exact card_S_mul_le hp hI t
      · have := hd (t + 1) (by omega) ht
        omega
  norm_cast
  refine (msgs_le hI hp).trans ?_
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · gcongr with t ht
    · exact hb t (Finset.mem_range.1 ht).le hm.ne'
    · exact hb K le_rfl hm.ne'

/-- **Asymptotic message bound.** If `q ≥ 1`, `q^{K+1} = n` and `q^t ≤ d t ≤ 2 q^t` for
`1 ≤ t ≤ K`, then the algorithm sends at most `8 (K+1) · n · q` messages. -/
theorem msgBound_real (q : ℝ) (hq : 1 ≤ q) (hqn : q ^ (K + 1) = m + 1)
    (hd : ∀ t, 1 ≤ t → t ≤ K → q ^ t ≤ d t ∧ (d t : ℝ) ≤ 2 * q ^ t) (U : Finset ℕ) :
    MsgBound (alg m K d) U (2 * K + 1) (8 * (K + 1) * (m + 1) * q) := by
  intro I _ hI p hp
  have hq0 : 0 < q := by linarith
  have hmain := msgs_le (K := K) (d := d) hI hp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · have : msgs (alg m K d) p (2 * K + 1) I = 0 := by
      apply Nat.eq_zero_of_le_zero
      refine hmain.trans ?_
      subst hm
      simp
    rw [this]
    push_cast
    positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  -- `q^t ≤ n` for `t ≤ K + 1`
  have hqt : ∀ t ≤ K + 1, q ^ t ≤ m + 1 := by
    intro t ht
    rw [← hqn]
    exact pow_le_pow_right₀ hq ht
  -- `|S t| · q^t ≤ 2n`
  have hS : ∀ t ≤ K, ((S d p I t).card : ℝ) * q ^ t ≤ 2 * (m + 1) := by
    intro t ht
    rcases t with _ | t
    · simp [S, hI]
      linarith
    · have h1 : ((S d p I (t + 1)).card : ℝ) * (min m (d (t + 1)) : ℕ) ≤ m + 1 := by
        exact_mod_cast card_S_mul_le hp hI t
      have h2 : q ^ (t + 1) ≤ 2 * ((min m (d (t + 1)) : ℕ) : ℝ) := by
        rw [Nat.cast_min]
        rcases le_total (m : ℝ) (d (t + 1)) with h | h
        · rw [min_eq_left h]
          have := hqt (t + 1) (by omega)
          linarith
        · rw [min_eq_right h]
          have := (hd (t + 1) (by omega) ht).1
          have : (0 : ℝ) ≤ d (t + 1) := by positivity
          linarith
      have h3 : (0 : ℝ) ≤ (S d p I (t + 1)).card := by positivity
      nlinarith
  have hterm : ∀ t < K, ((2 * (S d p I t).card * min m (d (t + 1)) : ℕ) : ℝ) ≤
      8 * (m + 1) * q := by
    intro t ht
    have h1 := hS t ht.le
    have h2 : min (m : ℝ) (d (t + 1) : ℝ) ≤ 2 * q ^ t * q := by
      rw [mul_assoc, ← pow_succ]
      exact (min_le_right _ _).trans (hd (t + 1) (by omega) (by omega)).2
    have h3 : (0 : ℝ) ≤ (S d p I t).card := by positivity
    have h4 : (0 : ℝ) ≤ q ^ t := by positivity
    push_cast
    calc 2 * ((S d p I t).card : ℝ) * min (m : ℝ) (d (t + 1) : ℝ)
        ≤ 2 * (S d p I t).card * (2 * q ^ t * q) := by gcongr
      _ = 4 * q * ((S d p I t).card * q ^ t) := by ring
      _ ≤ 4 * q * (2 * (m + 1)) := by gcongr
      _ = 8 * (m + 1) * q := by ring
  have hlast : ((S d p I K).card : ℝ) * m ≤ 2 * (m + 1) * q := by
    have h1 := hS K le_rfl
    have h2 : (m : ℝ) ≤ q ^ K * q := by rw [← pow_succ, hqn]; linarith
    have h3 : (0 : ℝ) ≤ (S d p I K).card := by positivity
    calc ((S d p I K).card : ℝ) * m ≤ (S d p I K).card * (q ^ K * q) := by gcongr
      _ = ((S d p I K).card * q ^ K) * q := by ring
      _ ≤ 2 * (m + 1) * q := by gcongr
  have hsum : (∑ t ∈ range K, ((2 * (S d p I t).card * min m (d (t + 1)) : ℕ) : ℝ)) ≤
      K * (8 * (m + 1) * q) := by
    calc (∑ t ∈ range K, ((2 * (S d p I t).card * min m (d (t + 1)) : ℕ) : ℝ))
        ≤ ∑ t ∈ range K, 8 * (m + 1) * q :=
          Finset.sum_le_sum fun t ht => hterm t (Finset.mem_range.1 ht)
      _ = K * (8 * (m + 1) * q) := by simp
  have hmain' : (msgs (alg m K d) p (2 * K + 1) I : ℝ) ≤
      ∑ t ∈ range K, ((2 * (S d p I t).card * min m (d (t + 1)) : ℕ) : ℝ) +
        ((S d p I K).card : ℝ) * m := by
    exact_mod_cast hmain
  have hmq : (0 : ℝ) ≤ (m + 1) * q := by positivity
  nlinarith

/-- **Theorem 3.10.** Synchronous clique, simultaneous wake-up: for every odd `ℓ = 2K + 1` the
algorithm with `K` iterations and `d i = ⌈n^{i/(K+1)}⌉` (`n = m + 1`) elects a leader and terminates
in `ℓ` rounds and sends at most `4 (ℓ + 1) · n^{1 + 2/(ℓ+1)}` messages, for every ID universe. (The
paper's `k` is `K + 2`; the paper requires `ℓ ≥ 3`, i.e. `K ≥ 1`, but the bound also holds for
`K = 0`.) -/
theorem theorem_3_10 (K : ℕ) (U : Finset ℕ) :
    let n : ℝ := m + 1
    let d : ℕ → ℕ := fun i => ⌈n ^ ((i : ℝ) / (K + 1))⌉₊
    let ℓ := 2 * K + 1
    ElectsBy (alg m K d) U ℓ ∧ TerminatesBy (alg m K d) U ℓ ∧
      MsgBound (alg m K d) U ℓ (4 * (ℓ + 1) * n ^ (1 + 2 / (ℓ + 1 : ℝ))) := by
  intro n d ℓ
  refine ⟨electsBy U, terminatesBy U, ?_⟩
  have hn : (1 : ℝ) ≤ n := by simp only [n]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hn0 : (0 : ℝ) < n := by linarith
  set q : ℝ := n ^ ((1 : ℝ) / (K + 1)) with hqdef
  have hK1 : (0 : ℝ) < K + 1 := by positivity
  have hq : 1 ≤ q := Real.one_le_rpow hn (by positivity)
  have hqt : ∀ t : ℕ, q ^ t = n ^ ((t : ℝ) / (K + 1)) := by
    intro t
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    ring
  have hqn : q ^ (K + 1) = m + 1 := by
    rw [hqt]
    push_cast
    rw [div_self hK1.ne', Real.rpow_one]
  have hd : ∀ t, 1 ≤ t → t ≤ K → q ^ t ≤ d t ∧ (d t : ℝ) ≤ 2 * q ^ t := by
    intro t _ _
    simp only [d]
    rw [← hqt]
    have h1 : 1 ≤ q ^ t := one_le_pow₀ hq
    refine ⟨Nat.le_ceil _, ?_⟩
    have := Nat.ceil_lt_add_one (show 0 ≤ q ^ t by linarith)
    linarith
  have hb := msgBound_real q hq hqn hd U
  have heq : (4 * ((ℓ : ℕ) + 1 : ℝ)) * n ^ (1 + 2 / ((ℓ : ℕ) + 1 : ℝ)) =
      8 * (K + 1) * (m + 1) * q := by
    simp only [ℓ]
    push_cast
    rw [Real.rpow_add hn0, Real.rpow_one, hqdef,
      show (2 : ℝ) / (2 * K + 1 + 1) = 1 / (K + 1) by field_simp; ring]
    simp only [n]
    ring
  intro I hIU hI p hp
  have := hb I hIU hI p hp
  simp only [ℓ] at heq ⊢
  push_cast at heq ⊢
  rw [heq]
  exact this

end Referees

end LeaderTradeoffs
