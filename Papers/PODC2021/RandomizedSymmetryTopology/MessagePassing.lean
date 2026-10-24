import Papers.PODC2021.RandomizedSymmetryTopology.Blackboard
import Papers.PODC2021.RandomizedSymmetryTopology.Realization

/-!
# The message-passing model (Eq. (2)), Lemma 4.3 and Theorem 4.2

Fraigniaud, Gelles, Lotker, PODC 2021, Section 4.2.

The parties form a clique `Kₙ`; every party `i` numbers its `n - 1` incident channels by a
bijection `π i : Fin (n - 1) ≃ {j // j ≠ i}` (`PortNumbering`). Knowledge (Eq. (2)):
`Kᵢ(t) = (Kᵢ(t-1), Xᵢ(t), K_{πᵢ(1)}(t-1), …, K_{πᵢ(n-1)}(t-1))`:
a party learns the knowledge of the neighbour behind each of its ports, but nothing about the port
number at the other end (in a full-information protocol every party sends the same message —
its whole history — on every port).

Main results:
* `mpK_eq_of_equitable`: an *equitable* partition of the parties (constant source on each class,
  and parties of the same class see the same classes behind the same ports) is never refined.
* `swapPorts`: for every configuration `α`, a port numbering for which parties connected to the
  same source see the same sequence of sources behind their ports; then parties with the same
  source always have the same knowledge (`mpK_swapPorts_eq`).
* `lemma_4_3`: for this numbering, every consistency class (facet of `π̃(ρ)`) has size divisible
  by `g = gcd(n₁, …, n_k)`.
* `corollary_4_4` (the "only if" direction of Theorem 4.2): if `gcd > 1`, some port numbering
  makes leader election impossible.
* `worstCase_iff`: the correct characterization for the model of Eq. (2): worst-case leader
  election is eventually solvable iff some source is connected to exactly one party — the same
  condition as in the blackboard model.
* `theorem_4_2_if_false`: hence the "if" direction of Theorem 4.2 is false for this model:
  `n = 5`, two sources with `n₁ = 2`, `n₂ = 3` (`gcd = 1`), and a port numbering under which
  leader election is never solved.
-/

open Finset Filter Topology

namespace Podc.RandomizedSymmetryTopology

/-- A port numbering of the clique on `Fin n`: port `p` of party `i` leads to `π i p ≠ i`, and
every other party is behind exactly one port. -/
abbrev PortNumbering (n : ℕ) : Type := (i : Fin n) → Fin (n - 1) ≃ {j : Fin n // j ≠ i}

/-- Knowledge values in the message-passing model with `d = n - 1` ports. -/
def MPKnow (d : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => MPKnow d t × Bool × (Fin d → MPKnow d t)

variable {n k : ℕ}

/-- **Eq. (2).** Knowledge of party `i` at time `t` in the message-passing model with port
numbering `π`. -/
def mpK (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) :
    (t : ℕ) → Fin n → MPKnow (n - 1) t
  | 0 => fun _ => ()
  | t + 1 => fun i =>
    ((mpK α π ω t i, ω t (α i), fun p => mpK α π ω t (π i p)) :
      MPKnow (n - 1) t × Bool × (Fin (n - 1) → MPKnow (n - 1) t))

theorem mpK_succ (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ) (i : Fin n) :
    mpK α π ω (t + 1) i =
      ((mpK α π ω t i, ω t (α i), fun p => mpK α π ω t (π i p)) :
        MPKnow (n - 1) t × Bool × (Fin (n - 1) → MPKnow (n - 1) t)) := rfl

theorem mpK_isLocal (α : Fin n → Fin k) (π : PortNumbering n) (ω ω' : Stream k) (t : ℕ)
    (h : ∀ s < t, ω s = ω' s) : mpK α π ω t = mpK α π ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih fun s hs => h s (by omega)
    funext i
    rw [mpK_succ, mpK_succ, ih, h t (by omega)]

theorem mpK_shift (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (s u : ℕ) :
    ∃ g : MPKnow (n - 1) (s + u) → MPKnow (n - 1) u,
      ∀ i, mpK α π (shiftStream ω s) u i = g (mpK α π ω (s + u) i) := by
  induction u with
  | zero => exact ⟨fun _ => (), fun _ => rfl⟩
  | succ u ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨fun x => ((g x.1, x.2.1, g ∘ x.2.2) :
      MPKnow (n - 1) u × Bool × (Fin (n - 1) → MPKnow (n - 1) u)), fun i => ?_⟩
    show mpK α π (shiftStream ω s) (u + 1) i = _
    rw [mpK_succ]
    change _ = ((g (mpK α π ω (s + u) i), ω (s + u) (α i),
      g ∘ fun p => mpK α π ω (s + u) (π i p)) :
        MPKnow (n - 1) u × Bool × (Fin (n - 1) → MPKnow (n - 1) u))
    congr 2
    · exact hg i
    · funext p; exact hg _

/-- The message-passing model with port numbering `π` as a full-information model. -/
def mpModel (α : Fin n → Fin k) (π : PortNumbering n) : FullInfoModel n k where
  Know := MPKnow (n - 1)
  K := mpK α π
  isLocal ω ω' t h := mpK_isLocal α π ω ω' t h
  prev t := ⟨fun x => (show MPKnow (n - 1) t × Bool × (Fin (n - 1) → MPKnow (n - 1) t) from x).1,
    fun _ _ => rfl⟩
  shift ω s u := mpK_shift α π ω s u

/-- Knowledge contains the own random bits: equal knowledge implies equal random strings. -/
theorem bits_eq_of_mpK_eq (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) {t : ℕ}
    {i j : Fin n} (h : mpK α π ω t i = mpK α π ω t j) : ∀ s < t, ω s (α i) = ω s (α j) := by
  induction t with
  | zero => intro s hs; omega
  | succ t ih =>
    rw [mpK_succ, mpK_succ] at h
    have h1 := Prod.mk.inj h
    have h2 := Prod.mk.inj h1.2
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · exact ih h1.1 s hs
    · exact h2.1

/-- **Equitable partitions are never refined.** If `c` is constant-source on its classes and
parties of the same class see parties of the same classes behind each port, then parties of the
same class have the same knowledge forever, whatever the random bits. -/
theorem mpK_eq_of_equitable {C : Type*} (α : Fin n → Fin k) (π : PortNumbering n) (c : Fin n → C)
    (hα : ∀ i j, c i = c j → α i = α j)
    (hπ : ∀ i j, c i = c j → ∀ p, c (π i p) = c (π j p)) (ω : Stream k) (t : ℕ) :
    ∀ i j, c i = c j → mpK α π ω t i = mpK α π ω t j := by
  induction t with
  | zero => intro _ _ _; rfl
  | succ t ih =>
    intro i j hij
    rw [mpK_succ, mpK_succ, ih i j hij, hα i j hij]
    congr 2
    funext p
    exact ih _ _ (hπ i j hij p)

/-! ### A port numbering that preserves the source classes -/

/-- An arbitrary port numbering. -/
noncomputable def basePorts (n : ℕ) : PortNumbering n := fun i =>
  (Fintype.equivOfCardEq (by simp [Fintype.card_subtype_compl])).symm

/-- A representative of the source class of `i` (it depends only on `α i`). -/
noncomputable def rep (α : Fin n → Fin k) (i : Fin n) : Fin n :=
  Classical.choose (⟨i, rfl⟩ : ∃ j, α j = α i)

theorem α_rep (α : Fin n → Fin k) (i : Fin n) : α (rep α i) = α i :=
  Classical.choose_spec (⟨i, rfl⟩ : ∃ j, α j = α i)

theorem rep_eq_rep (α : Fin n → Fin k) {i j : Fin n} (h : α i = α j) : rep α i = rep α j := by
  unfold rep
  have : (fun j' => α j' = α i) = (fun j' => α j' = α j) := by rw [h]
  congr 1

/-- The adversarial port numbering: party `i` uses the numbering of the representative `r` of its
source class, transported by the transposition `(r i)` (which preserves sources). Hence parties
with the same source see the same sources behind each port. -/
noncomputable def swapPorts (α : Fin n → Fin k) : PortNumbering n := fun i =>
  (basePorts n (rep α i)).trans
    ((Equiv.swap (rep α i) i).subtypeEquiv fun x => by
      constructor
      · intro hx h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact hx h
      · intro hx h
        exact hx (by rw [h, Equiv.swap_apply_left]))

theorem α_swap (α : Fin n → Fin k) (i x : Fin n) : α (Equiv.swap (rep α i) i x) = α x := by
  rcases eq_or_ne x (rep α i) with rfl | h1
  · rw [Equiv.swap_apply_left, α_rep α i]
  rcases eq_or_ne x i with rfl | h2
  · rw [Equiv.swap_apply_right, α_rep α x]
  · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem α_swapPorts (α : Fin n → Fin k) (i : Fin n) (p : Fin (n - 1)) :
    α (swapPorts α i p) = α (basePorts n (rep α i) p) := by
  simp [swapPorts, α_swap]

/-- With `swapPorts α`, parties connected to the same source always have the same knowledge. -/
theorem mpK_swapPorts_eq (α : Fin n → Fin k) (ω : Stream k) (t : ℕ) {i j : Fin n}
    (h : α i = α j) : mpK α (swapPorts α) ω t i = mpK α (swapPorts α) ω t j :=
  mpK_eq_of_equitable α (swapPorts α) α (fun _ _ h => h)
    (fun i j h p => by rw [α_swapPorts α i, α_swapPorts α j, rep_eq_rep α h]) ω t i j h

/-! ### Lemma 4.3 and Corollary 4.4 -/

/-- **Lemma 4.3.** If `g` divides every load `nⱼ` (e.g. `g = gcd(n₁, …, n_k)`), there is a port
numbering such that, for every realization and every time `t`, every facet `γ` of the consistency
projection `π̃(ρ)` has `g ∣ dim γ + 1 = |γ|`. -/
theorem lemma_4_3 (α : Fin n → Fin k) (g : ℕ) (hg : ∀ j, g ∣ load α j) :
    ∃ π : PortNumbering n, ∀ (ω : Stream k) (t : ℕ) (γ : Finset (Fin n)),
      IsFacet (consistencyComplex (mpK α π ω t)) γ → g ∣ γ.card := by
  classical
  refine ⟨swapPorts α, fun ω t γ hγ => ?_⟩
  obtain ⟨i, rfl⟩ := (isFacet_consistencyComplex_iff _ γ).1 hγ
  set C := univ.filter fun j => mpK α (swapPorts α) ω t j = mpK α (swapPorts α) ω t i
  rw [card_eq_sum_card_fiberwise (f := α) (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.dvd_sum fun s _ => ?_
  by_cases hs : ∃ j ∈ C, α j = s
  · obtain ⟨j, hj, rfl⟩ := hs
    have : C.filter (fun x => α x = α j) = univ.filter fun x => α x = α j := by
      ext x
      simp only [C, mem_filter, mem_univ, true_and] at hj ⊢
      constructor
      · exact fun h => h.2
      · intro hx; exact ⟨(mpK_swapPorts_eq α ω t hx).trans hj, hx⟩
    rw [this]; exact hg _
  · push Not at hs
    rw [Finset.filter_false_of_mem hs, card_empty]
    exact dvd_zero g

/-- If no source has load `1`, then with `swapPorts α` leader election is never solved. -/
theorem probSolves_swapPorts_eq_zero (α : Fin n → Fin k) (h : ∀ j, load α j ≠ 1) (t : ℕ) :
    probSolves (mpModel α (swapPorts α)) (leaderElection n) t = 0 := by
  rw [probSolves_eq_zero_iff]
  intro r hr
  obtain ⟨i, hi⟩ := (solves_leaderElection_iff _).1 hr
  obtain ⟨i', hne, hα⟩ := exists_partner α h i
  exact hi i' hne (mpK_swapPorts_eq α _ t hα)

/-- **Corollary 4.4** ("only if" direction of Theorem 4.2). If `gcd(n₁, …, n_k) > 1`, there is a
port numbering for which leader election is impossible: the probability of solving it is `0` at
every time, so it is not eventually solvable. -/
theorem corollary_4_4 (α : Fin n → Fin k) (hg : 1 < univ.gcd (load α)) :
    ∃ π : PortNumbering n, (∀ t, probSolves (mpModel α π) (leaderElection n) t = 0) ∧
      ¬ EventuallySolvable (mpModel α π) (leaderElection n) := by
  have h : ∀ j, load α j ≠ 1 := fun j hj => by
    have := Finset.gcd_dvd (s := univ) (f := load α) (mem_univ j)
    rw [hj, Nat.dvd_one] at this
    omega
  exact ⟨swapPorts α, probSolves_swapPorts_eq_zero α h,
    not_eventuallySolvable_of_zero _ (probSolves_swapPorts_eq_zero α h)⟩

/-- **The correct characterization for the model of Eq. (2).** Worst-case leader election
(eventually solvable for every port numbering) is possible iff some source is connected to exactly
one party. -/
theorem worstCase_iff (α : Fin n → Fin k) :
    (∀ π : PortNumbering n, EventuallySolvable (mpModel α π) (leaderElection n)) ↔
      ∃ j, load α j = 1 := by
  constructor
  · intro hO
    by_contra hc
    push Not at hc
    exact not_eventuallySolvable_of_zero _ (probSolves_swapPorts_eq_zero α hc) (hO _)
  · rintro ⟨j, hj⟩ π
    obtain ⟨i, hi, hu⟩ := (load_eq_one_iff α j).1 hj
    apply eventuallySolvable_of_pos (t := 1)
    rw [probSolves_pos_iff]
    refine ⟨singleOne j, (solves_leaderElection_iff _).2 ⟨i, fun i' hne heq => ?_⟩⟩
    have := bits_eq_of_mpK_eq α π _ heq 0 (by omega)
    rw [ext_of_lt _ (by omega)] at this
    simp only [singleOne, hi, decide_true, decide_eq_true_eq] at this
    exact hne (hu i' this)

/-! ### The "if" direction of Theorem 4.2 fails -/

/-- Five parties, two sources: parties `0, 1` read source `0`, parties `2, 3, 4` read source `1`. -/
def α₅ : Fin 5 → Fin 2 := fun i => if i.val < 2 then 0 else 1

theorem load_α₅ : load α₅ 0 = 2 ∧ load α₅ 1 = 3 := by decide

theorem gcd_load_α₅ : univ.gcd (load α₅) = 1 := by decide

/-- **Counterexample to Theorem 4.2 ("if" direction)** for the model of Eq. (2): with
`n₁ = 2`, `n₂ = 3` (so `gcd(n₁, n₂) = 1`) there is a port numbering under which no realization
ever solves leader election. -/
theorem theorem_4_2_counterexample :
    ∃ π : PortNumbering 5, (∀ t, probSolves (mpModel α₅ π) (leaderElection 5) t = 0) ∧
      ¬ EventuallySolvable (mpModel α₅ π) (leaderElection 5) := by
  have h : ∀ j, load α₅ j ≠ 1 := by decide
  exact ⟨swapPorts α₅, probSolves_swapPorts_eq_zero α₅ h,
    not_eventuallySolvable_of_zero _ (probSolves_swapPorts_eq_zero α₅ h)⟩

/-- **Theorem 4.2 is false** in the message-passing model of Eq. (2): its "if" direction
(`gcd(n₁, …, n_k) = 1` ⇒ leader election is eventually solvable for every port numbering) fails. -/
theorem theorem_4_2_if_false :
    ¬ ∀ (n k : ℕ) (α : Fin n → Fin k), univ.gcd (load α) = 1 →
      ∀ π : PortNumbering n, EventuallySolvable (mpModel α π) (leaderElection n) := by
  intro h
  obtain ⟨π, -, hπ⟩ := theorem_4_2_counterexample
  exact hπ (h 5 2 α₅ gcd_load_α₅ π)

/-- An explicit port numbering of `K₅`: the ports of party `i` lead to the other parties in
increasing order (`Fin.succAbove`). Parties `0, 1` see sources `0, 1, 1, 1` behind ports
`1, 2, 3, 4`; parties `2, 3, 4` see sources `0, 0, 1, 1`. -/
noncomputable def ports₅ : PortNumbering 5 := fun i =>
  Equiv.ofBijective (fun p : Fin 4 => ⟨i.succAbove p, Fin.succAbove_ne i p⟩)
    (by revert i; decide)

/-- The counterexample with the explicit numbering `ports₅`: the partition by sources is
equitable, so parties `0, 1` (resp. `2, 3, 4`) have equal knowledge forever. -/
theorem theorem_4_2_counterexample_explicit (t : ℕ) :
    probSolves (mpModel α₅ ports₅) (leaderElection 5) t = 0 := by
  have heq : ∀ ω i j, α₅ i = α₅ j → mpK α₅ ports₅ ω t i = mpK α₅ ports₅ ω t j :=
    fun ω => mpK_eq_of_equitable α₅ ports₅ α₅ (fun _ _ h => h) (by decide) ω t
  rw [probSolves_eq_zero_iff]
  intro r hr
  obtain ⟨i, hi⟩ := (solves_leaderElection_iff _).1 hr
  obtain ⟨i', hne, hα⟩ := exists_partner α₅ (by decide) i
  exact hi i' hne (heq _ i' i hα)

end Podc.RandomizedSymmetryTopology
