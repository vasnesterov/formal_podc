import Papers.PODC2021.RandomizedSymmetryTopology.MessagePassing

/-!
# Theorem 4.2 ("if" direction) in the standard port-numbering model

Fraigniaud, Gelles, Lotker, PODC 2021, Section 4.2.

In the standard port-numbering model a party may send different messages on different ports, so a
full-information protocol sends, on port `p`, its whole history together with `p`. The receiver
then learns the port number at the sender's end. Knowledge becomes
`Kᵢ(t) = (Kᵢ(t-1), Xᵢ(t), ((q₁, K_{πᵢ(1)}(t-1)), …, (q_{n-1}, K_{πᵢ(n-1)}(t-1))))`, where `q_p`
is the port of `πᵢ(p)` leading back to `i` (`backPort`). This is Eq. (2) with the back-ports added.

Main result:
* `theorem_4_2_if_twoSided`: if `gcd(n₁, …, n_k) = 1`, leader election is eventually solvable for
  every port numbering. Together with `corollary_4_4_standard` this is Theorem 4.2 in the standard
  model, the model used by the full version's proof (procedure CreateMatching).

## Proof

Run the sources so that, after `k` rounds, parties on different sources have different bits. The
partition of the parties into knowledge classes only gets finer, so within `n + 1` further rounds
there is a round `t` where it does not change. At such a round, two parties in the same class `C`
see, behind each port `p`, parties of the same class `D` with the same back-port `q`. Hence
`c ↦ πc(p)` maps `C` injectively into `D` (its left inverse is `d ↦ πd(q)`), and all classes have the
same size `m` (`card_class_le`). Each source is a union of classes, so `m` divides every `nⱼ`,
hence `m = 1`: every party is alone in its class.
-/

open Finset Filter Topology

namespace Podc.RandomizedSymmetryTopology

variable {n k : ℕ}

/-- The port of party `π i p` that leads back to `i`. -/
def backPort (π : PortNumbering n) (i : Fin n) (p : Fin (n - 1)) : Fin (n - 1) :=
  (π (π i p)).symm ⟨i, fun h => (π i p).2 h.symm⟩

theorem π_backPort (π : PortNumbering n) (i : Fin n) (p : Fin (n - 1)) :
    (π (π i p) (backPort π i p) : Fin n) = i := by
  simp [backPort]

/-- Knowledge values in the standard (two-sided) port model with `d = n - 1` ports. -/
def TSKnow (d : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => TSKnow d t × Bool × (Fin d → Fin d × TSKnow d t)

/-- Knowledge in the standard port model: Eq. (2) where the message received on port `p` also
carries the sender's port `backPort π i p`. -/
def tsK (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) :
    (t : ℕ) → Fin n → TSKnow (n - 1) t
  | 0 => fun _ => ()
  | t + 1 => fun i =>
    ((tsK α π ω t i, ω t (α i), fun p => (backPort π i p, tsK α π ω t (π i p))) :
      TSKnow (n - 1) t × Bool × (Fin (n - 1) → Fin (n - 1) × TSKnow (n - 1) t))

theorem tsK_succ (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ) (i : Fin n) :
    tsK α π ω (t + 1) i =
      ((tsK α π ω t i, ω t (α i), fun p => (backPort π i p, tsK α π ω t (π i p))) :
        TSKnow (n - 1) t × Bool × (Fin (n - 1) → Fin (n - 1) × TSKnow (n - 1) t)) := rfl

theorem tsK_isLocal (α : Fin n → Fin k) (π : PortNumbering n) (ω ω' : Stream k) (t : ℕ)
    (h : ∀ s < t, ω s = ω' s) : tsK α π ω t = tsK α π ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih fun s hs => h s (by omega)
    funext i
    rw [tsK_succ, tsK_succ, ih, h t (by omega)]

theorem tsK_shift (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (s u : ℕ) :
    ∃ g : TSKnow (n - 1) (s + u) → TSKnow (n - 1) u,
      ∀ i, tsK α π (shiftStream ω s) u i = g (tsK α π ω (s + u) i) := by
  induction u with
  | zero => exact ⟨fun _ => (), fun _ => rfl⟩
  | succ u ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨fun x => ((g x.1, x.2.1, fun p => ((x.2.2 p).1, g (x.2.2 p).2)) :
      TSKnow (n - 1) u × Bool × (Fin (n - 1) → Fin (n - 1) × TSKnow (n - 1) u)), fun i => ?_⟩
    show tsK α π (shiftStream ω s) (u + 1) i = _
    rw [tsK_succ]
    change _ = ((g (tsK α π ω (s + u) i), ω (s + u) (α i),
      fun p => (backPort π i p, g (tsK α π ω (s + u) (π i p)))) :
        TSKnow (n - 1) u × Bool × (Fin (n - 1) → Fin (n - 1) × TSKnow (n - 1) u))
    congr 2
    · exact hg i
    · funext p; rw [hg]

/-- The standard port model with port numbering `π` as a full-information model. -/
def tsModel (α : Fin n → Fin k) (π : PortNumbering n) : FullInfoModel n k where
  Know := TSKnow (n - 1)
  K := tsK α π
  isLocal ω ω' t h := tsK_isLocal α π ω ω' t h
  prev t := ⟨fun x =>
    (show TSKnow (n - 1) t × Bool × (Fin (n - 1) → Fin (n - 1) × TSKnow (n - 1) t) from x).1,
    fun _ _ => rfl⟩
  shift ω s u := tsK_shift α π ω s u

theorem tsK_eq_of_succ (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) {t : ℕ}
    {i j : Fin n} (h : tsK α π ω (t + 1) i = tsK α π ω (t + 1) j) :
    tsK α π ω t i = tsK α π ω t j := by
  rw [tsK_succ, tsK_succ] at h
  exact (Prod.mk.inj h).1

/-- Knowledge contains the own random bits. -/
theorem bits_eq_of_tsK_eq (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) {t : ℕ}
    {i j : Fin n} (h : tsK α π ω t i = tsK α π ω t j) : ∀ s < t, ω s (α i) = ω s (α j) := by
  induction t with
  | zero => intro s hs; omega
  | succ t ih =>
    have h0 := tsK_eq_of_succ α π ω h
    rw [tsK_succ, tsK_succ] at h
    intro s hs
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · exact ih h0 s hs
    · exact (Prod.mk.inj (Prod.mk.inj h).2).1

open Classical in
/-- At a round where the knowledge partition is stable, all knowledge classes have the same size:
`c ↦ π c p` maps the class of `x` injectively into the class of `y = π x p`. -/
theorem card_class_le (α : Fin n → Fin k) (π : PortNumbering n)
    (ω : Stream k) (t : ℕ)
    (hst : ∀ i j, tsK α π ω t i = tsK α π ω t j → tsK α π ω (t + 1) i = tsK α π ω (t + 1) j)
    {x y : Fin n} (hxy : x ≠ y) :
    (univ.filter fun c => tsK α π ω t c = tsK α π ω t x).card ≤
      (univ.filter fun d => tsK α π ω t d = tsK α π ω t y).card := by
  set p := (π x).symm ⟨y, hxy.symm⟩
  have hp : (π x p : Fin n) = y := by simp [p]
  -- for `c` in the class of `x`, the same port leads to the class of `y`, with the same back-port
  have key : ∀ c, tsK α π ω t c = tsK α π ω t x →
      backPort π c p = backPort π x p ∧ tsK α π ω t (π c p) = tsK α π ω t y := by
    intro c hc
    have h := hst c x hc
    rw [tsK_succ, tsK_succ] at h
    have h2 := congrFun (Prod.mk.inj (Prod.mk.inj h).2).2 p
    rw [← hp]
    exact Prod.mk.inj h2
  refine Finset.card_le_card_of_injOn (fun c => (π c p : Fin n)) ?_ ?_
  · intro c hc
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc ⊢
    exact (key c hc).2
  · intro c₁ hc₁ c₂ hc₂ h12
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hc₁ hc₂
    have e₁ := π_backPort π c₁ p
    have e₂ := π_backPort π c₂ p
    rw [(key c₁ hc₁).1] at e₁
    rw [(key c₂ hc₂).1] at e₂
    simp only at h12
    have hf : ∀ a b : Fin n, a = b → ∀ q, (π a q : Fin n) = π b q := by rintro a _ rfl q; rfl
    rw [← e₁, ← e₂]
    exact hf _ _ h12 _

/-- Forget the last round of a knowledge value. -/
def TSKnow.prev {d t : ℕ} (x : TSKnow d (t + 1)) : TSKnow d t :=
  (show TSKnow d t × Bool × (Fin d → Fin d × TSKnow d t) from x).1

theorem image_tsK_eq (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ)
    [DecidableEq (TSKnow (n - 1) t)] [DecidableEq (TSKnow (n - 1) (t + 1))] :
    univ.image (tsK α π ω t) = (univ.image (tsK α π ω (t + 1))).image TSKnow.prev := by
  rw [Finset.image_image]; rfl

/-- The number of knowledge classes at time `t`. -/
noncomputable def numClasses (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ) : ℕ :=
  by classical exact (univ.image (tsK α π ω t)).card

theorem numClasses_le_succ (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ) :
    numClasses α π ω t ≤ numClasses α π ω (t + 1) := by
  classical
  unfold numClasses
  rw [image_tsK_eq]
  exact card_image_le

/-- If the number of classes does not grow, equal knowledge stays equal one round later. -/
theorem tsK_succ_eq_of_numClasses (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ)
    (h : numClasses α π ω t = numClasses α π ω (t + 1)) (i j : Fin n)
    (hij : tsK α π ω t i = tsK α π ω t j) : tsK α π ω (t + 1) i = tsK α π ω (t + 1) j := by
  classical
  unfold numClasses at h
  rw [image_tsK_eq] at h
  have hinj := Finset.card_image_iff.1 (by convert h)
  exact hinj (mem_coe.2 (mem_image_of_mem _ (mem_univ i)))
    (mem_coe.2 (mem_image_of_mem _ (mem_univ j))) hij

theorem numClasses_le (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ) :
    numClasses α π ω t ≤ n := by
  classical
  unfold numClasses
  convert card_image_le (s := (univ : Finset (Fin n)))
  simp

theorem one_le_numClasses (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t : ℕ)
    (hn : 0 < n) : 1 ≤ numClasses α π ω t := by
  classical
  unfold numClasses
  exact card_pos.2 (Finset.image_nonempty.2 ⟨⟨0, hn⟩, mem_univ _⟩)

/-- Within `n` rounds after `t₀` there is a round where the partition is stable. -/
theorem exists_stable (α : Fin n → Fin k) (π : PortNumbering n) (ω : Stream k) (t₀ : ℕ)
    (hn : 0 < n) : ∃ t, t₀ ≤ t ∧ numClasses α π ω t = numClasses α π ω (t + 1) := by
  by_contra hc
  push Not at hc
  have hgrow : ∀ m, numClasses α π ω t₀ + m ≤ numClasses α π ω (t₀ + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := numClasses_le_succ α π ω (t₀ + m)
      have h2 := hc (t₀ + m) (by omega)
      rw [show t₀ + (m + 1) = t₀ + m + 1 by omega]
      omega
  have := hgrow n
  have := numClasses_le α π ω (t₀ + n)
  have := one_le_numClasses α π ω t₀ hn
  omega

/-- The stream used in the proof: in round `s + 1 ≤ k` only source `s` emits `1`. -/
def separating (k : ℕ) : Stream k := fun s j => decide (s = j.val)

/-- **Theorem 4.2, "if" direction, in the standard port model.** If `gcd(n₁, …, n_k) = 1`, then
for every port numbering of `Kₙ` leader election is eventually solvable. -/
theorem theorem_4_2_if_twoSided (α : Fin n → Fin k) (hg : univ.gcd (load α) = 1)
    (π : PortNumbering n) : EventuallySolvable (tsModel α π) (leaderElection n) := by
  classical
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      have : univ.gcd (load α) = 0 := Finset.gcd_eq_zero_iff.2 fun j _ => by
        simp [load]
      omega
    · exact h
  set ω := separating k
  obtain ⟨t, hkt, hst⟩ := exists_stable α π ω k hn
  have hst' := tsK_succ_eq_of_numClasses α π ω t hst
  -- equal knowledge at time `t ≥ k` implies the same source
  have hsrc : ∀ i j, tsK α π ω t i = tsK α π ω t j → α i = α j := by
    intro i j h
    have := bits_eq_of_tsK_eq α π ω h (α i).val (by omega)
    simp only [ω, separating, decide_true] at this
    exact Fin.ext (of_decide_eq_true this.symm)
  set cls := fun x => univ.filter fun c => tsK α π ω t c = tsK α π ω t x
  -- all classes have the same size
  have hcard : ∀ x, (cls x).card = (cls ⟨0, hn⟩).card := by
    intro x
    by_cases hx : tsK α π ω t x = tsK α π ω t ⟨0, hn⟩
    · simp only [cls, hx]
    · have hne : x ≠ ⟨0, hn⟩ := fun h => hx (h ▸ rfl)
      exact le_antisymm (card_class_le α π ω t hst' hne) (card_class_le α π ω t hst' hne.symm)
  set m := (cls ⟨0, hn⟩).card
  -- `m` divides every load
  have hdvd : ∀ j, m ∣ load α j := by
    intro j
    unfold load
    rw [card_eq_sum_card_fiberwise (f := tsK α π ω t)
      (t := (univ.filter fun i => α i = j).image (tsK α π ω t)) (fun x hx => mem_image_of_mem _ hx)]
    refine Finset.dvd_sum fun v hv => ?_
    obtain ⟨x, hx, rfl⟩ := mem_image.1 hv
    have : (univ.filter fun i => α i = j).filter (fun i => tsK α π ω t i = tsK α π ω t x) =
        cls x := by
      ext c
      simp only [cls, mem_filter, mem_univ, true_and] at hx ⊢
      exact ⟨fun h => h.2, fun h => ⟨(hsrc c x h).trans hx, h⟩⟩
    rw [this, hcard x]
  have hm : m = 1 := Nat.dvd_one.1 (hg ▸ Finset.dvd_gcd fun j _ => hdvd j)
  -- hence party `0` is alone in its class, and the realization of length `t` solves
  apply eventuallySolvable_of_pos (t := t)
  rw [probSolves_pos_iff]
  refine ⟨fun s => ω s, (solves_leaderElection_iff _).2 ⟨⟨0, hn⟩, fun j hj heq => hj ?_⟩⟩
  have hloc : tsK α π (ext fun s : Fin t => ω s) t = tsK α π ω t :=
    tsK_isLocal α π _ _ t fun s hs => ext_of_lt _ hs
  change tsK α π (ext fun s : Fin t => ω s) t j = tsK α π (ext fun s : Fin t => ω s) t ⟨0, hn⟩
    at heq
  rw [hloc] at heq
  have h0 : ⟨0, hn⟩ ∈ cls ⟨0, hn⟩ := by simp [cls]
  have hj' : j ∈ cls ⟨0, hn⟩ := by simp [cls, heq]
  exact Finset.card_le_one.1 (hm ▸ le_refl _) j hj' ⟨0, hn⟩ h0

/-- The instance `n₁ = 2`, `n₂ = 3` that refutes Theorem 4.2 in the model of Eq. (2)
(`theorem_4_2_counterexample`) is solvable for every port numbering in the standard model. -/
example (π : PortNumbering 5) : EventuallySolvable (tsModel α₅ π) (leaderElection 5) :=
  theorem_4_2_if_twoSided α₅ gcd_load_α₅ π

end Podc.RandomizedSymmetryTopology
