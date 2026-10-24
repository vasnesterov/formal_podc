import Papers.PODC2021.RandomizedSymmetryTopology.ZeroOne

/-!
# The blackboard model and Theorem 4.1

Fraigniaud, Gelles, Lotker, PODC 2021, Eq. (1) and Theorem 4.1.

Knowledge in the blackboard model (Eq. (1)):
`Kᵢ(t) = (Kᵢ(t-1), Xᵢ(t), {{Kⱼ(t-1) : j ≠ i}})`, where the knowledge of the other parties is a
*multiset* (the content of the blackboard, without origins). `BBKnow t` is the type of knowledge
values at time `t`, defined by recursion on `t`.

Main results:
* `bbK_eq_iff`: two parties have the same knowledge at time `t` iff they received the same `t`
  random bits (used in the paper's proof without proof: "equality of randomness is equivalent to
  equality of knowledge").
* `theorem_4_1`: leader election is eventually solvable in the blackboard model iff some source
  is connected to exactly one party.
* `theorem_4_1_bound`: the explicit bound of Eq. (25), `Pr[S(t)] ≥ 1 - (k-1)/2^t`.
-/

open Finset Filter Topology

namespace Podc.RandomizedSymmetryTopology

/-- Knowledge values in the blackboard model at time `t`. -/
def BBKnow : ℕ → Type
  | 0 => Unit
  | t + 1 => BBKnow t × Bool × Multiset (BBKnow t)

variable {n k : ℕ}

/-- **Eq. (1).** Knowledge of party `i` at time `t` in the blackboard model, for the randomness
configuration `α` and the source stream `ω`. -/
def bbK (α : Fin n → Fin k) (ω : Stream k) : (t : ℕ) → Fin n → BBKnow t
  | 0 => fun _ => ()
  | t + 1 => fun i =>
    ((bbK α ω t i, ω t (α i), (univ.erase i).val.map (bbK α ω t)) : BBKnow t × Bool × _)

theorem bbK_succ (α : Fin n → Fin k) (ω : Stream k) (t : ℕ) (i : Fin n) :
    bbK α ω (t + 1) i =
      ((bbK α ω t i, ω t (α i), (univ.erase i).val.map (bbK α ω t)) :
        BBKnow t × Bool × Multiset (BBKnow t)) := rfl

theorem bbK_isLocal (α : Fin n → Fin k) (ω ω' : Stream k) (t : ℕ)
    (h : ∀ s < t, ω s = ω' s) : bbK α ω t = bbK α ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have ih := ih fun s hs => h s (by omega)
    funext i
    rw [bbK_succ, bbK_succ, ih, h t (by omega)]

theorem bbK_shift (α : Fin n → Fin k) (ω : Stream k) (s u : ℕ) :
    ∃ g : BBKnow (s + u) → BBKnow u, ∀ i, bbK α (shiftStream ω s) u i = g (bbK α ω (s + u) i) := by
  induction u with
  | zero => exact ⟨fun _ => (), fun _ => rfl⟩
  | succ u ih =>
    obtain ⟨g, hg⟩ := ih
    refine ⟨fun x => ((g x.1, x.2.1, x.2.2.map g) : BBKnow u × Bool × Multiset (BBKnow u)),
      fun i => ?_⟩
    show bbK α (shiftStream ω s) (u + 1) i = _
    rw [bbK_succ]
    change _ = ((g (bbK α ω (s + u) i), ω (s + u) (α i),
      ((univ.erase i).val.map (bbK α ω (s + u))).map g) : BBKnow u × Bool × Multiset (BBKnow u))
    rw [Multiset.map_map]
    congr 2
    · exact hg i
    · congr 1; funext l; exact hg l

/-- The blackboard model as a full-information model. -/
def bbModel (α : Fin n → Fin k) : FullInfoModel n k where
  Know := BBKnow
  K := bbK α
  isLocal ω ω' t h := bbK_isLocal α ω ω' t h
  prev t := ⟨fun x => (show BBKnow t × Bool × Multiset (BBKnow t) from x).1, fun _ _ => rfl⟩
  shift ω s u := bbK_shift α ω s u

theorem map_erase_eq_of_eq {β γ : Type*} [DecidableEq β] (f : β → γ) {i j : β} {s : Finset β}
    (hi : i ∈ s) (hj : j ∈ s) (h : f i = f j) :
    (s.erase i).val.map f = (s.erase j).val.map f := by
  have hi' : s.val.map f = f i ::ₘ (s.erase i).val.map f := by
    rw [← Multiset.map_cons, ← Finset.insert_val_of_notMem (Finset.notMem_erase i s),
      Finset.insert_erase hi]
  have hj' : s.val.map f = f j ::ₘ (s.erase j).val.map f := by
    rw [← Multiset.map_cons, ← Finset.insert_val_of_notMem (Finset.notMem_erase j s),
      Finset.insert_erase hj]
  rw [hi', h] at hj'
  exact Multiset.cons_inj_right _ |>.1 hj'

/-- In the blackboard model, two parties have the same knowledge at time `t` iff they received the
same random bits during the first `t` rounds. -/
theorem bbK_eq_iff (α : Fin n → Fin k) (ω : Stream k) (t : ℕ) (i j : Fin n) :
    bbK α ω t i = bbK α ω t j ↔ ∀ s < t, ω s (α i) = ω s (α j) := by
  induction t generalizing i j with
  | zero => exact ⟨fun _ _ h => by omega, fun _ => rfl⟩
  | succ t ih =>
    rw [bbK_succ, bbK_succ]
    constructor
    · intro h
      have h := Prod.mk.inj h
      have h' := Prod.mk.inj h.2
      replace h := And.intro h.1 h'
      intro s hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
      · exact (ih i j).1 h.1 s hs
      · exact h.2.1
    · intro h
      have h1 : bbK α ω t i = bbK α ω t j := (ih i j).2 fun s hs => h s (by omega)
      rw [h1, h t (by omega), map_erase_eq_of_eq _ (mem_univ i) (mem_univ j) h1]

/-! ### Theorem 4.1 -/

theorem load_eq_one_iff (α : Fin n → Fin k) (j : Fin k) :
    load α j = 1 ↔ ∃ i, α i = j ∧ ∀ i', α i' = j → i' = i := by
  unfold load
  rw [card_eq_one]
  constructor
  · rintro ⟨i, hi⟩
    have hmem : i ∈ univ.filter fun i' => α i' = j := by rw [hi]; exact mem_singleton_self i
    refine ⟨i, (mem_filter.1 hmem).2, fun i' hi' => ?_⟩
    have : i' ∈ univ.filter fun i' => α i' = j := mem_filter.2 ⟨mem_univ _, hi'⟩
    rw [hi] at this; exact mem_singleton.1 this
  · rintro ⟨i, hi, hu⟩
    refine ⟨i, ?_⟩
    ext i'
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨hu i', fun h => h ▸ hi⟩

/-- If no source has load `1`, every party shares its source with another party. -/
theorem exists_partner (α : Fin n → Fin k) (h : ∀ j, load α j ≠ 1) (i : Fin n) :
    ∃ i', i' ≠ i ∧ α i' = α i := by
  by_contra hc
  push Not at hc
  exact h (α i) ((load_eq_one_iff α (α i)).2 ⟨i, rfl, fun i' hi' => by_contra fun hne => hc i' hne hi'⟩)

/-- The realization of length `1` in which exactly the source `j` emits `1`. -/
def singleOne (j : Fin k) : Window k 1 := fun _ j' => decide (j' = j)

/-- **Theorem 4.1.** In the blackboard model, with `nⱼ = load α j` parties connected to source `j`,
leader election is eventually solvable iff some source is connected to exactly one party. -/
theorem theorem_4_1 (α : Fin n → Fin k) :
    EventuallySolvable (bbModel α) (leaderElection n) ↔ ∃ j, load α j = 1 := by
  constructor
  · intro hO
    by_contra hc
    push Not at hc
    refine not_eventuallySolvable_of_zero _ (fun t => ?_) hO
    rw [probSolves_eq_zero_iff]
    intro r hr
    obtain ⟨i, hi⟩ := (solves_leaderElection_iff _).1 hr
    obtain ⟨i', hne, hα⟩ := exists_partner α hc i
    exact hi i' hne ((bbK_eq_iff α _ t i' i).2 fun s _ => by rw [hα])
  · rintro ⟨j, hj⟩
    obtain ⟨i, hi, hu⟩ := (load_eq_one_iff α j).1 hj
    apply eventuallySolvable_of_pos (t := 1)
    rw [probSolves_pos_iff]
    refine ⟨singleOne j, (solves_leaderElection_iff _).2 ⟨i, fun i' hne heq => ?_⟩⟩
    have := ((bbK_eq_iff α _ 1 i' i).1 heq) 0 (by omega)
    rw [ext_of_lt _ (by omega)] at this
    simp only [singleOne, hi, decide_true, decide_eq_true_eq] at this
    exact hne (hu i' this)

/-- Half of the bit vectors on `Fin k` agree at two distinct coordinates. -/
theorem card_filter_eq_eq {j j' : Fin k} (h : j' ≠ j) :
    2 * (univ.filter fun f : Fin k → Bool => f j' = f j).card = 2 ^ k := by
  classical
  set F := univ.filter fun f : Fin k → Bool => f j' = f j
  set F' := univ.filter fun f : Fin k → Bool => ¬ f j' = f j
  have hsum : F.card + F'.card = 2 ^ k := by
    rw [card_filter_add_card_filter_not, card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
  have hflip : F.card = F'.card := by
    refine card_bij (fun f _ => Function.update f j' (!f j')) (fun f hf => ?_) (fun f _ g _ hfg => ?_)
      (fun g hg => ⟨Function.update g j' (!g j'), ?_, ?_⟩)
    · simp only [F, F', mem_filter, mem_univ, true_and] at hf ⊢
      rw [Function.update_self, Function.update_of_ne h.symm, hf]; simp
    · funext x
      have hx := congrFun hfg x
      by_cases hxj : x = j'
      · subst hxj; simpa using hx
      · simpa [Function.update_of_ne hxj] using hx
    · simp only [F, F', mem_filter, mem_univ, true_and] at hg ⊢
      rw [Function.update_self, Function.update_of_ne h.symm]
      cases hgj : g j' <;> cases hgj' : g j <;> simp_all
    · simp
  omega

open Classical in
/-- **Eq. (25)** (proof of Theorem 4.1, "if" direction): if some source is connected to exactly one
party, then `Pr[S(t) | α] ≥ 1 - (k - 1)/2^t`. -/
theorem theorem_4_1_bound (α : Fin n → Fin k) {j : Fin k} (hj : load α j = 1) (t : ℕ) :
    1 - ((k : ℝ) - 1) / 2 ^ t ≤ probSolves (bbModel α) (leaderElection n) t := by
  obtain ⟨i, hi, hu⟩ := (load_eq_one_iff α j).1 hj
  set G := univ.filter fun r : Window k t => Solves (leaderElection n) (bbK α (ext r) t)
  set B := univ.filter fun r : Window k t => ¬ Solves (leaderElection n) (bbK α (ext r) t)
  set F := fun j' : Fin k => univ.filter fun f : Fin k → Bool => f j' = f j
  have hsub : B ⊆ (univ.erase j).biUnion fun j' => Fintype.piFinset fun _ : Fin t => F j' := by
    intro r hr
    simp only [B, mem_filter, mem_univ, true_and, solves_leaderElection_iff] at hr
    push Not at hr
    obtain ⟨i', hne, heq⟩ := hr i
    have hbits := (bbK_eq_iff α _ t i' i).1 heq
    have hα : α i' ≠ j := fun h => hne (hu i' h)
    simp only [mem_biUnion, mem_erase, mem_univ, and_true, Fintype.mem_piFinset]
    refine ⟨α i', hα, fun s => ?_⟩
    have := hbits s s.isLt
    rw [ext_of_lt _ s.isLt, hi] at this
    simpa [F] using this
  have hcardB : (B.card : ℝ) ≤ ((k : ℝ) - 1) * ((2 : ℝ) ^ k / 2) ^ t := by
    have h1 := (card_le_card hsub).trans card_biUnion_le
    have h2 : ∀ j' ∈ univ.erase j, ((Fintype.piFinset fun _ : Fin t => F j').card : ℝ) =
        ((2 : ℝ) ^ k / 2) ^ t := by
      intro j' hj'
      rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin]
      have := card_filter_eq_eq (k := k) (ne_of_mem_erase hj')
      push_cast
      congr 1
      have : (2 : ℝ) * (F j').card = 2 ^ k := by exact_mod_cast this
      linarith
    have hk : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun h => (h ▸ j).elim0
    calc (B.card : ℝ) ≤ ∑ j' ∈ univ.erase j, ((Fintype.piFinset fun _ : Fin t => F j').card : ℝ) := by
          exact_mod_cast h1
      _ = ((k : ℝ) - 1) * ((2 : ℝ) ^ k / 2) ^ t := by
          rw [sum_congr rfl h2, sum_const, card_erase_of_mem (mem_univ j), card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hk]
          simp
  have hsplit : G.card + B.card = 2 ^ (k * t) := by
    rw [← card_window]; exact card_filter_add_card_filter_not _
  have hG : (G.card : ℝ) = 2 ^ (k * t) - B.card := by
    have : ((G.card + B.card : ℕ) : ℝ) = ((2 ^ (k * t) : ℕ) : ℝ) := by rw [hsplit]
    push_cast at this; linarith
  show _ ≤ (G.card : ℝ) / 2 ^ (k * t)
  have hpos : (0 : ℝ) < 2 ^ (k * t) := by positivity
  have hpow : ((2 : ℝ) ^ k / 2) ^ t = 2 ^ (k * t) / 2 ^ t := by
    rw [div_pow, ← pow_mul]
  rw [hG, sub_div ((2 : ℝ) ^ (k * t)) _ ((2 : ℝ) ^ (k * t)), div_self hpos.ne']
  rw [hpow] at hcardB
  have : (B.card : ℝ) / 2 ^ (k * t) ≤ ((k : ℝ) - 1) / 2 ^ t := by
    rw [div_le_iff₀ hpos]
    calc (B.card : ℝ) ≤ ((k : ℝ) - 1) * (2 ^ (k * t) / 2 ^ t) := hcardB
      _ = ((k : ℝ) - 1) / 2 ^ t * 2 ^ (k * t) := by ring
  linarith

end Podc.RandomizedSymmetryTopology
