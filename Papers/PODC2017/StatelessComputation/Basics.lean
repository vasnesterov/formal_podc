import Papers.PODC2017.StatelessComputation.Model
import Cslib.Foundations.Combinatorics.Digraph.Walk

/-!
# Propositions 2.1 and 2.2: round complexity vs. radius and vs. the number of labelings

Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017, Section 2.3
(synchronous executions).

* Proposition 2.2: `R_n ≤ |Σ|^{|E|}` — if (some function of) the synchronous labeling sequence
  converges, it has converged after `|Σ|^{|E|}` steps (`out_const_of_converges`,
  `syncRun_const_of_converges`).
* Proposition 2.1: if a protocol computes a non-constant function and all outputs are correct
  from round `R` on (from every initial labeling), then some node reaches every node within `R`
  hops, i.e. the radius is at most `R` (`exists_center`).
-/

namespace StatelessComputation

variable {V : Type*} [Fintype V] [DecidableEq V] {L X Y : Type*} {G : Digraph V}

namespace Protocol

variable (P : Protocol G L X Y) (x : V → X)

omit [Fintype V] [DecidableEq V] in
lemma syncRun_add (ℓ0 : Labeling G L) (a b : ℕ) :
    P.syncRun x ℓ0 (a + b) = P.syncRun x (P.syncRun x ℓ0 a) b := by
  simp only [syncRun]; rw [add_comm, Function.iterate_add_apply]

omit [Fintype V] [DecidableEq V] in
/-- Once the synchronous sequence repeats (`ℓᵃ = ℓᵃ⁺ᵖ`), it is periodic from `a` on. -/
lemma syncRun_periodic (ℓ0 : Labeling G L) {a p : ℕ} (h : P.syncRun x ℓ0 (a + p) =
    P.syncRun x ℓ0 a) (t m : ℕ) (ht : a ≤ t) : P.syncRun x ℓ0 (t + m * p) = P.syncRun x ℓ0 t := by
  induction m with
  | zero => simp
  | succ m ih =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    have e1 : a + d + (m + 1) * p = (a + p) + (d + m * p) := by ring
    rw [e1, syncRun_add, h, ← syncRun_add, show a + (d + m * p) = a + d + m * p by ring, ih]

/-- The synchronous labeling sequence repeats within the first `|Σ|^{|E|}` steps. -/
lemma exists_repeat [DecidableRel G.Adj] [Fintype L] (ℓ0 : Labeling G L) :
    ∃ a p, 0 < p ∧ a + p ≤ Fintype.card L ^ Fintype.card (Arc G) ∧
      P.syncRun x ℓ0 (a + p) = P.syncRun x ℓ0 a := by
  have hc : Fintype.card (Labeling G L) < Fintype.card (Fin (Fintype.card L ^
      Fintype.card (Arc G) + 1)) := by
    simp [Labeling]
  obtain ⟨i, j, hij, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin _ => P.syncRun x ℓ0 i) hc
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with h | h
  · refine ⟨i, j - i, by omega, by omega, ?_⟩
    rw [show (i : ℕ) + (j - i) = j by omega]; exact he.symm
  · refine ⟨j, i - j, by omega, by omega, ?_⟩
    rw [show (j : ℕ) + (i - j) = i by omega]; exact he

/-- **Proposition 2.2** (general form). If `g (ℓᵗ)` is eventually constant along the
synchronous sequence, it is constant from time `|Σ|^{|E|} - 1` on. -/
theorem const_of_converges [DecidableRel G.Adj] [Fintype L] {β : Type*}
    (g : Labeling G L → β) (ℓ0 : Labeling G L) (c : β) (T : ℕ)
    (hT : ∀ t, T ≤ t → g (P.syncRun x ℓ0 t) = c) :
    ∀ t, Fintype.card L ^ Fintype.card (Arc G) ≤ t + 1 → g (P.syncRun x ℓ0 t) = c := by
  obtain ⟨a, p, hp, hap, hrep⟩ := P.exists_repeat x ℓ0
  intro t ht
  rw [← P.syncRun_periodic x ℓ0 hrep t T (by omega)]
  exact hT _ (by nlinarith)

/-- **Proposition 2.2** for outputs: `R_n ≤ |Σ|^{|E|}`. If node `i`'s output converges to `c`,
then its output at every time `t ≥ |Σ|^{|E|}` (computed from `ℓ^{t-1}`) is `c`. -/
theorem out_const_of_converges [DecidableRel G.Adj] [Fintype L] (ℓ0 : Labeling G L) (i : V)
    (c : Y) (T : ℕ) (hT : ∀ t, T ≤ t → P.out x (P.syncRun x ℓ0 t) i = c) :
    ∀ t, Fintype.card L ^ Fintype.card (Arc G) ≤ t + 1 → P.out x (P.syncRun x ℓ0 t) i = c :=
  P.const_of_converges x (fun ℓ => P.out x ℓ i) ℓ0 c T hT

/-- **Proposition 2.2** for labels: a converging synchronous labeling sequence has converged
by time `|Σ|^{|E|} - 1`. -/
theorem syncRun_const_of_converges [DecidableRel G.Adj] [Fintype L] (ℓ0 : Labeling G L)
    (ℓs : Labeling G L) (T : ℕ) (hT : ∀ t, T ≤ t → P.syncRun x ℓ0 t = ℓs) :
    ∀ t, Fintype.card L ^ Fintype.card (Arc G) ≤ t + 1 → P.syncRun x ℓ0 t = ℓs :=
  P.const_of_converges x id ℓ0 ℓs T hT

end Protocol

/-! ### Proposition 2.1 -/

/-- Walks: `WalkLen G k j v` iff there is a directed walk of length exactly `k` from `j` to `v`
(`Relation.RelatesInSteps` of the arcs). -/
abbrev WalkLen (G : Digraph V) (k : ℕ) (j v : V) : Prop := Relation.RelatesInSteps G.Adj j v k

/-- `near G j t`: the nodes at distance `< t` from `j`. -/
def near (G : Digraph V) (j : V) : ℕ → Set V
  | 0 => ∅
  | t + 1 => {v | v = j ∨ ∃ u ∈ near G j t, G.Adj u v}

omit [Fintype V] [DecidableEq V] in
lemma mem_near_iff (j v : V) (t : ℕ) : v ∈ near G j (t + 1) ↔ ∃ k ≤ t, WalkLen G k j v := by
  induction t generalizing v with
  | zero =>
    simp only [near, Set.mem_ofPred_eq, Set.mem_empty_iff_false, false_and, exists_false,
      or_false]
    constructor
    · rintro rfl; exact ⟨0, le_rfl, .refl _⟩
    · rintro ⟨k, hk, hw⟩
      obtain rfl : k = 0 := by omega
      exact hw.zero.symm
  | succ t ih =>
    change v = j ∨ (∃ u ∈ near G j (t + 1), G.Adj u v) ↔ _
    constructor
    · rintro (rfl | ⟨u, hu, hadj⟩)
      · exact ⟨0, by omega, .refl _⟩
      · obtain ⟨k, hk, hw⟩ := (ih u).1 hu
        exact ⟨k + 1, by omega, .tail _ _ _ _ hw hadj⟩
    · rintro ⟨k, hk, hw⟩
      cases hw with
      | refl => exact Or.inl rfl
      | tail _ _ _ hw hadj => exact Or.inr ⟨_, (ih _).2 ⟨_, by omega, hw⟩, hadj⟩

omit [Fintype V] [DecidableEq V] in
lemma mem_near_succ_of_adj {j u v : V} {t : ℕ} (hu : u ∈ near G j t) (h : G.Adj u v) :
    v ∈ near G j (t + 1) := Or.inr ⟨u, hu, h⟩

omit [Fintype V] [DecidableEq V] in
lemma self_mem_near_succ (j : V) (t : ℕ) : j ∈ near G j (t + 1) := Or.inl rfl

omit [Fintype V] [DecidableEq V] in
/-- Locality: if the inputs differ only at `j`, labels on arcs whose tail is at distance `≥ t`
from `j` agree at time `t`. -/
lemma syncRun_local (P : Protocol G L X Y) {x x' : V → X} {j : V}
    (hx : ∀ v, v ≠ j → x v = x' v) (ℓ0 : Labeling G L) (t : ℕ) (e : Arc G)
    (he : e.1.1 ∉ near G j t) : P.syncRun x ℓ0 t e = P.syncRun x' ℓ0 t e := by
  induction t generalizing e with
  | zero => rfl
  | succ t ih =>
    rw [Protocol.syncRun_succ, Protocol.syncRun_succ]
    simp only [Protocol.syncStep]
    have hj : e.1.1 ≠ j := fun h => he (by rw [h]; exact self_mem_near_succ (G := G) j t)
    have hin : inLab (P.syncRun x ℓ0 t) e.1.1 = inLab (P.syncRun x' ℓ0 t) e.1.1 := by
      funext w
      exact ih _ fun hw => he (mem_near_succ_of_adj hw w.2)
    rw [hin, hx _ hj]

omit [Fintype V] [DecidableEq V] in
lemma out_local (P : Protocol G L X Y) {x x' : V → X} {j : V}
    (hx : ∀ v, v ≠ j → x v = x' v) (ℓ0 : Labeling G L) (t : ℕ) (v : V)
    (hv : v ∉ near G j (t + 1)) :
    P.out x (P.syncRun x ℓ0 t) v = P.out x' (P.syncRun x' ℓ0 t) v := by
  simp only [Protocol.out]
  have hj : v ≠ j := fun h => hv (by rw [h]; exact self_mem_near_succ (G := G) j t)
  have hin : inLab (P.syncRun x ℓ0 t) v = inLab (P.syncRun x' ℓ0 t) v := by
    funext w
    exact syncRun_local P hx ℓ0 t _ fun hw => hv (mem_near_succ_of_adj hw w.2)
  rw [hin, hx _ hj]

/-- A non-constant function changes its value under some single-coordinate change. -/
lemma exists_sensitive {f : (V → X) → Y} (hf : ∃ x x', f x ≠ f x') :
    ∃ x j a, f x ≠ f (Function.update x j a) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, hxy⟩ := hf
  let h : Finset V → V → X := fun S v => if v ∈ S then y v else x v
  have key : ∀ S, f (h S) = f x := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [h]
    | insert j S hj ih =>
      have : h (insert j S) = Function.update (h S) j (y j) := by
        funext v
        by_cases hv : v = j
        · subst hv; simp [h]
        · simp [h, hv]
      rw [this, ← hcon, ih]
  apply hxy
  rw [← key Finset.univ]
  congr 1
  funext v; simp [h]

/-- **Proposition 2.1** of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17]. Let `P` be a protocol
(synchronous) computing a non-constant `f`, such that from every initial labeling all outputs
computed from round `R` on (i.e. from the labelings `ℓᵗ`, `t ≥ R`) are correct. Then some node
`j` reaches every node by a walk of length `≤ R`; i.e. the (out-)radius of `G` is at most `R`. -/
theorem exists_center [Nonempty L] (P : Protocol G L X Y) (f : (V → X) → Y)
    (hf : ∃ x x', f x ≠ f x') (R : ℕ)
    (hR : ∀ x ℓ0 t, R ≤ t → ∀ i, P.out x (P.syncRun x ℓ0 t) i = f x) :
    ∃ j, ∀ v, ∃ k ≤ R, WalkLen G k j v := by
  obtain ⟨x, j, a, hfx⟩ := exists_sensitive hf
  refine ⟨j, fun v => (mem_near_iff j v R).1 ?_⟩
  by_contra hv
  set x' := Function.update x j a
  have hx : ∀ u, u ≠ j → x u = x' u := fun u hu => (Function.update_of_ne hu a x).symm
  let ℓ0 : Labeling G L := fun _ => Classical.arbitrary L
  let m := P.syncRun x ℓ0 R
  have h1 : P.out x (P.syncRun x m R) v = f x := by
    rw [← Protocol.syncRun_add]; exact hR x ℓ0 _ (by omega) v
  have h2 : P.out x' (P.syncRun x' m R) v = f x' := hR x' m R le_rfl v
  rw [out_local P hx m R v hv, h2] at h1
  exact hfx h1.symm

end StatelessComputation
