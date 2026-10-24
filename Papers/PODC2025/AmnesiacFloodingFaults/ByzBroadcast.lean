import Papers.PODC2025.AmnesiacFloodingFaults.Faults

/-!
# Theorem 5.8, broadcast part (corrected)

The paper claims that a weak-Byzantine set `J` can force a failure to broadcast iff `J` contains a
cut vertex set. That is false (`theorem_5_8_broadcast_false`): what matters is whether
some honest node is cut off from *all* initiators. We prove the corrected statement: the adversary
can prevent some honest non-initiator from ever receiving the message iff some honest node is not
reachable from any initiator in the graph `G - J` (`honestGraph G J`).

* (⇐) the Byzantine nodes stay silent; flooding then runs on `G - J`, terminates there
  (Theorem 2.1), and the adversary hands control back only afterwards.
* (⇒) honest nodes forward to every honest neighbour that did not just send to them, so the
  informed honest nodes are closed under adjacency in `G - J`.
-/

namespace AmnesiacFloodingFaults

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

variable (G) in
/-- The graph `G - J` on the honest nodes (nodes of `J` become isolated). -/
def honestGraph (J : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∉ J ∧ y ∉ J
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- Some honest non-initiator never receives the message. -/
def ByzFailsBroadcast (I J : Set V) (k : ℕ) (B : ℕ → Config V) : Prop :=
  ∃ x, x ∉ J ∧ x ∉ I ∧ ∀ t, ¬ Active (byzRun G I J k B t) x

lemma mem_byzRun_honest {I J : Set V} {k : ℕ} {B : ℕ → Config V} {t : ℕ} {x y : V}
    (hx : x ∉ J) : (x, y) ∈ byzRun G I J k B t ↔
      (x, y) ∈ (match t with
        | 0 => step G I ∅
        | t + 1 => af G (byzRun G I J k B t)) := by
  have : ∀ t' B' X, (x, y) ∈ byzMix G J k t' B' X ↔ (x, y) ∈ X := by
    intro t' B' X
    unfold byzMix
    split_ifs
    · simp [hx]
    · rfl
  cases t <;> exact this _ _ _

/-- **Theorem 5.8, broadcast part, corrected.** Let the adversary
control `J` until a round `k ≥ k₀` of its choice. It can make some honest non-initiator never
receive the message iff some honest node is not reachable from any initiator in `G - J`. -/
theorem theorem_5_8_broadcast [Fintype V] {I J : Set V} (k₀ : ℕ) :
    (∃ k ≥ k₀, ∃ B, ByzFailsBroadcast (G := G) I J k B) ↔
      ∃ x, x ∉ J ∧ ∀ i ∈ I, ¬ (honestGraph G J).Reachable i x := by
  classical
  set GH := honestGraph G J
  constructor
  · rintro ⟨k, -, B, x, hxJ, hxI, hx⟩
    refine ⟨x, hxJ, fun i hi hreach => ?_⟩
    set Z := byzRun G I J k B
    set Inf : V → Prop := fun y => y ∈ I ∨ ∃ t, Active (Z t) y
    -- an honest sender is informed
    have hhead : ∀ j a b, (a, b) ∈ Z j → a ∉ J → Inf a := by
      intro j a b h ha
      rw [mem_byzRun_honest ha] at h
      cases j with
      | zero => exact Or.inl (by simpa [Active] using h.2.2)
      | succ j => exact Or.inr ⟨j, h.2.2.resolve_left (Set.notMem_empty _)⟩
    have hclosed : ∀ a b, Inf a → GH.Adj a b → Inf b := by
      intro a b ha hab
      obtain ⟨hab', haJ, hbJ⟩ := hab
      rcases ha with haI | ⟨t, ht⟩
      · -- `a` initiates in round 1
        have : (a, b) ∈ Z 0 := by
          rw [mem_byzRun_honest haJ]; exact ⟨hab', by simp, Or.inl haI⟩
        exact Or.inr ⟨0, a, this⟩
      · by_cases hba : (b, a) ∈ Z t
        · exact hhead t b a hba hbJ
        · have : (a, b) ∈ Z (t + 1) := by
            rw [mem_byzRun_honest haJ]; exact ⟨hab', hba, Or.inr ht⟩
          exact Or.inr ⟨t + 1, a, this⟩
    have : Inf x := by
      obtain ⟨p⟩ := hreach
      have : ∀ a b (q : GH.Walk a b), Inf a → Inf b := by
        intro a b q
        induction q with
        | nil => exact id
        | cons h q ih => exact fun ha => ih (hclosed _ _ ha h)
      exact this _ _ p (Or.inl hi)
    rcases this with h | ⟨t, ht⟩
    · exact hxI h
    · exact hx t ht
  · rintro ⟨x, hxJ, hx⟩
    -- flooding on `G - J` from `I`
    set R : ℕ → Config V := fun t => (af GH)^[t] (step GH I ∅)
    obtain ⟨m, hm⟩ := theorem_2_1 (G := GH) (reachable_empty.step I)
    have hRm : ∀ t ≥ m, R t = ∅ := by
      intro t ht
      obtain ⟨r, rfl⟩ : ∃ r, t = m + r := ⟨t - m, by omega⟩
      simp only [R]
      rw [add_comm, Function.iterate_add_apply, hm, iterate_af_empty]
    set k := k₀ + m + 2
    set Z := byzRun G I J k (fun _ => ∅)
    have hZmix : ∀ t, t < k → ∀ e : V × V, e ∈ Z t ↔ e ∈ (match t with
        | 0 => step G I ∅
        | t + 1 => af G (Z t)) ∧ e.1 ∉ J := by
      intro t ht e
      have : ∀ X, e ∈ byzMix G J k t ∅ X ↔ e ∈ X ∧ e.1 ∉ J := by
        intro X
        unfold byzMix
        rw [ite_eq_left ht]
        simp
      cases t <;> exact this _
    -- invariants while the adversary is silent
    have inv : ∀ t, t < k →
        (∀ y, y ∉ J → (Active (Z t) y ↔ Active (R t) y)) ∧
        (∀ a b, a ∉ J → b ∉ J → ((a, b) ∈ Z t ↔ (a, b) ∈ R t)) ∧
        (∀ a b, (a, b) ∈ Z t → a ∉ J ∧ ((t = 0 ∧ a ∈ I) ∨ ∃ t', t = t' + 1 ∧ Active (R t') a)) := by
      intro t
      induction t with
      | zero =>
        intro ht
        have hR0 : R 0 = step GH I ∅ := rfl
        have hc : ∀ a b, a ∉ J → b ∉ J → ((a, b) ∈ Z 0 ↔ (a, b) ∈ R 0) := by
          intro a b ha hb
          rw [hZmix 0 ht, hR0]
          simp [honestGraph, GH, Active, ha, hb]
        refine ⟨fun y hy => ?_, hc, fun a b h => ?_⟩
        · constructor
          · rintro ⟨a, ha⟩
            have := (hZmix 0 ht _).1 ha
            exact ⟨a, (hc a y this.2 hy).1 ha⟩
          · rintro ⟨a, ha⟩
            have haJ : a ∉ J := ha.1.2.1
            exact ⟨a, (hc a y haJ hy).2 ha⟩
        · have := (hZmix 0 ht _).1 h
          exact ⟨this.2, Or.inl ⟨rfl, by simpa [Active] using this.1.2.2⟩⟩
      | succ t ih =>
        intro ht
        obtain ⟨ha, hc, -⟩ := ih (by omega)
        have hR : R (t + 1) = af GH (R t) := by
          simp only [R]; rw [Function.iterate_succ_apply']
        have hc' : ∀ a b, a ∉ J → b ∉ J → ((a, b) ∈ Z (t + 1) ↔ (a, b) ∈ R (t + 1)) := by
          intro a b haJ hbJ
          rw [hZmix (t + 1) ht, hR]
          simp only [mem_step, Set.mem_empty_iff_false, false_or, haJ, not_false_eq_true,
            and_true, hc b a hbJ haJ, ha a haJ]
          simp [GH, honestGraph, haJ, hbJ]
        refine ⟨fun y hy => ?_, hc', fun a b h => ?_⟩
        · constructor
          · rintro ⟨a, h⟩
            have := (hZmix (t + 1) ht _).1 h
            exact ⟨a, (hc' a y this.2 hy).1 h⟩
          · rintro ⟨a, h⟩
            have haJ : a ∉ J := by
              rw [hR] at h; exact h.1.2.1
            exact ⟨a, (hc' a y haJ hy).2 h⟩
        · have := (hZmix (t + 1) ht _).1 h
          refine ⟨this.2, Or.inr ⟨t, rfl, ?_⟩⟩
          exact (ha a this.2).1 (this.1.2.2.resolve_left (Set.notMem_empty _))
    -- the flood dies before the adversary hands back control
    have hZempty : Z (k - 1) = ∅ := by
      ext ⟨a, b⟩
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h
      obtain ⟨-, h2⟩ := (inv (k - 1) (by omega)).2.2 a b h
      rcases h2 with ⟨h0, -⟩ | ⟨t', ht', ⟨w, hw⟩⟩
      · omega
      · rw [hRm t' (by omega)] at hw; exact hw
    have hZafter : ∀ r, Z (k + r) = ∅ := by
      intro r
      show byzRun G I J k (fun _ => ∅) (k + r) = ∅
      rw [byzRun_eventually]
      have h1 : byzRun G I J k (fun _ => ∅) ((k - 1) + 1) = ∅ := by
        simp only [byzRun, byzMix]
        rw [ite_eq_right (by omega)]
        rw [show byzRun G I J k (fun _ => ∅) (k - 1) = ∅ from hZempty]; exact step_empty_empty
      have : byzRun G I J k (fun _ => ∅) k = ∅ := by
        rwa [show k - 1 + 1 = k by omega] at h1
      rw [this, iterate_af_empty]
    -- activity on `G - J` stays in the component of `I`
    have hreachR : ∀ t a b, (a, b) ∈ R t → ∃ i ∈ I, GH.Reachable i b := by
      intro t
      induction t with
      | zero =>
        rintro a b ⟨hab, -, ha⟩
        exact ⟨a, by simpa [Active] using ha, hab.reachable⟩
      | succ t ih =>
        intro a b h
        simp only [R] at h
        rw [Function.iterate_succ_apply'] at h
        obtain ⟨c, hc⟩ := h.2.2.resolve_left (Set.notMem_empty _)
        obtain ⟨i, hi, hreach⟩ := ih c a hc
        exact ⟨i, hi, hreach.trans h.1.reachable⟩
    refine ⟨k, by omega, fun _ => ∅, x, hxJ, fun hxI => hx x hxI (Reachable.refl _), fun t ht => ?_⟩
    rcases Nat.lt_or_ge t k with htk | htk
    · obtain ⟨b, hb⟩ := ((inv t htk).1 x hxJ).1 ht
      obtain ⟨i, hi, hreach⟩ := hreachR t b x hb
      exact hx i hi hreach
    · obtain ⟨r, rfl⟩ : ∃ r, t = k + r := ⟨t - k, by omega⟩
      obtain ⟨b, hb⟩ := ht
      rw [show byzRun G I J k (fun _ => ∅) (k + r) = ∅ from hZafter r] at hb
      exact hb

end AmnesiacFloodingFaults
