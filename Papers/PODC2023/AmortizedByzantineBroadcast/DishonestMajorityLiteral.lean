import Papers.PODC2023.AmortizedByzantineBroadcast.DishonestMajorityConsistency

/-!
# Section 5 of [WXMRS23]: Algorithm 5.2 read literally violates validity (and consistency)

Algorithm 5.2 invokes `TrustCast(G_u, n, k)`, whose rules (Algorithm 5.1) run in rounds `1..n` of
the slot, and whose equivocation rule only concerns proposals of the current slot `k`. With the trust
graph shared across slots this is not enough: equivocation evidence that one honest node `x`
receives in the last maintained round of a slot reaches the other honest node `u` only when the
evidence is no longer processed, so `x` and `u` keep *different* trust graphs forever
(transferability fails), and in the next slot with a silent Byzantine sender `u` accuses `x`
(integrity fails), later isolating itself; when `x` is the sender, `u` commits `⊥`.

Execution (`N = Fin 3`, `x = 0`, `u = 1` honest, `a = 2` Byzantine, `f = 1`, `n = 3`, `T = 7`;
slots `0, 1` have sender `a`, slot `2` has sender `x`):
* round 0: `a` sends `⟨prop, true, 0⟩_a` to everybody (delivered in round 1);
* round `δ - 1`: `a` sends `⟨prop, false, 0⟩_a` to `x` only (delivered in round `δ`), where
  `δ = n = 3` is the last TrustCast round (literal reading); `x` removes `a`, forwards both
  proposals, but `u` receives them in round `4`, outside TrustCast, and never removes `a`;
* slot 1 (`a` silent): in round 1 of the slot `u` accuses `a`; in round 2 the edge `x – a` is still
  in `G_u` (but not in `G_x`), so `dist_{G_u}(x, a) = 1 < 2` and `u` accuses the honest `x`;
  in round 3 `u` removes the edge `u – x` and is isolated;
* slot 2 (sender `x` honest): `x ∉ G_u`, so `u` votes `⟨corrupt, x⟩_u` and commits `⊥`.

In slot 0 already `x` votes `⟨corrupt, a⟩_x` (as `a ∉ G_x`) and commits `⊥`, while `u` never removes
`a` and commits `true`: consistency (Lemma 5) fails as well.

The same execution with `δ = T - 1 = 6` breaks validity for the reading "graph maintenance in every
round, but equivocation evidence only of the current slot" (`Reading.slotLocal`), so the charitable
reading under which Lemmas 4 and 5 are proved (`Reading.charitable`) must also keep equivocation
evidence across slots.
-/

namespace Podc.AmortizedByzantineBroadcast.DishonestMajority

open SimpleGraph

/-- Graph maintenance in every round, but only equivocation evidence of the current slot. -/
def Reading.slotLocal : Reading := ⟨fun _ => True, fun j k => j = k⟩

namespace Counterexample

/-- The setup: `f = 1`; slots `0, 1` have the Byzantine sender `2`, later slots the honest `0`. -/
def setup (R : Reading) : Setup (Fin 3) Bool :=
  ⟨1, fun k => if k ≤ 1 then 2 else 0, fun _ => true, R⟩

/-- Honest nodes. -/
def H : Set (Fin 3) := {0, 1}

/-- The adversary: `⟨prop, true, 0⟩_2` to everybody in round 1, `⟨prop, false, 0⟩_2` to `0` in
round `δ`. -/
def adv (δ : ℕ) : ℕ → Fin 3 → Set (Msg (Fin 3) Bool) := fun r w =>
  (if r = 1 then {Msg.prop true 0} else ∅) ∪ (if r = δ ∧ w = 0 then {Msg.prop false 0} else ∅)

section
variable (R : Reading) (δ : ℕ)

lemma T_eq : (setup R).T = 7 := by simp [Setup.T, setup]

lemma n_eq : (setup R).n = 3 := by simp

lemma advValid : (setup R).AdvValid H (adv δ) := by
  intro r u a hu ha hs
  exfalso
  simp only [adv, Set.mem_union] at ha
  rcases ha with ha | ha <;> split_ifs at ha <;> simp_all [Msg.signer, setup, H]

/-- Which atoms an honest node `w` can know at state `r` of the execution. -/
def Allowed (r : ℕ) (w : Fin 3) : Msg (Fin 3) Bool → Prop
  | .prop m j => (j = 0 ∧ (m = true ∨ (w = 0 ∧ δ + 1 ≤ r) ∨ δ + 2 ≤ r)) ∨ (2 ≤ j ∧ m = true)
  | .accuse _ _ => 10 ≤ r
  | .corrupt _ _ => True

lemma allowed_mono {r r' : ℕ} (h : r ≤ r') {w : Fin 3} {a : Msg (Fin 3) Bool}
    (ha : Allowed δ r w a) : Allowed δ r' w a := by
  cases a with
  | prop m j =>
    simp only [Allowed] at ha ⊢
    rcases ha with ⟨h1, h2 | ⟨h3, h4⟩ | h5⟩ | h6
    · exact Or.inl ⟨h1, Or.inl h2⟩
    · exact Or.inl ⟨h1, Or.inr (Or.inl ⟨h3, by omega⟩)⟩
    · exact Or.inl ⟨h1, Or.inr (Or.inr (by omega))⟩
    · exact Or.inr h6
  | accuse => simp only [Allowed] at ha ⊢; omega
  | corrupt => trivial

lemma allowed_forward {r : ℕ} {w w' : Fin 3} {a : Msg (Fin 3) Bool}
    (ha : Allowed δ (r + 1) w' a) : Allowed δ (r + 2) w a := by
  cases a with
  | prop m j =>
    simp only [Allowed] at ha ⊢
    rcases ha with ⟨h1, h2 | ⟨h3, h4⟩ | h5⟩ | h6
    · exact Or.inl ⟨h1, Or.inl h2⟩
    · exact Or.inl ⟨h1, Or.inr (Or.inr (by omega))⟩
    · exact Or.inl ⟨h1, Or.inr (Or.inr (by omega))⟩
    · exact Or.inr h6
  | accuse => simp only [Allowed] at ha ⊢; omega
  | corrupt => trivial

lemma prop_true_known {w : Fin 3} {r : ℕ} (hr : 2 ≤ r) :
    Msg.prop true 0 ∈ ((setup R).cfg H (adv δ) r w).know :=
  (setup R).know_mono w hr (Or.inr (Or.inl (Or.inl (by simp))))

lemma allowed_know : ∀ r, ∀ w ∈ H, ∀ a ∈ ((setup R).cfg H (adv δ) r w).know, Allowed δ r w a := by
  intro r
  induction r with
  | zero => intro w _ a ha; simp [Setup.cfg_zero, State.init] at ha
  | succ r ih =>
    intro w hw a ha
    rcases ha with ha | ha | ⟨w', hw', ha⟩
    · exact allowed_mono δ (by omega) (ih w hw a ha)
    · simp only [adv, Set.mem_union] at ha
      rcases ha with ha | ha <;> split_ifs at ha with h1
      · simp only [Set.mem_singleton_iff] at ha; subst ha; simp [Allowed]
      · simp at ha
      · simp only [Set.mem_singleton_iff] at ha; subst ha
        exact Or.inl ⟨rfl, Or.inr (Or.inl ⟨h1.2, by omega⟩)⟩
      · simp at ha
    · cases r with
      | zero => simp [Setup.cfg_zero, State.init] at ha
      | succ s =>
        rw [Setup.out_succ] at ha
        rcases (setup R).out_cases ha with hk | ⟨rfl, -, hS⟩ | ⟨y, rfl, ht1, htn, hnp, -, -⟩ | ⟨rfl, -⟩
        · exact allowed_forward δ (ih w' hw' a hk)
        · have hS' : w' = (if (setup R).slot s ≤ 1 then 2 else 0) := hS
          have : ¬ (setup R).slot s ≤ 1 := by
            intro h
            simp only [h, ↓reduceIte] at hS'
            subst hS'
            simp [H] at hw'
          exact Or.inr ⟨by omega, rfl⟩
        · simp only [Allowed]
          by_contra hlt
          apply hnp
          refine ⟨true, ?_⟩
          have hT := T_eq R
          simp only [Setup.loc, Setup.slot, hT, n_eq] at ht1 htn ⊢
          have hs : s / 7 = 0 := by omega
          rw [hs]
          exact prop_true_known R δ (by omega)
        · trivial

end

/-- What the counterexample needs from the reading `R` and the delivery round `δ` of the second
proposal: `x` processes the equivocation in round `δ` of slot `0`, `u` never processes slot-`0`
equivocation evidence afterwards (up to the end of slot `1`), and graph maintenance runs in rounds
`2, 3` of slot `1`. -/
structure Hyp (R : Reading) (δ : ℕ) : Prop where
  two_le : 2 ≤ δ
  le_six : δ ≤ 6
  maint_δ : R.maint δ
  eq00 : R.eqSlot 0 0
  no_late : ∀ r, δ + 1 ≤ r → r ≤ 13 → ¬ (R.maint (r % 7) ∧ R.eqSlot 0 (r / 7))
  maint2 : R.maint 2
  maint3 : R.maint 3

lemma hyp_literal : Hyp (Reading.literal 3) 3 where
  two_le := by omega
  le_six := by omega
  maint_δ := by simp [Reading.literal]
  eq00 := rfl
  no_late r h1 h2 := by
    simp only [Reading.literal, not_and]
    intro h3 h4
    omega
  maint2 := by simp [Reading.literal]
  maint3 := by simp [Reading.literal]

lemma hyp_slotLocal : Hyp Reading.slotLocal 6 where
  two_le := by omega
  le_six := by omega
  maint_δ := trivial
  eq00 := rfl
  no_late r h1 h2 := by
    simp only [Reading.slotLocal, true_and]
    omega
  maint2 := trivial
  maint3 := trivial

section
variable {R : Reading} {δ : ℕ} (hy : Hyp R δ)
include hy

omit hy in
lemma loc_eq (r : ℕ) : (setup R).loc r = r % 7 := by simp [Setup.loc, T_eq]

omit hy in
lemma slot_eq (r : ℕ) : (setup R).slot r = r / 7 := by simp [Setup.slot, T_eq]

omit hy in
/-- A processed equivocation removes all edges at the equivocator (any reading). -/
lemma not_adj_of_equivocated {u : Fin 3} {r j : ℕ}
    (hj : (setup R).equivocated r ((setup R).cfg H (adv δ) (r + 1) u).know j) {a b : Fin 3}
    (hab : (setup R).S j = a ∨ (setup R).S j = b) : ¬ ((setup R).cfg H (adv δ) (r + 1) u).G.Adj a b := by
  rw [Setup.G_succ]
  unfold Setup.G2
  rw [deleteEdges_adj]
  rintro ⟨-, h⟩
  refine h ⟨j, hj, ?_⟩
  rcases hab with h | h <;> simp [h]

/-- `x = 0` removes all edges at `a = 2` in round `δ`. -/
lemma x_isolates_a {r : ℕ} (hr : δ + 1 ≤ r) (y : Fin 3) : ¬ ((setup R).cfg H (adv δ) r 0).G.Adj 2 y := by
  intro h
  have hj : (setup R).equivocated δ ((setup R).cfg H (adv δ) (δ + 1) 0).know 0 := by
    refine ⟨by rw [loc_eq, Nat.mod_eq_of_lt (by have := hy.le_six; omega)]; exact hy.maint_δ,
      by rw [slot_eq, Nat.div_eq_of_lt (by have := hy.le_six; omega)]; exact hy.eq00,
      true, false, by decide, prop_true_known R δ (by have := hy.two_le; omega), ?_⟩
    exact Or.inr (Or.inl (Or.inr (by simp)))
  exact not_adj_of_equivocated hj (Or.inl rfl) ((setup R).G_anti 0 hr h)

/-- `u = 1` never processes an equivocation up to the end of slot `1`. -/
lemma u_no_equiv {r : ℕ} (hr : r ≤ 13) (j : ℕ) :
    ¬ (setup R).equivocated r ((setup R).cfg H (adv δ) (r + 1) 1).know j := by
  rintro ⟨hm, he, m, m', hne, h1, h2⟩
  have a1 := allowed_know R δ (r + 1) 1 (by simp [H]) _ h1
  have a2 := allowed_know R δ (r + 1) 1 (by simp [H]) _ h2
  simp only [Allowed] at a1 a2
  have hlate : δ + 2 ≤ r + 1 := by
    rcases a1 with ⟨hj, hm1 | ⟨h0, -⟩ | hl⟩ | ⟨hj, hm1⟩ <;>
    rcases a2 with ⟨hj', hm2 | ⟨h0', -⟩ | hl'⟩ | ⟨hj', hm2⟩ <;>
    first | omega | (exact absurd (hm1.trans hm2.symm) hne)
  rcases a1 with ⟨hj, -⟩ | ⟨hj, hm1⟩
  · subst hj
    rw [loc_eq, slot_eq] at *
    exact hy.no_late r (by omega) hr ⟨hm, he⟩
  · rcases a2 with ⟨hj', -⟩ | ⟨-, hm2⟩
    · omega
    · exact hne (hm1.trans hm2.symm)

/-- `u`'s trust graph is complete up to the end of round `8`. -/
lemma u_top : ∀ r ≤ 9, ((setup R).cfg H (adv δ) r 1).G = ⊤ := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
    intro hr
    rw [Setup.G_succ, ih (by omega)]
    unfold Setup.G2 Setup.G1
    ext a b
    simp only [deleteEdges_adj, top_adj]
    constructor
    · exact fun h => h.1.1
    · intro hab
      refine ⟨⟨hab, ?_⟩, ?_⟩
      · rintro ⟨p, q, ⟨-, hk, -, -⟩, -⟩
        have := allowed_know R δ (r + 1) 1 (by simp [H]) _ hk
        simp only [Allowed] at this
        omega
      · rintro ⟨j, hj, -⟩
        exact u_no_equiv hy (by omega) j hj

omit hy in
lemma no_prop_one {r : ℕ} {w : Fin 3} (hw : w ∈ H) :
    ¬ Setup.HasProp ((setup R).cfg H (adv δ) r w).know 1 := by
  rintro ⟨m, hm⟩
  have := allowed_know R δ r w hw _ hm
  simp only [Allowed] at this
  omega

omit hy in
lemma no_accuse_early {r : ℕ} (hr : r ≤ 9) {w : Fin 3} (hw : w ∈ H) {p q : Fin 3} :
    Msg.accuse p q ∉ ((setup R).cfg H (adv δ) r w).know := by
  intro hk
  have := allowed_know R δ r w hw _ hk
  simp only [Allowed] at this
  omega

/-- In round `8` (round 1 of slot 1) the only accusation multicast by an honest node is
`⟨accuse, a⟩_u`. -/
lemma round8_accuse {w p q : Fin 3} (hw : w ∈ H)
    (h : Msg.accuse p q ∈ ((setup R).cfg H (adv δ) 9 w).out) : p = 2 ∧ q = 1 := by
  rw [Setup.out_succ] at h
  rcases (setup R).out_cases h with hk | ⟨h1, -⟩ | ⟨y, h1, ht1, htn, hnp, hre, hd⟩ | ⟨h1, -⟩
  · exact absurd hk (no_accuse_early (by omega) hw)
  · simp at h1
  · injection h1 with h2 h3
    subst h2 h3
    have hl : (setup R).loc 8 = 1 := by rw [loc_eq]
    have hs : (setup R).slot 8 = 1 := by rw [slot_eq]
    rw [hl, hs] at hd
    have hS : (setup R).S 1 = 2 := rfl
    rw [hS] at hd
    have hy2 : p = 2 := by
      have : ((setup R).Gacc H (adv δ) q 8).edist p 2 = 0 :=
        Order.lt_one_iff.mp (by exact_mod_cast hd)
      exact edist_eq_zero_iff.mp this
    subst hy2
    refine ⟨rfl, ?_⟩
    have hw' : q = 0 ∨ q = 1 := by simpa [H] using hw
    rcases hw' with rfl | rfl
    · exfalso
      have hre' := hre.mono (((setup R).Gacc_le 0 8).trans ((setup R).G_anti 0 (r := δ + 1) (r' := 8) (by
        have := hy.le_six; omega)))
      exact Setup.not_reachable_of_isolated (v := 0) (c := 2) (by decide)
        (fun a ha => x_isolates_a hy (r := δ + 1) le_rfl a ha.symm) hre'
    · rfl
  · simp at h1

/-- `u` accuses `a` in round `8`. -/
lemma u_accuses_a : Msg.accuse 2 1 ∈ ((setup R).cfg H (adv δ) 9 1).out := by
  rw [Setup.out_succ]
  have hl : (setup R).loc 8 = 1 := by rw [loc_eq]
  have hs : (setup R).slot 8 = 1 := by rw [slot_eq]
  have hadj : ((setup R).Gacc H (adv δ) 1 8).Adj 1 2 := by
    unfold Setup.Gacc Setup.G1
    rw [deleteEdges_adj, u_top hy 8 (by omega)]
    refine ⟨by simp, ?_⟩
    rintro ⟨p, q, ⟨-, hk, -, -⟩, -⟩
    exact no_accuse_early (by omega) (by simp [H]) hk
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨2, rfl, by rw [hl], by rw [hl]; simp, ?_,
    hadj.reachable, ?_⟩))))
  · rw [hs]; exact no_prop_one (w := 1) (by simp [H])
  · rw [hs, hl]
    show ((setup R).Gacc H (adv δ) 1 8).edist 2 2 < _
    simp

/-- The accusations known to `u` after round `9` (before slot-1 round 2 processing). -/
lemma know10_accuse {p q : Fin 3} (hk : Msg.accuse p q ∈ ((setup R).cfg H (adv δ) 10 1).know) :
    p = 2 ∧ q = 1 := by
  rcases hk with hk | hk | ⟨w, hw, hk⟩
  · exact absurd hk (no_accuse_early (r := 9) (by omega) (by simp [H]))
  · simp only [adv, Set.mem_union] at hk
    have := hy.le_six
    rcases hk with hk | hk <;> split_ifs at hk with h1 <;> simp_all
  · exact round8_accuse hy hw hk

/-- After processing the accusations of round `9`, `u` still has the edges `u – x` and `x – a`, but
not `u – a`. -/
lemma gacc9 : ((setup R).Gacc H (adv δ) 1 9).Adj 1 0 ∧ ((setup R).Gacc H (adv δ) 1 9).Adj 0 2 ∧
    ¬ ((setup R).Gacc H (adv δ) 1 9).Adj 2 1 := by
  have htop := u_top hy 9 le_rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold Setup.Gacc Setup.G1
    rw [deleteEdges_adj, htop]
    refine ⟨by simp, ?_⟩
    rintro ⟨p, q, ⟨-, hk, -, -⟩, he⟩
    obtain ⟨rfl, rfl⟩ := know10_accuse hy hk
    simp at he
  · unfold Setup.Gacc Setup.G1
    rw [deleteEdges_adj, htop]
    refine ⟨by simp, ?_⟩
    rintro ⟨p, q, ⟨-, hk, -, -⟩, he⟩
    obtain ⟨rfl, rfl⟩ := know10_accuse hy hk
    simp at he
  · unfold Setup.Gacc Setup.G1
    rw [deleteEdges_adj, htop]
    rintro ⟨-, h⟩
    refine h ⟨2, 1, ⟨?_, (setup R).deliver (by simp [H]) 1 (u_accuses_a hy), by simp, by simp⟩, rfl⟩
    rw [loc_eq]; exact hy.maint2

/-- `u` accuses the honest `x` in round `9` (round 2 of slot 1): integrity fails. -/
theorem u_accuses_x : Msg.accuse 0 1 ∈ ((setup R).cfg H (adv δ) 10 1).out := by
  obtain ⟨h10, h02, -⟩ := gacc9 hy
  rw [Setup.out_succ]
  have hl : (setup R).loc 9 = 2 := by rw [loc_eq]
  have hs : (setup R).slot 9 = 1 := by rw [slot_eq]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨0, rfl, by rw [hl]; omega, by rw [hl]; simp, ?_,
    h10.reachable, ?_⟩))))
  · rw [hs]; exact no_prop_one (w := 1) (by simp [H])
  · rw [hs, hl]
    show ((setup R).Gacc H (adv δ) 1 9).edist 0 2 < _
    have h1 : ((setup R).Gacc H (adv δ) 1 9).edist 0 2 = 1 := edist_eq_one_iff_adj.mpr h02
    rw [h1]
    norm_num

/-- From round `10` on, `u` has no edges at all. -/
lemma u_isolated {r : ℕ} (hr : 11 ≤ r) (y : Fin 3) : ¬ ((setup R).cfg H (adv δ) r 1).G.Adj 1 y := by
  obtain ⟨h10, -, h21⟩ := gacc9 hy
  have hle : ((setup R).cfg H (adv δ) r 1).G ≤ (setup R).Gacc H (adv δ) 1 10 :=
    ((setup R).G_anti 1 hr).trans ((setup R).G_succ_le_Gacc 1 10)
  have hle' : (setup R).Gacc H (adv δ) 1 10 ≤ (setup R).Gacc H (adv δ) 1 9 :=
    ((setup R).Gacc_le 1 10).trans ((setup R).G_succ_le_Gacc 1 9)
  have h10' : ((setup R).cfg H (adv δ) 10 1).G.Adj 1 0 := by
    rw [Setup.G_succ]
    unfold Setup.G2
    rw [deleteEdges_adj]
    refine ⟨h10, ?_⟩
    rintro ⟨j, hj, -⟩
    exact u_no_equiv hy (by omega) j hj
  have hx : ¬ ((setup R).Gacc H (adv δ) 1 10).Adj 0 1 := by
    unfold Setup.Gacc Setup.G1
    rw [deleteEdges_adj]
    rintro ⟨-, h⟩
    refine h ⟨0, 1, ⟨?_, (setup R).deliver (by simp [H]) 1 (u_accuses_x hy), h10'.reachable,
      Reachable.refl 1⟩, rfl⟩
    rw [loc_eq]; exact hy.maint3
  intro h
  have h' := hle h
  fin_cases y
  · exact hx h'.symm
  · exact h'.ne rfl
  · exact h21 (hle' h').symm

/-- `u` commits `⊥` in slot `2`, whose sender `x` is honest: validity fails. -/
theorem u_commits_bot : (setup R).commit H (adv δ) 1 2 = none := by
  have hv : (setup R).Voted H (adv δ) 1 ((setup R).S 2) (2 * (setup R).T +
      ((setup R).n + (setup R).f + 2)) := by
    refine ⟨18, by rw [T_eq, n_eq]; simp [setup], ?_⟩
    rw [Setup.out_succ]
    have hl : (setup R).loc 18 = 4 := by rw [loc_eq]
    have hs : (setup R).slot 18 = 2 := by rw [slot_eq]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hs], ?_⟩)))))
    refine ⟨by rw [hl, n_eq], by rw [hl, n_eq]; simp [setup], ?_, by rw [hl, n_eq]; simp⟩
    rw [hs]
    show ¬ ((setup R).cfg H (adv δ) 19 1).G.Reachable 1 0
    intro hre
    exact Setup.not_reachable_of_isolated (v := 0) (c := 1) (by decide)
      (fun a ha => u_isolated hy (r := 19) (by omega) a ha.symm) hre.symm
  simp only [Setup.commit, hv, ↓reduceIte]

end

lemma H_compl : Hᶜ = {(2 : Fin 3)} := by
  ext y; fin_cases y <;> simp [H]

lemma ncard_compl : Hᶜ.ncard ≤ 1 := by rw [H_compl, Set.ncard_singleton]

/-- In slot `0` of the literal execution, `x` votes against `a` (it removed `a` in round `3`) and
commits `⊥`. -/
lemma x_commits_bot :
    (setup (Reading.literal 3)).commit H (adv 3) 0 0 = none := by
  have hv : (setup (Reading.literal 3)).Voted H (adv 3) 0 ((setup (Reading.literal 3)).S 0)
      (0 * (setup (Reading.literal 3)).T + ((setup (Reading.literal 3)).n +
        (setup (Reading.literal 3)).f + 2)) := by
    refine ⟨4, by rw [n_eq]; simp [setup], ?_⟩
    rw [Setup.out_succ]
    have hl : (setup (Reading.literal 3)).loc 4 = 4 := by rw [loc_eq]
    have hs : (setup (Reading.literal 3)).slot 4 = 0 := by rw [slot_eq]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by rw [hs], ?_⟩)))))
    refine ⟨by rw [hl, n_eq], by rw [hl, n_eq]; simp [setup], ?_, by rw [hl, n_eq]; simp⟩
    rw [hs]
    show ¬ ((setup (Reading.literal 3)).cfg H (adv 3) 5 0).G.Reachable 0 2
    exact Setup.not_reachable_of_isolated (v := 0) (c := 2) (by decide)
      (fun a ha => x_isolates_a hyp_literal (r := 5) (by omega) a ha.symm)
  simp only [Setup.commit, hv, ↓reduceIte]

/-- In slot `0` of the literal execution, `u` never removes `a`, does not vote, and commits
`true`. -/
lemma u_commits_true :
    (setup (Reading.literal 3)).commit H (adv 3) 1 0 = some true := by
  have hnv : ∀ r ≤ 6, Msg.corrupt 2 1 ∉ ((setup (Reading.literal 3)).cfg H (adv 3) (r + 1) 1).out := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr h
      have h' := h
      rw [Setup.out_succ] at h'
      rcases (setup (Reading.literal 3)).out_cases h' with hk | ⟨h1, -⟩ | ⟨y, h1, -⟩ | ⟨-, hds⟩
      · obtain ⟨r', h1, h2⟩ := (setup (Reading.literal 3)).origin (advValid _ 3) (r + 1) 1
          (by simp [H]) _ hk (by simp [Msg.signer, H])
        exact ih r' (by omega) (by omega) h2
      · simp at h1
      · simp at h1
      · apply hds.2.2.1
        show ((setup (Reading.literal 3)).cfg H (adv 3) (r + 1) 1).G.Reachable 1 _
        rw [u_top hyp_literal (r + 1) (by omega)]
        by_cases he : (1 : Fin 3) = (setup (Reading.literal 3)).S ((setup (Reading.literal 3)).slot r)
        · rw [← he]
        · exact (show (⊤ : SimpleGraph (Fin 3)).Adj 1 _ from he).reachable
  have hv : ¬ (setup (Reading.literal 3)).Voted H (adv 3) 1 ((setup (Reading.literal 3)).S 0)
      (0 * (setup (Reading.literal 3)).T + ((setup (Reading.literal 3)).n +
        (setup (Reading.literal 3)).f + 2)) := by
    rintro ⟨r, hr, h⟩
    rw [n_eq] at hr
    exact hnv r (by simpa [setup] using hr) h
  have hp : Setup.HasProp ((setup (Reading.literal 3)).cfg H (adv 3)
      (0 * (setup (Reading.literal 3)).T + (setup (Reading.literal 3)).n + 1) 1).know 0 :=
    ⟨true, prop_true_known _ 3 (by rw [n_eq]; omega)⟩
  rw [Setup.commit, ite_eq_right_of_eq_false _ _ (eq_false hv), dite_eq_left_of_eq_true (eq_true hp)]
  have := allowed_know (Reading.literal 3) 3 _ 1 (by simp [H]) _ hp.choose_spec
  simp only [Allowed, n_eq] at this
  congr 1
  rcases this with ⟨-, h | ⟨h, -⟩ | h⟩ | ⟨h, -⟩
  · exact h
  · exact absurd h (by decide)
  · omega
  · omega

/-- **Lemma 4 (Validity) of [WXMRS23] fails for Algorithm 5.2 read literally** (TrustCast rules,
including accusation processing, vertex removal and equivocation detection, only in rounds `1..n`
of the slot and only for the current slot): with `n = 3`, `f = 1` and one Byzantine node, an
honest node commits `⊥` in a slot whose sender is honest. -/
theorem literal_validity_fails :
    ∃ (P : Setup (Fin 3) Bool) (H : Set (Fin 3)) (adv : ℕ → Fin 3 → Set (Msg (Fin 3) Bool)),
      P.R = Reading.literal P.n ∧ P.AdvValid H adv ∧ Hᶜ.ncard ≤ P.f ∧ P.f < P.n ∧
      ∃ k u, P.S k ∈ H ∧ u ∈ H ∧ P.commit H adv u k ≠ some (P.input k) :=
  ⟨setup (Reading.literal 3), H, adv 3, by rw [n_eq]; rfl, advValid _ 3, ncard_compl,
    by rw [n_eq]; simp [setup], 2, 1, by simp [setup, H], by simp [H],
    by rw [u_commits_bot hyp_literal]; simp⟩

/-- Integrity (TrustCast property 3) fails in the literal reading: an honest node accuses an honest
node. -/
theorem literal_integrity_fails :
    (0 : Fin 3) ∈ H ∧ (1 : Fin 3) ∈ H ∧
      Msg.accuse 0 1 ∈ ((setup (Reading.literal 3)).cfg H (adv 3) 10 1).out :=
  ⟨by simp [H], by simp [H], u_accuses_x hyp_literal⟩

/-- **Lemma 5 (Consistency) of [WXMRS23] fails for Algorithm 5.2 read literally**: in the same
execution, in slot `0` the honest `x` commits `⊥` and the honest `u` commits `true`. -/
theorem literal_consistency_fails :
    ∃ (P : Setup (Fin 3) Bool) (H : Set (Fin 3)) (adv : ℕ → Fin 3 → Set (Msg (Fin 3) Bool)),
      P.R = Reading.literal P.n ∧ P.AdvValid H adv ∧ Hᶜ.ncard ≤ P.f ∧ P.f < P.n ∧
      ∃ k u v, u ∈ H ∧ v ∈ H ∧ P.commit H adv u k ≠ P.commit H adv v k :=
  ⟨setup (Reading.literal 3), H, adv 3, by rw [n_eq]; rfl, advValid _ 3, ncard_compl,
    by rw [n_eq]; simp [setup], 0, 0, 1, by simp [H], by simp [H],
    by rw [x_commits_bot, u_commits_true]; simp⟩

/-- Validity also fails if graph maintenance runs in every round but equivocation evidence is only
considered during its own slot (`Reading.slotLocal`): the second proposal reaches `x` in the last
round of slot `0`. -/
theorem slotLocal_validity_fails :
    ∃ (P : Setup (Fin 3) Bool) (H : Set (Fin 3)) (adv : ℕ → Fin 3 → Set (Msg (Fin 3) Bool)),
      P.R = Reading.slotLocal ∧ P.AdvValid H adv ∧ Hᶜ.ncard ≤ P.f ∧ P.f < P.n ∧
      ∃ k u, P.S k ∈ H ∧ u ∈ H ∧ P.commit H adv u k ≠ some (P.input k) :=
  ⟨setup Reading.slotLocal, H, adv 6, rfl, advValid _ 6, ncard_compl,
    by rw [n_eq]; simp [setup], 2, 1, by simp [setup, H], by simp [H],
    by rw [u_commits_bot hyp_slotLocal]; simp⟩

/-! ### Non-vacuity: the same attack against the charitable reading

All hypotheses of `Setup.validity` and `Setup.consistency` hold for this execution under the
charitable reading, and there the honest `u` does commit the honest sender's message in slot `2`. -/

example : (setup Reading.charitable).AdvValid H (adv 3) ∧
    Hᶜ.ncard ≤ (setup Reading.charitable).f ∧
    (setup Reading.charitable).f < (setup Reading.charitable).n := by
  refine ⟨advValid _ 3, ncard_compl, by rw [n_eq]; simp [setup]⟩

example : (setup Reading.charitable).commit H (adv 3) 1 2 = some true :=
  (setup Reading.charitable).validity rfl (advValid _ 3) 2 (by simp [setup, H]) (by simp [H])

example (k : ℕ) :
    (setup Reading.charitable).commit H (adv 3) 0 k =
      (setup Reading.charitable).commit H (adv 3) 1 k :=
  (setup Reading.charitable).consistency rfl (advValid _ 3) ncard_compl k (by simp [H]) (by simp [H])

end Counterexample

end Podc.AmortizedByzantineBroadcast.DishonestMajority
