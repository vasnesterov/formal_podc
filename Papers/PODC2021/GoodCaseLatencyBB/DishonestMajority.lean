import Papers.PODC2021.GoodCaseLatencyBB.DelayCover
import Papers.PODC2021.GoodCaseLatencyBB.SyncThird

/-!
# Theorem 19: good-case latency of BRB with a dishonest majority

Abraham, Nayak, Ren, Xiang, *Good-case Latency of Byzantine Broadcast: a Complete
Categorization*, PODC 2021 (arXiv:2102.07240v3), Appendix C.5, Theorem 19.

Let `h = n - f ≥ 2`, `f ≥ n / 2` and `k = ⌊n / h⌋ ≥ 2`. The processes are split into groups
`G 0 = {s}, G 1, …, G (2k-1)` (label `g : P → ℕ`), such that two cyclically consecutive groups
contain `≥ h` processes. The executions of the paper are covering runs (`DCover.run`, all
delays `Δ`) of the *ring* (`ring`): node `some p` sits at position `g p`, a second copy `none` of the
broadcaster sits at position `2k` (next to `G (2k-1)`), every node listens to the nodes of the
neighbouring positions, and at time `0` the groups `G j`, `j ≤ k`, listen to the left copy of the
broadcaster (proposal `a`) and the others to the right copy (proposal `b`).

* `ring s g k a b cL cR`: the ring where the broadcaster references of the left groups (resp.
  right groups) go to `cL` (resp. `cR`): `W0` = (`some s`, `some s`), `W*` = (`some s`, `none`),
  `W1` = (`none`, `none`).
* `exRun j`: the paper's Execution `j` (`0 ≤ j ≤ 2k-1`): `G j ∪ G (j+1)` correct (cyclically).
* Locality: `G 1` sees the same in `W0` and `W*` before `(k+1)Δ`, `G (2k-1)` the same in `W*`
  and `W1` before `kΔ`.
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

namespace DishonestMajority

variable {P M S V K : Type*} [DecidableEq P]

/-- Ring position of a node: `some p` is at `g p`, the right copy `none` of the broadcaster at
`2k`. -/
def lab (g : P → ℕ) (k : ℕ) : Option P → ℕ
  | none => 2 * k
  | some p => g p

/-- The ring covering system. Node `some p` runs `p`, node `none` runs the broadcaster `s`;
proposals: `a` everywhere except `b` at `none`. A node listens to nodes at neighbouring positions;
broadcaster messages come from the node itself (for the copies of `s`), from `cL` for `G 1`,
from `cR` for `G (2k-1)`, and at time `0` (the proposal) from `cL` for `G j`, `j ≤ k`, and from
`cR` otherwise. -/
def ring (s : P) (g : P → ℕ) (k : ℕ) (a b : V) (cL cR : Option P) :
    DCover P (Option P) V where
  proc x := x.getD s
  inp x := x.elim b fun _ => a
  nbr σ x q :=
    if q = s then
      match x with
      | none => some none
      | some p =>
        if p = s then some (some s)
        else if g p = 1 then some cL
        else if g p = 2 * k - 1 then some cR
        else if σ = 0 then (if g p ≤ k then some cL else some cR)
        else none
    else if g q ≤ lab g k x + 1 ∧ lab g k x ≤ g q + 1 then some (some q) else none

section ring

variable (s : P) (g : P → ℕ) (k : ℕ) (a b : V) (cL cR : Option P)

theorem ring_nbr_ne {q : P} (hq : q ≠ s) (σ : ℕ) (x : Option P) :
    (ring s g k a b cL cR).nbr σ x q =
      if g q ≤ lab g k x + 1 ∧ lab g k x ≤ g q + 1 then some (some q) else none := by
  simp [ring, hq]

theorem ring_nbr_none (σ : ℕ) : (ring s g k a b cL cR).nbr σ none s = some none := by
  simp [ring]

theorem ring_nbr_self (σ : ℕ) : (ring s g k a b cL cR).nbr σ (some s) s = some (some s) := by
  simp [ring]

theorem ring_nbr_some {p : P} (hp : p ≠ s) (σ : ℕ) :
    (ring s g k a b cL cR).nbr σ (some p) s =
      if g p = 1 then some cL
      else if g p = 2 * k - 1 then some cR
      else if σ = 0 then (if g p ≤ k then some cL else some cR)
      else none := by
  simp [ring, hp]

@[simp] theorem ring_proc (x : Option P) : (ring s g k a b cL cR).proc x = x.getD s := rfl

@[simp] theorem ring_inp (x : Option P) : (ring s g k a b cL cR).inp x = x.elim b fun _ => a :=
  rfl

end ring

/-- The groups `j` and `j + 1` (cyclically: `G (2k-1)` and `G 0`). -/
def pair (g : P → ℕ) (k j : ℕ) (p : P) : Prop :=
  g p = j ∨ g p = j + 1 ∨ (j = 2 * k - 1 ∧ g p = 0)

instance (g : P → ℕ) (k j : ℕ) : DecidablePred (pair g k j) := fun p => by
  unfold pair; infer_instance

/-- The faulty processes of Execution `j`: all but `G j ∪ G (j+1)`. -/
def fset [Fintype P] (g : P → ℕ) (k j : ℕ) : Finset P := univ.filter fun p => ¬ pair g k j p

theorem mem_fset [Fintype P] {g : P → ℕ} {k j : ℕ} {p : P} :
    p ∈ fset g k j ↔ ¬ pair g k j p := by simp [fset]

/-- A labelling of the processes for the ring argument with `f` faults. -/
structure IsRingLabel [Fintype P] (s : P) (g : P → ℕ) (k f : ℕ) : Prop where
  two_le : 2 ≤ k
  eq_zero : ∀ p, g p = 0 ↔ p = s
  le : ∀ p, g p ≤ 2 * k - 1
  nonempty : ∀ j, 1 ≤ j → j ≤ 2 * k - 1 → ∃ p, g p = j
  card_le : ∀ j ≤ 2 * k - 1, (fset g k j).card ≤ f

/-- Left references of the world of Execution `j`. -/
def cL (s : P) (k j : ℕ) : Option P := if j = 2 * k - 1 then none else some s

/-- Right references of the world of Execution `j`. -/
def cR (s : P) (j : ℕ) : Option P := if j = 0 then some s else none

/-- The lift of Execution `j`. -/
def lift (s : P) (k j : ℕ) (p : P) : Option P := if j = 2 * k - 1 ∧ p = s then none else some p

/-- The world of Execution `j`. -/
abbrev world (s : P) (g : P → ℕ) (k : ℕ) (a b : V) (j : ℕ) : DCover P (Option P) V :=
  ring s g k a b (cL s k j) (cR s j)

/-- **Execution `j`** of the paper (`0 ≤ j ≤ 2k-1`), with delivery offset `e` (delay `e + 1`). -/
def exRun [Fintype P] (A : Algorithm P M S V V) (e : ℕ) (s : P) (g : P → ℕ) (k : ℕ) (a b : V)
    (j : ℕ) : Run P M V :=
  (world s g k a b j).run A e (fset g k j) (lift s k j)

section runs

variable [Fintype P] {s : P} {g : P → ℕ} {k f : ℕ} (hg : IsRingLabel s g k f) (a b : V)
include hg

theorem cov {j : ℕ} (hj : j ≤ 2 * k - 1) :
    ∀ p ∉ fset g k j, (world s g k a b j).proc (lift s k j p) = p ∧
      ∀ q ∉ fset g k j, ∀ σ, (world s g k a b j).nbr σ (lift s k j p) q = some (lift s k j q) := by
  have h2 := hg.two_le
  intro p hp
  rw [mem_fset, not_not] at hp
  refine ⟨by unfold lift; split_ifs with h; exacts [by simp [h.2], rfl], fun q hq σ => ?_⟩
  rw [mem_fset, not_not] at hq
  have hp0 := hg.eq_zero p
  have hq0 := hg.eq_zero q
  have hpl := hg.le p
  have hql := hg.le q
  have hs0 := (hg.eq_zero s).2 rfl
  unfold pair at hp hq
  by_cases hqs : q = s
  · subst hqs
    by_cases hps : p = q
    · subst hps
      unfold lift
      split_ifs with h
      · exact ring_nbr_none _ _ _ _ _ _ _ _
      · exact ring_nbr_self _ _ _ _ _ _ _ _
    · have : lift q k j p = some p := by simp [lift, hps]
      have hp' : g p ≠ 0 := fun h => hps (hp0.1 h)
      rw [this, ring_nbr_some _ _ _ _ _ _ _ hps]
      simp only [cL, cR, lift, and_true]
      split_ifs <;> first | rfl | omega
  · have : lift s k j q = some q := by simp [lift, hqs]
    have hq' : g q ≠ 0 := fun h => hqs (hq0.1 h)
    rw [this, ring_nbr_ne _ _ _ _ _ _ _ hqs, ite_eq_left]
    unfold lift
    split_ifs with h
    · simp only [lab]; omega
    · simp only [lab]
      by_cases hps : p = s
      · have : j ≠ 2 * k - 1 := fun h1 => h ⟨h1, hps⟩
        subst hps; omega
      · have hp' : g p ≠ 0 := fun h => hps (hp0.1 h)
        omega

theorem exRun_syncValid (A : Algorithm P M S V V) (e : ℕ) {j : ℕ} (hj : j ≤ 2 * k - 1) :
    exRun A e s g k a b j ∈ syncRuns f (e + 1) :=
  DCover.run_syncValid A e _ (hg.card_le j hj) _

theorem exRun_authValid {Au : Auth P M K} {A : Algorithm P M S V V} (hU : A.Unforging Au)
    (e : ℕ) {j : ℕ} (hj : j ≤ 2 * k - 1) : (exRun A e s g k a b j).AuthValid Au A := by
  have h2 := hg.two_le
  have hs0 := (hg.eq_zero s).2 rfl
  refine DCover.run_authValid A e _ hU (cov hg a b hj)
    {x | (j = 0 → x ≠ none) ∧ (j = 2 * k - 1 → x ≠ some s)} ?_ ?_ ?_
  · intro x hx σ q y hy
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_cases hqs : q = s
    · subst hqs
      cases x with
      | none => rw [ring_nbr_none] at hy; cases hy; exact ⟨hx, rfl⟩
      | some p =>
        by_cases hps : p = q
        · subst hps; rw [ring_nbr_self] at hy; cases hy; exact ⟨hx, rfl⟩
        · rw [ring_nbr_some _ _ _ _ _ _ _ hps] at hy
          simp only [cL, cR] at hy
          refine ⟨⟨fun h0 => ?_, fun h1 => ?_⟩, ?_⟩ <;> split_ifs at hy <;> cases hy <;>
            first | rfl | omega | simp
    · rw [ring_nbr_ne _ _ _ _ _ _ _ hqs] at hy
      split_ifs at hy
      cases hy
      exact ⟨⟨by simp, by simp [hqs]⟩, rfl⟩
  · intro p hp
    rw [mem_fset, not_not] at hp
    have hp0 := hg.eq_zero p
    unfold pair at hp
    simp only [Set.mem_ofPred_eq, lift]
    constructor <;> intro h <;> split_ifs with h' <;> grind
  · intro z hz hzF
    rw [mem_fset, not_not] at hzF
    simp only [Set.mem_ofPred_eq] at hz
    unfold pair at hzF
    cases z with
    | none =>
      simp only [ring_proc, Option.getD_none] at hzF ⊢
      simp only [lift, and_true]
      split_ifs with h
      · rfl
      · exfalso; rw [hs0] at hzF; exact hz.1 (by omega) rfl
    | some p =>
      simp only [ring_proc, Option.getD_some, lift]
      split_ifs with h
      · obtain ⟨h1, rfl⟩ := h; exact absurd rfl (hz.2 h1)
      · exact (ite_eq_right h).symm

end runs


/-! ### Locality -/

section locality

variable {s : P} {g : P → ℕ} {k : ℕ} (A : Algorithm P M S V V) (e : ℕ) (a b : V)

/-- **Locality at `G 1`**: the worlds `W0` (all broadcaster references to the left copy) and `W*`
look the same to `G 1` before time `(k+1)Δ`: the right copy's proposal reaches `G (k+1)` at `Δ`
and needs `k` more hops. -/
theorem loc_left (h2 : 2 ≤ k) (hg0 : ∀ p, g p = 0 ↔ p = s) {p : P} (hp : g p = 1) :
    ∀ τ < (e + 1) * (k + 1), (ring s g k a b (some s) (some s)).st A e τ (some p) =
      (ring s g k a b (some s) none).st A e τ (some p) := by
  intro τ hτ
  have hs0 := (hg0 s).2 rfl
  refine DCover.st_eq_of_level (C' := ring s g k a b (some s) (some s)) A e (ring s g k a b (some s) none) rfl
    (fun x => x.elim (k + 1) fun p => g p - 1)
    ((e + 1) * (k + 1)) ?_ (fun _ _ => rfl) τ (some p) (by simp [hp]; omega)
  intro σ x q h
  have hlt := DCover.lt_of_add_mul_lt h
  cases x with
  | none => simp at hlt
  | some p' =>
    simp only [Option.elim_some] at hlt ⊢
    by_cases hqs : q = s
    · subst hqs
      by_cases hps : p' = q
      · subst hps
        simp only [ring_nbr_self, Option.some.injEq, forall_eq', Option.elim_some, hs0]
        exact ⟨trivial, by omega⟩
      · rw [ring_nbr_some _ _ _ _ _ _ _ hps, ring_nbr_some _ _ _ _ _ _ _ hps]
        refine ⟨?_, fun y hy => ?_⟩
        · split_ifs <;> first | rfl | omega
        · split_ifs at hy <;> first | omega | (cases hy; simp [hs0])
    · rw [ring_nbr_ne _ _ _ _ _ _ _ hqs, ring_nbr_ne _ _ _ _ _ _ _ hqs]
      refine ⟨rfl, fun y hy => ?_⟩
      split_ifs at hy with hc
      cases hy; simp only [lab, Option.elim_some] at hc ⊢; omega

/-- **Locality at `G (2k-1)`**: the worlds `W*` and `W1` (all broadcaster references to the right
copy) look the same to `G (2k-1)` before time `kΔ`: the left copy's proposal reaches `G k` at `Δ`
and needs `k - 1` more hops. -/
theorem loc_right (h2 : 2 ≤ k) (hg0 : ∀ p, g p = 0 ↔ p = s) (hle : ∀ p, g p ≤ 2 * k - 1)
    {p : P} (hp : g p = 2 * k - 1) :
    ∀ τ < (e + 1) * k, (ring s g k a b none none).st A e τ (some p) =
      (ring s g k a b (some s) none).st A e τ (some p) := by
  intro τ hτ
  have hs0 := (hg0 s).2 rfl
  have hps : p ≠ s := fun h => by rw [h] at hp; omega
  refine DCover.st_eq_of_level (C' := ring s g k a b none none) A e (ring s g k a b (some s) none) rfl
    (fun x => x.elim 0 fun p => if p = s then k else 2 * k - 1 - g p)
    ((e + 1) * k) ?_ (fun _ _ => rfl) τ (some p) (by simp [hp, hps]; omega)
  intro σ x q h
  have hlt := DCover.lt_of_add_mul_lt h
  cases x with
  | none =>
    by_cases hqs : q = s
    · subst hqs
      simp only [ring_nbr_none, Option.some.injEq, forall_eq', Option.elim_none]
      exact ⟨trivial, by omega⟩
    · rw [ring_nbr_ne _ _ _ _ _ _ _ hqs, ring_nbr_ne _ _ _ _ _ _ _ hqs]
      refine ⟨rfl, fun y hy => ?_⟩
      split_ifs at hy with hc
      cases hy; simp only [lab, Option.elim_some, Option.elim_none, hqs, ite_false] at hc ⊢
      omega
  | some p' =>
    by_cases hps' : p' = s
    · subst hps'; simp at hlt
    simp only [Option.elim_some, hps', ite_false] at hlt ⊢
    have hp'l := hle p'
    have hp'0 : g p' ≠ 0 := fun h => hps' ((hg0 p').1 h)
    by_cases hqs : q = s
    · subst hqs
      rw [ring_nbr_some _ _ _ _ _ _ _ hps', ring_nbr_some _ _ _ _ _ _ _ hps']
      refine ⟨?_, fun y hy => ?_⟩
      · split_ifs <;> first | rfl | omega
      · split_ifs at hy <;> first | omega | (cases hy; simp)
    · rw [ring_nbr_ne _ _ _ _ _ _ _ hqs, ring_nbr_ne _ _ _ _ _ _ _ hqs]
      refine ⟨rfl, fun y hy => ?_⟩
      split_ifs at hy with hc
      cases hy; simp only [lab, Option.elim_some, hqs, ite_false] at hc ⊢
      omega

end locality

/-! ### The groups -/

/-- The group of the process of rank `r`: rank `0` is the broadcaster (group `0`), then blocks of
`h` ranks `qh, qh+1, …, qh+h-1` form a singleton group `2q` and a group `2q+1` of size `h - 1`; the
last group `2k-1` collects all remaining ranks. -/
def grp (h k r : ℕ) : ℕ :=
  if r = 0 then 0 else min (if r % h = 0 then 2 * (r / h) else 2 * (r / h) + 1) (2 * k - 1)

theorem grp_spec {h k q m : ℕ} (hm : m < h) (hne : q * h + m ≠ 0) :
    grp h k (q * h + m) = min (if m = 0 then 2 * q else 2 * q + 1) (2 * k - 1) := by
  have hd := (Nat.div_mod_unique (a := q * h + m) (b := h) (d := q) (c := m) (by omega)).2
    ⟨by rw [Nat.mul_comm]; omega, hm⟩
  simp only [grp, hne, ite_false, hd.1, hd.2]

theorem exists_ringLabel [Fintype P] (s : P) {f : ℕ} (hh : 2 ≤ Fintype.card P - f)
    (hf : Fintype.card P ≤ 2 * f) :
    ∃ g : P → ℕ, IsRingLabel s g (Fintype.card P / (Fintype.card P - f)) f := by
  set n := Fintype.card P with hn
  set h := n - f with hhd
  set k := n / h with hkd
  have hk : 2 ≤ k := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hkh : k * h ≤ n := Nat.div_mul_le_self n h
  have hn0 : 0 < n := by omega
  set e : P ≃ Fin n := (Fintype.equivFin P).trans (Equiv.swap ((Fintype.equivFin P) s) ⟨0, hn0⟩)
    with he
  have hes : e s = ⟨0, hn0⟩ := by simp [he]
  have hes' : ∀ p, (e p : ℕ) = 0 ↔ p = s := by
    intro p
    constructor
    · intro h0
      apply e.injective
      rw [hes]; exact Fin.ext h0
    · rintro rfl; rw [hes]
  -- every rank decomposes as `q * h + m`
  have hdec : ∀ r : ℕ, r = r / h * h + r % h := fun r => by
    have := Nat.div_add_mod r h; rw [Nat.mul_comm] at this; omega
  have hmod : ∀ r : ℕ, r % h < h := fun r => Nat.mod_lt r (by omega)
  -- the rank-`r` process, for `r < n`
  let φ : ℕ → P := fun r => e.symm ⟨min r (n - 1), by omega⟩
  have hφ : ∀ r < n, (e (φ r) : ℕ) = r := fun r hr => by
    simp only [φ, Equiv.apply_symm_apply]; omega
  have hφinj : ∀ r₁ < n, ∀ r₂ < n, φ r₁ = φ r₂ → r₁ = r₂ := fun r₁ h₁ r₂ h₂ he => by
    rw [← hφ r₁ h₁, ← hφ r₂ h₂, he]
  refine ⟨fun p => grp h k (e p), ?_⟩
  have hpair : ∀ j ≤ 2 * k - 1, h ≤ (univ.filter (pair (fun p => grp h k (e p)) k j)).card := by
    intro j hj
    let rk : ℕ → ℕ := fun m =>
      if j = 2 * k - 1 then (if m = 0 then 0 else (k - 1) * h + m) else j / 2 * h + j % 2 + m
    -- bounds and groups of the chosen ranks
    have hrk : ∀ m < h, rk m < n ∧ pair (fun p => grp h k (e p)) k j (φ (rk m)) := by
      intro m hm
      have hk1 : (k - 1 + 1) * h ≤ n := by rw [show k - 1 + 1 = k by omega]; exact hkh
      rw [Nat.add_mul, Nat.one_mul] at hk1
      by_cases hjl : j = 2 * k - 1
      · by_cases hm0 : m = 0
        · have : rk m = 0 := by simp [rk, hjl, hm0]
          rw [this]
          refine ⟨hn0, Or.inr (Or.inr ⟨hjl, ?_⟩)⟩
          simp only [hφ 0 hn0, grp, ite_true]
        · have : rk m = (k - 1) * h + m := by simp [rk, hjl, hm0]
          rw [this]
          refine ⟨by omega, Or.inl ?_⟩
          simp only
          rw [hφ _ (by omega), grp_spec hm (by omega)]
          simp only [hm0, ite_false]; omega
      · obtain ⟨q, rfl | rfl⟩ := Nat.even_or_odd' j
        · have : rk m = q * h + m := by
            simp only [rk, hjl, ite_false, show 2 * q / 2 = q by omega,
              show 2 * q % 2 = 0 by omega, Nat.add_zero]
          rw [this]
          have hq1 : (q + 1) * h ≤ k * h := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at hq1
          refine ⟨by omega, ?_⟩
          simp only [pair]
          rw [hφ _ (by omega)]
          by_cases h0 : q * h + m = 0
          · rw [h0]; left
            have : q ≤ q * h := Nat.le_mul_of_pos_right q (by omega)
            simp only [grp, ite_true]; omega
          · rw [grp_spec hm h0]
            split_ifs <;> omega
        · have hq1 : (q + 1 + 1) * h ≤ k * h := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.add_mul, Nat.one_mul] at hq1
          have : rk m = q * h + 1 + m := by
            simp only [rk, hjl, ite_false, show (2 * q + 1) / 2 = q by omega,
              show (2 * q + 1) % 2 = 1 by omega]
          rw [this]
          refine ⟨by omega, ?_⟩
          simp only [pair]
          rw [hφ _ (by omega)]
          by_cases hm1 : m + 1 < h
          · rw [show q * h + 1 + m = q * h + (m + 1) by omega, grp_spec hm1 (by omega)]
            simp only [show m + 1 ≠ 0 by omega, ite_false]; omega
          · rw [show q * h + 1 + m = (q + 1) * h + 0 by rw [Nat.add_mul]; omega,
              grp_spec (by omega) (by rw [Nat.add_mul]; omega)]
            simp only [ite_true]; omega
    calc h = (range h).card := (card_range h).symm
      _ ≤ _ := by
        refine card_le_card_of_injOn (fun m => φ (rk m)) (fun m hm => ?_) (fun m₁ hm₁ m₂ hm₂ he => ?_)
        · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]
          exact (hrk m (by simpa using hm)).2
        · simp only [coe_range, Set.mem_Iio] at hm₁ hm₂
          have := hφinj _ (hrk m₁ hm₁).1 _ (hrk m₂ hm₂).1 he
          simp only [rk] at this
          split_ifs at this <;> omega
  refine ⟨hk, fun p => ?_, fun p => ?_, fun j hj1 hj => ?_, fun j hj => ?_⟩
  · rw [← hes' p]
    constructor
    · intro h0
      by_contra hne
      rw [hdec (e p), grp_spec (hmod _) (by rw [← hdec]; exact hne)] at h0
      split_ifs at h0 with hm0
      · have : (e p : ℕ) / h ≠ 0 := fun hq => by
          have := hdec (e p); rw [hq, hm0] at this; simp at this; exact hne this
        omega
      · omega
    · intro h0; simp [grp, h0]
  · simp only [grp]; split_ifs <;> omega
  · have hb : j / 2 * h + j % 2 < n := by
      have hq1 : (j / 2 + 1) * h ≤ k * h := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hq1
      omega
    refine ⟨φ (j / 2 * h + j % 2), ?_⟩
    have := Nat.le_mul_of_pos_right (j / 2) (show 0 < h by omega)
    rw [hφ _ hb, grp_spec (by omega) (by omega)]
    split_ifs <;> omega
  · have := hpair j hj
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset P)) (pair (fun p => grp h k (e p)) k j)
    simp only [card_univ] at hsum
    simp only [fset]
    omega

/-! ### The chain of executions -/

section main

variable [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V} {s : P} {g : P → ℕ} {k f : ℕ}

/-- The ring argument: with a ring labelling for `f` faults, no BRB protocol (for delay bound
`Δ = e + 1`) lets all honest processes commit before time `kΔ` when the broadcaster is honest. -/
theorem not_latencyWithin_of_ringLabel (hU : A.Unforging Au) (hg : IsRingLabel s g k f) {e : ℕ}
    {a b : V} (hab : a ≠ b) (hA : IsBRB Au A s (syncRuns f (e + 1))) :
    ¬ LatencyWithin Au A s (syncRuns f (e + 1)) ((e + 1) * k - 1) := by
  intro hlat
  have h2 := hg.two_le
  have hs0 := (hg.eq_zero s).2 rfl
  set W := ring s g k a b (some s) none with hW
  set R := exRun A e s g k a b with hR
  have hV : ∀ j ≤ 2 * k - 1, R j ∈ syncRuns f (e + 1) := fun j hj =>
    exRun_syncValid hg a b A e hj
  have hAV : ∀ j ≤ 2 * k - 1, (R j).AuthValid Au A := fun j hj => exRun_authValid hg a b hU e hj
  have hF : ∀ j p, pair g k j p → p ∉ (R j).faulty := fun j p hp => by
    simp only [hR, exRun, DCover.run_faulty, mem_fset, not_not]; exact hp
  have hdec : ∀ j ≤ 2 * k - 1, ∀ p, pair g k j p → ∀ v, (R j).Decides A p v ↔
      ∃ τ, A.decide p ((world s g k a b j).st A e τ (lift s k j p)) = some v :=
    fun j hj p hp v => DCover.decides_run_iff A e _ (cov hg a b hj)
      (by rw [mem_fset, not_not]; exact hp)
  have hst : ∀ j ≤ 2 * k - 1, ∀ p, pair g k j p → ∀ τ,
      (R j).st A τ p = (world s g k a b j).st A e τ (lift s k j p) :=
    fun j hj p hp τ => DCover.st_run_correct A e _ (cov hg a b hj) τ p
      (by rw [mem_fset, not_not]; exact hp)
  -- a commit by the deadline in a good-case execution `j` has the broadcaster's value
  have hcommit : ∀ j ≤ 2 * k - 1, s ∉ (R j).faulty → ∀ p, pair g k j p →
      ∃ τ ≤ (e + 1) * k - 1, A.decide p ((R j).st A τ p) = some ((R j).inp s) := by
    intro j hj hs p hp
    exact CommitsBy.eq_of_agreement
      (fun w hw hv => hA.agreement _ (hV j hj) (hAV j hj) p (hF j p hp) p (hF j p hp) w _ hw hv)
      (hlat _ (hV j hj) (hAV j hj) hs p (hF j p hp))
      (hA.validity _ (hV j hj) (hAV j hj) hs p (hF j p hp))
  have hpos : 1 ≤ (e + 1) * k := Nat.mul_pos (by omega) (by omega)
  -- left end: `G 1` decides `a` in `W*`
  have hleft : ∀ p, g p = 1 → ∃ τ, A.decide p (W.st A e τ (some p)) = some a := by
    intro p hp
    have hp0 : pair g k 0 p := Or.inr (Or.inl (by omega))
    have hs : s ∉ (R 0).faulty := hF 0 s (Or.inl hs0)
    obtain ⟨τ, hτ, hd⟩ := hcommit 0 (by omega) hs p hp0
    rw [hst 0 (by omega) p hp0] at hd
    have hl : ∀ q, lift s k 0 q = some q := fun q => by simp [lift]; omega
    have hc : cL s k 0 = some s := by simp [cL]; omega
    have hc' : cR s 0 = some s := by simp [cR]
    simp only [world, hl, hc, hc'] at hd
    refine ⟨τ, ?_⟩
    have hinp : (R 0).inp s = a := by rw [hR, exRun, DCover.run_inp, hl]; rfl
    have hkk : (e + 1) * k ≤ (e + 1) * (k + 1) := Nat.mul_le_mul_left _ (by omega)
    rw [← loc_left A e a b h2 hg.eq_zero hp τ (by omega)]
    rw [hinp] at hd
    exact hd
  -- right end: `G (2k-1)` decides `b` in `W*`
  have hright : ∀ p, g p = 2 * k - 1 → ∃ τ, A.decide p (W.st A e τ (some p)) = some b := by
    intro p hp
    have hps : p ≠ s := fun h => by rw [h] at hp; omega
    have hp0 : pair g k (2 * k - 1) p := Or.inl hp
    have hs : s ∉ (R (2 * k - 1)).faulty := hF _ s (Or.inr (Or.inr ⟨rfl, hs0⟩))
    obtain ⟨τ, hτ, hd⟩ := hcommit (2 * k - 1) le_rfl hs p hp0
    rw [hst _ le_rfl p hp0] at hd
    have hl : lift s k (2 * k - 1) p = some p := by simp [lift, hps]
    have hls : lift s k (2 * k - 1) s = none := by simp [lift]
    have hc : cL s k (2 * k - 1) = none := by simp [cL]
    have hc' : cR s (2 * k - 1) = none := by simp [cR]; omega
    simp only [world, hl, hc, hc'] at hd
    refine ⟨τ, ?_⟩
    have hinp : (R (2 * k - 1)).inp s = b := by rw [hR, exRun, DCover.run_inp, hls]; rfl
    rw [← loc_right A e a b h2 hg.eq_zero hg.le hp τ (by omega)]
    rw [hinp] at hd
    exact hd
  -- middle executions live in `W*`
  have hmid : ∀ j, j ≠ 0 → j ≠ 2 * k - 1 → world s g k a b j = W ∧ ∀ p, lift s k j p = some p := by
    intro j hj0 hj1
    refine ⟨by simp [world, cL, cR, hj0, hj1, hW], fun p => by simp [lift, hj1]⟩
  -- the chain
  have chain : ∀ j, 1 ≤ j → j ≤ 2 * k - 1 → ∀ p, g p = j →
      ∃ τ, A.decide p (W.st A e τ (some p)) = some a := by
    intro j hj1
    induction j, hj1 using Nat.le_induction with
    | base => intro _ p hp; exact hleft p hp
    | succ j hj1 ih =>
      intro hj p hp
      obtain ⟨p₀, hp₀⟩ := hg.nonempty j hj1 (by omega)
      obtain ⟨hw, hl⟩ := hmid j (by omega) (by omega)
      have hp₀j : pair g k j p₀ := Or.inl hp₀
      have hpj : pair g k j p := Or.inr (Or.inl hp)
      have hd0 : (R j).Decides A p₀ a := by
        rw [hdec j (by omega) p₀ hp₀j, hw, hl]; exact ih (by omega) p₀ hp₀
      obtain ⟨w, hw'⟩ := hA.termination _ (hV j (by omega)) (hAV j (by omega))
        ⟨p₀, hF j p₀ hp₀j, a, hd0⟩ p (hF j p hpj)
      obtain rfl := hA.agreement _ (hV j (by omega)) (hAV j (by omega)) p₀ (hF j p₀ hp₀j) p
        (hF j p hpj) a w hd0 hw'
      rw [hdec j (by omega) p hpj, hw, hl] at hw'
      exact hw'
  obtain ⟨p, hp⟩ := hg.nonempty (2 * k - 1) (by omega) le_rfl
  have hpj : pair g k (2 * k - 2) p := Or.inr (Or.inl (by omega))
  obtain ⟨hw, hl⟩ := hmid (2 * k - 2) (by omega) (by omega)
  have da : (R (2 * k - 2)).Decides A p a := by
    rw [hdec _ (by omega) p hpj, hw, hl]; exact chain _ (by omega) le_rfl p hp
  have db : (R (2 * k - 2)).Decides A p b := by
    rw [hdec _ (by omega) p hpj, hw, hl]; exact hright p hp
  exact hab (hA.agreement _ (hV _ (by omega)) (hAV _ (by omega)) p (hF _ p hpj) p (hF _ p hpj)
    a b da db)

end main

/-! ### The proposal needs one delay -/

section proposal

variable [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V} {s : P} {f : ℕ}

/-- The fault-free system in which the broadcaster has proposal `v` and everybody else `a`. -/
def triv (s : P) (a v : V) : DCover P P V where
  proc := id
  inp p := if p = s then v else a
  nbr _ _ q := some q

/-- Trivial bound: if some process `p ≠ s` exists, no BRB protocol commits before the first
message of the broadcaster can arrive (time `Δ`), already in fault-free runs. -/
theorem not_latencyWithin_pred {p : P} (hps : p ≠ s) {e : ℕ} {a b : V} (hab : a ≠ b)
    (hA : IsBRB Au A s (syncRuns f (e + 1))) :
    ¬ LatencyWithin Au A s (syncRuns f (e + 1)) e := by
  intro hlat
  have hcov : ∀ v, ∀ q ∉ (∅ : Finset P), (triv s a v).proc (id q) = q ∧
      ∀ r ∉ (∅ : Finset P), ∀ σ, (triv s a v).nbr σ (id q) r = some (id r) :=
    fun _ _ _ => ⟨rfl, fun _ _ _ => rfl⟩
  let R : V → Run P M V := fun v => (triv s a v).run A e ∅ id
  have hV : ∀ v, R v ∈ syncRuns f (e + 1) := fun v =>
    DCover.run_syncValid A e _ (by simp) id
  have hF : ∀ v q, q ∉ (R v).faulty := fun v q => by simp [R]
  have hAV : ∀ v, (R v).AuthValid Au A := fun v b hb => absurd hb (hF v b)
  have hinp : ∀ v, (R v).inp s = v := fun v => by simp [R, triv]
  obtain ⟨τ, hτ, hd⟩ := CommitsBy.eq_of_agreement
    (fun w hw hv => hA.agreement _ (hV a) (hAV a) p (hF a p) p (hF a p) w _ hw hv)
    (hlat _ (hV a) (hAV a) (hF a s) p (hF a p))
    (hA.validity _ (hV a) (hAV a) (hF a s) p (hF a p))
  have hloc : (triv s a b).st A e τ p = (triv s a a).st A e τ p :=
    DCover.st_eq_of_level (C' := triv s a b) A e (triv s a a) rfl
      (fun x => if x = s then 1 else 0) (e + 1)
      (fun σ x q h => by
        have := Nat.le_mul_of_pos_right (e + 1) (show 0 < (if x = s then 1 else 0) + 1 by omega)
        omega)
      (fun x hx => by
        by_cases hxs : x = s
        · simp [hxs] at hx
        · simp [triv, hxs])
      τ p (by simp [hps]; omega)
  have hdb : (R b).Decides A p a := by
    refine ⟨τ, ?_⟩
    rw [DCover.st_run_correct A e _ (hcov b) τ p (by simp), id, hloc]
    rw [hinp, DCover.st_run_correct A e _ (hcov a) τ p (by simp)] at hd
    exact hd
  have := hA.validity _ (hV b) (hAV b) (hF b s) p (hF b p)
  rw [hinp] at this
  exact hab (hA.agreement _ (hV b) (hAV b) p (hF b p) p (hF b p) a b hdb this)

end proposal

end DishonestMajority

end GoodCaseLatencyBB

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync DishonestMajority

variable {P M S V K : Type*} [DecidableEq P]

/-! ### Monotonicity -/

theorem LatencyWithin.mono_time {Au : Auth P M K} {A : Algorithm P M S V V} {s : P}
    {Adm : Set (Run P M V)} {T T' : ℕ} (h : LatencyWithin Au A s Adm T) (hT : T ≤ T') :
    LatencyWithin Au A s Adm T' := fun R hR hav hs p hp => by
  obtain ⟨v, τ, hτ, hd⟩ := h R hR hav hs p hp
  exact ⟨v, τ, hτ.trans hT, hd⟩

theorem LatencyWithin.anti {Au : Auth P M K} {A : Algorithm P M S V V} {s : P}
    {Adm Adm' : Set (Run P M V)} {T : ℕ} (h : LatencyWithin Au A s Adm T) (hsub : Adm' ⊆ Adm) :
    LatencyWithin Au A s Adm' T := fun R hR => h R (hsub hR)

theorem IsBRB.anti {Au : Auth P M K} {A : Algorithm P M S V V} {s : P}
    {Adm Adm' : Set (Run P M V)} (h : IsBRB Au A s Adm) (hsub : Adm' ⊆ Adm) :
    IsBRB Au A s Adm' :=
  ⟨fun R hR => h.agreement R (hsub hR), fun R hR => h.validity R (hsub hR),
    fun R hR => h.termination R (hsub hR)⟩

theorem syncRuns_mono {f f' d : ℕ} (hf : f ≤ f') :
    (syncRuns f d : Set (Run P M V)) ⊆ syncRuns f' d := fun _ hR =>
  ⟨hR.card_faulty.trans hf, hR.dl_ge, hR.dl_lt⟩

/-! ### Main results -/

/-- **Theorem 19 of [ANRX21], strengthened.** Let `n = |P|`, `f ≥ n / 2` and `n - f ≥ 2`.
No Byzantine reliable broadcast protocol (synchronous, delay bound `Δ`, synchronized start,
unforgeable signatures) has good-case latency below `⌊n / (n - f)⌋ · Δ`: in some synchronous run
with an honest broadcaster some honest process has not committed by time
`⌊n / (n - f)⌋ · Δ - 1`. This is one `Δ` more than the paper's bound (the paper lets the
broadcaster's proposal arrive without delay). -/
theorem dishonestMajority_lower_bound [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V}
    (hU : A.Unforging Au) {s : P} {f Δ : ℕ} (hΔ : 1 ≤ Δ) (hh : 2 ≤ Fintype.card P - f)
    (hf : Fintype.card P ≤ 2 * f) {a b : V} (hab : a ≠ b) (hA : IsBRB Au A s (syncRuns f Δ)) :
    ¬ LatencyWithin Au A s (syncRuns f Δ) (Fintype.card P / (Fintype.card P - f) * Δ - 1) := by
  obtain ⟨e, rfl⟩ : ∃ e, Δ = e + 1 := ⟨Δ - 1, by omega⟩
  obtain ⟨g, hg⟩ := exists_ringLabel s hh hf
  rw [Nat.mul_comm]
  exact not_latencyWithin_of_ringLabel hU hg hab hA

/-- **Theorem 19 of [ANRX21]** (as stated): for `f ≥ n / 2` (and `n - f ≥ 2`), every BRB protocol
has good-case latency at least `(⌊n / (n - f)⌋ - 1) · Δ`, even with synchronized start. -/
theorem theorem_19 [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V}
    (hU : A.Unforging Au) {s : P} {f Δ : ℕ} (hΔ : 1 ≤ Δ) (hh : 2 ≤ Fintype.card P - f)
    (hf : Fintype.card P ≤ 2 * f) {a b : V} (hab : a ≠ b) (hA : IsBRB Au A s (syncRuns f Δ)) :
    ¬ LatencyWithin Au A s (syncRuns f Δ)
      ((Fintype.card P / (Fintype.card P - f) - 1) * Δ - 1) := fun h =>
  dishonestMajority_lower_bound hU hΔ hh hf hab hA
    (h.mono_time (Nat.sub_le_sub_right (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _))

/-- The case `f = n - 1` (excluded from `theorem_19`, whose proof needs `n - f ≥ 2`): a BRB
protocol tolerating `n - 1` faults has good-case latency at least `⌊n / 2⌋ · Δ` (by
monotonicity in `f` for `n ≥ 4`, and by `not_latencyWithin_pred` for `n ∈ {2, 3}`). -/
theorem allButOne_lower_bound [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V}
    (hU : A.Unforging Au) {s : P} {Δ : ℕ} (hΔ : 1 ≤ Δ) (hn : 2 ≤ Fintype.card P) {a b : V}
    (hab : a ≠ b) (hA : IsBRB Au A s (syncRuns (Fintype.card P - 1) Δ)) :
    ¬ LatencyWithin Au A s (syncRuns (Fintype.card P - 1) Δ) (Fintype.card P / 2 * Δ - 1) := by
  intro hlat
  by_cases h4 : 4 ≤ Fintype.card P
  · have hsub := syncRuns_mono (P := P) (M := M) (V := V) (d := Δ)
      (show Fintype.card P - 2 ≤ Fintype.card P - 1 by omega)
    have := dishonestMajority_lower_bound hU hΔ (f := Fintype.card P - 2) (by omega) (by omega)
      hab (hA.anti hsub)
    rw [show Fintype.card P - (Fintype.card P - 2) = 2 by omega] at this
    exact this (hlat.anti hsub)
  · obtain ⟨e, rfl⟩ : ∃ e, Δ = e + 1 := ⟨Δ - 1, by omega⟩
    obtain ⟨p, hps⟩ : ∃ p, p ≠ s := by
      by_contra hc
      simp only [ne_eq, not_exists, not_not] at hc
      have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 fun x y => (hc x).trans (hc y).symm
      omega
    refine not_latencyWithin_pred hps hab hA (hlat.mono_time ?_)
    rw [show Fintype.card P / 2 = 1 by omega]; omega

/-- Theorem 19's claim `(n − 1)Δ` for `f = n − 1` holds for `n = 3` (`2Δ`): it is Theorem 9 with
`δ = Δ` (`f = 2 ≥ n/3`). (For `n = 3, f = 2` the stronger bound `⌊n/(n−f)⌋Δ = 3Δ` fails: the 3-party
protocol of `ThreeParties.lean`, run with synchronized start, commits by `Δ + δ = 2Δ`.) -/
theorem theorem_19_three [Fintype P] {Au : Auth P M K} {A : Algorithm P M S V V}
    (hU : A.Unforging Au) {s : P} {Δ : ℕ} (hΔ : 1 ≤ Δ) (h3 : Fintype.card P = 3) {a b : V}
    (hab : a ≠ b) (hA : IsBRB Au A s (syncRuns (Fintype.card P - 1) Δ)) :
    ¬ LatencyWithin Au A s (syncRuns (Fintype.card P - 1) Δ)
      ((Fintype.card P - 1) * Δ - 1) := by
  have := theorem_9 hU (δ := Δ) hΔ le_rfl (by omega) (by omega) hab hA
  rw [h3] at this ⊢
  rwa [show (3 - 1) * Δ - 1 = Δ + Δ - 1 by omega]

end GoodCaseLatencyBB
