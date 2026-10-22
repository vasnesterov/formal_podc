import Papers.PODC2015.MinimalSynchronyBC.CB

/-!
# Byzantine consensus from CB, EA and AC objects (Figure 4, Theorem 4)

An execution of Figure 4 at the level of the objects it uses (the paper's proof of Theorem 4
uses only their specifications). A correct process `i`:
* line 1: `est_i ← CB[0].CB_broadcast VALID(inp i)`; round 1 starts with this estimate;
* line 4: `v ← EA_propose(r, est_i)` (`ea i r`);
* line 5: if `v ∈ CB[0].cb_valid_i` (at the time `t5 i r` of the test) then `est_i ← v`; the
  value proposed to `AC_OBJECT[r]` is `acIn i r`;
* line 6: `⟨tag, est_i⟩ ← AC_OBJECT[r].AC_propose(est_i)` (`ac i r`); round `r + 1` starts with
  this estimate (unless `i` decided and stopped);
* line 7: if `tag = commit`, RB-broadcast `DECIDE(est_i)` (RB instance `D r`);
* line 9: decide `v` once `DECIDE(v)` was RB-delivered from `t + 1` processes (`decT`).

`est i r = none` means that `i` never starts round `r` (rounds are numbered from 1).

* `Fig4.validity`, `Fig4.agreement`: **CONS-Validity and CONS-Agreement** (the safety part of
  Theorem 4) in every execution, from CB-Set Validity of `CB[0]`, the AC specification of every
  `AC_OBJECT[r]`, EA-Validity of every round, and RB-Validity of `DECIDE`.
* `Fig4.termination`: **CONS-Termination**, *assuming* that the EA object satisfies
  EA-Termination and EA-Eventual agreement — the composition argument of the paper. Figure 3
  does **not** satisfy EA-Termination (`lemma2_false`), so this does not give Theorem 4.
-/

namespace MinimalSynchronyBC

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- An execution of Figure 4 at the level of its objects. -/
structure Fig4 (P V : Type*) where
  /-- Proposals. -/
  inp : P → V
  /-- `CB[0]`. -/
  cb0 : CBObs P V
  /-- Estimate when starting round `r` (`none`: round `r` not started). -/
  est : P → ℕ → Option V
  /-- Value returned by `EA_propose(r, est)`. -/
  ea : P → ℕ → Option V
  /-- Time of the test of line 5 in round `r`. -/
  t5 : P → ℕ → ℕ
  /-- Value proposed to `AC_OBJECT[r]`. -/
  acIn : P → ℕ → Option V
  /-- Output of `AC_OBJECT[r]`. -/
  ac : P → ℕ → Option (Tag × V)
  /-- RB deliveries of the `DECIDE` messages of round `r`. -/
  D : ℕ → RBTrace P V
  /-- Decision: time and value. -/
  decT : P → Option (ℕ × V)

/-- The `DECIDE` message RB-broadcast by `j` in round `r` (line 7). -/
def Fig4.decBc (C : Fig4 P V) (r : ℕ) (j : P) : Option V :=
  match C.ac j r with
  | some (.commit, v) => some v
  | _ => none

/-- The processes from which `i` RB-delivered `DECIDE(v)` (in some round) by time `τ`. -/
def Fig4.decFrom (C : Fig4 P V) (i : P) (τ : ℕ) (v : V) : Set P :=
  {j | ∃ r, C.D r i τ j = some v}

/-- The rules of Figure 4 for correct processes and the safety specifications of the objects. -/
structure Fig4.Follows (t : ℕ) (B : Finset P) (C : Fig4 P V) : Prop where
  /-- `CB[0]` is a CB-broadcast instance with inputs `inp`. -/
  cb0 : CBSpec t B (fun j => some (C.inp j)) C.cb0
  /-- There is no round 0. -/
  est0 : ∀ {i}, i ∉ B → C.est i 0 = none
  /-- Line 1: round 1 starts with the value returned by `CB[0]`. -/
  est1 : ∀ {i}, i ∉ B → C.est i 1 = (C.cb0.ret i).map Prod.snd
  /-- Line 4 is executed only in started rounds. -/
  ea_est : ∀ {i r v}, i ∉ B → C.ea i r = some v → (C.est i r).isSome
  /-- EA-Validity in every round (the input of round `r` is `est · r`). -/
  ea_valid : ∀ r, EAValidity B (fun j => C.est j r) (fun j => C.ea j r)
  /-- Line 5. -/
  line5 : ∀ {i r u e}, i ∉ B → C.ea i r = some u → C.est i r = some e →
    C.acIn i r = some u ∧ u ∈ C.cb0.valid i (C.t5 i r) ∨
      C.acIn i r = some e ∧ u ∉ C.cb0.valid i (C.t5 i r)
  /-- Line 6 is executed only after line 4. -/
  acIn_none : ∀ {i r}, i ∉ B → C.ea i r = none → C.acIn i r = none
  /-- Every `AC_OBJECT[r]` is an adopt-commit object with inputs `acIn · r`. -/
  ac : ∀ r, ACSpec t B (fun j => C.acIn j r) (fun j => C.ac j r)
  /-- Round `r + 1` starts with the estimate returned by `AC_OBJECT[r]` (`r ≥ 1`). -/
  next : ∀ {i r v}, i ∉ B → 1 ≤ r → C.est i (r + 1) = some v → (C.ac i r).map Prod.snd = some v
  /-- Line 7: the `DECIDE` messages are RB-broadcast. -/
  dec_rb : ∀ r, RBSpec B (C.decBc r) (C.D r)
  /-- Line 9. -/
  line9 : ∀ {i τ v}, i ∉ B → C.decT i = some (τ, v) → t + 1 ≤ (C.decFrom i τ v).ncard

/-- Values that some correct process has in `CB[0].cb_valid` at some time. -/
def Fig4.Good (C : Fig4 P V) (B : Finset P) (u : V) : Prop :=
  ∃ k ∉ B, ∃ τ, u ∈ C.cb0.valid k τ

namespace Fig4

variable {t m : ℕ} {B : Finset P} {C : Fig4 P V}

/-- Estimates and AC inputs of correct processes are `Good` values. -/
theorem good_est (h : C.Follows t B) : ∀ r, (∀ i ∉ B, ∀ e, C.est i r = some e → C.Good B e) ∧
    (∀ i ∉ B, ∀ e, C.acIn i r = some e → C.Good B e) := by
  have hacIn : ∀ r, (∀ i ∉ B, ∀ e, C.est i r = some e → C.Good B e) →
      ∀ i ∉ B, ∀ e, C.acIn i r = some e → C.Good B e := by
    intro r hest i hi e he
    cases hu : C.ea i r with
    | none => rw [h.acIn_none hi hu] at he; exact absurd he (by simp)
    | some u =>
      obtain ⟨e', he'⟩ := Option.isSome_iff_exists.1 (h.ea_est hi hu)
      rcases h.line5 hi hu he' with ⟨h1, hv⟩ | ⟨h1, -⟩ <;> rw [h1] at he <;> cases he
      · exact ⟨i, hi, _, hv⟩
      · exact hest i hi _ he'
  intro r
  induction r with
  | zero => exact ⟨fun i hi e he => by rw [h.est0 hi] at he; exact absurd he (by simp),
      hacIn 0 fun i hi e he => by rw [h.est0 hi] at he; exact absurd he (by simp)⟩
  | succ r ih =>
    have hest : ∀ i ∉ B, ∀ e, C.est i (r + 1) = some e → C.Good B e := by
      intro i hi e he
      rcases Nat.eq_zero_or_pos r with rfl | hr
      · rw [h.est1 hi] at he
        obtain ⟨⟨τ, v⟩, hret, rfl⟩ := Option.map_eq_some_iff.1 he
        exact ⟨i, hi, τ, h.cb0.op_validity hi hret⟩
      · have := h.next hi hr he
        obtain ⟨⟨d, v⟩, hac, rfl⟩ := Option.map_eq_some_iff.1 this
        obtain ⟨j, hj, hxj⟩ := (h.ac r).domain hi hac
        exact ih.2 j hj _ hxj
    exact ⟨hest, hacIn _ hest⟩

/-- `Good` values are proposals of correct processes. -/
theorem Good.inp (h : C.Follows t B) {u : V} (hu : C.Good B u) : ∃ j ∉ B, C.inp j = u := by
  obtain ⟨k, hk, τ, hτ⟩ := hu
  obtain ⟨j, hj, hx⟩ := h.cb0.set_validity hk hτ
  exact ⟨j, hj, Option.some_injective _ hx⟩

/-- A correct process decides a value committed by a correct process. -/
theorem exists_commit (h : C.Follows t B) (hB : B.card ≤ t) {i : P} (hi : i ∉ B) {τ : ℕ}
    {v : V} (hd : C.decT i = some (τ, v)) : ∃ j ∉ B, ∃ r, C.ac j r = some (.commit, v) := by
  have hc := h.line9 hi hd
  -- some sender is correct
  have : ¬ C.decFrom i τ v ⊆ (B : Set P) := by
    intro hsub
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset] at this
    omega
  obtain ⟨j, ⟨r, hr⟩, hj⟩ := Set.not_subset.1 this
  refine ⟨j, hj, r, ?_⟩
  have := (h.dec_rb r).validity hi hj hr
  unfold decBc at this
  split at this
  · rename_i heq; cases this; exact heq
  · exact absurd this (by simp)

/-- **CONS-Validity** (Theorem 4): a decided value was proposed by a correct process. -/
theorem validity (h : C.Follows t B) (hB : B.card ≤ t) {i : P} (hi : i ∉ B) {τ : ℕ} {v : V}
    (hd : C.decT i = some (τ, v)) : ∃ j ∉ B, C.inp j = v := by
  obtain ⟨j, hj, r, hr⟩ := exists_commit h hB hi hd
  obtain ⟨k, hk, hx⟩ := (h.ac r).domain hj hr
  exact Good.inp h ((good_est h r).2 k hk v hx)

/-- After a correct process commits `v` in round `r`, every correct process obtains `v` from
every `AC_OBJECT[s]`, `s ≥ r`. -/
theorem ac_eq_of_commit (h : C.Follows t B) {j : P} (hj : j ∉ B) {r : ℕ} {v : V}
    (hc : C.ac j r = some (.commit, v)) :
    ∀ s, r ≤ s → ∀ k ∉ B, ∀ d w, C.ac k s = some (d, w) → w = v := by
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · obtain ⟨k, hk, hx⟩ := (h.ac 0).domain hj hc
      cases hu : C.ea k 0 with
      | none => rw [h.acIn_none hk hu] at hx; exact absurd hx (by simp)
      | some u =>
        have := h.ea_est hk hu
        rw [h.est0 hk] at this; exact absurd this (by simp)
    · exact hr
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro k hk d w hk'; exact (h.ac r).quasi hj hk hc hk'
  | succ s hs ih =>
    intro k hk d w hk'
    -- all correct estimates of round `s + 1` are `v`
    have hest : ∀ j' ∉ B, C.est j' (s + 1) = none ∨ C.est j' (s + 1) = some v := by
      intro j' hj'
      cases he : C.est j' (s + 1) with
      | none => exact Or.inl rfl
      | some e =>
        right
        have := h.next hj' (by omega) he
        obtain ⟨⟨d', w'⟩, hac, rfl⟩ := Option.map_eq_some_iff.1 this
        rw [ih j' hj' d' w' hac]
    -- hence all correct AC inputs of round `s + 1` are `v`
    have hin : ∀ j' ∉ B, C.acIn j' (s + 1) = none ∨ C.acIn j' (s + 1) = some v := by
      intro j' hj'
      cases hu : C.ea j' (s + 1) with
      | none => exact Or.inl (h.acIn_none hj' hu)
      | some u =>
        right
        have huv := h.ea_valid (s + 1) v hest j' hj' u hu
        obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (h.ea_est hj' hu)
        have hev : e = v := by
          rcases hest j' hj' with h' | h'
          · rw [h'] at he; exact absurd he (by simp)
          · rw [h'] at he; exact (Option.some_injective _ he).symm
        rcases h.line5 hj' hu he with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
        · rw [huv]
        · rw [hev]
    exact ((h.ac (s + 1)).obligation hin hk hk').2

/-- **CONS-Agreement** (Theorem 4): no two correct processes decide different values. -/
theorem agreement (h : C.Follows t B) (hB : B.card ≤ t) {i k : P} (hi : i ∉ B) (hk : k ∉ B)
    {τ τ' : ℕ} {v v' : V} (hd : C.decT i = some (τ, v)) (hd' : C.decT k = some (τ', v')) :
    v = v' := by
  obtain ⟨j, hj, r, hr⟩ := exists_commit h hB hi hd
  obtain ⟨j', hj', r', hr'⟩ := exists_commit h hB hk hd'
  rcases le_total r r' with hle | hle
  · exact (ac_eq_of_commit h hj hr r' hle j' hj' _ _ hr').symm
  · exact ac_eq_of_commit h hj' hr' r hle j hj _ _ hr

/-! ### Termination, assuming an EA object -/

/-- A property that holds from some time on for each member of a finite set holds for all of them
from some common time on (`exists_time_forall` with the arguments of `mono` swapped). -/
theorem _root_.MinimalSynchronyBC.exists_common_time {ι : Type*} (s : Finset ι) {Q : ι → ℕ → Prop}
    (hmono : ∀ j τ τ', τ ≤ τ' → Q j τ → Q j τ') (h : ∀ j ∈ s, ∃ τ, Q j τ) :
    ∃ T, ∀ j ∈ s, Q j T :=
  exists_time_forall s Q (fun j τ τ' h1 h2 => hmono j τ τ' h2 h1) h

/-- The liveness assumptions of Theorem 4's proof: the proposals are `m`-valued with
`n − t > m t`, the EA object satisfies **EA-Termination and EA-Eventual agreement** (Section 5.1),
undecided correct processes go on to the next round, rounds take time, and line 9 fires as soon
as its predicate holds. -/
structure Live (t m : ℕ) (B : Finset P) (C : Fig4 P V) : Prop where
  /-- The correct processes propose at most `m` values. -/
  mvalued : MValued m B (fun j => some (C.inp j))
  /-- `n − t > m t`. -/
  nt : m * t < Fintype.card P - t
  /-- EA-Termination. -/
  ea_term : ∀ r, 1 ≤ r → EATermination B (fun j => C.est j r) (fun j => C.ea j r)
  /-- EA-Eventual agreement. -/
  ea_ev : (∀ i ∉ B, ∀ r, 1 ≤ r → (C.est i r).isSome) → ∀ r₀, ∃ r ≥ r₀, ∃ v,
    (∀ i ∉ B, C.ea i r = some v) ∧ ∃ j ∉ B, C.est j r = some v
  /-- A correct process that never decides starts round `r + 1` after `AC_OBJECT[r]` returns. -/
  cont : ∀ {i r}, i ∉ B → 1 ≤ r → C.decT i = none → (C.ac i r).isSome →
    (C.est i (r + 1)).isSome
  /-- The test of line 5 of round `r` happens at time `≥ r`. -/
  t5_ge : ∀ i r, r ≤ C.t5 i r
  /-- Line 9 fires once its predicate holds. -/
  dec_live : ∀ {i τ v}, i ∉ B → t + 1 ≤ (C.decFrom i τ v).ncard → (C.decT i).isSome

theorem decFrom_mono (h : C.Follows t B) {i : P} {τ τ' : ℕ} (hτ : τ ≤ τ') (v : V) :
    C.decFrom i τ v ⊆ C.decFrom i τ' v := fun _ ⟨r, hr⟩ => ⟨r, (h.dec_rb r).mono hr hτ⟩

/-- If a correct process decides, every correct process decides (RB-Termination-2). -/
theorem decides_of_decides (h : C.Follows t B) (hL : C.Live t m B) {k i : P} (hk : k ∉ B)
    (hi : i ∉ B) {τ : ℕ} {v : V} (hd : C.decT k = some (τ, v)) : (C.decT i).isSome := by
  classical
  have hc := h.line9 hk hd
  have hfin : (C.decFrom k τ v).Finite := Set.toFinite _
  obtain ⟨T, hT⟩ := exists_common_time hfin.toFinset (Q := fun j T => j ∈ C.decFrom i T v)
    (fun j τ τ' hle hj => decFrom_mono h hle v hj) (fun j hj => by
      obtain ⟨r, hr⟩ := (Set.Finite.mem_toFinset _).1 hj
      obtain ⟨τ', hτ'⟩ := (h.dec_rb r).term2 hk hi hr
      exact ⟨τ', r, hτ'⟩)
  refine hL.dec_live (τ := T) (v := v) hi (hc.trans (Set.ncard_le_ncard (fun j hj => ?_) (Set.toFinite _)))
  exact hT j ((Set.Finite.mem_toFinset _).2 hj)

/-- `acIn · r` is `m`-valued and feasible. -/
theorem feasible_acIn (h : C.Follows t B) (hL : C.Live t m B) (hB : B.card ≤ t) (r : ℕ)
    (hall : ∀ j ∉ B, (C.acIn j r).isSome) : Feasible t B (fun j => C.acIn j r) := by
  obtain ⟨S, hS, hSv⟩ := hL.mvalued
  refine feasible_of_mValued hB hall ⟨S, hS, fun j hj u hu => ?_⟩ hL.nt
  obtain ⟨k, hk, rfl⟩ := Good.inp h ((good_est h r).2 j hj u hu)
  exact hSv k hk _ rfl

/-- **CONS-Termination** (Theorem 4), *assuming* EA-Termination and EA-Eventual agreement
(`Live`): every correct process decides. This is the paper's composition argument; the EA
object of Figure 3 does not satisfy EA-Termination (`lemma2_false`). -/
theorem termination (h : C.Follows t B) (hL : C.Live t m B) (hn : 3 * t < Fintype.card P)
    (hB : B.card ≤ t) : ∀ i ∉ B, (C.decT i).isSome := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨i₀, hi₀, hnd⟩ := hcon
  -- nobody decides
  have hnone : ∀ i ∉ B, C.decT i = none := by
    intro i hi
    cases hd : C.decT i with
    | none => rfl
    | some d =>
      obtain ⟨τ, v⟩ := d
      exact absurd (decides_of_decides h hL hi hi₀ hd) (by simpa using hnd)
  have hcorr : (univ \ B).card ≥ Fintype.card P - t := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]; omega
  -- feasibility of `CB[0]`
  have hfeas0 : Feasible t B (fun j => some (C.inp j)) :=
    feasible_of_mValued hB (fun _ _ => rfl) hL.mvalued hL.nt
  -- AC objects terminate in rounds started by everybody
  have hac : ∀ r, 1 ≤ r → (∀ i ∉ B, (C.est i r).isSome) → ∀ i ∉ B, (C.ac i r).isSome := by
    intro r hr hest
    have hea := hL.ea_term r hr hest
    have hin : ∀ j ∉ B, (C.acIn j r).isSome := by
      intro j hj
      obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 (hea j hj)
      obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (hest j hj)
      rcases h.line5 hj hu he with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
    exact (h.ac r).termination hin (feasible_acIn h hL hB r hin)
  -- every correct process starts every round
  have hstart : ∀ i ∉ B, ∀ r, 1 ≤ r → (C.est i r).isSome := by
    intro i hi r hr
    induction r, hr using Nat.le_induction generalizing i with
    | base =>
      rw [h.est1 hi]
      simpa using h.cb0.op_termination (fun _ _ => rfl) hfeas0 i hi
    | succ r hr ih => exact hL.cont hi hr (hnone i hi) (hac r hr ih i hi)
  -- `CB[0]` eventually contains every good value at every correct process
  obtain ⟨T, hT⟩ := exists_common_time ((univ \ B) ×ˢ ((univ \ B).image C.inp))
    (Q := fun p τ => C.Good B p.2 → p.2 ∈ C.cb0.valid p.1 τ)
    (fun p τ τ' hle hp hg => h.cb0.mono hle (hp hg)) (fun p hp => by
      by_cases hg : C.Good B p.2
      · obtain ⟨k, hk, τ, hτ⟩ := hg
        have hp1 : p.1 ∉ B := by simpa using (mem_product.1 hp).1
        obtain ⟨T', hT'⟩ := h.cb0.set_agreement hk hp1
        refine ⟨max τ T', fun _ => ?_⟩
        rw [← hT' _ (le_max_right _ _)]
        exact h.cb0.mono (le_max_left _ _) hτ
      · exact ⟨0, fun hg' => absurd hg' hg⟩)
  obtain ⟨r, hrT, v, hea, j, hj, hjv⟩ := hL.ea_ev hstart (max T 1)
  have hgood : C.Good B v := (good_est h r).1 j hj v hjv
  have hvalid : ∀ i ∉ B, v ∈ C.cb0.valid i (C.t5 i r) := by
    intro i hi
    obtain ⟨k, hk, hkv⟩ := Good.inp h hgood
    have := hT (i, v) (mem_product.2 ⟨by simpa using hi, mem_image.2 ⟨k, by simpa using hk, hkv⟩⟩)
      hgood
    exact h.cb0.mono (le_trans (le_max_left _ _) (le_trans hrT (hL.t5_ge i r))) this
  have hin : ∀ i ∉ B, C.acIn i r = some v := by
    intro i hi
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.1 (hstart i hi r (by omega))
    rcases h.line5 hi (hea i hi) he with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact h1
    · exact absurd (hvalid i hi) h2
  have hcommit : ∀ i ∉ B, C.ac i r = some (.commit, v) := by
    intro i hi
    obtain ⟨⟨d, w⟩, hdw⟩ := Option.isSome_iff_exists.1
      (hac r (by omega) (fun i hi => hstart i hi r (by omega)) i hi)
    obtain ⟨rfl, rfl⟩ := (h.ac r).obligation (v := v) (fun j hj => Or.inr (hin j hj)) hi hdw
    exact hdw
  -- all correct processes RB-deliver `DECIDE(v)` from all correct processes
  obtain ⟨T', hT'⟩ := exists_common_time (univ \ B) (Q := fun j τ => C.D r i₀ τ j = some v)
    (fun j τ τ' hle hj => (h.dec_rb r).mono hj hle) (fun j hj => by
      have hj' : j ∉ B := by simpa using hj
      exact (h.dec_rb r).term1 hi₀ hj' (by simp [decBc, hcommit j hj']))
  have hsub : ((univ \ B : Finset P) : Set P) ⊆ C.decFrom i₀ T' v := fun j hj => ⟨r, hT' j hj⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset] at this
  have hdec := hL.dec_live (τ := T') (v := v) hi₀ (by omega)
  rw [hnone i₀ hi₀] at hdec
  exact absurd hdec (by simp)

end Fig4

end MinimalSynchronyBC
