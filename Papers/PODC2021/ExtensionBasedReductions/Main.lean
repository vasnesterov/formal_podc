import Papers.PODC2021.ExtensionBasedReductions.Theorem1
import Podc.Computability.Distributed.NIS.ISConversion

/-!
# Theorem 1 of Brusse–Ellen (PODC 2021), for reductions with local post-processing

*If task `T` reduces to task `S`, and there is an augmented extension-based proof of the impossibility
of solving `T` in the NIS model, then there is an augmented extension-based proof of the impossibility
of solving `S` in the NIS model.*

We prove it for reductions `(R₁, R₂)` in the sense of the paper (Section 3) in which `R₂` can be solved
without communication (each process applies a function `h` to its own output of `S`); `R₁` is an
arbitrary task solvable in the NIS model. The general case needs the composition `A₂ ∘ (A ∘ A₁)` of
Section 6 (estimate vectors), which we do not formalize.
-/

namespace Podc.ExtensionBasedReductions

open Cslib.NIS

open St

variable {P XT M ZS ZT : Type} [DecidableEq P] [Fintype P] [Inhabited XT] [Inhabited M] [Finite ZS]

section Local
variable {δ1 : Protocol P XT M} {t : ℕ} (hIS : IsIS δ1 t) (ht : 0 < t) (hw : WaitFree δ1)
  (post : P → ZS → ZT)

/-- The simulation data of Theorem 1. -/
noncomputable def thm1Sim (δA : Protocol P M ZS) (σT : Prover P XT ZT (YQ P ZT) (Option (List P))) :
    SimData (assignSpec (P := P)) (assignSpec (P := P)) (compP δ1 t δA post) δA where
  σ := σT
  H := handler δ1 t post
  I := SimInv δ1 t δA post
  init := simInv_init
  step := by
    intro hs ht0 m w r hI hleg hr hv
    cases m with
    | query C q =>
      by_cases hq : (decided δ1 (trunc t C q)).isSome
      · simp only [handler, if_pos hq] at hr
        obtain ⟨h1, h2, h3, -⟩ := step_queryA hIS ht hw hI hleg hq hr hv
        exact ⟨h1, h2, h3⟩
      · simp only [handler, if_neg hq] at hr
        exact step_queryA1 hIS ht hw hI hleg hq hr hv
    | oracle C o =>
      simp only [handler] at hr
      exact step_oracle hIS ht hw hI hleg hr hv
    | endPhase C =>
      obtain ⟨h1, h2, h3, -⟩ := step_end hIS ht hw hI hleg hr hv
      exact ⟨h1, h2, h3⟩

omit [DecidableEq P] [Fintype P] [Inhabited XT] [Inhabited M] [Finite ZS] in
/-- A monotone bounded sequence increases only finitely often. -/
lemma eventually_not_of_bounded (Φ : ℕ → ℕ) (K B : ℕ) (E : ℕ → Prop)
    (hmono : ∀ k ≥ K, Φ k ≤ Φ (k + 1)) (hinc : ∀ k ≥ K, E k → Φ k < Φ (k + 1))
    (hb : ∀ k ≥ K, Φ k ≤ B) : ∃ K' ≥ K, ∀ k ≥ K', ¬ E k := by
  by_contra hne
  push_neg at hne
  have hgrow : ∀ n, ∃ k ≥ K, Φ K + n ≤ Φ k := by
    intro n
    induction n with
    | zero => exact ⟨K, le_rfl, le_rfl⟩
    | succ n ih =>
      obtain ⟨k, hk, hΦ⟩ := ih
      obtain ⟨k', hk', hE⟩ := hne k hk
      have hm : ∀ i, Φ k ≤ Φ (k + i) := fun i => by
        induction i with
        | zero => rfl
        | succ i ihi => exact ihi.trans (hmono _ (by omega))
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hk'
      exact ⟨k + i + 1, by omega, by have := hinc (k + i) (by omega) hE; have := hm i; omega⟩
  obtain ⟨k, hk, hΦ⟩ := hgrow (B + 1)
  have := hb k hk; omega

omit [DecidableEq P] [Fintype P] [Inhabited XT] [Inhabited M] [Finite ZS] in
lemma window_single {α : Type} (pl : ℕ → α) {a b : ℕ} (hab : a < b) {e : α}
    (h : window pl a b = [e]) : b = a + 1 ∧ pl a = e := by
  have hl := congrArg List.length h
  simp [window] at hl
  refine ⟨by omega, ?_⟩
  rw [window_cons pl hab] at h
  simp at h; exact h.1

include hIS ht hw

/-- **Theorem 1** (local post-processing version): let `A₁` (an IS protocol in normal form)
solve `R₁`, and suppose that for every input vector `x` of `T`, every output vector `u ∈ R₁(x)`
is an input vector of `S` and every `w ∈ S(u)` gives a valid output vector `h ∘ w ∈ T(x)`.
If `T` has an augmented extension-based impossibility proof, so does `S`. -/
theorem theorem1_local {T : Task P XT ZT} {S : Task P M ZS} {R1 : Task P XT M}
    (hR1 : Solves δ1 R1)
    (hred : ∀ x ∈ T.inputs, x ∈ R1.inputs ∧ ∀ u ∈ R1.spec x, u ∈ S.inputs ∧
      ∀ w ∈ S.spec u, (fun j => post j (w j)) ∈ T.spec x)
    (hT : HasAugEBProof T) : HasAugEBProof S := by
  obtain ⟨σT, hσT⟩ := hT
  refine ⟨proverS δ1 t post σT, fun δA pl hc hv => ?_⟩
  set D := thm1Sim hIS ht hw post δA σT
  obtain ⟨ps, a, ha0, hamono, hwin, hleg, hI, hrun⟩ :=
    D.transfer assignSpec_total T (hσT (compP δ1 t δA post)) pl hc hv
  have hamono' : StrictMono a := strictMono_nat_of_lt_succ hamono
  have hst : ∀ j, statesOf (hist ps j) = states ps j := fun j => (states_eq_statesOf ps j).symm
  have hstA : ∀ j, statesOf (hist pl (a j)) = states pl (a j) := fun j =>
    (states_eq_statesOf pl (a j)).symm
  have hwv : ∀ j, ∀ e ∈ window pl (a j) (a (j + 1)), ValidResp (assignSpec (P := P)) δA e.1 e.2 := by
    intro j e he
    simp only [window, List.mem_map, List.mem_range'] at he
    obtain ⟨i, -, rfl⟩ := he
    exact hv i
  have hlegS : ∀ j, Legal (assignSpec (P := P)) (compP δ1 t δA post) (statesOf (hist ps j)) (ps j).1 :=
    fun j => by rw [hst]; exact hwin.1 j
  refine ⟨hleg, ?_⟩
  rcases hwin.2 with ⟨k, C, hC, hvi⟩ | hinf | ⟨K, hK⟩
  · ---------------- (W1) a violation of `T` gives a violation of `S`
    left
    have hI' := hI k
    rw [← hst] at hC
    have hRC := hI'.ginvY.reach hC
    refine ⟨a k, toA δ1 t C, by rw [← hstA]; exact hI'.reach C hC, ?_⟩
    obtain ⟨hxT, hno⟩ := hvi
    obtain ⟨hx1, hu⟩ := hred _ hxT
    have hum := ucan_mem hIS ht hw hR1 hRC hx1
    obtain ⟨huS, hw'⟩ := hu _ hum
    rw [Violates, inputs_toA hIS ht hw hRC]
    refine ⟨huS, fun ⟨y, hy, hyo⟩ => hno ⟨fun j => post j (y j), hw' y hy, fun q z hq => ?_⟩⟩
    rw [outs_toA hIS ht hw hRC] at hq
    cases ho : outs δA (toA δ1 t C) q with
    | none => rw [ho] at hq; cases hq
    | some w => rw [ho] at hq; cases hq; simp [hyo q w ho]
  · ---------------- (W2) infinitely many phases
    right; left
    by_contra hfin
    push_neg at hfin
    obtain ⟨N0, hN0⟩ := hfin
    -- the base of `𝒫`'s phase stays constant from `N0` on
    have hbase : ∀ k ≥ N0, (states pl k).base = (states pl N0).base := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => rfl
      | succ k hk ih =>
        rw [← ih]
        show ((states pl k).next (pl k).1).base = _
        cases hm : (pl k).1 with
        | query C q => rfl
        | oracle C o => rfl
        | endPhase C => exact absurd ⟨C, hm⟩ (hN0 k hk)
    set B := (states pl N0).base
    have hJ : N0 ≤ a N0 := hamono'.le_apply
    -- every phase end of `𝒫_T` from `N0` on is at a configuration whose `A`-part is in the start set
    have hend : ∀ j ≥ N0, ∀ C, (ps j).1 = .endPhase C → ∃ u, toA δ1 t C = reinit B u := by
      intro j hj C hC
      have hr := hrun j
      rw [hC] at hr
      have := step_end hIS ht hw (hI j) (by rw [← hC]; exact hlegS j) hr (hwv j)
      rcases this.2.2.2 with ⟨-, r', hw1⟩ | ⟨⟨u, hu⟩, -⟩
      · obtain ⟨-, hpl⟩ := window_single pl (hamono j) hw1
        exact absurd ⟨toA δ1 t C, by rw [hpl]⟩ (hN0 (a j) (le_trans hJ (hamono'.monotone hj)))
      · rw [hstA, hbase _ (le_trans hJ (hamono'.monotone hj))] at hu
        exact ⟨u, hu⟩
    -- first phase end of `𝒫_T` at or after `N0`
    obtain ⟨J, hJN, C0, hC0⟩ := hinf N0
    -- the potential: the `A₁`-part of the base of `𝒫_T`'s phase
    let Φ : ℕ → ℕ := fun k => ∑ j, (trunc t (states ps k).base j).depth
    have hreachB : ∀ k, Reach (compP δ1 t δA post) (states ps k).base := fun k =>
      (ginv_states hwin.1 k).1
    have hbaseA : ∀ k ≥ J + 1, totalDepth (toA δ1 t (states ps k).base) = totalDepth B := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base =>
        show totalDepth (toA δ1 t ((states ps J).next (ps J).1).base) = _
        rw [hC0]; obtain ⟨u, hu⟩ := hend J hJN C0 hC0
        simp only [GState.next]; rw [hu, measure_reinit]
      | succ k hk ih =>
        show totalDepth (toA δ1 t ((states ps k).next (ps k).1).base) = _
        cases hm : (ps k).1 with
        | query C q => exact ih
        | oracle C o => exact ih
        | endPhase C =>
          obtain ⟨u, hu⟩ := hend k (by omega) C hm
          simp only [GState.next]; rw [hu, measure_reinit]
    obtain ⟨K', -, hK'⟩ := eventually_not_of_bounded Φ (J + 1) (Fintype.card P * (2 * t))
      (fun k => IsEnd (ps k).1)
      (fun k hk => by
        show ∑ j, (trunc t (states ps k).base j).depth ≤
          ∑ j, (trunc t ((states ps k).next (ps k).1).base j).depth
        cases hm : (ps k).1 with
        | query C q => exact le_rfl
        | oracle C o => exact le_rfl
        | endPhase C =>
          simp only [GState.next]
          have hCr : C ∈ (states ps k).resp := by have := hwin.1 k; rw [hm] at this; exact this
          have hlt := measure_lt_of_mem_resp (ginv_states hwin.1 k) hCr
          have h1 := measure_split hIS ht hw (hreachB k)
          have h2 := measure_split hIS ht hw ((ginv_states hwin.1 k).reach (Or.inr hCr))
          obtain ⟨u, hu⟩ := hend k (by omega) C hm
          rw [h1.1, hbaseA k hk] at hlt
          rw [h2.1, hu, measure_reinit] at hlt
          omega)
      (fun k hk ⟨C, hm⟩ => by
        show ∑ j, (trunc t (states ps k).base j).depth <
          ∑ j, (trunc t ((states ps k).next (ps k).1).base j).depth
        rw [hm]; simp only [GState.next]
        have hCr : C ∈ (states ps k).resp := by have := hwin.1 k; rw [hm] at this; exact this
        have hlt := measure_lt_of_mem_resp (ginv_states hwin.1 k) hCr
        have h1 := measure_split hIS ht hw (hreachB k)
        have h2 := measure_split hIS ht hw ((ginv_states hwin.1 k).reach (Or.inr hCr))
        obtain ⟨u, hu⟩ := hend k (by omega) C hm
        rw [h1.1, hbaseA k hk] at hlt
        rw [h2.1, hu, measure_reinit] at hlt
        omega)
      (fun k _ => by
        calc Φ k ≤ ∑ _j : P, 2 * t :=
              Finset.sum_le_sum fun j _ => (measure_split hIS ht hw (hreachB k)).2 j
          _ = Fintype.card P * (2 * t) := by simp)
    obtain ⟨k, hk, hE⟩ := hinf K'
    exact hK' k hk hE
  · ---------------- (W3) an infinite chain of queries
    right; right
    -- the configurations of the chain
    have hq : ∀ k ≥ K, ∃ C q, (ps k).1 = .query C q := fun k hk => by
      obtain ⟨C, q, _, h1, _⟩ := hK k hk; exact ⟨C, q, h1⟩
    obtain ⟨C0, q0, -⟩ := hq K le_rfl
    haveI : Nonempty (Config P XT) := ⟨C0⟩
    haveI : Nonempty P := ⟨q0⟩
    choose! Cf qf hCq using hq
    have hlink : ∀ k ≥ K, Cf (k + 1) = step (Cf k) (qf k) := by
      intro k hk
      obtain ⟨C, q, q', h1, h2⟩ := hK k hk
      rw [hCq k hk] at h1
      obtain ⟨rfl, rfl⟩ := Move.query.inj h1
      rw [hCq (k + 1) (by omega)] at h2
      exact (Move.query.inj h2).1
    have hreach : ∀ k ≥ K, Reach (compP δ1 t δA post) (Cf k) := fun k hk => by
      have := hwin.1 k; rw [hCq k hk] at this
      exact (ginv_states hwin.1 k).reach this.1
    have hactive : ∀ k ≥ K, Active (compP δ1 t δA post) (Cf k) (qf k) := fun k hk => by
      have := hwin.1 k; rw [hCq k hk] at this; exact this.2
    let Ψ : ℕ → ℕ := fun k => ∑ j, (trunc t (Cf k) j).depth
    have hstepΨ : ∀ k ≥ K, (decided δ1 (trunc t (Cf k) (qf k))).isSome → Ψ (k + 1) = Ψ k := by
      intro k hk hqk
      show ∑ j, (trunc t (Cf (k + 1)) j).depth = _
      rw [hlink k hk, (toA_stepA hIS ht hw (hreach k hk) hqk).2.2]
    have hstepΨ1 : ∀ k ≥ K, ¬ (decided δ1 (trunc t (Cf k) (qf k))).isSome → Ψ (k + 1) = Ψ k + 1 := by
      intro k hk hqk
      have hq' : decided δ1 (trunc t (Cf k) (qf k)) = none := by simpa using hqk
      obtain ⟨-, htr, -⟩ := toA_execA1 (δA := δA) (post := post) hIS ht hw (hreach k hk)
        (μ := [qf k]) ⟨hq', trivial⟩
      show ∑ j, (trunc t (Cf (k + 1)) j).depth = _
      rw [hlink k hk]; simp only [exec_cons, exec_nil] at htr; rw [htr]
      exact measure_step _ _
    obtain ⟨K', hKK', hK'⟩ := eventually_not_of_bounded Ψ K (Fintype.card P * (2 * t))
      (fun k => ¬ (decided δ1 (trunc t (Cf k) (qf k))).isSome)
      (fun k hk => by
        by_cases h : (decided δ1 (trunc t (Cf k) (qf k))).isSome
        · rw [hstepΨ k hk h]
        · rw [hstepΨ1 k hk h]; omega)
      (fun k hk h => by rw [hstepΨ1 k hk h]; omega)
      (fun k hk => by
        calc Ψ k ≤ ∑ _j : P, 2 * t :=
              Finset.sum_le_sum fun j _ => (measure_split hIS ht hw (hreach k hk)).2 j
          _ = Fintype.card P * (2 * t) := by simp)
    -- from `K'` on, every window is the single query `(toA C, q)`
    have hwin1 : ∀ k ≥ K', a (k + 1) = a k + 1 ∧ (pl (a k)).1 = .query (toA δ1 t (Cf k)) (qf k) := by
      intro k hk
      have hqk : (decided δ1 (trunc t (Cf k) (qf k))).isSome := by
        exact not_not.1 (hK' k hk)
      have hr := hrun k
      rw [hCq k (by omega)] at hr
      simp only [D, thm1Sim, handler, if_pos hqk] at hr
      have hl := hlegS k
      rw [hCq k (by omega)] at hl
      obtain ⟨-, -, -, hw1⟩ := step_queryA hIS ht hw (hI k) hl hqk hr (hwv k)
      obtain ⟨h1, h2⟩ := window_single pl (hamono k) hw1
      exact ⟨h1, by rw [h2]⟩
    have hlin : ∀ i, a (K' + i) = a K' + i := fun i => by
      induction i with
      | zero => rfl
      | succ i ih => rw [← add_assoc, (hwin1 _ (by omega)).1, ih]; ring
    refine ⟨a K', fun s hs => ?_⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hs
    have h1 := (hwin1 (K' + i) (by omega)).2
    have h2 := (hwin1 (K' + i + 1) (by omega)).2
    rw [hlin] at h1
    rw [show K' + i + 1 = K' + (i + 1) by ring, hlin] at h2
    have hqk : (decided δ1 (trunc t (Cf (K' + i)) (qf (K' + i)))).isSome := by
      exact not_not.1 (hK' (K' + i) (by omega))
    rw [show K' + (i + 1) = K' + i + 1 by ring, hlink _ (by omega),
      (toA_stepA hIS ht hw (hreach _ (by omega)) hqk).1] at h2
    exact ⟨_, _, _, h1, by rw [show a K' + i + 1 = a K' + (i + 1) by ring]; exact h2⟩

end Local

/-! ## The paper's notion of reduction -/

/-- `(R₁, R₂)` is a reduction from `T` to `S` (Section 3): `R₁` and `R₂` are solvable in the NIS model
and `R₂ ∘ S ∘ R₁ (x) ⊆ T(x)` for every input vector `x` of `T`. We also record that the composition is
well formed (outputs of each task are inputs of the next one, and inputs of `T` are inputs of `R₁`). -/
structure IsReduction {X Y M' W : Type} (T : Task P X Y) (S : Task P M' W) (R1 : Task P X M')
    (R2 : Task P W Y) : Prop where
  solv1 : ∃ δ : Protocol P X M', Solves δ R1
  solv2 : ∃ δ : Protocol P W Y, Solves δ R2
  sub : ∀ x ∈ T.inputs, (R2.comp (S.comp R1)).spec x ⊆ T.spec x
  wf_in : T.inputs ⊆ R1.inputs
  wf1 : ∀ x ∈ R1.inputs, R1.spec x ⊆ S.inputs
  wf2 : ∀ u ∈ S.inputs, S.spec u ⊆ R2.inputs

/-- `R₂` is solved without communication: each process applies `h` to its own input. -/
def LocallySolvable {W Y : Type} (R2 : Task P W Y) (h : P → W → Y) : Prop :=
  ∀ w ∈ R2.inputs, (fun j => h j (w j)) ∈ R2.spec w

/-- **Theorem 1** of the paper, for reductions `(R₁, R₂)` whose second task `R₂` is solvable without
communication (e.g. `R₂` = the identity task, or any local relabelling of the outputs of `S`). -/
theorem theorem1 [Finite XT] {T : Task P XT ZT} {S : Task P M ZS} {R1 : Task P XT M}
    {R2 : Task P ZS ZT} (hred : IsReduction T S R1 R2) {h : P → ZS → ZT}
    (hloc : LocallySolvable R2 h) (hT : HasAugEBProof T) : HasAugEBProof S := by
  obtain ⟨δ0, hδ0⟩ := hred.solv1
  obtain ⟨δ1, t, ht, hIS, hR1⟩ := exists_isIS_of_solves hδ0
  refine theorem1_local hIS ht hR1.1 h hR1 (fun x hx => ⟨hred.wf_in hx, fun u hu => ?_⟩) hT
  have huS := hred.wf1 x (hred.wf_in hx) hu
  refine ⟨huS, fun w hw => hred.sub x hx ?_⟩
  exact ⟨w, ⟨u, hu, hw⟩, hloc w (hred.wf2 u huS hw)⟩

/-- Contrapositive form used in the paper's conclusion: if `T` reduces to `S` (with `R₂` local) and
there is no augmented extension-based proof for `S`, there is none for `T`. -/
theorem no_augEBProof_of_reduction [Finite XT] {T : Task P XT ZT} {S : Task P M ZS}
    {R1 : Task P XT M} {R2 : Task P ZS ZT} (hred : IsReduction T S R1 R2) {h : P → ZS → ZT}
    (hloc : LocallySolvable R2 h) (hS : ¬ HasAugEBProof S) : ¬ HasAugEBProof T :=
  fun hT => hS (theorem1 hred hloc hT)

end Podc.ExtensionBasedReductions
