import Papers.PODC2021.ThinUnison.Main
import Podc.Stabilization.Daemon

/-!
# Corollary 1.2 of [EK21]: a self-stabilizing synchronizer (Section 4)

Emek, Keren. *A Thin Self-Stabilizing Asynchronous Unison Algorithm with Applications to Fault
Tolerant Biological Networks*, PODC 2021 ([EK21]), Section 4.

Given a (deterministic) synchronous SA algorithm `Π` with state set `Q`, the synchronizer `Π*`
has state set `Q × Q × Turn k`: a state `(q, q', ν)` consists of the current simulated `Π`-state
`q`, the previous simulated `Π`-state `q'` and an AlgAU turn `ν`. Every node runs AlgAU on the
third coordinate; when AlgAU performs an AA transition (the only transitions that advance the
clock, from the able turn `ν` to the able turn `ν' = φ(ν)‾`), the node moves from `(q, q', ν)` to
`(p, q, ν')`, where `p = δ_Π(q, S)` and `S` is the *simulated signal*: the set of `r` such that the
node senses some `Π*`-state `(r, ·, ν)` or `(·, r, ν')`. Otherwise the first two coordinates are
kept. The output of `(q, q', ν)` is `ω(q)` if `ν` is able (and `q` is an output state of `Π`).
The state space has `|Q|² (4k - 2) = O(D |Q|²)` states.

## Main results

* `synchronizer`, `synchOutput`: the construction.
* `synchronizer_isRun_auPart`: the third coordinate of an execution of `Π*` is an execution of
  AlgAU.
* `allGood_stab`: the configuration of AlgAU is good from time `R(N(D))` on (extracted from the
  proof of Theorem 1.1).
* `corollary_1_2_general`, `corollary_1_2`: **Corollary 1.2 of [EK21]** for deterministic `Π` and
  *static* tasks (outputs eventually constant): if `Π` synchronously stabilizes within `f` rounds,
  then `Π*` stabilizes under every fair schedule within `N(D) + D + f` rounds, to an output vector
  that `Π` would also produce.

## Proof

After `T = R(N(D))` the AlgAU component is good forever. We lift the clocks to integers
(`uclk`, see `Good.lean`): `U_v(t)` changes exactly at the AA steps of `v`, neighbours differ by at
most one, and `pos(λ_v(t)) ≡ B + U_v(t) (mod 2k)`. Let `j₀ = max_v U_v(T)`. For `j ≥ j₀` let
`X(v, j)` be the first coordinate of `v` while `U_v = j` (`simState`). When `v` advances from `j`
to `j + 1`, every node of `N⁺(v)` has `U ∈ {j, j + 1}`; a node with `U = j` has turn `ν` and first
coordinate `X(u, j)`, a node with `U = j + 1` has turn `φ(ν)‾` and second coordinate `X(u, j)`.
Hence the simulated signal is exactly the `Π`-signal of `v` under `X(·, j)`, and
`X(·, j + 1)` is one synchronous step of `Π` from `X(·, j)` (`simState_succ`).
-/

namespace ThinUnison

open Cslib.StoneAge

variable {V Q : Type*}

/-! ## The construction -/

/-- The simulated `Π`-signal of a node in turn `ν` sensing the set `S` of `Π*`-states (Section 4
of [EK21]): all `r` such that some state `(r, ·, ν)` or `(·, r, φ(ν)‾)` is sensed. -/
def simSignal {k : ℕ} (ν : Turn k) (S : Set (Q × Q × Turn k)) : Set Q :=
  {r | ∃ x ∈ S, (x.1 = r ∧ x.2.2 = ν) ∨ (x.2.1 = r ∧ x.2.2 = ν.aa)}

open Classical in
/-- The synchronizer `Π*` of Section 4 of [EK21] applied to a deterministic SA algorithm `Π`,
with AlgAU parameter `k`. A state `(q, q', ν)`: current simulated state, previous simulated
state, AlgAU turn. If AlgAU performs an AA transition (`ν` able and the AA condition holds for the
sensed turns), the node moves to `(δ_Π(q, S), q, φ(ν)‾)` with `S` the simulated signal; otherwise
it keeps `q, q'` and applies AlgAU's transition function to `ν`. -/
noncomputable def synchronizer (P : Algorithm Q) (k : ℕ) : Algorithm (Q × Q × Turn k) where
  δ s S :=
    if s.2.2.faulty = false ∧ AACond s.2.2 ((fun x => x.2.2) '' S) then
      (P.δ s.1 (simSignal s.2.2 S), s.1, s.2.2.aa)
    else (s.1, s.2.1, δ k s.2.2 ((fun x => x.2.2) '' S))

/-- The output of the synchronizer: `ω(q)` for a state `(q, q', ν)` with `ν` able (`none` encodes
non-output states). -/
def synchOutput {O : Type*} {k : ℕ} (ω : Q → Option O) (s : Q × Q × Turn k) : Option O :=
  if s.2.2.faulty then none else ω s.1

/-- The AlgAU component of a `Π*`-execution. -/
def auPart {k : ℕ} (C : ℕ → V → Q × Q × Turn k) : ℕ → V → Turn k := fun t v => (C t v).2.2

/-- The third coordinate of `Π*` follows AlgAU. -/
theorem synchronizer_δ_snd_snd (P : Algorithm Q) (k : ℕ) (s : Q × Q × Turn k)
    (S : Set (Q × Q × Turn k)) :
    ((synchronizer P k).δ s S).2.2 = δ k s.2.2 ((fun x => x.2.2) '' S) := by
  unfold synchronizer
  dsimp only
  split_ifs with h
  · unfold δ; simp [h.1, h.2]
  · rfl

theorem signal_map (G : SimpleGraph V) {R : Type*} (f : Q → R) (C : V → Q) (v : V) :
    signal G (fun w => f (C w)) v = f '' signal G C v := by
  ext r
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨C u, ⟨u, hu, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, rfl⟩

theorem fwd_ne {k : ℕ} {ℓ : ℤ} (h : IsLevel k ℓ) : fwd k ℓ ≠ ℓ := by lvl_omega

section Run

variable {G : SimpleGraph V} {P : Algorithm Q} {k : ℕ} {A : ℕ → Set V}
  {C : ℕ → V → Q × Q × Turn k}

/-- The AlgAU component of an execution of `Π*` is an execution of AlgAU. -/
theorem synchronizer_isRun_auPart (hC : IsRun G (synchronizer P k) A C) :
    AURun G A (auPart C) := by
  refine ⟨fun t => funext fun v => ?_⟩
  classical
  by_cases hv : v ∈ A t
  · simp only [step, hv, ite_true]
    show (C (t + 1) v).2.2 = _
    rw [hC.succ_of_mem hv, synchronizer_δ_snd_snd,
      ← signal_map G (fun x : Q × Q × Turn k => x.2.2) (C t) v]
    rfl
  · simp only [step, hv, ite_false]
    show (C (t + 1) v).2.2 = _
    rw [hC.succ_of_not_mem hv]; rfl

/-- If the AlgAU component does not change, the whole `Π*`-state does not change. -/
theorem eq_of_auPart_eq (hC : IsRun G (synchronizer P k) A C) {t : ℕ} {v : V}
    (h : auPart C (t + 1) v = auPart C t v) : C (t + 1) v = C t v := by
  by_cases hv : v ∈ A t
  · simp only [auPart] at h
    rw [hC.succ_of_mem hv] at h ⊢
    unfold synchronizer at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h'
    · exact absurd (congrArg Turn.lvl h) (fwd_ne (C t v).2.2.isLevel)
    · exact Prod.ext rfl (Prod.ext rfl h)
  · exact hC.succ_of_not_mem hv

/-- An AA transition of AlgAU performs one simulated step of `Π`. -/
theorem succ_of_aa (hC : IsRun G (synchronizer P k) A C) {t : ℕ} {v : V} (hv : v ∈ A t)
    (hf : (C t v).2.2.faulty = false) (h : AAN G (auPart C) t v) :
    C (t + 1) v = (P.δ (C t v).1 (simSignal (C t v).2.2 (signal G (C t) v)), (C t v).1,
      (C t v).2.2.aa) := by
  have h' : AACond (C t v).2.2 ((fun x => x.2.2) '' signal G (C t) v) := by
    rw [← signal_map G (fun x : Q × Q × Turn k => x.2.2) (C t) v]
    exact aaCond_signal_iff.2 ⟨hf, h⟩
  rw [hC.succ_of_mem hv]
  unfold synchronizer
  dsimp only
  simp only [hf, h', and_self, ite_true]

end Run

/-! ## Auxiliary facts -/

/-- Discrete intermediate value theorem: a sequence that increases by at most one per step
crosses every intermediate value by a `+1` step. -/
theorem exists_step_eq {f : ℕ → ℤ} {a b : ℕ} (hf : ∀ s, a ≤ s → f (s + 1) ≤ f s + 1) {j : ℤ}
    (ha : f a ≤ j) (hb : j < f b) (hab : a ≤ b) :
    ∃ s, a ≤ s ∧ s < b ∧ f s = j ∧ f (s + 1) = j + 1 := by
  induction b, hab using Nat.le_induction with
  | base => omega
  | succ n hn ih =>
    by_cases h : j < f n
    · obtain ⟨s, h1, h2, h3, h4⟩ := ih h; exact ⟨s, h1, by omega, h3, h4⟩
    · have := hf n hn; exact ⟨n, hn, by omega, by omega, by omega⟩

theorem uclk_succ_cases {k : ℕ} {C : ℕ → V → Turn k} (o : V → ℤ) {T s : ℕ} (v : V)
    (hs : T ≤ s) :
    uclk C o T (s + 1) v = uclk C o T s v ∨ uclk C o T (s + 1) v = uclk C o T s v + 1 := by
  rw [uclk_succ o v hs]; split_ifs <;> simp

/-- The good configuration of AlgAU after `N(D)` rounds (extracted from the proof of
Theorem 1.1 of [EK21]): for any execution of AlgAU with `k ≥ 3D + 2` on a graph of diameter at
most `D` under a fair schedule, the graph is good at time `R(N(D))` (and hence forever after, by
Lemma 2.10). -/
theorem allGood_stab {G : SimpleGraph V} [Finite V] {D k : ℕ} (hDk : 3 * D + 2 ≤ k)
    (hD : G.ediam ≤ D) {A : ℕ → Set V} (hA : Fair A) {C : ℕ → V → Turn k} (hC : AURun G A C) :
    AllGood G C (R A (stabRoundsK k D)) := by
  have hk1 : 1 ≤ k := by omega
  set T0 := R A (outRounds k 1) with hT0
  have hop : ∀ t, T0 ≤ t → AllOutProt G C t := fun t ht => hC.corollary_2_15 hA hk1 ht
  set T1 := (rho A)^[2 * k - 3] T0 with hT1
  have hjust : ∀ t, T1 ≤ t → Justified G C t := fun t ht => hC.corollary_2_17 hA hop ht
  have hT01 : T0 ≤ T1 := le_rho_iter hA _ _
  have hpersist : ∀ s, T1 ≤ s → AllProt G C s → AllProt G C (s + 1) := fun s hs h =>
    fun v => (hC.allGood_succ (AURun.lemma_2_18 (hjust s hs) h) v).1
  have hprot := hC.lemma_2_22 hA hDk hD (hop T1 hT01) hpersist
  set T2 := (rho A)^[(D + 1) * (2 * ((k - 1) * (2 * k - 2)))] T1 with hT2
  have hT12 : T1 ≤ T2 := le_rho_iter hA _ _
  have hgood : AllGood G C T2 := AURun.lemma_2_18 (hjust T2 hT12) hprot
  have hR : R A (stabRoundsK k D) = T2 := by
    rw [hT2, hT1, hT0, R, R, rho_iter_add, rho_iter_add]; rfl
  rw [hR]; exact hgood

open Classical in
/-- The simulated configuration of round `j` (relative to the unwrapped clocks `uclk` with start
time `T` and offsets `o`): the first coordinate of `w` at some time `τ ≥ T` with `U_w(τ) = j`. -/
noncomputable def simState {k : ℕ} (C : ℕ → V → Q × Q × Turn k) (o : V → ℤ) (T : ℕ) (j : ℤ)
    (w : V) : Q :=
  if h : ∃ τ, T ≤ τ ∧ uclk (auPart C) o T τ w = j then (C h.choose w).1 else (C T w).1

/-! ## The simulation -/

section Sim

variable {G : SimpleGraph V} {P : Algorithm Q} {k : ℕ} {A : ℕ → Set V}
  {C : ℕ → V → Q × Q × Turn k} (hC : IsRun G (synchronizer P k) A C) {T : ℕ}
  (hg : AllGood G (auPart C) T) {o : V → ℤ}

include hC hg

/-- While the unwrapped clock does not change, the `Π*`-state does not change. -/
theorem eq_of_uclk_eq {t t' : ℕ} {w : V} (ht : T ≤ t) (htt' : t ≤ t')
    (h : uclk (auPart C) o T t' w = uclk (auPart C) o T t w) : C t' w = C t w := by
  revert h
  induction t', htt' using Nat.le_induction with
  | base => intro; rfl
  | succ n hn ih =>
    intro h
    have m1 := uclk_mono (C := auPart C) o w (t := T) hn
    have m2 := uclk_mono (C := auPart C) o w (t := T) (show n ≤ n + 1 by omega)
    have hn' : uclk (auPart C) o T n w = uclk (auPart C) o T t w := by omega
    rw [← ih hn']
    apply eq_of_auPart_eq hC
    have hgn := (synchronizer_isRun_auPart hC).allGood_le hg (ht.trans hn)
    apply (synchronizer_isRun_auPart hC).eq_of_not_chg hgn
    intro hc
    have := uclk_succ (C := auPart C) o w (ht.trans hn)
    rw [ite_eq_left hc] at this
    omega

/-- A `+1` step of the unwrapped clock is an AA transition. -/
theorem aa_of_uclk_succ {t : ℕ} {w : V} (ht : T ≤ t)
    (h : uclk (auPart C) o T (t + 1) w = uclk (auPart C) o T t w + 1) :
    w ∈ A t ∧ AAN G (auPart C) t w := by
  have hgt := (synchronizer_isRun_auPart hC).allGood_le hg ht
  have hc : output (auPart C (t + 1) w) ≠ output (auPart C t w) := by
    intro hc
    have := uclk_succ (C := auPart C) o w ht
    rw [ite_eq_right (not_not.2 hc)] at this; omega
  obtain ⟨h1, h2, -⟩ := (synchronizer_isRun_auPart hC).aa_of_chg hgt hc
  exact ⟨h1, h2⟩

/-- A `+1` step of the unwrapped clock performs one simulated step of `Π`. -/
theorem succ_of_uclk_succ {t : ℕ} {w : V} (ht : T ≤ t)
    (h : uclk (auPart C) o T (t + 1) w = uclk (auPart C) o T t w + 1) :
    C (t + 1) w = (P.δ (C t w).1 (simSignal (C t w).2.2 (signal G (C t) w)), (C t w).1,
      (C t w).2.2.aa) := by
  obtain ⟨hw, haan⟩ := aa_of_uclk_succ hC hg ht h
  exact succ_of_aa hC hw (((synchronizer_isRun_auPart hC).allGood_le hg ht w).2.1) haan

/-- The first coordinate of `w` at time `t ≥ T` is the simulated state of round `U_w(t)`. -/
theorem fst_eq_simState {t : ℕ} {w : V} (ht : T ≤ t) :
    (C t w).1 = simState C o T (uclk (auPart C) o T t w) w := by
  have h : ∃ τ, T ≤ τ ∧ uclk (auPart C) o T τ w = uclk (auPart C) o T t w := ⟨t, ht, rfl⟩
  rw [simState, dite_eq_left h]
  obtain ⟨h3, h4⟩ := h.choose_spec
  rcases le_total t h.choose with h5 | h5
  · rw [eq_of_uclk_eq hC hg ht h5 h4]
  · rw [eq_of_uclk_eq hC hg h3 h5 h4.symm]

/-- The second coordinate of `w` at time `t ≥ T` with `U_w(t) = j + 1 > o_w` is the simulated
state of round `j`. -/
theorem snd_eq_simState {t : ℕ} {w : V} {j : ℤ} (ht : T ≤ t) (hj : o w ≤ j)
    (hU : uclk (auPart C) o T t w = j + 1) : (C t w).2.1 = simState C o T j w := by
  have hT : uclk (auPart C) o T T w = o w := uclk_self o T w
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_step_eq (f := fun s => uclk (auPart C) o T s w)
    (a := T) (b := t) (j := j)
    (fun s hs => by
      rcases uclk_succ_cases (C := auPart C) o w hs with h | h <;> simp only [h] <;> omega)
    (by simp only [hT]; omega) (by simp only [hU]; omega) ht
  have e1 := succ_of_uclk_succ hC hg hs1 (by rw [hs3, hs4])
  have e2 := eq_of_uclk_eq hC hg (hs1.trans (Nat.le_succ s)) hs2 (by rw [hs4, hU])
  rw [e2, e1]
  dsimp only
  rw [fst_eq_simState hC hg hs1, hs3]

variable (hk : 2 ≤ k) {B : ZMod (2 * k)}
  (h1 : ∀ v, (pos k (auPart C T v).lvl : ZMod (2 * k)) = B + (o v : ZMod (2 * k)))
  (h2 : ∀ u v, G.Adj u v → o u ≤ o v + 1)

include hk h1 h2

/-- Nearby nodes have the same turn iff they have the same unwrapped clock. -/
theorem auPart_eq_iff {s : ℕ} {v w : V} (hs : T ≤ s)
    (hw1 : uclk (auPart C) o T s w ≤ uclk (auPart C) o T s v + 1)
    (hw2 : uclk (auPart C) o T s v ≤ uclk (auPart C) o T s w + 1) :
    auPart C s w = auPart C s v ↔ uclk (auPart C) o T s w = uclk (auPart C) o T s v := by
  have hgs := (synchronizer_isRun_auPart hC).allGood_le hg hs
  obtain ⟨i1, -⟩ := (synchronizer_isRun_auPart hC).uclk_inv hk hg o B h1 h2 hs
  constructor
  · intro h
    have e := i1 w
    rw [h, i1 v] at e
    exact eq_of_intCast_eq (n := 2 * k) (add_left_cancel e).symm (by push_cast; omega)
      (by push_cast; omega)
  · intro h
    apply Turn.ext
    · exact eq_of_pos_cast (auPart C s w).isLevel (auPart C s v).isLevel (by rw [i1, i1, h])
    · rw [(hgs w).2.1, (hgs v).2.1]

/-- A nearby node is in turn `φ(ν)‾` (`ν` the turn of `v`) iff its unwrapped clock is one more. -/
theorem auPart_eq_aa_iff {s : ℕ} {v w : V} (hs : T ≤ s)
    (hw1 : uclk (auPart C) o T s w ≤ uclk (auPart C) o T s v + 1)
    (hw2 : uclk (auPart C) o T s v ≤ uclk (auPart C) o T s w + 1) :
    auPart C s w = (auPart C s v).aa ↔
      uclk (auPart C) o T s w = uclk (auPart C) o T s v + 1 := by
  have hgs := (synchronizer_isRun_auPart hC).allGood_le hg hs
  obtain ⟨i1, -⟩ := (synchronizer_isRun_auPart hC).uclk_inv hk hg o B h1 h2 hs
  have ea : (pos k (auPart C s v).aa.lvl : ZMod (2 * k)) =
      B + ((uclk (auPart C) o T s v + 1 : ℤ) : ZMod (2 * k)) := by
    rw [show (auPart C s v).aa.lvl = fwd k (auPart C s v).lvl from rfl,
      pos_fwd_cast (auPart C s v).isLevel, i1 v]
    push_cast; ring
  constructor
  · intro h
    have e := i1 w
    rw [h, ea] at e
    exact eq_of_intCast_eq (n := 2 * k) (add_left_cancel e).symm (by push_cast; omega)
      (by push_cast; omega)
  · intro h
    apply Turn.ext
    · exact eq_of_pos_cast (auPart C s w).isLevel (auPart C s v).aa.isLevel
        (by rw [i1, ea, h])
    · rw [(hgs w).2.1]; rfl

/-- At an AA step of `v`, all neighbours have unwrapped clock `U_v` or `U_v + 1`. -/
theorem uclk_of_aan {s : ℕ} {v u : V} (hs : T ≤ s) (haan : AAN G (auPart C) s v)
    (hu : G.Adj v u) :
    uclk (auPart C) o T s u = uclk (auPart C) o T s v ∨
      uclk (auPart C) o T s u = uclk (auPart C) o T s v + 1 := by
  have hgs := (synchronizer_isRun_auPart hC).allGood_le hg hs
  obtain ⟨-, i2⟩ := (synchronizer_isRun_auPart hC).uclk_inv hk hg o B h1 h2 hs
  have b1 := i2 u v hu.symm
  have b2 := i2 v u hu
  rcases (haan u hu).2 with hl | hl
  · left
    exact (auPart_eq_iff hC hg hk h1 h2 hs b1 b2).1
      (Turn.ext hl (by rw [(haan u hu).1, (hgs v).2.1]))
  · right
    exact (auPart_eq_aa_iff hC hg hk h1 h2 hs b1 b2).1 (Turn.ext hl (by rw [(haan u hu).1]; rfl))

/-- The key step: at an AA step of `v` at time `s ≥ T` with `U_v(s) = j ≥ max_w o_w`, the
simulated signal is the `Π`-signal of `v` under the simulated configuration of round `j`. -/
theorem simSignal_eq {s : ℕ} {v : V} (hs : T ≤ s) (haan : AAN G (auPart C) s v)
    (hj : ∀ w, o w ≤ uclk (auPart C) o T s v) :
    simSignal (C s v).2.2 (signal G (C s) v) =
      signal G (simState C o T (uclk (auPart C) o T s v)) v := by
  obtain ⟨-, i2⟩ := (synchronizer_isRun_auPart hC).uclk_inv hk hg o B h1 h2 hs
  have hr : ∀ w, (w = v ∨ G.Adj v w) →
      uclk (auPart C) o T s w = uclk (auPart C) o T s v ∨
        uclk (auPart C) o T s w = uclk (auPart C) o T s v + 1 := by
    rintro w (rfl | hw)
    · left; rfl
    · exact uclk_of_aan hC hg hk h1 h2 hs haan hw
  ext r
  constructor
  · rintro ⟨x, ⟨w, hw, rfl⟩, hx | hx⟩
    · refine ⟨w, hw, ?_⟩
      have hU := (auPart_eq_iff hC hg hk h1 h2 hs (by have := hr w hw; omega)
        (by have := hr w hw; omega)).1 hx.2
      rw [← hx.1, fst_eq_simState hC hg hs, hU]
    · refine ⟨w, hw, ?_⟩
      have hU := (auPart_eq_aa_iff hC hg hk h1 h2 hs (by have := hr w hw; omega)
        (by have := hr w hw; omega)).1 hx.2
      rw [← hx.1, snd_eq_simState hC hg hs (hj w) hU]
  · rintro ⟨w, hw, rfl⟩
    refine ⟨C s w, ⟨w, hw, rfl⟩, ?_⟩
    have b1 : uclk (auPart C) o T s w ≤ uclk (auPart C) o T s v + 1 := by
      have := hr w hw; omega
    have b2 : uclk (auPart C) o T s v ≤ uclk (auPart C) o T s w + 1 := by
      have := hr w hw; omega
    rcases hr w hw with hU | hU
    · left
      exact ⟨by rw [fst_eq_simState hC hg hs, hU], (auPart_eq_iff hC hg hk h1 h2 hs b1 b2).2 hU⟩
    · right
      exact ⟨snd_eq_simState hC hg hs (hj w) hU,
        (auPart_eq_aa_iff hC hg hk h1 h2 hs b1 b2).2 hU⟩

/-- The simulated configuration of round `j + 1` is one synchronous step of `Π` from the
simulated configuration of round `j` (for `j ≥ max_w o_w`). -/
theorem simState_succ {j : ℤ} (hj : ∀ w, o w ≤ j)
    (hunb : ∀ w, ∃ τ, T ≤ τ ∧ j + 1 ≤ uclk (auPart C) o T τ w) (v : V) :
    simState C o T (j + 1) v = P.δ (simState C o T j v) (signal G (simState C o T j) v) := by
  have hT : uclk (auPart C) o T T v = o v := uclk_self o T v
  obtain ⟨τ, hτ1, hτ2⟩ := hunb v
  obtain ⟨s, hs1, -, hs3, hs4⟩ := exists_step_eq (f := fun s => uclk (auPart C) o T s v)
    (a := T) (b := τ) (j := j)
    (fun s hs => by
      rcases uclk_succ_cases (C := auPart C) o v hs with h | h <;> simp only [h] <;> omega)
    (by simp only [hT]; exact hj v) (by omega) hτ1
  obtain ⟨hv, haan⟩ := aa_of_uclk_succ hC hg hs1 (by rw [hs3, hs4])
  have e1 := succ_of_aa hC hv (((synchronizer_isRun_auPart hC).allGood_le hg hs1 v).2.1) haan
  rw [← hs4, ← fst_eq_simState hC hg (hs1.trans (Nat.le_succ s)), e1]
  dsimp only
  rw [simSignal_eq hC hg hk h1 h2 hs1 haan (by rw [hs3]; exact hj), fst_eq_simState hC hg hs1, hs3]

/-- The simulated configurations form a synchronous execution of `Π`. -/
theorem simState_run {j0 : ℤ} (hj0 : ∀ w, o w ≤ j0)
    (hunb : ∀ (n : ℤ) w, ∃ τ, T ≤ τ ∧ n ≤ uclk (auPart C) o T τ w) (i : ℕ) :
    simState C o T (j0 + i) = run G P (simState C o T j0) sync i := by
  induction i with
  | zero => simp [run]
  | succ i ih =>
    funext v
    show _ = step G P (sync i) (run G P (simState C o T j0) sync i) v
    rw [← ih]
    simp only [step, sync, Set.mem_univ, ite_true]
    push_cast
    rw [← add_assoc]
    exact simState_succ hC hg hk h1 h2 (fun w => (hj0 w).trans (by omega)) (fun w => hunb _ w) v

end Sim

/-! ## Main results -/

variable {G : SimpleGraph V}

/-- **Simulation theorem** for the synchronizer of Section 4 of [EK21] (`k ≥ 3D + 2`). For every
initial configuration `C0` of `Π*` and every fair schedule there are an initial configuration
`D0` of `Π` and simulated round numbers `r t v` such that, from time `R(N(D) + D)` on, the first
coordinate of every node `v` at time `t` is the state of `v` in the synchronous execution of `Π`
from `D0` after `r t v` rounds (and the AlgAU turn is able). The round numbers are non-decreasing
in `t`, differ by at most one across edges (from time `R(N(D))` on), and are at least `i` from time
`R(N(D) + D + i)` on. -/
theorem synchronizer_simulation [Finite V] {D k : ℕ} (hDk : 3 * D + 2 ≤ k) (hD : G.ediam ≤ D)
    (P : Algorithm Q) (C0 : V → Q × Q × Turn k) {A : ℕ → Set V} (hA : Fair A) :
    ∃ (D0 : V → Q) (r : ℕ → V → ℕ),
      (∀ i t, R A (stabRoundsK k D + D + i) ≤ t → ∀ v, i ≤ r t v) ∧
      (∀ t, R A (stabRoundsK k D + D) ≤ t → ∀ v,
        (run G (synchronizer P k) C0 A t v).1 = run G P D0 sync (r t v) v ∧
        (run G (synchronizer P k) C0 A t v).2.2.faulty = false) ∧
      (∀ t v, r t v ≤ r (t + 1) v) ∧
      (∀ t, R A (stabRoundsK k D) ≤ t → ∀ u v, G.Adj u v → r t u ≤ r t v + 1) := by
  classical
  set C := run G (synchronizer P k) C0 A with hCdef
  have hC : IsRun G (synchronizer P k) A C := isRun_run _ _ _ _
  have hC' := synchronizer_isRun_auPart hC
  set T := R A (stabRoundsK k D) with hTdef
  have hg : AllGood G (auPart C) T := allGood_stab hDk hD hA hC'
  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨fun v => isEmptyElim v, fun _ v => isEmptyElim v, fun _ _ _ v => isEmptyElim v,
      fun _ _ v => isEmptyElim v, fun _ v => isEmptyElim v, fun _ _ u => isEmptyElim u⟩
  have hk : 2 ≤ k := by omega
  obtain ⟨o, B, h1, h2⟩ := AURun.exists_offsets hD (by omega : D + 2 ≤ k) hg (Classical.arbitrary V)
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨vm, -, hvm⟩ := Finset.exists_max_image Finset.univ o Finset.univ_nonempty
  obtain ⟨j0, hj0e⟩ : ∃ j0, o vm = j0 := ⟨_, rfl⟩
  have hj0 : ∀ w, o w ≤ j0 := fun w => hj0e ▸ hvm w (Finset.mem_univ w)
  have hM : ∀ w, j0 - D ≤ uclk (auPart C) o T T w := by
    intro w
    obtain ⟨p, hp⟩ := SimpleGraph.ediam_le_coe_iff.1 hD vm w
    have := le_add_length_of_walk h2 p
    rw [uclk_self]; omega
  have hiter : ∀ (n : ℕ) w, j0 - D + n ≤ uclk (auPart C) o T ((rho A)^[n] T) w := fun n w =>
    hC'.uclk_rho_iter hA hk hg o B h1 h2 n le_rfl hM w
  have hunb : ∀ (n : ℤ) w, ∃ τ, T ≤ τ ∧ n ≤ uclk (auPart C) o T τ w := fun n w =>
    ⟨(rho A)^[(n - (j0 - D)).toNat] T, le_rho_iter hA _ _, by
      have := hiter (n - (j0 - D)).toNat w; omega⟩
  have hR : ∀ i, R A (stabRoundsK k D + D + i) = (rho A)^[D + i] T := by
    intro i
    rw [hTdef, R, R, rho_iter_add, show stabRoundsK k D + D + i = D + i + stabRoundsK k D by ring]
  have hge : ∀ i t, R A (stabRoundsK k D + D + i) ≤ t → ∀ v,
      j0 + i ≤ uclk (auPart C) o T t v := by
    intro i t ht v
    rw [hR] at ht
    have := hiter (D + i) v
    have := uclk_mono (C := auPart C) o v (t := T) ht
    push_cast at *; omega
  have hTle : ∀ i t, R A (stabRoundsK k D + D + i) ≤ t → T ≤ t := by
    intro i t ht
    rw [hR] at ht
    exact (le_rho_iter hA _ _).trans ht
  refine ⟨simState C o T j0, fun t v => (uclk (auPart C) o T t v - j0).toNat, ?_, ?_, ?_, ?_⟩
  · intro i t ht v; have := hge i t ht v; dsimp only; omega
  · intro t ht v
    have ht0 : R A (stabRoundsK k D + D + 0) ≤ t := by simpa using ht
    have hTt := hTle 0 t ht0
    have hU := hge 0 t ht0 v
    refine ⟨?_, (hC'.allGood_le hg hTt v).2.1⟩
    rw [fst_eq_simState hC hg hTt, ← simState_run hC hg hk h1 h2 hj0 hunb]
    dsimp only; congr 1; push_cast at hU; omega
  · intro t v
    have := uclk_mono (C := auPart C) o v (t := T) (show t ≤ t + 1 by omega)
    dsimp only; omega
  · intro t ht u v huv
    have := (hC'.uclk_inv hk hg o B h1 h2 ht).2 u v huv
    dsimp only; omega

/-- `Π` synchronously self-stabilizes on `G` within `f` rounds for the *static* task `Legal`
(output vectors that, once reached, must be kept forever, e.g. leader election or MIS): from
every initial configuration, the synchronous execution has, from round `f` on, a fixed legal
output vector (`ω q = none` encodes that `q` is not an output state). -/
def SyncStabilizes (G : SimpleGraph V) {O : Type*} (P : Algorithm Q) (ω : Q → Option O)
    (Legal : (V → O) → Prop) (f : ℕ) : Prop :=
  ∀ D0 : V → Q, ∃ out : V → O, Legal out ∧
    ∀ j, f ≤ j → ∀ v, ω (run G P D0 sync j v) = some (out v)

open Cslib.SelfStabilization in
/-- `SyncStabilizes` is pseudo-stabilization within `f` rounds, for the class of synchronous
executions of `Π`, of the static specification "a fixed legal output vector forever". -/
theorem syncStabilizes_iff {O : Type*} {P : Algorithm Q} {ω : Q → Option O}
    {Legal : (V → O) → Prop} {f : ℕ} : SyncStabilizes G P ω Legal f ↔
    PseudoStabilizingWithin (IsSyncExec fun C v => P.δ (C v) (signal G C v))
      (fun e => ∃ out : V → O, Legal out ∧ ∀ j v, ω (e j v) = some (out v)) f := by
  have hrun := fun D0 => Cslib.StoneAge.run_sync_mem_isSyncExec (G := G) P D0
  constructor
  · intro h e he
    obtain ⟨out, hout, h⟩ := h (e 0)
    refine ⟨out, hout, fun j v => ?_⟩
    have he' : IsSyncExec (fun C v => P.δ (C v) (signal G C v)) e := he
    show ω (e (f + j) v) = some (out v)
    have h2 := (hrun (e 0)).eq_iterate (f + j)
    rw [run_zero] at h2
    rw [he'.eq_iterate, ← h2]
    exact h _ (Nat.le_add_right f j) v
  · intro h D0
    obtain ⟨out, hout, h⟩ := h _ (hrun D0)
    refine ⟨out, hout, fun j hj v => ?_⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le hj
    exact h i v

/-- **Corollary 1.2 of [EK21]** (deterministic `Π`, static tasks, any `k ≥ 3D + 2`): if `Π`
synchronously self-stabilizes within `f` rounds on `G` (of diameter at most `D`), then for every
initial configuration of the synchronizer `Π*` and every fair schedule, from time
`R(N(D) + D + f)` on all nodes of `Π*` output a fixed legal output vector. -/
theorem corollary_1_2_general [Finite V] {D k : ℕ} (hDk : 3 * D + 2 ≤ k) (hD : G.ediam ≤ D)
    {O : Type*} {P : Algorithm Q} {ω : Q → Option O} {Legal : (V → O) → Prop} {f : ℕ}
    (hP : SyncStabilizes G P ω Legal f) (C0 : V → Q × Q × Turn k) {A : ℕ → Set V}
    (hA : Fair A) :
    ∃ out : V → O, Legal out ∧ ∀ t, R A (stabRoundsK k D + D + f) ≤ t → ∀ v,
      synchOutput ω (run G (synchronizer P k) C0 A t v) = some (out v) := by
  obtain ⟨D0, r, hr1, hr2, -, -⟩ := synchronizer_simulation hDk hD P C0 hA
  obtain ⟨out, hout1, hout2⟩ := hP D0
  refine ⟨out, hout1, fun t ht v => ?_⟩
  have ht' : R A (stabRoundsK k D + D) ≤ t :=
    (rho_iter_le_iter hA (by omega : stabRoundsK k D + D ≤ stabRoundsK k D + D + f) 0).trans ht
  obtain ⟨e1, e2⟩ := hr2 t ht' v
  simp only [synchOutput, e2, Bool.false_eq_true, ite_false, e1]
  exact hout2 _ (hr1 f t ht v) v

/-- **Corollary 1.2 of [EK21]** (deterministic `Π`, static tasks), with the paper's parameter
`k = 3D + 2` of AlgAU: the synchronizer `Π*` (state space `|Q|² (12D + 4)`) stabilizes within
`N(D) + D + f = f + O(D³)` rounds under every fair schedule. -/
theorem corollary_1_2 [Finite V] {D : ℕ} (hD : G.ediam ≤ D) {O : Type*} {P : Algorithm Q}
    {ω : Q → Option O} {Legal : (V → O) → Prop} {f : ℕ} (hP : SyncStabilizes G P ω Legal f)
    (C0 : V → Q × Q × Turn (3 * D + 2)) {A : ℕ → Set V} (hA : Fair A) :
    ∃ out : V → O, Legal out ∧ ∀ t, R A (stabRounds D + D + f) ≤ t → ∀ v,
      synchOutput ω (run G (synchronizer P (3 * D + 2)) C0 A t v) = some (out v) :=
  corollary_1_2_general le_rfl hD hP C0 hA

/-- Corollary 1.2 of [EK21] with an explicit `f + O(D³)` bound: stabilization within
`f + 71 (D + 1)³` rounds. -/
theorem corollary_1_2_exists [Finite V] {D : ℕ} (hD : G.ediam ≤ D) {O : Type*} {P : Algorithm Q}
    {ω : Q → Option O} {Legal : (V → O) → Prop} {f : ℕ} (hP : SyncStabilizes G P ω Legal f)
    (C0 : V → Q × Q × Turn (3 * D + 2)) {A : ℕ → Set V} (hA : Fair A) :
    ∃ i ≤ f + 71 * (D + 1) ^ 3, ∃ out : V → O, Legal out ∧ ∀ t, R A i ≤ t → ∀ v,
      synchOutput ω (run G (synchronizer P (3 * D + 2)) C0 A t v) = some (out v) := by
  refine ⟨stabRounds D + D + f, ?_, corollary_1_2 hD hP C0 hA⟩
  have h1 := stabRounds_le D
  have h2 : D ≤ (D + 1) ^ 3 := (Nat.le_succ D).trans (Nat.le_self_pow (by norm_num) _)
  omega

end ThinUnison
