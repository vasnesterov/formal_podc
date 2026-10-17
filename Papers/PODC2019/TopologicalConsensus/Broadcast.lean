import Papers.PODC2019.TopologicalConsensus.DynamicNetworks
import Papers.PODC2019.TopologicalConsensus.Strong

/-!
# Broadcastability and weak vs. strong validity for message adversaries (Section 7, Section 8.4)

In the dynamic-network model (`DN.dnModel MA`, arbitrary and independent inputs, processes
`Fin n`):

* `Heard σ t q p`: `q` has (transitively) heard of `p` after `t` rounds; `Broadcaster σ p`.
* `broadcaster_of_solvable`: if binary consensus is solvable, every pattern of `MA` has a
  broadcaster (`bProc L σ`, extracted from the decision sets as in the proof of Theorem 7.11).
* `dn_corollary_7_7`: if binary consensus is solvable, every connected component of `Σ`
  (uniform topology) has a common broadcaster whose input is the same in the whole component
  (Lemma 7.4, Lemma 7.6, Corollary 7.7).
* `dn_theorem_7_9_exists`: the broadcaster decision sets `{β(σ) = p, x_p = v}` are clopen for a
  suitable choice `β` of broadcasters (Theorem 7.9 with an *existentially chosen* broadcaster;
  with the paper's canonical choice it is false, see `CanonicalCex.lean`).
* `binary_iff_strong`, `binary_iff_weak` (Theorem 7.12, (1) ⇔ (3) ⇔ (4)): binary consensus is
  solvable iff strong consensus is solvable for every value set `V` iff (weak) consensus is
  solvable for every `V`.
-/

namespace TopoConsensus

namespace DN

open Set Cslib.HeardOf Topology
open Cslib.DynNet (Journey journey_self_iff journey_succ_iff)

set_option linter.unusedSectionVars false

variable {P V W : Type*}

/-! ### Heard-of relation -/

/-- `q` has (transitively) heard of `p` after `t` rounds of `σ`: there is a journey
(`Cslib.DynNet.Journey`) from `p` at time `0` to `q` at time `t` (`heard_zero_iff`,
`heard_succ_iff` restate the recursive definition). -/
def Heard (σ : ℕ → Graph P) (t : ℕ) (q p : P) : Prop := Journey σ 0 p t q

/-- `p` is a broadcaster of `σ`: every process eventually hears of `p` (Definition 7.3). -/
def Broadcaster (σ : ℕ → Graph P) (p : P) : Prop := ∀ q, ∃ T, Heard σ T q p

theorem heard_zero_iff {σ : ℕ → Graph P} {q p : P} : Heard σ 0 q p ↔ q = p :=
  journey_self_iff.trans eq_comm

theorem heard_succ_iff {σ : ℕ → Graph P} {t : ℕ} {q p : P} :
    Heard σ (t + 1) q p ↔ Heard σ t q p ∨ ∃ r, σ t r q ∧ Heard σ t r p := by
  rw [Heard, journey_succ_iff (Nat.zero_le t)]
  constructor
  · rintro ⟨r, h, rfl | hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, h⟩
  · rintro (h | ⟨r, hr, h⟩)
    · exact ⟨q, h, Or.inl rfl⟩
    · exact ⟨r, h, Or.inr hr⟩

theorem Heard.mono {σ : ℕ → Graph P} {t : ℕ} {q p : P} (h : Heard σ t q p) :
    ∀ u, t ≤ u → Heard σ u q p :=
  fun _ hu => Journey.mono_right h hu

variable {x y z : P → V} {σ τ : ℕ → Graph P}

/-- Heard-of property (iii): a process that cannot distinguish two executions and has heard of
`p` sees the same input of `p`. -/
theorem FIIndist.input_of_heard {t : ℕ} {q p : P} (h : FIIndist x y σ τ t q)
    (hh : Heard σ t q p) : x p = y p :=
  (Cslib.HeardOf.FIIndist.journey h hh).2.zero

/-- Indistinguishability of the communication patterns does not depend on the inputs. -/
theorem FIIndist.pattern {V' : Type*} {t : ℕ} {q : P} (h : FIIndist x y σ τ t q) (z : P → V') :
    FIIndist z z σ τ t q :=
  Cslib.HeardOf.FIIndist.imp (fun _ _ => rfl) h

/-- Changing the input of `p` is invisible to a process that has not heard of `p`. -/
theorem FIIndist_of_not_heard {p : P} (hxy : ∀ r, r ≠ p → x r = y r) {t : ℕ} {q : P}
    (hn : ¬ Heard σ t q p) : FIIndist x y σ σ t q :=
  Cslib.HeardOf.FIIndist.of_agree (fun _ hr => hxy _ fun e => hn (e ▸ hr))
    (fun _ _ _ _ => Iff.rfl)

/-! ### Inputs and pattern of an execution -/

/-- The inputs of an execution. -/
def inpOf (γ : ℕ → Conf P V) : P → V := (γ 0).inp

/-- The communication pattern of an execution. -/
def patOf (γ : ℕ → Conf P V) : ℕ → Graph P := fun k => (γ (k + 1)).pat k

theorem inpOf_exec : inpOf (exec x σ) = x := rfl

theorem patOf_exec : patOf (exec x σ) = σ := by
  funext k; simp [patOf, exec, trunc]

variable [Nonempty P] {MA : Set (ℕ → Graph P)}

theorem eq_exec {γ : ℕ → Conf P V} (hγ : γ ∈ (dnModel (V := V) MA).adm) :
    γ = exec (inpOf γ) (patOf γ) ∧ patOf γ ∈ MA := by
  obtain ⟨x, σ, hσ, rfl⟩ := hγ
  rw [inpOf_exec, patOf_exec]
  exact ⟨rfl, hσ⟩

/-- A labelling of executions is locally constant (its fibres are `d_u`-open). -/
def LocConst (MA : Set (ℕ → Graph P)) (L : (P → V) → (ℕ → Graph P) → W) : Prop :=
  ∀ x, ∀ σ ∈ MA, ∃ T, ∀ y, ∀ τ ∈ MA, (∃ p, FIIndist x y σ τ T p) → L y τ = L x σ

/-- The induced labelling of `Σ`. -/
def labOf (L : (P → V) → (ℕ → Graph P) → W) (γ : (dnModel (V := V) MA).adm) : W :=
  L (inpOf (γ : ℕ → Conf P V)) (patOf (γ : ℕ → Conf P V))

variable [Fintype P]

theorem isOpen_labOf {L : (P → V) → (ℕ → Graph P) → W} (hL : LocConst MA L) (w : W) :
    IsOpen[(dnModel (V := V) MA).τU] (labOf (MA := MA) L ⁻¹' {w}) := by
  rw [Model.isOpen_τU_iff]
  intro γ hγ
  obtain ⟨hγe, hγm⟩ := eq_exec γ.2
  obtain ⟨T, hT⟩ := hL _ _ hγm
  refine ⟨T, fun δ ⟨p, hp⟩ => ?_⟩
  obtain ⟨hδe, hδm⟩ := eq_exec δ.2
  simp only [mem_preimage, mem_singleton_iff] at hγ ⊢
  rw [← hγ]
  rw [hγe, hδe] at hp
  exact hT _ _ hδm ⟨p, okP_upTo_iff.1 hp⟩

theorem isClopen_labOf {L : (P → V) → (ℕ → Graph P) → W} (hL : LocConst MA L) (w : W) :
    IsClopen[(dnModel (V := V) MA).τU] (labOf (MA := MA) L ⁻¹' {w}) :=
  @isClopen_fibers _ _ (dnModel (V := V) MA).τU _ (isOpen_labOf hL) w

/-- A locally constant labelling is constant on connected components. -/
theorem labOf_eq_of_mem_connectedComponent {L : (P → V) → (ℕ → Graph P) → W}
    (hL : LocConst MA L) {γ δ : (dnModel (V := V) MA).adm}
    (h : δ ∈ @connectedComponent _ (dnModel (V := V) MA).τU γ) :
    labOf (MA := MA) L δ = labOf (MA := MA) L γ := by
  let _ := (dnModel (V := V) MA).τU
  have := (isClopen_labOf hL (labOf (MA := MA) L γ)).connectedComponent_subset
    (x := γ) rfl h
  simpa using this

end DN

/-! ### Extracting a broadcaster from binary consensus (proof of Theorem 7.11) -/

namespace DN

open Set Cslib.HeardOf Topology

variable {n : ℕ} [NeZero n] {MA : Set (ℕ → Graph (Fin n))}

/-- `I_k`: processes `< k` have input `1`, the others `0`. -/
def Ivec (k : ℕ) : Fin n → Bool := fun q => decide (q.val < k)

/-- Binary labellings. -/
abbrev BinLab (n : ℕ) := (Fin n → Bool) → (ℕ → Graph (Fin n)) → Bool

/-- Validity of a binary labelling. -/
def BinValid (MA : Set (ℕ → Graph (Fin n))) (L : BinLab n) : Prop :=
  ∀ v x, ∀ σ ∈ MA, (∀ p, x p = v) → L x σ = v

open Classical in
/-- `b(σ)`: the least `k` with `L(I_{k+1}, σ) = 1`. -/
noncomputable def bIdx (L : BinLab n) (σ : ℕ → Graph (Fin n)) : ℕ :=
  if h : ∃ k, L (Ivec (k + 1)) σ = true then Nat.find h else 0

/-- The broadcaster `b(σ)` as a process. -/
noncomputable def bProc (L : BinLab n) (σ : ℕ → Graph (Fin n)) : Fin n :=
  ⟨bIdx L σ % n, Nat.mod_lt _ (Nat.pos_of_neZero n)⟩

omit [NeZero n] in
theorem Ivec_of_le {k : ℕ} (hk : n ≤ k) : Ivec (n := n) k = fun _ => true := by
  funext q; simp [Ivec]; omega

omit [NeZero n] in
theorem Ivec_zero : Ivec (n := n) 0 = fun _ => false := by
  funext q; simp [Ivec]

variable {L : BinLab n}

theorem exists_bIdx (hV : BinValid MA L) {σ : ℕ → Graph (Fin n)} (hσ : σ ∈ MA) :
    ∃ k, L (Ivec (k + 1)) σ = true :=
  ⟨n - 1, hV true _ σ hσ (fun p => by
    rw [Ivec_of_le (by have := Nat.pos_of_neZero n; omega)])⟩

theorem bIdx_spec (hV : BinValid MA L) {σ : ℕ → Graph (Fin n)} (hσ : σ ∈ MA) :
    bIdx L σ < n ∧ L (Ivec (bIdx L σ + 1)) σ = true ∧ L (Ivec (bIdx L σ)) σ = false := by
  classical
  have h := exists_bIdx hV hσ
  have hb : bIdx L σ = Nat.find h := by unfold bIdx; rw [dite_eq_left h]
  refine ⟨?_, ?_, ?_⟩
  · rw [hb]
    have := Nat.find_min' h (m := n - 1) (hV true _ σ hσ (fun p => by
      rw [Ivec_of_le (by have := Nat.pos_of_neZero n; omega)]))
    have := Nat.pos_of_neZero n
    omega
  · rw [hb]; exact Nat.find_spec h
  · rw [hb]
    rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | hpos
    · rw [h0, Ivec_zero]; exact hV false _ σ hσ (fun _ => rfl)
    · have := Nat.find_min h (m := Nat.find h - 1) (by omega)
      rw [show Nat.find h - 1 + 1 = Nat.find h by omega] at this
      simpa using this

theorem bProc_val (hV : BinValid MA L) {σ : ℕ → Graph (Fin n)} (hσ : σ ∈ MA) :
    (bProc L σ).val = bIdx L σ := Nat.mod_eq_of_lt (bIdx_spec hV hσ).1

/-- `b(σ)` is a broadcaster of `σ`: otherwise some process could not distinguish the inputs
`I_b` and `I_{b+1}` (which differ only at `b`), although their labels differ. -/
theorem broadcaster_bProc (hV : BinValid MA L) (hL : LocConst MA L) {σ : ℕ → Graph (Fin n)}
    (hσ : σ ∈ MA) : Broadcaster σ (bProc L σ) := by
  obtain ⟨-, h1, h0⟩ := bIdx_spec hV hσ
  intro q
  by_contra hq
  push Not at hq
  have hdiff : ∀ r, r ≠ bProc L σ → Ivec (bIdx L σ) r = Ivec (bIdx L σ + 1) r := by
    intro r hr
    have : r.val ≠ bIdx L σ := fun h => hr (Fin.ext (by rw [bProc_val hV hσ, h]))
    simp only [Ivec]
    congr 1
    exact propext ⟨fun h => by omega, fun h => by omega⟩
  obtain ⟨T, hT⟩ := hL (Ivec (bIdx L σ)) σ hσ
  have := hT (Ivec (bIdx L σ + 1)) σ hσ ⟨q, FIIndist_of_not_heard hdiff (hq T)⟩
  rw [h1, h0] at this
  exact Bool.noConfusion this

/-- If binary consensus is solvable, every pattern of `MA` has a broadcaster. -/
theorem broadcaster_of_solvable (h : UniformSolvable (dnModel (V := Bool) MA)) :
    ∀ σ ∈ MA, ∃ p, Broadcaster σ p := by
  obtain ⟨L, hV, hL⟩ := dn_solvable_iff.1 h
  exact fun σ hσ => ⟨_, broadcaster_bProc (L := L) hV hL hσ⟩

/-- `b(·)` and the broadcaster's input are locally constant. -/
theorem locConst_bProc_input (hV : BinValid MA L) (hL : LocConst MA L) (V : Type*) :
    LocConst MA (fun (x : Fin n → V) σ => (bProc L σ, x (bProc L σ))) := by
  classical
  intro x σ hσ
  -- times for local constancy of `L` at `(I_k, σ)`, `k ≤ n`
  have hTk : ∀ k : Fin (n + 1), ∃ T, ∀ y, ∀ τ ∈ MA, (∃ p, FIIndist (Ivec k) y σ τ T p) →
      L y τ = L (Ivec k) σ := fun k => hL _ σ hσ
  choose Tk hTk using hTk
  -- times by which everybody has heard of the broadcaster
  have hTq := broadcaster_bProc hV hL hσ
  choose Tq hTq using hTq
  refine ⟨max (Finset.univ.sup Tk) (Finset.univ.sup Tq), fun y τ hτ ⟨r, hr⟩ => ?_⟩
  -- the labels of all `I_k` agree
  have hagree : ∀ k, L (Ivec k) τ = L (Ivec k) σ := by
    intro k
    have hk : ∀ j : Fin (n + 1), L (Ivec j) τ = L (Ivec j) σ := by
      intro j
      refine hTk j _ τ hτ ⟨r, ?_⟩
      exact (hr.pattern (Ivec j)).mono _
        ((Finset.le_sup (Finset.mem_univ j)).trans (le_max_left _ _))
    by_cases hkn : k ≤ n
    · exact hk ⟨k, Nat.lt_succ_of_le hkn⟩
    · rw [Ivec_of_le (by omega), ← Ivec_of_le (n := n) le_rfl]
      exact hk ⟨n, Nat.lt_succ_self n⟩
  have hb : bIdx L τ = bIdx L σ := by
    have e1 := exists_bIdx hV hσ
    have e2 := exists_bIdx hV hτ
    unfold bIdx
    rw [dite_eq_left e1, dite_eq_left e2]
    apply le_antisymm
    · exact Nat.find_min' e2 (by rw [hagree]; exact Nat.find_spec e1)
    · exact Nat.find_min' e1 (by rw [← hagree]; exact Nat.find_spec e2)
  have hp : bProc L τ = bProc L σ := Fin.ext (by simp only [bProc, hb])
  show (bProc L τ, y (bProc L τ)) = (bProc L σ, x (bProc L σ))
  rw [hp]
  have hheard : Heard σ (max (Finset.univ.sup Tk) (Finset.univ.sup Tq)) r (bProc L σ) :=
    (hTq r).mono _ ((Finset.le_sup (Finset.mem_univ r)).trans (le_max_right _ _))
  rw [hr.input_of_heard hheard]

/-- **Lemma 7.4 / Lemma 7.6 / Corollary 7.7 for message adversaries**: if binary consensus is
solvable, every connected component of `Σ` (uniform topology) has a common broadcaster that has
the same input in every execution of the component. -/
theorem dn_corollary_7_7 (h : UniformSolvable (dnModel (V := Bool) MA)) (V : Type*)
    (γ : (dnModel (V := V) MA).adm) :
    ∃ p, ∀ δ ∈ @connectedComponent _ (dnModel (V := V) MA).τU γ,
      Broadcaster (patOf (δ : ℕ → Conf (Fin n) V)) p ∧
      inpOf (δ : ℕ → Conf (Fin n) V) p = inpOf (γ : ℕ → Conf (Fin n) V) p := by
  obtain ⟨L, hV, hL⟩ := dn_solvable_iff.1 h
  have hloc := locConst_bProc_input (L := L) hV hL V
  refine ⟨bProc L (patOf (γ : ℕ → Conf (Fin n) V)), fun δ hδ => ?_⟩
  have := labOf_eq_of_mem_connectedComponent hloc hδ
  simp only [labOf, Prod.mk.injEq] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨?_, ?_⟩
  · rw [← h1]; exact broadcaster_bProc hV hL (eq_exec δ.2).2
  · exact (congrArg (inpOf (δ : ℕ → Conf (Fin n) V)) h1).symm.trans h2

/-- **Theorem 7.9 for message adversaries, with an existentially chosen broadcaster**: if binary
consensus is solvable, there is a choice `β(σ)` of a broadcaster of every `σ ∈ MA` such that all
broadcaster decision sets `Σ^p_v = {(x, σ) | β(σ) = p, x_p = v}` are clopen in the uniform
topology (for every value set `V`). -/
theorem dn_theorem_7_9_exists (h : UniformSolvable (dnModel (V := Bool) MA)) (V : Type*) :
    ∃ β : (ℕ → Graph (Fin n)) → Fin n, (∀ σ ∈ MA, Broadcaster σ (β σ)) ∧
      ∀ (p : Fin n) (v : V), IsClopen[(dnModel (V := V) MA).τU]
        {γ | β (patOf (γ : ℕ → Conf (Fin n) V)) = p ∧ inpOf (γ : ℕ → Conf (Fin n) V) p = v} := by
  obtain ⟨L, hV, hL⟩ := dn_solvable_iff.1 h
  refine ⟨bProc L, fun σ hσ => broadcaster_bProc hV hL hσ, fun p v => ?_⟩
  have := isClopen_labOf (locConst_bProc_input (L := L) hV hL V) (p, v)
  convert this using 1
  ext γ
  simp only [mem_ofPred_eq, labOf, mem_preimage, mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, h2⟩; exact ⟨rfl, h2⟩
  · rintro ⟨rfl, h2⟩; exact ⟨rfl, h2⟩

/-- Binary consensus ⇒ strong consensus for any value set: decide the input of `b(σ)`. -/
theorem strong_of_binary (h : UniformSolvable (dnModel (V := Bool) MA)) (V : Type*) :
    StrongUniformSolvable (dnModel (V := V) MA) := by
  obtain ⟨L, hV, hL⟩ := dn_solvable_iff.1 h
  have hloc := locConst_bProc_input (L := L) hV hL V
  have hS : LocConst MA (fun (x : Fin n → V) σ => x (bProc L σ)) := by
    intro x σ hσ
    obtain ⟨T, hT⟩ := hloc x σ hσ
    exact ⟨T, fun y τ hτ hp => congrArg Prod.snd (hT y τ hτ hp)⟩
  rw [Model.theorem_5_2c_strong _ lockstepRecall, Model.τUc_eq_τU _ faultFree]
  exact ⟨labOf (MA := MA) (fun (x : Fin n → V) σ => x (bProc L σ)), isClopen_labOf hS,
    fun γ => ⟨_, rfl⟩⟩

/-- **Theorem 7.12 for message adversaries ((1) ⇔ (3))**: binary consensus is solvable iff
consensus with strong validity is solvable for every set of values. -/
theorem binary_iff_strong :
    UniformSolvable (dnModel (V := Bool) MA) ↔
      ∀ V : Type, StrongUniformSolvable (dnModel (V := V) MA) :=
  ⟨fun h V => strong_of_binary h V, fun h => (h Bool).uniformSolvable⟩

/-- **Theorem 7.12 for message adversaries ((1) ⇔ (4))**: binary consensus is solvable iff
consensus (weak validity) is solvable for every set of values. -/
theorem binary_iff_weak :
    UniformSolvable (dnModel (V := Bool) MA) ↔ ∀ V : Type, UniformSolvable (dnModel (V := V) MA) :=
  ⟨fun h V => (strong_of_binary h V).uniformSolvable, fun h => h Bool⟩

end DN

end TopoConsensus
