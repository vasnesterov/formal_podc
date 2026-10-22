/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- CSLib candidate: Cslib/Computability/Distributed/SWMR/FLP.lean
import Podc.Computability.Distributed.SWMR.Basic

/-!
# FLP / Loui–Abu-Amara: no 1-resilient binary consensus from read/write registers

We prove that binary consensus (with weak validity, `binConsensus`) cannot be solved
`1`-resiliently by `m ≥ 2` processes in the asynchronous read/write SWMR shared-memory model
(`Alg.not_solves_binConsensus`). This is the shared-memory version of Fischer–Lynch–Paterson
due to Loui and Abu-Amara.

The proof is the classical valency argument:

* `FLP.exists_biv_init`: some initial configuration is bivalent (inputs are flipped one at a
  time; two adjacent univalent configurations of different valences differ only in the local
  state of one process, which may crash);
* `FLP.swap`: two steps of different processes commute up to the local state of one of them;
* `FLP.exists_biv_ext`: every reachable bivalent configuration has, for every process `p`, a
  bivalent extension ending with a step of `p`;
* iterating the extension with `p` ranging cyclically over all processes yields an infinite
  execution without faulty processes in which nobody ever decides (`concatSched` builds the
  infinite schedule from the finite blocks).
-/

namespace Cslib.SWMR

/-! ### Infinite schedules from finite blocks -/

section Blocks

variable {P : Type}

/-- The concatenation of the first `j` blocks. -/
def concatBlocks (B : ℕ → List P) (j : ℕ) : List P := (List.range j).flatMap B

@[simp] lemma concatBlocks_zero (B : ℕ → List P) : concatBlocks B 0 = [] := rfl

lemma concatBlocks_succ (B : ℕ → List P) (j : ℕ) :
    concatBlocks B (j + 1) = concatBlocks B j ++ B j := by
  simp [concatBlocks, List.range_succ]

lemma concatBlocks_prefix (B : ℕ → List P) {j j' : ℕ} (h : j ≤ j') :
    concatBlocks B j <+: concatBlocks B j' := by
  induction j', h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ j' _ ih => exact ih.trans (by rw [concatBlocks_succ]; exact List.prefix_append _ _)

lemma le_length_concatBlocks {B : ℕ → List P} (hB : ∀ i, B i ≠ []) (j : ℕ) :
    j ≤ (concatBlocks B j).length := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [concatBlocks_succ, List.length_append]
    have := List.length_pos_of_ne_nil (hB j)
    omega

/-- The infinite schedule obtained by concatenating the nonempty blocks `B 0, B 1, …`. -/
def concatSched (B : ℕ → List P) (hB : ∀ i, B i ≠ []) (n : ℕ) : P :=
  (concatBlocks B (n + 1))[n]'(by have := le_length_concatBlocks hB (n + 1); omega)

lemma getElem?_concatBlocks {B : ℕ → List P} (hB : ∀ i, B i ≠ []) {j n : ℕ}
    (hn : n < (concatBlocks B j).length) :
    (concatBlocks B j)[n]? = some (concatSched B hB n) := by
  have h1 : n < (concatBlocks B (n + 1)).length := by
    have := le_length_concatBlocks hB (n + 1); omega
  rw [concatSched, ← List.getElem?_eq_getElem h1]
  rcases le_total j (n + 1) with h | h
  · obtain ⟨t, ht⟩ := concatBlocks_prefix B h
    rw [← ht, List.getElem?_append_left hn]
  · obtain ⟨t, ht⟩ := concatBlocks_prefix B h
    rw [← ht, List.getElem?_append_left h1]

lemma pre_concatSched {B : ℕ → List P} (hB : ∀ i, B i ≠ []) (j : ℕ) :
    pre (concatSched B hB) (concatBlocks B j).length = concatBlocks B j := by
  apply List.ext_getElem?
  intro n
  by_cases hn : n < (concatBlocks B j).length
  · rw [getElem?_concatBlocks hB hn]
    simp [pre, hn]
  · rw [List.getElem?_eq_none (by simpa using hn), List.getElem?_eq_none (by simpa using hn)]

lemma exists_pre_append_of_le (σ : ℕ → P) {T T' : ℕ} (h : T ≤ T') :
    ∃ ρ, pre σ T ++ ρ = pre σ T' := by
  induction T', h using Nat.le_induction with
  | base => exact ⟨[], by simp⟩
  | succ T' _ ih =>
    obtain ⟨ρ, hρ⟩ := ih
    exact ⟨ρ ++ [σ T'], by rw [pre_succ, ← hρ, List.append_assoc]⟩

end Blocks

namespace FLP

variable {P K : Type} {V : K → Type} [DecidableEq P] [DecidableEq K] {A : Alg P K V Bool Bool}

/-- `C` is reachable from some initial configuration. -/
def Reach (A : Alg P K V Bool Bool) (C : Config A) : Prop :=
  ∃ x σ, C = A.run (A.initCfg x) σ

/-- Some extension of `C` contains the decision `b`. -/
def Can (C : Config A) (b : Bool) : Prop := ∃ τ q, (A.run C τ).out q = some b

/-- Both decisions are still possible from `C`. -/
def Biv (C : Config A) : Prop := Can C true ∧ Can C false

lemma reach_init (x : P → Bool) : Reach A (A.initCfg x) := ⟨x, [], rfl⟩

lemma Reach.run {C : Config A} (h : Reach A C) (τ : List P) : Reach A (A.run C τ) := by
  obtain ⟨x, σ, rfl⟩ := h
  exact ⟨x, σ ++ τ, (Alg.run_append _ _ _).symm⟩

lemma Reach.step {C : Config A} (h : Reach A C) (p : P) : Reach A (A.step p C) := by
  simpa using h.run [p]

lemma Can.of_run {C : Config A} {τ : List P} {b : Bool} (h : Can (A.run C τ) b) : Can C b := by
  obtain ⟨ρ, q, hq⟩ := h
  exact ⟨τ ++ ρ, q, by rw [Alg.run_append]; exact hq⟩

lemma Can.of_step {C : Config A} {p : P} {b : Bool} (h : Can (A.step p C) b) : Can C b :=
  Can.of_run (τ := [p]) (by simpa using h)

lemma not_can_not {C : Config A} (hb : ¬ Biv C) {c : Bool} (hc : Can C c) : ¬ Can C (!c) := by
  cases c
  · exact fun h => hb ⟨h, hc⟩
  · exact fun h => hb ⟨hc, h⟩

section Safety

variable {t : ℕ} (hA : A.Solves t binConsensus)
include hA

lemma agree {C : Config A} (hC : Reach A C) {p q : P} {b c : Bool} (hp : C.out p = some b)
    (hq : C.out q = some c) : b = c := by
  obtain ⟨x, σ, rfl⟩ := hC
  exact (hA.1 x σ).2 p q b c hp hq

lemma eq_of_out_of_can {C : Config A} (hC : Reach A C) {p : P} {b c : Bool}
    (hp : C.out p = some b) (hc : Can C c) : c = b := by
  obtain ⟨τ, q, hq⟩ := hc
  exact (agree hA (hC.run τ) (Alg.out_run_of_out C τ hp) hq).symm

lemma eq_of_can_init_const (b : Bool) {c : Bool} (h : Can (A.initCfg (fun _ => b)) c) :
    c = b := by
  obtain ⟨τ, q, hq⟩ := h
  exact (hA.1 _ τ).1 b (fun _ => rfl) q c hq

end Safety

/-! ### Commuting steps -/

lemma step_of_write {C : Config A} {p : P} {i : K} {v : V i} {s : A.S}
    (h : A.next p (C.loc p) = .write i v s) :
    A.step p C =
      { C with loc := Function.update C.loc p s,
               mem := Function.update C.mem p (Function.update (C.mem p) i v) } := by
  unfold Alg.step; rw [h]

lemma step_of_read {C : Config A} {p r : P} {i : K} {k : V i → A.S}
    (h : A.next p (C.loc p) = .read r i k) :
    A.step p C = { C with loc := Function.update C.loc p (k (C.mem r i)) } := by
  unfold Alg.step; rw [h]

lemma step_of_decide {C : Config A} {p : P} {y : Bool} {s : A.S}
    (h : A.next p (C.loc p) = .decide y s) :
    A.step p C =
      { C with loc := Function.update C.loc p s,
               out := Function.update C.out p ((C.out p).or (some y)) } := by
  unfold Alg.step; rw [h]

/-- Two steps of different processes commute up to the local state of one process. -/
lemma swap (E : Config A) {p q : P} (hpq : p ≠ q) :
    ∃ u, AgreeOn ({u}ᶜ : Set P) (A.step q (A.step p E)) (A.step p (A.step q E)) := by
  have hq' : (A.step p E).loc q = E.loc q := Alg.step_loc_ne E hpq.symm
  have hp' : (A.step q E).loc p = E.loc p := Alg.step_loc_ne E hpq
  rcases hap : A.next p (E.loc p) with ⟨i, v, s⟩ | ⟨r, i, k⟩ | ⟨y, s⟩ <;>
  rcases haq : A.next q (E.loc q) with ⟨i', v', s'⟩ | ⟨r', i', k'⟩ | ⟨y', s'⟩
  all_goals
    have hq'' := haq
    rw [← hq'] at hq''
    have hp'' := hap
    rw [← hp'] at hp''
    first | rw [step_of_write hq''] | rw [step_of_read hq''] | rw [step_of_decide hq'']
    first | rw [step_of_write hp''] | rw [step_of_read hp''] | rw [step_of_decide hp'']
    first | rw [step_of_write hap] | rw [step_of_read hap] | rw [step_of_decide hap]
    first | rw [step_of_write haq] | rw [step_of_read haq] | rw [step_of_decide haq]
  -- in all cases but write/read the two configurations coincide; otherwise they differ only in
  -- the local state of the reader
  all_goals first
    | (refine ⟨p, fun x hx => ⟨?_, ?_⟩, ?_⟩ <;>
        (try simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx) <;>
        simp [Function.update_apply, Function.update_comm hpq] <;>
        split_ifs <;> simp_all; done)
    | (refine ⟨q, fun x hx => ⟨?_, ?_⟩, ?_⟩
       all_goals try simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
       all_goals simp [Function.update_apply]
       all_goals split_ifs <;> simp_all)

/-! ### Auxiliary combinatorics -/

omit [DecidableEq P] [DecidableEq K] in
/-- Discrete intermediate value theorem. -/
lemma exists_flip_nat (Q : ℕ → Prop) {m : ℕ} (h0 : ¬ Q 0) (hm : Q m) :
    ∃ i, i < m ∧ ¬ Q i ∧ Q (i + 1) := by
  induction m with
  | zero => exact absurd hm h0
  | succ m ih =>
    by_cases h : Q m
    · obtain ⟨i, hi, h1, h2⟩ := ih h
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨m, by omega, h, hm⟩

omit [DecidableEq P] [DecidableEq K] in
/-- Discrete intermediate value theorem along the prefixes of a list. -/
lemma exists_flip_list {α : Type} (Q : List α → Prop) (τ : List α) (h : ¬ (Q [] ↔ Q τ)) :
    ∃ τ' q, q ∈ τ ∧ ¬ (Q τ' ↔ Q (τ' ++ [q])) := by
  induction τ using List.reverseRecOn with
  | nil => exact absurd Iff.rfl h
  | append_singleton τ a ih =>
    by_cases h' : Q [] ↔ Q τ
    · exact ⟨τ, a, by simp, fun h'' => h (h'.trans h'')⟩
    · obtain ⟨τ', q, h2, h3⟩ := ih h'
      exact ⟨τ', q, by simp [h2], h3⟩

/-- If some extension of `C` decides `b`, then so does some extension in which the first step of
`p` comes right after a `p`-free schedule. -/
lemma can_pfree {C : Config A} {b : Bool} (h : Can C b) (p : P) :
    ∃ τ, p ∉ τ ∧ Can (A.run C (τ ++ [p])) b := by
  obtain ⟨ρ, q, hq⟩ := h
  induction ρ generalizing C with
  | nil => exact ⟨[], by simp, [], q, Alg.step_out_of_out _ _ (by simpa using hq)⟩
  | cons r ρ ih =>
    by_cases hr : r = p
    · subst hr
      exact ⟨[], by simp, ρ, q, by simpa using hq⟩
    · obtain ⟨τ, hτ, hc⟩ := ih (C := A.step r C) (by simpa using hq)
      exact ⟨r :: τ, by simp [Ne.symm hr, hτ], by simpa using hc⟩

/-! ### The valency argument -/

section Valency

variable [Fintype P] (hP : 2 ≤ Fintype.card P) (hA : A.Solves 1 binConsensus)
include hP hA

/-- Termination in the `1`-resilient model: after any reachable configuration, if `u` crashes,
some other process `w` decides. -/
lemma exists_decide_ne {C : Config A} (hC : Reach A C) (u : P) :
    ∃ τ : List P, (∀ q ∈ τ, q ≠ u) ∧ ∃ w, w ≠ u ∧ ∃ c, (A.run C τ).out w = some c := by
  obtain ⟨x, σ, rfl⟩ := hC
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) u
  obtain ⟨τ, hτ, hd⟩ :=
    hA.exists_decide ({u}ᶜ : Finset P) (by simp) x σ (u := w) (by simpa using hw)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hd
  exact ⟨τ, fun q hq => by simpa using hτ q hq, w, hw, c, by rwa [← Alg.run_append]⟩

/-- Every reachable configuration can decide some value. -/
lemma exists_can {C : Config A} (hC : Reach A C) : ∃ c, Can C c := by
  obtain ⟨u⟩ : Nonempty P := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨τ, -, w, -, c, hc⟩ := exists_decide_ne hP hA hC u
  exact ⟨c, τ, w, hc⟩

/-- Indistinguishability: if a reachable `C` and an arbitrary `D` agree outside one process `u`,
they can decide a common value (crash `u`). -/
lemma exists_can_of_agreeOn {C D : Config A} (hC : Reach A C) {u : P}
    (h : AgreeOn ({u}ᶜ : Set P) C D) : ∃ c, Can C c ∧ Can D c := by
  obtain ⟨τ, hτ, w, hw, c, hc⟩ := exists_decide_ne hP hA hC u
  have h' := h.run (σ := τ) (fun q hq => by simpa using hτ q hq)
  exact ⟨c, ⟨τ, w, hc⟩, ⟨τ, w, by rw [← (h'.1 w (by simpa using hw)).2]; exact hc⟩⟩

/-- Some initial configuration is bivalent. -/
lemma exists_biv_init : ∃ x : P → Bool, Biv (A.initCfg x) := by
  by_contra hne
  simp only [not_exists] at hne
  set e := Fintype.equivFin P
  let x : ℕ → P → Bool := fun i p => decide ((e p : ℕ) < i)
  let Q : ℕ → Prop := fun i => Can (A.initCfg (x i)) true
  have h0 : ¬ Q 0 := by
    intro h
    have hx : x 0 = fun _ => false := by funext p; simp [x]
    have := eq_of_can_init_const hA false (by rw [← hx]; exact h)
    simp at this
  have hm : Q (Fintype.card P) := by
    have hx : x (Fintype.card P) = fun _ => true := by funext p; simp [x, (e p).isLt]
    obtain ⟨c, hc⟩ := exists_can hP hA (reach_init (x (Fintype.card P)))
    rw [hx] at hc
    have := eq_of_can_init_const hA true hc
    subst this
    simpa [Q, hx] using hc
  obtain ⟨i, hi, hQi, hQi1⟩ := exists_flip_nat Q h0 hm
  have hagree : AgreeOn ({e.symm ⟨i, hi⟩}ᶜ : Set P) (A.initCfg (x i)) (A.initCfg (x (i + 1))) := by
    refine ⟨fun q hq => ⟨?_, rfl⟩, rfl⟩
    have hqi : (e q : ℕ) ≠ i := by
      intro h
      apply hq
      simp only [Set.mem_singleton_iff, Equiv.eq_symm_apply]
      exact Fin.ext h
    simp only [Alg.initCfg, x]
    congr 2
    exact propext (by omega)
  obtain ⟨c, hc1, hc2⟩ := exists_can_of_agreeOn hP hA (reach_init _) hagree
  cases c
  · exact not_can_not (hne _) hc2 hQi1
  · exact hQi hc1

/-- Every reachable bivalent configuration has, for every process `p`, a bivalent extension whose
last step is a step of `p`. -/
lemma exists_biv_ext {C : Config A} (hC : Reach A C) (hb : Biv C) (p : P) :
    ∃ τ, Biv (A.run C (τ ++ [p])) := by
  by_contra hne
  simp only [not_exists] at hne
  let Q : List P → Prop := fun τ => Can (A.run C (τ ++ [p])) true
  obtain ⟨τ1, hτ1p, hτ1⟩ := can_pfree hb.1 p
  obtain ⟨τ0, hτ0p, hτ0⟩ := can_pfree hb.2 p
  have hτ0' : ¬ Q τ0 := not_can_not (hne _) hτ0
  obtain ⟨τ, hτp, hflip⟩ : ∃ τ, p ∉ τ ∧ ¬ (Q [] ↔ Q τ) := by
    by_cases hQ : Q []
    · exact ⟨τ0, hτ0p, fun h => hτ0' (h.1 hQ)⟩
    · exact ⟨τ1, hτ1p, fun h => hQ (h.2 hτ1)⟩
  obtain ⟨τ', q, hq, h3⟩ := exists_flip_list Q τ hflip
  have hqp : p ≠ q := fun h => hτp (h ▸ hq)
  have hE : Reach A (A.run C τ') := hC.run _
  obtain ⟨u, hu⟩ := swap (A.run C τ') hqp
  obtain ⟨c, hc1, hc2⟩ := exists_can_of_agreeOn hP hA ((hE.step p).step q) hu
  have hc1' : Can (A.run C (τ' ++ [p])) c := by rw [Alg.run_concat]; exact hc1.of_step
  have hc2' : Can (A.run C ((τ' ++ [q]) ++ [p])) c := by
    rw [Alg.run_concat, Alg.run_concat]; exact hc2
  have key : ∀ ρ, Can (A.run C (ρ ++ [p])) c → (Q ρ ↔ c = true) := by
    intro ρ hρ
    cases c
    · simpa [Q] using not_can_not (hne ρ) hρ
    · simpa [Q] using hρ
  exact h3 ((key _ hc1').trans (key _ hc2').symm)

end Valency

end FLP

open FLP in
/-- **Lemma 2.1** (Fischer–Lynch–Paterson; Loui–Abu-Amara for shared memory): binary consensus
cannot be solved `1`-resiliently by `m ≥ 2` processes in the asynchronous read/write SWMR
model. -/
theorem Alg.not_solves_binConsensus {P K : Type} {V : K → Type} [Fintype P] [DecidableEq P]
    [DecidableEq K] (hP : 2 ≤ Fintype.card P) (A : Alg P K V Bool Bool) :
    ¬ A.Solves 1 binConsensus := by
  intro hA
  have hm : 0 < Fintype.card P := by omega
  set e := Fintype.equivFin P
  let pp : ℕ → P := fun i => e.symm ⟨i % Fintype.card P, Nat.mod_lt _ hm⟩
  obtain ⟨x0, hx0⟩ := exists_biv_init hP hA
  have hext : ∀ C : Config A, Reach A C ∧ Biv C → ∀ p, ∃ τ,
      Reach A (A.run C (τ ++ [p])) ∧ Biv (A.run C (τ ++ [p])) := fun C hC p => by
    obtain ⟨τ, hτ⟩ := exists_biv_ext hP hA hC.1 hC.2 p
    exact ⟨τ, hC.1.run _, hτ⟩
  choose! τf hτf using hext
  -- the bivalent configurations `Cs i`, each extending the previous one by the block `B i`
  let Cs : ℕ → Config A := fun n =>
    Nat.rec (motive := fun _ => Config A) (A.initCfg x0)
      (fun i C => A.run C (τf C (pp i) ++ [pp i])) n
  let B : ℕ → List P := fun i => τf (Cs i) (pp i) ++ [pp i]
  have hgood : ∀ i, Reach A (Cs i) ∧ Biv (Cs i) := by
    intro i
    induction i with
    | zero => exact ⟨reach_init _, hx0⟩
    | succ i ih => exact hτf _ ih _
  have hflat : ∀ j, Cs j = A.run (A.initCfg x0) (concatBlocks B j) := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [concatBlocks_succ, Alg.run_append, ← ih]
  have hB : ∀ i, B i ≠ [] := by simp [B]
  set σ := concatSched B hB
  have hinf : ∀ p, InfOften σ p := by
    intro p N
    set i := (e p : ℕ) + N * Fintype.card P
    have hpi : pp i = p := by
      simp only [pp, i, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (e p).isLt]
      simp
    refine ⟨(concatBlocks B i ++ τf (Cs i) (pp i)).length, ?_, ?_⟩
    · have := le_length_concatBlocks hB i
      simp only [List.length_append]
      have : N ≤ N * Fintype.card P := Nat.le_mul_of_pos_right N hm
      omega
    · have h1 : concatBlocks B (i + 1) = (concatBlocks B i ++ τf (Cs i) (pp i)) ++ [pp i] := by
        rw [concatBlocks_succ, List.append_assoc]
      have h2 := getElem?_concatBlocks hB (j := i + 1)
        (n := (concatBlocks B i ++ τf (Cs i) (pp i)).length) (by rw [h1]; simp)
      rw [h1, List.getElem?_concat_length] at h2
      rw [← hpi]
      exact (Option.some_injective _ h2).symm
  have hF : (Faulty σ).ncard ≤ 1 := by
    have : Faulty σ = ∅ := Set.eq_empty_of_forall_notMem (fun p hp => hp (hinf p))
    simp [this]
  obtain ⟨T, hT⟩ := hA.2 x0 σ hF (pp 0) (hinf _)
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hT
  obtain ⟨ρ, hρ⟩ := exists_pre_append_of_le σ (le_length_concatBlocks hB T)
  have hout : (Cs T).out (pp 0) = some c := by
    rw [hflat, ← pre_concatSched hB T, ← hρ, Alg.run_append]
    exact Alg.out_run_of_out _ _ hc
  have h1 := eq_of_out_of_can hA (hgood T).1 hout (hgood T).2.1
  have h2 := eq_of_out_of_can hA (hgood T).1 hout (hgood T).2.2
  exact Bool.noConfusion (h1.trans h2.symm)

end Cslib.SWMR
