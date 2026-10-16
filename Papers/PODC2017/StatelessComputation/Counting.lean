import Papers.PODC2017.StatelessComputation.Model

/-!
# Theorem 5.10: hard functions need linear label complexity on bounded-degree graphs

Dolev, Erdmann, Lutz, Schapira, Zair, *Stateless Computation*, PODC 2017, Section 5.

**Theorem 5.10.** Let `(Gₙ)` be a family of graphs of maximal degree `k`. Then for every `n > 8`
there is a function `f : {0,1}ⁿ → {0,1}` that cannot be computed by a stateless protocol on `Gₙ`
with label complexity `Lₙ < n / (4k)`.

We prove it for every `n ≥ 6` (the counting argument fails for `n = 5`, `k = 1`), for one `f`
that works simultaneously for *all* label spaces `L` with `|L|^(4k) < 2ⁿ` (i.e.
`log₂ |L| < n / (4k)`), and with "computes" in the weakest (synchronous) sense
`Protocol.SyncComputes`. Proof: a protocol computes at most one function; protocols over `L`
transport to protocols over `Fin |L|`; there are at most `(2 s^k)^(2 n s^k)` protocols over
`Fin s`; summing over all admissible `s` gives fewer than `2^(2^n)` functions.
-/

namespace StatelessComputation
namespace Counting

open Finset

universe u

variable {n : ℕ} {G : Digraph (Fin n)}

/-- A protocol is its vector of reaction functions. -/
def protocolEquiv {V : Type*} {G : Digraph V} {L X Y : Type*} :
    Protocol G L X Y ≃ ((i : V) → (InNbr G i → L) → X → (OutNbr G i → L) × Y) where
  toFun P := P.δ
  invFun δ := ⟨δ⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A protocol computes at most one function (there is a node and an initial labeling). -/
lemma eq_of_syncComputes {L : Type*} [Nonempty L] (hn : 0 < n) {P : Protocol G L Bool Bool}
    {f g : (Fin n → Bool) → Bool} (hf : P.SyncComputes f) (hg : P.SyncComputes g) : f = g := by
  funext x
  obtain ⟨T1, h1⟩ := hf x (fun _ => Classical.arbitrary L) ⟨0, hn⟩
  obtain ⟨T2, h2⟩ := hg x (fun _ => Classical.arbitrary L) ⟨0, hn⟩
  rw [← h1 (max T1 T2) (le_max_left _ _), h2 (max T1 T2) (le_max_right _ _)]

/-- Transport of a protocol along a bijection of label spaces. -/
def transport {L L' : Type*} (e : L ≃ L') (P : Protocol G L Bool Bool) :
    Protocol G L' Bool Bool :=
  ⟨fun i inl b => ((fun w => e ((P.δ i (fun u => e.symm (inl u)) b).1 w)),
    (P.δ i (fun u => e.symm (inl u)) b).2)⟩

lemma transport_syncRun {L L' : Type*} (e : L ≃ L') (P : Protocol G L Bool Bool)
    (x : Fin n → Bool) (ℓ0 : Labeling G L) (t : ℕ) :
    (transport e P).syncRun x (fun a => e (ℓ0 a)) t = fun a => e (P.syncRun x ℓ0 t a) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Protocol.syncRun_succ, Protocol.syncRun_succ, ih]
    funext a
    simp [Protocol.syncStep, transport, inLab]
    rfl

lemma transport_out {L L' : Type*} (e : L ≃ L') (P : Protocol G L Bool Bool)
    (x : Fin n → Bool) (ℓ : Labeling G L) (i : Fin n) :
    (transport e P).out x (fun a => e (ℓ a)) i = P.out x ℓ i := by
  simp [Protocol.out, transport, inLab]
  rfl

lemma transport_syncComputes {L L' : Type*} (e : L ≃ L') {P : Protocol G L Bool Bool}
    {f : (Fin n → Bool) → Bool} (hP : P.SyncComputes f) : (transport e P).SyncComputes f := by
  intro x ℓ0' i
  obtain ⟨T, hT⟩ := hP x (fun a => e.symm (ℓ0' a)) i
  refine ⟨T, fun t ht => ?_⟩
  have h : ℓ0' = fun a => e (e.symm (ℓ0' a)) := by simp
  rw [h, transport_syncRun, transport_out]
  exact hT t ht

variable [DecidableRel G.Adj]

noncomputable instance (s : ℕ) : Fintype (Protocol G (Fin s) Bool Bool) :=
  Fintype.ofEquiv _ protocolEquiv.symm

/-- Number of protocols over `Fin s` on a graph with in- and out-degrees at most `k`. -/
lemma card_protocol_le {k s : ℕ} (hs : 1 ≤ s)
    (hin : ∀ i, (univ.filter (G.Adj · i)).card ≤ k)
    (hout : ∀ i, (univ.filter (G.Adj i ·)).card ≤ k) :
    Fintype.card (Protocol G (Fin s) Bool Bool) ≤ (2 * s ^ k) ^ (2 * n * s ^ k) := by
  rw [Fintype.card_congr protocolEquiv, Fintype.card_pi]
  have hfac : ∀ i : Fin n,
      Fintype.card ((InNbr G i → Fin s) → Bool → (OutNbr G i → Fin s) × Bool) ≤
        (2 * s ^ k) ^ (2 * s ^ k) := by
    intro i
    have hi : Fintype.card (InNbr G i) = (univ.filter (G.Adj · i)).card :=
      Fintype.card_subtype _
    have ho : Fintype.card (OutNbr G i) = (univ.filter (G.Adj i ·)).card :=
      Fintype.card_subtype _
    simp only [Fintype.card_fun, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    rw [hi, ho]
    set d := (univ.filter (G.Adj · i)).card
    set o := (univ.filter (G.Adj i ·)).card
    have hd : s ^ d ≤ s ^ k := Nat.pow_le_pow_right hs (hin i)
    have hoo : s ^ o ≤ s ^ k := Nat.pow_le_pow_right hs (hout i)
    have hpos : 1 ≤ 2 * s ^ k := by have := Nat.one_le_pow k s hs; omega
    calc ((s ^ o * 2) ^ 2) ^ s ^ d = (s ^ o * 2) ^ (2 * s ^ d) := by rw [← pow_mul]
      _ ≤ (2 * s ^ k) ^ (2 * s ^ d) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 * s ^ k) ^ (2 * s ^ k) := Nat.pow_le_pow_right hpos (by omega)
  calc ∏ i, Fintype.card ((InNbr G i → Fin s) → Bool → (OutNbr G i → Fin s) × Bool)
      ≤ ((2 * s ^ k) ^ (2 * s ^ k)) ^ (univ : Finset (Fin n)).card :=
        Finset.prod_le_pow_card _ _ _ (fun i _ => hfac i)
    _ = (2 * s ^ k) ^ (2 * n * s ^ k) := by
        rw [card_univ, Fintype.card_fin, ← pow_mul]; ring_nf

end Counting

/-! ### Arithmetic -/

namespace Counting

lemma aux_poly (n : ℕ) (hn : 8 ≤ n) : ((2 * n + 1) * (n + 4)) ^ 4 ≤ 256 * 8 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : 2 * ((2 * (n + 1) + 1) * (n + 1 + 4)) ≤ 3 * ((2 * n + 1) * (n + 4)) := by
      nlinarith
    have h2 := Nat.pow_le_pow_left h1 4
    rw [mul_pow, mul_pow 3] at h2
    rw [show (8 : ℕ) ^ (n + 1) = 8 ^ n * 8 from pow_succ 8 n]
    have : 16 * ((2 * (n + 1) + 1) * (n + 1 + 4)) ^ 4 ≤ 81 * ((2 * n + 1) * (n + 4)) ^ 4 := by
      simpa using h2
    omega

/-- `(n + 4)(2nM + 1) ≤ 4 · 2ⁿ` whenever `M⁴ < 2ⁿ`, `1 ≤ M`, `n ≥ 6`. -/
lemma aux_exp {n M : ℕ} (hn : 6 ≤ n) (hM : 1 ≤ M) (hM4 : M ^ 4 < 2 ^ n) :
    (n + 4) * (2 * n * M + 1) ≤ 4 * 2 ^ n := by
  rcases (show n = 6 ∨ n = 7 ∨ 8 ≤ n by omega) with rfl | rfl | h8
  · have : M ≤ 2 := by
      by_contra h
      have : 3 ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left (by omega) 4
      norm_num at hM4 this; omega
    interval_cases M <;> norm_num
  · have : M ≤ 3 := by
      by_contra h
      have : 4 ^ 4 ≤ M ^ 4 := Nat.pow_le_pow_left (by omega) 4
      norm_num at hM4 this; omega
    interval_cases M <;> norm_num
  · have hle : (n + 4) * (2 * n * M + 1) ≤ (2 * n + 1) * (n + 4) * M := by nlinarith
    refine hle.trans (le_of_lt ?_)
    rw [← Nat.pow_lt_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)]
    have hp := aux_poly n h8
    calc ((2 * n + 1) * (n + 4) * M) ^ 4 = ((2 * n + 1) * (n + 4)) ^ 4 * M ^ 4 := by ring
      _ < ((2 * n + 1) * (n + 4)) ^ 4 * 2 ^ n :=
          Nat.mul_lt_mul_of_pos_left hM4 (by positivity)
      _ ≤ 256 * 8 ^ n * 2 ^ n := Nat.mul_le_mul_right _ hp
      _ = (4 * 2 ^ n) ^ 4 := by
          rw [mul_pow, ← pow_mul, show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_mul, mul_assoc,
            ← pow_add]
          norm_num; ring_nf

/-- The counting inequality: `M · (2M)^(2nM) < 2^(2ⁿ)` when `M⁴ < 2ⁿ`, `n ≥ 6`. -/
lemma aux_count {n M : ℕ} (hn : 6 ≤ n) (hM : 1 ≤ M) (hM4 : M ^ 4 < 2 ^ n) :
    M * (2 * M) ^ (2 * n * M) < 2 ^ 2 ^ n := by
  have h1 : M * (2 * M) ^ (2 * n * M) ≤ (2 * M) ^ (2 * n * M + 1) := by
    rw [pow_succ, mul_comm]; exact Nat.mul_le_mul_left _ (by omega)
  refine lt_of_le_of_lt h1 ?_
  rw [← Nat.pow_lt_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)]
  set E := 2 * n * M + 1
  calc ((2 * M) ^ E) ^ 4 = (16 * M ^ 4) ^ E := by rw [← pow_mul, mul_comm E, pow_mul]; ring
    _ < (16 * 2 ^ n) ^ E := Nat.pow_lt_pow_left (by omega) (by omega)
    _ = 2 ^ ((n + 4) * E) := by
        rw [show (16 : ℕ) = 2 ^ 4 from rfl, ← pow_add, ← pow_mul, add_comm 4 n]
    _ ≤ 2 ^ (4 * 2 ^ n) := Nat.pow_le_pow_right (by norm_num) (aux_exp hn hM hM4)
    _ = (2 ^ 2 ^ n) ^ 4 := by rw [← pow_mul, mul_comm]

end Counting

open Counting

/-- Theorem 5.10 of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17], label-space form. On any
digraph with `n ≥ 6` nodes and all in- and out-degrees at most `k ≥ 1`, there is a Boolean
function `f` that no stateless protocol with a label space `L` satisfying `|L|^(4k) < 2ⁿ`
(i.e. label complexity `log₂ |L| < n / (4k)`) computes, even under the synchronous schedule. -/
theorem exists_hard_function {n k : ℕ} (hn : 6 ≤ n) (hk : 1 ≤ k) (G : Digraph (Fin n))
    [DecidableRel G.Adj]
    (hin : ∀ i, (Finset.univ.filter (G.Adj · i)).card ≤ k)
    (hout : ∀ i, (Finset.univ.filter (G.Adj i ·)).card ≤ k) :
    ∃ f : (Fin n → Bool) → Bool, ∀ (L : Type u) [Fintype L] [Nonempty L],
      Fintype.card L ^ (4 * k) < 2 ^ n → ∀ P : Protocol G L Bool Bool, ¬ P.SyncComputes f := by
  classical
  -- the largest admissible label-space size
  set S := Nat.findGreatest (fun s => s ^ (4 * k) < 2 ^ n) (2 ^ n) with hS
  have h1n : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
  have hS1 : 1 ≤ S := Nat.le_findGreatest (by omega) (by simpa using h1n)
  have hSspec : S ^ (4 * k) < 2 ^ n := Nat.findGreatest_spec (P := fun s => s ^ (4 * k) < 2 ^ n)
    (m := 1) (by omega) (by simpa using h1n)
  set M := S ^ k
  have hM1 : 1 ≤ M := Nat.one_le_pow _ _ hS1
  have hM4 : M ^ 4 < 2 ^ n := by rw [← pow_mul, mul_comm]; exact hSspec
  have hSM : S ≤ M := Nat.le_self_pow (by omega) S
  -- the function computed by a protocol (if any)
  let fn : (s : ℕ) → Protocol G (Fin s) Bool Bool → ((Fin n → Bool) → Bool) := fun _ P =>
    if h : ∃ f, P.SyncComputes f then h.choose else fun _ => false
  let Comp : Finset ((Fin n → Bool) → Bool) :=
    (Finset.Icc 1 S).biUnion fun s => (Finset.univ : Finset (Protocol G (Fin s) Bool Bool)).image
      (fn s)
  have hcard : Comp.card < Fintype.card ((Fin n → Bool) → Bool) := by
    calc Comp.card ≤ ∑ s ∈ Finset.Icc 1 S,
          ((Finset.univ : Finset (Protocol G (Fin s) Bool Bool)).image (fn s)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ s ∈ Finset.Icc 1 S, (2 * M) ^ (2 * n * M) := by
          refine Finset.sum_le_sum fun s hs => ?_
          have hs1 : 1 ≤ s := (Finset.mem_Icc.1 hs).1
          have hsM : s ^ k ≤ M := Nat.pow_le_pow_left (Finset.mem_Icc.1 hs).2 k
          calc _ ≤ (Finset.univ : Finset (Protocol G (Fin s) Bool Bool)).card :=
                Finset.card_image_le
            _ = Fintype.card (Protocol G (Fin s) Bool Bool) := Finset.card_univ
            _ ≤ (2 * s ^ k) ^ (2 * n * s ^ k) := card_protocol_le hs1 hin hout
            _ ≤ (2 * M) ^ (2 * n * s ^ k) := Nat.pow_le_pow_left (by omega) _
            _ ≤ (2 * M) ^ (2 * n * M) :=
                Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ hsM)
      _ = S * (2 * M) ^ (2 * n * M) := by simp
      _ ≤ M * (2 * M) ^ (2 * n * M) := Nat.mul_le_mul_right _ hSM
      _ < 2 ^ 2 ^ n := aux_count hn hM1 hM4
      _ = Fintype.card ((Fin n → Bool) → Bool) := by simp
  obtain ⟨f, hf⟩ : ∃ f, f ∉ Comp := by
    by_contra h
    push Not at h
    have : (Finset.univ : Finset ((Fin n → Bool) → Bool)) ⊆ Comp := fun f _ => h f
    have := Finset.card_le_card this
    rw [Finset.card_univ] at this
    omega
  refine ⟨f, fun L _ _ hL P hP => hf ?_⟩
  set s := Fintype.card L
  have hs1 : 1 ≤ s := Fintype.card_pos
  have hsS : s ≤ S := Nat.le_findGreatest
    (le_of_lt (lt_of_le_of_lt (Nat.le_self_pow (by omega) s) hL)) hL
  let e : L ≃ Fin s := Fintype.equivFin L
  have hP' := transport_syncComputes e hP
  have hex : ∃ g, (transport e P).SyncComputes g := ⟨f, hP'⟩
  have hfn : fn s (transport e P) = f := by
    simp only [fn, hex, ↓reduceDIte]
    exact eq_of_syncComputes (by omega) hex.choose_spec hP'
  exact Finset.mem_biUnion.2 ⟨s, Finset.mem_Icc.2 ⟨hs1, hsS⟩,
    Finset.mem_image.2 ⟨transport e P, Finset.mem_univ _, hfn⟩⟩

/-- Theorem 5.10 of [Dolev–Erdmann–Lutz–Schapira–Zair, PODC'17], in the paper's form with
label complexity `Lₙ = log₂ |L|`: there is `f` that no protocol with `Lₙ < n / (4k)` computes. -/
theorem exists_hard_function_logb {n k : ℕ} (hn : 6 ≤ n) (hk : 1 ≤ k) (G : Digraph (Fin n))
    [DecidableRel G.Adj]
    (hin : ∀ i, (Finset.univ.filter (G.Adj · i)).card ≤ k)
    (hout : ∀ i, (Finset.univ.filter (G.Adj i ·)).card ≤ k) :
    ∃ f : (Fin n → Bool) → Bool, ∀ (L : Type u) [Fintype L] [Nonempty L],
      Real.logb 2 (Fintype.card L) < (n : ℝ) / (4 * k) →
        ∀ P : Protocol G L Bool Bool, ¬ P.SyncComputes f := by
  obtain ⟨f, hf⟩ := exists_hard_function.{u} hn hk G hin hout
  refine ⟨f, fun L _ _ hL => hf L ?_⟩
  have hc : (0 : ℝ) < Fintype.card L := by exact_mod_cast Fintype.card_pos
  have hk' : (0 : ℝ) < 4 * k := by have : (1 : ℝ) ≤ k := by exact_mod_cast hk
                                   linarith
  have h1 : Real.logb 2 ((Fintype.card L : ℝ) ^ (4 * k)) < n := by
    rw [Real.logb_pow]
    rw [lt_div_iff₀ hk'] at hL
    push_cast; linarith
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_natCast] at h1
  exact_mod_cast h1

end StatelessComputation
