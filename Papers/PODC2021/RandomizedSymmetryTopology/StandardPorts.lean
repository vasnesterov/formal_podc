import Papers.PODC2021.RandomizedSymmetryTopology.MessagePassing
import Cslib.Computability.Distributed.PortNumbering.Basic

/-!
# Lemma 4.3 and Corollary 4.4 in the standard port-numbering model

Fraigniaud, Gelles, Lotker, PODC 2021, Section 4.2, restated in CSLib's standard (two-sided)
port-numbering model `Cslib.PortNumbering`: the parties form the clique `Kₙ` with ports
`0, …, n - 2` at every party, a party may send different messages on different ports, and the
receiver learns the port number at the sender's end (`PNGraph.rport`). Algorithms are
deterministic, synchronous, with unbounded states and messages.

Randomness: party `v` is connected to source `α v`, and gets as its local input the whole random
stream `x (α v)` of its source (`x : Fin k → I`). This is stronger than the paper's model (an
algorithm may even look at future bits), which only strengthens the impossibility results.

## Main results

* `lemma_4_3_standard`: if `g > 0` divides every load `nⱼ`, then there is a port numbering of
  `Kₙ` such that, for every algorithm, every input assignment `x` of the sources and every round
  `t`, every class of parties in the same state has size divisible by `g`.
* `corollary_4_4_standard`: if `gcd(n₁, …, n_k) > 1`, there is a port numbering of `Kₙ` under
  which no algorithm ever elects a unique leader, for any realization of the sources.

## Proof

Since `g` divides every load, the parties can be arranged as `Fin g × Fin m` so that the source
depends only on the second coordinate (`exists_equiv_prod`). Placing party `(q, r)` at position
`r + m q` of the *circulant* clique on `ℤ/n` (port `i` of `a` leads to `a + i + 1`, arriving at
port `n - 2 - i`), the rotation `a ↦ a + m` is an automorphism (`isCovering_rotate`) preserving
the sources. Hence by `Algorithm.state_covering` it preserves all states, so every state class is
rotation-invariant, and all orbits of the rotation have size `g`.
-/

open Finset Cslib.PortNumbering

namespace Podc.RandomizedSymmetryTopology

/-- `G` is the clique `Kₙ` with ports `0, …, n - 2` at every node. -/
structure IsClique {n : ℕ} (G : PNGraph (Fin n)) : Prop where
  deg_eq : ∀ v, G.deg v = n - 1
  simple : G.IsSimple
  adj : ∀ v w, w ≠ v → ∃ i < n - 1, G.nbr v i = w

namespace StandardPorts

theorem mod_cases {x N : ℕ} (h : x < 2 * N) :
    (x < N ∧ x % N = x) ∨ (N ≤ x ∧ x % N = x - N) := by
  rcases lt_or_ge x N with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  · exact Or.inr ⟨h1, by rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]⟩

-- CSLib candidate (Cslib/Computability/Distributed/PortNumbering)
/-- The circulant clique on `Fin N`: port `i` of `a` leads to `a + i + 1 (mod N)`, at that node's
port `N - 2 - i`. -/
def circulant (N : ℕ) : PNGraph (Fin N) where
  deg _ := N - 1
  p a i := (⟨(a.val + i + 1) % N, Nat.mod_lt _ a.pos⟩, N - 2 - i)
  p_lt a i h := by dsimp only at h ⊢; omega
  p_p a i h := by
    dsimp only at h ⊢
    simp only [Prod.mk.injEq, Fin.ext_iff]
    refine ⟨?_, by omega⟩
    rw [add_assoc _ (N - 2 - i), Nat.mod_add_mod,
      show a.val + i + 1 + (N - 2 - i + 1) = a.val + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt a.isLt]

theorem circulant_nbr (N : ℕ) (a : Fin N) (i : ℕ) :
    ((circulant N).nbr a i).val = (a.val + i + 1) % N := rfl

theorem isClique_circulant (N : ℕ) : IsClique (circulant N) where
  deg_eq _ := rfl
  simple := by
    refine ⟨fun a i hi h => ?_, fun a i j hi hj h => ?_⟩
    · change i < N - 1 at hi
      rw [Fin.ext_iff, circulant_nbr] at h
      have := a.isLt
      rcases mod_cases (x := a.val + i + 1) (N := N) (by omega) with h1 | h1 <;> omega
    · change i < N - 1 at hi
      change j < N - 1 at hj
      rw [Fin.ext_iff, circulant_nbr, circulant_nbr] at h
      have := a.isLt
      rcases mod_cases (x := a.val + i + 1) (N := N) (by omega) with h1 | h1 <;>
      rcases mod_cases (x := a.val + j + 1) (N := N) (by omega) with h2 | h2 <;> omega
  adj a w hw := by
    have ha := a.isLt
    have hw' := w.isLt
    have hne : w.val ≠ a.val := fun h => hw (Fin.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · refine ⟨w.val + N - a.val - 1, by omega, ?_⟩
      rw [Fin.ext_iff, circulant_nbr]
      rcases mod_cases (x := a.val + (w.val + N - a.val - 1) + 1) (N := N) (by omega)
        with h1 | h1 <;> omega
    · refine ⟨w.val - a.val - 1, by omega, ?_⟩
      rw [Fin.ext_iff, circulant_nbr]
      rcases mod_cases (x := a.val + (w.val - a.val - 1) + 1) (N := N) (by omega)
        with h1 | h1 <;> omega

/-- The rotation `a ↦ a + c (mod N)`. -/
def rotate (N c : ℕ) (a : Fin N) : Fin N := ⟨(a.val + c) % N, Nat.mod_lt _ a.pos⟩

/-- Rotations are automorphisms of the circulant clique. -/
theorem isCovering_rotate (N c : ℕ) : (circulant N).IsCovering (circulant N) (rotate N c) where
  deg_eq _ := rfl
  p_eq a i _ := by
    simp only [circulant, rotate, PNGraph.nbr, PNGraph.rport, Prod.mk.injEq, Fin.ext_iff,
      and_true]
    rw [add_assoc, Nat.mod_add_mod, Nat.mod_add_mod]
    congr 1
    omega

-- CSLib candidate (Cslib/Computability/Distributed/PortNumbering)
/-- The pull-back of a port-numbered graph along a bijection of the nodes. -/
def comapEquiv {V W : Type*} (e : V ≃ W) (H : PNGraph W) : PNGraph V where
  deg v := H.deg (e v)
  p v i := (e.symm (H.nbr (e v) i), H.rport (e v) i)
  p_lt v i h := by simpa using H.rport_lt h
  p_p v i h := by simp [H.nbr_nbr h, H.rport_rport h]

theorem isCovering_comapEquiv {V W : Type*} (e : V ≃ W) (H : PNGraph W) :
    (comapEquiv e H).IsCovering H e where
  deg_eq _ := rfl
  p_eq v i _ := by simp [comapEquiv, PNGraph.nbr, PNGraph.rport]

theorem isClique_comapEquiv {n N : ℕ} (e : Fin n ≃ Fin N) {H : PNGraph (Fin N)}
    (hH : IsClique H) : IsClique (comapEquiv e H) := by
  have hn : n = N := by simpa using Fintype.card_congr e
  subst hn
  refine ⟨fun v => hH.deg_eq (e v), ⟨fun v i hi h => ?_, fun v i j hi hj h => ?_⟩,
    fun v w hw => ?_⟩
  · have h' : e.symm (H.nbr (e v) i) = v := h
    exact hH.simple.1 (e v) i hi ((Equiv.symm_apply_eq e).1 h')
  · exact hH.simple.2 (e v) i j hi hj (e.symm.injective h)
  · obtain ⟨i, hi, h⟩ := hH.adj (e v) (e w) (e.injective.ne hw)
    exact ⟨i, hi, by change e.symm _ = w; rw [h]; simp⟩

/-- An invariant set of the rotation by `m` of `Fin (g * m)` has size divisible by `g`. -/
theorem dvd_card_of_rotate_invariant {g m : ℕ} (hg : 0 < g) (S : Finset (Fin (g * m)))
    (hS : ∀ a, rotate (g * m) m a ∈ S ↔ a ∈ S) : g ∣ S.card := by
  have step : ∀ (q : ℕ) (hq : q + 1 < g) (r : Fin m),
      rotate (g * m) m (finProdFinEquiv (⟨q, by omega⟩, r)) =
        finProdFinEquiv (⟨q + 1, hq⟩, r) := by
    intro q hq r
    ext
    simp only [rotate, finProdFinEquiv_apply_val]
    have : r.val + m * (q + 1) < g * m := by
      have := r.isLt
      have : m * (q + 2) ≤ m * g := Nat.mul_le_mul_left _ hq
      nlinarith
    rw [← Nat.mod_eq_of_lt this]
    congr 1
    ring
  have mem : ∀ (q : ℕ) (hq : q < g) (r : Fin m),
      finProdFinEquiv (⟨q, hq⟩, r) ∈ S ↔ finProdFinEquiv (⟨0, hg⟩, r) ∈ S := by
    intro q
    induction q with
    | zero => intros; rfl
    | succ q ih =>
      intro hq r
      rw [← step q hq r, hS, ih]
  set T := univ.filter fun r : Fin m => finProdFinEquiv (⟨0, hg⟩, r) ∈ S
  have : S = (univ ×ˢ T).map finProdFinEquiv.toEmbedding := by
    ext a
    obtain ⟨⟨q, r⟩, rfl⟩ := finProdFinEquiv.surjective a
    simp [T, mem q.val q.isLt r]
  rw [this, card_map, card_product, card_univ, Fintype.card_fin]
  exact dvd_mul_right _ _

/-- If `g` divides every load, the parties can be arranged as `Fin g × Fin m` such that the source
of a party depends only on its second coordinate. -/
theorem exists_equiv_prod {n k g : ℕ} (α : Fin n → Fin k) (hg : ∀ j, g ∣ load α j) :
    ∃ m, ∃ e : Fin n ≃ Fin g × Fin m, ∃ β : Fin m → Fin k, ∀ x, β (e x).2 = α x := by
  classical
  set c : Fin k → ℕ := fun j => load α j / g
  let β : Fin (∑ j, c j) → Fin k := fun r => (finSigmaFinEquiv.symm r).1
  have hβ : ∀ j, (univ.filter fun r => β r = j).card = c j := by
    intro j
    rw [← Fintype.card_subtype, ← Fintype.card_fin (c j)]
    exact Fintype.card_congr ((finSigmaFinEquiv.symm.subtypeEquiv fun r => Iff.rfl).trans
      (Equiv.sigmaSubtype j))
  have hcard : ∀ j, Fintype.card {x // α x = j} =
      Fintype.card {p : Fin g × Fin (∑ j, c j) // β p.2 = j} := by
    intro j
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have : (univ.filter fun p : Fin g × Fin (∑ j, c j) => β p.2 = j) =
        univ ×ˢ univ.filter fun r => β r = j := by
      ext p; simp
    rw [this, card_product, hβ, card_univ, Fintype.card_fin, Nat.mul_div_cancel' (hg j)]
    rfl
  refine ⟨∑ j, c j, Equiv.ofFiberEquiv (fun j => Fintype.equivOfCardEq (hcard j)), β,
    fun x => Equiv.ofFiberEquiv_map (f := α) (g := fun p : Fin g × Fin (∑ j, c j) => β p.2) _ x⟩

end StandardPorts

open StandardPorts

open Classical in
/-- **Lemma 4.3 (standard port model).** If `g > 0` divides the number `nⱼ` of parties connected
to every source `j`, then there is a port numbering of the clique `Kₙ` such that, whatever the
algorithm, the realization `x` of the sources and the round `t`, every class of parties in the same
state (in the paper: every facet of the realization of `π̃(ρ)`) has size divisible by `g`. -/
theorem lemma_4_3_standard {n k : ℕ} (α : Fin n → Fin k) (g : ℕ) (hg0 : 0 < g)
    (hg : ∀ j, g ∣ load α j) :
    ∃ G : PNGraph (Fin n), IsClique G ∧
      ∀ {I O : Type} (A : Algorithm I O) (x : Fin k → I) (t : ℕ) (v : Fin n),
        g ∣ (univ.filter fun w => A.state G (x ∘ α) t w = A.state G (x ∘ α) t v).card := by
  obtain ⟨m, e₁, β, hβ⟩ := exists_equiv_prod α hg
  let e : Fin n ≃ Fin (g * m) := e₁.trans finProdFinEquiv
  refine ⟨comapEquiv e (circulant (g * m)), isClique_comapEquiv e (isClique_circulant _), ?_⟩
  intro I O A x t v
  let y : Fin (g * m) → I := fun a => x (β a.modNat)
  have hy : x ∘ α = y ∘ e := by
    funext w
    simp only [Function.comp_apply, y, e, Equiv.trans_apply]
    rw [← hβ w]
    congr 2
    obtain ⟨q, r⟩ := e₁ w
    ext
    simp [Fin.modNat, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt r.isLt]
  have hrot : y ∘ rotate (g * m) m = y := by
    funext a
    simp only [Function.comp_apply, y]
    congr 2
    ext
    simp only [Fin.modNat, rotate]
    rw [Nat.mod_mod_of_dvd _ (Dvd.intro_left g rfl), Nat.add_mod_right]
  have key : ∀ w, A.state (comapEquiv e (circulant (g * m))) (x ∘ α) t w =
      A.state (circulant (g * m)) y t (e w) := by
    rw [hy]; exact A.state_covering (isCovering_comapEquiv e _) y t
  have key2 : ∀ a, A.state (circulant (g * m)) y t (rotate (g * m) m a) =
      A.state (circulant (g * m)) y t a := by
    intro a
    have := A.state_covering (isCovering_rotate (g * m) m) y t a
    rw [hrot] at this
    exact this.symm
  set S := univ.filter fun a => A.state (circulant (g * m)) y t a =
    A.state (circulant (g * m)) y t (e v)
  have hS : (univ.filter fun w => A.state (comapEquiv e (circulant (g * m))) (x ∘ α) t w =
      A.state (comapEquiv e (circulant (g * m))) (x ∘ α) t v) = S.map e.symm.toEmbedding := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_map_equiv, Equiv.symm_symm, S, key]
  rw [hS, card_map]
  exact dvd_card_of_rotate_invariant hg0 S fun a => by simp [S, key2]

/-- **Corollary 4.4 (standard port model).** If `gcd(n₁, …, n_k) > 1`, then there is a port
numbering of the clique `Kₙ` under which no deterministic algorithm, run on the parties' random
streams, ever elects a unique leader: for every realization `ω` of the sources and every round `T`,
the outputs are not of the form "exactly one party outputs `true`". -/
theorem corollary_4_4_standard {n k : ℕ} (α : Fin n → Fin k) (hg : 1 < univ.gcd (load α)) :
    ∃ G : PNGraph (Fin n), IsClique G ∧
      ∀ (A : Algorithm (ℕ → Bool) Bool) (ω : Stream k) (T : ℕ),
        ¬ ∃! v, A.eval G T (fun v s => ω s (α v)) v = true := by
  classical
  obtain ⟨G, hG, h⟩ := lemma_4_3_standard α (univ.gcd (load α)) (by omega)
    (fun j => Finset.gcd_dvd (mem_univ j))
  refine ⟨G, hG, fun A ω T ⟨v, hv, huniq⟩ => ?_⟩
  have hd := h A (fun j s => ω s j) T v
  have : (univ.filter fun w => A.state G ((fun j s => ω s j) ∘ α) T w =
      A.state G ((fun j s => ω s j) ∘ α) T v) = {v} := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hw
      apply huniq
      simp only [Algorithm.eval] at hv ⊢
      exact hw ▸ hv
    · rintro rfl; rfl
  rw [this, card_singleton] at hd
  have := Nat.le_of_dvd one_pos hd
  omega

/-- Non-vacuity: four parties, two sources with two parties each (`gcd = 2`). -/
def StandardPorts.α₄ : Fin 4 → Fin 2 := fun i => if i.val < 2 then 0 else 1

theorem StandardPorts.gcd_load_α₄ : univ.gcd (load α₄) = 2 := by decide

example : ∃ G : PNGraph (Fin 4), IsClique G ∧
    ∀ (A : Algorithm (ℕ → Bool) Bool) (ω : Stream 2) (T : ℕ),
      ¬ ∃! v, A.eval G T (fun v s => ω s (α₄ v)) v = true :=
  corollary_4_4_standard α₄ (by rw [gcd_load_α₄]; omega)

end Podc.RandomizedSymmetryTopology
