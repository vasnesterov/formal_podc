import Papers.PODC2012.ByzantineLinearCoding.Theorem1

/-!
# Instances of Theorem 1: Galois fields `GF(2^{L/ρ})` and complete networks

* `theorem_1_galois`: Theorem 1 with the paper's field `GF(2^{L/ρ})`, i.e. the bound
  `1 - C(n, n-f) (n-f-1) ρ / 2^{L/ρ}`.
* `TreePacking.star`: if all links inside `H` have capacity `≥ ρ`, the `ρ` stars centred at one
  node of `H` are edge-disjoint spanning trees (non-vacuity of the packing hypothesis).
* `theorem_1_complete`: Theorem 1 for networks in which every link has capacity `≥ ρ`, with no
  packing hypothesis left.
-/

namespace Podc.ByzantineLinearCoding

open Finset Cslib.Probability

variable {V : Type*} [DecidableEq V]

/-- `ρ` stars centred at the root: edge `r` of tree `q` is unit `q` of the link from the `r`-th
non-root node to the root. -/
noncomputable def TreePacking.star (z : V → V → ℕ) (H : Finset V) (ρ : ℕ) (hH : H.Nonempty)
    (hz : ∀ a ∈ H, ∀ b ∈ H, a ≠ b → ρ ≤ z a b) : TreePacking z H ρ :=
  let w := #H - 1
  have hw : #H = w + 1 := by have := hH.card_pos; omega
  let e : Fin (w + 1) ≃ H := (finCongr hw.symm).trans H.equivFin.symm
  let node : Fin (w + 1) ↪ V := ⟨fun i => (e i : V), fun i j h => e.injective (Subtype.ext h)⟩
  have hne : ∀ r : Fin w, node r.castSucc ≠ node (Fin.last w) := fun r h =>
    (Fin.castSucc_lt_last r).ne (node.injective h)
  { w := w
    node := node
    mem_iff := fun v => ⟨fun hv => ⟨e.symm ⟨v, hv⟩, show ((e (e.symm ⟨v, hv⟩) : H) : V) = v by rw [Equiv.apply_symm_apply]⟩,
      by rintro ⟨i, rfl⟩; exact (e i).2⟩
    sym := fun rq => ⟨(node rq.1.castSucc, node (Fin.last w)),
      Fin.castLE (hz _ (e _).2 _ (e _).2 (hne rq.1)) rq.2⟩
    sym_inj := by
      rintro ⟨r, q⟩ ⟨r', q'⟩ h
      simp only [Sigma.mk.inj_iff, Prod.mk.injEq] at h
      obtain ⟨⟨h1, -⟩, h2⟩ := h
      have hr : r = r' := Fin.castSucc_injective _ (node.injective h1)
      subst hr
      have := Fin.castLE_injective _ (eq_of_heq h2)
      rw [this]
    tail_mem := fun x => (e _).2
    head_mem := fun x => (e _).2
    connected := by
      intro q v hv
      obtain ⟨j, rfl⟩ : ∃ j, node j = v := ⟨e.symm ⟨v, hv⟩, show ((e (e.symm ⟨v, hv⟩) : H) : V) = v by rw [Equiv.apply_symm_apply]⟩
      induction j using Fin.lastCases with
      | last => exact Relation.ReflTransGen.refl
      | cast r => exact Relation.ReflTransGen.single ⟨r, Or.inr ⟨rfl, rfl⟩⟩ }

variable [Fintype V]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Theorem 1 for networks with all capacities `≥ ρ`** (e.g. complete networks): no packing
hypothesis is needed. -/
theorem theorem_1_complete {n f ρ : ℕ} (hV : Fintype.card V = n) (hf : 3 * f < n)
    (z : V → V → ℕ) (hz : ∀ a b, a ≠ b → ρ ≤ z a b) (Vk : Finset V) (disp : V → V → Prop) :
    1 - ((n.choose (n - f) * (n - f - 1) * ρ : ℕ) : ℝ) / Fintype.card F ≤
      uprob (fun c : Coding z ρ F => Correct z Vk disp f c) := by
  refine theorem_1 hV hf z Vk disp fun H hH => ⟨TreePacking.star z H ρ ?_ fun a _ b _ => hz a b⟩
  rw [← card_pos, (mem_Omega.1 hH).1.2]
  omega

/-- **Theorem 1** with the paper's field `GF(2^{L/ρ})` (`ρ ∣ L`, `0 < L`): the coding is correct
with probability `≥ 1 - 2^{-L/ρ} · C(n, n-f) (n-f-1) ρ`. -/
theorem theorem_1_galois {n f ρ L : ℕ} (hV : Fintype.card V = n) (hf : 3 * f < n)
    (hρL : ρ ∣ L) (hL : 0 < L)
    [Fintype (GaloisField 2 (L / ρ))] [DecidableEq (GaloisField 2 (L / ρ))]
    (z : V → V → ℕ) (Vk : Finset V) (disp : V → V → Prop)
    (hpack : ∀ H ∈ Omega Vk disp (n - f), Nonempty (TreePacking z H ρ)) :
    1 - ((n.choose (n - f) * (n - f - 1) * ρ : ℕ) : ℝ) / 2 ^ (L / ρ) ≤
      uprob (fun c : Coding z ρ (GaloisField 2 (L / ρ)) => Correct z Vk disp f c) := by
  have hk : L / ρ ≠ 0 := by
    obtain ⟨m, rfl⟩ := hρL
    rcases Nat.eq_zero_or_pos ρ with rfl | hρ
    · simp at hL
    · rw [Nat.mul_div_cancel_left _ hρ]; rintro rfl; simp at hL
  have hcard : Fintype.card (GaloisField 2 (L / ρ)) = 2 ^ (L / ρ) := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 _ hk]
  have := theorem_1 (F := GaloisField 2 (L / ρ)) hV hf z Vk disp hpack
  rwa [hcard, Nat.cast_pow, Nat.cast_ofNat] at this

end Podc.ByzantineLinearCoding
