import Papers.PODC2014.NetworkConstructors.CliquesBasic

/-!
# Protocol 9 (`c`-Cliques): the inductive invariant

The reachable configurations of Protocol 9 are described by a *component forest* `p : V → V`
(`p u = u` for roots, otherwise `p u` is the parent of `u`) with a height function `ht`
(so that `p` has no cycles), such that

* roots are exactly the agents in states `l_i`, `l̄_i`, `l`, `r`;
* an edge with at least one endpoint that is not a numbered follower (`k` or `l'_k`) is active iff
  it is a forest edge; edges between numbered followers are arbitrary (they may be wrong);
* the number of a numbered follower is its degree;
* every agent has exactly `nkids` children, `nfol` of them numbered and `nvis` of them visited
  (`l_i`: `i` children; `f_j`: `j`; `f`: none; `l̄_i`, `l`, `r`: `c − 1`, of which `i`, `c − 1`,
  `c − 1` are numbered; `r` has exactly one visited child).

`Inv.interact` reduces the preservation of the invariant by one interaction of `u` and `v` to
conditions at `u` and `v` (the parent of `v` may change between `u` and `v`).
-/

namespace Podc.NetworkConstructors.Cliques

open Cslib Cslib.NetworkConstructor Cslib.TransitionSystem St

variable {c : ℕ} {hc : 3 ≤ c} {V : Type*} [Fintype V] [DecidableEq V]

/-- The children of `u` in the forest `p`. -/
def kids (p : V → V) (u : V) : Finset V := Finset.univ.filter fun v => p v = u ∧ v ≠ u

@[simp] theorem mem_kids {p : V → V} {u v : V} : v ∈ kids p u ↔ p v = u ∧ v ≠ u := by
  simp [kids]

/-- The inductive invariant of Protocol 9 (see the module docstring). -/
structure Inv (C : Config V (St c)) (p : V → V) (ht : V → ℕ) : Prop where
  root : ∀ u, p u = u ↔ (C.st u).isRoot = true
  ht_lt : ∀ u, p u ≠ u → ht u < ht (p u)
  edge : ∀ u v, u ≠ v → ¬((C.st u).isFol = true ∧ (C.st v).isFol = true) →
    (C.edge u v = true ↔ (p u = v ∨ p v = u))
  deg : ∀ u, (C.st u).isFol = true → C.deg u = (C.st u).idx
  nkids : ∀ u, (kids p u).card = (C.st u).nkids
  nfol : ∀ u, ((kids p u).filter fun v => (C.st v).isFol = true).card = (C.st u).nfol
  nvis : ∀ u, ((kids p u).filter fun v => (C.st v).isVis = true).card = (C.st u).nvis

@[simp] theorem cliques_δ : (cliques c hc).δ = δ c hc := rfl

@[simp] theorem cliques_init : (cliques c hc).init = .l 0 (Nat.zero_le _) := rfl

@[simp] theorem cliques_out : (cliques c hc).out = St.out := rfl

theorem kids_eq_of_ne {p p' : V → V} {u v x : V} (hp : ∀ y, y ≠ v → p' y = p y)
    (hpv : p' v = p v ∨ ((p v = u ∨ p v = v) ∧ (p' v = u ∨ p' v = v))) (hxu : x ≠ u)
    (hxv : x ≠ v) : kids p' x = kids p x := by
  ext w
  simp only [mem_kids]
  by_cases hw : w = v
  · subst hw
    rcases hpv with h | ⟨hpv, hpv'⟩
    · rw [h]
    constructor
    · rintro ⟨h, -⟩; rcases hpv' with h' | h' <;> rw [h'] at h <;> exact absurd h.symm (by assumption)
    · rintro ⟨h, -⟩; rcases hpv with h' | h' <;> rw [h'] at h <;> exact absurd h.symm (by assumption)
  · rw [hp w hw]

set_option maxHeartbeats 1000000 in
/-- **Local preservation of the invariant.** -/
theorem Inv.interact {C : Config V (St c)} {p p' : V → V} {ht ht' : V → ℕ} {u v : V}
    {a' b' : St c} {e' : Bool} (hI : Inv C p ht) (huv : u ≠ v)
    (hδ : δ c hc (C.st u) (C.st v) (C.edge u v) = (a', b', e'))
    (hp : ∀ x, x ≠ v → p' x = p x)
    (hpv : p' v = p v ∨ ((p v = u ∨ p v = v) ∧ (p' v = u ∨ p' v = v)))
    (hroot_u : p' u = u ↔ a'.isRoot = true) (hroot_v : p' v = v ↔ b'.isRoot = true)
    (hht : ∀ x, p' x ≠ x → ht' x < ht' (p' x))
    (hfolu : (C.st u).isFol = true → a'.isFol = true)
    (hfolv : (C.st v).isFol = true → b'.isFol = true)
    (hedge : ¬(a'.isFol = true ∧ b'.isFol = true) → (e' = true ↔ (p' u = v ∨ p' v = u)))
    (hdegu : a'.isFol = true → ((cliques c hc).interact C u v).deg u = a'.idx)
    (hdegv : b'.isFol = true → ((cliques c hc).interact C u v).deg v = b'.idx)
    (hku : p u ≠ u → p u ≠ v → a'.isFol = (C.st u).isFol ∧ a'.isVis = (C.st u).isVis)
    (hkv : p v ≠ v → p v ≠ u → b'.isFol = (C.st v).isFol ∧ b'.isVis = (C.st v).isVis)
    (hnku : (kids p' u).card = a'.nkids) (hnkv : (kids p' v).card = b'.nkids)
    (hnfu : ((kids p' u).filter fun w =>
      (((cliques c hc).interact C u v).st w).isFol = true).card = a'.nfol)
    (hnfv : ((kids p' v).filter fun w =>
      (((cliques c hc).interact C u v).st w).isFol = true).card = b'.nfol)
    (hnvu : ((kids p' u).filter fun w =>
      (((cliques c hc).interact C u v).st w).isVis = true).card = a'.nvis)
    (hnvv : ((kids p' v).filter fun w =>
      (((cliques c hc).interact C u v).st w).isVis = true).card = b'.nvis) :
    Inv ((cliques c hc).interact C u v) p' ht' := by
  have hDu : ((cliques c hc).interact C u v).st u = a' := by simp [hδ]
  have hDv : ((cliques c hc).interact C u v).st v = b' := by
    simp [Protocol.interact_st_right C huv, hδ]
  have hDx : ∀ x, x ≠ u → x ≠ v → ((cliques c hc).interact C u v).st x = C.st x :=
    fun x h1 h2 => Protocol.interact_st_other C h1 h2
  have hDe : ((cliques c hc).interact C u v).edge u v = e' := by simp [hδ]
  have hDo : ∀ x y, ¬((x = u ∧ y = v) ∨ (x = v ∧ y = u)) →
      ((cliques c hc).interact C u v).edge x y = C.edge x y :=
    fun x y h => Protocol.interact_edge_other C h
  have hDdeg : ∀ x, x ≠ u → x ≠ v → ((cliques c hc).interact C u v).deg x = C.deg x :=
    fun x h1 h2 => Protocol.deg_interact_other h1 h2
  generalize (cliques c hc).interact C u v = D at *
  -- parents agree on pairs other than `{u, v}`
  have hpp : ∀ x y, x ≠ y → ¬((x = u ∧ y = v) ∨ (x = v ∧ y = u)) → (p' x = y ↔ p x = y) := by
    intro x y hxy hn
    by_cases hx : x = v
    · subst hx
      have hyu : y ≠ u := fun h => hn (.inr ⟨rfl, h⟩)
      rcases hpv with h | ⟨hpv, hpv'⟩
      · rw [h]
      constructor
      · intro h; rcases hpv' with h' | h' <;> rw [h'] at h
        · exact absurd h.symm hyu
        · exact absurd h hxy
      · intro h; rcases hpv with h' | h' <;> rw [h'] at h
        · exact absurd h.symm hyu
        · exact absurd h hxy
    · rw [hp x hx]
  have hfol : ∀ x, (C.st x).isFol = true → (D.st x).isFol = true := by
    intro x hx
    by_cases hxu : x = u
    · subst hxu; rw [hDu]; exact hfolu hx
    by_cases hxv : x = v
    · subst hxv; rw [hDv]; exact hfolv hx
    rw [hDx x hxu hxv]; exact hx
  have hkids := fun x (hxu : x ≠ u) (hxv : x ≠ v) => kids_eq_of_ne hp hpv hxu hxv
  -- states of the children of an agent other than `u`, `v`
  have hkst : ∀ x, x ≠ u → x ≠ v → ∀ w ∈ kids p x,
      (D.st w).isFol = (C.st w).isFol ∧ (D.st w).isVis = (C.st w).isVis := by
    intro x hxu hxv w hw
    rw [mem_kids] at hw
    by_cases hwu : w = u
    · subst hwu
      rw [hDu]
      exact hku (by rw [hw.1]; exact Ne.symm hw.2) (by rw [hw.1]; exact hxv)
    by_cases hwv : w = v
    · subst hwv
      rw [hDv]
      exact hkv (by rw [hw.1]; exact Ne.symm hw.2) (by rw [hw.1]; exact hxu)
    rw [hDx w hwu hwv]; exact ⟨rfl, rfl⟩
  refine ⟨fun x => ?_, hht, fun x y hxy hn => ?_, fun x hx => ?_, fun x => ?_, fun x => ?_,
    fun x => ?_⟩
  · by_cases hxu : x = u
    · subst hxu; rw [hDu]; exact hroot_u
    by_cases hxv : x = v
    · subst hxv; rw [hDv]; exact hroot_v
    rw [hDx x hxu hxv, hp x hxv]; exact hI.root x
  · by_cases huv' : (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    · rcases huv' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [hDu, hDv] at hn; rw [hDe]; exact hedge hn
      · rw [hDu, hDv] at hn
        have h2 := hedge (fun h => hn ⟨h.2, h.1⟩)
        rw [← hDe] at h2
        rw [D.symm x y, h2, or_comm]
    · rw [hDo x y huv', hpp x y hxy huv', hpp y x (Ne.symm hxy) (fun h => huv' (h.elim (fun h => .inr ⟨h.2, h.1⟩) (fun h => .inl ⟨h.2, h.1⟩)))]
      exact hI.edge x y hxy fun h => hn ⟨hfol x h.1, hfol y h.2⟩
  · by_cases hxu : x = u
    · subst hxu; rw [hDu] at hx ⊢; exact hdegu hx
    by_cases hxv : x = v
    · subst hxv; rw [hDv] at hx ⊢; exact hdegv hx
    rw [hDx x hxu hxv] at hx ⊢
    rw [hDdeg x hxu hxv]; exact hI.deg x hx
  · by_cases hxu : x = u
    · subst hxu; rw [hDu]; exact hnku
    by_cases hxv : x = v
    · subst hxv; rw [hDv]; exact hnkv
    rw [hDx x hxu hxv, hkids x hxu hxv]; exact hI.nkids x
  · by_cases hxu : x = u
    · subst hxu; rw [hDu]; exact hnfu
    by_cases hxv : x = v
    · subst hxv; rw [hDv]; exact hnfv
    rw [hDx x hxu hxv, hkids x hxu hxv, ← hI.nfol x]
    congr 1
    exact Finset.filter_congr fun w hw => by rw [(hkst x hxu hxv w hw).1]
  · by_cases hxu : x = u
    · subst hxu; rw [hDu]; exact hnvu
    by_cases hxv : x = v
    · subst hxv; rw [hDv]; exact hnvv
    rw [hDx x hxu hxv, hkids x hxu hxv, ← hI.nvis x]
    congr 1
    exact Finset.filter_congr fun w hw => by rw [(hkst x hxu hxv w hw).2]

end Podc.NetworkConstructors.Cliques
