import Papers.PODC2013.CongestedCliqueRouting.Knowledge

/-!
# Simulating a clique of virtual nodes

Every virtual node `v'` is hosted by the real node `(g v').1` and has local index `(g v').2 < F`
there (`g` injective). A real packet from `u` to `w` has `F · F · B` slots: slot `(i, j, k)`
carries slot `k` of the virtual packet from the `i`-th virtual node of `u` to the `j`-th virtual
node of `w`. This is how the general case `n ≠ s²` of Theorem 3.7 is reduced to the square
case (in place of the paper's three overlapping sub-cliques `V₁, V₂, V₃`).
-/

set_option linter.unusedSectionVars false

namespace CongestedCliqueRouting

open Finset

variable {I V V' K K' M : Type*} [DecidableEq M] {F B : ℕ} (g : V' → V × Fin F)

open Classical in
/-- The virtual node hosted by `u` with local index `i`, if any. -/
noncomputable def vnode (u : V) (i : Fin F) : Option V' :=
  if h : ∃ v', g v' = (u, i) then some (Classical.choose h) else none

lemma vnode_spec {u : V} {i : Fin F} {v' : V'} (h : vnode g u i = some v') : g v' = (u, i) := by
  unfold vnode at h
  split_ifs at h with hex
  · simp only [Option.some.injEq] at h
    rw [← h]
    exact Classical.choose_spec hex


lemma vnode_g (hg : Function.Injective g) (v' : V') : vnode g (g v').1 (g v').2 = some v' := by
  have hex : ∃ x, g x = ((g v').1, (g v').2) := ⟨v', rfl⟩
  unfold vnode
  rw [dif_pos hex]
  exact congrArg some (hg (Classical.choose_spec hex))

/-- Slot index of `(i, j, k)`. -/
def simSlot (i j : Fin F) (k : Fin B) : Fin (F * (F * B)) :=
  finProdFinEquiv (i, finProdFinEquiv (j, k))

/-- The real run simulating the virtual run `S'`. -/
noncomputable def simRun (S' : Run I V' M B) : Run I V M (F * (F * B)) :=
  fun d t u w ℓ =>
    match vnode g u (finProdFinEquiv.symm ℓ).1,
      vnode g w (finProdFinEquiv.symm (finProdFinEquiv.symm ℓ).2).1 with
    | some v', some w' => S' d t v' w' (finProdFinEquiv.symm (finProdFinEquiv.symm ℓ).2).2
    | _, _ => none

lemma simRun_slot (hg : Function.Injective g) (S' : Run I V' M B) (d : I) (t : ℕ) (v' w' : V')
    (k : Fin B) :
    simRun g S' d t (g v').1 (g w').1 (simSlot (g v').2 (g w').2 k) = S' d t v' w' k := by
  simp [simRun, simSlot, vnode_g g hg]

lemma simRun_some {S' : Run I V' M B} {d : I} {t : ℕ} {u w : V} {ℓ : Fin (F * (F * B))}
    {x : Item M} (h : simRun g S' d t u w ℓ = some x) :
    ∃ v' w' k, (g v').1 = u ∧ (g w').1 = w ∧ S' d t v' w' k = some x := by
  unfold simRun at h
  split at h
  · rename_i v' w' hv hw
    exact ⟨v', w', _, by rw [vnode_spec g hv], by rw [vnode_spec g hw], h⟩
  · simp at h

variable {g}

/-- Locality is preserved by the simulation, provided a virtual node's input is computed from
its host's input. -/
theorem simRun_isLocal (hg : Function.Injective g) {inp : I → V → K} {inp' : I → V' → K'}
    (φ : V' → K → K') (hφ : ∀ d v', inp' d v' = φ v' (inp d (g v').1)) {S' : Run I V' M B}
    (hS' : IsLocal inp' S') : IsLocal inp (simRun g S') := by
  intro t u d d' hv
  funext w ℓ
  simp only [simRun]
  split
  · rename_i v' w' hv' hw'
    have hu : (g v').1 = u := by rw [vnode_spec g hv']
    have hsame : SameView inp' S' d d' t v' := by
      refine ⟨by rw [hφ, hφ, hu, hv.1], fun r hr x' => ?_⟩
      funext k
      have := congrFun (hv.2 r hr (g x').1) (simSlot (g x').2 (g v').2 k)
      rw [← hu] at this
      simpa only [simRun_slot g hg] using this
    exact congrFun (congrFun (hS' t v' d d' hsame) w') _
  · rfl

/-- A host's view determines the views of the virtual nodes it hosts. -/
lemma sameView_sim (hg : Function.Injective g) {inp : I → V → K} {inp' : I → V' → K'}
    (φ : V' → K → K') (hφ : ∀ d v', inp' d v' = φ v' (inp d (g v').1)) {S' : Run I V' M B}
    {d d' : I} {t : ℕ} {v' : V'} (hv : SameView inp (simRun g S') d d' t (g v').1) :
    SameView inp' S' d d' t v' := by
  refine ⟨by rw [hφ, hφ, hv.1], fun r hr x' => ?_⟩
  funext k
  have := congrFun (hv.2 r hr (g x').1) (simSlot (g x').2 (g v').2 k)
  simpa only [simRun_slot g hg] using this

/-- What a virtual node knows, its host knows. -/
lemma Determined.of_sim (hg : Function.Injective g) {inp : I → V → K} {inp' : I → V' → K'}
    (φ : V' → K → K') (hφ : ∀ d v', inp' d v' = φ v' (inp d (g v').1)) {S' : Run I V' M B}
    {t : ℕ} {v' : V'} {α : Sort*} {f : I → α} (h : Determined inp' S' t v' f) :
    Determined inp (simRun g S') t (g v').1 f :=
  fun d d' hv => h d d' (sameView_sim hg φ hφ hv)

/-- Holding is transferred from virtual nodes to their hosts. -/
lemma holdsS_sim (hg : Function.Injective g) {msgs : I → V → Finset M}
    {msgs' : I → V' → Finset M} (hsub : ∀ d v', msgs' d v' ⊆ msgs d (g v').1)
    {S' : Run I V' M B} {d : I} {t : ℕ} {v' : V'} {m : M} (h : HoldsS msgs' S' d t v' m) :
    HoldsS msgs (simRun g S') d t (g v').1 m := by
  rcases h with h | ⟨r, hr, x', k, h⟩
  · exact Or.inl (hsub d v' h)
  · exact Or.inr ⟨r, hr, (g x').1, simSlot (g x').2 (g v').2 k, by rw [simRun_slot g hg]; exact h⟩

/-- The routing specification is transferred from the virtual run to the simulating run. -/
theorem simRun_routes (hg : Function.Injective g) {msgs : I → V → Finset M}
    {msgs' : I → V' → Finset M} (hsub : ∀ d v', msgs' d v' ⊆ msgs d (g v').1)
    (hcover : ∀ d u m, m ∈ msgs d u → ∃ v', m ∈ msgs' d v')
    {dst : I → M → V} {dst' : I → M → V'} (hdst : ∀ d m, (g (dst' d m)).1 = dst d m)
    {S' : Run I V' M B} {T C : ℕ} (hR : Routes msgs' dst' S' T C) :
    Routes msgs dst (simRun g S') T C where
  num_le d t ht u w ℓ k h := by
    obtain ⟨v', w', k', -, -, h'⟩ := simRun_some g h
    exact hR.num_le d t ht v' w' k' k h'
  valid d t ht u w ℓ m h := by
    obtain ⟨v', w', k', rfl, -, h'⟩ := simRun_some g h
    exact holdsS_sim hg hsub (hR.valid d t ht v' w' k' m h')
  deliver d u m hm := by
    obtain ⟨v', hv'⟩ := hcover d u m hm
    have := holdsS_sim hg hsub (hR.deliver d v' m hv')
    rwa [hdst] at this

end CongestedCliqueRouting
