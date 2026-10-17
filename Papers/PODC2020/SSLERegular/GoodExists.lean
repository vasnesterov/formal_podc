import Papers.PODC2020.SSLERegular.EulerGood
import Papers.PODC2020.SSLERegular.Euler
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Existence of legitimate configurations of SS-EulerCycle (repaired Lemma 3.1)

Chen–Chen, *Self-Stabilizing Leader Election in Regular Graphs*, PODC 2020, Lemma 3.1.

On a connected `2k`-regular graph (`k ≥ 1`), given a ring protocol satisfying `RingSpec`, there is
a configuration satisfying `Good`. The construction follows the paper:

1. a colouring `col : V → Fin (4k²)` that is injective on every neighbourhood (greedy colouring of
   the "common neighbour" graph, whose degrees are `< 4k²`; `exists_coloring_of_card_lt`);
2. an Euler circuit `p : Fin M → V` (`M = #E = n·k`, `exists_euler_cyclic_seq`); every vertex
   occurs exactly `k` times, and the occurrence `t` becomes the virtual node
   `(p t, rank of t among the occurrences of p t)`, with predecessor colour `col (p (t-1))` and
   successor colour `col (p (t+1))`. The virtual ring is then the Euler circuit, a single cycle;
3. ring states: a valid output-stable ring configuration given by `RingSpec` on that ring;
4. tokens: one token, at the ring leader `w0`, which is also the only virtual node with bit `true`.
-/

set_option linter.unusedSectionVars false

open Finset SimpleGraph

namespace SSLERegular

universe u

-- CSLib candidate
/-- Greedy colouring: if a symmetric conflict relation has fewer than `N` conflicts at each vertex,
there is a colouring with `N` colours in which conflicting distinct vertices get distinct colours. -/
lemma exists_coloring_of_card_lt {V : Type*} [Fintype V] [DecidableEq V] (Conf : V → V → Prop)
    [DecidableRel Conf] (hsymm : ∀ u v, Conf u v → Conf v u) {N : ℕ}
    (hb : ∀ v, #{u | Conf v u} < N) :
    ∃ f : V → Fin N, ∀ u v, Conf u v → u ≠ v → f u ≠ f v := by
  suffices h : ∀ S : Finset V, ∃ f : V → Fin N, ∀ u ∈ S, ∀ v ∈ S, Conf u v → u ≠ v → f u ≠ f v by
    obtain ⟨f, hf⟩ := h univ
    exact ⟨f, fun u v => hf u (mem_univ _) v (mem_univ _)⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact ⟨fun v => ⟨0, lt_of_le_of_lt (Nat.zero_le _) (hb v)⟩, by simp⟩
  | insert a S ha ih =>
    obtain ⟨f, hf⟩ := ih
    have hcard : #(({u | Conf a u} : Finset V).image f) < #(univ : Finset (Fin N)) := by
      rw [card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt card_image_le (hb a)
    obtain ⟨c, -, hc⟩ := exists_mem_notMem_of_card_lt_card hcard
    have hc' : ∀ u, Conf a u → f u ≠ c := fun u hu h =>
      hc (mem_image.2 ⟨u, by simpa using hu, h⟩)
    refine ⟨Function.update f a c, ?_⟩
    intro u hu v hv huv hne
    rw [mem_insert] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact absurd (hu.trans hv.symm) hne
    · subst hu
      have hva : v ≠ u := fun h => ha (h ▸ hv)
      rw [Function.update_self, Function.update_of_ne hva]
      exact (hc' v huv).symm
    · subst hv
      have hua : u ≠ v := fun h => ha (h ▸ hu)
      rw [Function.update_self, Function.update_of_ne hua]
      exact hc' u (hsymm _ _ huv)
    · have hua : u ≠ a := fun h => ha (h ▸ hu)
      have hva : v ≠ a := fun h => ha (h ▸ hv)
      rw [Function.update_of_ne hua, Function.update_of_ne hva]
      exact hf u hu v hv huv hne

variable {k : ℕ} {V : Type u} [DecidableEq V] [Fintype V] {G : SimpleGraph V}
  [DecidableRel G.Adj]

/-- A colouring with `4k²` colours that is injective on every neighbourhood of a `2k`-regular
graph (two distinct vertices with a common neighbour get distinct colours). -/
lemma exists_injCol_coloring (hdeg : ∀ v, G.degree v = 2 * k) (hk : 1 ≤ k) :
    ∃ col : V → Fin (4 * k ^ 2), ∀ x u v, G.Adj x u → G.Adj x v → col u = col v → u = v := by
  have hb : ∀ v, #({u | v ≠ u ∧ ∃ x, G.Adj x v ∧ G.Adj x u} : Finset V) < 4 * k ^ 2 := by
    intro v
    have hsub : ({u | v ≠ u ∧ ∃ x, G.Adj x v ∧ G.Adj x u} : Finset V) ⊆
        ((G.neighborFinset v).biUnion (fun y => G.neighborFinset y)).erase v := by
      intro u hu
      simp only [mem_filter, mem_univ, true_and] at hu
      obtain ⟨hne, x, hxv, hxu⟩ := hu
      exact mem_erase.2 ⟨Ne.symm hne, mem_biUnion.2 ⟨x, by simpa using hxv.symm, by simpa using hxu⟩⟩
    have hmem : v ∈ (G.neighborFinset v).biUnion (fun y => G.neighborFinset y) := by
      have hpos : 0 < #(G.neighborFinset v) := by
        rw [card_neighborFinset_eq_degree, hdeg]; omega
      obtain ⟨x, hx⟩ := Finset.card_pos.1 hpos
      rw [mem_neighborFinset] at hx
      exact mem_biUnion.2 ⟨x, by simpa using hx, by simpa using hx.symm⟩
    have hle : #((G.neighborFinset v).biUnion (fun y => G.neighborFinset y)) ≤ 4 * k ^ 2 := by
      refine card_biUnion_le.trans ?_
      simp only [card_neighborFinset_eq_degree, hdeg, sum_const, smul_eq_mul]
      apply le_of_eq; ring
    have h1 := card_le_card hsub
    rw [card_erase_of_mem hmem] at h1
    have h2 : 0 < #((G.neighborFinset v).biUnion (fun y => G.neighborFinset y)) := card_pos.2 ⟨v, hmem⟩
    exact lt_of_le_of_lt h1 (by omega)
  obtain ⟨f, hf⟩ := exists_coloring_of_card_lt (fun u v => u ≠ v ∧ ∃ x, G.Adj x u ∧ G.Adj x v)
    (fun u v ⟨h1, x, h2, h3⟩ => ⟨h1.symm, x, h3, h2⟩) (N := 4 * k ^ 2) hb
  exact ⟨f, fun x u v hu hv hc => by_contra fun hne => hf u v ⟨hne, x, hu, hv⟩ hne hc⟩

/-- The Euler sequence of `exists_euler_cyclic_seq` with its length as a free variable. -/
lemma exists_euler_seq (hconn : G.Connected) (heven : ∀ v, Even (G.degree v)) :
    ∃ (M : ℕ) (p : Fin M → V), M = #G.edgeFinset ∧ (∀ t, G.Adj (p t) (p (finRotate M t))) ∧
      (∀ u x, G.Adj u x → ∃ t, s(p t, p (finRotate M t)) = s(u, x)) ∧
      Function.Injective (fun t => s(p t, p (finRotate M t))) := by
  obtain ⟨p, hadj, hbij⟩ := exists_euler_cyclic_seq G hconn heven
  refine ⟨_, p, rfl, hadj, fun u x hux => ?_, fun a b h => hbij.1 (Subtype.ext h)⟩
  obtain ⟨t, ht⟩ := hbij.2 ⟨s(u, x), G.mem_edgeSet.2 hux⟩
  exact ⟨t, congrArg Subtype.val ht⟩

/-- **Lemma 3.1** (repaired SS-EulerCycle): on a connected `2k`-regular graph with `k ≥ 1`, given
a ring protocol solving SSLE on directed rings (`RingSpec`), a legitimate configuration exists. -/
theorem exists_good {RS : Type*} (hconn : G.Connected)
    (hdeg : ∀ v, G.degree v = 2 * k) (hk : 1 ≤ k) {R : RingProtocol RS}
    (hR : RingSpec.{u} R) (r0 : RS) : ∃ C : V → EState k RS, Good G R hdeg C := by
  -- 1. the colouring
  obtain ⟨col, hcol⟩ := exists_injCol_coloring hdeg hk
  -- 2. the Euler sequence
  have heven : ∀ v, Even (G.degree v) := fun v => by rw [hdeg]; exact even_two_mul k
  obtain ⟨M, p, hM, hadj, hsurj, hinjE⟩ := exists_euler_seq hconn heven
  set rot := finRotate M with hrotdef
  have hn : 2 * k < Fintype.card V := hdeg hconn.nonempty.some ▸ G.degree_lt_card_verts _
  have hMk : M = Fintype.card V * k := by
    have h := G.sum_degrees_eq_twice_card_edges
    simp only [hdeg, sum_const, card_univ, smul_eq_mul] at h
    have : 2 * (Fintype.card V * k) = 2 * M := by rw [hM, ← h]; ring
    omega
  -- every vertex occurs exactly `k` times
  have hocc : ∀ w, #({t | p t = w} : Finset (Fin M)) = k := by
    intro w
    have hA : #({t | w ∈ s(p t, p (rot t))} : Finset (Fin M)) = G.degree w := by
      rw [← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]
      refine card_bij (fun t _ => s(p t, p (rot t))) ?_ ?_ ?_
      · intro t ht
        simp only [mem_filter, mem_univ, true_and] at ht
        exact mem_filter.2 ⟨mem_edgeFinset.2 (hadj t), ht⟩
      · intro a _ b _ h
        exact hinjE h
      · intro e he
        obtain ⟨he, hwe⟩ := mem_filter.1 he
        induction e using Sym2.ind with
        | _ u x =>
          obtain ⟨t, ht⟩ := hsurj u x (mem_edgeFinset.1 he)
          exact ⟨t, mem_filter.2 ⟨mem_univ _, by rw [ht]; exact hwe⟩, ht⟩
    have hsplit : ({t | w ∈ s(p t, p (rot t))} : Finset (Fin M)) =
        ({t | p t = w} : Finset (Fin M)) ∪ ({t | p (rot t) = w} : Finset (Fin M)) := by
      ext t; simp [Sym2.mem_iff, eq_comm]
    have hdisj : Disjoint ({t | p t = w} : Finset (Fin M)) ({t | p (rot t) = w} : Finset (Fin M)) := by
      rw [disjoint_filter]; intro t _ h1 h2; exact (hadj t).ne (h1.trans h2.symm)
    have hrot : #({t | p (rot t) = w} : Finset (Fin M)) = #({t | p t = w} : Finset (Fin M)) := by
      refine card_nbij' rot rot.symm ?_ ?_ ?_ ?_
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter] at ht ⊢; exact ⟨mem_univ _, ht.2⟩
      · intro t ht
        rw [Finset.mem_coe, Finset.mem_filter] at ht ⊢
        refine ⟨mem_univ _, ?_⟩
        rw [Equiv.apply_symm_apply]; exact ht.2
      · intro t _; exact Equiv.symm_apply_apply _ _
      · intro t _; exact Equiv.apply_symm_apply _ _
    rw [hsplit, card_union_of_disjoint hdisj, hrot, hdeg] at hA
    omega
  -- numbering of the occurrences
  let idx : Fin M → Fin k := fun t => ⟨#({s | p s = p t ∧ s < t} : Finset (Fin M)), by
    rw [← hocc (p t)]
    apply card_lt_card
    rw [ssubset_iff_of_subset (fun s hs => by simp only [mem_filter] at hs ⊢; exact ⟨hs.1, hs.2.1⟩)]
    exact ⟨t, by simp, by simp⟩⟩
  let pos : Fin M → V × Fin k := fun t => (p t, idx t)
  have hlt : ∀ t t', p t = p t' → t < t' → (idx t : ℕ) < idx t' := by
    intro t t' hp htt
    show #({s | p s = p t ∧ s < t} : Finset (Fin M)) < #({s | p s = p t' ∧ s < t'} : Finset (Fin M))
    apply card_lt_card
    rw [ssubset_iff_of_subset (fun s hs => ?_)]
    · exact ⟨t, by simp [hp, htt], by simp⟩
    · simp only [mem_filter, mem_univ, true_and] at hs ⊢
      exact ⟨hs.1.trans hp, hs.2.trans htt⟩
  have hposinj : Function.Injective pos := by
    intro t t' h
    simp only [pos, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases lt_trichotomy t t' with h | h | h
    · exact absurd (congrArg Fin.val h2) (hlt t t' h1 h).ne
    · exact h
    · exact absurd (congrArg Fin.val h2) (hlt t' t h1.symm h).ne'
  have hcardX : Fintype.card (V × Fin k) = M := by simp [Fintype.card_prod, hMk]
  have hposbij : Function.Bijective pos :=
    (Fintype.bijective_iff_injective_and_card pos).2 ⟨hposinj, by simp [hcardX]⟩
  let posE := Equiv.ofBijective pos hposbij
  have hsymm : ∀ t, posE.symm (pos t) = t := fun t => posE.symm_apply_apply t
  -- 3. the skeleton
  let predc : V × Fin k → Fin (4 * k ^ 2) := fun w => col (p (rot.symm (posE.symm w)))
  let succc : V × Fin k → Fin (4 * k ^ 2) := fun w => col (p (rot (posE.symm w)))
  let mk : (V × Fin k → RS) → (V × Fin k → Bool) → V → EState k RS := fun rs tok v =>
    { node := fun i => { ringState := rs (v, i), pred := predc (v, i), succ := succc (v, i),
                         token := tok (v, i), bit := tok (v, i) },
      color := col v, prevColor := col v, colorBit := false, errFlag := false }
  let S : V → Skel k := fun v => (col v, fun i => (predc (v, i), succc (v, i)))
  have hV : ∀ t, VEdge G S (p t) (idx t) (p (rot t)) (idx (rot t)) := by
    intro t
    refine ⟨hadj t, ?_, ?_⟩
    · show col (p (rot (posE.symm (pos t)))) = col (p (rot t))
      rw [hsymm]
    · show col (p (rot.symm (posE.symm (pos (rot t))))) = col (p t)
      rw [hsymm, Equiv.symm_apply_apply]
  have hinjS : InjCol G S := fun x u v hu hv h => hcol x u v hu hv h
  have hokS : EdgeOK G S := by
    intro u x hux
    obtain ⟨t, ht'⟩ := hsurj u x hux
    rcases Sym2.eq_iff.1 ht' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; exact ⟨idx t, idx (rot t), h1 ▸ h2 ▸ hV t⟩
    · right; exact ⟨idx t, idx (rot t), h1 ▸ h2 ▸ hV t⟩
  -- the virtual ring is the Euler circuit
  set σ := vperm hdeg hinjS hokS with hσdef
  have hσ : ∀ t, σ (pos t) = pos (rot t) := fun t => (edge_iff_vperm hdeg hinjS hokS).1 (hV t)
  have hσpow : ∀ (i : ℕ) t, (σ ^ i) (pos t) = pos ((rot ^ i) t) := by
    intro i
    induction i with
    | zero => intro t; simp
    | succ i ih =>
      intro t
      rw [pow_succ', Equiv.Perm.mul_apply, ih, hσ, pow_succ', Equiv.Perm.mul_apply]
  have h3 : 3 ≤ Fintype.card (V × Fin k) := by
    rw [hcardX, hMk]; nlinarith
  have hM2 : 2 ≤ M := by omega
  have hsame : ∀ w w', σ.SameCycle w w' := by
    intro w w'
    obtain ⟨a, rfl⟩ := hposbij.2 w
    obtain ⟨b, rfl⟩ := hposbij.2 w'
    have hc := isCycle_finRotate_of_le hM2
    have hs := support_finRotate_of_le hM2
    have hab : rot.SameCycle a b :=
      hc.sameCycle (Equiv.Perm.mem_support.1 (by rw [hs]; exact mem_univ _))
        (Equiv.Perm.mem_support.1 (by rw [hs]; exact mem_univ _))
    obtain ⟨i, hi⟩ := hab.exists_nat_pow_eq
    exact ⟨i, by rw [zpow_natCast, hσpow, hi]⟩
  have hne : ∀ w, σ w ≠ w := fun w h =>
    G.irrefl (by have := adj_vperm hdeg hinjS hokS w; rwa [← hσdef, h] at this)
  have hcyc : σ.IsCycle := ⟨pos ⟨0, by omega⟩, hne _, fun y _ => hsame _ y⟩
  have hcardpos : 0 < Fintype.card (V × Fin k) := by omega
  have hsupp : σ.support = univ := eq_univ_of_forall fun w => Equiv.Perm.mem_support.2 (hne w)
  have hkey : ∀ w (t : ℕ), t < Fintype.card (V × Fin k) → ((σ ^ t) w = w ↔ t = 0) := by
    intro w t ht
    constructor
    · intro h
      have h1 : σ ^ t = 1 := (hcyc.pow_eq_one_iff' (hne w)).2 h
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hcyc.orderOf, hsupp, card_univ] at h2
      exact Nat.eq_zero_of_dvd_of_lt h2 ht
    · rintro rfl; simp
  -- 4. ring states: a valid output-stable configuration of the ring protocol on `σ`
  obtain ⟨c', -, hvalid⟩ := hR (V × Fin k) σ hsame h3 (fun _ => r0)
  obtain ⟨w0, hw0, -⟩ := hvalid.2
  -- 5. one token, at the ring leader, which alone has bit `true`
  refine ⟨mk c' (fun w => decide (w = w0)), hinjS, hokS,
    ⟨fun v => rfl, fun u v _ _ _ => rfl, fun v => rfl⟩, hsame, hvalid, w0, hw0,
    0, hcardpos, true, fun t ht => ?_⟩
  have := hkey w0 t ht
  show decide ((((σ ^ t) w0).1, ((σ ^ t) w0).2) = w0) = decide (t = 0) ∧
    decide ((((σ ^ t) w0).1, ((σ ^ t) w0).2) = w0) = (if t ≤ 0 then true else !true)
  simp only [Prod.mk.eta, this]
  rcases Nat.eq_zero_or_pos t with h | h <;> simp [h]

end SSLERegular
