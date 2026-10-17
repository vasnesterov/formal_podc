import Papers.PODC2013.CongestedCliqueRouting.SquareMain
import Papers.PODC2013.CongestedCliqueRouting.Simulation
import Papers.PODC2013.CongestedCliqueRouting.Compose

/-!
# Theorem 3.7 as a subroutine

`box_spec`: on any node set `V ≃ Fin N`, if every node `v` holds a set `H d v` of keys (at most
`s₂²` of them) and chooses a target `tg d v x` for each of its keys such that every node is the
target of at most `s₂²` keys (where `N ≤ s₂² ≤ F N`), then a 15-round run `boxRun` delivers every
key to its target. The run is local w.r.t. the inputs `(x, tg x)`, and at the end every node
knows the set of keys it received. Used in Step 6 of Algorithm 4 (sorting).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

namespace Setup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] [Nonempty V] {s : ℕ}
  [NeZero s] {σ : Setup I V M s}

/-- At the end, a node holds exactly the messages destined to it. -/
lemma src_of_HE (hG : σ.Good) {d : I} {w : V} {m : M} (h : m ∈ σ.HE d w) :
    (∃ v, m ∈ σ.inp d v) ∧ σ.dst m = w := by
  rw [mem_HE hG] at h
  obtain ⟨u, c, k, hg, hc⟩ := h
  obtain ⟨hm, hy, -, -⟩ := relD_spec hG d hc
  have hdg := HD_dg hG d hm
  refine ⟨?_, ?_⟩
  · obtain ⟨w', hw', -⟩ := HD_sub hG d hm
    obtain ⟨u', hu', -⟩ := HC_sub hG d hw'
    obtain ⟨v, hv, -⟩ := HB_sub hG d hu'
    exact ⟨v, hv⟩
  · apply σ.e.injective
    refine Prod.ext ?_ ?_
    · show grp σ.e (σ.dst m) = grp σ.e w
      rw [← hg]; exact hdg
    · show mem σ.e (σ.dst m) = mem σ.e w
      exact Fin.ext hy.symm

end Setup

section Box

variable {I V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M]
  {N s2 F : ℕ} [NeZero s2] (eV : V ≃ Fin N) (hNpos : 0 < N) (hN : N ≤ s2 * s2)
  (hF : s2 * s2 ≤ F * N)

/-- Index of a virtual node. -/
def bidx (v : Fin s2 × Fin s2) : ℕ := (finProdFinEquiv v : ℕ)

include hNpos hF in
/-- Host and local index of a virtual node. -/
def bhost (v : Fin s2 × Fin s2) : V × Fin F :=
  (eV.symm ⟨bidx v % N, Nat.mod_lt _ hNpos⟩,
    ⟨bidx v / N, (Nat.div_lt_iff_lt_mul hNpos).2
      (lt_of_lt_of_le (finProdFinEquiv v).isLt hF)⟩)

include hN in
/-- The primary virtual node of a real node. -/
def bprim (v : V) : Fin s2 × Fin s2 :=
  finProdFinEquiv.symm ⟨eV v, lt_of_lt_of_le (eV v).isLt hN⟩

lemma bhost_inj : Function.Injective (bhost eV hNpos hF) := by
  intro v w h
  simp only [bhost, Prod.mk.injEq, Fin.mk.injEq, EmbeddingLike.apply_eq_iff_eq] at h
  have : bidx v = bidx w := by
    rw [← Nat.mod_add_div (bidx v) N, ← Nat.mod_add_div (bidx w) N, h.1, h.2]
  exact finProdFinEquiv.injective (Fin.ext this)

lemma bhost_bprim (v : V) : (bhost eV hNpos hF (bprim eV hN v)).1 = v := by
  apply eV.injective
  simp only [bhost, bprim, bidx, Equiv.apply_symm_apply]
  ext
  simp [Nat.mod_eq_of_lt (eV v).isLt]

lemma bprim_inj : Function.Injective (bprim (V := V) eV hN) := by
  intro v w h
  simp only [bprim, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq] at h
  exact eV.injective (Fin.ext h)

variable (H : I → V → Finset M) (tg : I → V → M → V)

/-- Keys paired with their targets. -/
def pairsIn (d : I) (v : V) : Finset (M × V) := (H d v).image fun x => (x, tg d v x)

/-- Input of a virtual node: the pairs of its host, if it is the host's primary node. -/
def bphi (v : Fin s2 × Fin s2) (P : Finset (M × V)) : Finset (M × V) :=
  if bprim eV hN (bhost eV hNpos hF v).1 = v then P else ∅

/-- The square routing algorithm on the virtual nodes. -/
def boxSetup : Setup I (Fin s2 × Fin s2) (M × V) s2 where
  e := Equiv.refl _
  dst p := bprim eV hN p.2
  inp d v := bphi eV hNpos hN hF v (pairsIn H tg d (bhost eV hNpos hF v).1)

/-- Decoding node numbers. -/
def vdec (k : ℕ) : Option V := if h : k < N then some (eV.symm ⟨k, h⟩) else none

lemma vdec_enc (w : V) : vdec eV (eV w : ℕ) = some w := by simp [vdec]

/-- Theorem 3.7 as a 15-round subroutine. -/
noncomputable def boxRun : Run I V M ((F * (F * 3)) * 2) :=
  mapRun (pairP fun w => (eV w : ℕ))
    (simRun (bhost eV hNpos hF) (boxSetup eV hNpos hN hF H tg).run)

/-- Keys whose target is `w`. -/
def Recv (d : I) (w : V) : Finset M := univ.biUnion fun v => (H d v).filter fun x => tg d v x = w

variable {H tg}

lemma boxSetup_good (hcard : ∀ d v, (H d v).card ≤ s2 * s2)
    (hload : ∀ d w, ∑ v, ((H d v).filter fun x => tg d v x = w).card ≤ s2 * s2) :
    (boxSetup eV hNpos hN hF H tg).Good where
  card_le d v := by
    simp only [boxSetup, bphi]
    split_ifs
    · exact card_image_le.trans (hcard _ _)
    · simp
  load_le d w'' := by
    simp only [boxSetup]
    have h1 : ∀ v'', ((bphi eV hNpos hN hF v'' (pairsIn H tg d (bhost eV hNpos hF v'').1)).filter
        fun p => bprim eV hN p.2 = w'').card ≤ ∑ v, if bprim eV hN v = v'' then
          ((H d v).filter fun x => bprim eV hN (tg d v x) = w'').card else 0 := by
      intro v''
      simp only [bphi]
      split_ifs with hv
      · rw [Finset.sum_eq_single (bhost eV hNpos hF v'').1]
        · rw [if_pos hv, pairsIn, filter_image]
          exact card_image_le
        · intro b _ hb
          rw [if_neg]
          intro hb'
          apply hb
          rw [← hb', bhost_bprim]
        · simp
      · simp
    refine le_trans (sum_le_sum fun v'' _ => h1 v'') ?_
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, if_true]
    by_cases hw : ∃ w, bprim eV hN w = w''
    · obtain ⟨w, rfl⟩ := hw
      refine le_trans (le_of_eq (sum_congr rfl fun v _ => ?_)) (hload d w)
      congr 1
      exact filter_congr fun x _ => (bprim_inj eV hN).eq_iff
    · push Not at hw
      simp [hw]

variable (hcard : ∀ d v, (H d v).card ≤ s2 * s2)
  (hload : ∀ d w, ∑ v, ((H d v).filter fun x => tg d v x = w).card ≤ s2 * s2)

include hcard hload

theorem box_isLocal : IsLocal (pairsIn H tg) (boxRun eV hNpos hN hF H tg) :=
  isLocal_mapRun (simRun_isLocal (bhost_inj eV hNpos hF) (bphi eV hNpos hN hF) (fun _ _ => rfl)
    (Setup.square_correct (boxSetup_good eV hNpos hN hF hcard hload)).1)
    (unpairP_pairP (vdec_enc eV))

lemma holdsS_box {d : I} {t : ℕ} {v : Fin s2 × Fin s2} {x : M} {w : V}
    (h : HoldsS (boxSetup eV hNpos hN hF H tg).inp (boxSetup eV hNpos hN hF H tg).run d t v
      (x, w)) :
    HoldsS H (boxRun eV hNpos hN hF H tg) d t (bhost eV hNpos hF v).1 x := by
  rcases h with h | ⟨r, hr, x', k, h⟩
  · left
    simp only [boxSetup, bphi] at h
    split_ifs at h
    · simp only [pairsIn, mem_image, Prod.mk.injEq] at h
      obtain ⟨y, hy, rfl, -⟩ := h
      exact hy
    · simp at h
  · right
    refine ⟨r, hr, (bhost eV hNpos hF x').1, pslot (simSlot (bhost eV hNpos hF x').2
      (bhost eV hNpos hF v).2 k) 0, ?_⟩
    simp only [boxRun, mapRun]
    exact pairP_msg (by rw [simRun_slot _ (bhost_inj eV hNpos hF)]; exact h)

theorem box_num_le {d : I} {t : ℕ} (ht : t < 15) {u v : V} {i : Fin ((F * (F * 3)) * 2)}
    {k : ℕ} (h : boxRun eV hNpos hN hF H tg d t u v i = some (Item.num k)) :
    k ≤ s2 * s2 * s2 := by
  have hR := (Setup.square_correct (boxSetup_good eV hNpos hN hF hcard hload)).2
  simp only [boxRun, mapRun] at h
  rcases pairP_eq_some h with ⟨j, x, w, -, hy⟩ | ⟨j, k', hj, hk⟩
  · rcases hy with hy | hy
    · cases hy
    · cases hy
      have h1 : (eV w : ℕ) < N := (eV w).isLt
      have : 1 ≤ s2 := Nat.one_le_iff_ne_zero.2 (NeZero.ne s2)
      nlinarith
  · injection hk with hk
    subst hk
    obtain ⟨v', w', k'', -, -, h'⟩ := simRun_some _ hj
    exact hR.num_le d t ht v' w' k'' _ h'

theorem box_valid {d : I} {t : ℕ} (ht : t < 15) {u v : V} {i : Fin ((F * (F * 3)) * 2)}
    {x : M} (h : boxRun eV hNpos hN hF H tg d t u v i = some (Item.msg x)) :
    HoldsS H (boxRun eV hNpos hN hF H tg) d t u x := by
  have hR := (Setup.square_correct (boxSetup_good eV hNpos hN hF hcard hload)).2
  simp only [boxRun, mapRun] at h
  rcases pairP_eq_some h with ⟨j, x', w, hj, hy⟩ | ⟨j, k', hj, hk⟩
  · rcases hy with hy | hy
    · cases hy
      obtain ⟨v', w', k'', rfl, -, h'⟩ := simRun_some _ hj
      exact holdsS_box eV hNpos hN hF hcard hload (hR.valid d t ht v' w' k'' _ h')
    · cases hy
  · cases hk

theorem box_deliver (d : I) (v : V) {x : M} (hx : x ∈ H d v) :
    HoldsS H (boxRun eV hNpos hN hF H tg) d 15 (tg d v x) x := by
  have hR := (Setup.square_correct (boxSetup_good eV hNpos hN hF hcard hload)).2
  have hin : (x, tg d v x) ∈ (boxSetup eV hNpos hN hF H tg).inp d (bprim eV hN v) := by
    simp only [boxSetup, bphi, bhost_bprim, if_true, pairsIn, mem_image]
    exact ⟨x, hx, rfl⟩
  have := holdsS_box eV hNpos hN hF hcard hload (hR.deliver d _ _ hin)
  simpa [boxSetup, bhost_bprim] using this

theorem box_known (w : V) :
    Determined (pairsIn H tg) (boxRun eV hNpos hN hF H tg) 15 w fun d => Recv H tg d w := by
  let σ := boxSetup eV hNpos hN hF H tg
  have hG : σ.Good := boxSetup_good eV hNpos hN hF hcard hload
  have h1 : Determined σ.inp σ.run 15 (bprim eV hN w)
      fun d => (σ.HE d (bprim eV hN w)).image Prod.fst :=
    (determined_received (r := 14) (by norm_num) _).map _
  have h2 := Determined.of_sim (bhost_inj eV hNpos hF) (bphi eV hNpos hN hF)
    (fun _ _ => rfl) h1
  rw [bhost_bprim] at h2
  refine (Determined.of_mapRun (unpairP_pairP (vdec_enc eV)) h2).congr fun d => ?_
  ext x
  simp only [Recv, mem_biUnion, mem_univ, true_and, mem_filter, mem_image, Prod.exists,
    exists_and_right, exists_eq_right]
  constructor
  · rintro ⟨v, hx, rfl⟩
    have hin : (x, tg d v x) ∈ σ.inp d (bprim eV hN v) := by
      simp only [σ, boxSetup, bphi, bhost_bprim, if_true, pairsIn, mem_image]
      exact ⟨x, hx, rfl⟩
    have h3 := Setup.HE_of_inp hG d hin
    exact ⟨tg d v x, h3⟩
  · rintro ⟨w', hw'⟩
    obtain ⟨⟨v'', hv''⟩, hdst⟩ := Setup.src_of_HE hG hw'
    have hw : w' = w := bprim_inj eV hN hdst
    subst hw
    simp only [σ, boxSetup, bphi] at hv''
    split_ifs at hv''
    · simp only [pairsIn, mem_image, Prod.mk.injEq] at hv''
      obtain ⟨y, hy, rfl, h2⟩ := hv''
      exact ⟨_, hy, h2⟩
    · simp at hv''

end Box

end CongestedCliqueRouting
