import Papers.PODC2013.CongestedCliqueRouting.SortSpec2
import Papers.PODC2013.CongestedCliqueRouting.Main

/-!
# Theorem 4.5: deterministic sorting on the congested clique within 37 rounds

Problem 4.1: node `i` is given `n` keys `keys i 0, …, keys i (n-1)` (all keys distinct, as the
paper assumes w.l.o.g.); node `v` must learn the keys whose rank in the global order lies in
`[v n, (v + 1) n)` (ranks counted from `0`; the paper's "indices `i(n-1)+1, …, in`" is a typo for
`(i-1)n+1, …, in`). Keys are opaque `O(log n)`-bit items that can only be forwarded by nodes
holding them; nodes may compare the keys they hold.

`theorem_4_5`: for every `n` there is a deterministic algorithm with packets of `384` slots and
numbers at most `32 n²` solving Problem 4.1 within 37 rounds (in fact 32). For `n` not a perfect
square the algorithm runs the square algorithm on `⌈√n⌉²` virtual nodes (at most two per node).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

section Model

variable {M : Type*} [LinearOrder M] {n B : ℕ}

/-- Node `v` holds key `x` at the beginning of round `t`. -/
def SortHolds (A : Algorithm (Fin n) (Fin n → M) M B) (keys : Fin n → Fin n → M) (t : ℕ)
    (v : Fin n) (x : M) : Prop :=
  (∃ j, keys v j = x) ∨ ∃ r < t, ∃ u i, A.sent keys r u v i = some (Item.msg x)

/-- Rank of `x` among all keys (number of keys below `x`). -/
def keyRank (keys : Fin n → Fin n → M) (x : M) : ℕ :=
  (univ.filter fun p : Fin n × Fin n => keys p.1 p.2 < x).card

/-- `A` solves Problem 4.1 within `T` rounds. -/
def SortSolves (A : Algorithm (Fin n) (Fin n → M) M B) (T : ℕ) : Prop :=
  ∀ keys : Fin n → Fin n → M, Function.Injective (fun p : Fin n × Fin n => keys p.1 p.2) →
    (∀ t < T, ∀ u v i k, A.sent keys t u v i = some (Item.num k) → k ≤ 32 * n ^ 2) ∧
    (∀ t < T, ∀ u v i x, A.sent keys t u v i = some (Item.msg x) → SortHolds A keys t u x) ∧
    (∀ i j (v : Fin n), (v : ℕ) = keyRank keys (keys i j) / n → SortHolds A keys T v (keys i j))

end Model

/-- Extending a routing run by silent rounds. -/
lemma Routes.extendTo {I V M : Type*} [Fintype V] [DecidableEq M] {B : ℕ}
    {msgs : I → V → Finset M} {dst : I → M → V} {S : Run I V M B} {T C : ℕ}
    (hR : Routes msgs dst S T C) (hT : ∀ d t, T ≤ t → ∀ u v i, S d t u v i = none) :
    ∀ k, Routes msgs dst S (T + k) C
  | 0 => hR
  | k + 1 => (Routes.extendTo hR hT k).extend fun d u v i => hT d (T + k) (by omega) u v i

section Inst

variable (M : Type*) [LinearOrder M] (n : ℕ)

/-- Sorting instances. -/
abbrev SortInst := {k : Fin n → Fin n → M // Function.Injective fun p : Fin n × Fin n => k p.1 p.2}

variable {M n}

/-- Keys of a node. -/
def keysOf (k : Fin n → M) : Finset M := univ.image k

/-- Input of a virtual node. -/
def svphi (v' : Fin (side n) × Fin (side n)) (k : Fin n → M) : Finset M :=
  if h : (vidx v' : ℕ) < n then keysOf k else ∅

/-- Output node of rank `r`. -/
def sout (hn : 0 < n) (r : ℕ) : Fin (side n) × Fin (side n) :=
  prim hn ⟨min (r / n) (n - 1), by omega⟩

/-- The virtual sorting setup. -/
def ssetup (hn : 0 < n) : SortSetup (SortInst M n) (Fin (side n) × Fin (side n)) M (side n) where
  e := Equiv.refl _
  inp d v' := svphi v' (d.1 (host hn v').1)
  out := sout hn

lemma ssetup_inp_sub (hn : 0 < n) (d : SortInst M n) (v' : Fin (side n) × Fin (side n)) :
    (ssetup hn).inp d v' ⊆ keysOf (d.1 (host hn v').1) := by
  simp only [ssetup, svphi]
  split_ifs
  · exact subset_rfl
  · exact empty_subset _

lemma mem_ssetup_inp (hn : 0 < n) {d : SortInst M n} {u : Fin n} {x : M} :
    x ∈ keysOf (d.1 u) → x ∈ (ssetup hn).inp d (prim hn u) := by
  intro hx
  simp only [ssetup, svphi, vidx_prim, u.isLt, dif_pos, host_prim]
  exact hx

lemma U_eq (hn : 0 < n) (d : SortInst M n) :
    (ssetup hn).U d = univ.image fun p : Fin n × Fin n => d.1 p.1 p.2 := by
  ext x
  rw [SortSetup.U, mem_biUnion, mem_image]
  constructor
  · rintro ⟨v', -, hv'⟩
    have := ssetup_inp_sub hn d v' hv'
    simp only [keysOf, mem_image, mem_univ, true_and] at this
    obtain ⟨j, rfl⟩ := this
    exact ⟨(_, j), mem_univ _, rfl⟩
  · rintro ⟨⟨i, j⟩, -, rfl⟩
    exact ⟨prim hn i, mem_univ _, mem_ssetup_inp hn (by simp [keysOf])⟩

lemma rk_U (hn : 0 < n) (d : SortInst M n) (x : M) :
    rk ((ssetup hn).U d) x = keyRank d.1 x := by
  unfold rk keyRank
  rw [U_eq, filter_image, card_image_of_injective _ d.2]

lemma card_U (hn : 0 < n) (d : SortInst M n) : ((ssetup hn).U d).card = n * n := by
  rw [U_eq, card_image_of_injective _ d.2]; simp

lemma ssetup_good (hn : 0 < n) : (ssetup (M := M) hn).Good where
  card_le d v' := by
    refine le_trans (card_le_card (ssetup_inp_sub hn d v')) ?_
    exact le_trans card_image_le (by simpa using le_side_sq hn)
  disj d u w huw := by
    rw [disjoint_left]
    intro x hu hw
    simp only [ssetup, svphi] at hu hw
    split_ifs at hu hw with h1 h2
    · simp only [keysOf, mem_image, mem_univ, true_and] at hu hw
      obtain ⟨j, rfl⟩ := hu
      obtain ⟨j', hj'⟩ := hw
      have := d.2 (a₁ := ((host hn w).1, j')) (a₂ := ((host hn u).1, j)) hj'
      simp only [Prod.mk.injEq] at this
      have h3 := this.1
      rw [host_of_lt hn h1, host_of_lt hn h2] at h3
      apply huw
      apply finProdFinEquiv.injective
      apply Fin.ext
      simp only [Fin.mk.injEq] at h3
      exact h3.symm
    all_goals simp at *
  out_le d w := by
    rw [card_U]
    by_cases hw : ∃ i : Fin n, prim hn i = w
    · obtain ⟨i, rfl⟩ := hw
      calc ((range (n * n)).filter fun r => sout hn r = prim hn i).card
          ≤ (Ico (i * n) (i * n + n)).card := by
            refine card_le_card fun r hr => ?_
            rw [mem_filter, mem_range] at hr
            simp only [sout] at hr
            have hinj : Function.Injective (prim hn) := by
              intro a b h
              have := congrArg (fun v => (vidx v : ℕ)) h
              simp only [vidx_prim] at this
              exact Fin.ext this
            have h1 := congrArg Fin.val (hinj hr.2)
            simp only at h1
            have h2 : r / n < n := (Nat.div_lt_iff_lt_mul hn).2 hr.1
            rw [min_eq_left (by omega)] at h1
            simp only [mem_Ico]
            constructor
            · rw [← h1]; exact Nat.div_mul_le_self r n
            · rw [← h1]
              have := Nat.lt_div_mul_add (a := r) hn
              linarith
        _ = n := by simp
        _ ≤ side n * side n := le_side_sq hn
    · push Not at hw
      rw [card_eq_zero.2]
      · exact Nat.zero_le _
      · rw [filter_eq_empty_iff]
        intro r _ h
        exact hw _ h

end Inst

/-- **Theorem 4.5** (Lenzen, PODC 2013): Problem 4.1 can be solved deterministically within
37 rounds on the congested clique, with packets of `384` slots of `O(log n)` bits each. -/
theorem theorem_4_5 (M : Type*) [LinearOrder M] (n : ℕ) :
    ∃ A : Algorithm (Fin n) (Fin n → M) M (2 * (2 * SB)), SortSolves A 37 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ _ _ _ _ _ => none, fun k _ => ⟨fun _ _ u => u.elim0, fun _ _ u => u.elim0,
      fun i => i.elim0⟩⟩
  set τ := ssetup (M := M) hn
  obtain ⟨hloc, hR⟩ := SortSetup.sort_correct (ssetup_good (M := M) hn)
  have hsilent : ∀ d t, 32 ≤ t → ∀ u v i, τ.run d t u v i = none := by
    intro d t ht u v i
    simp only [SortSetup.run]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    simp [ofList]
  have hR37 := Routes.extendTo hR hsilent 5
  let realInp : SortInst M n → Fin n → (Fin n → M) := fun d u => d.1 u
  have hlocR : IsLocal realInp (simRun (host hn) τ.run) :=
    simRun_isLocal (host_injective hn) svphi (fun d v' => rfl) hloc
  let dstR : SortInst M n → M → Fin n := fun d x => ⟨min (keyRank d.1 x / n) (n - 1), by omega⟩
  have hRR : Routes (fun d u => keysOf (d.1 u)) dstR (simRun (host hn) τ.run) 37
      (8 * (side n * side n * side n)) :=
    simRun_routes (host_injective hn) (ssetup_inp_sub hn)
      (fun d u m hm => ⟨prim hn u, mem_ssetup_inp hn hm⟩)
      (fun d x => by
        show (host hn (sout hn (rk (τ.U d) x))).1 = _
        rw [rk_U]
        exact host_prim hn _) hR37
  refine ⟨synth realInp (simRun (host hn) τ.run), fun keys hk => ?_⟩
  let D : SortInst M n := ⟨keys, hk⟩
  have hsent : ∀ t u v, (synth realInp (simRun (host hn) τ.run)).sent keys t u v =
      simRun (host hn) τ.run D t u v := fun t u v => synth_sent hlocR D t u v
  have hholds : ∀ t v x, HoldsS (fun d u => keysOf (d.1 u)) (simRun (host hn) τ.run) D t v x →
      SortHolds (synth realInp (simRun (host hn) τ.run)) keys t v x := by
    rintro t v x (hh | ⟨r, hr, u, i, hh⟩)
    · simp only [keysOf, mem_image, mem_univ, true_and] at hh
      exact Or.inl hh
    · exact Or.inr ⟨r, hr, u, i, by rw [hsent]; exact hh⟩
  have hcube : 8 * (side n * side n * side n) ≤ 32 * n ^ 2 := by
    have h1 := side_sq_le hn
    have h2 : side n ≤ side n * side n :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))
    have h3 : side n * side n * side n ≤ (2 * n) * (2 * n) := Nat.mul_le_mul h1 (h2.trans h1)
    nlinarith
  refine ⟨fun t ht u v i k h => ?_, fun t ht u v i x h => ?_, fun i j v hv => ?_⟩
  · rw [hsent] at h
    exact (hRR.num_le _ t ht u v i k h).trans hcube
  · rw [hsent] at h
    exact hholds _ _ _ (hRR.valid _ t ht u v i x h)
  · have := hholds _ _ _ (hRR.deliver D i (keys i j) (by simp [keysOf, D]))
    have hv' : dstR D (keys i j) = v := by
      apply Fin.ext
      show min (keyRank keys (keys i j) / n) (n - 1) = v
      have : keyRank keys (keys i j) < n * n := by
        rw [← rk_U hn D]
        have := rk_lt_card (H := τ.U D) (x := keys i j) (by
          rw [U_eq]; exact mem_image.2 ⟨(i, j), mem_univ _, rfl⟩)
        rwa [card_U] at this
      have : keyRank keys (keys i j) / n < n := (Nat.div_lt_iff_lt_mul hn).2 this
      rw [min_eq_left (by omega), hv]
    rwa [hv'] at this

end CongestedCliqueRouting
