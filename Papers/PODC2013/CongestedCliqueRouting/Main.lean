import Papers.PODC2013.CongestedCliqueRouting.SquareMain
import Papers.PODC2013.CongestedCliqueRouting.Simulation

/-!
# Theorem 3.7: deterministic routing on the congested clique in 16 rounds

`theorem_3_7`: there is an absolute constant number of slots per packet (`12`) such that for
every `n` there is a deterministic congested-clique algorithm that solves every instance of the
information distribution task with at most `n` messages per source and per destination
(Problem 3.1 and its relaxation) within 16 rounds (in fact 15), sending numbers `≤ 8 n²`.

For `n` nodes we run the square algorithm on `s² ≥ n` virtual nodes, `s = ⌈√n⌉`, each real node
hosting at most two of them (`s² ≤ 2n`).
-/

set_option linter.unusedSectionVars false

namespace CongestedCliqueRouting

open Finset

/-- Extending a routing run by a silent round. -/
lemma Routes.extend {I V M : Type*} [Fintype V] [DecidableEq M] {B : ℕ}
    {msgs : I → V → Finset M} {dst : I → M → V} {S : Run I V M B} {T C : ℕ}
    (hR : Routes msgs dst S T C) (hT : ∀ d u v i, S d T u v i = none) :
    Routes msgs dst S (T + 1) C where
  num_le d t ht u v i k h := by
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact hR.num_le d t ht u v i k h
    · rw [hT] at h; simp at h
  valid d t ht u v i m h := by
    rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
    · exact hR.valid d t ht u v i m h
    · rw [hT] at h; simp at h
  deliver d v m hm := (hR.deliver d v m hm).mono (Nat.le_succ T)

section Side

/-- `⌈√n⌉` for `n ≥ 1`. -/
def side (n : ℕ) : ℕ := Nat.sqrt (n - 1) + 1

instance (n : ℕ) : NeZero (side n) := ⟨by simp [side]⟩

lemma le_side_sq {n : ℕ} (hn : 0 < n) : n ≤ side n * side n := by
  have := Nat.lt_succ_sqrt (n - 1)
  simp only [Nat.succ_eq_add_one] at this
  unfold side
  omega

lemma side_sq_le {n : ℕ} (hn : 0 < n) : side n * side n ≤ 2 * n := by
  have h := Nat.sqrt_le (n - 1)
  unfold side
  set r := Nat.sqrt (n - 1)
  have : 2 * r ≤ r * r + 1 := by nlinarith [sq_nonneg ((r : ℤ) - 1)]
  calc (r + 1) * (r + 1) = r * r + 2 * r + 1 := by ring
    _ ≤ r * r + (r * r + 1) + 1 := by omega
    _ ≤ 2 * n := by omega

lemma side_cube_le {n : ℕ} (hn : 0 < n) : side n * side n * side n ≤ 8 * n ^ 2 := by
  have h1 := side_sq_le hn
  have h2 : side n ≤ side n * side n := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (NeZero.ne _))
  calc side n * side n * side n ≤ (2 * n) * (2 * n) := Nat.mul_le_mul h1 (h2.trans h1)
    _ ≤ 8 * n ^ 2 := by nlinarith

end Side

variable (n : ℕ)

/-- Routing instances with at most `n` messages per destination. -/
abbrev GoodInstance := {d : RoutingInstance n // d.LoadOK}

/-- The messages of node `u` with input `k`. -/
def msgsK (u : Fin n) (k : Fin n → Option (Fin n)) : Finset (Header n) :=
  univ.filter fun h => h.src = u ∧ k h.idx = some h.dst

/-- The messages initially held by node `u`. -/
def realMsgs (d : GoodInstance n) (u : Fin n) : Finset (Header n) := msgsK n u (d.1 u)

lemma card_msgsK_le (u : Fin n) (k : Fin n → Option (Fin n)) : (msgsK n u k).card ≤ n := by
  calc (msgsK n u k).card ≤ (univ : Finset (Fin n)).card := by
        refine card_le_card_of_injOn (fun h => h.idx) (fun _ _ => mem_univ _) ?_
        rintro ⟨s1, i1, d1⟩ h1 ⟨s2, i2, d2⟩ h2 heq
        simp only [msgsK, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h1 h2
        simp only at heq
        subst heq
        obtain ⟨rfl, h1⟩ := h1
        obtain ⟨rfl, h2⟩ := h2
        rw [h1, Option.some.injEq] at h2
        rw [h2]
    _ = n := by simp

section Virtual

variable {n}

/-- Index of a virtual node. -/
def vidx (v' : Fin (side n) × Fin (side n)) : Fin (side n * side n) := finProdFinEquiv v'

/-- Host and local index of a virtual node. -/
def host (hn : 0 < n) (v' : Fin (side n) × Fin (side n)) : Fin n × Fin 2 :=
  (⟨(vidx v' : ℕ) % n, Nat.mod_lt _ hn⟩,
    ⟨(vidx v' : ℕ) / n, by
      have h1 := (vidx v').isLt
      have h2 := side_sq_le hn
      exact (Nat.div_lt_iff_lt_mul hn).2 (by omega)⟩)

lemma host_injective (hn : 0 < n) : Function.Injective (host hn) := by
  intro v w h
  simp only [host, Prod.mk.injEq, Fin.mk.injEq] at h
  have : (vidx v : ℕ) = vidx w := by
    rw [← Nat.mod_add_div (vidx v : ℕ) n, ← Nat.mod_add_div (vidx w : ℕ) n, h.1, h.2]
  exact finProdFinEquiv.injective (Fin.ext this)

/-- The virtual node of real node `u` (its primary virtual node). -/
def prim (hn : 0 < n) (u : Fin n) : Fin (side n) × Fin (side n) :=
  finProdFinEquiv.symm ⟨u, lt_of_lt_of_le u.isLt (le_side_sq hn)⟩

lemma vidx_prim (hn : 0 < n) (u : Fin n) : (vidx (prim hn u) : ℕ) = u := by
  simp only [vidx, prim, Equiv.apply_symm_apply]

lemma host_prim (hn : 0 < n) (u : Fin n) : (host hn (prim hn u)).1 = u := by
  ext; simp [host, vidx_prim, Nat.mod_eq_of_lt u.isLt]

lemma host_of_lt (hn : 0 < n) {v' : Fin (side n) × Fin (side n)} (h : (vidx v' : ℕ) < n) :
    (host hn v').1 = ⟨vidx v', h⟩ := by
  ext; simp [host, Nat.mod_eq_of_lt h]

/-- Input of a virtual node, computed from its host's input. -/
def vphi (v' : Fin (side n) × Fin (side n)) (k : Fin n → Option (Fin n)) : Finset (Header n) :=
  if h : (vidx v' : ℕ) < n then msgsK n ⟨vidx v', h⟩ k else ∅

/-- The virtual setup: square algorithm on `side n × side n` virtual nodes. -/
def vsetup (hn : 0 < n) : Setup (GoodInstance n) (Fin (side n) × Fin (side n)) (Header n) (side n) where
  e := Equiv.refl _
  dst h := prim hn h.dst
  inp d v' := vphi v' (d.1 (host hn v').1)

lemma vsetup_inp_sub (hn : 0 < n) (d : GoodInstance n) (v' : Fin (side n) × Fin (side n)) :
    (vsetup hn).inp d v' ⊆ realMsgs n d (host hn v').1 := by
  simp only [vsetup, vphi]
  split_ifs with h
  · rw [host_of_lt hn h]; rfl
  · exact empty_subset _

lemma mem_vsetup_inp (hn : 0 < n) {d : GoodInstance n} {v' : Fin (side n) × Fin (side n)}
    {h : Header n} (hh : h ∈ (vsetup hn).inp d v') : (h.src : ℕ) = vidx v' := by
  simp only [vsetup, vphi] at hh
  split_ifs at hh with hlt
  · simp only [msgsK, mem_filter, mem_univ, true_and] at hh
    rw [hh.1]
  · simp at hh

lemma vsetup_good (hn : 0 < n) : (vsetup hn).Good where
  card_le d v' := by
    simp only [vsetup, vphi]
    split_ifs
    · exact (card_msgsK_le n _ _).trans (le_side_sq hn)
    · simp
  load_le d w' := by
    classical
    set A := fun v' => ((vsetup hn).inp d v').filter fun m => (vsetup hn).dst m = w'
    have hdisj : ∀ x ∈ (univ : Finset (Fin (side n) × Fin (side n))),
        ∀ y ∈ (univ : Finset (Fin (side n) × Fin (side n))), x ≠ y → Disjoint (A x) (A y) := by
      intro x _ y _ hxy
      rw [disjoint_left]
      intro h hx hy
      have h1 := mem_vsetup_inp hn (mem_filter.1 hx).1
      have h2 := mem_vsetup_inp hn (mem_filter.1 hy).1
      exact hxy (finProdFinEquiv.injective (Fin.ext (h1.symm.trans h2)))
    rw [← card_biUnion hdisj]
    set S := univ.filter fun h : Header n => d.1 h.src h.idx = some h.dst ∧ prim hn h.dst = w'
    have hsub : univ.biUnion A ⊆ S := by
      intro h hh
      simp only [mem_biUnion, mem_univ, true_and] at hh
      obtain ⟨v', hv'⟩ := hh
      rw [mem_filter] at hv'
      have := vsetup_inp_sub hn d v' hv'.1
      simp only [realMsgs, msgsK, mem_filter, mem_univ, true_and] at this
      simp only [S, mem_filter, mem_univ, true_and]
      refine ⟨?_, hv'.2⟩
      rw [this.1]; exact this.2
    refine (card_le_card hsub).trans ((?_ : S.card ≤ n).trans (le_side_sq hn))
    by_cases hS : S.Nonempty
    · obtain ⟨h0, hh0⟩ := hS
      have hh0' := (mem_filter.1 hh0).2
      calc S.card = (S.image fun h => (h.src, h.idx)).card := by
            refine (card_image_of_injOn ?_).symm
            rintro ⟨s1, i1, d1⟩ h1 ⟨s2, i2, d2⟩ h2 heq
            simp only [S, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at h1 h2
            simp only [Prod.mk.injEq] at heq
            obtain ⟨rfl, rfl⟩ := heq
            rw [h1.1, Option.some.injEq] at h2
            rw [h2.1]
        _ ≤ (univ.filter fun p : Fin n × Fin n => d.1 p.1 p.2 = some h0.dst).card := by
            refine card_le_card fun p hp => ?_
            simp only [mem_image] at hp
            obtain ⟨h, hh, rfl⟩ := hp
            have hh' := (mem_filter.1 hh).2
            have : h.dst = h0.dst := by
              have := hh'.2.trans hh0'.2.symm
              have := congrArg (fun v => (vidx v : ℕ)) this
              simp only [vidx_prim] at this
              exact Fin.ext this
            simp only [mem_filter, mem_univ, true_and]
            rw [← this]; exact hh'.1
        _ ≤ n := d.2 h0.dst
    · rw [not_nonempty_iff_eq_empty] at hS
      simp [hS]

end Virtual

/-- **Theorem 3.7** (Lenzen, PODC 2013): the information distribution task (Problem 3.1, and
its relaxation to at most `n` messages per source and destination) can be solved
deterministically within 16 rounds on the congested clique, with packets of `12` slots of
`O(log n)` bits each (numbers at most `8 n²`). -/
theorem theorem_3_7 (n : ℕ) :
    ∃ A : Algorithm (Fin n) (Fin n → Option (Fin n)) (Header n) 12, Solves A 16 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun _ _ _ _ _ _ => none, fun d _ => ⟨fun _ _ u => u.elim0, fun _ _ u => u.elim0,
      fun i => i.elim0⟩⟩
  set σ := vsetup hn
  obtain ⟨hloc, hR⟩ := Setup.square_correct (vsetup_good hn)
  have hR16 : Routes σ.inp (fun _ => σ.dst) σ.run 16 (side n * side n * side n) :=
    hR.extend fun d u v i => rfl
  let realInp : GoodInstance n → Fin n → (Fin n → Option (Fin n)) := fun d u => d.1 u
  have hlocR : IsLocal realInp (simRun (host hn) σ.run) :=
    simRun_isLocal (host_injective hn) vphi (fun d v' => rfl) hloc
  have hRR : Routes (realMsgs n) (fun _ => Header.dst) (simRun (host hn) σ.run) 16
      (side n * side n * side n) :=
    simRun_routes (host_injective hn) (vsetup_inp_sub hn)
      (fun d u m hm => ⟨prim hn u, by
        simp only [vsetup, vphi, vidx_prim, u.isLt, dite_true]
        rw [host_prim]
        simpa [realMsgs] using hm⟩)
      (fun _ m => host_prim hn m.dst) hR16
  refine ⟨synth realInp (simRun (host hn) σ.run), fun d hd => ?_⟩
  have hsent : ∀ t u v, (synth realInp (simRun (host hn) σ.run)).sent d t u v =
      simRun (host hn) σ.run ⟨d, hd⟩ t u v := fun t u v => synth_sent hlocR ⟨d, hd⟩ t u v
  have hholds : ∀ t v h, HoldsS (realMsgs n) (simRun (host hn) σ.run) ⟨d, hd⟩ t v h →
      Holds (synth realInp (simRun (host hn) σ.run)) d t v h := by
    rintro t v h (hh | ⟨r, hr, u, i, hh⟩)
    · simp only [realMsgs, msgsK, mem_filter, mem_univ, true_and] at hh
      exact Or.inl hh
    · exact Or.inr ⟨r, hr, u, i, by rw [hsent]; exact hh⟩
  refine ⟨fun t ht u v i k h => ?_, fun t ht u v i h hh => ?_, fun i j k hk => ?_⟩
  · rw [hsent] at h
    exact (hRR.num_le _ t ht u v i k h).trans (side_cube_le hn)
  · rw [hsent] at hh
    exact hholds _ _ _ (hRR.valid _ t ht u v i h hh)
  · exact hholds _ _ _ (hRR.deliver ⟨d, hd⟩ i ⟨i, j, k⟩ (by simp [realMsgs, msgsK, hk]))

/-- Problem 3.1 exactly as stated in the paper: every node has exactly `n` messages
(`d i j = some _` for all `i, j`) and is the destination of exactly `n` messages. -/
theorem theorem_3_7_exact (n : ℕ) :
    ∃ A : Algorithm (Fin n) (Fin n → Option (Fin n)) (Header n) 12,
      ∀ dest : Fin n → Fin n → Fin n,
        (∀ k, (univ.filter fun p : Fin n × Fin n => dest p.1 p.2 = k).card = n) →
        (∀ i j, Holds A (fun i j => some (dest i j)) 16 (dest i j) ⟨i, j, dest i j⟩) := by
  obtain ⟨A, hA⟩ := theorem_3_7 n
  refine ⟨A, fun dest hdest i j => ?_⟩
  have hload : RoutingInstance.LoadOK (n := n) (fun i j => some (dest i j)) := by
    intro k
    simp only [Option.some.injEq]
    exact (hdest k).le
  exact (hA _ hload).2.2 i j _ rfl

end CongestedCliqueRouting
