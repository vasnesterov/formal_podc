import Papers.PODC2013.CongestedCliqueRouting.SquarePhaseBCD

/-!
# The square algorithm is local and routes all messages in 15 rounds

`Setup.square_correct`: for `n = s²` nodes, every node holding at most `s²` messages and every
node being the destination of at most `s²` messages, the intended run `σ.run` is implementable by
a deterministic algorithm (`IsLocal`), uses packets of three slots, numbers `≤ s³`, forwards only
held messages, and delivers every message within 15 rounds.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

section KnowGeneric

variable {I V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] {s : ℕ}
  {K : Type*} {inp : I → V → K} {S : Run I V M 3} (e : V ≃ Fin s × Fin s)

/-- After a group announcement in rounds `t, t+1`, every node knows the vectors of its
group-mates. -/
lemma ga_known {t : ℕ} {x : I → V → Fin s → ℕ} (h0 : ∀ d, S d t = ga1 e (x d))
    (h1 : ∀ d, S d (t + 1) = ga2 e (S d t)) (w : V) :
    Determined inp S (t + 2) w (fun d => fun b j => x d (node e (grp e w) b) j) := by
  refine Determined.congr ((determined_recv (r := t + 1) (by omega) w).map
    (fun f => fun b j => numAt (f (node e j b)))) (fun d => ?_)
  funext b j
  simp only [h1, h0, ga2_ga1, numAt_pNum]

/-- After a broadcast in round `t`, everybody knows the broadcast matrix. -/
lemma bc_known {t : ℕ} {T : I → Fin s → Fin s → ℕ} (h0 : ∀ d, S d t = bc e (T d)) (w : V) :
    Determined inp S (t + 1) w T := by
  refine Determined.congr ((determined_recv (r := t) (by omega) w).map
    (fun f => fun a j => numAt (f (node e a j)))) (fun d => ?_)
  funext a j
  simp [h0, bc]

end KnowGeneric

lemma nums_c33a {M : Type*} [DecidableEq M] {r : Option (M × ℕ × ℕ)} {i : Fin 3} {k : ℕ}
    (h : c33a r i = some (Item.num k)) : ∃ m y k', r = some (m, y, k') ∧ (k = y ∨ k = k') := by
  rcases r with _ | ⟨m, y, k'⟩
  · simp [c33a, pkt0] at h
  · exact ⟨m, y, k', rfl, nums_pMsg3 h⟩

lemma c33a_slot2 {M : Type*} [DecidableEq M] {r : Option (M × ℕ × ℕ)} {k : ℕ}
    (h : c33a r 2 = some (Item.num k)) : ∃ m y, r = some (m, y, k) := by
  rcases r with _ | ⟨m, y, k'⟩
  · simp [c33a, pkt0] at h
  · simp [c33a, pMsg3] at h
    exact ⟨m, y, by rw [h]⟩

lemma decode2_slot0 {M : Type*} [DecidableEq M] {p : Packet M 3} {m : M} {k : ℕ} (h : (m, k) ∈ decode2 p) :
    p 0 = some (Item.msg m) := by
  unfold decode2 at h
  split at h
  · rename_i m' k' h0 _
    simp only [mem_singleton, Prod.mk.injEq] at h
    rw [h0, h.1]
  · simp at h

namespace Setup

variable {I V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] [Nonempty V] {s : ℕ}
  [NeZero s] (σ : Setup I V M s)

/-! ### Congruence: local decisions depend only on known data -/

section Congr

variable {d d' : I}

lemma Tp_congr (h : σ.T d = σ.T d') : σ.Tp d = σ.Tp d' := by unfold Tp; rw [h]

lemma q_congr {a : Fin s} (hC : σ.C d a = σ.C d' a) (hT : σ.T d = σ.T d') :
    σ.q d a = σ.q d' a := by
  funext j; unfold q; rw [hC, Tp_congr σ hT]

lemma E_congr {a : Fin s} (hC : σ.C d a = σ.C d' a) (hT : σ.T d = σ.T d') :
    σ.E d a = σ.E d' a := by
  funext b x; unfold E; rw [q_congr σ hC hT]

lemma Ep_congr {a : Fin s} (hC : σ.C d a = σ.C d' a) (hT : σ.T d = σ.T d') :
    σ.Ep d a = σ.Ep d' a := by
  unfold Ep; rw [E_congr σ hC hT]

lemma Rp_congr {a : Fin s} (hC : σ.C d a = σ.C d' a) (hT : σ.T d = σ.T d') :
    σ.Rp d a = σ.Rp d' a := by
  unfold Rp R; rw [Ep_congr σ hC hT]

lemma relA_congr {v : V} (hI : σ.inp d v = σ.inp d' v)
    (hC : σ.C d (grp σ.e v) = σ.C d' (grp σ.e v)) (hT : σ.T d = σ.T d') :
    σ.relA d v = σ.relA d' v := by
  have hx : σ.xA d v = σ.xA d' v := by unfold xA; rw [hI, q_congr σ hC hT]
  have hy : σ.yA d v = σ.yA d' v := by unfold yA; rw [hI, hx, Ep_congr σ hC hT]
  unfold relA; rw [hI, hx, hy, Rp_congr σ hC hT]

lemma relB_congr {v : V} (hH : σ.HB d v = σ.HB d' v)
    (hF : σ.F d (grp σ.e v) = σ.F d' (grp σ.e v)) : σ.relB d v = σ.relB d' v := by
  have hFp : σ.Fp d (grp σ.e v) = σ.Fp d' (grp σ.e v) := by unfold Fp; rw [hF]
  have hy : σ.yB d v = σ.yB d' v := by unfold yB; rw [hH, hFp]
  have hR : σ.R1p d (grp σ.e v) = σ.R1p d' (grp σ.e v) := by unfold R1p R1; rw [hFp]
  unfold relB; rw [hH, hy, hR]

lemma relD_congr {v : V} (hH : σ.HD d v = σ.HD d' v)
    (hG3 : σ.G3 d (grp σ.e v) = σ.G3 d' (grp σ.e v)) : σ.relD d v = σ.relD d' v := by
  have hp : σ.G3p d (grp σ.e v) = σ.G3p d' (grp σ.e v) := by unfold G3p; rw [hG3]
  unfold relD; rw [hH, hp]

end Congr

/-! ### Locality -/

lemma C_known (w : V) : Determined σ.inp σ.run 2 w (fun d => σ.C d (grp σ.e w)) :=
  ga_known (t := 0) σ.e (x := σ.c0) (fun _ => rfl) (fun _ => rfl) w

lemma T_known (w : V) : Determined σ.inp σ.run 3 w σ.T :=
  bc_known (t := 2) σ.e (T := σ.T) (fun _ => rfl) w

lemma F_known (w : V) : Determined σ.inp σ.run 8 w (fun d => σ.F d (grp σ.e w)) :=
  ga_known (t := 6) σ.e (x := σ.c1) (fun _ => rfl) (fun _ => rfl) w

lemma G3_known (w : V) : Determined σ.inp σ.run 13 w (fun d => σ.G3 d (grp σ.e w)) :=
  ga_known (t := 11) σ.e (x := σ.c3) (fun _ => rfl) (fun _ => rfl) w

lemma HB_known (v : V) : Determined σ.inp σ.run 6 v (fun d => σ.HB d v) :=
  determined_received (r := 5) (by norm_num) v

lemma HC_known (v : V) : Determined σ.inp σ.run 10 v (fun d => σ.HC d v) :=
  determined_received (r := 9) (by norm_num) v

lemma HD_known (v : V) : Determined σ.inp σ.run 11 v (fun d => σ.HD d v) :=
  determined_received (r := 10) (by norm_num) v

/-- A packet vector that is a function of the packets received in the previous round is
determined. -/
lemma relay_known {t : ℕ} (v : V) (Φ : (V → Packet M 3) → V → Packet M 3)
    (h : ∀ d, σ.run d (t + 1) v = Φ (fun u => σ.run d t u v)) :
    Determined σ.inp σ.run (t + 1) v (fun d => σ.run d (t + 1) v) :=
  ((determined_recv (r := t) (by omega) v).map Φ).congr h

theorem run_isLocal : IsLocal σ.inp σ.run := by
  intro t v
  match t with
  | 0 =>
    exact ((determined_inp 0 v).map fun H => fun w =>
      if mem σ.e w = mem σ.e v then pNum (cnt H σ.dg (grp σ.e w)) else pkt0).congr
      (fun d => rfl)
  | 1 =>
    exact σ.relay_known v (fun f w => f (node σ.e (grp σ.e w) (mem σ.e v))) (fun d => rfl)
  | 2 =>
    refine (((C_known σ v).map fun Cm => ∑ b, Cm b (mem σ.e v)).map fun x => fun _ =>
      (pNum x : Packet M 3)).congr fun d => ?_
    funext w
    simp [run, P2, bc, T, C]
  | 3 =>
    intro d d' hv
    show (fun c => c33a (σ.relA d v c)) = fun c => c33a (σ.relA d' v c)
    rw [σ.relA_congr (determined_inp 3 v d d' hv) ((C_known σ v).mono (by norm_num) d d' hv)
      (T_known σ v d d' hv)]
  | 4 =>
    exact σ.relay_known v (fun f w => c33b σ.e f w) (fun d => rfl)
  | 5 =>
    exact σ.relay_known v (fun f z => scatter σ.e (univ.biUnion fun c => decode2 (f c))
      Prod.snd Prod.fst z) (fun d => rfl)
  | 6 =>
    exact ((HB_known σ v).map fun H => fun w =>
      if mem σ.e w = mem σ.e v then pNum (cnt H σ.dg (grp σ.e w)) else pkt0).congr
      (fun d => rfl)
  | 7 =>
    exact σ.relay_known v (fun f w => f (node σ.e (grp σ.e w) (mem σ.e v))) (fun d => rfl)
  | 8 =>
    intro d d' hv
    show (fun c => c33a (σ.relB d v c)) = fun c => c33a (σ.relB d' v c)
    rw [σ.relB_congr ((HB_known σ v).mono (by norm_num) d d' hv) (F_known σ v d d' hv)]
  | 9 =>
    exact σ.relay_known v (fun f w => c33b σ.e f w) (fun d => rfl)
  | 10 =>
    exact σ.relay_known v (fun f z => scatter σ.e (univ.biUnion fun u => msgsOf (f u))
      (fun m => (σ.dg m : ℕ)) id z) (fun d => rfl)
  | 11 =>
    exact ((HD_known σ v).map fun H => fun w =>
      if mem σ.e w = mem σ.e v then pNum (cnt H σ.dm (grp σ.e w)) else pkt0).congr
      (fun d => rfl)
  | 12 =>
    exact σ.relay_known v (fun f w => f (node σ.e (grp σ.e w) (mem σ.e v))) (fun d => rfl)
  | 13 =>
    intro d d' hv
    show (fun c => c33a (σ.relD d v c)) = fun c => c33a (σ.relD d' v c)
    rw [σ.relD_congr ((HD_known σ v).mono (by norm_num) d d' hv) (G3_known σ v d d' hv)]
  | 14 =>
    exact σ.relay_known v (fun f w => c33b σ.e f w) (fun d => rfl)
  | t + 15 => exact determined_const _ v (fun _ => pkt0)

/-! ### Routing specification -/

variable {σ}

lemma le_cube (x : ℕ) (hx : x ≤ s * s) : x ≤ s * s * s := by
  have : 1 ≤ s := Nat.one_le_iff_ne_zero.2 (NeZero.ne s)
  calc x ≤ s * s := hx
    _ = s * s * 1 := by ring
    _ ≤ s * s * s := Nat.mul_le_mul_left _ this

lemma fin_le_cube (x : Fin s) : (x : ℕ) ≤ s * s * s := by
  have : 1 ≤ s := Nat.one_le_iff_ne_zero.2 (NeZero.ne s)
  refine le_cube _ (le_trans x.isLt.le ?_)
  calc s = s * 1 := by ring
    _ ≤ s * s := Nat.mul_le_mul_left _ this

lemma holds_of_rcvd {d : I} {r t : ℕ} {v : V} {m : M} (hr : r < t)
    (h : m ∈ rcvd (σ.run d r) v) : HoldsS σ.inp σ.run d t v m :=
  holdsS_of_mem_received h hr

theorem run_num_le (hG : σ.Good) (d : I) (t : ℕ) (ht : t < 15) (u v : V) (i : Fin 3) (k : ℕ)
    (h : σ.run d t u v i = some (Item.num k)) : k ≤ s * s * s := by
  have hc0 : ∀ u j, σ.c0 d u j ≤ s * s * s := fun u j =>
    le_cube _ (le_trans (card_filter_le _ _) (hG.card_le d u))
  have hc1 : ∀ u j, σ.c1 d u j ≤ s * s * s := fun u j =>
    le_cube _ (le_trans (card_filter_le _ _) (card_HB_le d u))
  have hc3 : ∀ u j, σ.c3 d u j ≤ s * s * s := fun u j =>
    le_cube _ (le_trans (card_filter_le _ _) (card_HD_le d u))
  interval_cases t
  · obtain ⟨j, rfl⟩ := nums_ga1 σ.e h; exact hc0 _ _
  · obtain ⟨u', j, rfl⟩ := nums_ga2_ga1 σ.e h; exact hc0 _ _
  · have := nums_pNum h
    subst this
    calc σ.T d (grp σ.e u) (mem σ.e u) ≤ ∑ j, σ.T d (grp σ.e u) j :=
          single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
      _ ≤ s * (s * s) := T_row hG d _
      _ = s * s * s := by ring
  · obtain ⟨m, y, k', hr, hk⟩ := nums_c33a h
    obtain ⟨-, rfl, rfl, -⟩ := relA_spec hG d hr
    rcases hk with rfl | rfl <;> exact fin_le_cube _
  · obtain ⟨u', hu'⟩ := nums_c33b σ.e h
    obtain ⟨m, y, hr⟩ := c33a_slot2 hu'
    obtain ⟨-, -, rfl, -⟩ := relA_spec hG d hr
    exact fin_le_cube _
  · exact (nums_scatter σ.e h).elim
  · obtain ⟨j, rfl⟩ := nums_ga1 σ.e h; exact hc1 _ _
  · obtain ⟨u', j, rfl⟩ := nums_ga2_ga1 σ.e h; exact hc1 _ _
  · obtain ⟨m, y, k', hr, hk⟩ := nums_c33a h
    obtain ⟨-, rfl, rfl, -⟩ := relB_spec hG d hr
    rcases hk with rfl | rfl
    · exact fin_le_cube _
    · exact Nat.zero_le _
  · obtain ⟨u', hu'⟩ := nums_c33b σ.e h
    obtain ⟨m, y, hr⟩ := c33a_slot2 hu'
    obtain ⟨-, -, rfl, -⟩ := relB_spec hG d hr
    exact Nat.zero_le _
  · exact (nums_scatter σ.e h).elim
  · obtain ⟨j, rfl⟩ := nums_ga1 σ.e h; exact hc3 _ _
  · obtain ⟨u', j, rfl⟩ := nums_ga2_ga1 σ.e h; exact hc3 _ _
  · obtain ⟨m, y, k', hr, hk⟩ := nums_c33a h
    obtain ⟨-, rfl, rfl, -⟩ := relD_spec hG d hr
    rcases hk with rfl | rfl
    · exact fin_le_cube _
    · exact Nat.zero_le _
  · obtain ⟨u', hu'⟩ := nums_c33b σ.e h
    obtain ⟨m, y, hr⟩ := c33a_slot2 hu'
    obtain ⟨-, -, rfl, -⟩ := relD_spec hG d hr
    exact Nat.zero_le _

theorem run_valid (hG : σ.Good) (d : I) (t : ℕ) (ht : t < 15) (u v : V) (i : Fin 3) (m : M)
    (h : σ.run d t u v i = some (Item.msg m)) : HoldsS σ.inp σ.run d t u m := by
  have hm : m ∈ msgsOf (σ.run d t u v) := mem_msgsOf.2 ⟨i, h⟩
  interval_cases t
  · simp [run, P0, msgsOf_ga1] at hm
  · simp [run, P1, P0, msgsOf_ga2_ga1] at hm
  · simp [run, P2, bc] at hm
  · exact Or.inl (msgsOf_c33a_relayOf hm)
  · obtain ⟨u', hu'⟩ := msgsOf_c33b σ.e hm
    exact holds_of_rcvd (r := 3) (by norm_num) (mem_rcvd.2 ⟨u', hu'⟩)
  · obtain ⟨⟨m', k⟩, hb, rfl, -, -⟩ := msgsOf_scatter σ.e hm
    simp only [TA, tagged, mem_biUnion, mem_univ, true_and] at hb
    obtain ⟨c, hc⟩ := hb
    exact Or.inr ⟨4, by norm_num, c, 0, decode2_slot0 hc⟩
  · simp [run, P6, msgsOf_ga1] at hm
  · simp [run, P7, P6, msgsOf_ga2_ga1] at hm
  · exact holds_of_rcvd (r := 5) (by norm_num) (msgsOf_c33a_relayOf hm)
  · obtain ⟨u', hu'⟩ := msgsOf_c33b σ.e hm
    exact holds_of_rcvd (r := 8) (by norm_num) (mem_rcvd.2 ⟨u', hu'⟩)
  · obtain ⟨m', hb, rfl, -, -⟩ := msgsOf_scatter σ.e hm
    exact holds_of_rcvd (r := 9) (by norm_num) hb
  · simp [run, P11, msgsOf_ga1] at hm
  · simp [run, P12, P11, msgsOf_ga2_ga1] at hm
  · exact holds_of_rcvd (r := 10) (by norm_num) (msgsOf_c33a_relayOf hm)
  · obtain ⟨u', hu'⟩ := msgsOf_c33b σ.e hm
    exact holds_of_rcvd (r := 13) (by norm_num) (mem_rcvd.2 ⟨u', hu'⟩)

/-- **Square case of Theorem 3.7** (with the fixes listed in `differencies.md`): on `s²` nodes,
with at most `s²` messages per source and per destination, the intended run is implementable
and routes every message within 15 rounds, with packets of 3 slots and numbers `≤ s³`. -/
theorem square_correct (hG : σ.Good) :
    IsLocal σ.inp σ.run ∧ Routes σ.inp (fun _ => σ.dst) σ.run 15 (s * s * s) :=
  ⟨σ.run_isLocal, ⟨fun d t ht u v i k h => run_num_le hG d t ht u v i k h,
    fun d t ht u v i m h => run_valid hG d t ht u v i m h,
    fun d v m hm => holds_of_rcvd (r := 14) (by norm_num) (HE_of_inp hG d hm)⟩⟩

end Setup

end CongestedCliqueRouting
