import Papers.PODC2014.MultiMessageBroadcastMAC.Basic

/-!
# Lemmas 3.3, 3.5–3.10 and Corollary 3.8

The basic properties of the sets `R_i(t)` (messages got by `i` by time `t`) and `C_i(t)` (messages
acknowledged at `i` by time `t`) in an execution of BMMB with an abstract MAC layer, and the two
"progress" lemmas obtained from the progress bound.
-/

namespace Podc.MultiMessageBroadcastMAC

variable {V M : Type*}

lemma List.getElem_notMem_take_of_nodup {l : List M} (hl : l.Nodup) {a : ℕ} (ha : a < l.length) :
    l[a] ∉ l.take a := by
  intro h
  obtain ⟨b, hb, hb'⟩ := List.getElem_of_mem h
  rw [List.length_take] at hb
  rw [List.getElem_take] at hb'
  have := (List.Nodup.getElem_inj_iff hl).1 hb'
  omega

namespace Exec

variable [DecidableEq V] [DecidableEq M] {G G' : SimpleGraph V} (α : Exec G G' M)

open Config

/-! ### Elementary facts about `R` and `C` -/

lemma mem_R {i : V} {t : ℝ} {m : M} : m ∈ α.R i t ↔ m ∈ (α.at_ t).log i := List.mem_toFinset

lemma mem_C {i : V} {t : ℝ} {m : M} : m ∈ α.C i t ↔ (α.at_ t).Acked i m := List.mem_toFinset

lemma card_R (i : V) (t : ℝ) : (α.R i t).card = ((α.at_ t).log i).length :=
  List.toFinset_card_of_nodup ((α.inv _).nodup i)

omit [DecidableEq M] in
lemma acks_le_at (i : V) (t : ℝ) : (α.at_ t).acks i ≤ ((α.at_ t).log i).length :=
  (α.inv _).acks_le i

lemma card_C (i : V) (t : ℝ) : (α.C i t).card = (α.at_ t).acks i := by
  unfold C at_
  rw [List.toFinset_card_of_nodup (((α.inv _).nodup i).sublist (List.take_sublist _ _)),
    List.length_take, min_eq_left ((α.inv _).acks_le i)]

omit [DecidableEq M] in
lemma at_mono {t t' : ℝ} (h : t ≤ t') : StepMono (α.at_ t) (α.at_ t') :=
  α.mono (α.last_monotone h)

/-- **Lemma 3.5**, part 1: `R_i` and `C_i` grow with time. -/
theorem lemma_3_5_1 (i : V) {t t' : ℝ} (h : t ≤ t') : α.R i t ⊆ α.R i t' ∧ α.C i t ⊆ α.C i t' :=
  ⟨fun _ hm => α.mem_R.2 (((α.at_mono h).log_prefix i).subset (α.mem_R.1 hm)),
    fun _ hm => α.mem_C.2 (α.acked_mono (α.last_monotone h) (α.mem_C.1 hm))⟩

lemma C_subset_R (i : V) (t : ℝ) : α.C i t ⊆ α.R i t :=
  fun _ hm => α.mem_R.2 (List.take_subset _ _ (α.mem_C.1 hm))

/-- **Lemma 3.5**, part 2: `C_i(t) ⊆ R_i(t')` for `t ≤ t'`. -/
theorem lemma_3_5_2 (i : V) {t t' : ℝ} (h : t ≤ t') : α.C i t ⊆ α.R i t' :=
  (α.C_subset_R i t).trans (α.lemma_3_5_1 i h).1

/-- **Lemma 3.5**, part 3: if `i` and `i'` are neighbours in `G`, then `C_{i'}(t) ⊆ R_i(t')` for
`t ≤ t'`. -/
theorem lemma_3_5_3 {i i' : V} (hadj : G.Adj i i') {t t' : ℝ} (h : t ≤ t') :
    α.C i' t ⊆ α.R i t' := by
  refine Finset.Subset.trans (fun m hm => α.mem_R.2 ?_) (α.lemma_3_5_1 i h).1
  exact (α.inv _).acked_nbr i' i hadj.symm m (α.mem_C.1 hm)

/-- **Lemma 3.6**: in the final state at time `t`, `bcastq_i` contains exactly the messages of
`R_i(t) − C_i(t)` (and it is duplicate-free). -/
theorem lemma_3_6 (i : V) (t : ℝ) :
    ((α.at_ t).queue i).toFinset = α.R i t \ α.C i t ∧ ((α.at_ t).queue i).Nodup := by
  refine ⟨?_, ((α.inv _).nodup i).sublist (List.drop_sublist _ _)⟩
  ext m
  simp only [List.mem_toFinset, Finset.mem_sdiff, mem_R, mem_C, queue, Acked]
  exact List.mem_drop_iff_of_nodup ((α.inv _).nodup i) _ _

lemma busy_iff (i : V) (t : ℝ) : (α.at_ t).Busy i ↔ (α.C i t).card < (α.R i t).card := by
  rw [card_C, card_R]; rfl

lemma busy_of_not_subset {i : V} {t : ℝ} (h : ¬ α.R i t ⊆ α.C i t) : (α.at_ t).Busy i := by
  rw [busy_iff]
  by_contra h'
  exact h (Finset.eq_of_subset_of_card_le (α.C_subset_R i t) (not_lt.1 h')).symm.subset

/-! ### The acknowledgment bound -/

omit [DecidableEq M] in
/-- Every pending broadcast started at some configuration. -/
lemma exists_fresh {i : V} {n : ℕ} (h : (α.cfg n).Busy i) :
    ∃ s ≤ n, α.Fresh i s ∧ (α.cfg s).acks i = (α.cfg n).acks i := by
  induction n with
  | zero => exact ⟨0, le_rfl, ⟨h, fun n' h' => by omega⟩, rfl⟩
  | succ n ih =>
    by_cases hp : (α.cfg n).Busy i ∧ (α.cfg n).acks i = (α.cfg (n + 1)).acks i
    · obtain ⟨s, hs, hf, he⟩ := ih hp.1
      exact ⟨s, by omega, hf, he.trans hp.2⟩
    · refine ⟨n + 1, le_rfl, ⟨h, fun n' h' => ?_⟩, rfl⟩
      obtain rfl : n = n' := by omega
      exact hp

variable {α}

omit [DecidableEq M] in
/-- A broadcast pending at time `t` is acknowledged by time `t + F_ack`. -/
lemma ack_progress {Fack : ℝ} (hA : α.AckBound Fack) {i : V} {t : ℝ} (ht : 0 ≤ t)
    (h : (α.at_ t).Busy i) : (α.at_ t).acks i < (α.at_ (t + Fack)).acks i := by
  obtain ⟨s, hs, hf, he⟩ := α.exists_fresh h
  obtain ⟨n', hn', hlt⟩ := hA i s hf
  have : n' ≤ α.last (t + Fack) :=
    α.le_last (hn'.trans (by linarith [α.T_mono hs, α.T_last_le ht]))
  rw [at_, ← he]
  exact hlt.trans_le ((α.mono this).acks_le i)

omit [DecidableEq M] in
/-- The counting core of Lemma 3.7: within `k F_ack` time, `k` more broadcasts are acknowledged,
as long as the queue at time `t` lasts. -/
lemma acks_add {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) {i : V} {t : ℝ} (ht : 0 ≤ t)
    (k : ℕ) :
    min ((α.at_ t).log i).length ((α.at_ t).acks i + k) ≤ (α.at_ (t + k * Fack)).acks i := by
  induction k with
  | zero => simp
  | succ k ih =>
    set s := t + k * Fack
    have hs : t + ((k + 1 : ℕ) : ℝ) * Fack = s + Fack := by push_cast; ring
    rw [hs]
    have hss : 0 ≤ s := by positivity
    have hmono := (α.at_mono (show s ≤ s + Fack by linarith)).acks_le i
    by_cases hb : (α.at_ s).Busy i
    · have := ack_progress hA hss hb
      omega
    · have hlen := ((α.at_mono (show t ≤ s from le_add_of_nonneg_right (by positivity))).log_prefix i).length_le
      unfold Busy at hb
      omega

/-- **Lemma 3.7**, part 1: a message in position `k ≥ 1` of `bcastq_i` at time `t` is
acknowledged by time `t + k F_ack`. -/
theorem lemma_3_7_1 {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) {i : V} {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} (hk : 1 ≤ k) {m' : M} (hm : ((α.at_ t).queue i)[k - 1]? = some m') :
    m' ∈ α.C i (t + k * Fack) := by
  have h := acks_add hA hF ht (i := i) k
  unfold queue at hm
  rw [List.getElem?_drop, List.getElem?_eq_some_iff] at hm
  obtain ⟨hlt, hm⟩ := hm
  rw [mem_C]
  have hpre := (α.at_mono (show t ≤ t + k * Fack from
    le_add_of_nonneg_right (by positivity))).log_prefix i
  unfold Acked
  rw [← hm, hpre.getElem hlt]
  have hlt2 : (α.at_ t).acks i + (k - 1) < (α.at_ (t + k * Fack)).acks i := by omega
  have hidx : (α.at_ t).acks i + (k - 1) <
      (((α.at_ (t + k * Fack)).log i).take ((α.at_ (t + k * Fack)).acks i)).length := by
    rw [List.length_take]; have := α.acks_le_at i (t + k * Fack); omega
  have := List.getElem_mem hidx
  rwa [List.getElem_take] at this

/-- **Lemma 3.7**, part 2: if `bcastq_i` has length at least `k` at time `t`, then
`|C_i(t + k F_ack)| ≥ |C_i(t)| + k`. -/
theorem lemma_3_7_2 {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) {i : V} {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ ((α.at_ t).queue i).length) :
    (α.C i t).card + k ≤ (α.C i (t + k * Fack)).card := by
  have h := acks_add hA hF ht (i := i) k
  have := α.acks_le_at i t
  rw [card_C, card_C]
  unfold queue at hk
  rw [List.length_drop] at hk
  omega

/-- **Lemma 3.7**, part 3: if `|R_i(t)| ≥ k`, then `|C_i(t + k F_ack)| ≥ k`. -/
theorem lemma_3_7_3 {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) {i : V} {t : ℝ}
    (ht : 0 ≤ t) {k : ℕ} (hk : k ≤ (α.R i t).card) : k ≤ (α.C i (t + k * Fack)).card := by
  have h := acks_add hA hF ht (i := i) k
  rw [card_C]
  rw [card_R] at hk
  omega

/-- **Corollary 3.8**: if `|C_i(t)| ≥ ℓ - 1` and `|R_i(t)| ≥ ℓ` (`ℓ > 0`), then
`|C_i(t + F_ack)| ≥ ℓ`. -/
theorem corollary_3_8 {Fack : ℝ} (hA : α.AckBound Fack) (hF : 0 ≤ Fack) {i : V} {t : ℝ} (ht : 0 ≤ t) {ℓ : ℕ}
    (hℓ : 0 < ℓ) (hC : ℓ - 1 ≤ (α.C i t).card) (hR : ℓ ≤ (α.R i t).card) :
    ℓ ≤ (α.C i (t + Fack)).card := by
  by_cases hb : (α.at_ t).Busy i
  · have := ack_progress hA ht hb
    rw [card_C] at hC ⊢
    omega
  · rw [busy_iff] at hb
    have := Finset.card_le_card (α.lemma_3_5_1 i (show t ≤ t + Fack by linarith)).2
    omega

/-! ### The progress bound -/

omit [DecidableEq M] in
/-- **Lemma 3.3**: `connect(α', j) ⊆ contend(α', j)`. -/
theorem lemma_3_3 (hG : G ≤ G') {a b : ℕ} (hab : a ≤ b) (j : V) :
    α.connect a b j ⊆ α.contend a j :=
  fun _ hp => ⟨hG hp.1, fun h => hp.2.2 (α.acked_mono hab h)⟩

/-- **Lemma 3.10**: if every message `i` got by time `t` has been acknowledged by every
`G'`-neighbour of `i`, and a `G`-neighbour `j` of `i` got a message that `i` did not get, then `i`
gets a new message within `F_prog` time. -/
theorem lemma_3_10 (hG : G ≤ G') {Fprog : ℝ} (hP : α.ProgBound Fprog) (hFp : 0 ≤ Fprog)
    {i j : V} (hij : G.Adj i j) {t : ℝ} (ht : 0 ≤ t)
    (h1 : ∀ i', G'.Adj i' i → α.R i t ⊆ α.C i' t) (h2 : (α.R j t \ α.R i t).Nonempty) :
    (α.R i t).card < (α.R i (t + Fprog)).card := by
  by_contra hlt
  have hsub := (α.lemma_3_5_1 i (show t ≤ t + Fprog by linarith)).1
  have heq : α.R i (t + Fprog) = α.R i t :=
    (Finset.eq_of_subset_of_card_le hsub (not_lt.1 hlt)).symm
  obtain ⟨t', ht', hlast⟩ := α.exists_gt_last_eq (t := t + Fprog) (by linarith)
  have hR' : ∀ m, m ∈ (α.cfg (α.last t')).log i → m ∈ α.R i t := by
    intro m hm
    rw [← heq, mem_R, at_, ← hlast]; exact hm
  -- `j` is broadcasting some message `m'` that `i` does not have
  have hjb : (α.at_ t).Busy j := by
    refine α.busy_of_not_subset fun hs => ?_
    obtain ⟨x, hx⟩ := h2
    rw [Finset.mem_sdiff] at hx
    exact hx.2 (α.lemma_3_5_3 hij le_rfl (hs hx.1))
  set m' := ((α.at_ t).log j)[(α.at_ t).acks j]'hjb
  have hm'C : m' ∉ α.C j t := by
    rw [mem_C]
    exact List.getElem_notMem_take_of_nodup ((α.inv _).nodup j) hjb
  have hconn : (j, m') ∈ α.connect (α.last t) (α.last t') i := by
    refine ⟨hij.symm, ?_, fun hack => ?_⟩
    · show m' ∈ _
      have hidx : (α.at_ t).acks j < (((α.at_ t).log j).take ((α.at_ t).acks j + 1)).length := by
        have := hjb; unfold Busy at this; rw [List.length_take]; omega
      have := List.getElem_mem hidx
      rwa [List.getElem_take] at this
    · have := hR' _ ((α.inv _).acked_nbr j i hij.symm m' hack)
      exact hm'C (h1 j (hG hij.symm) this)
  obtain ⟨⟨i', m''⟩, hc, hh⟩ := hP t t' i ht (by linarith) ⟨_, hconn⟩
  have := hR' _ ((α.inv _).heard_log _ _ _ hh)
  exact hc.2 (α.mem_C.1 (h1 i' hc.1 this))

/-- **Lemma 3.9**: if `i` and `j` are neighbours in `G` and `R_j(t) ≠ ∅`, then
`R_i(t + F_prog) ≠ ∅`. -/
theorem lemma_3_9 (hG : G ≤ G') {Fprog : ℝ} (hP : α.ProgBound Fprog) (hFp : 0 ≤ Fprog)
    {i j : V} (hij : G.Adj i j) {t : ℝ} (ht : 0 ≤ t) (hj : (α.R j t).Nonempty) :
    (α.R i (t + Fprog)).Nonempty := by
  by_cases hi : (α.R i t).Nonempty
  · exact hi.mono (α.lemma_3_5_1 i (by linarith)).1
  · rw [Finset.not_nonempty_iff_eq_empty] at hi
    have := lemma_3_10 hG hP hFp hij ht (by simp [hi]) (by simpa [hi] using hj)
    rw [hi, Finset.card_empty] at this
    exact Finset.card_pos.1 this

/-! ### Where messages come from -/

omit [DecidableEq M] in
variable (α) in
/-- Every message in a log arrived somewhere, at an earlier event. -/
lemma arrives_before_of_mem_log {n : ℕ} {i : V} {m : M} (h : m ∈ (α.cfg n).log i) :
    ∃ n' < n, ∃ j, α.ev n' = .arrive j m := by
  induction n generalizing i m with
  | zero => simp at h
  | succ n ih =>
    have ih' : ∀ {i m}, m ∈ (α.cfg n).log i → ∃ n' < n + 1, ∃ j, α.ev n' = .arrive j m :=
      fun h => let ⟨n', hn', hj⟩ := ih h; ⟨n', by omega, hj⟩
    rw [cfg_succ] at h
    rcases hev : α.ev n with ⟨j, m'⟩ | ⟨u, v⟩ | u | _
    all_goals rw [hev] at h; simp only [step] at h
    · split_ifs at h with h1
      · exact ih' h
      · by_cases hij : i = j
        · subst hij
          simp only [Function.update_self, List.mem_append, List.mem_singleton] at h
          rcases h with h | rfl
          · exact ih' h
          · exact ⟨n, by omega, i, hev⟩
        · simp only [ne_eq, hij, not_false_eq_true, Function.update_of_ne] at h; exact ih' h
    · split at h
      next m' hh =>
        split_ifs at h with h1 h2
        · exact ih' h
        · by_cases hiv : i = v
          · subst hiv
            simp only [Function.update_self, List.mem_append, List.mem_singleton] at h
            rcases h with h | rfl
            · exact ih' h
            · obtain ⟨hlt, he⟩ := Config.head_eq_some hh
              exact ih' (he ▸ List.getElem_mem hlt)
          · simp only [ne_eq, hiv, not_false_eq_true, Function.update_of_ne] at h; exact ih' h
        · exact ih' h
      · exact ih' h
    · split at h
      · split_ifs at h <;> exact ih' h
      · exact ih' h
    · exact ih' h

omit [DecidableEq M] in
variable (α) in
/-- Every message in a log arrived somewhere. -/
lemma arrives_of_mem_log {n : ℕ} {i : V} {m : M} (h : m ∈ (α.cfg n).log i) :
    ∃ j, α.Arrives j m :=
  let ⟨n', _, j, hj⟩ := α.arrives_before_of_mem_log h
  ⟨j, n', hj⟩

variable (α) in
lemma R_subset {K : Finset M} (hK : ∀ i m, α.Arrives i m → m ∈ K) (i : V) (t : ℝ) :
    α.R i t ⊆ K := fun m hm =>
  let ⟨j, hj⟩ := α.arrives_of_mem_log (α.mem_R.1 hm)
  hK j m hj

omit [DecidableEq M] in
variable (α) in
/-- After `arrive(m)_u`, node `u` has `m`. -/
lemma mem_log_arrive {n : ℕ} {u : V} {m : M} (hn : α.ev n = .arrive u m) :
    m ∈ (α.cfg (n + 1)).log u := by
  rw [cfg_succ, hn]
  simp only [step]
  split_ifs with h
  · exact h
  · simp

variable (α) in
/-- With all arrivals at time `0`, a message that arrives at `u` is in `R_u(0)`. -/
lemma mem_R_zero (h0 : α.ArrivalsAtZero) {u : V} {m : M} (hm : α.Arrives u m) : m ∈ α.R u 0 := by
  obtain ⟨n, hn⟩ := hm
  have hle : n + 1 ≤ α.last 0 := α.le_last (le_of_eq (h0 n u m hn))
  rw [mem_R]
  exact ((α.mono hle).log_prefix u).subset (α.mem_log_arrive hn)

end Exec

end Podc.MultiMessageBroadcastMAC
