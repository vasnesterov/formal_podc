import Papers.PODC2014.MultiMessageBroadcastMAC.Model

/-!
# Invariants of BMMB and the basic lemmas of §3.2.3

* `Inv`: invariants of every reachable configuration (logs are duplicate-free, a message
  acknowledged by `u` is in the log of every `G`-neighbour of `u`, …).
* Monotonicity along executions; Lemmas 3.5 and 3.6 on the sets `R_i(t)`, `C_i(t)`.
-/

namespace Podc.MultiMessageBroadcastMAC

variable {V M : Type*}

/-- Taking a prefix of length at most `l.length` does not see what is appended later. -/
lemma List.take_of_prefix {l l' : List M} (h : l <+: l') {a : ℕ} (ha : a ≤ l.length) :
    l'.take a = l.take a := by
  obtain ⟨x, rfl⟩ := h
  exact List.take_append_of_le_length ha

/-- In a duplicate-free list, the elements after position `k` are those not before it. -/
lemma List.mem_drop_iff_of_nodup {l : List M} (hl : l.Nodup) (k : ℕ) (x : M) :
    x ∈ l.drop k ↔ x ∈ l ∧ x ∉ l.take k := by
  have h := List.take_append_drop k l
  rw [← h] at hl
  have hd := (List.nodup_append.1 hl).2.2
  constructor
  · intro hx
    refine ⟨List.mem_of_mem_drop hx, fun hx' => hd _ hx' _ hx rfl⟩
  · rintro ⟨hx, hx'⟩
    rw [← h] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact absurd hx hx'
    · exact hx

namespace Config

/-- Invariants of reachable configurations. -/
structure Inv (G : SimpleGraph V) (c : Config V M) : Prop where
  nodup : ∀ i, (c.log i).Nodup
  acks_le : ∀ i, c.acks i ≤ (c.log i).length
  heard_log : ∀ v u m, (u, m) ∈ c.heard v → m ∈ c.log v
  acked_nbr : ∀ u v, G.Adj u v → ∀ m, c.Acked u m → m ∈ c.log v

@[simp] lemma init_log (i : V) : (init : Config V M).log i = [] := rfl
@[simp] lemma init_acks (i : V) : (init : Config V M).acks i = 0 := rfl
@[simp] lemma init_heard (i : V) : (init : Config V M).heard i = ∅ := rfl

lemma Inv.init (G : SimpleGraph V) : Inv G (init : Config V M) :=
  ⟨fun _ => by simp, fun _ => by simp, fun _ _ _ h => by simp at h,
    fun _ _ _ _ h => by simp [Acked] at h⟩

lemma head_eq_some {c : Config V M} {i : V} {m : M} (h : c.head i = some m) :
    ∃ hi : c.acks i < (c.log i).length, (c.log i)[c.acks i] = m := by
  unfold head at h
  rw [List.getElem?_eq_some_iff] at h
  exact h

lemma head_eq_none {c : Config V M} {i : V} (h : c.head i = none) :
    (c.log i).length ≤ c.acks i := by
  unfold head at h
  rwa [List.getElem?_eq_none_iff] at h

end Config

section StepLemmas

variable [DecidableEq V] (G G' : SimpleGraph V)

open Config

/-- What every step preserves monotonically. -/
structure StepMono (c c' : Config V M) : Prop where
  log_prefix : ∀ i, c.log i <+: c'.log i
  acks_le : ∀ i, c.acks i ≤ c'.acks i
  heard_sub : ∀ i, c.heard i ⊆ c'.heard i

omit [DecidableEq V] in
lemma StepMono.refl (c : Config V M) : StepMono c c :=
  ⟨fun _ => List.prefix_refl _, fun _ => le_rfl, fun _ => subset_rfl⟩

omit [DecidableEq V] in
lemma StepMono.trans {c c' c'' : Config V M} (h : StepMono c c') (h' : StepMono c' c'') :
    StepMono c c'' :=
  ⟨fun i => (h.log_prefix i).trans (h'.log_prefix i), fun i => (h.acks_le i).trans (h'.acks_le i),
    fun i => (h.heard_sub i).trans (h'.heard_sub i)⟩

lemma stepMono_update_log {c : Config V M} {i : V} {m : M} :
    ∀ j, c.log j <+: Function.update c.log i (c.log i ++ [m]) j := by
  intro j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Function.update_of_ne hj]

lemma stepMono_step (c : Config V M) (e : Event V M) : StepMono c (step G G' c e) := by
  classical
  cases e with
  | arrive i m =>
    simp only [step]
    split_ifs
    · exact StepMono.refl c
    · exact ⟨stepMono_update_log, fun _ => le_rfl, fun _ => subset_rfl⟩
  | rcv u v =>
    have hh : ∀ (m : M) j, c.heard j ⊆ Function.update c.heard v (insert (u, m) (c.heard v)) j := by
      intro m j
      by_cases hj : j = v
      · subst hj; simp only [Function.update_self]; exact Set.subset_insert _ _
      · simp [Function.update_of_ne hj]
    simp only [step]
    split
    · split_ifs
      · exact ⟨fun j => List.prefix_refl _, fun _ => le_rfl, hh _⟩
      · exact ⟨stepMono_update_log, fun _ => le_rfl, hh _⟩
      · exact StepMono.refl c
    · exact StepMono.refl c
  | ack u =>
    simp only [step]
    split
    · split_ifs
      · refine ⟨fun _ => List.prefix_refl _, fun j => ?_, fun _ => subset_rfl⟩
        by_cases hj : j = u
        · subst hj; simp
        · simp [Function.update_of_ne hj]
      · exact StepMono.refl c
    · exact StepMono.refl c
  | skip => exact StepMono.refl c

omit [DecidableEq V] in
/-- `Acked` only looks at the prefix of length `acks`. -/
lemma acked_of_prefix {c c' : Config V M} {u : V} (hl : c.log u <+: c'.log u)
    (ha : c.acks u = c'.acks u) (hle : c.acks u ≤ (c.log u).length) (m : M) :
    c'.Acked u m ↔ c.Acked u m := by
  unfold Acked
  rw [← ha, List.take_of_prefix hl hle]

lemma Config.Inv.next {c : Config V M} (hc : Inv G c) (e : Event V M) : Inv G (step G G' c e) := by
  classical
  have hm := stepMono_step G G' c e
  cases e with
  | arrive i m =>
    simp only [step]
    split_ifs with h
    · exact hc
    · refine ⟨fun j => ?_, fun j => ?_, fun v u m' hm' => ?_, fun u v huv m' hm' => ?_⟩
      · by_cases hj : j = i
        · subst hj; simp only [Function.update_self]
          exact List.nodup_append.2 ⟨hc.nodup j, List.nodup_singleton m, fun a ha b hb => by simp at hb; subst hb; exact fun e => h (e ▸ ha)⟩
        · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]; exact hc.nodup j
      · exact (hc.acks_le j).trans (stepMono_update_log j).length_le
      · exact (stepMono_update_log v).subset (hc.heard_log v u m' hm')
      · simp only [Acked] at hm'
        rw [List.take_of_prefix (stepMono_update_log u) (hc.acks_le u)] at hm'
        exact (stepMono_update_log v).subset (hc.acked_nbr u v huv m' hm')
  | rcv u v =>
    simp only [step]
    split
    next m hh =>
      split_ifs with h1 h2
      · -- `v` already has `m`
        refine ⟨hc.nodup, hc.acks_le, fun w x m' hm' => ?_, hc.acked_nbr⟩
        by_cases hw : w = v
        · subst hw
          simp only [Function.update_self, Set.mem_insert_iff, Prod.mk.injEq] at hm'
          rcases hm' with ⟨-, rfl⟩ | hm'
          · exact h2
          · exact hc.heard_log _ _ _ hm'
        · simp only [ne_eq, hw, not_false_eq_true, Function.update_of_ne] at hm'
          exact hc.heard_log _ _ _ hm'
      · refine ⟨fun j => ?_, fun j => ?_, fun w x m' hm' => ?_, fun x w hxw m' hm' => ?_⟩
        · by_cases hj : j = v
          · subst hj; simp only [Function.update_self]
            exact List.nodup_append.2 ⟨hc.nodup j, List.nodup_singleton m, fun a ha b hb => by simp at hb; subst hb; exact fun e => h2 (e ▸ ha)⟩
          · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]; exact hc.nodup j
        · exact (hc.acks_le j).trans (stepMono_update_log j).length_le
        · by_cases hw : w = v
          · subst hw
            simp only [Function.update_self, Set.mem_insert_iff, Prod.mk.injEq] at hm' ⊢
            rcases hm' with ⟨-, rfl⟩ | hm'
            · simp
            · exact List.mem_append_left _ (hc.heard_log _ _ _ hm')
          · simp only [ne_eq, hw, not_false_eq_true, Function.update_of_ne] at hm' ⊢
            exact hc.heard_log _ _ _ hm'
        · simp only [Acked] at hm'
          rw [List.take_of_prefix (stepMono_update_log x) (hc.acks_le x)] at hm'
          exact (stepMono_update_log w).subset (hc.acked_nbr x w hxw m' hm')
      · exact hc
    · exact hc
  | ack u =>
    simp only [step]
    split
    next m hh =>
      split_ifs with h1
      · obtain ⟨hlt, hmu⟩ := head_eq_some hh
        refine ⟨hc.nodup, fun j => ?_, hc.heard_log, fun x w hxw m' hm' => ?_⟩
        · by_cases hj : j = u
          · subst hj; simpa using hlt
          · simp only [ne_eq, hj, not_false_eq_true, Function.update_of_ne]; exact hc.acks_le j
        · by_cases hx : x = u
          · subst hx
            simp only [Acked, Function.update_self] at hm'
            rw [List.take_add_one, List.getElem?_eq_getElem hlt] at hm'
            rcases List.mem_append.1 hm' with hm' | hm'
            · exact hc.acked_nbr x w hxw m' hm'
            · simp only [Option.toList_some, List.mem_singleton] at hm'
              subst hm'; rw [hmu]; exact hc.heard_log _ _ _ (h1 w hxw)
          · exact hc.acked_nbr x w hxw m' (by simpa [Acked, Function.update_of_ne hx] using hm')
      · exact hc
    · exact hc
  | skip => exact hc

end StepLemmas

namespace Exec

variable [DecidableEq V] {G G' : SimpleGraph V} (α : Exec G G' M)

open Config

lemma inv (n : ℕ) : Inv G (α.cfg n) := by
  induction n with
  | zero => exact Inv.init G
  | succ n ih => exact ih.next G G' _

lemma mono {n n' : ℕ} (h : n ≤ n') : StepMono (α.cfg n) (α.cfg n') := by
  induction h with
  | refl => exact StepMono.refl _
  | step _ ih => exact ih.trans (stepMono_step G G' _ _)

lemma acked_mono {n n' : ℕ} (h : n ≤ n') {u : V} {m : M} (hm : (α.cfg n).Acked u m) :
    (α.cfg n').Acked u m := by
  have hp := (α.mono h).log_prefix u
  have hle := (α.mono h).acks_le u
  unfold Acked at *
  rw [← List.take_of_prefix hp ((α.inv n).acks_le u)] at hm
  exact List.take_subset_take_left _ hle hm

lemma started_mono {n n' : ℕ} (h : n ≤ n') {u : V} {m : M} (hm : (α.cfg n).Started u m) :
    (α.cfg n').Started u m := by
  have hp := (α.mono h).log_prefix u
  have hle := (α.mono h).acks_le u
  unfold Started at *
  exact List.take_subset_take_left _ (by omega) ((hp.take _).subset hm)

end Exec

end Podc.MultiMessageBroadcastMAC
