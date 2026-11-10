import Papers.PODC2012.OrderPreservingByzRenaming.Spec

/-!
# The 2-round echo-counting algorithm (Algorithm 8, §6.3)

Processes are `Fin n` on the complete network. A process receives its own messages through the
self-loop (link `n` in the paper); in CSLib's `LockStep` there is no self-loop, so a process adds its
own message to its inbox itself (`Function.update`).

* Round 1: broadcast `⟨ID, my id⟩`; `linkid[lnk]` is the id received on link `lnk`, `timely` the
  set of ids received.
* Round 2: broadcast `⟨MultiEcho, timely⟩`. An echo `ids` from link `lnk` is *valid* (`isValid`) iff
  `linkid[lnk] ≠ ⊥`, `|ids| ≤ n` and `|timely ∩ ids| ≥ n - t`. `counter[id]` = number of valid echoes
  containing `id`, `accepted` = union of the valid echoes.
* New name: `newid[my id] = ∑_{id ∈ accepted, id ≤ my id} min(counter[id], n - t)` (Lines 17–22).
-/

namespace Podc.OrderPreservingByzRenaming.TwoRound

open Cslib.Byzantine.LockStep

/-- Messages of Algorithm 8. -/
inductive Msg
  | ident (v : ℕ)
  | echo (s : Finset ℕ)

variable {n : ℕ}

/-- `linkid[lnk]`: the id received on link `j` in Round 1. -/
def linkid (ib : Fin n → Option Msg) (j : Fin n) : Option ℕ :=
  match ib j with
  | some (.ident v) => some v
  | _ => none

/-- `timely`: the set of ids received in Round 1. -/
def timely (ib : Fin n → Option Msg) : Finset ℕ :=
  Finset.univ.biUnion fun j => (linkid ib j).toFinset

/-- The `MultiEcho` set received on link `j` in Round 2. -/
def echoOf (ib : Fin n → Option Msg) (j : Fin n) : Option (Finset ℕ) :=
  match ib j with
  | some (.echo s) => some s
  | _ => none

/-- `isValid(lnk, ids)` of Algorithm 8. -/
def IsValid (t : ℕ) (ib1 : Fin n → Option Msg) (j : Fin n) (ids : Finset ℕ) : Prop :=
  (linkid ib1 j).isSome ∧ ids.card ≤ n ∧ n - t ≤ (timely ib1 ∩ ids).card

instance (t : ℕ) (ib1 : Fin n → Option Msg) (j : Fin n) (ids : Finset ℕ) :
    Decidable (IsValid t ib1 j ids) := by unfold IsValid; infer_instance

/-- The valid echo received on link `j` (`∅` if there is none). -/
def vEcho (t : ℕ) (ib1 ib2 : Fin n → Option Msg) (j : Fin n) : Finset ℕ :=
  match echoOf ib2 j with
  | some ids => if IsValid t ib1 j ids then ids else ∅
  | none => ∅

/-- `counter[z]`: the number of valid echoes containing `z`. -/
def counter (t : ℕ) (ib1 ib2 : Fin n → Option Msg) (z : ℕ) : ℕ :=
  (Finset.univ.filter fun j => z ∈ vEcho t ib1 ib2 j).card

/-- `accepted`: the ids contained in valid echoes. -/
def accepted (t : ℕ) (ib1 ib2 : Fin n → Option Msg) : Finset ℕ :=
  Finset.univ.biUnion (vEcho t ib1 ib2)

/-- `newid[v]` (Lines 17–21): the accumulated offsets `min(counter, n - t)` of the accepted ids
`≤ v`. -/
def newid (t : ℕ) (ib1 ib2 : Fin n → Option Msg) (v : ℕ) : ℕ :=
  ∑ z ∈ (accepted t ib1 ib2).filter (· ≤ v), min (counter t ib1 ib2 z) (n - t)

/-- **Algorithm 8** as a `LockStep` protocol (parameter `t`: the assumed bound on faults). -/
def alg (n t : ℕ) : Protocol (Fin n) ℕ Msg ℕ where
  send p x h _ := match h with
    | [] => some (.ident x)
    | [ib1] => some (.echo (timely (Function.update ib1 p (some (.ident x)))))
    | _ => none
  decide p x h := match h with
    | [ib1, ib2] =>
      let ib1' := Function.update ib1 p (some (.ident x))
      let ib2' := Function.update ib2 p (some (.echo (timely ib1')))
      some (newid t ib1' ib2' x)
    | _ => none

/-- Algorithm 8 decides only after exactly two rounds. -/
lemma decide_eq_none (t : ℕ) (p : Fin n) (x : ℕ) (h : History (Fin n) Msg) (hl : h.length ≠ 2) :
    (alg n t).decide p x h = none := by
  match h with
  | [] => rfl
  | [_] => rfl
  | [_, _] => simp at hl
  | _ :: _ :: _ :: _ => rfl

/-! ### The inboxes of a run -/

section Run

variable (s : Scenario (Fin n) ℕ Msg)

open Classical in
/-- The Round-1 inbox of `p` (with its own message on its own link). -/
noncomputable def inb1 (p : Fin n) : Fin n → Option Msg := fun j =>
  if j = p then some (.ident (s.input p))
  else if j ∈ s.byz then s.adv 0 j p else some (.ident (s.input j))

open Classical in
/-- The Round-2 inbox of `p` (with its own message on its own link). -/
noncomputable def inb2 (p : Fin n) : Fin n → Option Msg := fun j =>
  if j = p then some (.echo (timely (inb1 s p)))
  else if j ∈ s.byz then s.adv 1 j p else some (.echo (timely (inb1 s j)))

variable {s} (t : ℕ)

@[simp] lemma alg_send_nil (p : Fin n) (x : ℕ) (q : Fin n) :
    (alg n t).send p x [] q = some (.ident x) := rfl

@[simp] lemma alg_send_one (p : Fin n) (x : ℕ) (ib : Inbox (Fin n) Msg) (q : Fin n) :
    (alg n t).send p x [ib] q = some (.echo (timely (Function.update ib p (some (.ident x))))) := rfl

lemma alg_decide_two (p : Fin n) (x : ℕ) (ib1 ib2 : Inbox (Fin n) Msg) :
    (alg n t).decide p x [ib1, ib2] =
      some (newid t (Function.update ib1 p (some (.ident x)))
        (Function.update ib2 p (some (.echo (timely (Function.update ib1 p (some (.ident x))))))) x) :=
  rfl

/-- The raw inbox of `q` in round `r` (index `r`, counting from `0`). -/
noncomputable def raw (r : ℕ) (q : Fin n) : Inbox (Fin n) Msg :=
  fun p => deliver ⊤ (alg n t) s (hist ⊤ (alg n t) s r) r p q

lemma hist_one' (q : Fin n) : hist ⊤ (alg n t) s 1 q = [raw (s := s) t 0 q] := rfl

lemma hist_two' (q : Fin n) : hist ⊤ (alg n t) s 2 q = [raw (s := s) t 0 q, raw (s := s) t 1 q] := rfl

lemma raw_zero (hs : s.Reliable) (p : Fin n) :
    Function.update (raw (s := s) t 0 p) p (some (.ident (s.input p))) = inb1 s p := by
  funext j
  by_cases hj : j = p
  · subst hj; simp [inb1]
  · rw [Function.update_of_ne hj]
    have hadj : (⊤ : SimpleGraph (Fin n)).Adj j p := by simpa using hj
    by_cases hb : j ∈ s.byz
    · simp [raw, deliver, inb1, hj, hadj, hb]
    · simp [raw, deliver, inb1, hj, hadj, hb, hs 0 j p]

lemma raw_one (hs : s.Reliable) (p : Fin n) :
    Function.update (raw (s := s) t 1 p) p (some (.echo (timely (inb1 s p)))) = inb2 s p := by
  funext j
  by_cases hj : j = p
  · subst hj; simp [inb2]
  · rw [Function.update_of_ne hj]
    have hadj : (⊤ : SimpleGraph (Fin n)).Adj j p := by simpa using hj
    by_cases hb : j ∈ s.byz
    · simp [raw, deliver, inb2, hj, hadj, hb]
    · have := raw_zero t hs j
      simp only [raw, deliver, inb2, hj, hadj, hb, hs 1 j p, ite_true, ite_false, hist_one',
        alg_send_one]
      rw [← this]

/-- An honest process decides exactly `newid[my id]`, computed from its two inboxes. -/
theorem decides_iff (hs : s.Reliable) (p : Fin n) (o : ℕ) :
    Decides ⊤ (alg n t) s p o ↔ o = newid t (inb1 s p) (inb2 s p) (s.input p) := by
  rw [decides_iff_firstSome, firstSome_iff_of_ne 2]
  · simp only [status]
    rw [hist_two', alg_decide_two, raw_zero t hs, raw_one t hs]
    simp [eq_comm]
  · intro r hr
    simp only [status]
    exact decide_eq_none t p _ _ (by simpa using hr)

end Run

/-! ### Generic counting facts -/

section Counting

variable (t : ℕ) (ib1 ib2 : Fin n → Option Msg)

lemma card_timely_le : (timely ib1).card ≤ n := by
  unfold timely
  calc _ ≤ ∑ j : Fin n, ((linkid ib1 j).toFinset).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum fun j _ => by
        cases linkid ib1 j <;> simp
    _ = n := by simp

lemma card_vEcho_le (j : Fin n) : (vEcho t ib1 ib2 j).card ≤ n := by
  unfold vEcho
  split
  · split_ifs with h
    · exact h.2.1
    · simp
  · simp

lemma vEcho_eq_of_valid {j : Fin n} {ids : Finset ℕ} (hj : ib2 j = some (.echo ids))
    (hv : IsValid t ib1 j ids) : vEcho t ib1 ib2 j = ids := by
  simp [vEcho, echoOf, hj, hv]

lemma mem_accepted_of_counter_pos {z : ℕ} (h : 0 < counter t ib1 ib2 z) :
    z ∈ accepted t ib1 ib2 := by
  obtain ⟨j, hj⟩ := Finset.card_pos.1 h
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [accepted, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, hj⟩

/-- `newid` as a sum over all ids `≤ v` (ids that are not accepted have counter `0`). -/
lemma newid_eq_sum_range (v : ℕ) :
    newid t ib1 ib2 v = ∑ z ∈ Finset.range (v + 1), min (counter t ib1 ib2 z) (n - t) := by
  unfold newid
  apply Finset.sum_subset
  · intro z hz
    simp only [Finset.mem_filter] at hz
    simp only [Finset.mem_range]; omega
  · intro z _ hz
    by_cases h : z ∈ accepted t ib1 ib2
    · simp only [Finset.mem_filter, not_and] at hz
      have : z ≤ v := by simp only [Finset.mem_range] at *; omega
      exact absurd this (hz h)
    · have : counter t ib1 ib2 z = 0 := by
        by_contra h0; exact h (mem_accepted_of_counter_pos t ib1 ib2 (Nat.pos_of_ne_zero h0))
      simp [this]

/-- The sum of all counters is the total size of the valid echoes. -/
lemma sum_counter_eq :
    ∑ z ∈ accepted t ib1 ib2, counter t ib1 ib2 z = ∑ j, (vEcho t ib1 ib2 j).card := by
  unfold counter
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.card_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter, accepted, Finset.mem_biUnion, Finset.mem_univ, true_and,
    and_iff_right_iff_imp]
  exact fun h => ⟨j, h⟩

/-- Validity of names: `newid ≤ n²`. -/
lemma newid_le (v : ℕ) : newid t ib1 ib2 v ≤ n ^ 2 := by
  calc newid t ib1 ib2 v
      ≤ ∑ z ∈ (accepted t ib1 ib2).filter (· ≤ v), counter t ib1 ib2 z :=
        Finset.sum_le_sum fun _ _ => min_le_left _ _
    _ ≤ ∑ z ∈ accepted t ib1 ib2, counter t ib1 ib2 z :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = ∑ j, (vEcho t ib1 ib2 j).card := sum_counter_eq t ib1 ib2
    _ ≤ ∑ _j : Fin n, n := Finset.sum_le_sum fun j _ => card_vEcho_le t ib1 ib2 j
    _ = n ^ 2 := by simp [sq]

/-- If `v`'s counter is at least `n - t`, `newid` grows by exactly `n - t` at `v`. -/
lemma newid_add_le {a b : ℕ} (hab : a < b) (hb : n - t ≤ counter t ib1 ib2 b) :
    newid t ib1 ib2 a + (n - t) ≤ newid t ib1 ib2 b := by
  rw [newid_eq_sum_range, newid_eq_sum_range]
  have hsub : insert b (Finset.range (a + 1)) ⊆ Finset.range (b + 1) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_range] at hz ⊢
    omega
  have hnot : b ∉ Finset.range (a + 1) := by simp; omega
  calc _ = ∑ z ∈ insert b (Finset.range (a + 1)), min (counter t ib1 ib2 z) (n - t) := by
        rw [Finset.sum_insert hnot, min_eq_right hb, add_comm]
    _ ≤ _ := Finset.sum_le_sum_of_subset hsub

end Counting

/-! ### Correctness (Lemmas 43, 44, Theorem 45) -/

section Correct

variable {s : Scenario (Fin n) ℕ Msg} (t : ℕ)

open Classical in
/-- The Byzantine processes, as a finset. -/
noncomputable def byzF (s : Scenario (Fin n) ℕ Msg) : Finset (Fin n) :=
  Finset.univ.filter (· ∈ s.byz)

/-- The correct ids. -/
noncomputable def corrIds (s : Scenario (Fin n) ℕ Msg) : Finset ℕ :=
  s.honestFinset.image s.input

lemma inb1_honest (p : Fin n) {j : Fin n} (hj : j ∉ s.byz) :
    inb1 s p j = some (.ident (s.input j)) := by
  by_cases h : j = p
  · subst h; simp [inb1]
  · simp [inb1, h, hj]

lemma inb2_honest (p : Fin n) {j : Fin n} (hj : j ∉ s.byz) :
    inb2 s p j = some (.echo (timely (inb1 s j))) := by
  by_cases h : j = p
  · subst h; simp [inb2]
  · simp [inb2, h, hj]

lemma corrIds_subset_timely (p : Fin n) : corrIds s ⊆ timely (inb1 s p) := by
  intro z hz
  simp only [corrIds, Finset.mem_image, Scenario.mem_honestFinset] at hz
  obtain ⟨j, hj, rfl⟩ := hz
  simp only [timely, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact ⟨j, by simp [linkid, inb1_honest p hj]⟩

lemma card_timely_sdiff_le (p : Fin n) :
    (timely (inb1 s p) \ corrIds s).card ≤ (byzF s).card := by
  have : timely (inb1 s p) \ corrIds s ⊆ (byzF s).biUnion fun j => (linkid (inb1 s p) j).toFinset := by
    intro z hz
    simp only [Finset.mem_sdiff, timely, Finset.mem_biUnion, Finset.mem_univ, true_and] at hz
    obtain ⟨⟨j, hj⟩, hz⟩ := hz
    simp only [Finset.mem_biUnion]
    refine ⟨j, ?_, hj⟩
    by_contra hb
    simp only [byzF, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [linkid, inb1_honest p hb, Option.mem_toFinset, Option.mem_def,
      Option.some.injEq] at hj
    subst hj
    exact hz (Finset.mem_image.2 ⟨j, by simpa using hb, rfl⟩)
  refine (Finset.card_le_card this).trans (Finset.card_biUnion_le.trans ?_)
  calc _ ≤ ∑ _j ∈ byzF s, 1 := Finset.sum_le_sum fun j _ => by
        cases linkid (inb1 s p) j <;> simp
    _ = _ := by simp

lemma card_corrIds (hinj : Set.InjOn s.input s.honest) :
    (corrIds s).card = n - (byzF s).card := by
  unfold corrIds
  rw [Finset.card_image_of_injOn (by simpa using hinj)]
  have : s.honestFinset = (byzF s)ᶜ := by
    ext p; simp [byzF]
  rw [this, Finset.card_compl, Fintype.card_fin]

variable (hinj : Set.InjOn s.input s.honest) (hf : (byzF s).card ≤ t)
include hinj hf

/-- Echoes of correct processes are valid at every process. -/
lemma vEcho_honest (p : Fin n) {j : Fin n} (hj : j ∉ s.byz) :
    vEcho t (inb1 s p) (inb2 s p) j = timely (inb1 s j) := by
  apply vEcho_eq_of_valid t _ _ (inb2_honest p hj)
  refine ⟨by simp [linkid, inb1_honest p hj], card_timely_le _, ?_⟩
  have h1 : corrIds s ⊆ timely (inb1 s p) ∩ timely (inb1 s j) :=
    Finset.subset_inter (corrIds_subset_timely p) (corrIds_subset_timely j)
  have := Finset.card_le_card h1
  rw [card_corrIds hinj] at this
  omega

/-- Correct ids are counted at least `n - t` times. -/
lemma counter_corr (p : Fin n) {z : ℕ} (hz : z ∈ corrIds s) :
    n - t ≤ counter t (inb1 s p) (inb2 s p) z := by
  have hsub : s.honestFinset ⊆ Finset.univ.filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j := by
    intro j hj
    simp only [Scenario.mem_honestFinset] at hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, vEcho_honest t hinj hf p hj]
    exact corrIds_subset_timely j hz
  have h1 := Finset.card_le_card hsub
  have h2 : s.honestFinset.card = n - (byzF s).card := by
    rw [← card_corrIds hinj]; unfold corrIds
    rw [Finset.card_image_of_injOn (by simpa using hinj)]
  unfold counter
  omega

omit hinj hf in
/-- A valid Byzantine echo contains at most `t + f ≤ 2t` non-correct ids. -/
lemma card_vEcho_sdiff_le (p : Fin n) (j : Fin n) :
    (vEcho t (inb1 s p) (inb2 s p) j \ corrIds s).card ≤ t + (byzF s).card := by
  unfold vEcho
  split
  · rename_i ids _
    split_ifs with hv
    · obtain ⟨-, hcard, hcommon⟩ := hv
      have h1 : timely (inb1 s p) ∩ ids ⊆ (ids ∩ corrIds s) ∪ (timely (inb1 s p) \ corrIds s) := by
        intro z hz
        simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hz ⊢
        tauto
      have h2 := (Finset.card_le_card h1).trans (Finset.card_union_le _ _)
      have h3 := card_timely_sdiff_le (s := s) p
      have h4 := Finset.card_sdiff_add_card_inter ids (corrIds s)
      omega
    · simp
  · simp

/-- The counter at `p` exceeds the counter at `q` at most by the number of Byzantine echoes. -/
lemma counter_le (p q : Fin n) (_hp : p ∉ s.byz) (_hq : q ∉ s.byz) (z : ℕ) :
    counter t (inb1 s p) (inb2 s p) z ≤ counter t (inb1 s q) (inb2 s q) z +
      ((byzF s).filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card := by
  unfold counter
  set E := vEcho t (inb1 s p) (inb2 s p)
  set E' := vEcho t (inb1 s q) (inb2 s q)
  have : Finset.univ.filter (fun j => z ∈ E j) ⊆
      (Finset.univ.filter fun j => z ∈ E' j) ∪ (byzF s).filter fun j => z ∈ E j := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hb : j ∈ s.byz
    · right; exact ⟨by simp [byzF, hb], hj⟩
    · left
      have h1 : E j = timely (inb1 s j) := vEcho_honest t hinj hf p hb
      have h2 : E' j = timely (inb1 s j) := vEcho_honest t hinj hf q hb
      rw [h2, ← h1]; exact hj
  exact (Finset.card_le_card this).trans (Finset.card_union_le _ _)

/-- **Lemma 43.** The new names computed by two correct processes for the same id differ by at
most `2t²`. -/
theorem lemma_43 (p q : Fin n) (hp : p ∉ s.byz) (hq : q ∉ s.byz) (v : ℕ) :
    newid t (inb1 s p) (inb2 s p) v ≤ newid t (inb1 s q) (inb2 s q) v + 2 * t ^ 2 := by
  rw [newid_eq_sum_range, newid_eq_sum_range]
  set R := Finset.range (v + 1)
  -- pointwise comparison
  have hpt : ∀ z ∈ R, min (counter t (inb1 s p) (inb2 s p) z) (n - t) ≤
      min (counter t (inb1 s q) (inb2 s q) z) (n - t) +
        (if z ∈ corrIds s then 0 else ((byzF s).filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card) := by
    intro z _
    split_ifs with hz
    · have h1 := counter_corr t hinj hf p hz
      have h2 := counter_corr t hinj hf q hz
      omega
    · have := counter_le t hinj hf p q hp hq z
      omega
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [Finset.sum_add_distrib]
  gcongr
  -- double counting of the Byzantine echoes
  calc ∑ z ∈ R, (if z ∈ corrIds s then 0 else ((byzF s).filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card)
      = ∑ z ∈ R.filter (· ∉ corrIds s), ((byzF s).filter fun j => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card := by
        rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun z _ => by split_ifs <;> simp_all
    _ = ∑ j ∈ byzF s, ((R.filter (· ∉ corrIds s)).filter fun z => z ∈ vEcho t (inb1 s p) (inb2 s p) j).card := by
        simp only [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ _j ∈ byzF s, (t + (byzF s).card) := by
        refine Finset.sum_le_sum fun j _ => le_trans (Finset.card_le_card ?_)
          (card_vEcho_sdiff_le t p j)
        intro z hz
        simp only [Finset.mem_filter] at hz
        simp only [Finset.mem_sdiff]
        exact ⟨hz.2, hz.1.2⟩
    _ = (byzF s).card * (t + (byzF s).card) := by simp
    _ ≤ t * (t + t) := Nat.mul_le_mul hf (by omega)
    _ = 2 * t ^ 2 := by ring

/-- **Lemma 44.** For correct ids `a < b`, every correct process computes
`newid[a] + (n - t) ≤ newid[b]`. -/
theorem lemma_44 (p : Fin n) {a b : ℕ} (hb : b ∈ corrIds s) (hab : a < b) :
    newid t (inb1 s p) (inb2 s p) a + (n - t) ≤ newid t (inb1 s p) (inb2 s p) b :=
  newid_add_le t _ _ hab (counter_corr t hinj hf p hb)

end Correct

open Classical in
/-- **Theorem 45.** Algorithm 8 solves order-preserving renaming with target namespace
`{1, …, n²}` in two rounds if `n > 2t² + t`. -/
theorem theorem_45 (t : ℕ) (hn : 2 * t ^ 2 + t < n) :
    Solves (⊤ : SimpleGraph (Fin n)) (alg n t) (atMost t) (OPRenaming (n ^ 2)) := by
  rintro s hbyz hs ⟨hinj, -⟩
  have hf : (byzF s).card ≤ t := by
    have : s.byz = ↑(byzF s) := by ext p; simp [byzF]
    rw [mem_atMost, this, Set.ncard_coe_finset] at hbyz
    exact hbyz
  have hdec := decides_iff (s := s) t hs
  have hK : 2 * t ^ 2 < n - t := by omega
  have hmem : ∀ p ∈ s.honest, s.input p ∈ corrIds s := fun p hp =>
    Finset.mem_image.2 ⟨p, by simpa [Scenario.honest] using hp, rfl⟩
  -- order preservation
  have hord : ∀ p ∈ s.honest, ∀ q ∈ s.honest, s.input p < s.input q →
      newid t (inb1 s p) (inb2 s p) (s.input p) < newid t (inb1 s q) (inb2 s q) (s.input q) := by
    intro p hp q hq hlt
    have h1 := lemma_43 t hinj hf p q hp hq (s.input p)
    have h2 := lemma_44 t hinj hf q (hmem q hq) hlt
    omega
  refine ⟨fun p _ => ⟨_, (hdec p _).2 rfl⟩, fun p hp o ho => ?_, fun p hp q hq o o' ho ho' hne => ?_,
    fun p hp q hq o o' ho ho' hlt => ?_⟩
  · rw [hdec] at ho
    subst ho
    refine ⟨?_, newid_le t _ _ _⟩
    -- `newid[x] ≥ min(counter[x], n - t) = n - t ≥ 1`
    rw [newid_eq_sum_range]
    calc 1 ≤ n - t := by omega
      _ = min (counter t (inb1 s p) (inb2 s p) (s.input p)) (n - t) :=
          (min_eq_right (counter_corr t hinj hf p (hmem p hp))).symm
      _ ≤ _ := Finset.single_le_sum (f := fun z => min (counter t (inb1 s p) (inb2 s p) z) (n - t))
          (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ _)
  · rw [hdec] at ho ho'
    subst ho ho'
    have hx : s.input p ≠ s.input q := fun h => hne (hinj hp hq h)
    rcases Nat.lt_or_gt_of_ne hx with h | h
    · exact (hord p hp q hq h).ne
    · exact (hord q hq p hp h).ne'
  · rw [hdec] at ho ho'
    subst ho ho'
    exact hord p hp q hq hlt

/-- Non-vacuity: the hypothesis of Theorem 45 holds e.g. for `n = 4`, `t = 1`. -/
example : Solves (⊤ : SimpleGraph (Fin 4)) (alg 4 1) (atMost 1) (OPRenaming (4 ^ 2)) :=
  theorem_45 1 (by norm_num)

end Podc.OrderPreservingByzRenaming.TwoRound
