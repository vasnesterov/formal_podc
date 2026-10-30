import Papers.PODC2019.RDMAAgreement.LowerBound.Model

/-!
# Theorem 6.1: no 2-deciding consensus with static permissions

Aguilera, Ben-David, Guerraoui, Marathe, Zablotchi, *The Impact of RDMA on Agreement*, PODC 2019
(arXiv:1905.12143v2), Theorem 6.1.

Proof (repaired version of the paper's). In the failure-free synchronous run with read-first tie
breaking, the reads a process `p` invokes at time 0 take effect before any write, so they return
the initial memory; write responses are fixed by the static permissions. Hence the local state of
`p` at times 0, 1, 2 is a function of its input alone (`view0`, `view1`, `view2`). Suppose it
records a decision `v`. Take `v' ≠ v` and the synchronous run `E''` in which `p` is crashed from
the start and everybody else has input `v'`: by termination some `q ≠ p` decides, by validity it
decides `v'`. Now build the asynchronous execution `E'`: `p` (input as before) invokes its initial
operations, its reads take effect at once, its writes stay pending; then the others replay `E''`
(they cannot see `p`: its reads change nothing and its writes have not taken effect), so `q`
decides `v'`; finally `p`'s writes take effect and `p` replays its first two steps and decides `v`,
contradicting agreement.

The paper's proof instead starts from an *arbitrary* execution in which `p` decides in two delays
and lets a single process `p'` run alone; see `differencies.md` for why both steps need repair.
-/

namespace Podc.RDMAAgreement.LowerBound

open Function

set_option linter.unusedSectionVars false

variable {P V R W S : Type*} [DecidableEq P] [DecidableEq R] [DecidableEq W]

namespace Alg

variable (A : Alg P V R W S)

/-! ### Basic facts about `exec` and `run` -/

@[simp] lemma run_nil (c : Cfg P R W S) : A.run c [] = c := rfl

@[simp] lemma run_cons (c : Cfg P R W S) (e : Event P R W) (es : List (Event P R W)) :
    A.run c (e :: es) = A.run (A.exec c e) es := rfl

lemma run_append (c : Cfg P R W S) (es es' : List (Event P R W)) :
    A.run c (es ++ es') = A.run (A.run c es) es' := by
  simp [run, List.foldl_append]

lemma exec_lin (c : Cfg P R W S) (p : P) (o : Op R W) :
    A.exec c (.lin p o) =
      if o ∈ c.pend p then
        { c with
          mem := (A.access p c.mem o).1
          pend := Function.update c.pend p ((c.pend p).erase o)
          ready := Function.update c.ready p (c.ready p ++ [(o, (A.access p c.mem o).2)]) }
      else c := rfl

lemma exec_step (c : Cfg P R W S) (p : P) (k : ℕ) :
    A.exec c (.step p k) =
      { c with
        st := Function.update c.st p (A.step p (c.st p) ((c.ready p).take k)).1
        ready := Function.update c.ready p ((c.ready p).drop k)
        pend := Function.update c.pend p
          (c.pend p ++ (A.step p (c.st p) ((c.ready p).take k)).2) } := rfl

/-- The components of process `p` in a configuration. -/
def Own (c c' : Cfg P R W S) (p : P) : Prop :=
  c.st p = c'.st p ∧ c.pend p = c'.pend p ∧ c.ready p = c'.ready p

lemma exec_own_of_ne (c : Cfg P R W S) (e : Event P R W) (p : P) (h : e.proc ≠ p) :
    Own (A.exec c e) c p := by
  cases e with
  | lin q o =>
    simp only [Event.proc] at h
    rw [exec_lin]
    split_ifs
    · exact ⟨rfl, update_of_ne h.symm _ _, update_of_ne h.symm _ _⟩
    · exact ⟨rfl, rfl, rfl⟩
  | step q k =>
    simp only [Event.proc] at h
    exact ⟨update_of_ne h.symm _ _, update_of_ne h.symm _ _, update_of_ne h.symm _ _⟩

lemma run_own_of_ne (c : Cfg P R W S) (es : List (Event P R W)) (p : P)
    (h : ∀ e ∈ es, e.proc ≠ p) : Own (A.run c es) c p := by
  induction es generalizing c with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons e es ih =>
    simp only [run_cons]
    obtain ⟨h1, h2, h3⟩ := ih (A.exec c e) (fun e' he' => h e' (by simp [he']))
    obtain ⟨g1, g2, g3⟩ := A.exec_own_of_ne c e p (h e (by simp))
    exact ⟨h1.trans g1, h2.trans g2, h3.trans g3⟩

/-- Two configurations agree on the memory and on all processes other than `p`. -/
def AgreeExcept (p : P) (c c' : Cfg P R W S) : Prop :=
  c.mem = c'.mem ∧ ∀ q, q ≠ p → Own c c' q

lemma exec_agreeExcept {p : P} {c c' : Cfg P R W S} (h : AgreeExcept p c c')
    (e : Event P R W) (he : e.proc ≠ p) : AgreeExcept p (A.exec c e) (A.exec c' e) := by
  obtain ⟨hm, ho⟩ := h
  cases e with
  | lin q o =>
    simp only [Event.proc] at he
    obtain ⟨-, hp, hr⟩ := ho q he
    rw [exec_lin, exec_lin, hp]
    split_ifs with hmem
    · refine ⟨by simp [hm], fun r hr' => ⟨(ho r hr').1, ?_, ?_⟩⟩
      · by_cases hrq : r = q
        · subst hrq; simp
        · simp [update_of_ne hrq, (ho r hr').2.1]
      · by_cases hrq : r = q
        · subst hrq; simp [hr, hm]
        · simp [update_of_ne hrq, (ho r hr').2.2]
    · exact ⟨hm, ho⟩
  | step q k =>
    simp only [Event.proc] at he
    obtain ⟨hs, hp, hr⟩ := ho q he
    rw [exec_step, exec_step]
    refine ⟨hm, fun r hr' => ?_⟩
    by_cases hrq : r = q
    · subst hrq; simp [Own, hs, hp, hr]
    · simp [Own, update_of_ne hrq, (ho r hr').1, (ho r hr').2.1, (ho r hr').2.2]

lemma run_agreeExcept {p : P} {c c' : Cfg P R W S} (h : AgreeExcept p c c')
    (es : List (Event P R W)) (he : ∀ e ∈ es, e.proc ≠ p) :
    AgreeExcept p (A.run c es) (A.run c' es) := by
  induction es generalizing c c' with
  | nil => exact h
  | cons e es ih =>
    exact ih (exec_agreeExcept A h e (he e (by simp))) (fun e' he' => he e' (by simp [he']))

/-- Linearizations never change local states. -/
lemma exec_lin_st (c : Cfg P R W S) (q : P) (o : Op R W) :
    (A.exec c (.lin q o)).st = c.st := by
  rw [exec_lin]; split_ifs <;> rfl

/-- Linearizations only append to the undelivered responses. -/
lemma exec_lin_ready (c : Cfg P R W S) (q p : P) (o : Op R W) :
    ∃ L, (A.exec c (.lin q o)).ready p = c.ready p ++ L := by
  rw [exec_lin]
  split_ifs
  · by_cases hpq : p = q
    · subst hpq; exact ⟨[(o, (A.access p c.mem o).2)], by simp⟩
    · exact ⟨[], by simp [update_of_ne hpq]⟩
  · exact ⟨[], by simp⟩

/-- An event list consisting of linearizations. -/
def AllLin (es : List (Event P R W)) : Prop := ∀ e ∈ es, ∃ q o, e = .lin q o

lemma run_lin_st_ready (c : Cfg P R W S) (es : List (Event P R W)) (h : AllLin es) (p : P) :
    (A.run c es).st p = c.st p ∧ ∃ L, (A.run c es).ready p = c.ready p ++ L := by
  induction es generalizing c with
  | nil => exact ⟨rfl, [], by simp⟩
  | cons e es ih =>
    obtain ⟨q, o, rfl⟩ := h e (by simp)
    obtain ⟨h1, L, h2⟩ := ih (A.exec c (.lin q o)) (fun e he => h e (by simp [he]))
    obtain ⟨L', h3⟩ := A.exec_lin_ready c q p o
    refine ⟨by simp [h1, A.exec_lin_st], L' ++ L, ?_⟩
    simp [h2, h3]

/-- Reads do not change the memory. -/
lemma access_read_fst (p : P) (m : R → W) (o : Op R W) (ho : o.isRead = true) :
    (A.access p m o).1 = m := by
  cases o with
  | read r => rfl
  | write r w => simp [Op.isRead] at ho

/-- Write responses do not depend on the memory (static permissions). -/
lemma access_write_snd (p : P) (m m' : R → W) (o : Op R W) (ho : o.isRead = false) :
    (A.access p m o).2 = (A.access p m' o).2 := by
  cases o with
  | read r => simp [Op.isRead] at ho
  | write r w => simp only [access]; split_ifs <;> rfl

/-- An event list of read linearizations (of any processes) does not change the memory. -/
lemma run_reads_mem (c : Cfg P R W S) (es : List (Event P R W))
    (h : ∀ e ∈ es, ∃ q o, e = .lin q o ∧ o.isRead = true) : (A.run c es).mem = c.mem := by
  induction es generalizing c with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨q, o, rfl, ho⟩ := h e (by simp)
    rw [run_cons, ih _ (fun e he => h e (by simp [he]))]
    simp only [exec]; split_ifs
    · exact A.access_read_fst q c.mem o ho
    · rfl

/-- `p`'s own reads take effect in order: pending writes stay, responses are appended. -/
lemma run_reads_self (p : P) (l ws : List (Op R W)) (hws : ∀ o ∈ ws, o.isRead = false)
    (c : Cfg P R W S) (hc : c.pend p = ws ++ l) :
    (A.run c ((l.filter Op.isRead).map (Event.lin p))).pend p =
        ws ++ l.filter (fun o => !o.isRead) ∧
      (A.run c ((l.filter Op.isRead).map (Event.lin p))).ready p =
        c.ready p ++ (l.filter Op.isRead).map (fun o => (o, (A.access p c.mem o).2)) ∧
      (A.run c ((l.filter Op.isRead).map (Event.lin p))).mem = c.mem ∧
      (A.run c ((l.filter Op.isRead).map (Event.lin p))).st p = c.st p := by
  induction l generalizing ws c with
  | nil => simp [hc]
  | cons o t ih =>
    by_cases ho : o.isRead = true
    · have hmem : o ∈ c.pend p := by simp [hc]
      have hnot : o ∉ ws := fun h => by simp [hws o h] at ho
      set c1 := A.exec c (.lin p o) with hc1
      have h1 : c1.pend p = ws ++ t := by
        simp [c1, exec, hc, List.erase_append_right _ hnot]
      have h1m : c1.mem = c.mem := by
        simp [c1, exec, hmem, A.access_read_fst p c.mem o ho]
      have h1r : c1.ready p = c.ready p ++ [(o, (A.access p c.mem o).2)] := by
        simp [c1, exec, hmem]
      have h1s : c1.st p = c.st p := by simp [c1, A.exec_lin_st]
      obtain ⟨i1, i2, i3, i4⟩ := ih ws hws c1 h1
      simp only [List.filter_cons, ho, ite_true, List.map_cons, run_cons, Bool.not_true,
        Bool.false_eq_true, ite_false] at i1 i2 i3 i4 ⊢
      refine ⟨i1, ?_, i3.trans h1m, i4.trans h1s⟩
      rw [i2, h1r, h1m]; simp
    · have ho' : o.isRead = false := by simpa using ho
      obtain ⟨i1, i2, i3, i4⟩ := ih (ws ++ [o])
        (fun o' h' => by
          rcases List.mem_append.1 h' with h' | h'
          · exact hws o' h'
          · simp at h'; subst h'; exact ho') c (by simp [hc])
      simp only [List.filter_cons, ho', Bool.false_eq_true, ite_false, Bool.not_false,
        ite_true] at i1 i2 i3 i4 ⊢
      exact ⟨by simpa using i1, i2, i3, i4⟩

/-- `p`'s pending writes take effect in order; their responses do not depend on the memory. -/
lemma run_writes_self (p : P) (l rest : List (Op R W)) (hl : ∀ o ∈ l, o.isRead = false)
    (c : Cfg P R W S) (hc : c.pend p = l ++ rest) :
    (A.run c (l.map (Event.lin p))).pend p = rest ∧
      (A.run c (l.map (Event.lin p))).ready p =
        c.ready p ++ l.map (fun o => (o, (A.access p A.mem0 o).2)) ∧
      (A.run c (l.map (Event.lin p))).st p = c.st p := by
  induction l generalizing c with
  | nil => simp [hc]
  | cons o t ih =>
    have hmem : o ∈ c.pend p := by simp [hc]
    set c1 := A.exec c (.lin p o) with hc1
    have h1 : c1.pend p = t ++ rest := by simp [c1, exec, hc]
    have h1r : c1.ready p = c.ready p ++ [(o, (A.access p A.mem0 o).2)] := by
      simp [c1, exec, hmem, A.access_write_snd p c.mem A.mem0 o (hl o (by simp))]
    have h1s : c1.st p = c.st p := by simp [c1, A.exec_lin_st]
    obtain ⟨i1, i2, i3⟩ := ih (fun o' h' => hl o' (by simp [h'])) c1 h1
    simp only [List.map_cons, run_cons]
    exact ⟨i1, by rw [i2, h1r]; simp, i3.trans h1s⟩

/-! ### The view of a process in the synchronous run up to time 2 -/

/-- Responses to the reads among `ops`, against memory `m`. -/
def rdResp (p : P) (m : R → W) (ops : List (Op R W)) : List (Op R W × Resp W) :=
  (ops.filter Op.isRead).map (fun o => (o, (A.access p m o).2))

/-- Responses to the writes among `ops` (they do not depend on the memory). -/
def wrResp (p : P) (ops : List (Op R W)) : List (Op R W × Resp W) :=
  (ops.filter fun o => !o.isRead).map (fun o => (o, (A.access p A.mem0 o).2))

/-- Responses to the initial operations in read-first order, reads returning the initial memory. -/
def resps0 (p : P) (ops : List (Op R W)) : List (Op R W × Resp W) :=
  A.rdResp p A.mem0 ops ++ A.wrResp p ops

/-- Local state of `p` at time 0, 1, 2 of the failure-free read-first synchronous run, as a
function of its input only. -/
def view (p : P) (v : V) : ℕ → S
  | 0 => (A.init p v).1
  | 1 => (A.step p (A.init p v).1 []).1
  | _ => (A.step p (A.step p (A.init p v).1 []).1 (A.resps0 p (A.init p v).2)).1

section Sync

variable [Fintype P]

lemma syncRun_eq_run (x : P → V) (C : Finset P) (t : ℕ) :
    A.syncRun x C t = A.run (A.initCfg x C) (A.syncEvs x C t) := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [syncRun, syncEvs, run_append, ← ih]

lemma exists_split (p : P) :
    ∃ s t : List P, (Finset.univ : Finset P).toList = s ++ p :: t ∧ p ∉ s ∧ p ∉ t := by
  obtain ⟨s, t, h⟩ := List.append_of_mem (Finset.mem_toList.2 (Finset.mem_univ p))
  have hnd := Finset.nodup_toList (Finset.univ : Finset P)
  rw [h] at hnd
  refine ⟨s, t, h, fun hs => ?_, fun ht => ?_⟩
  · exact (List.nodup_append.1 hnd).2.2 p hs p (by simp) rfl
  · exact (List.nodup_cons.1 (List.nodup_append.1 hnd).2.1).1 ht

lemma mem_flatMap_proc_ne {p : P} {s : List P} (hp : p ∉ s) (f : P → List (Op R W))
    {e : Event P R W} (he : e ∈ s.flatMap fun q => (f q).map (Event.lin q)) : e.proc ≠ p := by
  obtain ⟨q, hq, he⟩ := List.mem_flatMap.1 he
  obtain ⟨o, -, rfl⟩ := List.mem_map.1 he
  exact fun h => hp (h ▸ hq)

lemma mem_flatMap_read {s : List P} (c : Cfg P R W S) {e : Event P R W}
    (he : e ∈ s.flatMap fun q => ((c.pend q).filter Op.isRead).map (Event.lin q)) :
    ∃ q o, e = .lin q o ∧ o.isRead = true := by
  obtain ⟨q, -, he⟩ := List.mem_flatMap.1 he
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 he
  exact ⟨q, o, rfl, (List.mem_filter.1 ho).2⟩

/-- One synchronous round, seen by a non-crashed process `p`: its step receives exactly the
responses available at the start of the round, and afterwards the responses to the operations
that were pending at the start of the round are available, reads first (reads return the memory
at the start of the round). -/
lemma round_own (C : Finset P) (c : Cfg P R W S) (p : P) (hp : p ∉ C) :
    (A.run c (roundEvs C c)).st p = (A.step p (c.st p) (c.ready p)).1 ∧
      (A.run c (roundEvs C c)).ready p = A.rdResp p c.mem (c.pend p) ++ A.wrResp p (c.pend p) := by
  obtain ⟨s, t, hst, hs, ht⟩ := exists_split p
  set fr : P → List (Op R W) := fun q => (c.pend q).filter Op.isRead
  set fw : P → List (Op R W) := fun q => (c.pend q).filter fun o => !o.isRead
  have hround : roundEvs C c =
      (s.flatMap fun q => (fr q).map (Event.lin q)) ++ ((fr p).map (Event.lin p) ++
        (t.flatMap fun q => (fr q).map (Event.lin q))) ++
      ((s.flatMap fun q => (fw q).map (Event.lin q)) ++ ((fw p).map (Event.lin p) ++
        (t.flatMap fun q => (fw q).map (Event.lin q)))) ++
      (((s.filter fun q => q ∉ C).map fun q => Event.step q (c.ready q).length) ++
        (Event.step p (c.ready p).length ::
          ((t.filter fun q => q ∉ C).map fun q => Event.step q (c.ready q).length))) := by
    simp [roundEvs, hst, List.flatMap_append, List.filter_append, hp, fr, fw]
  rw [hround]
  simp only [run_append]
  -- reads of processes in `s`
  set c1 := A.run c (s.flatMap fun q => (fr q).map (Event.lin q))
  have c1m : c1.mem = c.mem := A.run_reads_mem c _ (fun e he => mem_flatMap_read c he)
  have c1o : Own c1 c p := A.run_own_of_ne c _ p (fun e he => mem_flatMap_proc_ne hs fr he)
  -- reads of `p`
  set c2 := A.run c1 ((fr p).map (Event.lin p))
  obtain ⟨c2p, c2r, c2m, c2s⟩ := A.run_reads_self p (c.pend p) [] (by simp) c1 (by simp [c1o.2.1])
  -- reads of processes in `t`
  set c3 := A.run c2 (t.flatMap fun q => (fr q).map (Event.lin q))
  have c3o : Own c3 c2 p := A.run_own_of_ne c2 _ p (fun e he => mem_flatMap_proc_ne ht fr he)
  -- writes of processes in `s`
  set c4 := A.run c3 (s.flatMap fun q => (fw q).map (Event.lin q))
  have c4o : Own c4 c3 p := A.run_own_of_ne c3 _ p (fun e he => mem_flatMap_proc_ne hs fw he)
  -- writes of `p`
  set c5 := A.run c4 ((fw p).map (Event.lin p))
  obtain ⟨c5p, c5r, c5s⟩ := A.run_writes_self p (fw p) []
    (fun o ho => by simpa using (List.mem_filter.1 ho).2) c4
    (by rw [c4o.2.1, c3o.2.1]; simpa using c2p)
  -- writes of processes in `t`
  set c6 := A.run c5 (t.flatMap fun q => (fw q).map (Event.lin q))
  have c6o : Own c6 c5 p := A.run_own_of_ne c5 _ p (fun e he => mem_flatMap_proc_ne ht fw he)
  -- steps of processes in `s`
  set c7 := A.run c6 ((s.filter fun q => q ∉ C).map fun q => Event.step q (c.ready q).length)
  have c7o : Own c7 c6 p := A.run_own_of_ne c6 _ p (fun e he => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
    exact fun h => hs (h ▸ (List.mem_filter.1 hq).1))
  -- the step of `p`
  have hready7 : c7.ready p = c.ready p ++ (A.rdResp p c.mem (c.pend p) ++ A.wrResp p (c.pend p)) := by
    rw [c7o.2.2, c6o.2.2, c5r, c4o.2.2, c3o.2.2, c2r, c1o.2.2, c1m]
    simp [rdResp, wrResp, fw, List.append_assoc]
  have hst7 : c7.st p = c.st p := by rw [c7o.1, c6o.1, c5s, c4o.1, c3o.1, c2s, c1o.1]
  set c8 := A.exec c7 (Event.step p (c.ready p).length)
  have c8s : c8.st p = (A.step p (c.st p) (c.ready p)).1 := by
    simp [c8, exec_step, hready7, hst7]
  have c8r : c8.ready p = A.rdResp p c.mem (c.pend p) ++ A.wrResp p (c.pend p) := by
    simp [c8, exec_step, hready7]
  -- steps of processes in `t`
  rw [run_cons]
  have c9o := A.run_own_of_ne c8
    ((t.filter fun q => q ∉ C).map fun q => Event.step q (c.ready q).length) p (fun e he => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 he
      exact fun h => ht (h ▸ (List.mem_filter.1 hq).1))
  exact ⟨c9o.1.trans c8s, c9o.2.2.trans c8r⟩

/-- The local state of a process at times 0, 1, 2 of the failure-free synchronous run depends on
its input only. -/
lemma syncRun_view (x : P → V) (p : P) (t : ℕ) (ht : t ≤ 2) :
    (A.syncRun x ∅ t).st p = A.view p (x p) t := by
  have h1 := A.round_own ∅ (A.initCfg x ∅) p (by simp)
  have h2 := A.round_own ∅ (A.syncRun x ∅ 1) p (by simp)
  interval_cases t
  · rfl
  · simp only [syncRun] at h1 ⊢
    rw [h1.1]; rfl
  · simp only [syncRun] at h1 h2 ⊢
    rw [h2.1, h1.1, h1.2]
    simp [view, resps0, initCfg]

/-- A process crashed from the start never appears in the events of a synchronous round. -/
lemma roundEvs_proc_ne {C : Finset P} {c : Cfg P R W S} {p : P} (hpC : p ∈ C)
    (hpend : c.pend p = []) : ∀ e ∈ roundEvs C c, e.proc ≠ p := by
  intro e he
  simp only [roundEvs, List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filter] at he
  rcases he with (⟨q, -, o, ho, rfl⟩ | ⟨q, -, o, ho, rfl⟩) | ⟨q, ⟨-, hq⟩, rfl⟩
  · simp only [Event.proc]; rintro rfl; simp [hpend] at ho
  · simp only [Event.proc]; rintro rfl; simp [hpend] at ho
  · simp only [Event.proc]; rintro rfl; simp [hpC] at hq

lemma syncRun_crashed (x : P → V) {C : Finset P} {p : P} (hpC : p ∈ C) (t : ℕ) :
    (A.syncRun x C t).pend p = [] ∧ ∀ e ∈ A.syncEvs x C t, e.proc ≠ p := by
  induction t with
  | zero => simp [syncRun, syncEvs, initCfg, hpC]
  | succ t ih =>
    have hr := roundEvs_proc_ne (c := A.syncRun x C t) hpC ih.1
    refine ⟨?_, ?_⟩
    · simp only [syncRun]
      rw [(A.run_own_of_ne _ _ p hr).2.1, ih.1]
    · intro e he
      simp only [syncEvs, List.mem_append] at he
      exact he.elim (ih.2 e) (hr e)

end Sync

end Alg

open Alg

/-- **Theorem 6.1** of [Aguilera et al., PODC 2019]: in the partially synchronous shared-memory
model with registers with arbitrary *static* permissions, a memory that never fails, and at most
one process crash, no consensus algorithm is 2-deciding.

Precisely: let the algorithm satisfy uniform agreement and validity in all asynchronous
executions, and termination in synchronous runs with at most one process crashed (from the
start), which is implied by termination under partial synchrony. If there are at least two
processes and two values, then in the failure-free synchronous run (simultaneous operations
linearized read-first), no process has decided by time 2, whatever the inputs. -/
theorem theorem_6_1 [Fintype P] (hP : 2 ≤ Fintype.card P) (hV : ∃ v w : V, v ≠ w)
    (A : Alg P V R W S) (hAgr : A.Agreement) (hVal : A.Validity) (hTerm : A.SyncTermination 1)
    (x₀ : P → V) (p : P) (t : ℕ) (ht : t ≤ 2) :
    A.decision ((A.syncRun x₀ ∅ t).st p) = none := by
  by_contra hdec
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hdec
  rw [A.syncRun_view x₀ p t ht] at hv
  -- another value and another process
  obtain ⟨v', hv'⟩ : ∃ v' : V, v' ≠ v := by
    obtain ⟨a, b, hab⟩ := hV
    by_cases ha : a = v
    · exact ⟨b, fun h => hab (ha.trans h.symm)⟩
    · exact ⟨a, ha⟩
  obtain ⟨q, hqp⟩ : ∃ q : P, q ≠ p := by
    by_contra! h
    have : Fintype.card P ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
    omega
  -- E'': `p` crashed from the start, everybody has input `v'`
  set x' : P → V := fun _ => v'
  obtain ⟨T, hT⟩ := hTerm x' {p} (by simp) q (by simpa using hqp)
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 hT
  obtain ⟨hcr1, hcr2⟩ := A.syncRun_crashed x' (Finset.mem_singleton_self p) T
  -- the initial configurations with and without `p` agree except at `p`
  have hinit : ∀ y : P → V, (∀ r, r ≠ p → y r = v') →
      AgreeExcept p (A.initCfg y ∅) (A.initCfg x' {p}) := by
    intro y hy
    refine ⟨rfl, fun r hr => ⟨by simp [initCfg, hy r hr, x'], by simp [initCfg, hy r hr, x', hr],
      rfl⟩⟩
  -- validity in E'' (as an asynchronous execution in which `p` never takes a step): `u = v'`
  have huv' : u = v' := by
    have hag := A.run_agreeExcept (hinit x' (fun _ _ => rfl)) (A.syncEvs x' {p} T) hcr2
    rw [← A.syncRun_eq_run] at hag
    have hdq : A.Decides x' (A.syncEvs x' {p} T) q u :=
      ⟨(A.syncEvs x' {p} T).length, by rw [List.take_length, (hag.2 q hqp).1, hu]⟩
    obtain ⟨r, hr⟩ := hVal _ _ _ _ hdq
    exact hr.symm
  -- E': `p` has input `x₀ p`; its reads take effect, then E'' is replayed, then `p`'s writes
  set xE : P → V := Function.update x' p (x₀ p)
  set ops := (A.init p (x₀ p)).2
  set pR := (ops.filter Op.isRead).map (Event.lin p)
  set pW := (ops.filter fun o => !o.isRead).map (Event.lin p)
  set E := A.syncEvs x' {p} T
  set c0 := A.initCfg xE ∅
  have hc0p : c0.pend p = [] ++ ops := by simp [c0, initCfg, xE, ops]
  obtain ⟨ca1, ca2, ca3, ca4⟩ := A.run_reads_self p ops [] (by simp) c0 hc0p
  set ca := A.run c0 pR
  have haga : AgreeExcept p ca (A.initCfg x' {p}) := by
    have h0 := hinit xE (fun r hr => by simp [xE, hr, x'])
    refine ⟨ca3.trans h0.1, fun r hr => ?_⟩
    have ho := A.run_own_of_ne c0 pR r (fun e he => by
      obtain ⟨o, -, rfl⟩ := List.mem_map.1 he; exact fun h => hr h.symm)
    obtain ⟨g1, g2, g3⟩ := h0.2 r hr
    exact ⟨ho.1.trans g1, ho.2.1.trans g2, ho.2.2.trans g3⟩
  set cb := A.run ca E
  have hagb := A.run_agreeExcept haga E hcr2
  rw [← A.syncRun_eq_run] at hagb
  have hcbo : Own cb ca p := A.run_own_of_ne ca E p hcr2
  obtain ⟨cc1, cc2, cc3⟩ := A.run_writes_self p (ops.filter fun o => !o.isRead) []
    (fun o ho => by simpa using (List.mem_filter.1 ho).2) cb (by rw [hcbo.2.1, ca1]; simp)
  set cc := A.run cb pW
  set N := (A.resps0 p ops).length
  set es := pR ++ E ++ pW ++ [Event.step p 0, Event.step p N]
  -- `q` decides `u = v'` in E'
  have hdq : A.Decides xE es q u := by
    refine ⟨(pR ++ E).length, ?_⟩
    have : es = (pR ++ E) ++ (pW ++ [Event.step p 0, Event.step p N]) := by simp [es]
    rw [this, List.take_left' rfl, run_append, (hagb.2 q hqp).1, hu]
  -- `p` decides `v` in E'
  have hready : cc.ready p = A.resps0 p ops := by
    rw [cc2, hcbo.2.2, ca2]
    simp [resps0, rdResp, wrResp, c0, initCfg]
  have hstc : cc.st p = (A.init p (x₀ p)).1 := by
    rw [cc3, hcbo.1, ca4]; simp [c0, initCfg, xE]
  have hdp : A.Decides xE es p v := by
    have hrun : A.run c0 (pR ++ E ++ pW) = cc := by simp [run_append, cc, cb, ca]
    interval_cases t
    · exact ⟨0, by simpa [c0, initCfg, xE, view] using hv⟩
    · refine ⟨(pR ++ E ++ pW ++ [Event.step p 0]).length, ?_⟩
      have : es = (pR ++ E ++ pW ++ [Event.step p 0]) ++ [Event.step p N] := by simp [es]
      rw [this, List.take_left' rfl, run_append, hrun]
      simpa [exec_step, hstc, view] using hv
    · refine ⟨es.length, ?_⟩
      have : es = (pR ++ E ++ pW) ++ [Event.step p 0, Event.step p N] := by simp [es]
      rw [List.take_length, this, run_append, hrun]
      simpa [exec_step, hstc, hready, N, view, ops] using hv
  exact hv' (huv' ▸ hAgr _ _ _ _ _ _ hdq hdp)

/-- **Theorem 6.1**, phrased with the paper's notion: no consensus algorithm is 2-deciding. -/
theorem not_twoDeciding [Fintype P] (hP : 2 ≤ Fintype.card P) (hV : ∃ v w : V, v ≠ w)
    (A : Alg P V R W S) (hAgr : A.Agreement) (hVal : A.Validity) (hTerm : A.SyncTermination 1)
    (x : P → V) : ¬ A.TwoDecidingOn x := by
  rintro ⟨p, t, ht, h⟩
  rw [theorem_6_1 hP hV A hAgr hVal hTerm x p t ht] at h
  exact Bool.false_ne_true h

end Podc.RDMAAgreement.LowerBound
