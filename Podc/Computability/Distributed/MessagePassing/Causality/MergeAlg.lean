import Podc.Computability.Distributed.MessagePassing.Causality.Basic

-- CSLib candidate: Cslib/Computability/Distributed/MessagePassing/Causality/MergeAlg.lean

/-!
# Merge-and-update timestamping algorithms

Many online timestamping algorithms (vector clocks and their variants) have the same shape:
each process `p` keeps a value `v_p` (initially `init`); at an event `e` of `p`,

1. if `e` is a receive, `v_p := v_p ⊔ u` where `u` is the value piggybacked on the message;
2. `v_p := upd e v_p` (the update may depend on the position and kind of the event);
3. `τ(e) := v_p`; if `e` is a send, `v_p` is piggybacked on the message.

`MergeAlg.run` executes such an algorithm along an execution (a left fold: the algorithm is
distributed and online by construction); `MergeAlg.ts ex i` is the timestamp of event `i`.

* `ts_append`: timestamps depend only on the prefix ending with the event (online).
* `ts_eq`: the recurrence `τ(j) = upd j (τ(prev j) ⊔ τ(send of j))`.
* `hb_le`/`hb_lt`: with an inflationary (strictly inflationary) update, `i → j ⇒ τ i ≤ τ j`
  (`τ i < τ j`).
* `ts_map`: a map commuting with `init`, `⊔` and the updates transports timestamps between two
  algorithms (used to identify restrictions and roundings of vector clocks).
-/

namespace Cslib.Causality

/-- A merge-and-update algorithm: initial value and update rule. -/
structure MergeAlg (P V : Type*) where
  /-- The initial value of every process. -/
  init : V
  /-- The update applied at an event (given its position, the event and the merged value). -/
  upd : ℕ → Act P → V → V

namespace MergeAlg

variable {P V W : Type*} [DecidableEq P] [SemilatticeSup V] (A : MergeAlg P V)

/-- One step: process the next event `a`, given the states of the processes and the timestamps
assigned so far. -/
def step (s : (P → V) × List V) (a : Act P) : (P → V) × List V :=
  let merged := match a with
    | .recv _ m => s.1 a.proc ⊔ (s.2[m]?.getD A.init)
    | _ => s.1 a.proc
  let v := A.upd s.2.length a merged
  (Function.update s.1 a.proc v, s.2 ++ [v])

/-- Run the algorithm along an execution: final states and the list of timestamps. -/
def run (ex : Exec P) : (P → V) × List V := ex.foldl A.step (fun _ => A.init, [])

/-- The timestamp of event `i`. -/
def ts (ex : Exec P) (i : ℕ) : V := (A.run ex).2[i]?.getD A.init

/-- The value of the process of event `j` before `j`. -/
def inVal (ex : Exec P) (j : ℕ) : V := (ex.prev j).elim A.init (A.ts ex)

/-- The merged value at event `j` (before the update). -/
def merged (ex : Exec P) (j : ℕ) : V :=
  match ex[j]? with
  | some (.recv _ m) => A.inVal ex j ⊔ (if m < j then A.ts ex m else A.init)
  | _ => A.inVal ex j

lemma run_append_single (ex : Exec P) (a : Act P) :
    A.run (ex ++ [a]) = A.step (A.run ex) a := by
  simp [run, List.foldl_append]

lemma run_length (ex : Exec P) : (A.run ex).2.length = ex.length := by
  induction ex using List.reverseRecOn with
  | nil => rfl
  | append_singleton ex a ih => simp [run_append_single, step, ih]

lemma run_snd_append_single (ex : Exec P) (a : Act P) :
    (A.run (ex ++ [a])).2 = (A.run ex).2 ++ [(A.run (ex ++ [a])).2.getLast?.getD A.init] := by
  simp [run_append_single, step]

lemma run_snd_append (ex l : Exec P) :
    (A.run (ex ++ l)).2.take ex.length = (A.run ex).2 := by
  induction l generalizing ex with
  | nil => simp [List.take_of_length_le, run_length]
  | cons a l ih =>
    have := ih (ex ++ [a])
    rw [show ex ++ [a] ++ l = ex ++ a :: l by simp] at this
    rw [show ex.length = min ex.length (ex ++ [a]).length by simp, ← List.take_take, this]
    simp [run_append_single, step, run_length]

lemma ts_append (ex l : Exec P) {i : ℕ} (hi : i < ex.length) :
    A.ts (ex ++ l) i = A.ts ex i := by
  unfold ts
  rw [← A.run_snd_append ex l, List.getElem?_take_of_lt hi]

lemma ts_take (ex : Exec P) {i k : ℕ} (hi : i < k) : A.ts (ex.take k) i = A.ts ex i := by
  by_cases hk : k ≤ ex.length
  · have h := A.ts_append (ex.take k) (ex.drop k) (i := i) (by simp; omega)
    rw [List.take_append_drop] at h
    exact h.symm
  · rw [List.take_of_length_le (by omega)]

/-- The algorithm is online: the timestamp of event `i` is a function of the prefix ending
with `i`. -/
lemma ts_eq_onlineTs (ex : Exec P) {i : ℕ} (hi : i < ex.length) :
    A.ts ex i = onlineTs (fun l => A.ts l (l.length - 1)) ex i := by
  unfold onlineTs
  simp only [List.length_take, min_eq_left (show i + 1 ≤ ex.length by omega), Nat.add_sub_cancel]
  rw [A.ts_take ex (Nat.lt_succ_self i)]

lemma ts_of_length_le (ex : Exec P) {i : ℕ} (hi : ex.length ≤ i) : A.ts ex i = A.init := by
  unfold ts
  rw [List.getElem?_eq_none (by rw [run_length]; omega)]
  rfl

lemma ts_append_single_last (ex : Exec P) (a : Act P) :
    A.ts (ex ++ [a]) ex.length =
      A.upd ex.length a (match a with
        | .recv _ m => (A.run ex).1 a.proc ⊔ ((A.run ex).2[m]?.getD A.init)
        | _ => (A.run ex).1 a.proc) := by
  unfold ts
  rw [run_append_single]
  simp only [step]
  rw [List.getElem?_append_right (by rw [run_length]), run_length]
  simp

/-- The state of process `p` after the execution `ex` is the timestamp of its last event. -/
lemma run_fst (ex : Exec P) (p : P) :
    (A.run ex).1 p = (Exec.lastBefore ex p ex.length).elim A.init (A.ts ex) := by
  induction ex using List.reverseRecOn with
  | nil => rfl
  | append_singleton ex a ih =>
    rw [run_append_single]
    simp only [step]
    by_cases hp : p = a.proc
    · subst hp
      have hl : Exec.lastBefore (ex ++ [a]) a.proc (ex ++ [a]).length = some ex.length := by
        simp only [List.length_append, List.length_singleton, Exec.lastBefore, Exec.procAt,
          List.getElem?_append_right le_rfl, Nat.sub_self]
        simp
      rw [Function.update_self, hl]
      simp only [Option.elim]
      rw [ts_append_single_last, run_length]
    · rw [Function.update_of_ne hp, ih]
      have hl : Exec.lastBefore (ex ++ [a]) p (ex ++ [a]).length = Exec.lastBefore ex p ex.length := by
        simp only [List.length_append, List.length_singleton, Exec.lastBefore]
        have hne : ¬ Exec.procAt (ex ++ [a]) ex.length = some p := by
          simp [Exec.procAt, Ne.symm hp]
        simp only [hne, ite_false]
        exact Exec.lastBefore_append (ex := ex) _ le_rfl
      rw [hl]
      cases h : Exec.lastBefore ex p ex.length with
      | none => rfl
      | some i =>
        simp only [Option.elim]
        exact (A.ts_append ex [a] (Exec.lastBefore_eq_some_iff.1 h).1).symm

/-- The recurrence: `τ(j) = upd j (merged j)`. -/
lemma ts_eq (ex : Exec P) {j : ℕ} {a : Act P} (hj : ex[j]? = some a) :
    A.ts ex j = A.upd j a (A.merged ex j) := by
  have hjl : j < ex.length := (List.getElem?_eq_some_iff.1 hj).1
  set pre := ex.take j
  have hpre : pre.length = j := by simp [pre]; omega
  have hsplit : ex.take (j + 1) = pre ++ [a] := by
    rw [List.take_add_one, hj]; rfl
  rw [← A.ts_take ex (Nat.lt_succ_self j), hsplit, ← hpre, ts_append_single_last, run_fst, hpre]
  congr 1
  have hprev : ex.prev j = Exec.lastBefore pre a.proc j := by
    unfold Exec.prev
    rw [hj]
    simp only
    rw [← hpre, ← Exec.lastBefore_append (ex := pre) (ex.drop j) le_rfl, List.take_append_drop]
  have hin : (Exec.lastBefore pre a.proc j).elim A.init (A.ts pre) = A.inVal ex j := by
    unfold inVal
    rw [hprev]
    cases h : Exec.lastBefore pre a.proc j with
    | none => rfl
    | some i =>
      simp only [Option.elim]
      exact A.ts_take ex (Exec.lastBefore_eq_some_iff.1 h).1
  unfold merged
  rw [hj]
  cases a with
  | recv p m =>
    simp only [Act.proc_recv] at hin ⊢
    rw [hin]
    congr 1
    split_ifs with hm
    · rw [← A.ts_take ex hm]
      rfl
    · rw [List.getElem?_eq_none (by rw [run_length, hpre]; omega)]
      rfl
  | send p q => exact hin
  | comp p => exact hin

variable {A}

lemma inVal_le_merged (ex : Exec P) (j : ℕ) : A.inVal ex j ≤ A.merged ex j := by
  unfold merged
  split <;> simp

lemma le_merged_of_step {ex : Exec P} (hwf : ex.WF) {i j : ℕ} (h : ex.Step i j) :
    A.ts ex i ≤ A.merged ex j := by
  cases h with
  | po h =>
    refine le_trans ?_ (inVal_le_merged ex j)
    simp [inVal, h]
  | msg h =>
    unfold merged
    rw [h]
    simp [hwf.recv_lt h]

/-- With an inflationary update, timestamps are monotone along happened-before. -/
lemma le_merged_of_hb {ex : Exec P} (hwf : ex.WF) (hinf : ∀ j a x, x ≤ A.upd j a x) {i j : ℕ}
    (h : ex.HB i j) : A.ts ex i ≤ A.merged ex j := by
  induction h with
  | single h => exact le_merged_of_step hwf h
  | @tail k l h₁ h₂ ih =>
    refine le_trans ?_ (le_merged_of_step hwf h₂)
    have hk : k < ex.length := (h₂.lt hwf).trans h₂.lt_length
    rw [A.ts_eq ex (List.getElem?_eq_getElem hk)]
    exact ih.trans (hinf _ _ _)

lemma hb_le {ex : Exec P} (hwf : ex.WF) (hinf : ∀ j a x, x ≤ A.upd j a x) {i j : ℕ}
    (h : ex.HB i j) : A.ts ex i ≤ A.ts ex j := by
  rw [A.ts_eq ex (List.getElem?_eq_getElem h.lt_length)]
  exact (le_merged_of_hb hwf hinf h).trans (hinf _ _ _)

lemma hbeq_le {ex : Exec P} (hwf : ex.WF) (hinf : ∀ j a x, x ≤ A.upd j a x) {i j : ℕ}
    (h : ex.HBeq i j) : A.ts ex i ≤ A.ts ex j := by
  rcases h with rfl | h
  · exact le_rfl
  · exact hb_le hwf hinf h

/-- With a strictly inflationary update, timestamps strictly increase along happened-before. -/
lemma hb_lt {V : Type*} [Lattice V] {A : MergeAlg P V} {ex : Exec P} (hwf : ex.WF)
    (hinf : ∀ j a x, x < A.upd j a x) {i j : ℕ} (h : ex.HB i j) : A.ts ex i < A.ts ex j := by
  rw [A.ts_eq ex (List.getElem?_eq_getElem h.lt_length)]
  exact (le_merged_of_hb hwf (fun j a x => (hinf j a x).le) h).trans_lt (hinf _ _ _)

/-! ### Transport along a homomorphism -/

/-- A map `f` transports the runs of `A` to the runs of `B` if it preserves the initial value,
binary sups and commutes with the updates. -/
lemma ts_map [SemilatticeSup W] {A : MergeAlg P V} {B : MergeAlg P W} (f : V → W)
    (hinit : f A.init = B.init) (hsup : ∀ x y, f (x ⊔ y) = f x ⊔ f y)
    (hupd : ∀ j a x, f (A.upd j a x) = B.upd j a (f x)) (ex : Exec P) (i : ℕ) :
    B.ts ex i = f (A.ts ex i) := by
  have key : ∀ (l : Exec P) (s : (P → V) × List V),
      l.foldl B.step (f ∘ s.1, s.2.map f) = (f ∘ (l.foldl A.step s).1, (l.foldl A.step s).2.map f) := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons a l ih =>
      intro s
      simp only [List.foldl_cons]
      rw [← ih]
      congr 1
      simp only [step, List.length_map, Prod.mk.injEq, List.map_append, List.map_cons,
        List.map_nil]
      have hm : f (match a with
          | .recv _ m => s.1 a.proc ⊔ (s.2[m]?.getD A.init)
          | _ => s.1 a.proc) =
          (match a with
          | .recv _ m => (f ∘ s.1) a.proc ⊔ ((s.2.map f)[m]?.getD B.init)
          | _ => (f ∘ s.1) a.proc) := by
        cases a with
        | recv p m =>
          simp only [hsup, Function.comp_apply, List.getElem?_map]
          cases s.2[m]? <;> simp [hinit]
        | send p q => rfl
        | comp p => rfl
      rw [← hm, ← hupd]
      exact ⟨(Function.comp_update f s.1 a.proc _).symm, rfl⟩
  have h := key ex (fun _ => A.init, [])
  have h0 : (f ∘ (fun _ : P => A.init), ([] : List V).map f) = ((fun _ => B.init), []) := by
    simp [Function.comp_def, hinit]
  rw [h0] at h
  unfold ts run
  rw [h]
  simp only [List.getElem?_map]
  cases (ex.foldl A.step (fun _ => A.init, [])).2[i]? <;> simp [hinit]

end MergeAlg

end Cslib.Causality
