import Papers.PODC2025.TwoShotConsensusObjects.Defs

/-!
# The queue examples of Section 4.2.5

A FIFO queue of natural numbers with `enqueue(x)`, `dequeue()` and `read()` (returns the whole
content). With the allowance maps of the paper:

* **RQ** (readable queue, both processes may call everything) is in `C₁` (`rq_C1`), with the
  paper's witness (queue `[0]`, `f = g = dequeue`);
* **WQ** (weak queue, nobody may dequeue) is in `C₂` (`wq_C2`), with the paper's witness
  (empty queue, `f = enqueue(0)`, `g = enqueue(1)`, `c₀ = c₁ = read`);
* **AQ** (asymmetric queue, only `p₀` may dequeue): the paper claims AQ is in `C₁.₅` with
  witness `s = [0]`, `f = dequeue`, `f' = read`, `g = enqueue(1)`, `g' = read`. This witness
  violates property (1) (`paper_AQ_witness_fails`: `dequeue` returns `0` whether or not
  `enqueue(1)` came first) and in fact **AQ is not in `C₁.₅` at all** (`aq_not_C15`, for every
  state and every choice of operations, in both role orientations). AQ is in `C₂`
  (`aq_C2`, same witness as WQ), so it does solve consensus — the characterization is unaffected,
  only the illustration is wrong.
-/

namespace TwoShotCons

open Cslib.SharedMemory

/-- Queue operations. -/
inductive QOp where
  | enq (x : ℕ)
  | deq
  | read
  deriving DecidableEq

/-- Queue responses. -/
inductive QResp where
  | ok
  | val (v : Option ℕ)
  | st (l : List ℕ)
  deriving DecidableEq

/-- The sequential specification of the queue. -/
def qδ : List ℕ → QOp → List ℕ × QResp
  | l, .enq x => (l ++ [x], .ok)
  | l, .deq => (l.tail, .val l.head?)
  | l, .read => (l, .st l)

@[simp] lemma qδ_enq (l : List ℕ) (x : ℕ) : qδ l (.enq x) = (l ++ [x], .ok) := rfl
@[simp] lemma qδ_deq (l : List ℕ) : qδ l .deq = (l.tail, .val l.head?) := rfl
@[simp] lemma qδ_read (l : List ℕ) : qδ l .read = (l, .st l) := rfl

/-- The FIFO queue with `read`. -/
abbrev queue : ObjSpec where
  State := List ℕ
  Op := QOp
  Resp := QResp
  init := []
  δ := qδ

/-- Readable queue: both processes may call every operation. -/
def RQ : Fin 2 → Set QOp := fun _ => Set.univ

/-- Asymmetric queue: `p₁` may not dequeue. -/
def AQ : Fin 2 → Set QOp := fun p => if p = 0 then Set.univ else {o | o ≠ .deq}

/-- Weak queue: nobody may dequeue. -/
def WQ : Fin 2 → Set QOp := fun _ => {o | o ≠ .deq}

instance : DecidableEq queue.Resp := inferInstanceAs (DecidableEq QResp)

/-- RQ is in `C₁` (paper's witness). -/
theorem rq_C1 : C1 queue RQ :=
  ⟨([0] : List ℕ), QOp.deq, QOp.deq, trivial, trivial, by
    unfold DistBoth Dist view; decide⟩

/-- The paper's witness for "AQ is in `C₁.₅`" violates property (1). -/
theorem paper_AQ_witness_fails :
    ¬ Dist queue ([0] : List ℕ) 0 [(0, QOp.deq), (1, QOp.enq 1)] [(1, QOp.enq 1), (0, QOp.deq)] := by
  unfold Dist view; decide

/-- The `C₂` properties hold for WQ with the paper's witness. -/
theorem wq_C2Cond : C2Cond queue WQ := by
  refine ⟨([] : List ℕ), QOp.enq 0, QOp.enq 1, 1, fun _ => QOp.read, by decide,
    by simp [WQ], by simp [WQ], fun i _ => by simp [WQ], ?_⟩
  unfold DistBoth Dist view own
  decide

lemma C1.mono {O : ObjSpec} {m m' : Fin 2 → Set O.Op} (h : ∀ p, m p ⊆ m' p) (hc : C1 O m) :
    C1 O m' := by
  obtain ⟨s, f, g, hf, hg, hd⟩ := hc
  exact ⟨s, f, g, h 0 hf, h 1 hg, hd⟩

lemma C15Cond.mono {O : ObjSpec} {m m' : Fin 2 → Set O.Op} (h : ∀ p, m p ⊆ m' p) {a b : Fin 2}
    (hc : C15Cond O m a b) : C15Cond O m' a b := by
  obtain ⟨s, f, f', g, g', hf, hf', hg, hg', rest⟩ := hc
  exact ⟨s, f, f', g, g', h a hf, h a hf', h b hg, h b hg', rest⟩

lemma wq_le_aq : ∀ p, WQ p ⊆ AQ p := by
  intro p o ho
  fin_cases p <;> simp_all [WQ, AQ]

/-- AQ is not in `C₁`. -/
theorem aq_not_C1 : ¬ C1 queue AQ := by
  rintro ⟨s, f, g, -, hg, hD0, hD1⟩
  simp only [AQ, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, Set.mem_ofPred_eq] at hg
  cases g with
  | enq y => apply hD1; simp [view, resps]
  | deq => exact hg rfl
  | read => apply hD0; simp [view, resps]

/-- **AQ is not in `C₁.₅`** (for every state and every choice of operations, in both role
orientations), contrary to the example of Section 4.2.5. -/
theorem aq_not_C15Cond (a b : Fin 2) (hab : a ≠ b) : ¬ C15Cond queue AQ a b := by
  rintro ⟨s, f, f', g, g', hf, hf', hg, hg', h1, -, h3, h4, -⟩
  rw [distBoth_iff queue hab] at h3 h4
  have := fin2_cases' a b hab
  rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- `p₀` distinguishes, `p₁` may only enqueue / read
    simp only [AQ, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, Set.mem_ofPred_eq] at hg hg'
    cases g with
    | deq => exact hg rfl
    | read => apply h1; simp [view, resps]
    | enq y =>
      cases g' with
      | deq => exact hg' rfl
      | enq z => apply h3.2; simp [view, resps]
      | read =>
        cases f with
        | enq x => apply h1; simp [view, resps]
        | read => apply h3.2; simp [view, resps]
        | deq =>
          cases s with
          | nil => apply h4.2; simp [view, resps]
          | cons z t => apply h1; simp [view, resps]
  · -- `p₁` distinguishes with `enqueue` / `read`
    simp only [AQ, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, ite_false, Set.mem_ofPred_eq] at hf
    cases f with
    | deq => exact hf rfl
    | enq x => apply h1; simp [view, resps]
    | read => apply h3.2; simp [view, resps]
where
  fin2_cases' (a b : Fin 2) (hab : a ≠ b) : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    fin_cases a <;> fin_cases b <;> simp_all

theorem aq_not_C15 : ¬ C15 queue AQ := fun h =>
  h.2.elim (aq_not_C15Cond 0 1 (by decide)) (aq_not_C15Cond 1 0 (by decide))

/-- AQ is in `C₂` (with the witness of WQ). -/
theorem aq_C2 : C2 queue AQ := by
  refine ⟨aq_not_C1, aq_not_C15, ?_⟩
  obtain ⟨s, f, g, n, c, hn, hf, hg, hc, rest⟩ := wq_C2Cond
  exact ⟨s, f, g, n, c, hn, wq_le_aq 0 hf, wq_le_aq 1 hg, fun i hi => wq_le_aq _ (hc i hi), rest⟩

/-- WQ is in `C₂`. -/
theorem wq_C2 : C2 queue WQ :=
  ⟨fun h => aq_not_C1 (h.mono wq_le_aq),
    fun h => aq_not_C15 ⟨aq_not_C1, h.2.elim (fun h => Or.inl (h.mono wq_le_aq))
      (fun h => Or.inr (h.mono wq_le_aq))⟩, wq_C2Cond⟩

end TwoShotCons
