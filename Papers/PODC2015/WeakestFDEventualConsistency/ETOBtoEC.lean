import Papers.PODC2015.WeakestFDEventualConsistency.EquivBasic

/-!
# Theorem 1, direction ETOB → EC: the transformation `T_{ETOB→EC}` (Algorithm 2)

Process `p` uses an ETOB black box: its broadcasts `broadcastETOB(m)` are outputs
`tobBcast m` of the transformation, and every change of the black box's output variable `d_p` is
an input event `tobDeliver l` (the new value `l` of `d_p`, stored in the local state). The black
box is only constrained by the hypothesis that its history (`tobHist`) satisfies ETOB whenever its
broadcasts are distinct.

The application is folded into the algorithm: `inp p j` is the value `p` proposes to instance `j`;
`p` invokes instance `0` at its first time-out and instance `j + 1` in the very step in which it
returns its response to instance `j` (the usage assumption of EC). Invocations and responses are
outputs `inv j v`, `resp j v`; they form the EC history `ecHist`.

**Repair.** The paper broadcasts `(ℓ, v)`; two processes proposing the same value to the same
instance then broadcast the same message, violating the ETOB usage assumption "broadcast messages
are distinct". We broadcast `(p, ℓ, v)` instead; `First(ℓ)` is the value of the first message of
the form `(_, ℓ, _)` in `d_p`.

Instances are numbered from `0`. The state `next` is the number of instances invoked so far
(`0` before the first invocation, `count_p + 1` afterwards in the paper's notation).
-/

namespace Podc.WeakestFDEventualConsistency.ETOBtoEC

open Cslib.FailureDetectors

variable {P R V : Type*}

/-- Inputs: a new value of the ETOB black box's output variable. -/
inductive Input (P V : Type*) where
  /-- The output variable `d_p` of the ETOB black box becomes `l`. -/
  | tobDeliver (l : List (P × ℕ × V))

/-- Outputs: EC invocations and responses, and broadcasts handed to the ETOB black box. -/
inductive Output (P V : Type*) where
  /-- `proposeEC_j(v)` is invoked. -/
  | inv (j : ℕ) (v : V)
  /-- `v` is returned as the response to `proposeEC_j`. -/
  | resp (j : ℕ) (v : V)
  /-- `broadcastETOB(m)`. -/
  | tobBcast (m : P × ℕ × V)

/-- Local state. -/
structure State (P V : Type*) where
  /-- Number of instances invoked so far. -/
  next : ℕ
  /-- Last value of the black box's output variable `d_p`. -/
  d : List (P × ℕ × V)

/-- `First(j)`: the value of the first message of the form `(_, j, _)` in `l`, if any. -/
def first (l : List (P × ℕ × V)) (j : ℕ) : Option V :=
  (l.find? fun x => x.2.1 == j).map fun x => x.2.2

/-- The outputs of an invocation of instance `j` by `p`. -/
def invOuts (inp : P → ℕ → V) (p : P) (j : ℕ) : List (Output P V) :=
  [.inv j (inp p j), .tobBcast (p, j, inp p j)]

/-- **Algorithm 2** (`T_{ETOB→EC}`), with the application's proposals `inp`. It sends no messages
of its own and ignores the failure detector. -/
def alg (inp : P → ℕ → V) : Algorithm P R Empty (Input P V) (Output P V) (State P V) where
  init _ := ⟨0, []⟩
  step p _ s e := match e with
    | .recv _ m => m.elim
    | .input (.tobDeliver l) => (⟨s.next, l⟩, none, [])
    | .tick => match s.next with
      | 0 => (⟨1, s.d⟩, none, invOuts inp p 0)
      | j + 1 => match first s.d j with
        | some v => (⟨j + 2, s.d⟩, none, .resp j v :: invOuts inp p (j + 1))
        | none => (s, none, [])

/-! ### One step -/

section Step

variable (inp : P → ℕ → V) (p : P) (x : R) (s : State P V) (e : Event P Empty (Input P V))


lemma step_next : ((alg (R := R) inp).step p x s e).1.next = s.next ∨ ((alg (R := R) inp).step p x s e).1.next = s.next + 1 := by
  rcases e with ⟨_, m⟩ | _ | ⟨⟨l⟩⟩
  · exact m.elim
  · simp only [alg]
    rcases h : s.next with _ | j
    · simp
    · simp only
      rcases first s.d j with _ | v <;> simp [h]
  · simp [alg]

lemma step_d_of_ne_input (he : ∀ l, e ≠ .input (.tobDeliver l)) : ((alg (R := R) inp).step p x s e).1.d = s.d := by
  rcases e with ⟨_, m⟩ | _ | ⟨⟨l⟩⟩
  · exact m.elim
  · simp only [alg]
    rcases s.next with _ | j
    · rfl
    · simp only
      rcases first s.d j with _ | v <;> rfl
  · exact absurd rfl (he l)

lemma mem_step_outs_inv {j : ℕ} {v : V} (h : Output.inv j v ∈ ((alg (R := R) inp).step p x s e).2.2) :
    s.next = j ∧ ((alg (R := R) inp).step p x s e).1.next = j + 1 ∧ v = inp p j := by
  rcases e with ⟨_, m⟩ | _ | ⟨⟨l⟩⟩
  · exact m.elim
  · simp only [alg] at h ⊢
    rcases hn : s.next with _ | k
    · simp only [hn, invOuts] at h ⊢
      simp only [List.mem_cons, Output.inv.injEq, reduceCtorEq, List.mem_nil_iff, or_false] at h
      obtain ⟨rfl, rfl⟩ := h
      simp
    · simp only [hn] at h ⊢
      rcases hf : first s.d k with _ | w
      · simp [hf] at h
      · simp only [hf, invOuts, List.mem_cons, reduceCtorEq, Output.inv.injEq,
          List.mem_nil_iff, or_false, false_or] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        simp
  · simp [alg] at h

lemma mem_step_outs_bcast {m : P × ℕ × V} (h : Output.tobBcast m ∈ ((alg (R := R) inp).step p x s e).2.2) :
    m = (p, m.2.1, inp p m.2.1) ∧ Output.inv m.2.1 (inp p m.2.1) ∈ ((alg (R := R) inp).step p x s e).2.2 := by
  rcases e with ⟨_, m⟩ | _ | ⟨⟨l⟩⟩
  · exact m.elim
  · simp only [alg] at h ⊢
    rcases hn : s.next with _ | k
    · simp only [hn, invOuts] at h ⊢
      simp only [List.mem_cons, reduceCtorEq, Output.tobBcast.injEq, List.mem_nil_iff,
        or_false, false_or] at h
      subst h
      simp
    · simp only [hn] at h ⊢
      rcases hf : first s.d k with _ | w
      · simp [hf] at h
      · simp only [hf, invOuts, List.mem_cons, reduceCtorEq, Output.tobBcast.injEq,
          List.mem_nil_iff, or_false, false_or] at h ⊢
        subst h
        simp
  · simp [alg] at h

lemma mem_step_outs_resp {j : ℕ} {v : V} (h : Output.resp j v ∈ ((alg (R := R) inp).step p x s e).2.2) :
    s.next = j + 1 ∧ ((alg (R := R) inp).step p x s e).1.next = j + 2 ∧ first s.d j = some v := by
  rcases e with ⟨_, m⟩ | _ | ⟨⟨l⟩⟩
  · exact m.elim
  · simp only [alg] at h ⊢
    rcases hn : s.next with _ | k
    · simp [hn, invOuts] at h
    · simp only [hn] at h ⊢
      rcases hf : first s.d k with _ | w
      · simp [hf] at h
      · simp only [hf, invOuts, List.mem_cons, Output.resp.injEq, reduceCtorEq,
          List.mem_nil_iff, or_false] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        simpa using hf
  · simp [alg] at h

lemma step_outs_of_next_succ (h : ((alg (R := R) inp).step p x s e).1.next = s.next + 1) :
    Output.inv s.next (inp p s.next) ∈ ((alg (R := R) inp).step p x s e).2.2 ∧
      Output.tobBcast (p, s.next, inp p s.next) ∈ ((alg (R := R) inp).step p x s e).2.2 ∧
      ∀ j, s.next = j + 1 → ∃ v, Output.resp j v ∈ ((alg (R := R) inp).step p x s e).2.2 := by
  rcases e with ⟨_, m⟩ | _ | ⟨⟨l⟩⟩
  · exact m.elim
  · simp only [alg] at h ⊢
    rcases hn : s.next with _ | k
    · simp [invOuts]
    · simp only [hn] at h ⊢
      rcases hf : first s.d k with _ | w
      · simp [hf, hn] at h
      · simp [invOuts]
  · simp [alg] at h

lemma step_tick_zero (h : s.next = 0) : ((alg (R := R) inp).step p x s .tick).1.next = 1 := by
  simp only [alg, h]

lemma step_tick_succ {j : ℕ} {v : V} (h : s.next = j + 1) (hf : first s.d j = some v) :
    ((alg (R := R) inp).step p x s .tick).1.next = j + 2 := by
  simp only [alg, h, hf]

end Step

variable [DecidableEq P]

/-- The EC history produced by the transformation. -/
def ecHist (inp : P → ℕ → V) (r : Run P R (Input P V)) : ECHist P V where
  inv p j v t := (alg inp).Out r p (.inv j v) t
  resp p j v t := (alg inp).Out r p (.resp j v) t

/-- The history of the ETOB black box. -/
def tobHist (inp : P → ℕ → V) (r : Run P R (Input P V)) : TOBHist P (P × ℕ × V) where
  bcast p m t := (alg inp).Out r p (.tobBcast m) t
  d p t := ((alg (R := R) inp).st r p t).d


/-! ### Runs -/

section Run

variable {inp : P → ℕ → V} {r : Run P R (Input P V)}

/-- Number of instances invoked by `p` before time `t`. -/
def nxt (inp : P → ℕ → V) (r : Run P R (Input P V)) (p : P) (t : ℕ) : ℕ :=
  ((alg (R := R) inp).st r p t).next

lemma nxt_succ (p : P) (t : ℕ) :
    nxt inp r p (t + 1) = nxt inp r p t ∨ nxt inp r p (t + 1) = nxt inp r p t + 1 := by
  rcases st_succ_cases (A := alg (R := R) inp) r t p with ⟨h, -⟩ | ⟨c, e, -, -, h, -⟩
  · left; simp [nxt, h]
  · simp only [nxt, h]; exact step_next ..

lemma nxt_succ_le (p : P) (t : ℕ) : nxt inp r p (t + 1) ≤ nxt inp r p t + 1 := by
  rcases nxt_succ (inp := inp) (r := r) p t with h | h <;> omega

lemma nxt_mono (p : P) : Monotone (nxt inp r p) :=
  monotone_nat_of_le_succ fun t => by rcases nxt_succ (inp := inp) (r := r) p t with h | h <;> omega

lemma inv_iff {p : P} {j : ℕ} {v : V} {t : ℕ} :
    (ecHist inp r).inv p j v t ↔
      nxt inp r p t = j ∧ nxt inp r p (t + 1) = j + 1 ∧ v = inp p j := by
  rcases st_succ_cases (A := alg (R := R) inp) r t p with ⟨h, hout⟩ | ⟨c, e, -, -, h, hout⟩
  · simp only [ecHist, nxt, h]
    exact ⟨fun h' => absurd h' (hout _), fun ⟨h1, h2, _⟩ => by omega⟩
  · simp only [ecHist, hout, nxt, h]
    constructor
    · exact mem_step_outs_inv inp p _ _ e
    · rintro ⟨h1, h2, rfl⟩
      subst h1
      exact (step_outs_of_next_succ inp p _ _ e h2).1

lemma bcast_iff {p : P} {m : P × ℕ × V} {t : ℕ} :
    (tobHist inp r).bcast p m t ↔ ∃ j, m = (p, j, inp p j) ∧ (ecHist inp r).inv p j (inp p j) t := by
  rcases st_succ_cases (A := alg (R := R) inp) r t p with ⟨h, hout⟩ | ⟨c, e, -, -, h, hout⟩
  · simp only [tobHist, ecHist]
    exact ⟨fun h' => absurd h' (hout _), fun ⟨_, _, h'⟩ => absurd h' (hout _)⟩
  · constructor
    · intro hb
      simp only [tobHist, hout] at hb
      obtain ⟨h1, h2⟩ := mem_step_outs_bcast inp p _ _ e hb
      exact ⟨_, h1, (hout _).mpr h2⟩
    · rintro ⟨j, rfl, hinv⟩
      obtain ⟨h1, h2, -⟩ := inv_iff.mp hinv
      simp only [nxt, h] at h1 h2
      simp only [tobHist, hout]
      subst h1
      exact (step_outs_of_next_succ inp p _ _ e h2).2.1

lemma resp_spec {p : P} {j : ℕ} {v : V} {t : ℕ} (hr : (ecHist inp r).resp p j v t) :
    nxt inp r p t = j + 1 ∧ nxt inp r p (t + 1) = j + 2 ∧ first ((tobHist inp r).d p t) j = some v := by
  rcases st_succ_cases (A := alg (R := R) inp) r t p with ⟨h, hout⟩ | ⟨c, e, -, -, h, hout⟩
  · exact absurd hr (hout _)
  · simp only [ecHist, hout] at hr
    simp only [nxt, h, tobHist]
    exact mem_step_outs_resp inp p _ _ e hr

lemma resp_of_nxt {p : P} {j t : ℕ} (h1 : nxt inp r p t = j + 1) (h2 : nxt inp r p (t + 1) = j + 2) :
    ∃ v, (ecHist inp r).resp p j v t := by
  rcases st_succ_cases (A := alg (R := R) inp) r t p with ⟨h, hout⟩ | ⟨c, e, -, -, h, hout⟩
  · simp only [nxt, h] at h2 h1; omega
  · simp only [nxt, h] at h1 h2
    obtain ⟨v, hv⟩ := (step_outs_of_next_succ inp p (r.H p t) _ e (by omega)).2.2 j h1
    exact ⟨v, (hout _).mpr hv⟩

lemma nxt_tick_zero {p : P} {t : ℕ} (hσ : r.σ t = some (p, .tick)) (h0 : nxt inp r p t = 0) :
    nxt inp r p (t + 1) = 1 := by
  have := (Algorithm.cfg_succ_of_event (A := alg (R := R) inp) r t p .tick .tick hσ
    (Algorithm.event_tick _)).1
  simp only [nxt] at h0 ⊢
  rw [this]
  exact step_tick_zero inp p _ _ h0

lemma nxt_tick_succ {p : P} {t j : ℕ} {v : V} (hσ : r.σ t = some (p, .tick))
    (h0 : nxt inp r p t = j + 1) (hf : first ((tobHist inp r).d p t) j = some v) :
    nxt inp r p (t + 1) = j + 2 := by
  have := (Algorithm.cfg_succ_of_event (A := alg (R := R) inp) r t p .tick .tick hσ
    (Algorithm.event_tick _)).1
  simp only [nxt, tobHist] at h0 hf ⊢
  rw [this]
  exact step_tick_succ inp p _ _ h0 hf

lemma eq_of_nxt {p : P} {t t' n : ℕ} (h1 : nxt inp r p t = n) (h2 : nxt inp r p (t + 1) = n + 1)
    (h1' : nxt inp r p t' = n) (h2' : nxt inp r p (t' + 1) = n + 1) : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := nxt_mono (inp := inp) (r := r) p (show t + 1 ≤ t' by omega); omega
  · have := nxt_mono (inp := inp) (r := r) p (show t' + 1 ≤ t by omega); omega

/-- If `p` has invoked at least `n + 1` instances by time `t`, it invoked instance `n` earlier. -/
lemma exists_inv_of_lt_nxt {p : P} {t n : ℕ} (h : n < nxt inp r p t) :
    ∃ t' < t, (ecHist inp r).inv p n (inp p n) t' := by
  obtain ⟨s, -, hs, h1, h2⟩ := exists_step_of_le_lt (nxt_mono p) (nxt_succ_le p)
    (show nxt inp r p 0 ≤ n from Nat.zero_le n) h
  exact ⟨s, hs, inv_iff.mpr ⟨h1, h2, rfl⟩⟩

end Run

/-! ### `First` -/

omit [DecidableEq P] in
lemma find?_of_first {l : List (P × ℕ × V)} {j : ℕ} {v : V} (h : first l j = some v) :
    ∃ a, l.find? (fun x => x.2.1 == j) = some (a, j, v) := by
  simp only [first, Option.map_eq_some_iff] at h
  obtain ⟨⟨a, j', v'⟩, h1, rfl⟩ := h
  have := List.find?_some h1
  simp only [beq_iff_eq] at this
  subst this
  exact ⟨a, h1⟩

omit [DecidableEq P] in
lemma first_isSome_of_mem {l : List (P × ℕ × V)} {a : P} {j : ℕ} {v : V} (h : (a, j, v) ∈ l) :
    ∃ w, first l j = some w := by
  rcases hf : l.find? (fun x => x.2.1 == j) with _ | x
  · rw [List.find?_eq_none] at hf
    exact absurd (by simp) (hf _ h)
  · exact ⟨x.2.2, by simp [first, hf]⟩

/-! ### Correctness -/

section Correctness

variable {inp : P → ℕ → V} {r : Run P R (Input P V)}

/-- The transformation respects the usage assumption of EC (as a black box for its own
application): instances are invoked once each, `j + 1` exactly when the response to `j` is
returned. -/
theorem ecHist_properUse : (ecHist inp r).ProperUse where
  inv_once p j v v' t t' h h' := by
    obtain ⟨h1, h2, rfl⟩ := inv_iff.mp h
    obtain ⟨h1', h2', rfl⟩ := inv_iff.mp h'
    exact ⟨eq_of_nxt h1 h2 h1' h2', rfl⟩
  inv_succ p j v t h := by
    obtain ⟨h1, h2, -⟩ := inv_iff.mp h
    exact resp_of_nxt h1 h2
  resp_inv p j v t h := by
    obtain ⟨h1, h2, -⟩ := resp_spec h
    exact ⟨_, inv_iff.mpr ⟨h1, h2, rfl⟩⟩

/-- Responses come after the corresponding invocations. -/
theorem ecHist_respAfterInv : (ecHist inp r).RespAfterInv := fun p j v t h => by
  obtain ⟨h1, -, -⟩ := resp_spec h
  obtain ⟨t', ht', hi⟩ := exists_inv_of_lt_nxt (show j < nxt inp r p t by omega)
  exact ⟨_, t', ht', hi⟩

/-- The repaired transformation broadcasts distinct messages (the usage assumption of ETOB). -/
theorem tobHist_distinct : (tobHist inp r).Distinct := fun p q m t t' h h' => by
  obtain ⟨j, rfl, hi⟩ := bcast_iff.mp h
  obtain ⟨j', he, hi'⟩ := bcast_iff.mp h'
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, -⟩ := he
  exact ⟨rfl, (ecHist_properUse.inv_once _ _ _ _ _ _ hi hi').1⟩

theorem ecIntegrity : ECIntegrity (ecHist inp r) := fun p j v v' t t' h h' => by
  obtain ⟨h1, h2, h3⟩ := resp_spec h
  obtain ⟨h1', h2', h3'⟩ := resp_spec h'
  have := eq_of_nxt h1 h2 h1' h2'
  subst this
  rw [h3] at h3'
  exact ⟨rfl, Option.some.inj h3'⟩

theorem ecValidity (hnc : TOBNoCreation (tobHist inp r)) : ECValidity (ecHist inp r) := by
  intro p j v t h
  obtain ⟨-, -, hf⟩ := resp_spec h
  obtain ⟨a, ha⟩ := find?_of_first hf
  obtain ⟨q', t', ht', hb⟩ := hnc p t _ (List.mem_of_find?_eq_some ha)
  obtain ⟨j', he, hi⟩ := bcast_iff.mp hb
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  exact ⟨a, t', ht'.le, hi⟩

theorem ecTermination (hA : (alg inp).Admissible r) (hval : TOBValidity r.F (tobHist inp r)) :
    ECTermination r.F (ecHist inp r) := by
  intro p hp
  have key : ∀ n, ∃ t, n ≤ nxt inp r p t := by
    intro n
    induction n with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ n ih =>
      obtain ⟨t, ht⟩ := ih
      cases n with
      | zero =>
        obtain ⟨t1, -, hσ⟩ := hA.ticks p hp t
        by_cases h0 : nxt inp r p t1 = 0
        · exact ⟨t1 + 1, by rw [nxt_tick_zero hσ h0]⟩
        · exact ⟨t1, by omega⟩
      | succ j =>
        obtain ⟨t0, -, hi⟩ := exists_inv_of_lt_nxt (show j < nxt inp r p t by omega)
        obtain ⟨T, -, hT⟩ := hval p _ t0 hp (bcast_iff.mpr ⟨j, rfl, hi⟩)
        obtain ⟨t1, ht1, hσ⟩ := hA.ticks p hp (max T t)
        by_cases hlt : j + 2 ≤ nxt inp r p t1
        · exact ⟨t1, hlt⟩
        · have hn : nxt inp r p t1 = j + 1 := by
            have := nxt_mono (inp := inp) (r := r) p (le_of_max_le_right ht1)
            omega
          obtain ⟨v, hv⟩ := first_isSome_of_mem (hT t1 (le_of_max_le_left ht1))
          exact ⟨t1 + 1, by rw [nxt_tick_succ hσ hn hv]⟩
  intro j
  obtain ⟨t, ht⟩ := key (j + 2)
  obtain ⟨s, -, -, h1, h2⟩ := exists_step_of_le_lt (nxt_mono p) (nxt_succ_le p)
    (show nxt inp r p 0 ≤ j + 1 from Nat.zero_le _) (show j + 1 < nxt inp r p t by omega)
  obtain ⟨v, hv⟩ := resp_of_nxt h1 h2
  exact ⟨v, s, hv⟩

/-- EC-Agreement. The instance `k` is chosen beyond every instance invoked before both `τ` (the
ETOB stabilization time) and the crashes of all faulty processes; the paper's choice ("the
smallest `k` such that every process invoking `proposeEC_k` invokes it after `τ`") does not
account for faulty processes, whose `d` is not constrained by ETOB-Stability/Total-order. -/
theorem ecAgreement [Finite P] (hA : (alg inp).Admissible r) (hetob : ETOB r.F (tobHist inp r)) :
    ∃ k, ECAgreementFrom (ecHist inp r) k := by
  obtain ⟨-, -, hnd, hag, τ, hstab, htot⟩ := hetob
  obtain ⟨Tc, hTc⟩ := r.F.exists_crash_bound
  obtain ⟨K, hK⟩ := exists_bound (fun p => nxt inp r p (max τ Tc))
  refine ⟨K, fun j hj p q v v' t t' h h' => ?_⟩
  have late : ∀ p v t, (ecHist inp r).resp p j v t → max τ Tc ≤ t ∧ r.F.Correct p := by
    intro p v t h
    obtain ⟨h1, -, -⟩ := resp_spec h
    have hTt : max τ Tc ≤ t := by
      by_contra hc
      have := nxt_mono (inp := inp) (r := r) p (show t ≤ max τ Tc by omega)
      have := hK p
      omega
    obtain ⟨c, hσ⟩ := h.1
    exact ⟨hTt, correct_of_step_of_le hA hTc (le_trans (le_max_right _ _) hTt) hσ⟩
  obtain ⟨hTt, hp⟩ := late p v t h
  obtain ⟨hTt', hq⟩ := late q v' t' h'
  by_contra hne
  obtain ⟨-, -, hf⟩ := resp_spec h
  obtain ⟨-, -, hf'⟩ := resp_spec h'
  obtain ⟨a, ha⟩ := find?_of_first hf
  obtain ⟨b, hb⟩ := find?_of_first hf'
  have hne' : (b, j, v') ≠ (a, j, v) := by simp only [ne_eq, Prod.mk.injEq]; tauto
  have hτt : τ ≤ t := le_trans (le_max_left _ _) hTt
  have hτt' : τ ≤ t' := le_trans (le_max_left _ _) hTt'
  -- `p` stably delivers its first message `(a, j, v)`, `q` its first message `(b, j, v')`
  have hsp : (tobHist inp r).StablyDelivers p (a, j, v) :=
    ⟨t, fun t'' ht'' => (hstab p hp t t'' hτt ht'').subset (List.mem_of_find?_eq_some ha)⟩
  have hsq : (tobHist inp r).StablyDelivers q (b, j, v') :=
    ⟨t', fun t'' ht'' => (hstab q hq t' t'' hτt' ht'').subset (List.mem_of_find?_eq_some hb)⟩
  obtain ⟨T1, hT1⟩ := hag p q (a, j, v) hp hq hsp
  obtain ⟨T2, hT2⟩ := hag q p (b, j, v') hq hp hsq
  obtain ⟨T3, hT3⟩ := hsp
  obtain ⟨T4, hT4⟩ := hsq
  set T := max (max t t') (max (max T1 T2) (max T3 T4))
  have h1 : Before (a, j, v) (b, j, v') ((tobHist inp r).d p T) :=
    before_of_find?_of_prefix ha (hstab p hp t T hτt (by omega)) (hT2 T (by omega)) (by simp) hne'
  have h2 : Before (b, j, v') (a, j, v) ((tobHist inp r).d q T) :=
    before_of_find?_of_prefix hb (hstab q hq t' T hτt' (by omega)) (hT1 T (by omega)) (by simp)
      hne'.symm
  have h3 := htot p q hp hq T (by omega) _ _ (hT1 T (by omega)) (hT4 T (by omega)) h1
  exact not_before_of_before (hnd q T) h3 h2

/-- **Theorem 1 of [DGKPS15], direction ETOB → EC.** In every admissible run of the
(repaired) transformation `T_{ETOB→EC}` in which the ETOB black box satisfies ETOB whenever it
is used properly (distinct broadcasts), the invocation/response history of the transformation
satisfies eventual consensus. -/
theorem ec_of_etob [Finite P] (hA : (alg inp).Admissible r)
    (hbb : (tobHist inp r).Distinct → ETOB r.F (tobHist inp r)) : EC r.F (ecHist inp r) := by
  have h := hbb tobHist_distinct
  exact ⟨ecTermination hA h.1, ecIntegrity, ecValidity h.2.1, ecAgreement hA h⟩

end Correctness

end Podc.WeakestFDEventualConsistency.ETOBtoEC
