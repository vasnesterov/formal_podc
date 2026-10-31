import Papers.PODC2015.WeakestFDEventualConsistency.EquivBasic

/-!
# Theorem 1, direction EC → ETOB: the transformation `T_{EC→ETOB}` (Algorithm 1)

Process `p` uses an EC black box (multivalued, values `List M`): its invocations
`proposeEC_j(l)` are outputs `ecInv j l` of the transformation, its responses are input events
`ecResp j l` scheduled by the adversary at `p`. The black box is constrained only by hypotheses on
its history `ecHist`: well-formedness (responses after invocations, at most one response per
instance) and EC whenever it is used properly.

The application's `broadcastETOB(m)` are input events `bcast m`; the ETOB history `tobHist` has
these broadcasts and the output variable `d_p` (a field of the local state).

Instances are numbered from `0`; `count` is the number of instances invoked so far (the paper's
`count_i`, with the paper's instances numbered from `1`). `toDeliver` is kept as a duplicate-free
list and `NewBatch(d, toDeliver)` is `toDeliver` without the elements of `d` (in the order of
reception). At the first time-out, `p` proposes `d ++ NewBatch(d, toDeliver)` (here `d = []`, as
in the paper).
-/

namespace Podc.WeakestFDEventualConsistency.ECtoETOB

open Cslib.FailureDetectors

variable {P R M : Type*}

/-- Inputs: from the application (`broadcastETOB(m)`) and from the EC black box (response `l`
to instance `j`). -/
inductive Input (M : Type*) where
  /-- `broadcastETOB(m)`. -/
  | bcast (m : M)
  /-- The EC black box returns `l` as the response to `proposeEC_j`. -/
  | ecResp (j : ℕ) (l : List M)

/-- Outputs: invocations of the EC black box. -/
inductive Output (M : Type*) where
  /-- `proposeEC_j(l)`. -/
  | ecInv (j : ℕ) (l : List M)

/-- Messages. -/
inductive Msg (M : Type*) where
  /-- `push(m)`. -/
  | push (m : M)

/-- Local state. -/
structure State (M : Type*) where
  /-- The output variable `d_p`. -/
  d : List M
  /-- Messages received in `push` messages (no duplicates). -/
  toDeliver : List M
  /-- Number of EC instances invoked so far. -/
  count : ℕ

variable [DecidableEq M]

/-- `NewBatch(d, toDeliver)`: the elements of `toDeliver` not in `d`. -/
def newBatch (d td : List M) : List M := td.filter (fun m => m ∉ d)

/-- The sequence proposed to EC: `d . NewBatch(d, toDeliver)`. -/
def proposal (d td : List M) : List M := d ++ newBatch d td

/-- **Algorithm 1** (`T_{EC→ETOB}`); it ignores the failure detector. -/
def alg : Algorithm P R (Msg M) (Input M) (Output M) (State M) where
  init _ := ⟨[], [], 0⟩
  step _ _ s e := match e with
    | .input (.bcast m) => (s, some (.push m), [])
    | .recv _ (.push m) => (⟨s.d, s.toDeliver.insert m, s.count⟩, none, [])
    | .input (.ecResp _ l) =>
      (⟨l, s.toDeliver, s.count + 1⟩, none, [.ecInv s.count (proposal l s.toDeliver)])
    | .tick =>
      if s.count = 0 then
        (⟨s.d, s.toDeliver, 1⟩, none, [.ecInv 0 (proposal s.d s.toDeliver)])
      else (s, none, [])

/-! ### One step -/

section Step

variable (p : P) (x : R) (s : State M) (e : Event P (Msg M) (Input M))

lemma step_count : ((alg (P := P) (R := R)).step p x s e).1.count = s.count ∨
    ((alg (P := P) (R := R)).step p x s e).1.count = s.count + 1 := by
  rcases e with ⟨_, ⟨m⟩⟩ | _ | ⟨m⟩ | ⟨j, l⟩
  · simp [alg]
  · simp only [alg]; split_ifs <;> simp_all
  · simp [alg]
  · simp [alg]

lemma mem_step_outs {j : ℕ} {l : List M} (h : Output.ecInv j l ∈ ((alg (P := P) (R := R)).step p x s e).2.2) :
    s.count = j ∧ ((alg (P := P) (R := R)).step p x s e).1.count = j + 1 ∧
      l = proposal ((alg (P := P) (R := R)).step p x s e).1.d
        ((alg (P := P) (R := R)).step p x s e).1.toDeliver := by
  rcases e with ⟨_, ⟨m⟩⟩ | _ | ⟨m⟩ | ⟨j', l'⟩
  · simp [alg] at h
  · simp only [alg] at h ⊢
    split_ifs at h ⊢ with h0
    · simp only [List.mem_cons, Output.ecInv.injEq, List.mem_nil_iff, or_false] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [h0]
    · simp at h
  · simp [alg] at h
  · simp only [alg, List.mem_cons, Output.ecInv.injEq, List.mem_nil_iff, or_false] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    simp

lemma step_outs_of_count_succ
    (h : ((alg (P := P) (R := R)).step p x s e).1.count = s.count + 1) :
    Output.ecInv s.count (proposal ((alg (P := P) (R := R)).step p x s e).1.d
        ((alg (P := P) (R := R)).step p x s e).1.toDeliver) ∈
      ((alg (P := P) (R := R)).step p x s e).2.2 ∧
    ((e = .tick ∧ s.count = 0 ∧ ((alg (P := P) (R := R)).step p x s e).1.d = s.d) ∨
      ∃ j l, e = .input (.ecResp j l)) := by
  rcases e with ⟨_, ⟨m⟩⟩ | _ | ⟨m⟩ | ⟨j', l'⟩
  · simp [alg] at h
  · simp only [alg] at h ⊢
    split_ifs at h ⊢ with h0
    · simp [h0]
    · simp at h
  · simp [alg] at h
  · simp [alg]

lemma step_resp {j : ℕ} {l : List M} :
    ((alg (P := P) (R := R)).step p x s (.input (.ecResp j l))).1.count = s.count + 1 ∧
    ((alg (P := P) (R := R)).step p x s (.input (.ecResp j l))).1.d = l := by
  simp [alg]

lemma step_d_of_not_resp (he : ∀ j l, e ≠ .input (.ecResp j l)) :
    ((alg (P := P) (R := R)).step p x s e).1.d = s.d := by
  rcases e with ⟨_, ⟨m⟩⟩ | _ | ⟨m⟩ | ⟨j', l'⟩
  · simp [alg]
  · simp only [alg]; split_ifs <;> simp
  · simp [alg]
  · exact absurd rfl (he j' l')

lemma step_toDeliver_subset :
    s.toDeliver ⊆ ((alg (P := P) (R := R)).step p x s e).1.toDeliver := by
  rcases e with ⟨_, ⟨m⟩⟩ | _ | ⟨m⟩ | ⟨j', l'⟩
  · simp only [alg]; exact List.subset_insert _ _
  · simp only [alg]; split_ifs <;> simp
  · simp [alg]
  · simp [alg]

lemma step_toDeliver_nodup (h : s.toDeliver.Nodup) :
    ((alg (P := P) (R := R)).step p x s e).1.toDeliver.Nodup := by
  rcases e with ⟨_, ⟨m⟩⟩ | _ | ⟨m⟩ | ⟨j', l'⟩
  · simp only [alg]; exact h.insert
  · simp only [alg]; split_ifs <;> simpa
  · simpa [alg]
  · simpa [alg]

lemma mem_step_toDeliver {m : M} (h : m ∈ ((alg (P := P) (R := R)).step p x s e).1.toDeliver) :
    m ∈ s.toDeliver ∨ ∃ q, e = .recv q (.push m) := by
  rcases e with ⟨q, ⟨m'⟩⟩ | _ | ⟨m'⟩ | ⟨j', l'⟩
  · simp only [alg, List.mem_insert_iff] at h
    rcases h with rfl | h
    · exact Or.inr ⟨q, rfl⟩
    · exact Or.inl h
  · simp only [alg] at h; split_ifs at h <;> simp_all
  · simp_all [alg]
  · simp_all [alg]

lemma step_recv {q : P} {m : M} :
    m ∈ ((alg (P := P) (R := R)).step p x s (.recv q (.push m))).1.toDeliver := by
  simp [alg]

lemma step_msg_bcast {m : M} :
    ((alg (P := P) (R := R)).step p x s (.input (.bcast m))).2.1 = some (.push m) := rfl

lemma step_msg {m : Msg M} (h : ((alg (P := P) (R := R)).step p x s e).2.1 = some m) :
    ∃ m', m = .push m' ∧ e = .input (.bcast m') := by
  rcases e with ⟨_, ⟨m⟩⟩ | _ | ⟨m'⟩ | ⟨j', l'⟩
  · simp [alg] at h
  · simp only [alg] at h; split_ifs at h
  · simp only [alg, Option.some.injEq] at h
    exact ⟨m', h.symm, rfl⟩
  · simp [alg] at h

end Step

variable [DecidableEq P]

/-- The ETOB history implemented by the transformation. -/
def tobHist (r : Run P R (Input M)) : TOBHist P M where
  bcast p m t := r.σ t = some (p, .input (.bcast m))
  d p t := ((alg (R := R)).st r p t).d

/-- The history of the EC black box. -/
def ecHist (r : Run P R (Input M)) : ECHist P (List M) where
  inv p j l t := (alg (R := R)).Out r p (.ecInv j l) t
  resp p j l t := r.σ t = some (p, .input (.ecResp j l))

/-! ### Runs -/

section Run

variable {r : Run P R (Input M)}

/-- Number of instances invoked by `p` before time `t`. -/
def cnt (r : Run P R (Input M)) (p : P) (t : ℕ) : ℕ := ((alg (R := R)).st r p t).count

/-- `toDeliver_p` before time `t`. -/
def td (r : Run P R (Input M)) (p : P) (t : ℕ) : List M := ((alg (R := R)).st r p t).toDeliver

lemma cnt_succ (p : P) (t : ℕ) : cnt r p (t + 1) = cnt r p t ∨ cnt r p (t + 1) = cnt r p t + 1 := by
  rcases st_succ_cases (A := alg (R := R)) r t p with ⟨h, -⟩ | ⟨c, e, -, -, h, -⟩
  · left; simp [cnt, h]
  · simp only [cnt, h]; exact step_count ..

lemma cnt_succ_le (p : P) (t : ℕ) : cnt r p (t + 1) ≤ cnt r p t + 1 := by
  rcases cnt_succ (r := r) p t with h | h <;> omega

lemma cnt_mono (p : P) : Monotone (cnt r p) :=
  monotone_nat_of_le_succ fun t => by rcases cnt_succ (r := r) p t with h | h <;> omega

lemma cnt_zero (p : P) : cnt r p 0 = 0 := rfl

lemma d_zero (p : P) : (tobHist r).d p 0 = [] := rfl

lemma inv_iff {p : P} {j : ℕ} {l : List M} {t : ℕ} :
    (ecHist r).inv p j l t ↔ cnt r p t = j ∧ cnt r p (t + 1) = j + 1 ∧
      l = proposal ((tobHist r).d p (t + 1)) (td r p (t + 1)) := by
  rcases st_succ_cases (A := alg (R := R)) r t p with ⟨h, hout⟩ | ⟨c, e, -, -, h, hout⟩
  · simp only [ecHist, cnt, h]
    exact ⟨fun h' => absurd h' (hout _), fun ⟨h1, h2, _⟩ => by omega⟩
  · simp only [ecHist, hout, cnt, td, tobHist, h]
    constructor
    · exact mem_step_outs _ _ _ e
    · rintro ⟨h1, h2, rfl⟩
      subst h1
      exact (step_outs_of_count_succ _ _ _ e h2).1

lemma resp_step {p : P} {j : ℕ} {l : List M} {t : ℕ} (h : (ecHist r).resp p j l t) :
    cnt r p (t + 1) = cnt r p t + 1 ∧ (tobHist r).d p (t + 1) = l := by
  have := (Algorithm.cfg_succ_of_event (A := alg (R := R)) r t p _ _ h
    (Algorithm.event_input _ _)).1
  simp only [cnt, tobHist, this]
  exact step_resp ..

lemma cnt_succ_cases {p : P} {t : ℕ} (h : cnt r p (t + 1) = cnt r p t + 1) :
    (cnt r p t = 0 ∧ (tobHist r).d p (t + 1) = (tobHist r).d p t) ∨
      ∃ j l, (ecHist r).resp p j l t := by
  rcases st_succ_cases (A := alg (R := R)) r t p with ⟨h', -⟩ | ⟨c, e, hσ, he, h', -⟩
  · simp only [cnt, h'] at h; omega
  · simp only [cnt, h'] at h
    rcases (step_outs_of_count_succ _ _ _ e h).2 with ⟨rfl, h0, hd⟩ | ⟨j, l, rfl⟩
    · left; simp only [cnt, tobHist, h']; exact ⟨h0, hd⟩
    · right
      refine ⟨j, l, ?_⟩
      show r.σ t = _; rw [hσ, event_eq_input he]


lemma d_succ_of_no_resp {p : P} {t : ℕ} (h : ∀ j l, ¬ (ecHist r).resp p j l t) :
    (tobHist r).d p (t + 1) = (tobHist r).d p t := by
  rcases st_succ_cases (A := alg (R := R)) r t p with ⟨h', -⟩ | ⟨c, e, hσ, he, h', -⟩
  · simp [tobHist, h']
  · simp only [tobHist, h']
    apply step_d_of_not_resp
    rintro j l rfl
    exact h j l (show r.σ t = _ by rw [hσ, event_eq_input he])

lemma td_succ_subset (p : P) (t : ℕ) : td r p t ⊆ td r p (t + 1) := by
  rcases st_succ_cases (A := alg (R := R)) r t p with ⟨h', -⟩ | ⟨c, e, hσ, he, h', -⟩
  · simp [td, h']
  · simp only [td, h']
    exact step_toDeliver_subset ..

lemma td_mono {p : P} {t t' : ℕ} (h : t ≤ t') : td r p t ⊆ td r p t' := by
  induction t', h using Nat.le_induction with
  | base => exact fun _ h => h
  | succ t' _ ih => exact List.Subset.trans ih (td_succ_subset p t')

lemma td_nodup (p : P) (t : ℕ) : (td r p t).Nodup :=
  Algorithm.st_induction (A := alg (R := R)) r (fun _ (s : State M) => s.toDeliver.Nodup) (fun _ => List.nodup_nil)
    (fun _ _ _ _ _ _ h => step_toDeliver_nodup _ _ _ _ h) t p

/-- Messages in `toDeliver` were ETOB-broadcast earlier. -/
lemma mem_td {p : P} {t : ℕ} {m : M} (h : m ∈ td r p t) :
    ∃ q s, s < t ∧ (tobHist r).bcast q m s := by
  induction t generalizing p with
  | zero => simp [td, Algorithm.st, Algorithm.initCfg, alg] at h
  | succ t ih =>
    rcases st_succ_cases (A := alg (R := R)) r t p with ⟨h', -⟩ | ⟨c, e, hσ, he, h', -⟩
    · simp only [td, h'] at h
      obtain ⟨q, s, hs, hb⟩ := ih h
      exact ⟨q, s, by omega, hb⟩
    · simp only [td, h'] at h
      rcases mem_step_toDeliver _ _ _ _ h with h | ⟨q, rfl⟩
      · obtain ⟨q, s, hs, hb⟩ := ih h
        exact ⟨q, s, by omega, hb⟩
      · obtain ⟨s, -, hs⟩ := Algorithm.event_eq_recv he
        have hst : s < t := by
          by_contra hc
          rw [Algorithm.msg_eq_none_of_le r t s (by omega)] at hs
          simp at hs
        obtain ⟨c', e', hσ', he', hb⟩ := Algorithm.msg_spec r hs
        obtain ⟨m', hm', rfl⟩ := step_msg _ _ _ _ hb
        cases hm'
        exact ⟨q, s, by omega, show r.σ s = _ by rw [hσ', event_eq_input he']⟩

/-- A message `push(m)` received by `q` puts `m` in `toDeliver_q`. -/
lemma mem_td_of_recv (hA : (alg (R := R)).Admissible r) {p q : P} {s t : ℕ} {m : M}
    (hσ : r.σ t = some (q, .recv p s))
    (hs : ((alg (R := R)).cfg r (s + 1)).msg s = some (p, .push m)) : m ∈ td r q (t + 1) := by
  obtain ⟨hst, m', hm'⟩ := hA.recv_valid t q p s hσ
  rw [Algorithm.msg_eq_succ r hst, hs] at hm'
  cases hm'
  have := (Algorithm.cfg_succ_of_event r t q _ _ hσ (Algorithm.event_recv
    (show ((alg (R := R)).cfg r t).msg s = some (p, .push m) by rw [Algorithm.msg_eq_succ r hst, hs]))).1
  simp only [td, this]
  exact step_recv ..

/-- An ETOB-broadcast is sent as `push(m)` at the same time. -/
lemma msg_of_bcast {p : P} {s : ℕ} {m : M} (h : (tobHist r).bcast p m s) :
    ((alg (R := R)).cfg r (s + 1)).msg s = some (p, .push m) := by
  rw [(Algorithm.cfg_succ_of_event r s p _ _ h (Algorithm.event_input _ _)).2.1]
  rfl
end Run

/-! ### Proposals -/

omit [DecidableEq M] in
lemma mem_proposal [DecidableEq M] {d td : List M} {m : M} :
    m ∈ proposal d td ↔ m ∈ d ∨ m ∈ td := by
  simp only [proposal, newBatch, List.mem_append, List.mem_filter, decide_eq_true_eq]
  tauto

lemma proposal_nodup {d td : List M} (hd : d.Nodup) (htd : td.Nodup) :
    (proposal d td).Nodup := by
  rw [proposal, List.nodup_append]
  refine ⟨hd, htd.filter _, fun a ha b hb hab => ?_⟩
  subst hab
  simp only [newBatch, List.mem_filter, decide_eq_true_eq] at hb
  exact hb.2 ha

lemma prefix_proposal (d td : List M) : d <+: proposal d td := List.prefix_append _ _

/-! ### The black box is used properly -/

section BlackBox

variable {r : Run P R (Input M)}

lemma eq_of_cnt {p : P} {t t' n : ℕ} (h1 : cnt r p t = n) (h2 : cnt r p (t + 1) = n + 1)
    (h1' : cnt r p t' = n) (h2' : cnt r p (t' + 1) = n + 1) : t = t' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := cnt_mono (r := r) p (show t + 1 ≤ t' by omega); omega
  · have := cnt_mono (r := r) p (show t' + 1 ≤ t by omega); omega

variable (hwf : (ecHist r).RespAfterInv) (hint : ECIntegrity (ecHist r))
include hwf hint

/-- A (well-formed) response to instance `j` arrives when `p` has invoked exactly the instances
`0, …, j`. -/
lemma cnt_of_resp {p : P} {j : ℕ} {l : List M} {t : ℕ} (h : (ecHist r).resp p j l t) :
    cnt r p t = j + 1 := by
  induction t using Nat.strong_induction_on generalizing j l with
  | _ t ih =>
  obtain ⟨l', t', ht', hi⟩ := hwf p j l t h
  obtain ⟨h1, h2, -⟩ := inv_iff.mp hi
  have hge : j + 1 ≤ cnt r p t := h2 ▸ cnt_mono p (show t' + 1 ≤ t by omega)
  by_contra hne
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := exists_step_of_le_lt (cnt_mono p) (cnt_succ_le p)
    (show cnt r p (t' + 1) ≤ j + 1 by omega) (show j + 1 < cnt r p t by omega)
  rcases cnt_succ_cases (show cnt r p (s + 1) = cnt r p s + 1 by omega) with ⟨h0, -⟩ | ⟨j', l'', hr⟩
  · omega
  · have := ih s hs2 hr
    have hj : j' = j := by omega
    subst hj
    have := (hint p j' _ _ _ _ hr h).1
    omega

/-- The transformation uses the EC black box properly. -/
theorem ecHist_properUse : (ecHist r).ProperUse where
  inv_once p j l l' t t' h h' := by
    obtain ⟨h1, h2, rfl⟩ := inv_iff.mp h
    obtain ⟨h1', h2', rfl⟩ := inv_iff.mp h'
    obtain rfl := eq_of_cnt h1 h2 h1' h2'
    exact ⟨rfl, rfl⟩
  inv_succ p j l t h := by
    obtain ⟨h1, h2, -⟩ := inv_iff.mp h
    rcases cnt_succ_cases (show cnt r p (t + 1) = cnt r p t + 1 by omega) with ⟨h0, -⟩ | ⟨j', l', hr⟩
    · omega
    · have := cnt_of_resp hwf hint hr
      have hj : j' = j := by omega
      subst hj
      exact ⟨l', hr⟩
  resp_inv p j l t h := by
    have h1 := cnt_of_resp hwf hint h
    have h2 := (resp_step h).1
    exact ⟨_, inv_iff.mpr ⟨h1, by omega, rfl⟩⟩

/-- Before its second instance is invoked, `d_p` is empty. -/
lemma d_of_cnt_le_one {p : P} {t : ℕ} (h : cnt r p t ≤ 1) : (tobHist r).d p t = [] := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases hr : ∃ j l, (ecHist r).resp p j l t
    · obtain ⟨j, l, hr⟩ := hr
      have := cnt_of_resp hwf hint hr
      have := (resp_step hr).1
      omega
    · push Not at hr
      rw [d_succ_of_no_resp hr]
      exact ih (le_trans (cnt_mono p (Nat.le_succ t)) h)

/-- Once `p` has invoked `j + 2` instances, `d_p` is `p`'s response to instance `j`. -/
lemma resp_of_cnt {p : P} {j t : ℕ} (h : cnt r p t = j + 2) :
    ∃ t' < t, (ecHist r).resp p j ((tobHist r).d p t) t' := by
  induction t with
  | zero => simp [cnt_zero] at h
  | succ t ih =>
    by_cases hr : ∃ j l, (ecHist r).resp p j l t
    · obtain ⟨j', l, hr⟩ := hr
      have h1 := cnt_of_resp hwf hint hr
      obtain ⟨h2, h3⟩ := resp_step hr
      have hj : j' = j := by omega
      subst hj
      rw [h3]
      exact ⟨t, by omega, hr⟩
    · push Not at hr
      rw [d_succ_of_no_resp hr]
      have hc : cnt r p t = j + 2 := by
        rcases cnt_succ (r := r) p t with h' | h'
        · omega
        · rcases cnt_succ_cases h' with ⟨h0, -⟩ | ⟨j', l', hr'⟩
          · omega
          · exact absurd hr' (hr j' l')
      obtain ⟨t', ht', hr'⟩ := ih hc
      exact ⟨t', by omega, hr'⟩

lemma d_nodup_of_resp_nodup (hn : ∀ p j l t, (ecHist r).resp p j l t → l.Nodup) (p : P) (t : ℕ) :
    ((tobHist r).d p t).Nodup := by
  by_cases h : cnt r p t ≤ 1
  · rw [d_of_cnt_le_one hwf hint h]; exact List.nodup_nil
  · obtain ⟨t', -, hr⟩ := resp_of_cnt hwf hint (show cnt r p t = (cnt r p t - 2) + 2 by omega)
    exact hn _ _ _ _ hr

/-- The structure of a response under EC-Validity: it is the proposal `d ++ NewBatch` of some
invoker `q`, where `d` is `[]` (instance `0`) or `q`'s response to the previous instance. -/
lemma resp_structure (hval : ECValidity (ecHist r)) {p : P} {j : ℕ} {l : List M} {t : ℕ}
    (h : (ecHist r).resp p j l t) :
    ∃ q t', t' ≤ t ∧ (∃ c, r.σ t' = some (q, c)) ∧
      l = proposal ((tobHist r).d q (t' + 1)) (td r q (t' + 1)) ∧
      ((j = 0 ∧ (tobHist r).d q (t' + 1) = []) ∨
        ∃ j', j = j' + 1 ∧ ∃ t'' ≤ t', (ecHist r).resp q j' ((tobHist r).d q (t' + 1)) t'') := by
  obtain ⟨q, t', ht', hi⟩ := hval p j l t h
  obtain ⟨-, h2, hl⟩ := inv_iff.mp hi
  refine ⟨q, t', ht', hi.1, hl, ?_⟩
  rcases j with _ | j'
  · exact Or.inl ⟨rfl, d_of_cnt_le_one hwf hint (by omega)⟩
  · obtain ⟨t'', ht'', hr⟩ := resp_of_cnt hwf hint h2
    exact Or.inr ⟨j', rfl, t'', by omega, hr⟩

end BlackBox

/-! ### Correctness -/

section Correctness

variable {r : Run P R (Input M)}
variable (hwf : (ecHist r).RespAfterInv) (hint : ECIntegrity (ecHist r))
  (hval : ECValidity (ecHist r))
include hwf hint hval

lemma resp_nodup : ∀ j p l t, (ecHist r).resp p j l t → l.Nodup := by
  intro j
  induction j with
  | zero =>
    intro p l t h
    obtain ⟨q, t', -, -, rfl, ⟨-, h0⟩ | ⟨j', hj, -⟩⟩ := resp_structure hwf hint hval h
    · exact proposal_nodup (by rw [h0]; exact List.nodup_nil) (td_nodup _ _)
    · omega
  | succ j ih =>
    intro p l t h
    obtain ⟨q, t', -, -, rfl, ⟨h0, -⟩ | ⟨j', hj, t'', -, hr⟩⟩ := resp_structure hwf hint hval h
    · omega
    · obtain rfl : j' = j := by omega
      exact proposal_nodup (ih _ _ _ hr) (td_nodup _ _)

lemma resp_noCreation : ∀ j p l t, (ecHist r).resp p j l t → ∀ m ∈ l,
    ∃ q s, s ≤ t ∧ (tobHist r).bcast q m s := by
  intro j
  induction j with
  | zero =>
    intro p l t h m hm
    obtain ⟨q, t', ht', -, rfl, ⟨-, h0⟩ | ⟨j', hj, -⟩⟩ := resp_structure hwf hint hval h
    · rcases mem_proposal.mp hm with hm | hm
      · simp [h0] at hm
      · obtain ⟨q', s, hs, hb⟩ := mem_td hm
        exact ⟨q', s, by omega, hb⟩
    · omega
  | succ j ih =>
    intro p l t h m hm
    obtain ⟨q, t', ht', -, rfl, ⟨h0, -⟩ | ⟨j', hj, t'', ht'', hr⟩⟩ := resp_structure hwf hint hval h
    · omega
    · obtain rfl : j' = j := by omega
      rcases mem_proposal.mp hm with hm | hm
      · obtain ⟨q', s, hs, hb⟩ := ih _ _ _ hr m hm
        exact ⟨q', s, by omega, hb⟩
      · obtain ⟨q', s, hs, hb⟩ := mem_td hm
        exact ⟨q', s, by omega, hb⟩

/-- From the agreement instance `k` on, responses grow by extension. -/
lemma resp_prefix {k : ℕ} (hag : ECAgreementFrom (ecHist r) k) {j j' : ℕ} (hk : k ≤ j)
    (hj : j ≤ j') {p q : P} {l l' : List M} {t t' : ℕ} (h : (ecHist r).resp p j l t)
    (h' : (ecHist r).resp q j' l' t') : l <+: l' := by
  induction j', hj using Nat.le_induction generalizing q l' t' with
  | base => rw [hag j hk p q l l' t t' h h']
  | succ j' hj ih =>
    obtain ⟨q₀, t₀, -, -, rfl, ⟨h0, -⟩ | ⟨j'', hj'', t'', -, hr⟩⟩ := resp_structure hwf hint hval h'
    · omega
    · obtain rfl : j'' = j' := by omega
      exact (ih hr).trans (prefix_proposal _ _)

omit hval in
lemma exists_cnt_ge (hterm : ECTermination r.F (ecHist r)) {p : P} (hp : r.F.Correct p) (n : ℕ) :
    ∃ t, n + 2 ≤ cnt r p t := by
  obtain ⟨l, t, hr⟩ := hterm p hp n
  have := cnt_of_resp hwf hint hr
  have := (resp_step hr).1
  exact ⟨t + 1, by omega⟩

omit hval in
/-- `d_p` after `p` invoked `j + 2` instances (`j ≥ k`) is a response to an instance `≥ k`. -/
lemma d_eq_resp {k : ℕ} {p : P} {t : ℕ} (h : k + 2 ≤ cnt r p t) :
    ∃ j t', k ≤ j ∧ cnt r p t = j + 2 ∧ (ecHist r).resp p j ((tobHist r).d p t) t' := by
  obtain ⟨t', -, hr⟩ := resp_of_cnt hwf hint (show cnt r p t = (cnt r p t - 2) + 2 by omega)
  exact ⟨_, t', by omega, by omega, hr⟩

theorem tobNoCreation : TOBNoCreation (tobHist r) := by
  intro p t m hm
  by_cases h : cnt r p t ≤ 1
  · rw [d_of_cnt_le_one hwf hint h] at hm; simp at hm
  · obtain ⟨t', ht', hr⟩ := resp_of_cnt hwf hint (show cnt r p t = (cnt r p t - 2) + 2 by omega)
    obtain ⟨q, s, hs, hb⟩ := resp_noCreation hwf hint hval _ _ _ _ hr m hm
    exact ⟨q, s, by omega, hb⟩

theorem tobNoDup : TOBNoDup (tobHist r) :=
  d_nodup_of_resp_nodup hwf hint (fun p j l t h => resp_nodup hwf hint hval j p l t h)

theorem tobValidity [Finite P] (hA : (alg (R := R)).Admissible r)
    (hterm : ECTermination r.F (ecHist r)) : TOBValidity r.F (tobHist r) := by
  intro p m t hp hb
  have hmsg := msg_of_bcast hb
  have hrecv : ∀ q, r.F.Correct q → ∃ T, m ∈ td r q T := by
    intro q hq
    obtain ⟨t', ht'⟩ := hA.delivery q hq (t + 1) t p (.push m) hmsg
    exact ⟨t' + 1, mem_td_of_recv hA ht' hmsg⟩
  choose! T hT using hrecv
  obtain ⟨Tc, hTc⟩ := r.F.exists_crash_bound
  obtain ⟨T1, hT1⟩ := exists_bound T
  obtain ⟨j0, hj0⟩ := exists_bound (fun q => cnt r q (max Tc T1))
  -- every proposal to an instance `≥ j0` contains `m`
  have hinv : ∀ q j l t', j0 ≤ j → (ecHist r).inv q j l t' → m ∈ l := by
    intro q j l t' hj hi
    obtain ⟨h1, h2, hl⟩ := inv_iff.mp hi
    have hT0 : max Tc T1 ≤ t' := by
      by_contra hc
      have := cnt_mono (r := r) q (show t' + 1 ≤ max Tc T1 by omega)
      have := hj0 q
      omega
    obtain ⟨c, hσ⟩ := hi.1
    have hq := correct_of_step_of_le hA hTc (le_trans (le_max_left _ _) hT0) hσ
    rw [hl]
    exact mem_proposal.mpr (Or.inr (td_mono (show T q ≤ t' + 1 by have := hT1 q; omega) (hT q hq)))
  have hresp : ∀ q j l t', j0 ≤ j → (ecHist r).resp q j l t' → m ∈ l := by
    intro q j l t' hj h
    obtain ⟨q', t'', -, hi⟩ := hval q j l t' h
    exact hinv q' j l t'' hj hi
  obtain ⟨t2, ht2⟩ := exists_cnt_ge hwf hint hterm hp j0
  refine ⟨max (t + 1) t2, by omega, fun t'' ht'' => ?_⟩
  have hc : j0 + 2 ≤ cnt r p t'' := le_trans ht2 (cnt_mono p (by omega))
  obtain ⟨j, t3, hj, -, hr⟩ := d_eq_resp hwf hint hc
  exact hresp p _ _ _ hj hr

omit hval in
/-- The stabilization time: every correct process has invoked `k + 2` instances. -/
lemma exists_stab_time [Finite P] (hterm : ECTermination r.F (ecHist r)) (k : ℕ) :
    ∃ τ, ∀ p, r.F.Correct p → ∀ t, τ ≤ t → k + 2 ≤ cnt r p t := by
  have h : ∀ p, r.F.Correct p → ∃ t, k + 2 ≤ cnt r p t :=
    fun p hp => exists_cnt_ge hwf hint hterm hp k
  choose! T hT using h
  obtain ⟨τ, hτ⟩ := exists_bound T
  exact ⟨τ, fun p hp t ht => le_trans (hT p hp) (cnt_mono p (le_trans (hτ p) ht))⟩

theorem tobAgreement [Finite P] (hterm : ECTermination r.F (ecHist r)) {k : ℕ}
    (hag : ECAgreementFrom (ecHist r) k) : TOBAgreement r.F (tobHist r) := by
  intro p q m hp hq ⟨t0, hm⟩
  obtain ⟨τ, hτ⟩ := exists_stab_time hwf hint hterm k
  obtain ⟨a, ta, hka, hca, hra⟩ := d_eq_resp hwf hint (hτ p hp (max t0 τ) (le_max_right _ _))
  obtain ⟨t2, ht2⟩ := exists_cnt_ge hwf hint hterm hq a
  refine ⟨max t2 τ, fun t ht => ?_⟩
  obtain ⟨b, tb, -, hcb, hrb⟩ := d_eq_resp hwf hint (hτ q hq t (le_trans (le_max_right _ _) ht))
  have hab : a ≤ b := by
    have := cnt_mono (r := r) q (le_trans (le_max_left _ _) ht)
    omega
  exact (resp_prefix hwf hint hval hag hka hab hra hrb).subset (hm _ (le_max_left _ _))

theorem etob_stab_totalOrder [Finite P] (hterm : ECTermination r.F (ecHist r)) {k : ℕ}
    (hag : ECAgreementFrom (ecHist r) k) :
    ∃ τ, ETOBStability r.F (tobHist r) τ ∧ ETOBTotalOrder r.F (tobHist r) τ := by
  obtain ⟨τ, hτ⟩ := exists_stab_time hwf hint hterm k
  refine ⟨τ, fun p hp t₁ t₂ h₁ h₂ => ?_, fun p q hp hq t ht m₁ m₂ hm₁ hm₂ hb => ?_⟩
  · obtain ⟨a, ta, hka, hca, hra⟩ := d_eq_resp hwf hint (hτ p hp t₁ h₁)
    obtain ⟨b, tb, -, hcb, hrb⟩ := d_eq_resp hwf hint (hτ p hp t₂ (le_trans h₁ h₂))
    have hab : a ≤ b := by have := cnt_mono (r := r) p h₂; omega
    exact resp_prefix hwf hint hval hag hka hab hra hrb
  · obtain ⟨a, ta, hka, -, hra⟩ := d_eq_resp hwf hint (hτ p hp t ht)
    obtain ⟨b, tb, hkb, -, hrb⟩ := d_eq_resp hwf hint (hτ q hq t ht)
    rcases le_total a b with hab | hab
    · exact hb.of_prefix (resp_prefix hwf hint hval hag hka hab hra hrb)
    · exact hb.of_prefix_of_mem (resp_prefix hwf hint hval hag hkb hab hrb hra)
        (resp_nodup hwf hint hval _ _ _ _ hra) hm₁ hm₂

end Correctness

/-- **Theorem 1 of [DGKPS15], direction EC → ETOB.** In every admissible run of the
transformation `T_{EC→ETOB}` whose EC black box is well-formed (it responds to an instance only
after `p` invoked it, and at most once) and satisfies EC whenever it is used properly, the
transformation implements ETOB.

The well-formedness hypothesis `ECIntegrity` (unconditional) is needed: with only
`RespAfterInv`, a black box answering instance `0` twice makes the usage improper, and then it is
unconstrained (see `differencies.md`). The ETOB usage assumption (distinct broadcasts) is not
needed. -/
theorem etob_of_ec [Finite P] {r : Run P R (Input M)} (hA : (alg (R := R)).Admissible r)
    (hwf : (ecHist r).RespAfterInv) (hint : ECIntegrity (ecHist r))
    (hbb : (ecHist r).ProperUse → EC r.F (ecHist r)) : ETOB r.F (tobHist r) := by
  obtain ⟨hterm, -, hval, k, hag⟩ := hbb (ecHist_properUse hwf hint)
  exact ⟨tobValidity hwf hint hval hA hterm, tobNoCreation hwf hint hval,
    tobNoDup hwf hint hval, tobAgreement hwf hint hval hterm hag,
    etob_stab_totalOrder hwf hint hval hterm hag⟩

end Podc.WeakestFDEventualConsistency.ECtoETOB
