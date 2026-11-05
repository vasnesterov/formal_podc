import Papers.PODC2012.LeaderElectionSpaceLB.Model

/-!
# Non-vacuity of the hypotheses of the space lower bound

The space lower bound (Theorem 5.1 of Giakkoupis–Woelfel, PODC 2012) assumes an algorithm that
is a leader election (`Alg.IsLeaderElection`) and nondeterministically solo-terminating
(`Alg.SoloTerminating`). Here we show that these hypotheses are satisfiable for **every** finite
set of processes `P`, by a deterministic obstruction-free algorithm `racing P` using one
single-writer register per process (`Reg = P`, values `ℕ`, initial value `0`).

## The algorithm ("racing counters, lose if someone is ahead")

Process `p` keeps a counter `c`, initially `1`. One iteration:

1. write `R_p := c`;
2. read the registers `R_q` of all other processes `q ≠ p`, one by one (in a fixed order);
   as soon as a value `o > c` is read, return `False` (lose);
3. if every value `o` read in this iteration satisfies `o + 2 ≤ c`, return `True` (win);
   otherwise set `c := c + 1` and start the next iteration.

The local state (`St`) records the identity of the process, its phase, the counter `c`, the
processes still to be read in the current iteration (`rem`) and the maximum `mx` of the values
read so far in the current iteration.

## Proof idea

* Per-process invariants (`Inv`): `R_q + 1 = c_q` in the write phase and `R_q = c_q` otherwise;
  a winner has `mx + 2 ≤ c`; a loser `p` has some `q` with `c_p < c_q`.
* Pairwise invariant (`Jst p q`): if `p` has read `q` in its current iteration (or won) and
  `mx_p + 2 ≤ c_p`, then `c_q ≤ mx_p + 1`, and if `c_q = mx_p + 1` then `q` is in its write phase,
  or has not yet read `p` in its current iteration, or has lost. (After `p`'s read, `q` writes at
  most once more, and then reads `R_p = c_p > c_q` and loses.) Two winners would give
  `c_q < c_p < c_q`.
* If all processes of `S` returned, the one with the largest counter cannot have lost (a loser is
  overtaken by some process with a larger counter, which must have taken steps, hence is in `S`).
* Solo termination: in a solo run the other registers stay constant, so the counter cannot grow
  beyond their maximum `+ 2`.
-/

namespace Podc.LeaderElectionSpaceLB.Racing

open Function

/-- Phase of a process of the racing algorithm. -/
inductive Ph where
  /-- About to write its counter. -/
  | write
  /-- Reading the registers of the other processes. -/
  | read
  /-- Returned (`true` = won). -/
  | done (win : Bool)
  deriving DecidableEq

/-- Local state of a process of the racing algorithm. -/
structure St (P : Type*) where
  /-- The identity of the process. -/
  me : P
  /-- The phase. -/
  ph : Ph
  /-- The counter. -/
  c : ℕ
  /-- The processes still to be read in the current iteration. -/
  rem : List P
  /-- The maximum value read so far in the current iteration. -/
  mx : ℕ

variable {P : Type*}

/-- The state reached when `rem` remains to be read with maximum `mx` read so far: read the next
register, or (nothing left) win if `mx + 2 ≤ c` and otherwise start the next iteration. -/
def cont (p : P) (c : ℕ) (rem : List P) (mx : ℕ) : St P :=
  match rem with
  | [] => if mx + 2 ≤ c then ⟨p, .done true, c, [], mx⟩ else ⟨p, .write, c + 1, [], 0⟩
  | _ :: _ => ⟨p, .read, c, rem, mx⟩

/-- The next action. -/
def act (s : St P) : Act P ℕ :=
  match s.ph with
  | .write => .write s.me s.c
  | .read => .read (s.rem.headD s.me)
  | .done b => .done b

/-- The state after reading the value `v`: lose if `v > c`, otherwise continue. -/
def rdNext (s : St P) (v : ℕ) : St P :=
  if s.c < v then { s with ph := .done false } else cont s.me s.c s.rem.tail (max s.mx v)

theorem cont_cases (p : P) (c : ℕ) (rem : List P) (mx : ℕ) :
    (rem ≠ [] ∧ cont p c rem mx = ⟨p, .read, c, rem, mx⟩) ∨
    (rem = [] ∧ mx + 2 ≤ c ∧ cont p c rem mx = ⟨p, .done true, c, [], mx⟩) ∨
    (rem = [] ∧ ¬ mx + 2 ≤ c ∧ cont p c rem mx = ⟨p, .write, c + 1, [], 0⟩) := by
  cases rem with
  | nil => by_cases h : mx + 2 ≤ c <;> simp [cont, h]
  | cons a l => simp [cont]

theorem act_eq_done {s : St P} {b : Bool} : act s = .done b ↔ s.ph = .done b := by
  unfold act; split <;> simp_all

variable [Fintype P] [DecidableEq P]

/-- All processes other than `p`, in a fixed order. -/
noncomputable def others (p : P) : List P := (Finset.univ.erase p).toList

/-- The state after writing the counter: start reading the other processes. -/
noncomputable def wrNext (s : St P) : St P := cont s.me s.c (others s.me) 0

variable (P) in
/-- The racing-counters leader election algorithm (deterministic, one single-writer register
per process). -/
noncomputable def racing : Alg P P ℕ (St P) where
  init p := {⟨p, .write, 1, [], 0⟩}
  init_nonempty _ := Set.singleton_nonempty _
  v₀ _ := 0
  act := act
  readNext s v := {rdNext s v}
  writeNext s := {wrNext s}

/-- Configurations of the racing algorithm. -/
abbrev Cfg (P : Type*) := Config P P ℕ (St P)

theorem mem_others {p q : P} : q ∈ others p ↔ q ≠ p := by simp [others]

theorem enabled_iff {C : Cfg P} {p : P} {l : St P} :
    (racing P).Enabled C (p, l) ↔
      ((C.loc p).ph = .write ∧ l = wrNext (C.loc p)) ∨
      ((C.loc p).ph = .read ∧ l = rdNext (C.loc p) (C.val ((C.loc p).rem.headD (C.loc p).me))) := by
  simp only [Alg.Enabled, racing]
  rcases h : (C.loc p).ph with _ | _ | b <;> simp [act, h]

theorem apply_write {C : Cfg P} {p : P} {l : St P} (h : (C.loc p).ph = .write) :
    (racing P).apply C (p, l) = ⟨update C.loc p l, update C.val (C.loc p).me (C.loc p).c,
      update C.wr (C.loc p).me (some p)⟩ := by
  simp [Alg.apply, racing, act, h]

theorem apply_read {C : Cfg P} {p : P} {l : St P} (h : (C.loc p).ph = .read) :
    (racing P).apply C (p, l) = { C with loc := update C.loc p l } := by
  simp [Alg.apply, racing, act, h]

theorem apply_loc_ne {C : Cfg P} {e : P × St P} {q : P} (h : e.1 ≠ q) :
    ((racing P).apply C e).loc q = C.loc q := by
  unfold Alg.apply; split <;> simp [update_of_ne h.symm]


/-! ### Invariants -/

/-- The pairwise invariant: if `p` has read `q` in its current iteration (or has won) and
`mx_p + 2 ≤ c_p`, then `c_q ≤ mx_p + 1`, and if equality holds then `q` has not read `p` yet in
its current iteration (or is in its write phase, or has lost). -/
def Jst (p q : P) (sp sq : St P) : Prop :=
  ((sp.ph = .read ∧ q ∉ sp.rem) ∨ sp.ph = .done true) → sp.mx + 2 ≤ sp.c →
    sq.c ≤ sp.mx + 1 ∧
      (sq.c = sp.mx + 1 → sq.ph = .write ∨ (sq.ph = .read ∧ p ∈ sq.rem) ∨ sq.ph = .done false)

theorem Jst_wr_left {p q : P} {sq : St P} (c : ℕ) (hpq : p ≠ q) :
    Jst p q (cont p c (others p) 0) sq := by
  have hq : q ∈ others p := mem_others.2 (Ne.symm hpq)
  rcases cont_cases p c (others p) 0 with ⟨_, h⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [h]; intro h1; simp at h1; exact absurd hq h1
  · rw [h0] at hq; simp at hq
  · rw [h0] at hq; simp at hq

omit [Fintype P] in
theorem Jst_rd_left {p q h : P} {t : List P} {sp sq : St P} {v : ℕ} (hJ : Jst p q sp sq)
    (hph : sp.ph = .read) (hrem : sp.rem = h :: t)
    (hq : h = q → sq.c ≤ v + 1 ∧ (sq.c = v + 1 → sq.ph = .write)) :
    Jst p q (rdNext sp v) sq := by
  unfold rdNext
  split_ifs with hv
  · intro H; simp at H
  · rw [hrem, List.tail_cons]
    have key : q ∉ t → max sp.mx v + 2 ≤ sp.c → sq.c ≤ max sp.mx v + 1 ∧
        (sq.c = max sp.mx v + 1 →
          sq.ph = .write ∨ (sq.ph = .read ∧ p ∈ sq.rem) ∨ sq.ph = .done false) := by
      intro hqt hmx
      by_cases hqh : h = q
      · obtain ⟨h1, h2⟩ := hq hqh
        refine ⟨by omega, fun h3 => Or.inl (h2 (by omega))⟩
      · obtain ⟨h1, h2⟩ := hJ (Or.inl ⟨hph, by rw [hrem]; simp [Ne.symm hqh, hqt]⟩) (by omega)
        exact ⟨by omega, fun h3 => h2 (by omega)⟩
    rcases cont_cases sp.me sp.c t (max sp.mx v) with ⟨_, e⟩ | ⟨ht, _, e⟩ | ⟨_, _, e⟩ <;>
      rw [e] <;> intro H hmx <;> simp only at H hmx ⊢
    · simp at H; exact key H hmx
    · subst ht; exact key (by simp) hmx
    · simp at H

theorem Jst_wr_right {p q : P} {sp sq : St P} (hpq : p ≠ q)
    (hJ : Jst p q sp sq) : Jst p q sp (cont q sq.c (others q) 0) := by
  have hp : p ∈ others q := mem_others.2 hpq
  rcases cont_cases q sq.c (others q) 0 with ⟨_, e⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · rw [e]; intro H hmx
    exact ⟨(hJ H hmx).1, fun _ => Or.inr (Or.inl ⟨rfl, hp⟩)⟩
  · rw [h0] at hp; simp at hp
  · rw [h0] at hp; simp at hp

omit [Fintype P] in
theorem Jst_rd_right {p q h : P} {t : List P} {sp sq : St P} {v : ℕ} (hJ : Jst p q sp sq)
    (hph : sq.ph = .read) (hrem : sq.rem = h :: t)
    (hp : h = p → ((sp.ph = .read ∧ q ∉ sp.rem) ∨ sp.ph = .done true) → v = sp.c) :
    Jst p q sp (rdNext sq v) := by
  intro H hmx
  obtain ⟨h1, h2⟩ := hJ H hmx
  unfold rdNext
  split_ifs with hv
  · exact ⟨h1, fun _ => Or.inr (Or.inr rfl)⟩
  · rw [hrem, List.tail_cons]
    -- if `q`'s counter equals `mx_p + 1`, then `p` is still to be read, and not next
    have hne : sq.c = sp.mx + 1 → p ∈ t := by
      intro h3
      rcases h2 h3 with h4 | ⟨-, h4⟩ | h4
      · rw [hph] at h4; cases h4
      · rw [hrem] at h4
        rcases List.mem_cons.1 h4 with h5 | h5
        · have := hp h5.symm H; omega
        · exact h5
      · rw [hph] at h4; cases h4
    rcases cont_cases sq.me sq.c t (max sq.mx v) with ⟨_, e⟩ | ⟨ht, _, e⟩ | ⟨ht, _, e⟩ <;>
      rw [e] <;> simp only
    · exact ⟨h1, fun h3 => Or.inr (Or.inl ⟨trivial, hne h3⟩)⟩
    · subst ht
      exact ⟨h1, fun h3 => absurd (hne h3) (by simp)⟩
    · subst ht
      refine ⟨?_, fun _ => Or.inl trivial⟩
      by_contra h6
      exact absurd (hne (by omega)) (by simp)

/-- The invariants of the racing algorithm. -/
structure Inv (C : Cfg P) : Prop where
  me : ∀ q, (C.loc q).me = q
  pos : ∀ q, 1 ≤ (C.loc q).c
  wr : ∀ q, (C.loc q).ph = .write → C.val q + 1 = (C.loc q).c
  nwr : ∀ q, (C.loc q).ph ≠ .write → C.val q = (C.loc q).c
  rem : ∀ q, (C.loc q).ph = .read → (C.loc q).rem ≠ []
  won : ∀ q, (C.loc q).ph = .done true → (C.loc q).mx + 2 ≤ (C.loc q).c
  lost : ∀ q, (C.loc q).ph = .done false → ∃ r, (C.loc q).c < (C.loc r).c
  pair : ∀ p q, p ≠ q → Jst p q (C.loc p) (C.loc q)


/-- What a single step of process `r` does. -/
theorem step_facts {C : Cfg P} {r : P} {l : St P} (hI : Inv C)
    (hE : (racing P).Enabled C (r, l)) :
    ((racing P).apply C (r, l)).loc = update C.loc r l ∧
    (∀ q, q ≠ r → ((racing P).apply C (r, l)).val q = C.val q) ∧
    ((racing P).apply C (r, l)).val r = (C.loc r).c ∧
    l.me = r ∧ (C.loc r).c ≤ l.c ∧ (l.ph = .write → l.c = (C.loc r).c + 1) ∧
    (l.ph ≠ .write → l.c = (C.loc r).c) ∧ (l.ph = .read → l.rem ≠ []) ∧
    (l.ph = .done true → l.mx + 2 ≤ l.c) ∧ (l.ph = .done false → ∃ h, (C.loc r).c < C.val h) := by
  have hme := hI.me r
  rcases enabled_iff.1 hE with ⟨hw, rfl⟩ | ⟨hr, rfl⟩
  · rw [apply_write hw]
    simp only [hme]
    refine ⟨trivial, fun q hq => update_of_ne hq _ _, update_self .., ?_⟩
    unfold wrNext; rw [hme]
    rcases cont_cases r (C.loc r).c (others r) 0 with ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;>
      rw [e] <;> simp_all
  · rw [apply_read hr]
    obtain ⟨h, t, hrem⟩ := List.exists_cons_of_ne_nil (hI.rem r hr)
    refine ⟨rfl, fun _ _ => rfl, hI.nwr r (by simp [hr]), ?_⟩
    have hv0 : (C.loc r).rem.headD (C.loc r).me = h := by rw [hrem]; rfl
    rw [hv0]; unfold rdNext; rw [hrem, List.tail_cons, hme]
    by_cases hv : (C.loc r).c < C.val h
    · rw [ite_eq_left hv]
      simp only [Ne, reduceCtorEq, not_false_eq_true, true_implies, le_refl, true_and,
        IsEmpty.forall_iff, implies_true, Ph.done.injEq, Bool.false_eq_true]
      exact ⟨h, hv⟩
    · rw [ite_eq_right hv]
      rcases cont_cases r (C.loc r).c t (max (C.loc r).mx (C.val h)) with
        ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, e⟩ <;> rw [e] <;> simp_all

theorem Inv.apply {C : Cfg P} {r : P} {l : St P} (hI : Inv C)
    (hE : (racing P).Enabled C (r, l)) : Inv ((racing P).apply C (r, l)) := by
  obtain ⟨hloc, hval, hvr, hme, hc, hw, hnw, hrem, hwon, hlost⟩ := step_facts hI hE
  set C' := (racing P).apply C (r, l)
  have hloc' : ∀ q, C'.loc q = if q = r then l else C.loc q := by
    intro q; rw [hloc, update_apply]
  have mono : ∀ q, (C.loc q).c ≤ (C'.loc q).c := by
    intro q; rw [hloc']; split_ifs with h
    · subst h; exact hc
    · exact le_rfl
  constructor
  · intro q; rw [hloc']; split_ifs with h
    · subst h; exact hme
    · exact hI.me q
  · intro q; rw [hloc']; split_ifs with h
    · subst h; exact (hI.pos q).trans hc
    · exact hI.pos q
  · intro q; rw [hloc']; split_ifs with h
    · subst h; rw [hvr]; intro h'; rw [hw h']
    · rw [hval q h]; exact hI.wr q
  · intro q; rw [hloc']; split_ifs with h
    · subst h; rw [hvr]; intro h'; rw [hnw h']
    · rw [hval q h]; exact hI.nwr q
  · intro q; rw [hloc']; split_ifs with h
    · exact hrem
    · exact hI.rem q
  · intro q; rw [hloc']; split_ifs with h
    · exact hwon
    · exact hI.won q
  · intro q; rw [hloc']; split_ifs with h
    · subst h
      intro h'
      obtain ⟨x, hx⟩ := hlost h'
      refine ⟨x, ?_⟩
      have h1 := mono x
      have h2 : C.val x ≤ (C.loc x).c := by
        by_cases hx' : (C.loc x).ph = .write
        · have := hI.wr x hx'; omega
        · exact (hI.nwr x hx').le
      by_cases hc' : l.ph = .write
      · rw [hc'] at h'; cases h'
      · rw [hnw hc']; omega
    · intro h'
      obtain ⟨x, hx⟩ := hI.lost q h'
      exact ⟨x, hx.trans_le (mono x)⟩
  · intro p q hpq
    have hme' := hI.me r
    rcases enabled_iff.1 hE with ⟨hw', hl⟩ | ⟨hr', hl⟩
    · by_cases hp : p = r
      · subst hp
        rw [hloc' p, hloc' q, ite_eq_left rfl, ite_eq_right (Ne.symm hpq), hl]
        unfold wrNext; rw [hme']
        exact Jst_wr_left _ hpq
      · by_cases hq : q = r
        · subst hq
          rw [hloc' p, hloc' q, ite_eq_left rfl, ite_eq_right hp, hl]
          unfold wrNext; rw [hme']
          exact Jst_wr_right hpq (hI.pair p q hpq)
        · rw [hloc' p, hloc' q, ite_eq_right hp, ite_eq_right hq]
          exact hI.pair p q hpq
    · obtain ⟨h, t, hrem⟩ := List.exists_cons_of_ne_nil (hI.rem r hr')
      rw [hrem, List.headD_cons] at hl
      by_cases hp : p = r
      · subst hp
        rw [hloc' p, hloc' q, ite_eq_left rfl, ite_eq_right (Ne.symm hpq), hl]
        refine Jst_rd_left (hI.pair p q hpq) hr' hrem ?_
        rintro rfl
        by_cases hx : (C.loc h).ph = .write
        · have := hI.wr h hx
          exact ⟨by omega, fun _ => hx⟩
        · have := hI.nwr h hx
          exact ⟨by omega, fun _ => by omega⟩
      · by_cases hq : q = r
        · subst hq
          rw [hloc' p, hloc' q, ite_eq_left rfl, ite_eq_right hp, hl]
          refine Jst_rd_right (hI.pair p q hpq) hr' hrem ?_
          rintro rfl H
          apply hI.nwr
          rcases H with ⟨H, -⟩ | H <;> rw [H] <;> simp
        · rw [hloc' p, hloc' q, ite_eq_right hp, ite_eq_right hq]
          exact hI.pair p q hpq

theorem Inv.init {C : Cfg P} (h : (racing P).IsInit C) : Inv C := by
  obtain ⟨hl, hv, -⟩ := h
  have hl' : ∀ q, C.loc q = ⟨q, .write, 1, [], 0⟩ := fun q => hl q
  have hv' : ∀ q, C.val q = 0 := fun q => hv q
  constructor <;> intro q <;> simp [hl', hv', Jst]

theorem Inv.run {C : Cfg P} (hI : Inv C) :
    ∀ {es : List (P × St P)}, (racing P).Valid C es → Inv ((racing P).run C es) := by
  intro es
  induction es generalizing C with
  | nil => intro _; exact hI
  | cons e es ih =>
    intro hV
    exact ih (hI.apply (r := e.1) (l := e.2) hV.1) hV.2

theorem Inv.of_reachable {C : Cfg P} (h : (racing P).Reachable C) : Inv C := by
  obtain ⟨C₀, es, h0, hV, rfl⟩ := h
  exact (Inv.init h0).run hV


/-! ### Safety -/

theorem won_iff {C : Cfg P} {p : P} : (racing P).Won C p ↔ (C.loc p).ph = .done true :=
  act_eq_done

theorem finished_iff {C : Cfg P} {p : P} :
    (racing P).Finished C p ↔ ∃ b, (C.loc p).ph = .done b :=
  exists_congr fun _ => act_eq_done

/-- A process that takes no step keeps its local state. -/
theorem loc_run_of_forall_ne {C : Cfg P} {q : P} :
    ∀ {es : List (P × St P)}, (∀ e ∈ es, e.1 ≠ q) → ((racing P).run C es).loc q = C.loc q := by
  intro es
  induction es generalizing C with
  | nil => intro _; rfl
  | cons e es ih =>
    intro h
    show ((racing P).run ((racing P).apply C e) es).loc q = _
    rw [ih (fun e' he' => h e' (List.mem_cons_of_mem _ he')), apply_loc_ne (h e (by simp))]

/-- The racing algorithm is a leader election algorithm (for every number of processes). -/
theorem racing_isLeaderElection : (racing P).IsLeaderElection := by
  intro C₀ es h0 hV S hS
  have hI := (Inv.init h0).run hV
  set C := (racing P).run C₀ es
  refine ⟨fun p _ q _ hp hq => ?_, fun hne hfin => ?_⟩
  · by_contra hpq
    rw [won_iff] at hp hq
    have h1 := hI.pair p q hpq (Or.inr hp) (hI.won p hp)
    have h2 := hI.pair q p (Ne.symm hpq) (Or.inr hq) (hI.won q hq)
    have := hI.won p hp
    have := hI.won q hq
    omega
  · classical
    obtain ⟨p0, hp0⟩ := hne
    obtain ⟨p, hpS, hmax⟩ := Finset.exists_max_image (Finset.univ.filter (· ∈ S))
      (fun q => (C.loc q).c) ⟨p0, by simp [hp0]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hpS hmax
    obtain ⟨b, hb⟩ := finished_iff.1 (hfin p hpS)
    cases b
    · exfalso
      obtain ⟨q, hq⟩ := hI.lost p hb
      by_cases hqS : q ∈ S
      · exact absurd (hmax q hqS) (by omega)
      · have hloc : C.loc q = C₀.loc q :=
          loc_run_of_forall_ne (fun e he h' => hqS (h' ▸ hS e he))
        have h0q : C₀.loc q = ⟨q, .write, 1, [], 0⟩ := h0.1 q
        have := hI.pos p
        rw [hloc, h0q] at hq
        simp only at hq
        omega
    · exact ⟨p, hpS, won_iff.2 hb⟩

/-! ### Solo termination -/

theorem valid_append {C : Cfg P} {es es' : List (P × St P)} :
    (racing P).Valid C (es ++ es') ↔
      (racing P).Valid C es ∧ (racing P).Valid ((racing P).run C es) es' := by
  induction es generalizing C with
  | nil => simp [Alg.Valid, Alg.run]
  | cons e es ih =>
    simp only [List.cons_append, Alg.Valid, ih, and_assoc]
    exact Iff.rfl

theorem run_append {C : Cfg P} {es es' : List (P × St P)} :
    (racing P).run C (es ++ es') = (racing P).run ((racing P).run C es) es' := by
  simp [Alg.run, List.foldl_append]

/-- Completing a read phase solo: the process returns, or starts the next iteration with counter
`c + 1`, in which case some value seen (or `mx`) was `> c - 2`. Registers are not changed. -/
theorem rd_solo (p : P) (c : ℕ) : ∀ (rem : List P) (mx : ℕ) (C : Cfg P),
    C.loc p = cont p c rem mx →
    ∃ es : List (P × St P), (∀ e ∈ es, e.1 = p) ∧ (racing P).Valid C es ∧
      ((racing P).run C es).val = C.val ∧
      ((∃ b, (((racing P).run C es).loc p).ph = .done b) ∨
        (((racing P).run C es).loc p = ⟨p, .write, c + 1, [], 0⟩ ∧
          (c < mx + 2 ∨ ∃ q ∈ rem, c < C.val q + 2))) := by
  intro rem
  induction rem with
  | nil =>
    intro mx C hC
    refine ⟨[], by simp, trivial, rfl, ?_⟩
    simp only [Alg.run, List.foldl_nil]
    by_cases h : mx + 2 ≤ c
    · left; exact ⟨true, by rw [hC]; simp [cont, h]⟩
    · right; exact ⟨by rw [hC]; simp [cont, h], Or.inl (by omega)⟩
  | cons q rest ih =>
    intro mx C hC
    have hph : (C.loc p).ph = .read := by rw [hC]; rfl
    set l := rdNext (C.loc p) (C.val q) with hl
    have hE : (racing P).Enabled C (p, l) := by
      rw [enabled_iff]; right; refine ⟨hph, ?_⟩; rw [hl, hC]; rfl
    set C1 := (racing P).apply C (p, l)
    have hC1 : C1 = { C with loc := update C.loc p l } := apply_read hph
    have hl' : l = if c < C.val q then ⟨p, .done false, c, q :: rest, mx⟩
        else cont p c rest (max mx (C.val q)) := by rw [hl, hC]; rfl
    have hval : C1.val = C.val := by rw [hC1]
    by_cases hv : c < C.val q
    · refine ⟨[(p, l)], by simp, ⟨hE, trivial⟩, hval, Or.inl ⟨false, ?_⟩⟩
      show (C1.loc p).ph = _
      rw [hC1]; simp [hl', hv]
    · obtain ⟨es, h1, h2, h3, h4⟩ := ih (max mx (C.val q)) C1 (by rw [hC1]; simp [hl', hv])
      refine ⟨(p, l) :: es, ?_, ⟨hE, h2⟩, ?_, ?_⟩
      · intro e he
        rcases List.mem_cons.1 he with rfl | he
        · rfl
        · exact h1 e he
      · show ((racing P).run C1 es).val = _
        rw [h3, hval]
      · rcases h4 with h4 | ⟨h4, h5⟩
        · exact Or.inl h4
        · refine Or.inr ⟨h4, ?_⟩
          rw [hval] at h5
          rcases h5 with h5 | ⟨q', hq', h5⟩
          · by_cases h6 : c < mx + 2
            · exact Or.inl h6
            · exact Or.inr ⟨q, by simp, by omega⟩
          · exact Or.inr ⟨q', by simp [hq'], h5⟩

/-- From a write phase, a solo run returns: the other registers stay `≤ B`, so the counter
cannot exceed `B + 2`. -/
theorem wr_solo (p : P) (B : ℕ) : ∀ n (C : Cfg P), B + 2 - (C.loc p).c = n →
    (C.loc p).me = p → (C.loc p).ph = .write → (∀ q, q ≠ p → C.val q ≤ B) →
    ∃ es : List (P × St P), (∀ e ∈ es, e.1 = p) ∧ (racing P).Valid C es ∧
      (racing P).Finished ((racing P).run C es) p := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro C hn hme hph hB
  set c := (C.loc p).c with hc
  set l := wrNext (C.loc p) with hl
  have hE : (racing P).Enabled C (p, l) := enabled_iff.2 (Or.inl ⟨hph, rfl⟩)
  set C1 := (racing P).apply C (p, l)
  have hC1 : C1 = ⟨update C.loc p l, update C.val (C.loc p).me c,
      update C.wr (C.loc p).me (some p)⟩ := apply_write hph
  have hloc1 : C1.loc p = cont p c (others p) 0 := by rw [hC1]; simp [hl, wrNext, hme, c]
  have hval1 : ∀ q, q ≠ p → C1.val q = C.val q := by intro q hq; rw [hC1]; simp [hme, hq]
  obtain ⟨es, h1, h2, h3, h4⟩ := rd_solo p c (others p) 0 C1 hloc1
  have hmem : ∀ e ∈ (p, l) :: es, e.1 = p := by
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact h1 e he
  rcases h4 with ⟨b, hb⟩ | ⟨h4, h5⟩
  · exact ⟨(p, l) :: es, hmem, ⟨hE, h2⟩, finished_iff.2 ⟨b, hb⟩⟩
  · have hcB : c < B + 2 := by
      rcases h5 with h5 | ⟨q, hq, h5⟩
      · omega
      · have := hB q (mem_others.1 hq); rw [hval1 q (mem_others.1 hq)] at h5; omega
    set C2 := (racing P).run C1 es
    obtain ⟨es', h1', h2', h3'⟩ := ih (B + 2 - (c + 1)) (by omega) C2 (by rw [h4])
      (by rw [h4]) (by rw [h4])
      (by intro q hq; rw [h3, hval1 q hq]; exact hB q hq)
    refine ⟨((p, l) :: es) ++ es', ?_, valid_append.2 ⟨⟨hE, h2⟩, h2'⟩, ?_⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact hmem e he
      · exact h1' e he
    · rw [run_append]; exact h3'

/-- The racing algorithm is (nondeterministically) solo-terminating. -/
theorem racing_soloTerminating : (racing P).SoloTerminating := by
  intro C hR p
  have hI := Inv.of_reachable hR
  have hB : ∀ q, q ≠ p → C.val q ≤ Finset.univ.sup C.val :=
    fun q _ => Finset.le_sup (Finset.mem_univ q)
  rcases hph : (C.loc p).ph with _ | _ | b
  · exact wr_solo p _ _ C rfl (hI.me p) hph hB
  · obtain ⟨h, t, hrem⟩ := List.exists_cons_of_ne_nil (hI.rem p hph)
    have hC : C.loc p = cont p (C.loc p).c (h :: t) (C.loc p).mx := by
      have := hI.me p
      cases hs : C.loc p
      simp_all [cont]
    obtain ⟨es, h1, h2, h3, h4⟩ := rd_solo p _ _ _ C hC
    rcases h4 with ⟨b, hb⟩ | ⟨h4, -⟩
    · exact ⟨es, h1, h2, finished_iff.2 ⟨b, hb⟩⟩
    · obtain ⟨es', h1', h2', h3'⟩ := wr_solo p (Finset.univ.sup C.val) _ _ rfl (by rw [h4])
        (by rw [h4]) (by intro q hq; rw [h3]; exact hB q hq)
      refine ⟨es ++ es', ?_, valid_append.2 ⟨h2, h2'⟩, by rw [run_append]; exact h3'⟩
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact h1 e he
      · exact h1' e he
  · exact ⟨[], by simp, trivial, finished_iff.2 ⟨b, hph⟩⟩

end Podc.LeaderElectionSpaceLB.Racing
