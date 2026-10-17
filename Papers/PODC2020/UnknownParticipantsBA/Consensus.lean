import Papers.PODC2020.UnknownParticipantsBA.Layer
import Cslib.Computability.Distributed.Byzantine.KingPhase

/-!
# Consensus in the id-only model (Section 5 of the BA, Algorithm 3 / Section VII of the full version)

The BA announces: "we use the rotor-coordinator's opinion as the king's opinion and the thresholds
`n − f` and `n − 2f` are replaced by `2n_v/3` and `n_v/3`; this results in an `O(n)` round
consensus algorithm"; the full version gives Algorithm 3 and claims `O(f)` rounds.

We verify the following phase-king algorithm (a repaired Algorithm 3, see `differencies.md`):
the candidate-set layer runs in every round; phase `k ≥ 0` takes 3 rounds (steps `3k+2`, `3k+3`,
`3k+4`; the inputs of phase `k` are broadcast at the end of step `3k+1`):

```
end of step 3k+1 : broadcast input(x_v)
step 3k+2        : if received ≥ 2n_v/3 input(x_v): broadcast prefer(x_v)
step 3k+3        : if received ≥ n_v/3 prefer(y): x_v ← y
                   if received ≥ 2n_v/3 prefer(x_v): broadcast strongprefer(x_v)
                   coordinator c_k ← C_v[k mod |C_v|]; if v = c_k: broadcast opinion(x_v)
step 3k+4        : if received ≥ 2n_v/3 strongprefer(x_v) and not decided: decide x_v
                   if received < n_v/3 strongprefer(x_v): x_v ← opinion received from c_k (if any)
                   broadcast input(x_v)                                 (phase k+1)
```

A node that has decided keeps participating (it never halts); `dec` records the (first) decision.
-/

namespace UnknownBA

/-- Application messages of the consensus algorithm. -/
inductive CMsg (X : Type*) where
  | input (x : X) : CMsg X
  | prefer (x : X) : CMsg X
  | strong (x : X) : CMsg X
  | opinion (x : X) : CMsg X
  deriving DecidableEq

def CMsg.prefVal {X : Type*} : CMsg X → Option X
  | .prefer y => some y
  | _ => none

def CMsg.opVal {X : Type*} : CMsg X → Option X
  | .opinion y => some y
  | _ => none

variable {I X : Type*} [DecidableEq I] [LinearOrder I] [LinearOrder X]

/-- Values `y` with `(q, app a) ∈ B`, `f a = some y`. -/
def vals (f : CMsg X → Option X) (B : Finset (I × Msg I (CMsg X))) : Finset X :=
  B.biUnion fun e => (e.2.appVal.bind f).toFinset

omit [DecidableEq I] [LinearOrder I] in
lemma mem_vals {f : CMsg X → Option X} {B : Finset (I × Msg I (CMsg X))} {y : X} :
    y ∈ vals f B ↔ ∃ q a, (q, Msg.app a) ∈ B ∧ f a = some y := by
  simp only [vals, Finset.mem_biUnion, Option.mem_toFinset]
  constructor
  · rintro ⟨⟨q, m⟩, hm, h⟩
    cases m with
    | app a => exact ⟨q, a, hm, h⟩
    | _ => simp [Msg.appVal] at h
  · rintro ⟨q, a, hm, h⟩
    exact ⟨_, hm, by simp [Msg.appVal, h]⟩

/-- Values sent by senders in `P`. -/
def valsFrom (P : Finset I) (f : CMsg X → Option X) (B : Finset (I × Msg I (CMsg X))) :
    Finset X := vals f (B.filter fun e => e.1 ∈ P)

omit [LinearOrder I] in
lemma mem_valsFrom {P : Finset I} {f : CMsg X → Option X} {B : Finset (I × Msg I (CMsg X))}
    {y : X} : y ∈ valsFrom P f B ↔ ∃ q ∈ P, ∃ a, (q, Msg.app a) ∈ B ∧ f a = some y := by
  rw [valsFrom, mem_vals]
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨q, a, ⟨hm, hq⟩, h⟩; exact ⟨q, hq, a, hm, h⟩
  · rintro ⟨q, hq, a, hm, h⟩; exact ⟨q, a, ⟨hm, hq⟩, h⟩

/-- A deterministic choice from a finite set (its minimum; default `d` if empty). -/
def pick (s : Finset X) (d : X) : X := if h : s.Nonempty then s.min' h else d

omit [DecidableEq I] [LinearOrder I] in
lemma pick_eq {s : Finset X} {d y : X} (hy : y ∈ s) (h : ∀ z ∈ s, z = y) : pick s d = y := by
  have hne : s.Nonempty := ⟨y, hy⟩
  simp only [pick, hne, dite_true]
  exact h _ (s.min'_mem hne)

/-- Application state of a consensus node. -/
structure CState (I X : Type*) where
  id : I
  x : X
  coord : Finset I
  dec : Option X
  out : Finset (CMsg X)

/-- Candidate values at step `3k+3`: `y` with at least `n/3` copies of `prefer(y)`. -/
def prefCands (n : ℕ) (B : Finset (I × Msg I (CMsg X))) : Finset X :=
  (vals CMsg.prefVal B).filter fun y => n ≤ 3 * cnt B (Msg.app (CMsg.prefer y))

/-- The consensus algorithm as an extension of the candidate-set layer. -/
def consExt : Ext I X (CMsg X) (CState I X) where
  init v x := ⟨v, x, ∅, none, ∅⟩
  halted _ := false
  out st := st.out
  step s c st B :=
    if s % 3 = 1 then
      { st with out := if 2 * c.heard.card ≤ 3 * cnt B (Msg.app (CMsg.input st.x))
                       then {CMsg.prefer st.x} else ∅ }
    else if s % 3 = 2 then
      { st with
        x := pick (prefCands c.heard.card B) st.x
        coord := selSet c.C (s / 3)
        out := (if 2 * c.heard.card ≤
                    3 * cnt B (Msg.app (CMsg.prefer (pick (prefCands c.heard.card B) st.x)))
                  then {CMsg.strong (pick (prefCands c.heard.card B) st.x)} else ∅) ∪
               (if st.id ∈ selSet c.C (s / 3)
                  then {CMsg.opinion (pick (prefCands c.heard.card B) st.x)} else ∅) }
    else if s = 0 then { st with out := {CMsg.input st.x} }
    else
      { st with
        dec := if st.dec = none ∧ 2 * c.heard.card ≤ 3 * cnt B (Msg.app (CMsg.strong st.x))
               then some st.x else st.dec
        x := if 3 * cnt B (Msg.app (CMsg.strong st.x)) < c.heard.card
             then pick (valsFrom st.coord CMsg.opVal B) st.x else st.x
        out := {CMsg.input (if 3 * cnt B (Msg.app (CMsg.strong st.x)) < c.heard.card
             then pick (valsFrom st.coord CMsg.opVal B) st.x else st.x)} }

/-- The consensus protocol of the id-only model. -/
def cons : Protocol I X (Msg I (CMsg X)) (St I (CState I X)) := withRotor consExt

omit [DecidableEq I] [LinearOrder I] [LinearOrder X] in
lemma ite_t {α : Type*} {c : Prop} [Decidable c] (h : c) {a b : α} :
    (if c then a else b) = a := by simp [h]

omit [DecidableEq I] [LinearOrder I] [LinearOrder X] in
lemma ite_f {α : Type*} {c : Prop} [Decidable c] (h : ¬ c) {a b : α} :
    (if c then a else b) = b := by simp [h]

/-! ### The four kinds of steps -/

section steps

variable (s : ℕ) (c : Core I) (st : CState I X) (B : Finset (I × Msg I (CMsg X)))

lemma consExt_step_id : (consExt.step s c st B).id = st.id := by
  simp only [consExt]; split_ifs <;> rfl

lemma consExt_step_zero : consExt.step 0 c st B = { st with out := {CMsg.input st.x} } := by
  simp [consExt]

lemma consExt_step_pref {k : ℕ} (hs : s = 3 * k + 1) :
    consExt.step s c st B =
      { st with out := if 2 * c.heard.card ≤ 3 * cnt B (Msg.app (CMsg.input st.x))
                       then {CMsg.prefer st.x} else ∅ } := by
  have : s % 3 = 1 := by omega
  simp [consExt, this]

lemma consExt_step_strong {k : ℕ} (hs : s = 3 * k + 2) :
    consExt.step s c st B =
      { st with
        x := pick (prefCands c.heard.card B) st.x
        coord := selSet c.C k
        out := (if 2 * c.heard.card ≤
                    3 * cnt B (Msg.app (CMsg.prefer (pick (prefCands c.heard.card B) st.x)))
                  then {CMsg.strong (pick (prefCands c.heard.card B) st.x)} else ∅) ∪
               (if st.id ∈ selSet c.C k
                  then {CMsg.opinion (pick (prefCands c.heard.card B) st.x)} else ∅) } := by
  have h1 : s % 3 = 2 := by omega
  have h2 : s / 3 = k := by omega
  simp [consExt, h1, h2]

lemma consExt_step_king {k : ℕ} (hs : s = 3 * k + 3) :
    consExt.step s c st B =
      { st with
        dec := if st.dec = none ∧ 2 * c.heard.card ≤ 3 * cnt B (Msg.app (CMsg.strong st.x))
               then some st.x else st.dec
        x := if 3 * cnt B (Msg.app (CMsg.strong st.x)) < c.heard.card
             then pick (valsFrom st.coord CMsg.opVal B) st.x else st.x
        out := {CMsg.input (if 3 * cnt B (Msg.app (CMsg.strong st.x)) < c.heard.card
             then pick (valsFrom st.coord CMsg.opVal B) st.x else st.x)} } := by
  have h1 : s % 3 = 0 := by omega
  have h2 : s ≠ 0 := by omega
  simp [consExt, h1, h2]

end steps

variable (E : Env I X (Msg I (CMsg X)))

local notation "R" => run (withRotor consExt) E
local notation "Bx" s:max v:max => inbox (withRotor consExt) E (R s) s v

lemma cons_hinit : ∀ (v : I) (x : X), (consExt (I := I)).halted (consExt.init v x) = false :=
  fun _ _ => rfl

lemma cons_alive (s : ℕ) (v : I) : Alive consExt E s v := rfl

lemma cons_ext (s : ℕ) (v : I) :
    (R (s + 1) v).ext = consExt.step s (R (s + 1) v).core (R s v).ext (Bx s v) :=
  ext_succ (cons_alive E s v)

lemma cons_id (s : ℕ) (v : I) : (R s v).ext.id = v := by
  induction s with
  | zero => rfl
  | succ s ih => rw [cons_ext, consExt_step_id, ih]

lemma mem_cons_out {s : ℕ} {q : I} {a : CMsg X} :
    Msg.app a ∈ (withRotor consExt).out (R s q) ↔ a ∈ (R s q).ext.out := by
  rw [mem_out_app]
  exact ⟨fun h => h.2, fun h => ⟨cons_alive E s q, h⟩⟩

/-- At the end of step `3k + 1` a correct node broadcasts exactly `input(x_v)`. -/
lemma cons_out_input (k : ℕ) (v : I) :
    (R (3 * k + 1) v).ext.out = {CMsg.input (R (3 * k + 1) v).ext.x} := by
  rcases k with _ | k
  · rw [cons_ext, consExt_step_zero]
  · rw [show 3 * (k + 1) + 1 = (3 * k + 3) + 1 by ring, cons_ext,
      consExt_step_king _ _ _ _ rfl]

lemma cons_pref (k : ℕ) (v : I) :
    (R (3 * k + 2) v).ext.x = (R (3 * k + 1) v).ext.x ∧
    (R (3 * k + 2) v).ext.dec = (R (3 * k + 1) v).ext.dec ∧
    (R (3 * k + 2) v).ext.out =
      if 2 * (R (3 * k + 2) v).core.heard.card ≤
          3 * cnt (Bx (3 * k + 1) v) (Msg.app (CMsg.input (R (3 * k + 1) v).ext.x))
      then {CMsg.prefer (R (3 * k + 1) v).ext.x} else ∅ := by
  rw [show 3 * k + 2 = (3 * k + 1) + 1 by ring, cons_ext, consExt_step_pref _ _ _ _ rfl]
  exact ⟨rfl, rfl, rfl⟩

lemma cons_strong (k : ℕ) (v : I) :
    let n := (R (3 * k + 3) v).core.heard.card
    let x' := pick (prefCands n (Bx (3 * k + 2) v)) (R (3 * k + 2) v).ext.x
    (R (3 * k + 3) v).ext.x = x' ∧
    (R (3 * k + 3) v).ext.coord = selSet (R (3 * k + 3) v).core.C k ∧
    (R (3 * k + 3) v).ext.dec = (R (3 * k + 2) v).ext.dec ∧
    (R (3 * k + 3) v).ext.out =
      (if 2 * n ≤ 3 * cnt (Bx (3 * k + 2) v) (Msg.app (CMsg.prefer x'))
        then {CMsg.strong x'} else ∅) ∪
      (if v ∈ selSet (R (3 * k + 3) v).core.C k then {CMsg.opinion x'} else ∅) := by
  intro n x'
  rw [show 3 * k + 3 = (3 * k + 2) + 1 by ring, cons_ext, consExt_step_strong _ _ _ _ rfl,
    cons_id]
  exact ⟨rfl, rfl, rfl, rfl⟩

lemma cons_king (k : ℕ) (v : I) :
    let n := (R (3 * k + 4) v).core.heard.card
    let st := (R (3 * k + 3) v).ext
    let cs := cnt (Bx (3 * k + 3) v) (Msg.app (CMsg.strong st.x))
    (R (3 * k + 4) v).ext.dec =
      (if st.dec = none ∧ 2 * n ≤ 3 * cs then some st.x else st.dec) ∧
    (R (3 * k + 4) v).ext.x =
      (if 3 * cs < n then pick (valsFrom st.coord CMsg.opVal (Bx (3 * k + 3) v)) st.x
        else st.x) := by
  intro n st cs
  rw [show 3 * k + 4 = (3 * k + 3) + 1 by ring, cons_ext, consExt_step_king _ _ _ _ rfl]
  exact ⟨rfl, rfl⟩

lemma cons_x_one (v : I) : (R 1 v).ext.x = E.input v := by
  rw [cons_ext, consExt_step_zero]; rfl

lemma cons_dec_zero (v : I) : (R 0 v).ext.dec = none := rfl

/-- The decision changes only in a king step, from `none` to `some x_v`. -/
lemma cons_dec_step (s : ℕ) (v : I) :
    (R (s + 1) v).ext.dec = (R s v).ext.dec ∨
      ((R s v).ext.dec = none ∧ ∃ k, s = 3 * k + 3 ∧
        (R (s + 1) v).ext.dec = some (R s v).ext.x ∧
        2 * (R (s + 1) v).core.heard.card ≤
          3 * cnt (Bx s v) (Msg.app (CMsg.strong (R s v).ext.x))) := by
  rcases Nat.lt_or_ge s 3 with hs | hs
  · interval_cases s
    · left; rw [cons_ext, consExt_step_zero]
    · left; rw [cons_ext, consExt_step_pref _ _ _ _ (k := 0) rfl]
    · left; rw [cons_ext, consExt_step_strong _ _ _ _ (k := 0) rfl]
  · obtain ⟨k, hk⟩ : ∃ k, s = 3 * k + 3 ∨ s = 3 * k + 4 ∨ s = 3 * k + 5 :=
      ⟨s / 3 - 1, by omega⟩
    rcases hk with rfl | rfl | rfl
    · have := (cons_king E k v).1
      split_ifs at this with h
      · right; exact ⟨h.1, k, rfl, this, h.2⟩
      · left; exact this
    · left; rw [cons_ext, consExt_step_pref _ _ _ _ (k := k + 1) (by ring)]
    · left; rw [cons_ext, consExt_step_strong _ _ _ _ (k := k + 1) (by ring)]

/-! ### What correct nodes send -/

lemma out_input_iff (k : ℕ) (q : I) (y : X) :
    Msg.app (CMsg.input y) ∈ (withRotor consExt).out (R (3 * k + 1) q) ↔
      y = (R (3 * k + 1) q).ext.x := by
  rw [mem_cons_out, cons_out_input]; simp

lemma out_prefer_imp {k : ℕ} {q : I} {y : X}
    (h : Msg.app (CMsg.prefer y) ∈ (withRotor consExt).out (R (3 * k + 2) q)) :
    y = (R (3 * k + 1) q).ext.x ∧
      2 * (R (3 * k + 2) q).core.heard.card ≤ 3 * cnt (Bx (3 * k + 1) q) (Msg.app (CMsg.input y)) := by
  rw [mem_cons_out, (cons_pref E k q).2.2] at h
  split_ifs at h with hc
  · simp only [Finset.mem_singleton, CMsg.prefer.injEq] at h; subst h; exact ⟨rfl, hc⟩
  · simp at h

lemma out_prefer_of {k : ℕ} {q : I}
    (hc : 2 * (R (3 * k + 2) q).core.heard.card ≤
      3 * cnt (Bx (3 * k + 1) q) (Msg.app (CMsg.input (R (3 * k + 1) q).ext.x))) :
    Msg.app (CMsg.prefer (R (3 * k + 1) q).ext.x) ∈ (withRotor consExt).out (R (3 * k + 2) q) := by
  rw [mem_cons_out, (cons_pref E k q).2.2]; simp [hc]

lemma out_strong_imp {k : ℕ} {q : I} {y : X}
    (h : Msg.app (CMsg.strong y) ∈ (withRotor consExt).out (R (3 * k + 3) q)) :
    y = (R (3 * k + 3) q).ext.x ∧
      2 * (R (3 * k + 3) q).core.heard.card ≤ 3 * cnt (Bx (3 * k + 2) q) (Msg.app (CMsg.prefer y)) := by
  have hs := cons_strong E k q
  simp only at hs
  rw [mem_cons_out, hs.2.2.2, ← hs.1] at h
  simp only [Finset.mem_union] at h
  rcases h with h | h
  · split_ifs at h with hc
    · simp only [Finset.mem_singleton, CMsg.strong.injEq] at h; subst h; exact ⟨rfl, hc⟩
    · simp at h
  · split_ifs at h <;> simp at h

lemma out_strong_of {k : ℕ} {q : I}
    (hc : 2 * (R (3 * k + 3) q).core.heard.card ≤
      3 * cnt (Bx (3 * k + 2) q) (Msg.app (CMsg.prefer (R (3 * k + 3) q).ext.x))) :
    Msg.app (CMsg.strong (R (3 * k + 3) q).ext.x) ∈ (withRotor consExt).out (R (3 * k + 3) q) := by
  have hs := cons_strong E k q
  simp only at hs
  rw [mem_cons_out, hs.2.2.2, ← hs.1]
  simp [hc]

lemma out_opinion_iff (k : ℕ) (q : I) (y : X) :
    Msg.app (CMsg.opinion y) ∈ (withRotor consExt).out (R (3 * k + 3) q) ↔
      q ∈ (R (3 * k + 3) q).ext.coord ∧ y = (R (3 * k + 3) q).ext.x := by
  have hs := cons_strong E k q
  simp only at hs
  rw [mem_cons_out, hs.2.2.2, hs.2.1, ← hs.1]
  simp only [Finset.mem_union]
  constructor
  · rintro (h | h)
    · split_ifs at h <;> simp at h
    · split_ifs at h with hc
      · simp only [Finset.mem_singleton, CMsg.opinion.injEq] at h; exact ⟨hc, h⟩
      · simp at h
  · rintro ⟨hc, rfl⟩; right; simp [hc]

/-! ### Correctness -/

variable (hres : 2 * E.F.card < E.G.card)
include hres

omit hres in
/-- Count facts at a correct receiver in step `s + 1`, with the step written as `t`. -/
lemma cons_count {s t : ℕ} (hst : t = s + 1) (v : I) (m : CMsg X) :
    ∃ k ≤ E.F.card, (R t v).core.heard.card = E.G.card + k ∧
      corr consExt E s (Msg.app m) ≤ cnt (Bx s v) (Msg.app m) ∧
      cnt (Bx s v) (Msg.app m) ≤ corr consExt E s (Msg.app m) + k := by
  subst hst; exact count_bound cons_hinit (cons_alive E _ v) _

/-- Lemma 2 in the consensus run. -/
lemma cons_lemma2 {s t : ℕ} (hst : t = s + 1) {v : I} {m : CMsg X}
    (hc : 2 * (R t v).core.heard.card ≤ 3 * cnt (Bx s v) (Msg.app m)) :
    E.G.card + E.F.card < 3 * corr consExt E s (Msg.app m) := by
  subst hst; exact lemma2 cons_hinit hres (cons_alive E _ v) hc

/-- Lemma 1 in the consensus run. -/
lemma cons_lemma1 {s t : ℕ} (hst : t = s + 1) {v : I} {m : CMsg X}
    (hc : (R t v).core.heard.card ≤ 3 * cnt (Bx s v) (Msg.app m)) :
    ∃ q ∈ E.G, Msg.app m ∈ (withRotor consExt).out (R s q) := by
  subst hst; exact lemma1 cons_hinit hres (cons_alive E _ v) hc

omit hres in
lemma cons_corr_pos {s : ℕ} {m : CMsg X} (h : 0 < corr consExt E s (Msg.app m)) :
    ∃ q ∈ E.G, Msg.app m ∈ (withRotor consExt).out (R s q) := exists_of_corr_pos h

/-- (A) If a correct node receives `2n/3` copies of `prefer(y)` in step `3k+3`, then every correct
node adopts `y` in that step. -/
lemma adopt {k : ℕ} {w : I} {y : X}
    (hc : 2 * (R (3 * k + 3) w).core.heard.card ≤
      3 * cnt (Bx (3 * k + 2) w) (Msg.app (CMsg.prefer y)))
    {u : I} : (R (3 * k + 3) u).ext.x = y := by
  have hbig := cons_lemma2 E hres rfl hc
  obtain ⟨t, ht, hmt⟩ := cons_corr_pos E (show 0 < corr consExt E (3 * k + 2) (Msg.app (CMsg.prefer y)) by omega)
  obtain ⟨hy1, hy2⟩ := out_prefer_imp E hmt
  rw [(cons_strong E k u).1]
  apply pick_eq
  · simp only [prefCands, Finset.mem_filter]
    refine ⟨mem_vals.mpr ⟨t, _, (mem_inbox_correct _ _ _ _ _ ht _).mpr hmt, rfl⟩, ?_⟩
    obtain ⟨k', hk', h1, h2, -⟩ := cons_count E (s := 3 * k + 2) (t := 3 * k + 3) rfl u (CMsg.prefer y)
    omega
  · intro z hz
    simp only [prefCands, Finset.mem_filter] at hz
    obtain ⟨s', -, hms⟩ := cons_lemma1 E hres (s := 3 * k + 2) (t := 3 * k + 3) rfl hz.2
    obtain ⟨hz1, hz2⟩ := out_prefer_imp E hms
    obtain ⟨q, -, hq1, hq2⟩ := lemma9 cons_hinit hres (s := 3 * k + 1) (cons_alive E _ s')
      (cons_alive E _ t) hz2 hy2
    rw [out_input_iff] at hq1 hq2
    rw [hq1, hq2]

/-- (B) Lemma 10 of the full version: if a correct node decides (receives `2n/3` copies of
`strongprefer(y)`) in step `3k+4`, every correct node has opinion `y` after steps `3k+3` and
`3k+4`. -/
lemma lock {k : ℕ} {w : I} {y : X}
    (hc : 2 * (R (3 * k + 4) w).core.heard.card ≤
      3 * cnt (Bx (3 * k + 3) w) (Msg.app (CMsg.strong y)))
    (u : I) : (R (3 * k + 3) u).ext.x = y ∧ (R (3 * k + 4) u).ext.x = y := by
  have hbig := cons_lemma2 E hres rfl hc
  obtain ⟨t, ht, hmt⟩ := cons_corr_pos E (show 0 < corr consExt E (3 * k + 3) (Msg.app (CMsg.strong y)) by omega)
  obtain ⟨-, hy2⟩ := out_strong_imp E hmt
  have h3 : (R (3 * k + 3) u).ext.x = y := adopt E hres hy2
  refine ⟨h3, ?_⟩
  rw [(cons_king E k u).2, h3]
  obtain ⟨k', hk', h1, h2, -⟩ := cons_count E (s := 3 * k + 3) (t := 3 * k + 4) rfl u (CMsg.strong y)
  rw [ite_f (by omega)]

/-- (C) Lemma 8 of the full version: if all correct nodes start phase `k` with opinion `y`, they
keep it, and every correct node has decided after step `3k+4`, every new decision being `y`. -/
lemma unanimous {k : ℕ} {y : X} (h : ∀ u ∈ E.G, (R (3 * k + 1) u).ext.x = y) (u : I)
    (hu : u ∈ E.G) :
    (R (3 * k + 3) u).ext.x = y ∧ (R (3 * k + 4) u).ext.x = y ∧
      (R (3 * k + 4) u).ext.dec ≠ none ∧
      ((R (3 * k + 3) u).ext.dec = none → (R (3 * k + 4) u).ext.dec = some y) := by
  -- everybody sends `input y`, then `prefer y`
  have hin : corr consExt E (3 * k + 1) (Msg.app (CMsg.input y)) = E.G.card :=
    corr_eq_card fun q hq => (out_input_iff E k q y).mpr (h q hq).symm
  have hpref : ∀ q ∈ E.G, Msg.app (CMsg.prefer y) ∈ (withRotor consExt).out (R (3 * k + 2) q) := by
    intro q hq
    have := out_prefer_of E (k := k) (q := q) (by
      rw [h q hq]
      obtain ⟨k', hk', h1, h2, -⟩ := cons_count E (s := 3 * k + 1) (t := 3 * k + 2) rfl q (CMsg.input y)
      omega)
    rwa [h q hq] at this
  have hpc : corr consExt E (3 * k + 2) (Msg.app (CMsg.prefer y)) = E.G.card := corr_eq_card hpref
  have hx3 : ∀ q ∈ E.G, (R (3 * k + 3) q).ext.x = y := by
    intro q hq
    refine adopt E hres (w := q) ?_
    obtain ⟨k', hk', h1, h2, -⟩ := cons_count E (s := 3 * k + 2) (t := 3 * k + 3) rfl q (CMsg.prefer y)
    omega
  have hstrong : ∀ q ∈ E.G,
      Msg.app (CMsg.strong y) ∈ (withRotor consExt).out (R (3 * k + 3) q) := by
    intro q hq
    have := out_strong_of E (k := k) (q := q) (by
      rw [hx3 q hq]
      obtain ⟨k', hk', h1, h2, -⟩ := cons_count E (s := 3 * k + 2) (t := 3 * k + 3) rfl q (CMsg.prefer y)
      omega)
    rwa [hx3 q hq] at this
  have hsc : corr consExt E (3 * k + 3) (Msg.app (CMsg.strong y)) = E.G.card :=
    corr_eq_card hstrong
  obtain ⟨k', hk', h1, h2, -⟩ := cons_count E (s := 3 * k + 3) (t := 3 * k + 4) rfl u (CMsg.strong y)
  have hk := cons_king E k u
  simp only at hk
  rw [hx3 u hu] at hk
  refine ⟨hx3 u hu, ?_, ?_, ?_⟩
  · rw [hk.2, ite_f (by omega)]
  · rw [hk.1]
    split_ifs with hd
    · simp
    · intro hnone
      exact hd ⟨hnone, by omega⟩
  · intro hnone
    rw [hk.1, ite_t ⟨hnone, by omega⟩]

/-- (C') Persistence: unanimity at the start of phase `k` persists in all later phases. -/
lemma unanimous_forever {k : ℕ} {y : X} (h : ∀ u ∈ E.G, (R (3 * k + 1) u).ext.x = y) :
    ∀ j, ∀ u ∈ E.G, (R (3 * (k + j) + 1) u).ext.x = y ∧ (R (3 * (k + j) + 3) u).ext.x = y := by
  intro j
  induction j with
  | zero => exact fun u hu => ⟨h u hu, (unanimous E hres h u hu).1⟩
  | succ j ih =>
    rw [show k + (j + 1) = k + j + 1 by ring]
    have h1 : ∀ u ∈ E.G, (R (3 * (k + j + 1) + 1) u).ext.x = y := fun u hu => by
      rw [show 3 * (k + j + 1) + 1 = 3 * (k + j) + 4 by ring]
      exact (unanimous E hres (fun u hu => (ih u hu).1) u hu).2.1
    exact fun u hu => ⟨h1 u hu, (unanimous E hres h1 u hu).1⟩

/-- (D) Lemma 11 of the full version: in a phase whose coordinator is correct and common, all
correct nodes end the phase with the coordinator's opinion. -/
lemma good_phase {k : ℕ} {p : I} (hp : p ∈ E.G)
    (hco : ∀ u ∈ E.G, (R (3 * k + 3) u).ext.coord = {p}) (u : I) (hu : u ∈ E.G) :
    (R (3 * k + 4) u).ext.x = (R (3 * k + 3) p).ext.x := by
  -- the king's opinion, as received by a correct node
  have hking : ∀ u ∈ E.G, pick (valsFrom (R (3 * k + 3) u).ext.coord CMsg.opVal (Bx (3 * k + 3) u))
      (R (3 * k + 3) u).ext.x = (R (3 * k + 3) p).ext.x := by
    intro u hu
    rw [hco u hu]
    apply pick_eq
    · refine mem_valsFrom.mpr ⟨p, Finset.mem_singleton_self _, CMsg.opinion _,
        (mem_inbox_correct _ _ _ _ _ hp _).mpr ?_, rfl⟩
      exact (out_opinion_iff E k p _).mpr ⟨by rw [hco p hp]; simp, rfl⟩
    · intro z hz
      obtain ⟨q, hq, a, hm, ha⟩ := mem_valsFrom.mp hz
      rw [Finset.mem_singleton] at hq; subst hq
      rw [mem_inbox_correct _ _ _ _ _ hp] at hm
      cases a with
      | opinion z' =>
        simp only [CMsg.opVal, Option.some.injEq] at ha; subst ha
        exact ((out_opinion_iff E k _ _).mp hm).2
      | _ => simp [CMsg.opVal] at ha
  -- the king step (`Cslib.Byzantine.kingPhase_agreement`): a node that received `n_v / 3` copies of
  -- `strongprefer(x_v)` keeps `x_v`, the others adopt the coordinator's opinion
  refine Cslib.Byzantine.kingPhase_agreement (H := (E.G : Set I))
    (val := fun v => (R (3 * k + 3) v).ext.x) (out := fun v => (R (3 * k + 4) v).ext.x)
    (strong := fun v => ¬ 3 * cnt (Bx (3 * k + 3) v) (Msg.app (CMsg.strong (R (3 * k + 3) v).ext.x)) <
      (R (3 * k + 4) v).core.heard.card) (keep := id) (adopt := id)
    (fun v _ hs => ?_) (fun v _ hs => ?_) (fun v hv hs => ?_) (fun _ _ _ => rfl) u hu
  · -- coherence: a strong correct node holds the opinion of every correct node
    obtain ⟨t, -, hmt⟩ := cons_lemma1 E hres (s := 3 * k + 3) (t := 3 * k + 4) rfl (v := v)
      (m := CMsg.strong (R (3 * k + 3) v).ext.x) (by omega)
    obtain ⟨-, h2⟩ := out_strong_imp E hmt
    exact adopt E hres h2
  · exact (cons_king E k v).2.trans (ite_f hs)
  · exact (cons_king E k v).2.trans ((ite_t (not_not.1 hs)).trans (hking v hv))

omit hres in
/-- The origin of a decision: the first decision is taken in a king step. -/
lemma dec_origin {s : ℕ} {v : I} {y : X} (h : (R s v).ext.dec = some y) :
    ∃ k, 3 * k + 4 ≤ s ∧ (R (3 * k + 3) v).ext.dec = none ∧ y = (R (3 * k + 3) v).ext.x ∧
      2 * (R (3 * k + 4) v).core.heard.card ≤
        3 * cnt (Bx (3 * k + 3) v) (Msg.app (CMsg.strong y)) := by
  induction s with
  | zero => rw [cons_dec_zero] at h; cases h
  | succ s ih =>
    rcases cons_dec_step E s v with h' | ⟨hnone, k, rfl, hd, hc⟩
    · obtain ⟨k, hk, h1, h2, h3⟩ := ih (h' ▸ h)
      exact ⟨k, by omega, h1, h2, h3⟩
    · rw [hd, Option.some.injEq] at h
      subst h
      exact ⟨k, le_rfl, hnone, rfl, hc⟩

omit hres in
lemma dec_mono {s s' : ℕ} {v : I} (h : (R s v).ext.dec ≠ none) (hs : s ≤ s') :
    (R s' v).ext.dec = (R s v).ext.dec := by
  induction hs with
  | refl => rfl
  | step hle ih =>
    rcases cons_dec_step E _ v with h' | ⟨hnone, -⟩
    · rw [h', ih]
    · rw [ih] at hnone; exact absurd hnone h

/-- After a decision on `y` in phase `k`, all correct nodes hold `y` at the strong step of every
phase `≥ k`. -/
lemma after_decision {k : ℕ} {w : I} {y : X}
    (hw : 2 * (R (3 * k + 4) w).core.heard.card ≤
      3 * cnt (Bx (3 * k + 3) w) (Msg.app (CMsg.strong y))) :
    ∀ j, ∀ u ∈ E.G, (R (3 * (k + j) + 3) u).ext.x = y := by
  intro j u hu
  rcases j with _ | j
  · exact (lock E hres hw u).1
  · have h1 : ∀ u ∈ E.G, (R (3 * (k + 1) + 1) u).ext.x = y := fun u _ => by
      rw [show 3 * (k + 1) + 1 = 3 * k + 4 by ring]; exact (lock E hres hw u).2
    have := (unanimous_forever E hres h1 j u hu).2
    rwa [show k + 1 + j = k + (j + 1) by ring] at this

/-- **Agreement.** -/
theorem agreement {v u : I} (hv : v ∈ E.G) (hu : u ∈ E.G) {s s' : ℕ} {y y' : X}
    (h : (R s v).ext.dec = some y) (h' : (R s' u).ext.dec = some y') : y = y' := by
  obtain ⟨k, -, -, hy, hc⟩ := dec_origin E h
  obtain ⟨k', -, -, hy', hc'⟩ := dec_origin E h'
  rcases le_total k k' with hk | hk
  · have := after_decision E hres hc (k' - k) u hu
    rw [show k + (k' - k) = k' by omega] at this
    rw [hy', this]
  · have := after_decision E hres hc' (k - k') v hv
    rw [show k' + (k - k') = k by omega] at this
    rw [hy, this]

/-- **Validity.** If all correct nodes have the same input `y`, every decision is `y`. -/
theorem validity {y : X} (hin : ∀ v ∈ E.G, E.input v = y) {v : I} (hv : v ∈ E.G) {s : ℕ}
    {y' : X} (h : (R s v).ext.dec = some y') : y' = y := by
  obtain ⟨k, -, -, hy, -⟩ := dec_origin E h
  have h0 : ∀ u ∈ E.G, (R (3 * 0 + 1) u).ext.x = y := fun u hu => by
    rw [cons_x_one]; exact hin u hu
  have := (unanimous_forever E hres h0 k v hv).2
  rw [Nat.zero_add] at this
  rw [hy, this]

/-- **Termination in `O(f)` rounds**: every correct node has decided after step `3f + 7`. -/
theorem termination {v : I} (hv : v ∈ E.G) : (R (3 * E.F.card + 7) v).ext.dec ≠ none := by
  obtain ⟨r, hr, p, hp, hsel⟩ := layer_good cons_hinit hres (fun k => 3 * k + 3) (by norm_num)
    (fun r => by omega) (fun q _ => cons_alive E _ q)
  have hco : ∀ u ∈ E.G, (R (3 * r + 3) u).ext.coord = {p} := fun u hu => by
    rw [(cons_strong E r u).2.1]; exact hsel u hu
  have h1 : ∀ u ∈ E.G, (R (3 * (r + 1) + 1) u).ext.x = (R (3 * r + 3) p).ext.x := fun u hu => by
    rw [show 3 * (r + 1) + 1 = 3 * r + 4 by ring]; exact good_phase E hres hp hco u hu
  have hdec := (unanimous E hres h1 v hv).2.2.1
  rw [dec_mono E hdec (show 3 * (r + 1) + 4 ≤ 3 * E.F.card + 7 by omega)]
  exact hdec

/-- **Consensus with unknown participants** (Section 5 of the BA; Theorem 3 of the full version,
repaired algorithm): if `n > 3f`, then in every run of `cons`
* (termination) every correct node decides within `3f + 7` rounds;
* (agreement) all decisions of correct nodes are equal;
* (validity) if all correct nodes have the same input, that is the only possible decision. -/
theorem consensus_correct :
    (∀ v ∈ E.G, ∃ y, (run cons E (3 * E.F.card + 7) v).ext.dec = some y) ∧
    (∀ v ∈ E.G, ∀ u ∈ E.G, ∀ s s' y y', (run cons E s v).ext.dec = some y →
      (run cons E s' u).ext.dec = some y' → y = y') ∧
    (∀ y, (∀ v ∈ E.G, E.input v = y) → ∀ v ∈ E.G, ∀ s y',
      (run cons E s v).ext.dec = some y' → y' = y) := by
  refine ⟨fun v hv => Option.ne_none_iff_exists'.mp (termination E hres hv),
    fun v hv u hu s s' y y' h h' => agreement E hres hv hu h h',
    fun y hin v hv s y' h => validity E hres hin hv h⟩

omit [LinearOrder X] hres in
/-- **Binary validity** (the paper's formulation): with binary inputs, every decision of a correct
node is the input of some correct node. -/
theorem consensus_validity_bool (E : Env I Bool (Msg I (CMsg Bool)))
    (hres : 2 * E.F.card < E.G.card) {v : I} (hv : v ∈ E.G) {s : ℕ} {y : Bool}
    (h : (run cons E s v).ext.dec = some y) : ∃ u ∈ E.G, E.input u = y := by
  by_contra hne
  push Not at hne
  have := validity E hres (y := !y) (fun u hu => by
    have := hne u hu; cases hy : E.input u <;> cases y <;> simp_all) hv h
  cases y <;> simp at this

end UnknownBA
