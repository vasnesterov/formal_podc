import Papers.PODC2021.GoodCaseLatencyBB.Unsync
import Papers.PODC2021.GoodCaseLatencyBB.BRBProtocol

/-!
# Theorem 10 fails for `n = 3`

Abraham–Nayak–Ren–Xiang, PODC 2021, Theorem 10 claims: every BRB protocol for the
unsynchronized-start model (delays `≤ Δ`, clock skew `≤ δ/2`) resilient to `f > n/3` faults has
good-case latency at least `Δ + 1.5δ`. Its proof (`Thm10.theorem_10`) needs `n ≥ 4`. For `n = 3`
(and any `f`, in particular `f = 2, 3 > n/3`) the statement is false: the protocol below solves BRB
in the unsynchronized-start model with **any** number of faults and **any** clock skew, and has
good-case latency `Δ + δ`.

## The protocol ("wait `Δ`, then commit; confirm via commit certificates")

Processes: the broadcaster `s` and two others. Tokens: `prop v` signed by `s`, `commit v` signed
by the committer. Every process gossips the set of all tokens it knows at every step.

* `s` knows `prop(input)` and decides its input at its start.
* A non-broadcaster `x` records the local time `tf` at which it first knows a `prop` token.
  While undecided, at local time `tf + Δ`, if it knows exactly one proposed value `v`, it
  decides `v` and creates `commit v` (*fast commit*); otherwise, as soon as it knows two different
  proposed values and a `commit v` token signed by the third process, it decides `v` (*confirm*).

Why it works. Two honest fast commits agree: if `p` fast-commits `v` at global time `T_p` and `q`
fast-commits `w` at `T_q ≤ T_p`, then `q` knew `prop w` at `T_q − Δ`, so `p` knows it at
`T_q ≤ T_p` and `v = w` (`fast_agree`). A confirmation copies the fast commit of the only other
non-broadcaster, which (when honest) is the sender of the `commit` token (`cert_dec`). With an honest
broadcaster no honest process ever sees two proposed values. Termination: an honest fast commit is
gossiped, and the receiver either fast-commits or detects the equivocation and confirms
(`progress`).

## Main results

* `unforging`: the protocol (through the late-start wrapper) respects unforgeability.
* `three_brb`: BRB in `unsyncRuns f Δ σ` for `n = 3`, any `f`, any skew `σ`.
* `three_latency`: good-case latency `Δ + δ` (all correct start at `0`, delays `≤ δ`).
* `theorem_10_false_three`: for `n = 3` the conclusion of `Thm10.theorem_10` fails under all its
  other hypotheses; `theorem_10_n4_necessary`: the hypothesis `4 ≤ n` cannot be dropped.
-/

set_option linter.unusedSectionVars false

namespace GoodCaseLatencyBB

open Cslib.Byzantine.PartialSync Finset

namespace ThreeParties

/-- Signed statements: `prop p v` (a proposal of `v`) and `commit p v`, both signed by `p`. -/
inductive Tok (P V : Type*) where
  | prop (p : P) (v : V)
  | commit (p : P) (v : V)
  deriving DecidableEq

/-- Local state: known tokens, local clock, local time at which a proposal was first known,
latched decision. -/
structure St (P V : Type*) where
  known : Finset (Tok P V)
  clk : ℕ
  tf : Option ℕ
  dec : Option V

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- The signer of a token. -/
def Tok.signer : Tok P V → P
  | .prop p _ => p
  | .commit p _ => p

/-- Ideal signatures: a message is a finite set of tokens and carries exactly these tokens. -/
def auth : Auth P (Finset (Tok P V)) (Tok P V) where
  signer := Tok.signer
  tokens m := ↑m

/-- The empty state (also used before the start). -/
def St.dummy : St P V := ⟨∅, 0, none, none⟩

section Defs

variable (s : P) (Δ : ℕ)

/-- `v` is the only value proposed by `s` in `K`. -/
def Uniq (K : Finset (Tok P V)) (v : V) : Prop :=
  Tok.prop s v ∈ K ∧ ∀ w, Tok.prop s w ∈ K → w = v

/-- `K` contains two different proposals of `s` (equivocation). -/
def Equiv (K : Finset (Tok P V)) : Prop :=
  ∃ v w, Tok.prop s v ∈ K ∧ Tok.prop s w ∈ K ∧ v ≠ w

/-- `K` contains a commit of `v` by a process other than `s` and `x`. -/
def Cert (x : P) (K : Finset (Tok P V)) (v : V) : Prop :=
  ∃ y, y ≠ s ∧ y ≠ x ∧ Tok.commit y v ∈ K

open Classical in
/-- Update of `tf` in a step with known tokens `K`. -/
noncomputable def newTf (st : St P V) (K : Finset (Tok P V)) : Option ℕ :=
  if st.tf = none ∧ ∃ v, Tok.prop s v ∈ K then some (st.clk + 1) else st.tf

/-- Fast-commit condition. -/
def FastOK (st : St P V) (K : Finset (Tok P V)) : Prop :=
  st.dec = none ∧ (∃ k, newTf s st K = some k ∧ st.clk + 1 = k + Δ) ∧ ∃ v, Uniq s K v

/-- Confirmation condition. -/
def ConfOK (x : P) (st : St P V) (K : Finset (Tok P V)) : Prop :=
  st.dec = none ∧ Equiv s K ∧ ∃ v, Cert s x K v

open Classical in
/-- One step of process `x` whose known tokens (after receiving) are `K`. -/
noncomputable def step1 (x : P) (st : St P V) (K : Finset (Tok P V)) : St P V :=
  if h : FastOK s Δ st K then
    ⟨insert (Tok.commit x h.2.2.choose) K, st.clk + 1, newTf s st K, some h.2.2.choose⟩
  else if h' : ConfOK s x st K then
    ⟨K, st.clk + 1, newTf s st K, some h'.2.2.choose⟩
  else ⟨K, st.clk + 1, newTf s st K, st.dec⟩

/-- All tokens of all received messages. -/
def received (ib : P → List (Finset (Tok P V))) : Finset (Tok P V) :=
  univ.biUnion fun q => (ib q).toFinset.biUnion id

/-- **The protocol** with broadcaster `s` and parameter `Δ` (run through `lateStart`). -/
noncomputable def algo : Algorithm P (Finset (Tok P V)) (St P V) V V where
  init x v := if x = s then ⟨{Tok.prop s v}, 0, some 0, some v⟩ else St.dummy
  step x st ib := step1 s Δ x st (st.known ∪ received ib)
  send _ st _ := [st.known]
  decide _ st := st.dec

/-- The inner state of `x` at global time `t` (`St.dummy` before its start). -/
noncomputable def ist (R : Run P (Finset (Tok P V)) (V × ℕ)) (x : P) (t : ℕ) : St P V :=
  (R.st (lateStart (algo s Δ)) t x).elim (fun _ => St.dummy) id

/-- `x` fast-committed `v` (certificate visible at time `t`). -/
def Fast (R : Run P (Finset (Tok P V)) (V × ℕ)) (x : P) (t : ℕ) (v : V) : Prop :=
  Tok.commit x v ∈ (ist s Δ R x t).known ∧ ∃ T ≤ t, ustart R x + Δ ≤ T ∧
    Tok.prop s v ∈ (ist s Δ R x (T - Δ)).known ∧ Uniq s (ist s Δ R x T).known v

/-- `x` decided `v` by confirmation (certificate visible at time `t`). -/
def Conf (R : Run P (Finset (Tok P V)) (V × ℕ)) (x : P) (t : ℕ) (v : V) : Prop :=
  Equiv s (ist s Δ R x t).known ∧ Cert s x (ist s Δ R x t).known v

end Defs

/-! ### The local step -/

section Step

variable {s : P} {Δ : ℕ} {x : P} {st : St P V} {K : Finset (Tok P V)}

theorem step1_clk : (step1 s Δ x st K).clk = st.clk + 1 := by
  unfold step1; split_ifs <;> rfl

theorem step1_tf : (step1 s Δ x st K).tf = newTf s st K := by
  unfold step1; split_ifs <;> rfl

theorem step1_known :
    (step1 s Δ x st K).known = K ∨ ∃ v, (step1 s Δ x st K).known = insert (Tok.commit x v) K ∧
      st.dec = none ∧ (step1 s Δ x st K).dec = some v := by
  unfold step1; split_ifs with h h'
  · exact Or.inr ⟨_, rfl, h.1, rfl⟩
  · exact Or.inl rfl
  · exact Or.inl rfl

theorem subset_step1 : K ⊆ (step1 s Δ x st K).known := by
  rcases step1_known (s := s) (Δ := Δ) (x := x) (st := st) (K := K) with h | ⟨v, h, -⟩
  · rw [h]
  · rw [h]; exact subset_insert _ _

theorem mem_step1 {k : Tok P V} (hk : k ∈ (step1 s Δ x st K).known) :
    k ∈ K ∨ ∃ v, k = Tok.commit x v ∧ st.dec = none ∧ (step1 s Δ x st K).dec = some v := by
  rcases step1_known (s := s) (Δ := Δ) (x := x) (st := st) (K := K) with h | ⟨v, h, h1, h2⟩
  · rw [h] at hk; exact Or.inl hk
  · rw [h, mem_insert] at hk
    rcases hk with hk | hk
    · exact Or.inr ⟨v, hk, h1, h2⟩
    · exact Or.inl hk

theorem step1_prop {y : P} {w : V} :
    Tok.prop y w ∈ (step1 s Δ x st K).known ↔ Tok.prop y w ∈ K := by
  rcases step1_known (s := s) (Δ := Δ) (x := x) (st := st) (K := K) with h | ⟨v, h, -⟩
  · rw [h]
  · rw [h, mem_insert]; simp

theorem step1_dec_some {v : V} (h : st.dec = some v) : (step1 s Δ x st K).dec = some v := by
  unfold step1; split_ifs with h1 h2
  · rw [h1.1] at h; cases h
  · rw [h2.1] at h; cases h
  · exact h

theorem step1_dec_spec {v : V} (h0 : st.dec = none) (h : (step1 s Δ x st K).dec = some v) :
    ((∃ k, newTf s st K = some k ∧ st.clk + 1 = k + Δ) ∧ Uniq s K v ∧
      (step1 s Δ x st K).known = insert (Tok.commit x v) K) ∨
    (Equiv s K ∧ Cert s x K v ∧ (step1 s Δ x st K).known = K) := by
  unfold step1 at h ⊢; split_ifs at h ⊢ with h1 h2
  · cases h; exact Or.inl ⟨h1.2.1, h1.2.2.choose_spec, rfl⟩
  · cases h; exact Or.inr ⟨h2.2.1, h2.2.2.choose_spec, rfl⟩
  · rw [h0] at h; cases h

theorem step1_dec_progress (h : FastOK s Δ st K ∨ ConfOK s x st K) :
    (step1 s Δ x st K).dec ≠ none := by
  unfold step1; split_ifs with h1 h2
  · simp
  · simp
  · exact absurd h (by tauto)

theorem newTf_of_some {k : ℕ} (h : st.tf = some k) : newTf s st K = some k := by
  simp [newTf, h]

theorem newTf_ne_none (h : ∃ v, Tok.prop s v ∈ K) : newTf s st K ≠ none := by
  unfold newTf; split_ifs with h1
  · simp
  · intro h2; exact h1 ⟨h2, h⟩

theorem newTf_cases {k : ℕ} (h : newTf s st K = some k) :
    st.tf = some k ∨ (k = st.clk + 1 ∧ ∃ v, Tok.prop s v ∈ K) := by
  unfold newTf at h; split_ifs at h with h1
  · cases h; exact Or.inr ⟨rfl, h1.2⟩
  · exact Or.inl h

theorem Equiv.mono {K K' : Finset (Tok P V)} (h : K ⊆ K') : Equiv s K → Equiv s K' :=
  fun ⟨v, w, hv, hw, hne⟩ => ⟨v, w, h hv, h hw, hne⟩

theorem Cert.mono {K K' : Finset (Tok P V)} (h : K ⊆ K') {v : V} :
    Cert s x K v → Cert s x K' v :=
  fun ⟨y, h1, h2, h3⟩ => ⟨y, h1, h2, h h3⟩

theorem equiv_step1 : Equiv s (step1 s Δ x st K).known ↔ Equiv s K := by
  simp only [Equiv, step1_prop]

theorem uniq_step1 {v : V} : Uniq s (step1 s Δ x st K).known v ↔ Uniq s K v := by
  simp only [Uniq, step1_prop]

theorem mem_received {ib : P → List (Finset (Tok P V))} {k : Tok P V} :
    k ∈ received ib ↔ ∃ r, ∃ m ∈ ib r, k ∈ m := by
  simp [received]

theorem init_eq (s : P) (Δ : ℕ) (x : P) (v : V) :
    (algo s Δ).init x v = if x = s then ⟨{Tok.prop s v}, 0, some 0, some v⟩ else St.dummy := rfl

theorem init_known {v : V} {k : Tok P V} (hk : k ∈ ((algo s Δ).init x v).known) :
    x = s ∧ k = Tok.prop s v := by
  rw [init_eq] at hk; split_ifs at hk with h
  · exact ⟨h, by simpa using hk⟩
  · simp [St.dummy] at hk

end Step

/-! ### Runs: inner states -/

section RunLayer

variable {s : P} {Δ : ℕ} (R : Run P (Finset (Tok P V)) (V × ℕ))

theorem ist_before {x : P} {t : ℕ} (h : t < ustart R x) : ist s Δ R x t = St.dummy := by
  simp only [ist, lateStart_st_before (A := algo s Δ) (R := R) x t h]; rfl

theorem ist_start (x : P) : ist s Δ R x (ustart R x) = (algo s Δ).init x (R.inp x).1 := by
  simp only [ist, lateStart_st_start (A := algo s Δ) (R := R) x]; rfl

theorem st_inr {x : P} {t : ℕ} (h : ustart R x ≤ t) :
    R.st (lateStart (algo s Δ)) t x = .inr (ist s Δ R x t) := by
  obtain ⟨y, hy⟩ := lateStart_st_after (A := algo s Δ) (R := R) x t h
  simp only [ist, hy]; rfl

theorem ist_succ {x : P} {t : ℕ} (h : ustart R x ≤ t) :
    ist s Δ R x (t + 1) = step1 s Δ x (ist s Δ R x t)
      ((ist s Δ R x t).known ∪ received (R.inbox (lateStart (algo s Δ)) x t)) := by
  simp only [ist]; rw [Run.st_succ, st_inr R h]; rfl

theorem decide_eq (x : P) (t : ℕ) :
    (lateStart (algo s Δ)).decide x (R.st (lateStart (algo s Δ)) t x) = (ist s Δ R x t).dec := by
  simp only [ist]; generalize R.st (lateStart (algo s Δ)) t x = z; cases z <;> rfl

theorem decides_iff {x : P} {v : V} :
    R.Decides (lateStart (algo s Δ)) x v ↔ ∃ t, (ist s Δ R x t).dec = some v := by
  simp only [Run.Decides, decide_eq]

theorem out_eq {q : P} {τ : ℕ} {r : P} {m : Finset (Tok P V)} (hq : q ∉ R.faulty)
    (hm : m ∈ R.out (lateStart (algo s Δ)) q τ r) : m = (ist s Δ R q τ).known := by
  rw [Run.out_of_correct _ _ hq] at hm
  simp only [ist]; generalize R.st (lateStart (algo s Δ)) τ q = z at hm ⊢
  cases z <;> simp_all [lateStart, algo]

theorem mem_out {q : P} {τ : ℕ} (hq : q ∉ R.faulty) (hτ : ustart R q ≤ τ) (r : P) :
    (ist s Δ R q τ).known ∈ R.out (lateStart (algo s Δ)) q τ r := by
  rw [Run.out_of_correct _ _ hq, st_inr R hτ]; simp [lateStart, algo]

theorem ist_ind (x : P) {Q : ℕ → Prop} (hb : ∀ t < ustart R x, Q t) (h0 : Q (ustart R x))
    (hs : ∀ t, ustart R x ≤ t → Q t → Q (t + 1)) : ∀ t, Q t := by
  intro t
  rcases lt_or_ge t (ustart R x) with h | h
  · exact hb t h
  · induction t, h using Nat.le_induction with
    | base => exact h0
    | succ t ht ih => exact hs t ht ih

theorem ist_clk {x : P} {t : ℕ} (h : ustart R x ≤ t) :
    (ist s Δ R x t).clk = t - ustart R x := by
  induction t, h using Nat.le_induction with
  | base => rw [ist_start, init_eq]; split_ifs <;> simp [St.dummy]
  | succ t ht ih => rw [ist_succ R ht, step1_clk, ih]; omega

theorem known_mono {x : P} {t t' : ℕ} (h : t ≤ t') :
    (ist s Δ R x t).known ⊆ (ist s Δ R x t').known := by
  induction t', h using Nat.le_induction with
  | base => exact subset_rfl
  | succ t' _ ih =>
    refine ih.trans ?_
    rcases lt_or_ge t' (ustart R x) with h' | h'
    · rw [ist_before R h']; simp [St.dummy]
    · rw [ist_succ R h']; exact subset_union_left.trans subset_step1

theorem dec_mono {x : P} {t t' : ℕ} {v : V} (h : t ≤ t') (hv : (ist s Δ R x t).dec = some v) :
    (ist s Δ R x t').dec = some v := by
  induction t', h using Nat.le_induction with
  | base => exact hv
  | succ t' _ ih =>
    rcases lt_or_ge t' (ustart R x) with h' | h'
    · rw [ist_before R h'] at ih; cases ih
    · rw [ist_succ R h']; exact step1_dec_some ih

theorem tf_mono {x : P} {t t' k : ℕ} (h : t ≤ t') (hk : (ist s Δ R x t).tf = some k) :
    (ist s Δ R x t').tf = some k := by
  induction t', h using Nat.le_induction with
  | base => exact hk
  | succ t' _ ih =>
    rcases lt_or_ge t' (ustart R x) with h' | h'
    · rw [ist_before R h'] at ih; cases ih
    · rw [ist_succ R h', step1_tf]; exact newTf_of_some ih

theorem dec_unique {x : P} {t t' : ℕ} {v w : V} (hv : (ist s Δ R x t).dec = some v)
    (hw : (ist s Δ R x t').dec = some w) : v = w := by
  have h1 := dec_mono R (le_max_left t t') hv
  rw [dec_mono R (le_max_right t t') hw] at h1
  exact (Option.some.inj h1).symm

theorem ustart_le_of_mem {x : P} {t : ℕ} {k : Tok P V} (hk : k ∈ (ist s Δ R x t).known) :
    ustart R x ≤ t := by
  by_contra h; rw [ist_before R (by omega)] at hk; simp [St.dummy] at hk

theorem mem_known_of_inbox {x : P} {t : ℕ} {r : P} {m : Finset (Tok P V)} {k : Tok P V}
    (ht : ustart R x ≤ t) (hm : m ∈ R.inbox (lateStart (algo s Δ)) x t r) (hk : k ∈ m) :
    k ∈ (ist s Δ R x (t + 1)).known := by
  rw [ist_succ R ht]; exact subset_step1 (mem_union_right _ (mem_received.mpr ⟨r, m, hm, hk⟩))

theorem gossip {q r : P} {τ : ℕ} (hq : q ∉ R.faulty) (hdl : τ ≤ R.dl q τ r)
    (hu : ustart R r ≤ R.dl q τ r) :
    (ist s Δ R q τ).known ⊆ (ist s Δ R r (R.dl q τ r + 1)).known := by
  intro k hk
  exact mem_known_of_inbox R hu
    (Run.mem_inbox.mpr ⟨τ, hdl, rfl, mem_out R hq (ustart_le_of_mem R hk) r⟩) hk

theorem gossipU {f d σ : ℕ} (hV : UValid f d σ R) {q r : P} (hq : q ∉ R.faulty)
    (hr : r ∉ R.faulty) (τ : ℕ) : (ist s Δ R q τ).known ⊆ (ist s Δ R r (τ + d)).known :=
  (gossip R hq (hV.dl_ge q τ r hq hr) (hV.dl_start q τ r hq hr)).trans
    (known_mono R (by have := hV.dl_lt q τ r hq hr; omega))

end RunLayer

/-! ### Unforgeability and the origin of tokens -/

section Tokens

variable {s : P} {Δ : ℕ}

/-- Correct processes only emit their own tokens and relay received ones. -/
theorem unforging : (lateStart (algo (V := V) s Δ)).Unforging auth := by
  intro R p τ q m hm k hk
  have hm' : m = (ist s Δ R p τ).known := by
    simp only [ist]; generalize R.st (lateStart (algo s Δ)) τ p = z at hm ⊢
    cases z <;> simp_all [lateStart, algo]
  subst hm'
  change k ∈ (ist s Δ R p τ).known at hk
  revert k
  refine ist_ind R p (Q := fun τ => ∀ k ∈ (ist s Δ R p τ).known,
    auth.signer k = p ∨ k ∈ R.recvTokens auth (lateStart (algo s Δ)) p τ) ?_ ?_ ?_ τ
  · intro t ht k hk; rw [ist_before R ht] at hk; simp [St.dummy] at hk
  · intro k hk; rw [ist_start] at hk; obtain ⟨rfl, rfl⟩ := init_known hk; exact Or.inl rfl
  · intro t ht ih k hk
    rw [ist_succ R ht] at hk
    rcases mem_step1 hk with h | ⟨v, rfl, -⟩
    · rcases mem_union.mp h with h | h
      · rcases ih k h with h' | ⟨τ', hτ', rest⟩
        · exact Or.inl h'
        · exact Or.inr ⟨τ', by omega, rest⟩
      · obtain ⟨r, m, hm, hkm⟩ := mem_received.mp h
        exact Or.inr ⟨t, by omega, r, m, hm, hkm⟩
    · exact Or.inl rfl

variable {R : Run P (Finset (Tok P V)) (V × ℕ)}

theorem known_honest {x : P} (hx : x ∉ R.faulty) {τ : ℕ} {k : Tok P V}
    (hk : k ∈ (ist s Δ R x τ).known) : k ∈ R.honestTokens auth (lateStart (algo s Δ)) τ :=
  ⟨τ, le_rfl, x, hx, x, _, mem_out R hx (ustart_le_of_mem R hk) x, hk⟩

/-- A token emitted by correct processes and signed by a correct `y` is known to `y`. -/
theorem honest_known (hR : R.AuthValid auth (lateStart (algo s Δ))) {y : P} (hy : y ∉ R.faulty)
    {τ : ℕ} {k : Tok P V} (hk : k ∈ R.honestTokens auth (lateStart (algo s Δ)) τ)
    (hs : k.signer = y) : k ∈ (ist s Δ R y τ).known := by
  rcases Run.honestTokens_origin unforging hR hk with h | ⟨τ', hτ', r, m, hm, hkm⟩
  · exact absurd (by rw [← hs]; exact h) hy
  · have e : auth.signer k = y := hs
    rw [e] at hm
    rw [out_eq R hy hm] at hkm
    exact known_mono R hτ' hkm

/-- A token received by a correct process and signed by a correct `y` is known to `y`. -/
theorem recv_signed (hR : R.AuthValid auth (lateStart (algo s Δ))) {x : P} (hx : x ∉ R.faulty)
    {t : ℕ} {k : Tok P V} (hk : k ∈ received (R.inbox (lateStart (algo s Δ)) x t)) {y : P}
    (hy : y ∉ R.faulty) (hs : k.signer = y) : k ∈ (ist s Δ R y t).known := by
  obtain ⟨r, m, hm, hkm⟩ := mem_received.mp hk
  obtain ⟨σ, hσ, -, hm'⟩ := Run.mem_inbox.mp hm
  refine known_mono R hσ (honest_known hR hy ?_ hs)
  by_cases hr : r ∈ R.faulty
  · rw [Run.out_of_faulty _ _ hr] at hm'
    rcases hR r hr σ x hx m hm' k hkm with h | h
    · exact absurd (by rw [← hs]; exact h) hy
    · exact h
  · exact ⟨σ, le_rfl, r, hr, x, m, hm', hkm⟩

/-- A correct process holding its own commit token for `v` has decided `v`. -/
theorem own_commit (hR : R.AuthValid auth (lateStart (algo s Δ))) {x : P} (hx : x ∉ R.faulty) :
    ∀ t v, Tok.commit x v ∈ (ist s Δ R x t).known → (ist s Δ R x t).dec = some v := by
  refine ist_ind R x ?_ ?_ ?_
  · intro t ht v hv; rw [ist_before R ht] at hv; simp [St.dummy] at hv
  · intro v hv; rw [ist_start] at hv; obtain ⟨-, h⟩ := init_known hv; cases h
  · intro t ht ih v hv
    rw [ist_succ R ht] at hv ⊢
    rcases mem_step1 hv with h | ⟨w, hw, -, hd⟩
    · refine step1_dec_some ?_
      rcases mem_union.mp h with h | h
      · exact ih v h
      · exact ih v (recv_signed hR hx h hx rfl)
    · cases hw; exact hd

/-- A commit token of a correct `y` known to a correct process certifies `y`'s decision. -/
theorem cert_dec (hR : R.AuthValid auth (lateStart (algo s Δ))) {p y : P} (hp : p ∉ R.faulty)
    (hy : y ∉ R.faulty) {t : ℕ} {v : V} (h : Tok.commit y v ∈ (ist s Δ R p t).known) :
    (ist s Δ R y t).dec = some v :=
  own_commit hR hy t v (honest_known hR hy (known_honest hp h) rfl)

/-- A correct broadcaster only proposes its input. -/
theorem prop_bcast (hR : R.AuthValid auth (lateStart (algo s Δ))) (hs : s ∉ R.faulty) :
    ∀ t w, Tok.prop s w ∈ (ist s Δ R s t).known → w = (R.inp s).1 := by
  refine ist_ind R s ?_ ?_ ?_
  · intro t ht w hw; rw [ist_before R ht] at hw; simp [St.dummy] at hw
  · intro w hw; rw [ist_start] at hw; obtain ⟨-, h⟩ := init_known hw; cases h; rfl
  · intro t ht ih w hw
    rw [ist_succ R ht, step1_prop] at hw
    rcases mem_union.mp hw with h | h
    · exact ih w h
    · exact ih w (recv_signed hR hs h hs rfl)

theorem prop_input (hR : R.AuthValid auth (lateStart (algo s Δ))) (hs : s ∉ R.faulty) {x : P}
    (hx : x ∉ R.faulty) {t : ℕ} {w : V} (hw : Tok.prop s w ∈ (ist s Δ R x t).known) :
    w = (R.inp s).1 :=
  prop_bcast hR hs t w (honest_known hR hs (known_honest hx hw) rfl)

end Tokens

/-! ### Invariants of the local states (no honesty needed) -/

section Inv

variable {s : P} {Δ : ℕ} (R : Run P (Finset (Tok P V)) (V × ℕ))

/-- `tf` records the (local) time at which a proposal was first known. -/
theorem tf_inv (x : P) : ∀ t, (∀ k, (ist s Δ R x t).tf = some k →
    ustart R x + k ≤ t ∧ (ist s Δ R x (ustart R x + k)).tf = some k ∧
      ∃ w, Tok.prop s w ∈ (ist s Δ R x (ustart R x + k)).known) ∧
    ((∃ w, Tok.prop s w ∈ (ist s Δ R x t).known) → (ist s Δ R x t).tf ≠ none) := by
  refine ist_ind R x ?_ ?_ ?_
  · intro t ht; rw [ist_before R ht]; simp [St.dummy]
  · rw [ist_start, init_eq]; split_ifs with h
    · subst h; refine ⟨fun k hk => ?_, fun _ => by simp⟩
      simp only [Option.some.injEq] at hk; subst hk
      simp only [Nat.add_zero, le_refl, true_and]
      rw [ist_start, init_eq]; simp
    · simp [St.dummy]
  · rintro t ht ⟨ih1, -⟩
    refine ⟨fun k hk => ?_, fun ⟨w, hw⟩ => ?_⟩
    · rw [ist_succ R ht, step1_tf] at hk
      rcases newTf_cases hk with h | ⟨rfl, hp⟩
      · obtain ⟨h1, h2, h3⟩ := ih1 k h; exact ⟨by omega, h2, h3⟩
      · rw [ist_clk R ht] at hk ⊢
        have e : ustart R x + (t - ustart R x + 1) = t + 1 := by omega
        rw [e, ist_succ R ht, step1_tf]
        exact ⟨le_rfl, hk, hp.imp fun w hw => subset_step1 hw⟩
    · rw [ist_succ R ht, step1_tf]
      rw [ist_succ R ht, step1_prop] at hw
      exact newTf_ne_none ⟨w, hw⟩

theorem dec_init (s : P) (Δ : ℕ) : (ist s Δ R s (ustart R s)).dec = some (R.inp s).1 := by
  rw [ist_start, init_eq]; simp

/-- **Decision certificate.** A decision is the broadcaster's input (decided by `s` at start), a
fast commit, or a confirmation. -/
theorem dec_inv (x : P) : ∀ t v, (ist s Δ R x t).dec = some v →
    (x = s ∧ v = (R.inp s).1) ∨ (x ≠ s ∧ (Fast s Δ R x t v ∨ Conf s Δ R x t v)) := by
  refine ist_ind R x ?_ ?_ ?_
  · intro t ht v hv; rw [ist_before R ht] at hv; cases hv
  · intro v hv; rw [ist_start, init_eq] at hv; split_ifs at hv with h
    · subst h; cases hv; exact Or.inl ⟨rfl, rfl⟩
    · cases hv
  · intro t ht ih v hv
    by_cases hd : (ist s Δ R x t).dec = none
    · have hxs : x ≠ s := by
        rintro rfl
        have := dec_mono R ht (dec_init R x Δ)
        rw [hd] at this; cases this
      have hv' := hv
      rw [ist_succ R ht] at hv'
      refine Or.inr ⟨hxs, ?_⟩
      rcases step1_dec_spec hd hv' with ⟨⟨k, hk, hc⟩, hu, hkn⟩ | ⟨he, hc, hkn⟩
      · left
        obtain ⟨h1, -, w, hw⟩ := (tf_inv R x (t + 1)).1 k (by rw [ist_succ R ht, step1_tf]; exact hk)
        rw [ist_clk R ht] at hc
        have e : t + 1 - Δ = ustart R x + k := by omega
        have hw' : Tok.prop s w ∈ (ist s Δ R x (t + 1)).known := known_mono R h1 hw
        rw [ist_succ R ht, step1_prop] at hw'
        obtain rfl := hu.2 w hw'
        refine ⟨?_, t + 1, le_rfl, by omega, by rw [e]; exact hw, ?_⟩
        · rw [ist_succ R ht, hkn]; exact mem_insert_self _ _
        · rw [ist_succ R ht, uniq_step1]; exact hu
      · right
        unfold Conf; rw [ist_succ R ht, hkn]; exact ⟨he, hc⟩
    · obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hd
      have hw' := step1_dec_some (s := s) (Δ := Δ) (x := x)
        (K := (ist s Δ R x t).known ∪ received (R.inbox (lateStart (algo s Δ)) x t)) hw
      rw [← ist_succ R ht, hv] at hw'
      cases hw'
      rcases ih v hw with h | ⟨hxs, ⟨hc, T, hT, rest⟩ | ⟨he, hc⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨hxs, Or.inl ⟨known_mono R (Nat.le_succ t) hc, T, by omega, rest⟩⟩
      · exact Or.inr ⟨hxs, Or.inr ⟨Equiv.mono (known_mono R (Nat.le_succ t)) he,
          Cert.mono (known_mono R (Nat.le_succ t)) hc⟩⟩

/-- **Progress.** If `x` knows a proposal at `t₀`, then by `t₀ + Δ` it has decided, unless it has
seen an equivocation but no commit certificate (from `t₀`). -/
theorem progress (hΔ : 1 ≤ Δ) {x : P} {t₀ : ℕ} {w : V}
    (hw : Tok.prop s w ∈ (ist s Δ R x t₀).known)
    (hc : ¬ Equiv s (ist s Δ R x (t₀ + Δ)).known ∨ ∃ v, Cert s x (ist s Δ R x t₀).known v) :
    (ist s Δ R x (t₀ + Δ)).dec ≠ none := by
  intro hd
  have hu := ustart_le_of_mem R hw
  have hnone : ∀ t ≤ t₀ + Δ, (ist s Δ R x t).dec = none := fun t ht => by
    cases h : (ist s Δ R x t).dec with
    | none => rfl
    | some v => rw [dec_mono R ht h] at hd; cases hd
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.mp ((tf_inv R x t₀).2 ⟨w, hw⟩)
  obtain ⟨h1, h2, w', hw'⟩ := (tf_inv R x t₀).1 k hk
  have ht1 : ustart R x ≤ ustart R x + k + Δ - 1 := by omega
  have htf1 : (ist s Δ R x (ustart R x + k + Δ - 1)).tf = some k := tf_mono R (by omega) h2
  have hw1 : Tok.prop s w' ∈ (ist s Δ R x (ustart R x + k + Δ - 1)).known ∪
      received (R.inbox (lateStart (algo s Δ)) x (ustart R x + k + Δ - 1)) :=
    mem_union_left _ (known_mono R (by omega) hw')
  by_cases hU : ∃ v, Uniq s ((ist s Δ R x (ustart R x + k + Δ - 1)).known ∪
      received (R.inbox (lateStart (algo s Δ)) x (ustart R x + k + Δ - 1))) v
  · have hclk : (ist s Δ R x (ustart R x + k + Δ - 1)).clk + 1 = k + Δ := by
      rw [ist_clk R ht1]; omega
    apply step1_dec_progress (Or.inl ⟨hnone (ustart R x + k + Δ - 1) (by omega),
      ⟨k, newTf_of_some htf1, hclk⟩, hU⟩)
    rw [← ist_succ R ht1]; exact hnone _ (by omega)
  · have hE : Equiv s ((ist s Δ R x (ustart R x + k + Δ - 1)).known ∪
        received (R.inbox (lateStart (algo s Δ)) x (ustart R x + k + Δ - 1))) := by
      by_contra hE
      refine hU ⟨w', hw1, fun z hz => ?_⟩
      by_contra hne; exact hE ⟨z, w', hz, hw1, hne⟩
    have hE' : Equiv s (ist s Δ R x (t₀ + Δ)).known := by
      refine Equiv.mono (known_mono R (show ustart R x + k + Δ - 1 + 1 ≤ t₀ + Δ by omega)) ?_
      rw [ist_succ R ht1]; exact equiv_step1.mpr hE
    obtain ⟨v, hv⟩ := hc.resolve_left (not_not.mpr hE')
    have ht2 : ustart R x ≤ t₀ + Δ - 1 := by omega
    have e : t₀ + Δ = t₀ + Δ - 1 + 1 := by omega
    rw [e, ist_succ R ht2] at hE' hd
    exact step1_dec_progress (Or.inr ⟨hnone _ (by omega), equiv_step1.mp hE', v,
      Cert.mono ((known_mono R (by omega : t₀ ≤ t₀ + Δ - 1)).trans subset_union_left) hv⟩) hd

end Inv

/-! ### Agreement, validity, termination, latency -/

section Main

variable {s : P} {Δ : ℕ} {R : Run P (Finset (Tok P V)) (V × ℕ)}

/-- With an honest broadcaster, honest processes only decide its input. -/
theorem dec_input (hR : R.AuthValid auth (lateStart (algo s Δ))) (hs : s ∉ R.faulty) {x : P}
    (hx : x ∉ R.faulty) {t : ℕ} {v : V} (hv : (ist s Δ R x t).dec = some v) :
    v = (R.inp s).1 := by
  rcases dec_inv R x t v hv with ⟨-, h⟩ | ⟨-, ⟨-, T, -, -, hp, -⟩ | ⟨⟨a, b, ha, hb, hab⟩, -⟩⟩
  · exact h
  · exact prop_input hR hs hx hp
  · exact absurd ((prop_input hR hs hx ha).trans (prop_input hR hs hx hb).symm) hab

/-- Two honest fast commits agree. -/
theorem fast_agree {f σ : ℕ} (hV : UValid f Δ σ R) {p q : P} (hp : p ∉ R.faulty)
    (hq : q ∉ R.faulty) {t t' : ℕ} {v w : V} (h1 : Fast s Δ R p t v) (h2 : Fast s Δ R q t' w) :
    v = w := by
  obtain ⟨-, T, -, hT, hpv, hu⟩ := h1
  obtain ⟨-, T', -, hT', hqw, hu'⟩ := h2
  rcases le_total T' T with h | h
  · have := gossipU R hV hq hp (T' - Δ) hqw
    rw [Nat.sub_add_cancel (by omega)] at this
    exact (hu.2 w (known_mono R h this)).symm
  · have := gossipU R hV hp hq (T - Δ) hpv
    rw [Nat.sub_add_cancel (by omega)] at this
    exact hu'.2 v (known_mono R h this)

/-- With three processes, a process different from two distinct processes is the third one. -/
theorem eq_third (h3 : Fintype.card P = 3) {a b c y : P} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hya : y ≠ a) (hyb : y ≠ b) : y = c := by
  by_contra hyc
  have h4 : ({y, a, b, c} : Finset P).card = 4 := by
    rw [card_insert_of_notMem (by simp [hya, hyb, hyc]), card_insert_of_notMem (by simp [hab, hac]),
      card_pair hbc]
  have := card_le_univ ({y, a, b, c} : Finset P)
  omega

variable (h3 : Fintype.card P = 3) (hΔ : 1 ≤ Δ) {f σ : ℕ}
include h3

theorem three_agreement (hV : UValid f Δ σ R) (hR : R.AuthValid auth (lateStart (algo s Δ)))
    {p q : P} (hp : p ∉ R.faulty) (hq : q ∉ R.faulty) {v w : V}
    (hv : R.Decides (lateStart (algo s Δ)) p v) (hw : R.Decides (lateStart (algo s Δ)) q w) :
    v = w := by
  obtain ⟨t, hv⟩ := (decides_iff R).mp hv
  obtain ⟨t', hw⟩ := (decides_iff R).mp hw
  by_cases hs : s ∈ R.faulty
  · by_cases hpq : p = q
    · subst hpq; exact dec_unique R hv hw
    have hps : p ≠ s := fun h => hp (h ▸ hs)
    have hqs : q ≠ s := fun h => hq (h ▸ hs)
    rcases dec_inv R p t v hv with ⟨h, -⟩ | ⟨-, hfp | ⟨-, y, hy1, hy2, hy⟩⟩
    · exact absurd h hps
    · rcases dec_inv R q t' w hw with ⟨h, -⟩ | ⟨-, hfq | ⟨-, z, hz1, hz2, hz⟩⟩
      · exact absurd h hqs
      · exact fast_agree hV hp hq hfp hfq
      · obtain rfl : z = p := eq_third h3 (Ne.symm hqs) (Ne.symm hps) (Ne.symm hpq) hz1 hz2
        exact dec_unique R hv (cert_dec hR hq hp hz)
    · obtain rfl : y = q := eq_third h3 (Ne.symm hps) (Ne.symm hqs) hpq hy1 hy2
      exact dec_unique R (cert_dec hR hp hq hy) hw
  · rw [dec_input hR hs hp hv, dec_input hR hs hq hw]

omit h3 in
include hΔ in
theorem three_validity (hV : UValid f Δ σ R) (hR : R.AuthValid auth (lateStart (algo s Δ)))
    (hs : s ∉ R.faulty) {p : P} (hp : p ∉ R.faulty) :
    R.Decides (lateStart (algo s Δ)) p (R.inp s).1 := by
  rw [decides_iff]
  by_cases hps : p = s
  · subst hps; exact ⟨_, dec_init R p Δ⟩
  · have h0 : Tok.prop s (R.inp s).1 ∈ (ist s Δ R s (ustart R s)).known := by
      rw [ist_start, init_eq]; simp
    have h1 := gossipU R hV hs hp _ h0
    have h2 := progress R hΔ h1 (Or.inl fun ⟨a, b, ha, hb, hab⟩ =>
      hab ((prop_input hR hs hp ha).trans (prop_input hR hs hp hb).symm))
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp h2
    exact ⟨_, (dec_input hR hs hp hv) ▸ hv⟩

include hΔ in
theorem three_termination (hV : UValid f Δ σ R) (hR : R.AuthValid auth (lateStart (algo s Δ)))
    {p : P} (hp : p ∉ R.faulty) {v : V} (hv : R.Decides (lateStart (algo s Δ)) p v)
    {r : P} (hr : r ∉ R.faulty) : ∃ w, R.Decides (lateStart (algo s Δ)) r w := by
  by_cases hs : s ∈ R.faulty
  · simp only [decides_iff] at hv ⊢
    obtain ⟨t, hv⟩ := hv
    by_cases hrp : r = p
    · subst hrp; exact ⟨v, t, hv⟩
    have hps : p ≠ s := fun h => hp (h ▸ hs)
    have hrs : r ≠ s := fun h => hr (h ▸ hs)
    rcases dec_inv R p t v hv with ⟨h, -⟩ | ⟨-, ⟨hc, T, hT, hTu, hprop, -⟩ | ⟨-, y, hy1, hy2, hy⟩⟩
    · exact absurd h hps
    · have hpr : Tok.prop s v ∈ (ist s Δ R r (t + Δ)).known :=
        gossipU R hV hp hr t (known_mono R (by omega) hprop)
      have hcr : Tok.commit p v ∈ (ist s Δ R r (t + Δ)).known := gossipU R hV hp hr t hc
      obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp
        (progress R hΔ hpr (Or.inr ⟨v, p, hps, Ne.symm hrp, hcr⟩))
      exact ⟨w, _, hw⟩
    · obtain rfl : y = r := eq_third h3 (Ne.symm hps) (Ne.symm hrs) (Ne.symm hrp) hy1 hy2
      exact ⟨v, t, cert_dec hR hp hr hy⟩
  · exact ⟨_, three_validity hΔ hV hR hs hr⟩

include hΔ in
/-- **BRB for `n = 3`** in the unsynchronized-start model, for any number of faults `f` and any
clock skew `σ`. -/
theorem three_brb (s : P) (f σ : ℕ) :
    IsBRBU auth (algo (V := V) s Δ) s (unsyncRuns f Δ σ) where
  agreement _ hV hR _ hp _ hq _ _ hv hw := three_agreement h3 hV hR hp hq hv hw
  validity _ hV hR hs _ hp := three_validity hΔ hV hR hs hp
  termination _ hV hR := fun ⟨_, hp, _, hv⟩ _ hr => three_termination h3 hΔ hV hR hp hv hr

omit h3 in
include hΔ in
/-- **Good-case latency `Δ + δ`**: with an honest broadcaster, all correct processes starting at
time `0` and delays `≤ δ`, every honest process commits by time `Δ + δ`. -/
theorem three_latency (s : P) (f δ : ℕ) :
    LatencyWithin auth (lateStart (algo (V := V) s Δ)) s (unsyncGood f δ) (Δ + δ) := by
  rintro R ⟨hV, hu⟩ hR hs p hp
  by_cases hps : p = s
  · subst hps
    refine ⟨(R.inp p).1, 0, by omega, ?_⟩
    rw [decide_eq]; have := dec_init R p Δ; rwa [hu p hp] at this
  · have h0 : Tok.prop s (R.inp s).1 ∈ (ist s Δ R s 0).known := by
      rw [← hu s hs, ist_start, init_eq]; simp
    have h1 := gossipU R hV hs hp 0 h0
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (progress R hΔ h1 (Or.inl
      fun ⟨a, b, ha, hb, hab⟩ =>
        hab ((prop_input hR hs hp ha).trans (prop_input hR hs hp hb).symm)))
    exact ⟨w, 0 + δ + Δ, by omega, by rw [decide_eq]; exact hw⟩

omit h3 in
include hΔ in
/-- **Good-case latency `Δ + δ` with unsynchronized start** (Definition 6): with an honest
broadcaster, delays `≤ δ` and any clock skew `σ` allowed by `UValid`, every honest process commits
within `Δ + δ` after the broadcaster starts. -/
theorem three_latency_unsync (s : P) (f δ σ : ℕ) :
    LatencyFromStart auth (lateStart (algo (V := V) s Δ)) s (unsyncRuns f δ σ) (Δ + δ) := by
  intro R hV hR hs p hp
  by_cases hps : p = s
  · subst hps
    exact ⟨(R.inp p).1, ustart R p, by omega, by rw [decide_eq]; exact dec_init R p Δ⟩
  · have h0 : Tok.prop s (R.inp s).1 ∈ (ist s Δ R s (ustart R s)).known := by
      rw [ist_start, init_eq]; simp
    have h1 := gossipU R hV hs hp (ustart R s) h0
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp (progress R hΔ h1 (Or.inl
      fun ⟨a, b, ha, hb, hab⟩ =>
        hab ((prop_input hR hs hp ha).trans (prop_input hR hs hp hb).symm)))
    exact ⟨w, ustart R s + δ + Δ, by omega, by rw [decide_eq]; exact hw⟩

end Main

/-! ### Theorem 10 fails for `n = 3` -/

/-- **Theorem 10 of [ANRX21] is false for `n = 3`.** Under all other hypotheses of
`Thm10.theorem_10` (`δ = 2e ≥ 2`, `δ < Δ`, `n ≤ 3f − 1`, i.e. `f > n/3`), there is a BRB protocol
for the unsynchronized-start model (skew `≤ δ/2`) whose good-case latency is below `Δ + 1.5δ`:
every honest process commits by time `Δ + δ ≤ Δ + 1.5δ − 1`, both in good-case runs with
synchronized start (the form refuting `Thm10.theorem_10`) and, as in Definition 6, in good-case runs
with unsynchronized start (skew `≤ δ/2`), measured from the broadcaster's start. Note that `n = 3`
lies outside the paper's intended range `n/3 < f < n/2`: this refutes only the literal hypothesis
`f > n/3`. -/
theorem theorem_10_false_three (h3 : Fintype.card P = 3) (s : P) {f e Δ : ℕ} (he : 1 ≤ e)
    (hΔ : 2 * e < Δ) (_hn : Fintype.card P ≤ 3 * f - 1) :
    ∃ (A : Algorithm P (Finset (Tok P V)) (St P V) V V)
      (Au : Auth P (Finset (Tok P V)) (Tok P V)),
      (lateStart A).Unforging Au ∧ IsBRBU Au A s (unsyncRuns f Δ e) ∧
      LatencyWithin Au (lateStart A) s (unsyncGood (M := Finset (Tok P V)) f (2 * e))
        (Δ + 3 * e - 1) ∧
      LatencyFromStart Au (lateStart A) s (unsyncRuns (M := Finset (Tok P V)) f (2 * e) e)
        (Δ + 3 * e - 1) := by
  refine ⟨algo s Δ, auth, unforging, three_brb h3 (by omega) s f e, ?_, ?_⟩
  · intro R hR hA hs p hp
    obtain ⟨v, τ, hτ, h⟩ :=
      three_latency (V := V) (Δ := Δ) (by omega) s f (2 * e) R hR hA hs p hp
    exact ⟨v, τ, by omega, h⟩
  · intro R hR hA hs p hp
    obtain ⟨v, τ, hτ, h⟩ :=
      three_latency_unsync (V := V) (Δ := Δ) (by omega) s f (2 * e) e R hR hA hs p hp
    exact ⟨v, τ, by omega, h⟩

/-- The hypothesis `4 ≤ n` of `Thm10.theorem_10` cannot be dropped: its statement with `n = 3`
instead is false (already for `f = 2`, `e = 1`, `Δ = 3`). -/
theorem theorem_10_n4_necessary (h3 : Fintype.card P = 3) (s : P) :
    ¬ ∀ (A : Algorithm P (Finset (Tok P V)) (St P V) V V)
      (Au : Auth P (Finset (Tok P V)) (Tok P V)) (f e Δ : ℕ), (lateStart A).Unforging Au →
      1 ≤ e → 2 * e < Δ → Fintype.card P ≤ 3 * f - 1 → IsBRBU Au A s (unsyncRuns f Δ e) →
      ¬ LatencyWithin Au (lateStart A) s (unsyncGood (M := Finset (Tok P V)) f (2 * e))
        (Δ + 3 * e - 1) := by
  intro H
  obtain ⟨A, Au, hU, hA, hL, -⟩ :=
    theorem_10_false_three (V := V) h3 s (f := 2) (e := 1) (Δ := 3) le_rfl (by omega) (by omega)
  exact H A Au 2 1 3 hU le_rfl (by omega) (by omega) hA hL

end ThreeParties

end GoodCaseLatencyBB
