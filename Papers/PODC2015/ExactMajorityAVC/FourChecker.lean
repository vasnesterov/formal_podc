import Papers.PODC2015.ExactMajorityAVC.FourClaims

/-!
# A certificate checker for the case analysis of Theorem B.1

After Claim B.5 the transitions between states of the same output are known; the remaining
freedom of a symmetric four-state protocol is the outcome of the four "cross" pairs. The case
analysis of the paper (Claims B.6, B.7 and Cases 1–3) refutes all outcomes except those keeping
`#S0 − #S1` invariant. We replay it as a *certified case tree* (`Tree`): every node splits on the
outcome of one pair (all ten possible outcomes), every leaf either

* refutes the current partial transition table by a certificate (`Cert`):
  - `b2`: two initial configurations of the same size with different numbers of `S0` reach a
    common configuration (contradicting Claim B.2);
  - `safe`: an initial configuration with majority `S i` reaches a closed set of configurations
    in which all agents output `!i` (contradicting the second correctness property);
  - `live`: an initial configuration with majority `S i` reaches a closed set of configurations
    none of which has all outputs equal to `i` (contradicting the third property); or
* checks that the (now complete) table preserves `#S0 − #S1` (`inv`).

`checkTree_sound` proves that a successful check implies `Invariant P` for every symmetric
correct protocol agreeing with the starting table. Configurations in certificates are count
vectors (`Cnt`), so that the check runs by `decide` in the kernel.
-/

namespace Podc.ExactMajorityAVC.Four

open Cslib.PopulationProtocol Q4 Multiset

/-- Count vectors of configurations. -/
structure Cnt where
  /-- number of agents in `S0` -/
  s0 : ℕ
  /-- number of agents in `S1` -/
  s1 : ℕ
  /-- number of agents in `X` -/
  x : ℕ
  /-- number of agents in `Y` -/
  y : ℕ
  deriving DecidableEq, Repr

namespace Cnt

/-- The number of agents in state `q`. -/
def get (c : Cnt) : Q4 → ℕ
  | S0 => c.s0
  | S1 => c.s1
  | X => c.x
  | Y => c.y

/-- Add an agent in state `q`. -/
def inc (c : Cnt) : Q4 → Cnt
  | S0 => ⟨c.s0 + 1, c.s1, c.x, c.y⟩
  | S1 => ⟨c.s0, c.s1 + 1, c.x, c.y⟩
  | X => ⟨c.s0, c.s1, c.x + 1, c.y⟩
  | Y => ⟨c.s0, c.s1, c.x, c.y + 1⟩

/-- Remove an agent in state `q`. -/
def dec (c : Cnt) : Q4 → Cnt
  | S0 => ⟨c.s0 - 1, c.s1, c.x, c.y⟩
  | S1 => ⟨c.s0, c.s1 - 1, c.x, c.y⟩
  | X => ⟨c.s0, c.s1, c.x - 1, c.y⟩
  | Y => ⟨c.s0, c.s1, c.x, c.y - 1⟩

/-- The multiset configuration of a count vector. -/
def toMS (c : Cnt) : Multiset Q4 :=
  replicate c.s0 S0 + replicate c.s1 S1 + replicate c.x X + replicate c.y Y

lemma count_toMS (c : Cnt) (q : Q4) : count q c.toMS = c.get q := by
  cases q <;> simp [toMS, get, count_replicate]

lemma get_inc (c : Cnt) (p q : Q4) : (c.inc p).get q = c.get q + if q = p then 1 else 0 := by
  cases p <;> cases q <;> rfl

lemma get_dec (c : Cnt) (p q : Q4) : (c.dec p).get q = c.get q - if q = p then 1 else 0 := by
  cases p <;> cases q <;> rfl

lemma toMS_inc (c : Cnt) (p : Q4) : (c.inc p).toMS = p ::ₘ c.toMS := by
  ext q; rw [count_toMS, get_inc, count_cons, count_toMS]

lemma toMS_dec {c : Cnt} {p : Q4} (h : 1 ≤ c.get p) : c.toMS = p ::ₘ (c.dec p).toMS := by
  ext q; rw [count_cons, count_toMS, count_toMS, get_dec]
  split_ifs with hq
  · subst hq; omega
  · omega

end Cnt

/-- Table entries: the pair `(p, q)` interacts into the multiset `{a, b}`. -/
abbrev Entry := (Q4 × Q4) × (Q4 × Q4)

/-- Look up the outcome of the unordered pair `{p, q}`. -/
def lookup : List Entry → Q4 → Q4 → Option (Q4 × Q4)
  | [], _, _ => none
  | e :: t, p, q =>
    if (e.1.1 = p ∧ e.1.2 = q) ∨ (e.1.1 = q ∧ e.1.2 = p) then some e.2 else lookup t p q

/-- The protocol agrees with the table. -/
def Agrees (P : Protocol Q4) (tbl : List Entry) : Prop :=
  ∀ e ∈ tbl, pair (P.δ e.1.1 e.1.2) = pair e.2

variable {P : Protocol Q4} {γ : Q4 → Bool}

lemma lookup_sound (hS : Symmetric P) :
    ∀ {tbl : List Entry}, Agrees P tbl → ∀ {p q : Q4} {o : Q4 × Q4}, lookup tbl p q = some o →
      pair (P.δ p q) = pair o
  | [], _, _, _, _, h => by simp [lookup] at h
  | e :: t, hA, p, q, o, h => by
    simp only [lookup] at h
    split_ifs at h with he
    · cases h
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hA e (by simp)
      · rw [hS]; exact hA e (by simp)
    · exact lookup_sound hS (fun e' he' => hA e' (by simp [he'])) h

/-- Fire the pair `(p, q)` in `c`, if both are present and the outcome is in the table. -/
def fire (tbl : List Entry) (c : Cnt) (p q : Q4) : Option Cnt :=
  if 1 ≤ c.get p ∧ 1 ≤ (c.dec p).get q then
    match lookup tbl p q with
    | some o => some (((c.dec p).dec q).inc o.1 |>.inc o.2)
    | none => none
  else none

lemma fire_spec {tbl : List Entry} {c c' : Cnt} {p q : Q4} (h : fire tbl c p q = some c') :
    ∃ o, lookup tbl p q = some o ∧ c.toMS = p ::ₘ q ::ₘ ((c.dec p).dec q).toMS ∧
      c'.toMS = o.2 ::ₘ o.1 ::ₘ ((c.dec p).dec q).toMS := by
  unfold fire at h
  split_ifs at h with hc
  split at h
  · rename_i o ho
    cases h
    refine ⟨o, ho, ?_, by rw [Cnt.toMS_inc, Cnt.toMS_inc]⟩
    rw [Cnt.toMS_dec hc.1, Cnt.toMS_dec hc.2]
  · cases h

lemma fire_sound (hS : Symmetric P) {tbl : List Entry} (hA : Agrees P tbl) {c c' : Cnt}
    {p q : Q4} (h : fire tbl c p q = some c') : MStep (trans P) c.toMS c'.toMS := by
  obtain ⟨o, ho, h1, h2⟩ := fire_spec h
  have hp := lookup_sound hS hA ho
  rw [h1, h2]
  have := step_of (P := P) p q ((c.dec p).dec q).toMS
  convert this using 1
  have e1 : (P.δ p q).1 ::ₘ (P.δ p q).2 ::ₘ ((c.dec p).dec q).toMS =
      pair (P.δ p q) + ((c.dec p).dec q).toMS := by simp [pair, insert_eq_cons]
  rw [e1, hp]; simp [pair, insert_eq_cons, cons_swap]

/-- Fire a sequence of pairs. -/
def run (tbl : List Entry) : Cnt → List (Q4 × Q4) → Option Cnt
  | c, [] => some c
  | c, z :: π =>
    match fire tbl c z.1 z.2 with
    | some c' => run tbl c' π
    | none => none

lemma run_sound (hS : Symmetric P) {tbl : List Entry} (hA : Agrees P tbl) :
    ∀ {π : List (Q4 × Q4)} {c c' : Cnt}, run tbl c π = some c' → Reach P c.toMS c'.toMS
  | [], c, c', h => by simp [run] at h; subst h; exact .refl
  | z :: π, c, c', h => by
    simp only [run] at h
    split at h
    · rename_i c'' hf
      exact Relation.ReflTransGen.head (fire_sound hS hA hf) (run_sound hS hA h)
    · cases h

/-- The four states, as a list. -/
def allQ : List Q4 := [S0, S1, X, Y]

lemma mem_allQ (q : Q4) : q ∈ allQ := by cases q <;> simp [allQ]

/-- `F` is closed under all interactions (and all outcomes needed are in the table). -/
def closedCheck (tbl : List Entry) (F : List Cnt) : Bool :=
  F.all fun f => allQ.all fun p => allQ.all fun q =>
    if 1 ≤ f.get p ∧ 1 ≤ (f.dec p).get q then
      match fire tbl f p q with
      | some g => F.contains g
      | none => false
    else true

lemma closed_sound (hS : Symmetric P) {tbl : List Entry} (hA : Agrees P tbl) {F : List Cnt}
    (hF : closedCheck tbl F = true) {f : Cnt} (hf : f ∈ F) {c : Multiset Q4}
    (h : Reach P f.toMS c) : ∃ g ∈ F, c = g.toMS := by
  induction h with
  | refl => exact ⟨f, hf, rfl⟩
  | tail _ hs ih =>
    obtain ⟨g, hg, rfl⟩ := ih
    obtain ⟨p, q, r, hgr, rfl⟩ := exists_of_step hs
    have hp : 1 ≤ g.get p := by
      rw [← Cnt.count_toMS, hgr]; simp
    have hgr' := hgr
    rw [Cnt.toMS_dec hp, cons_inj_right] at hgr'
    have hq : 1 ≤ (g.dec p).get q := by
      rw [← Cnt.count_toMS, hgr']; simp
    have hcheck : (match fire tbl g p q with
        | some g' => F.contains g'
        | none => false) = true := by
      simp only [closedCheck, List.all_eq_true] at hF
      have := hF g hg p (mem_allQ p) q (mem_allQ q)
      simpa only [hp, hq, and_self, ↓reduceIte] using this
    split at hcheck
    · rename_i g' hfire
      refine ⟨g', List.contains_iff_mem.1 hcheck, ?_⟩
      obtain ⟨o, ho, -, h2⟩ := fire_spec hfire
      rw [Cnt.toMS_dec hq, cons_inj_right] at hgr'
      rw [h2, ← hgr']
      have hpo := lookup_sound hS hA ho
      have e1 : ∀ r' : Multiset Q4, (P.δ p q).1 ::ₘ (P.δ p q).2 ::ₘ r' = pair (P.δ p q) + r' := by
        intro r'; simp [pair, insert_eq_cons]
      rw [e1, hpo]; simp [pair, insert_eq_cons, cons_swap]
    · cases hcheck

/-- All agents of `c` output `i`. -/
def allOut (γ' : Q4 → Bool) (i : Bool) (c : Cnt) : Bool :=
  allQ.all fun q => c.get q == 0 || γ' q == i

lemma allOut_sound {γ' : Q4 → Bool} {i : Bool} {c : Cnt} (h : allOut γ' i c = true) :
    ∀ q ∈ c.toMS, γ' q = i := by
  intro q hq
  simp only [allOut, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  rcases h q (mem_allQ q) with h0 | h1
  · rw [← Cnt.count_toMS, count_eq_zero] at h0; exact absurd hq h0
  · exact h1

/-- The count vector of `cfg i a b`. -/
def cfgCnt (i : Bool) (a b : ℕ) : Cnt := if i then ⟨b, a, 0, 0⟩ else ⟨a, b, 0, 0⟩

lemma toMS_cfgCnt (i : Bool) (a b : ℕ) : (cfgCnt i a b).toMS = cfg i a b := by
  cases i <;> simp [cfgCnt, Cnt.toMS, cfg, add_comm]

/-- Certificates refuting a partial transition table. -/
inductive Cert
  /-- `cfg false a b` and `cfg false a' b'` reach a common configuration. -/
  | b2 (a b a' b' : ℕ) (π π' : List (Q4 × Q4))
  /-- `cfg i a b` (`b < a`) reaches the closed set `F` where all agents output `!i`. -/
  | safe (i : Bool) (a b : ℕ) (π : List (Q4 × Q4)) (F : List Cnt)
  /-- `cfg i a b` (`b < a`) reaches the closed set `F` with no configuration of outputs `i`. -/
  | live (i : Bool) (a b : ℕ) (π : List (Q4 × Q4)) (F : List Cnt)

/-- Check a certificate. -/
def checkCert (tbl : List Entry) (γ' : Q4 → Bool) : Cert → Bool
  | .b2 a b a' b' π π' =>
    a + b == a' + b' && a != a' &&
      match run tbl ⟨a, b, 0, 0⟩ π, run tbl ⟨a', b', 0, 0⟩ π' with
      | some c, some c' => c == c'
      | _, _ => false
  | .safe i a b π F =>
    decide (b < a) &&
      (match run tbl (cfgCnt i a b) π with
        | some c => F.contains c
        | none => false) &&
      closedCheck tbl F && F.all (allOut γ' (!i))
  | .live i a b π F =>
    decide (b < a) &&
      (match run tbl (cfgCnt i a b) π with
        | some c => F.contains c
        | none => false) &&
      closedCheck tbl F && F.all (fun f => !allOut γ' i f)

theorem checkCert_sound (hC : Correct P γ) (hS : Symmetric P) {γ' : Q4 → Bool}
    (hγ : ∀ q, γ q = γ' q) {tbl : List Entry} (hA : Agrees P tbl) (cert : Cert)
    (h : checkCert tbl γ' cert = true) : False := by
  cases cert with
  | b2 a b a' b' π π' =>
    simp only [checkCert, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    obtain ⟨⟨hn, ha⟩, h⟩ := h
    split at h
    · rename_i c c' h1 h2
      simp only [beq_iff_eq] at h
      subst h
      have r1 := run_sound hS hA h1
      have r2 := run_sound hS hA h2
      have e1 : (⟨a, b, 0, 0⟩ : Cnt).toMS = cfg false a b := by simp [Cnt.toMS, cfg]
      have e2 : (⟨a', b', 0, 0⟩ : Cnt).toMS = cfg false a' b' := by simp [Cnt.toMS, cfg]
      rw [e1] at r1; rw [e2] at r2
      exact claim_B_2 hC hn ha r1 r2
    · cases h
  | safe i a b π F =>
    simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hab, hrun⟩, hF⟩, hout⟩ := h
    split at hrun
    · rename_i c hc
      have r := run_sound hS hA hc
      rw [toMS_cfgCnt] at r
      refine hC.safe i a b hab _ r fun c' hc' q hq => ?_
      obtain ⟨g, hg, rfl⟩ := closed_sound hS hA hF (List.contains_iff_mem.1 hrun) hc'
      rw [hγ]
      exact allOut_sound (List.all_eq_true.1 hout g hg) q hq
    · cases hrun
  | live i a b π F =>
    simp only [checkCert, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hab, hrun⟩, hF⟩, hout⟩ := h
    split at hrun
    · rename_i c hc
      have r := run_sound hS hA hc
      rw [toMS_cfgCnt] at r
      obtain ⟨c', hc', habs⟩ := hC.live i a b hab _ r
      obtain ⟨g, hg, rfl⟩ := closed_sound hS hA hF (List.contains_iff_mem.1 hrun) hc'
      have hno := List.all_eq_true.1 hout g hg
      simp only [Bool.not_eq_true'] at hno
      have : allOut γ' i g = true := by
        simp only [allOut, List.all_eq_true, Bool.or_eq_true, beq_iff_eq]
        intro q _
        by_cases hq : g.get q = 0
        · exact Or.inl hq
        · right
          rw [← hγ]
          exact habs.mem q (by rw [← Cnt.count_toMS] at hq; exact count_ne_zero.1 hq)
      rw [this] at hno; cases hno
    · cases hrun

/-! ### Invariance check -/

/-- `#S0 − #S1` of a single state. -/
def dq : Q4 → ℤ
  | S0 => 1
  | S1 => -1
  | X => 0
  | Y => 0

lemma diff_pair (z : Q4 × Q4) : diff (pair z) = dq z.1 + dq z.2 := by
  obtain ⟨a, b⟩ := z
  cases a <;> cases b <;> simp [diff, pair, dq, insert_eq_cons]

/-- The table is complete and preserves `#S0 − #S1`. -/
def checkInv (tbl : List Entry) : Bool :=
  allQ.all fun p => allQ.all fun q =>
    match lookup tbl p q with
    | some o => dq o.1 + dq o.2 == dq p + dq q
    | none => false

theorem checkInv_sound (hS : Symmetric P) {tbl : List Entry} (hA : Agrees P tbl)
    (h : checkInv tbl = true) : Invariant P := by
  intro p q
  simp only [checkInv, List.all_eq_true] at h
  have := h p (mem_allQ p) q (mem_allQ q)
  split at this
  · rename_i o ho
    simp only [beq_iff_eq] at this
    rw [lookup_sound hS hA ho, diff_pair, this, ← diff_pair (p, q)]; rfl
  · cases this

/-! ### Case trees -/

/-- A certified case tree. `split p q t₀ … t₉` splits on the outcome of `(p, q)`, in the order
`S0S0, S0S1, S0X, S0Y, S1S1, S1X, S1Y, XX, XY, YY`. -/
inductive Tree
  | cert (c : Cert)
  | inv
  | split (p q : Q4) (t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : Tree)

/-- Check a case tree. -/
def checkTree (γ' : Q4 → Bool) : List Entry → Tree → Bool
  | tbl, .cert c => checkCert tbl γ' c
  | tbl, .inv => checkInv tbl
  | tbl, .split p q t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 =>
    checkTree γ' (((p, q), (S0, S0)) :: tbl) t0 && checkTree γ' (((p, q), (S0, S1)) :: tbl) t1 &&
    checkTree γ' (((p, q), (S0, X)) :: tbl) t2 && checkTree γ' (((p, q), (S0, Y)) :: tbl) t3 &&
    checkTree γ' (((p, q), (S1, S1)) :: tbl) t4 && checkTree γ' (((p, q), (S1, X)) :: tbl) t5 &&
    checkTree γ' (((p, q), (S1, Y)) :: tbl) t6 && checkTree γ' (((p, q), (X, X)) :: tbl) t7 &&
    checkTree γ' (((p, q), (X, Y)) :: tbl) t8 && checkTree γ' (((p, q), (Y, Y)) :: tbl) t9

lemma pair_cases (z : Q4 × Q4) :
    pair z = pair (S0, S0) ∨ pair z = pair (S0, S1) ∨ pair z = pair (S0, X) ∨
    pair z = pair (S0, Y) ∨ pair z = pair (S1, S1) ∨ pair z = pair (S1, X) ∨
    pair z = pair (S1, Y) ∨ pair z = pair (X, X) ∨ pair z = pair (X, Y) ∨
    pair z = pair (Y, Y) := by
  obtain ⟨a, b⟩ := z
  cases a <;> cases b <;> decide

lemma agrees_cons {tbl : List Entry} (hA : Agrees P tbl) {p q : Q4} {o : Q4 × Q4}
    (h : pair (P.δ p q) = pair o) : Agrees P (((p, q), o) :: tbl) := by
  intro e he
  rcases List.mem_cons.1 he with rfl | he
  · exact h
  · exact hA e he

/-- **Soundness of the case tree.** If the tree checks, every symmetric correct protocol
agreeing with the starting table keeps `#S0 − #S1` invariant. -/
theorem checkTree_sound (hC : Correct P γ) (hS : Symmetric P) {γ' : Q4 → Bool}
    (hγ : ∀ q, γ q = γ' q) :
    ∀ (t : Tree) {tbl : List Entry}, Agrees P tbl → checkTree γ' tbl t = true → Invariant P
  | .cert c, _, hA, h => (checkCert_sound hC hS hγ hA c h).elim
  | .inv, _, hA, h => checkInv_sound hS hA h
  | .split p q t0 t1 t2 t3 t4 t5 t6 t7 t8 t9, tbl, hA, h => by
    simp only [checkTree, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
    rcases pair_cases (P.δ p q) with e | e | e | e | e | e | e | e | e | e
    · exact checkTree_sound hC hS hγ t0 (agrees_cons hA e) h0
    · exact checkTree_sound hC hS hγ t1 (agrees_cons hA e) h1
    · exact checkTree_sound hC hS hγ t2 (agrees_cons hA e) h2
    · exact checkTree_sound hC hS hγ t3 (agrees_cons hA e) h3
    · exact checkTree_sound hC hS hγ t4 (agrees_cons hA e) h4
    · exact checkTree_sound hC hS hγ t5 (agrees_cons hA e) h5
    · exact checkTree_sound hC hS hγ t6 (agrees_cons hA e) h6
    · exact checkTree_sound hC hS hγ t7 (agrees_cons hA e) h7
    · exact checkTree_sound hC hS hγ t8 (agrees_cons hA e) h8
    · exact checkTree_sound hC hS hγ t9 (agrees_cons hA e) h9

end Podc.ExactMajorityAVC.Four
