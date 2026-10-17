import Papers.PODC2019.VABA.Invariants

/-!
# VABA: safety (agreement and external validity)

We prove, for every reachable state of the protocol model (`Model.lean`) and every certificate
threshold `Q` with `n + f < 2Q` (for the paper's `n = 3f + 1`, `Q = 2f + 1`):

* PB-provability and Lemma 6: certificates of one broadcast instance carry one value
  (`Inv.qc_agree`);
* Lemmas 8, 9, 14, 22: if a leader's broadcast has a stage-`i` certificate, every party that has
  left that view processed a stage-`(i-1)` certificate (`lock_of_commitQC`, `key_of_lockQC`,
  `decide_of_completed`);
* Lemma 12 (key safety, `Inv.key_safety`), Lemma 13 (agreement, `agreement`) and Corollary 16
  (external validity, `validity`);
* Lemma 21: a skip certificate implies `Q` completed broadcasts (`completed_of_skipQC`).
-/

namespace VABA

open Finset

variable {P V : Type*} [Fintype P] [DecidableEq P] {C : Cfg P V} {s : Glob P V}

namespace Inv

variable (hQ : Fintype.card P + C.f < 2 * C.Q) (I : Inv C s)
include hQ I

/-- A certificate has a signer that is honest now. -/
lemma honest_signer {st : Stmt P V} (h : QC C.Q s st) : ∃ p, p ∉ s.corrupt ∧ s.tok p st := by
  obtain ⟨p, hp, hc⟩ := exists_honest hQ h I.card_corrupt
  exact ⟨p, hc, mem_signers.mp hp⟩

/-- Two certificates have a common signer that is honest now. -/
lemma common_signer {st st' : Stmt P V} (h : QC C.Q s st) (h' : QC C.Q s st') :
    ∃ p, p ∉ s.corrupt ∧ s.tok p st ∧ s.tok p st' := by
  obtain ⟨p, hp, hp', hc⟩ := exists_honest_inter hQ h h' I.card_corrupt
  exact ⟨p, hc, mem_signers.mp hp, mem_signers.mp hp'⟩

/-- Lemmas 4–5: a stage-`st` certificate (`st ≥ 2`) implies a stage-`(st-1)` certificate on the
same value. -/
lemma qc_pred {j : ℕ} {k : P} {st : ℕ} {v : V} (h : QC C.Q s (.pb j k st v)) (hst : st ≠ 1) :
    QC C.Q s (.pb j k (st - 1) v) := by
  obtain ⟨p, hp, ht⟩ := honest_signer hQ I h
  rw [I.tok_pb p hp] at ht
  exact (I.d_spec p j k st v ht).2.2 hst

/-- A certificate of any stage `≤ 4`... implies a stage-1 certificate on the same value. -/
lemma qc_stage1 {j : ℕ} {k : P} {v : V} :
    ∀ st, 1 ≤ st → QC C.Q s (.pb j k st v) → QC C.Q s (.pb j k 1 v)
  | 0, h1, _ => absurd h1 (by norm_num)
  | 1, _, h => h
  | st + 2, _, h => by
    have := qc_pred hQ I h (by omega)
    exact qc_stage1 (st + 1) (by omega) (by simpa using this)

/-- PB-provability (1): two certificates on the same stage of the same instance agree. -/
lemma qc_unique {j : ℕ} {k : P} {st : ℕ} {v w : V} (h : QC C.Q s (.pb j k st v))
    (h' : QC C.Q s (.pb j k st w)) : v = w := by
  obtain ⟨p, hp, ht, ht'⟩ := common_signer hQ I h h'
  rw [I.tok_pb p hp] at ht ht'
  rw [ht] at ht'; exact Option.some.inj ht'

/-- Lemma 6: certificates of any stages of one broadcast instance carry the same value. -/
lemma qc_agree {j : ℕ} {k : P} {st st' : ℕ} {v w : V} (hst : 1 ≤ st) (hst' : 1 ≤ st')
    (h : QC C.Q s (.pb j k st v)) (h' : QC C.Q s (.pb j k st' w)) : v = w :=
  qc_unique hQ I (qc_stage1 hQ I st hst h) (qc_stage1 hQ I st' hst' h')

/-- Lemma 12 (key safety): if a leader's broadcast of view `j₀` has a stage-3 (commit)
certificate on `v`, then every stage-1 (key) certificate of the leader of any view `j ≥ j₀` is on
`v`. -/
lemma key_safety {j0 : ℕ} {l0 : P} {v : V} (hl0 : s.rev j0 = some l0)
    (h3 : QC C.Q s (.pb j0 l0 3 v)) :
    ∀ j, j0 ≤ j → ∀ l w, s.rev j = some l → QC C.Q s (.pb j l 1 w) → w = v := by
  have hj0 : 1 ≤ j0 := by
    rcases Nat.eq_zero_or_pos j0 with h | h
    · rw [h, I.rev_zero] at hl0; simp at hl0
    · exact h
  have h1 : QC C.Q s (.pb j0 l0 1 v) := qc_stage1 hQ I 3 (by norm_num) h3
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj l w hl hw
  rcases Nat.eq_or_lt_of_le hj with rfl | hlt
  · rw [hl0] at hl; cases hl
    exact qc_unique hQ I hw h1
  · -- an honest signer `p` of the key certificate of view `j`
    obtain ⟨p, hp, ht⟩ := honest_signer hQ I hw
    rw [I.tok_pb p hp] at ht
    obtain ⟨hjv, hkey, -⟩ := I.d_spec p j l 1 w ht
    obtain ⟨-, hkv⟩ := hkey rfl
    -- `p` left view `j0`; its exit set meets the stage-3 signers in an honest party `h`
    have hpast : Past (s.loc p) j0 := Or.inl (by omega)
    obtain ⟨l', hl'⟩ := Option.isSome_iff_exists.mp (I.lead_some p j0 hj0 hpast)
    have : l' = l0 := by
      have := (I.lead_spec p j0 l' hl').2; rw [hl0] at this; exact (Option.some.inj this).symm
    subst this
    obtain ⟨h, hex, hsig, hc⟩ :=
      exists_honest_inter hQ (I.exitR_card p j0 hj0 (by omega)) h3 I.card_corrupt
    rw [mem_signers, I.tok_pb h hc] at hsig
    have hge := I.kv_spec p j l w ht j0 l' hlt hl' h hex hc v hsig
    rcases hkv with h0 | ⟨-, hlt', l'', hl'', hq⟩
    · omega
    · exact ih _ hlt' hge l'' w hl'' hq

/-- Lemmas 8–9: if the leader's broadcast of view `j` has a stage-3 (commit) certificate, every
party that has left view `j` has `LOCK ≥ j`. -/
lemma lock_of_commitQC {j : ℕ} {l : P} {v : V} (hl : s.rev j = some l)
    (h3 : QC C.Q s (.pb j l 3 v)) {p : P} (hp : j < (s.loc p).view) : j ≤ (s.loc p).lock := by
  have hj : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, I.rev_zero] at hl; simp at hl
    · exact h
  obtain ⟨h, hex, hsig, hc⟩ :=
    exists_honest_inter hQ (I.exitR_card p j hj hp) h3 I.card_corrupt
  rw [mem_signers, I.tok_pb h hc] at hsig
  obtain ⟨-, l', hl', hv⟩ := I.rcvd_spec p j h (I.exitR_sub p j hex) hc
  have : l' = l := by
    have := (I.lead_spec p j l' hl').2; rw [hl] at this; exact (Option.some.inj this).symm
  subst this
  exact (hv v).2.1 hsig

/-- Lemmas 8 and 14: if the leader's broadcast of view `j` has a stage-2 (lock) certificate,
every party that has left view `j` has a `KEY` of view `≥ j`. -/
lemma key_of_lockQC {j : ℕ} {l : P} {v : V} (hl : s.rev j = some l)
    (h2 : QC C.Q s (.pb j l 2 v)) {p : P} (hp : j < (s.loc p).view) : j ≤ (s.loc p).key.1 := by
  have hj : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, I.rev_zero] at hl; simp at hl
    · exact h
  obtain ⟨h, hex, hsig, hc⟩ :=
    exists_honest_inter hQ (I.exitR_card p j hj hp) h2 I.card_corrupt
  rw [mem_signers, I.tok_pb h hc] at hsig
  obtain ⟨-, l', hl', hv⟩ := I.rcvd_spec p j h (I.exitR_sub p j hex) hc
  have : l' = l := by
    have := (I.lead_spec p j l' hl').2; rw [hl] at this; exact (Option.some.inj this).symm
  subst this
  exact (hv v).1 hsig

/-- Lemma 22: if the leader's broadcast of view `j` has a stage-4 certificate (it *completed*),
every party that has left view `j` has decided its value. -/
lemma decide_of_completed {j : ℕ} {l : P} {v : V} (hl : s.rev j = some l)
    (h4 : QC C.Q s (.pb j l 4 v)) {p : P} (hp : j < (s.loc p).view) : v ∈ (s.loc p).decs := by
  have hj : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, I.rev_zero] at hl; simp at hl
    · exact h
  obtain ⟨h, hex, hsig, hc⟩ := exists_honest_inter hQ (I.exitR_card p j hj hp) h4 I.card_corrupt
  rw [mem_signers, I.tok_pb h hc] at hsig
  obtain ⟨-, l', hl', hv⟩ := I.rcvd_spec p j h (I.exitR_sub p j hex) hc
  have : l' = l := by
    have := (I.lead_spec p j l' hl').2; rw [hl] at this; exact (Option.some.inj this).symm
  subst this
  exact (hv v).2.2 hsig

/-- Lemma 21: a skip certificate for view `j` implies that `Q` broadcasts of view `j` have a
stage-4 certificate. -/
lemma completed_of_skipQC {j : ℕ} (h : QC C.Q s (.skip j)) : C.Q ≤ (completed C.Q s j).card := by
  obtain ⟨p, hp, ht⟩ := honest_signer hQ I h
  exact I.tok_skip p hp j ht

/-- Commit certificates of leaders of any two views carry the same value. -/
lemma commitQC_agree {j j' : ℕ} {l l' : P} {v w : V} (hl : s.rev j = some l)
    (hl' : s.rev j' = some l') (h : QC C.Q s (.pb j l 3 v)) (h' : QC C.Q s (.pb j' l' 3 w)) :
    v = w := by
  rcases le_total j j' with hjj | hjj
  · exact (key_safety hQ I hl h j' hjj l' w hl' (qc_stage1 hQ I 3 (by norm_num) h')).symm
  · exact key_safety hQ I hl' h' j hjj l v hl (qc_stage1 hQ I 3 (by norm_num) h)

end Inv

/-- **Agreement** (Lemma 13). In every reachable state, all values decided by parties (while they
were honest) are equal; `n + f < 2Q` holds for the paper's `n = 3f + 1`, `Q = 2f + 1`. -/
theorem agreement (hQ : Fintype.card P + C.f < 2 * C.Q) (hR : Reach C s) {p q : P} {v w : V}
    (hv : v ∈ (s.loc p).decs) (hw : w ∈ (s.loc q).decs) : v = w := by
  have I := hR.inv
  obtain ⟨j, l, hl, h⟩ := I.decs_spec p v hv
  obtain ⟨j', l', hl', h'⟩ := I.decs_spec q w hw
  exact I.commitQC_agree hQ hl hl' h h'

/-- **External validity** (Corollary 16). Every decided value is externally valid. -/
theorem validity (hQ : Fintype.card P + C.f < 2 * C.Q) (hR : Reach C s) {p : P} {v : V}
    (hv : v ∈ (s.loc p).decs) : C.valid v := by
  have I := hR.inv
  obtain ⟨j, l, -, h⟩ := I.decs_spec p v hv
  obtain ⟨q, hq, ht⟩ := I.honest_signer hQ (I.qc_stage1 hQ 3 (by norm_num) h)
  rw [I.tok_pb q hq] at ht
  exact ((I.d_spec q j l 1 v ht).2.1 rfl).1

end VABA
