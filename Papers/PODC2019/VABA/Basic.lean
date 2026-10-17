import Papers.PODC2019.VABA.Model

/-!
# VABA: basic lemmas about the transition system

Simp lemmas for `proc`, `Glob.upd`, `Glob.sign`, monotonicity of certificates, and the quorum
intersection lemma.
-/

namespace VABA

open Finset

variable {P V : Type*}

/-! ### `proc` changes only `key`, `lock`, `decs` -/

section proc
variable (j st : ℕ) (o : Option V) (L : Loc P V)

@[simp] lemma proc_view : (proc j st o L).view = L.view := by
  unfold proc; split <;> (try split_ifs) <;> rfl
@[simp] lemma proc_ph : (proc j st o L).ph = L.ph := by
  unfold proc; split <;> (try split_ifs) <;> rfl
@[simp] lemma proc_lead : (proc j st o L).lead = L.lead := by
  unfold proc; split <;> (try split_ifs) <;> rfl
@[simp] lemma proc_d : (proc j st o L).d = L.d := by
  unfold proc; split <;> (try split_ifs) <;> rfl
@[simp] lemma proc_kv : (proc j st o L).kv = L.kv := by
  unfold proc; split <;> (try split_ifs) <;> rfl
@[simp] lemma proc_rcvd : (proc j st o L).rcvd = L.rcvd := by
  unfold proc; split <;> (try split_ifs) <;> rfl
@[simp] lemma proc_exitR : (proc j st o L).exitR = L.exitR := by
  unfold proc; split <;> (try split_ifs) <;> rfl
@[simp] lemma proc_prop : (proc j st o L).prop = L.prop := by
  unfold proc; split <;> (try split_ifs) <;> rfl

lemma proc_key_mono : L.key.1 ≤ (proc j st o L).key.1 := by
  unfold proc; split
  · exact le_rfl
  · split_ifs <;> simp; omega

lemma proc_lock_mono : L.lock ≤ (proc j st o L).lock := by
  unfold proc; split
  · exact le_rfl
  · split_ifs <;> simp; omega

lemma proc_decs_mono : L.decs ⊆ (proc j st o L).decs := by
  unfold proc; split
  · exact subset_rfl
  · split_ifs <;> simp [Set.subset_insert]

lemma proc_key_of {v : V} (h : o = some v) : j ≤ (proc j 1 o L).key.1 := by
  subst h; unfold proc; split_ifs <;> simp <;> omega

lemma proc_lock_of {v : V} (h : o = some v) : j ≤ (proc j 2 o L).lock := by
  subst h; unfold proc; split_ifs <;> simp <;> omega

lemma proc_decs_of {v : V} (h : o = some v) : v ∈ (proc j 3 o L).decs := by
  subst h; unfold proc; simp

lemma proc_key_cases :
    (proc j st o L).key = L.key ∨ (st = 1 ∧ o = some (proc j st o L).key.2 ∧
      (proc j st o L).key.1 = j) := by
  unfold proc; split
  · exact Or.inl rfl
  · split_ifs <;> simp_all

lemma proc_lock_cases :
    (proc j st o L).lock = L.lock ∨ (st = 2 ∧ o.isSome ∧ (proc j st o L).lock = j) := by
  unfold proc; split
  · exact Or.inl rfl
  · split_ifs <;> simp_all

lemma proc_decs_cases {v : V} (h : v ∈ (proc j st o L).decs) :
    v ∈ L.decs ∨ (st = 3 ∧ o = some v) := by
  unfold proc at h; split at h
  · exact Or.inl h
  · split_ifs at h <;> simp_all
    rcases h with h | h
    · exact Or.inr h.symm
    · exact Or.inl h

end proc

section procVC
variable (j : ℕ) (l : P) (H L : Loc P V)

@[simp] lemma procVC_view : (procVC j l H L).view = L.view := by simp [procVC]
@[simp] lemma procVC_ph : (procVC j l H L).ph = L.ph := by simp [procVC]
@[simp] lemma procVC_lead : (procVC j l H L).lead = L.lead := by simp [procVC]
@[simp] lemma procVC_d : (procVC j l H L).d = L.d := by simp [procVC]
@[simp] lemma procVC_kv : (procVC j l H L).kv = L.kv := by simp [procVC]
@[simp] lemma procVC_rcvd : (procVC j l H L).rcvd = L.rcvd := by simp [procVC]
@[simp] lemma procVC_exitR : (procVC j l H L).exitR = L.exitR := by simp [procVC]
@[simp] lemma procVC_prop : (procVC j l H L).prop = L.prop := by simp [procVC]

lemma procVC_key_mono : L.key.1 ≤ (procVC j l H L).key.1 := by
  unfold procVC
  refine (proc_key_mono _ _ _ _).trans ((proc_key_mono _ _ _ _).trans (proc_key_mono _ _ _ _))

lemma procVC_lock_mono : L.lock ≤ (procVC j l H L).lock := by
  unfold procVC
  refine (proc_lock_mono _ _ _ _).trans ((proc_lock_mono _ _ _ _).trans (proc_lock_mono _ _ _ _))

lemma procVC_decs_mono : L.decs ⊆ (procVC j l H L).decs := by
  unfold procVC
  exact (proc_decs_mono _ _ _ _).trans ((proc_decs_mono _ _ _ _).trans (proc_decs_mono _ _ _ _))

lemma procVC_key_of {v : V} (h : H.d j l 2 = some v) : j ≤ (procVC j l H L).key.1 := by
  unfold procVC
  exact (proc_key_of j _ L h).trans ((proc_key_mono _ _ _ _).trans (proc_key_mono _ _ _ _))

lemma procVC_lock_of {v : V} (h : H.d j l 3 = some v) : j ≤ (procVC j l H L).lock := by
  unfold procVC
  exact (proc_lock_of j _ _ h).trans (proc_lock_mono _ _ _ _)

lemma procVC_decs_of {v : V} (h : H.d j l 4 = some v) : v ∈ (procVC j l H L).decs := by
  unfold procVC
  exact proc_decs_of j _ _ h

lemma procVC_key_cases :
    (procVC j l H L).key = L.key ∨ (H.d j l 2 = some (procVC j l H L).key.2 ∧
      (procVC j l H L).key.1 = j) := by
  unfold procVC
  rcases proc_key_cases j 3 (H.d j l 4) (proc j 2 (H.d j l 3) (proc j 1 (H.d j l 2) L)) with
    h3 | h3
  · rcases proc_key_cases j 2 (H.d j l 3) (proc j 1 (H.d j l 2) L) with h2 | h2
    · rcases proc_key_cases j 1 (H.d j l 2) L with h1 | h1
      · left; rw [h3, h2, h1]
      · right; rw [h3, h2]; exact ⟨h1.2.1, h1.2.2⟩
    · simp at h2
  · simp at h3

lemma procVC_lock_cases :
    (procVC j l H L).lock = L.lock ∨ ((H.d j l 3).isSome ∧ (procVC j l H L).lock = j) := by
  unfold procVC
  rcases proc_lock_cases j 3 (H.d j l 4) (proc j 2 (H.d j l 3) (proc j 1 (H.d j l 2) L)) with
    h3 | h3
  · rcases proc_lock_cases j 2 (H.d j l 3) (proc j 1 (H.d j l 2) L) with h2 | h2
    · rcases proc_lock_cases j 1 (H.d j l 2) L with h1 | h1
      · left; rw [h3, h2, h1]
      · simp at h1
    · right; rw [h3]; exact ⟨h2.2.1, h2.2.2⟩
  · simp at h3

lemma procVC_decs_cases {v : V} (h : v ∈ (procVC j l H L).decs) :
    v ∈ L.decs ∨ H.d j l 4 = some v := by
  unfold procVC at h
  rcases proc_decs_cases _ _ _ _ h with h | h
  · rcases proc_decs_cases _ _ _ _ h with h | h
    · rcases proc_decs_cases _ _ _ _ h with h | h
      · exact Or.inl h
      · simp at h
    · simp at h
  · exact Or.inr h.2

end procVC

/-! ### `Glob.upd`, `Glob.sign` -/

section upd
variable [DecidableEq P]

@[simp] lemma upd_loc (s : Glob P V) (p q : P) (L : Loc P V) :
    (s.upd p L).loc q = if q = p then L else s.loc q := by
  simp [Glob.upd, Function.update_apply]
@[simp] lemma upd_corrupt (s : Glob P V) (p : P) (L : Loc P V) :
    (s.upd p L).corrupt = s.corrupt := rfl
@[simp] lemma upd_tok (s : Glob P V) (p : P) (L : Loc P V) : (s.upd p L).tok = s.tok := rfl
@[simp] lemma upd_rev (s : Glob P V) (p : P) (L : Loc P V) : (s.upd p L).rev = s.rev := rfl
end upd

@[simp] lemma sign_loc (s : Glob P V) (p : P) (st : Stmt P V) : (s.sign p st).loc = s.loc := rfl
@[simp] lemma sign_corrupt (s : Glob P V) (p : P) (st : Stmt P V) :
    (s.sign p st).corrupt = s.corrupt := rfl
@[simp] lemma sign_rev (s : Glob P V) (p : P) (st : Stmt P V) : (s.sign p st).rev = s.rev := rfl
@[simp] lemma sign_tok (s : Glob P V) (p q : P) (st x : Stmt P V) :
    (s.sign p st).tok q x ↔ s.tok q x ∨ (q = p ∧ x = st) := Iff.rfl


/-! ### Certificates -/

variable [Fintype P]

lemma signers_mono {s s' : Glob P V} (h : ∀ p x, s.tok p x → s'.tok p x) (st : Stmt P V) :
    signers s st ⊆ signers s' st := by
  intro p; simp only [mem_signers]; exact h p st

lemma QC_mono {Q : ℕ} {s s' : Glob P V} (h : ∀ p x, s.tok p x → s'.tok p x) {st : Stmt P V}
    (hq : QC Q s st) : QC Q s' st :=
  hq.trans (card_le_card (signers_mono h st))

lemma mem_completed {Q : ℕ} {s : Glob P V} {j : ℕ} {k : P} :
    k ∈ completed Q s j ↔ ∃ v, QC Q s (.pb j k 4 v) := by
  classical simp [completed]

lemma completed_mono {Q : ℕ} {s s' : Glob P V} (h : ∀ p x, s.tok p x → s'.tok p x) (j : ℕ) :
    completed Q s j ⊆ completed Q s' j := by
  intro k; simp only [mem_completed]
  rintro ⟨v, hv⟩; exact ⟨v, QC_mono h hv⟩

/-- Quorum intersection: two sets of size `≥ Q` with `n + f < 2Q` share a party outside any set
of at most `f` corrupted parties. -/
lemma exists_honest_inter [DecidableEq P] {Q f : ℕ} (hQ : Fintype.card P + f < 2 * Q) {A B X : Finset P}
    (hA : Q ≤ A.card) (hB : Q ≤ B.card) (hX : X.card ≤ f) : ∃ h ∈ A, h ∈ B ∧ h ∉ X := by
  by_contra hcon
  push Not at hcon
  have hsub : A ∩ B ⊆ X := by
    intro h hh; rw [mem_inter] at hh; exact hcon h hh.1 hh.2
  have h1 := card_union_add_card_inter A B
  have h2 : (A ∪ B).card ≤ Fintype.card P := card_le_univ _
  have h3 := card_le_card hsub
  omega

/-- A set of size `≥ Q` contains a party outside a set of at most `f` corrupted parties. -/
lemma exists_honest [DecidableEq P] {Q f : ℕ} (hQ : Fintype.card P + f < 2 * Q) {A X : Finset P}
    (hA : Q ≤ A.card) (hX : X.card ≤ f) : ∃ h ∈ A, h ∉ X := by
  obtain ⟨h, hA', -, hX'⟩ := exists_honest_inter hQ hA hA hX
  exact ⟨h, hA', hX'⟩

end VABA
