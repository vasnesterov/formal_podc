import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Signing

/-!
# Safety of the view-based protocol (Lemmas B.1–B.3)

`Sup th σ`: at least `th - f` honest parties signed `σ` (every valid `th`-certificate held by an
honest party gives this, `sup_of_cert`). With `k = ⌈(n+t+1)/2⌉` and `2t < n`, two such sets of
honest parties intersect (`quorum`). Hence:

* `key_unique` (**Lemma B.1** for keys): one value per view gets key certificates;
* `lock_sup_key`, `commit_sup_lock`: a lock (commit) certificate implies a key (lock) certificate;
* `key_after_commit` (**Lemma B.2**): after a commit certificate for `b` in view `v`, every key
  certificate of a view `≥ v` is for `b`;
* `commit_unique` (**Lemma B.3**): all commit certificates are for the same value.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {s : Scenario (Fin n) Bool (Msg n)}

/-- Signatures are produced before round `R₀`. -/
lemma Signed.toR0 {q : Fin n} {σ : Stmt} {r : ℕ} (h : Signed π s q σ r) :
    Signed π s q σ (R0 n) := by
  obtain ⟨r', hr', hm⟩ := h
  refine ⟨r', ?_, hm⟩
  rcases ownToks_cases hm with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> (unfold R0; unfold Rh at h1; omega)

variable (π s) in
/-- At least `th - f` honest parties signed `σ`. -/
def Sup (th : ℕ) (σ : Stmt) : Prop := th ≤ (signers π s σ (R0 n)).card + (byzF s).card

/-- The standing assumptions of the safety arguments. -/
structure Good (π : Params n) (s : Scenario (Fin n) Bool (Msg n)) : Prop where
  rel : s.Reliable
  auth : s.AuthValid (G n) (stageA π) auth
  res : 2 * π.t < n
  faults : (byzF s).card ≤ π.t

variable (hg : Good π s)
include hg

lemma sup_of_cert {r : ℕ} {p : Fin n} (hp : p ∉ s.byz) {th : ℕ} {σ : Stmt} {c : Cert n}
    (hv : Valid n th σ c) (hc : ∀ τ ∈ c, τ ∈ (S π s r p).toks) : Sup π s th σ := by
  have h := card_signers_of_valid hg.rel hg.auth hp hv hc
  have hsub : signers π s σ r ⊆ signers π s σ (R0 n) := by
    intro q hq; rw [mem_signers] at hq ⊢; exact ⟨hq.1, hq.2.toR0⟩
  unfold Sup; have := card_le_card hsub; omega

omit hg in
lemma k_spec : n + π.t + 1 ≤ 2 * π.k := by unfold Params.k; omega

lemma t_lt_k : π.t < π.k := by have := k_spec (π := π); have := hg.res; omega

lemma card_honest_le (A : Finset (Fin n)) (hA : ∀ q ∈ A, q ∉ s.byz) :
    A.card + (byzF s).card ≤ n := by
  have hd : Disjoint A (byzF s) := by
    rw [Finset.disjoint_left]; intro q hq hb; exact hA q hq (mem_byzF.1 hb)
  have := card_union_of_disjoint hd
  have := card_le_univ (A ∪ byzF s)
  simp at *; omega

/-- **Quorum intersection.** Two sets of honest parties, each of size `≥ k - f`, intersect. -/
lemma quorum (A B : Finset (Fin n)) (hA : ∀ q ∈ A, q ∉ s.byz) (hB : ∀ q ∈ B, q ∉ s.byz)
    (hAk : π.k ≤ A.card + (byzF s).card) (hBk : π.k ≤ B.card + (byzF s).card) :
    ∃ q, q ∈ A ∧ q ∈ B := by
  by_contra hne
  push_neg at hne
  have hd : Disjoint A B := Finset.disjoint_left.2 fun q hq hq' => hne q hq hq'
  have h1 := card_honest_le hg (A ∪ B) (by
    intro q hq; rcases mem_union.1 hq with h | h; exacts [hA q h, hB q h])
  rw [card_union_of_disjoint hd] at h1
  have := k_spec (π := π); have := hg.faults
  omega

lemma exists_signer {th : ℕ} {σ : Stmt} (h : Sup π s th σ) (hth : π.t < th) :
    ∃ q, q ∉ s.byz ∧ Signed π s q σ (R0 n) := by
  by_contra hne
  push_neg at hne
  have : signers π s σ (R0 n) = ∅ := by
    ext q; simp only [mem_signers, notMem_empty, iff_false, not_and]; exact hne q
  unfold Sup at h; rw [this] at h; have := hg.faults; simp at h; omega

lemma exists_common {σ σ' : Stmt} (h : Sup π s π.k σ) (h' : Sup π s π.k σ') :
    ∃ q, q ∉ s.byz ∧ Signed π s q σ (R0 n) ∧ Signed π s q σ' (R0 n) := by
  obtain ⟨q, hq, hq'⟩ := quorum hg _ _ (fun q hq => (mem_signers.1 hq).1)
    (fun q hq => (mem_signers.1 hq).1) h h'
  exact ⟨q, (mem_signers.1 hq).1, (mem_signers.1 hq).2, (mem_signers.1 hq').2⟩

/-- **Lemma B.1** (keys): at most one value gets a key certificate per view. -/
lemma key_unique {b b' : Bool} {v : ℕ} (h : Sup π s π.k (.key b v))
    (h' : Sup π s π.k (.key b' v)) : b = b' := by
  obtain ⟨q, -, h1, h2⟩ := exists_common hg h h'
  exact signed_key_unique h1 h2

lemma lock_sup_key {b : Bool} {v : ℕ} (h : Sup π s π.k (.lock b v)) :
    Sup π s π.k (.key b v) := by
  obtain ⟨q, hq, hs⟩ := exists_signer hg h (t_lt_k hg)
  obtain ⟨hv, -, c, hc, -, hval, -⟩ := signed_lock hs
  refine sup_of_cert hg (r := 11 * v + 7) hq hval fun τ hτ => ?_
  apply mem_toks_last
  rw [show 11 * v + 7 = 11 * v + 6 + 1 by omega, S_succ, trans_last]
  exact ⟨_, proposeLockOf_toks hc hτ⟩

lemma commit_sup_lock {b : Bool} {v : ℕ} (h : Sup π s π.k (.commit b v)) :
    Sup π s π.k (.lock b v) := by
  obtain ⟨q, hq, hs⟩ := exists_signer hg h (t_lt_k hg)
  obtain ⟨hv, -, c, hc, -, hval, -⟩ := signed_commit hs
  refine sup_of_cert hg (r := 11 * v + 9) hq hval fun τ hτ => ?_
  apply mem_toks_last
  rw [show 11 * v + 9 = 11 * v + 8 + 1 by omega, S_succ, trans_last]
  exact ⟨_, proposeCommitOf_toks hc hτ⟩

/-- What an honest key signer accepted in view `v`: a combined retrieval certificate (then it had
no lock) or a key certificate of an earlier view `v'` at least its lock view. -/
lemma key_signer_accepts {q : Fin n} (hq : q ∉ s.byz) {b : Bool} {v : ℕ}
    (hs : Signed π s q (.key b v) (R0 n)) :
    ((S π s (11 * v + 4) q).lock = none ∧ Sup π s (π.t + 1) (.inp b)) ∨
    (∃ v', v' < v ∧ Sup π s π.k (.key b v') ∧
      ∀ l, (S π s (11 * v + 4) q).lock = some l → l.2.1 ≤ v') := by
  obtain ⟨hv, -, hks⟩ := signed_key hs
  obtain ⟨b', J, hJ, -, hval, hok, he⟩ := keySign_spec hks
  cases he
  have hJt : ∀ τ ∈ J.toks, τ ∈ (S π s (11 * v + 5) q).toks := by
    intro τ hτ
    apply mem_toks_last
    rw [show 11 * v + 5 = 11 * v + 4 + 1 by omega, S_succ, trans_last]
    exact ⟨_, proposalOf_toks hJ hτ⟩
  cases J with
  | combine c =>
    left
    refine ⟨?_, sup_of_cert hg hq hval hJt⟩
    rcases hl : (S π s (11 * v + 4) q).lock with _ | l
    · rfl
    · simp [hl, lockOK] at hok
  | key v' c =>
    right
    refine ⟨v', hval.1, sup_of_cert hg hq hval.2 hJt, fun l hl => ?_⟩
    simpa [hl, lockOK] using hok

/-- **Lemma B.2.** After a commit certificate for `b₁` in view `v₁`, every key certificate of a
view `v ≥ v₁` is for `b₁`. -/
theorem key_after_commit {b₁ : Bool} {v₁ : ℕ} (hc : Sup π s π.k (.commit b₁ v₁)) :
    ∀ v, v₁ ≤ v → ∀ b, Sup π s π.k (.key b v) → b = b₁ := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro hv b hk
  rcases Nat.eq_or_lt_of_le hv with rfl | hlt
  · exact key_unique hg hk (lock_sup_key hg (commit_sup_lock hg hc))
  obtain ⟨q, hq, hcs, hks⟩ := exists_common hg hc hk
  obtain ⟨-, -, c, -, -, -, hlock⟩ := signed_commit hcs
  obtain ⟨l, hl, hle⟩ := S_lock_mono (show 11 * v₁ + 9 ≤ 11 * v + 4 by omega) hlock
  rcases key_signer_accepts hg hq hks with ⟨hnone, -⟩ | ⟨v', hv', hsup, hlv⟩
  · rw [hnone] at hl; cases hl
  · have := hlv l hl
    simp only at hle
    exact ih v' hv' (by omega) b hsup

/-- **Lemma B.3.** All commit certificates (with honest support) are for the same value. -/
theorem commit_unique {b b' : Bool} {v v' : ℕ} (h : Sup π s π.k (.commit b v))
    (h' : Sup π s π.k (.commit b' v')) : b = b' := by
  rcases le_total v v' with hle | hle
  · exact (key_after_commit hg h v' hle b' (lock_sup_key hg (commit_sup_lock hg h'))).symm
  · exact key_after_commit hg h' v hle b (lock_sup_key hg (commit_sup_lock hg h))

/-- Commits held by honest parties have honest support. -/
lemma sup_of_commit {r : ℕ} {p : Fin n} (hp : p ∉ s.byz) {c : Proof n}
    (h : (S π s r p).commit = some c) : Sup π s π.k (.commit c.1 c.2.1) :=
  sup_of_cert hg (r := r) hp (S_commit_valid r p c h)
    fun τ hτ => mem_toks_commit (by simp [optToks, h, hτ])

/-- **Agreement of commits.** Any two commits held by honest parties have the same value. -/
theorem commit_agree {r r' : ℕ} {p p' : Fin n} (hp : p ∉ s.byz) (hp' : p' ∉ s.byz)
    {c c' : Proof n} (h : (S π s r p).commit = some c) (h' : (S π s r' p').commit = some c') :
    c.1 = c'.1 :=
  commit_unique hg (sup_of_commit hg hp h) (sup_of_commit hg hp' h')

/-- Locks held by honest parties have honest support. -/
lemma sup_of_lock {r : ℕ} {p : Fin n} (hp : p ∉ s.byz) {c : Proof n}
    (h : (S π s r p).lock = some c) : Sup π s π.k (.lock c.1 c.2.1) :=
  sup_of_cert hg (r := r) hp (S_lock_valid r p c h).1
    fun τ hτ => mem_toks_lock (by simp [optToks, h, hτ])

end Podc.FewToManyFaultsBA.Sync
