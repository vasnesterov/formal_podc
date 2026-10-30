import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Liveness

/-!
# The fallback detection of `SyncBA` (Appendix B.3, Lemma B.12, Theorem B.14)

Rounds `11n` (`HELP`), `11n+1` (`PROOF`, `FALLBACK`) and `11n+2` (`LOCK`) of stage A:

* `commit_spread`: if an honest party has a commit at the end of the views, every honest party has
  one two rounds later (it answers the `HELP`s with `PROOF`s);
* `fb_of_no_commit`: if no honest party has a commit at the end of the views, every honest party
  builds a fallback certificate (it participates in the fallback);
* `no_fb_of_commit` (**Lemma B.12**, contrapositive): if every honest party has a commit at the
  end of the views, no honest party ever has a fallback certificate;
* `finalValue_eq_commit` (core of **Theorem B.14**): if no honest party had a commit at the end of
  the views but some honest party has one (`v`) at the end of stage A, every honest party enters the
  fallback with value `v`;
* `finalValue_valid`: under unanimous honest inputs `b₀`, every honest party's value is `b₀`.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {s : Scenario (Fin n) Bool (Msg n)}

lemma out_Rh (p : Fin n) (st : St n) (q : Fin n) :
    out π p st (Rh n) q = if st.commit.isNone then some (.help (p, .help)) else none := by
  simp [out]

lemma out_Rh1 (p : Fin n) (st : St n) (q : Fin n) :
    out π p st (Rh n + 1) q =
      if (if isHelp (st.last q) then st.commit else none).isNone ∧ (ownFb π.t st.last).isNone
      then none
      else some (.stage2 (if isHelp (st.last q) then st.commit else none) (ownFb π.t st.last)) := by
  have h1 : ¬ Rh n + 1 < Rh n := by omega
  simp [out, h1]

lemma out_Rh2_lock (p : Fin n) {st : St n} (q : Fin n) {c : Proof n} (hl : st.lock = some c)
    (hf : st.fb.isSome) : out π p st (Rh n + 2) q = some (.lock c) := by
  have h1 : ¬ Rh n + 2 < Rh n := by omega
  simp [out, h1, hl, hf]

lemma out_Rh2_none (p : Fin n) {st : St n} (q : Fin n) (hf : st.fb = none) :
    out π p st (Rh n + 2) q = none := by
  have h1 : ¬ Rh n + 2 < Rh n := by omega
  simp only [out, h1, ite_false, show Rh n + 2 ≠ Rh n by omega,
    show Rh n + 2 ≠ Rh n + 1 by omega, ite_true, hf]
  split <;> simp

lemma Rh_lt_R0 : Rh n < R0 n := by unfold R0 Rh; omega
lemma Rh1_lt_R0 : Rh n + 1 < R0 n := by unfold R0 Rh; omega
lemma Rh2_lt_R0 : Rh n + 2 < R0 n := by unfold R0 Rh; omega

lemma S_fb_Rh1 (p : Fin n) :
    (S π s (Rh n + 2) p).fb =
      (ownFb π.t (S π s (Rh n + 1) p).last).or (inboxFb π.t (aib π s (Rh n + 1) p)) := by
  rw [S_succ, trans_fb, if_pos rfl]

lemma S_fb_R0 (p : Fin n) : (S π s (R0 n) p).fb = (S π s (Rh n + 2) p).fb := by
  rw [show R0 n = Rh n + 2 + 1 by unfold R0 Rh; omega, S_succ, trans_fb, if_neg (by omega)]

lemma S_fb_lt : ∀ r (p : Fin n), r ≤ Rh n + 1 → (S π s r p).fb = none := by
  intro r
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro p hr
    rw [S_succ, trans_fb, if_neg (by omega)]
    exact ih p (by omega)

lemma ownFb_valid {ib : Fin n → Option (Msg n)} {c : Cert n} (h : ownFb π.t ib = some c) :
    Valid n (π.t + 1) .help c := by
  unfold ownFb at h
  split_ifs at h with hc
  cases h
  refine ⟨fun τ hτ => ?_, hc⟩
  simp only [helpToks, mem_biUnion, mem_univ, true_and] at hτ
  obtain ⟨q, hq⟩ := hτ
  split at hq
  · split_ifs at hq with he
    · simp only [mem_singleton] at hq; subst hq; exact he
    · simp at hq
  · simp at hq

lemma inboxFb_valid {ib : Fin n → Option (Msg n)} {c : Cert n} (h : inboxFb π.t ib = some c) :
    Valid n (π.t + 1) .help c := by
  unfold inboxFb at h
  obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some h
  split at hq
  · split_ifs at hq with hv; cases hq; exact hv
  · cases hq

variable (hg : Good π s)
include hg

/-- If an honest party has a commit at the end of the views, every honest party has one two rounds
later. -/
lemma commit_spread {p : Fin n} (hp : p ∉ s.byz) {c : Proof n}
    (hc : (S π s (Rh n) p).commit = some c) :
    ∀ q, q ∉ s.byz → (S π s (Rh n + 2) q).commit.isSome := by
  intro q hq
  by_cases hq0 : (S π s (Rh n) q).commit.isSome
  · exact commit_mono_isSome hg (by omega) hq0
  have hq0' : (S π s (Rh n) q).commit = none := by simpa using hq0
  have hhelp : isHelp ((S π s (Rh n + 1) p).last q) = true := by
    rw [S_last, aib_honest hg.rel Rh_lt_R0 p hq, out_Rh]; simp [hq0', isHelp]
  have hc1 := S_commit_mono (show Rh n ≤ Rh n + 1 by omega) hc
  have hm : aib π s (Rh n + 1) q p =
      some (.stage2 (some c) (ownFb π.t (S π s (Rh n + 1) p).last)) := by
    rw [aib_honest hg.rel Rh1_lt_R0 q hp, out_Rh1]; simp [hhelp, hc1]
  exact commit_of_recv (c := c) Rh1_lt_R0 hm
    (by simp [commitOf, S_commit_valid _ _ _ hc1])

/-- If no honest party has a commit at the end of the views, every honest party builds a fallback
certificate. -/
lemma fb_of_no_commit (hnc : ∀ q, q ∉ s.byz → (S π s (Rh n) q).commit = none) :
    ∀ p, p ∉ s.byz → (S π s (Rh n + 2) p).fb.isSome := by
  intro p hp
  have hmem : ∀ q, q ∉ s.byz → (q, Stmt.help) ∈ helpToks (S π s (Rh n + 1) p).last := by
    intro q hq
    simp only [helpToks, mem_biUnion, mem_univ, true_and]
    refine ⟨q, ?_⟩
    rw [S_last, aib_honest hg.rel Rh_lt_R0 p hq, out_Rh]
    simp [hnc q hq]
  have hsub : s.honestFinset.image (fun q => (q, Stmt.help)) ⊆
      helpToks (S π s (Rh n + 1) p).last := by
    intro τ hτ
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hτ
    exact hmem q ((Scenario.mem_honestFinset _).1 hq)
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (fun a b h => by simpa using h)] at hcard
  have := card_honest hg
  rw [S_fb_Rh1]
  simp [ownFb, show π.t + 1 ≤ (helpToks (S π s (Rh n + 1) p).last).card by omega]

/-- A valid fallback certificate has an honest signer, who had no commit at the end of the
views. -/
lemma help_cert_signer {r : ℕ} {p : Fin n} (hp : p ∉ s.byz) {c : Cert n}
    (hv : Valid n (π.t + 1) .help c) (hc : ∀ τ ∈ c, τ ∈ (S π s r p).toks) :
    ∃ q, q ∉ s.byz ∧ (S π s (Rh n) q).commit = none := by
  obtain ⟨q, hq, hs⟩ := exists_signer hg (sup_of_cert hg hp hv hc) (by omega)
  exact ⟨q, hq, (signed_help hs).2⟩

/-- **Lemma B.12** (contrapositive). If every honest party has a commit at the end of the views,
no honest party ever holds a fallback certificate. -/
lemma no_fb_of_commit (hall : ∀ q, q ∉ s.byz → (S π s (Rh n) q).commit.isSome) :
    ∀ r p, p ∉ s.byz → (S π s r p).fb = none := by
  have key : ∀ p, p ∉ s.byz → (S π s (Rh n + 2) p).fb = none := by
    intro p hp
    rw [S_fb_Rh1]
    rcases hf : ownFb π.t (S π s (Rh n + 1) p).last with _ | c
    · rcases hi : inboxFb π.t (aib π s (Rh n + 1) p) with _ | c'
      · rfl
      · exfalso
        obtain ⟨q, hq, hcq⟩ := help_cert_signer hg (r := Rh n + 2) hp (inboxFb_valid hi)
          (fun τ hτ => mem_toks_last (by rw [S_last]; exact inboxFb_toks hi hτ))
        have := hall q hq
        rw [hcq] at this; simp at this
    · exfalso
      obtain ⟨q, hq, hcq⟩ := help_cert_signer hg (r := Rh n + 1) hp (ownFb_valid hf)
        (fun τ hτ => mem_toks_last (ownFb_toks hf hτ))
      have := hall q hq
      rw [hcq] at this; simp at this
  intro r p hp
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [S_succ, trans_fb]
    split_ifs with h
    · subst h; rw [← S_fb_Rh1]; exact key p hp
    · exact ih

/-- **Theorem B.14, the delicate case.** If no honest party had a commit at the end of the views
but an honest party holds a commit for `b` at the end of stage A, every honest party's final value
is `b`. -/
theorem finalValue_eq_commit (hnc : ∀ q, q ∉ s.byz → (S π s (Rh n) q).commit = none)
    {p : Fin n} (hp : p ∉ s.byz) {c : Proof n} (hc : (S π s (R0 n) p).commit = some c) :
    ∀ q, q ∉ s.byz → finalValue π (S π s (R0 n) q) (s.input q) = c.1 := by
  intro q hq
  have hsup := sup_of_commit hg hp hc
  rcases hcq : (S π s (R0 n) q).commit with _ | c'
  swap
  · simp only [finalValue, hcq]; exact commit_agree hg hq hp hcq hc
  obtain ⟨p₀, hp₀, hs⟩ := exists_signer hg hsup (t_lt_k hg)
  obtain ⟨hv₁, -, cl, -, -, -, hlock⟩ := signed_commit hs
  obtain ⟨l, hl, hle⟩ := S_lock_mono (show 11 * c.2.1 + 9 ≤ Rh n + 2 by unfold Rh; omega) hlock
  have hfb := fb_of_no_commit hg hnc p₀ hp₀
  have hm : (S π s (R0 n) q).last p₀ = some (.lock l) := by
    rw [show R0 n = Rh n + 2 + 1 by unfold R0 Rh; omega, S_last,
      aib_honest hg.rel Rh2_lt_R0 q hp₀, out_Rh2_lock _ _ hl hfb]
  have hlv := (S_lock_valid (π := π) (s := s) _ p₀ l hl).1
  have hmem : l ∈ lockCands π.k (S π s (R0 n) q).last :=
    mem_lockCands.2 ⟨p₀, by rw [hm]; simp [lockMsg, hlv]⟩
  rcases hb : bestLock π.k (S π s (R0 n) q).last with _ | l'
  · rw [bestLock_none hb] at hmem; simp at hmem
  obtain ⟨hl'mem, hmax⟩ := bestLock_spec hb
  obtain ⟨q', hq'⟩ := mem_lockCands.1 hl'mem
  obtain ⟨hq'm, hl'v⟩ := lockMsg_spec hq'
  have hsupl : Sup π s π.k (.lock l'.1 l'.2.1) := sup_of_cert hg (r := R0 n) hq hl'v
    fun τ hτ => mem_toks_last ⟨q', by rw [hq'm]; simp [omToks, Msg.toks, hτ]⟩
  have hle' := hmax l hmem
  simp only [finalValue, hcq, hb]
  exact key_after_commit hg hsup l'.2.1 (by simp only at hle; omega) l'.1 (lock_sup_key hg hsupl)

/-- Under unanimous honest inputs, every honest final value is the common input. -/
lemma finalValue_valid (b₀ : Bool) (hun : ∀ q ∉ s.byz, s.input q = b₀) {r : ℕ} {q : Fin n}
    (hq : q ∉ s.byz) : finalValue π (S π s r q) (s.input q) = b₀ := by
  unfold finalValue
  split
  · rename_i c hc; exact commit_valid hg b₀ hun (sup_of_commit hg hq hc)
  · split
    · rename_i l hb
      obtain ⟨hl'mem, -⟩ := bestLock_spec hb
      obtain ⟨q', hq'⟩ := mem_lockCands.1 hl'mem
      obtain ⟨hq'm, hl'v⟩ := lockMsg_spec hq'
      exact lock_valid hg b₀ hun (sup_of_cert hg (r := r) hq hl'v
        fun τ hτ => mem_toks_last ⟨q', by rw [hq'm]; simp [omToks, Msg.toks, hτ]⟩)
    · exact hun q hq

end Podc.FewToManyFaultsBA.Sync
