import Papers.PODC2026.FewToManyFaultsBA.SyncBA.Out

/-!
# Validity: the synchronous retrieval protocol (Lemmas 10.1, 10.2, B.4)

* `retrieval_fail` (**Lemma 10.1**): if an honest party sets its retrieval input to `⊥`, the
  honest inputs are not unanimous (so both values satisfy strong unanimity).
* `key_valid` (**Lemmas 10.2 and B.4**): if all honest inputs are `b₀`, every key certificate
  (hence every lock and commit certificate) is for `b₀`.
-/

namespace Podc.FewToManyFaultsBA.Sync

open Cslib.Byzantine.LockStep Finset

variable {n : ℕ} [NeZero n] {π : Params n} {s : Scenario (Fin n) Bool (Msg n)}

lemma leaderPlan_retr {v : ℕ} {st : St n} {ib : Fin n → Option (Msg n)}
    (h : leaderPlan π v st ib = .retr) :
    st.commit = none ∧ (∀ q, commitSugg π.k (ib q) = none) ∧ bestKey π.k v ib = none := by
  unfold leaderPlan at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · rename_i hcs
      split at h
      · cases h
      · rename_i hb
        refine ⟨hc, fun q => ?_, hb⟩
        exact List.findSome?_eq_none_iff.1 hcs q (List.mem_finRange q)

lemma S_last {r : ℕ} (p : Fin n) : (S π s (r + 1) p).last = aib π s r p := by
  rw [S_succ, trans_last]

lemma card_honest (hg : Good π s) : π.t + 1 ≤ s.honestFinset.card := by
  classical
  have h1 : s.honestFinset ∪ byzF s = univ := by
    ext q; by_cases hq : q ∈ s.byz <;> simp [byzF, hq]
  have h2 := card_union_le s.honestFinset (byzF s)
  rw [h1, card_univ, Fintype.card_fin] at h2
  have := hg.faults; have := hg.res
  omega

/-- **Lemma 10.1.** If an honest party has set its retrieval input to `⊥`, the honest parties do
not all have the same input. -/
theorem retrieval_fail (hg : Good π s) {r : ℕ} {p : Fin n} (hp : p ∉ s.byz)
    (hvin : (S π s r p).vin = none) (b₀ : Bool) (hun : ∀ q ∉ s.byz, s.input q = b₀) : False := by
  classical
  obtain ⟨w, hw, -, hlead, hplan, hc0, hc1⟩ := S_vin_none r p hvin
  obtain ⟨rfl, hcom⟩ := lead_spec hw (by norm_num) (by norm_num) hlead
  have hlead1 : (S π s (11 * w + 1) (leader w)).lead = true := by
    rw [← S_lead (j := 3) hw (by norm_num) (by norm_num)]; exact hlead
  rw [S_plan3 hw, S_plan2 hw, hlead1, if_pos rfl] at hplan
  obtain ⟨-, hcs, -⟩ := leaderPlan_retr hplan
  have hr0 : ∀ j, j < 11 → 11 * w + j < R0 n := fun j hj => by
    have := view_lt_Rh (n := n) hw hj; unfold R0; unfold Rh at this; omega
  -- every honest party received `ReqSuggestion` and had no commit in phase 1
  have hnocommit : ∀ q, q ∉ s.byz → (S π s (11 * w + 1) q).commit = none := by
    intro q hq
    rcases hcq : (S π s (11 * w + 1) q).commit with _ | c
    · rfl
    exfalso
    have hreq : isReqSugg ((S π s (11 * w + 1) q).last (leader w)) = true := by
      have h00 : 11 * w < R0 n := by simpa using hr0 0 (by norm_num)
      rw [S_last, aib_honest hg.rel h00 q hp]
      have hlo : leaderOut (S π s (11 * w) (leader w)) 0 q = some .reqSugg := by
        simp [leaderOut, hcom]
      obtain ⟨pm, hpm⟩ := out_leader (π := π) hw (by norm_num) hlo
      simp only [Nat.add_zero] at hpm
      rw [hpm]; rfl
    have hpo : partyOut q (S π s (11 * w + 1) q) w 1 = some (.sugg (.commit c)) := by
      simp [partyOut, hreq, hcq, suggOf]
    obtain ⟨lm, hm⟩ := out_party (π := π) hw (by norm_num) hpo
    have := hcs q
    rw [aib_honest hg.rel (hr0 1 (by norm_num)) (leader w) hq, hm] at this
    have hv := S_commit_valid (π := π) (s := s) (11 * w + 1) q c hcq
    simp [commitSugg, hv] at this
  -- every honest party answers the retrieval
  have hmem : ∀ q, q ∉ s.byz → (q, Stmt.inp b₀) ∈ retrToks (.inp b₀) (aib π s (11 * w + 3) (leader w)) := by
    intro q hq
    have hact : (S π s (11 * w + 3) q).active = true := by
      rw [S_active hw (by norm_num) (by norm_num), hnocommit q hq]; rfl
    have hrun : isRunRetr ((S π s (11 * w + 3) q).last (leader w)) = true := by
      rw [show 11 * w + 3 = 11 * w + 2 + 1 by omega, S_last,
        aib_honest hg.rel (hr0 2 (by norm_num)) q hp]
      have hpl2 : (S π s (11 * w + 2) (leader w)).plan = .retr := by
        rw [S_plan2 hw, hlead1, if_pos rfl]; exact hplan
      have hlo : leaderOut (S π s (11 * w + 2) (leader w)) 2 q = some .runRetr := by
        simp [leaderOut, hpl2]
      obtain ⟨pm, hpm⟩ := out_leader (π := π) hw (by norm_num) hlo
      rw [hpm]; rfl
    have hpo : partyOut q (S π s (11 * w + 3) q) w 3 =
        some (.retr (retrAnswer q (S π s (11 * w + 3) q).vin)) := by
      simp [partyOut, hact, hrun]
    obtain ⟨lm, hm⟩ := out_party (π := π) hw (by norm_num) hpo
    simp only [retrToks, mem_biUnion, mem_univ, true_and]
    refine ⟨q, ?_⟩
    rw [aib_honest hg.rel (hr0 3 (by norm_num)) (leader w) hq, hm]
    simp only [mem_filter, and_true]
    rcases S_vin (π := π) (s := s) (11 * w + 3) q with h | h <;> rw [h] <;>
      cases b₀ <;> simp [retrAnswer, hun q hq]
  have hsub : s.honestFinset.image (fun q => (q, Stmt.inp b₀)) ⊆
      retrToks (.inp b₀) (aib π s (11 * w + 3) (leader w)) := by
    intro τ hτ
    obtain ⟨q, hq, rfl⟩ := mem_image.1 hτ
    exact hmem q ((Scenario.mem_honestFinset _).1 hq)
  have hcard := card_le_card hsub
  rw [card_image_of_injective _ (fun a b h => by simpa using h)] at hcard
  have := card_honest hg
  cases b₀ <;> omega

/-- **Lemmas 10.2 / B.4.** If all honest inputs are `b₀`, every key certificate is for `b₀`. -/
theorem key_valid (hg : Good π s) (b₀ : Bool) (hun : ∀ q ∉ s.byz, s.input q = b₀) :
    ∀ v b, Sup π s π.k (.key b v) → b = b₀ := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro b hk
  obtain ⟨q, hq, hs⟩ := exists_signer hg hk (t_lt_k hg)
  rcases key_signer_accepts hg hq hs with ⟨-, hinp⟩ | ⟨v', hv', hsup, -⟩
  · obtain ⟨q', hq', hs'⟩ := exists_signer hg hinp (by omega)
    obtain ⟨r', -, -, hvin⟩ := signed_inp hs'
    rcases hvin with h | h
    · rcases S_vin (π := π) (s := s) r' q' with h' | h' <;> rw [h'] at h
      · cases h; exact hun q' hq'
      · cases h
    · exact (retrieval_fail hg hq' h b₀ hun).elim
  · exact ih v' hv' b hsup

lemma commit_valid (hg : Good π s) (b₀ : Bool) (hun : ∀ q ∉ s.byz, s.input q = b₀) {b : Bool}
    {v : ℕ} (h : Sup π s π.k (.commit b v)) : b = b₀ :=
  key_valid hg b₀ hun v b (lock_sup_key hg (commit_sup_lock hg h))

lemma lock_valid (hg : Good π s) (b₀ : Bool) (hun : ∀ q ∉ s.byz, s.input q = b₀) {b : Bool}
    {v : ℕ} (h : Sup π s π.k (.lock b v)) : b = b₀ :=
  key_valid hg b₀ hun v b (lock_sup_key hg h)

end Podc.FewToManyFaultsBA.Sync
