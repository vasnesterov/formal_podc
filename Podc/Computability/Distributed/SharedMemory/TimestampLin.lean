import Podc.Computability.Distributed.SharedMemory.MWMRRegister

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/TimestampLin.lean

/-!
# Linearizability of multi-writer registers from timestamps

The classical correctness argument of ABD-like register implementations: every operation `x`
gets a timestamp `tok x` in a linear order `T` with bottom `⊥` (the timestamp of the initial
value), and

* the writes `W` that are linearized (all completed writes, possibly some pending ones) have
  distinct timestamps above `⊥`;
* a completed read returns the value of the write of `W` with the same timestamp (or `v₀` if its
  timestamp is `⊥`);
* if `a` precedes `b` in real time, then `tok a < tok b` when `b ∈ W`, and `tok a ≤ tok b` when
  `b` is a completed read.

Then the history is linearizable (`TSLin.exists_isLinearization`): order the writes by timestamp
and put every read right after the write it reads from. This reduces to the reads-from criterion
`MWMRReadsFrom` (`MWMRRegister.lean`); the proof follows `Papers/PODC2021/RegisterLinTermination`
(Alg. 4), where it was done for a specific algorithm.
-/

namespace Cslib.SharedMemory

open List

variable {P : Type} [DecidableEq P] {V : Type} {v₀ : V} {T : Type} [LinearOrder T] [OrderBot T]

/-- The timestamp criterion for histories of a multi-writer register. -/
structure TSLin (α : List (Label P (register V v₀))) (W : List (OpId P)) (tok : OpId P → T) :
    Prop where
  wellFormed : WellFormed α
  W_nodup : W.Nodup
  W_write : ∀ x ∈ W, ∃ v, opOf α x = some (.write v)
  W_complete : ∀ x v, opOf α x = some (.write v) → Completed α x → x ∈ W
  write_resp : ∀ x v r, opOf α x = some (.write v) → respOf α x = some r → r = v
  W_inj : ∀ a ∈ W, ∀ b ∈ W, tok a = tok b → a = b
  W_pos : ∀ x ∈ W, ⊥ < tok x
  read_val : ∀ x r, opOf α x = some .read → respOf α x = some r →
    (tok x = ⊥ ∧ r = v₀) ∨ ∃ w ∈ W, tok w = tok x ∧ opOf α w = some (.write r)
  prec_W : ∀ a b, Precedes α a b → b ∈ W → tok a < tok b
  prec_R : ∀ a b, Precedes α a b → opOf α b = some .read → Completed α b → tok a ≤ tok b

namespace TSLin

/-- The writes sorted by timestamp. -/
noncomputable def sortWs (W : List (OpId P)) (tok : OpId P → T) : List (OpId P) :=
  W.mergeSort (fun a b => decide (tok a ≤ tok b))

/-- The reads-from map: `0` for reads with timestamp `⊥`, otherwise `1 +` the position of the
write with the same timestamp. -/
def rfOf (ws : List (OpId P)) (tok : OpId P → T) (x : OpId P) : ℕ :=
  if tok x = ⊥ then 0 else ws.findIdx (fun w => decide (tok w = tok x)) + 1

section Sorted

variable {ws : List (OpId P)} {tok : OpId P → T}
  (hs : ws.Pairwise (fun a b => tok a ≤ tok b)) (hnd : ws.Nodup)
  (hinj : ∀ a ∈ ws, ∀ b ∈ ws, tok a = tok b → a = b)
include hs hnd hinj

lemma idx_eq_of_tok_eq {i j : ℕ} (hi : i < ws.length) (hj : j < ws.length)
    (h : tok ws[i] = tok ws[j]) : i = j :=
  (hnd.getElem_inj_iff).1 (hinj _ (getElem_mem hi) _ (getElem_mem hj) h)

lemma idx_lt_of_tok_lt {i j : ℕ} (hi : i < ws.length) (hj : j < ws.length)
    (h : tok ws[i] < tok ws[j]) : i < j := by
  by_contra hc
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact absurd (pairwise_iff_getElem.1 hs j i hj hi hlt) (not_le.2 h)
  · have : i = j := by omega
    subst this; exact lt_irrefl _ h

lemma findIdx_tok {i : ℕ} (hi : i < ws.length) :
    ws.findIdx (fun w => decide (tok w = tok ws[i])) = i := by
  rw [findIdx_eq hi]
  refine ⟨by simp, fun j hji => ?_⟩
  have := idx_eq_of_tok_eq hs hnd hinj (show j < ws.length by omega) hi
  simp only [decide_eq_false_iff_not]
  intro h; have := this h; omega

end Sorted

variable {α : List (Label P (register V v₀))} {W : List (OpId P)} {tok : OpId P → T}

/-- The timestamp criterion gives the hypotheses of the MWMR reads-from criterion. -/
theorem readsFrom (h : TSLin α W tok) :
    MWMRReadsFrom α (sortWs W tok) (rfOf (sortWs W tok) tok) := by
  set ws := sortWs W tok with hws_def
  have hperm : ws.Perm W := mergeSort_perm _ _
  have hmem : ∀ x, x ∈ ws ↔ x ∈ W := fun x => hperm.mem_iff
  have hnd : ws.Nodup := hperm.nodup_iff.2 h.W_nodup
  have hs : ws.Pairwise (fun a b => tok a ≤ tok b) := by
    have := pairwise_mergeSort (le := fun a b => decide (tok a ≤ tok b))
      (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; exact hab.trans hbc)
      (fun a b => by simpa using le_total _ _) W
    simp only [decide_eq_true_eq] at this
    exact this
  have hinj : ∀ a ∈ ws, ∀ b ∈ ws, tok a = tok b → a = b :=
    fun a ha b hb => h.W_inj a ((hmem a).1 ha) b ((hmem b).1 hb)
  have hpos : ∀ i (hi : i < ws.length), ⊥ < tok ws[i] :=
    fun i hi => h.W_pos _ ((hmem _).1 (getElem_mem hi))
  have hlook : ∀ x, opOf α x = some .read → Completed α x → tok x ≠ ⊥ →
      ∃ k, ∃ hk : k < ws.length, tok ws[k] = tok x ∧ rfOf ws tok x = k + 1 ∧
        respOf α x = some (wsVal α ws (k + 1)) := by
    intro x hx hc h0
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
    rcases h.read_val x v hx hv with ⟨h1, -⟩ | ⟨w, hw, h1, h2⟩
    · exact absurd h1 h0
    · obtain ⟨k, hk, rfl⟩ := getElem_of_mem ((hmem w).2 hw)
      refine ⟨k, hk, h1, ?_, ?_⟩
      · rw [rfOf, if_neg h0, ← h1, findIdx_tok hs hnd hinj hk]
      · rw [hv]; simp [wsVal, getElem?_eq_getElem hk, h2]
  have hW_after : ∀ a i (hi : i < ws.length), Precedes α a ws[i] → tok a < tok ws[i] :=
    fun a i hi hab => h.prec_W a _ hab ((hmem _).1 (getElem_mem hi))
  refine ⟨h.wellFormed, hnd, fun x hx => h.W_write x ((hmem x).1 hx),
    fun x v hv hc => (hmem x).2 (h.W_complete x v hv hc), h.write_resp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- read_le
    intro x hx hc
    by_cases h0 : tok x = ⊥
    · simp [rfOf, h0]
    · obtain ⟨k, hk, -, hrf, -⟩ := hlook x hx hc h0
      omega
  · -- read_val
    intro x hx hc
    by_cases h0 : tok x = ⊥
    · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (completed_iff_respOf.1 hc)
      rcases h.read_val x v hx hv with ⟨-, h1⟩ | ⟨w, hw, h1, -⟩
      · rw [hv, rfOf, if_pos h0]; exact congrArg some h1
      · exfalso
        have h2 := h.W_pos w hw
        rw [h1, h0] at h2; exact lt_irrefl _ h2
    · obtain ⟨k, hk, -, hrf, hval⟩ := hlook x hx hc h0
      rw [hrf]; exact hval
  · -- ww
    intro i j hi hj hij
    exact idx_lt_of_tok_lt hs hnd hinj hi hj (hW_after _ j hj hij)
  · -- wr
    intro i hi x hx hxc hix
    have hle := h.prec_R _ x hix hx hxc
    have h0 : tok x ≠ ⊥ := by
      intro h0; rw [h0] at hle; exact (lt_irrefl _ ((hpos i hi).trans_le hle))
    obtain ⟨k, hk, htk, hrf, -⟩ := hlook x hx hxc h0
    rw [hrf]; rw [← htk] at hle
    rcases hle.lt_or_eq with hlt | heq
    · have := idx_lt_of_tok_lt hs hnd hinj hi hk hlt; omega
    · have := idx_eq_of_tok_eq hs hnd hinj hi hk heq; omega
  · -- rw
    intro x i hi hx hxc hxi
    have hlt := hW_after x i hi hxi
    by_cases h0 : tok x = ⊥
    · simp [rfOf, h0]
    · obtain ⟨k, hk, htk, hrf, -⟩ := hlook x hx hxc h0
      rw [hrf]; rw [← htk] at hlt
      have := idx_lt_of_tok_lt hs hnd hinj hk hi hlt; omega
  · -- rr
    intro x y hx hxc hy hyc hxy
    have hle := h.prec_R x y hxy hy hyc
    by_cases h0 : tok x = ⊥
    · simp [rfOf, h0]
    · have h0' : tok y ≠ ⊥ := by
        intro h0'; rw [h0'] at hle; exact h0 (le_bot_iff.1 hle)
      obtain ⟨k, hk, htk, hrf, -⟩ := hlook x hx hxc h0
      obtain ⟨k', hk', htk', hrf', -⟩ := hlook y hy hyc h0'
      rw [hrf, hrf']; rw [← htk, ← htk'] at hle
      rcases hle.lt_or_eq with hlt | heq
      · have := idx_lt_of_tok_lt hs hnd hinj hk hk' hlt; omega
      · have := idx_eq_of_tok_eq hs hnd hinj hk hk' heq; omega

/-- **Timestamp criterion.** A history satisfying `TSLin` is linearizable. -/
theorem exists_isLinearization (h : TSLin α W tok) : ∃ L, IsLinearization α L :=
  ⟨_, h.readsFrom.isLinearization⟩

end TSLin

end Cslib.SharedMemory
