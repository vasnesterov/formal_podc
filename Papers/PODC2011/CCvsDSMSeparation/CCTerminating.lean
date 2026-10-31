import Papers.PODC2011.CCvsDSMSeparation.UpperBoundCC
import Papers.PODC2011.CCvsDSMSeparation.Terminating

/-!
# The algorithm of Section 5 is terminating in the paper's sense

Every call of `ccAlg` returns at its process' second step after the invocation, so in a fair
infinite history every call completes (`ccAlg_terminating`). This also shows that the paper's
notion `Algorithm.Terminating` is satisfiable, i.e. `theorem_6_2_terminating` is not vacuous.
-/

namespace Podc.CCvsDSMSeparation

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
lemma pre_succ {V Val : Type*} (h : ℕ → Ev N V Val) (m : ℕ) : pre h (m + 1) = pre h m ++ [h m] := by
  simp [pre, List.range_succ]

/-- After its first step following an invocation, a process of `ccAlg` can only return. -/
def LastStep (c : LState CCLoc) : Prop := (∃ b, c.1 = .pollRet b) ∨ c.1 = .sigRet

theorem ccAlg_terminating : (ccAlg N).Terminating := by
  intro h hInf _ hfair n o hn
  set p := (h n).p with hp
  by_contra hno
  push Not at hno
  have hnoret : ∀ m > n, (h m).p = p → ∀ b, (h m).op ≠ .ret b := fun m hm hmp b hb =>
    hno m hm hmp b hb
  -- the state of `p` right after its invocation
  have hst : ∀ m, (ccAlg N).Valid (pre h (m + 1)) →
      ∃ c c', (ccAlg N).state (pre h m) (h m).p = some c ∧ CCGood c ∧
        (ccAlg N).lstep (h m).p c (h m).op = some c' ∧
        (ccAlg N).state (pre h (m + 1)) (h m).p = some c' := by
    intro m hv
    rw [pre_succ] at hv ⊢
    rcases hhm : h m with ⟨q, op⟩
    rw [hhm] at hv
    exact state_of_stepOK (ccInv_of_valid (Algorithm.Valid.of_append _ hv))
      ((Algorithm.valid_snoc _ _ _).1 hv).2
  have key : ∀ m, n < m → ∃ c, (ccAlg N).state (pre h m) p = some c ∧ c.2 = some o ∧
      ∀ k, n < k → k < m → (h k).p = p → LastStep c := by
    intro m hm
    induction m with
    | zero => omega
    | succ m ih =>
      by_cases hmn : m = n
      · subst hmn
        obtain ⟨c, c', hc, hcg, hcl, hc'⟩ := hst m (hInf _)
        rw [← hp] at hc hcl hc'
        refine ⟨c', hc', ?_, fun k hk1 hk2 => by omega⟩
        rcases ccAlg_lstep hcg hcl with ⟨-, o', hop, rfl⟩ | ⟨-, x, hop, -⟩ | ⟨b, -, hop, -⟩ |
            ⟨-, hop, -⟩ | ⟨-, hop, -⟩ <;> rw [hn] at hop <;> cases hop
        rfl
      · obtain ⟨c, hc, hco, hlast⟩ := ih (by omega)
        by_cases hmp : (h m).p = p
        · obtain ⟨c₀, c', hc₀, hcg, hcl, hc'⟩ := hst m (hInf _)
          rw [hmp] at hc₀ hcl hc'
          rw [hc] at hc₀; cases hc₀
          refine ⟨c', hc', ?_, ?_⟩
          · rcases ccAlg_lstep hcg hcl with ⟨h1, o', hop, rfl⟩ | ⟨h1, x, hop, rfl⟩ |
                ⟨b, h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩
            · rw [h1] at hco; cases hco
            · rw [h1] at hco; exact hco
            · exact absurd hop (hnoret m (by omega) hmp b)
            · rw [h1] at hco; exact hco
            · exact absurd hop (hnoret m (by omega) hmp false)
          · intro k hk1 hk2 _
            rcases ccAlg_lstep hcg hcl with ⟨h1, o', hop, rfl⟩ | ⟨h1, x, hop, rfl⟩ |
                ⟨b, h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩
            · rw [h1] at hco; cases hco
            · left; exact ⟨x, rfl⟩
            · exact absurd hop (hnoret m (by omega) hmp b)
            · right; rfl
            · exact absurd hop (hnoret m (by omega) hmp false)
        · refine ⟨c, ?_, hco, fun k hk1 hk2 hkp => ?_⟩
          · rw [pre_succ, (ccAlg N).state_snoc_ne _ _ hmp]; exact hc
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hk2 with hk2 | rfl
            · exact hlast k hk1 hk2 hkp
            · exact absurd hkp hmp
  -- two steps of `p` after the invocation are impossible
  have hnot2 : ∀ k₁ k₂, n < k₁ → k₁ < k₂ → (h k₁).p = p → (h k₂).p ≠ p := by
    intro k₁ k₂ hk1 hk2 hp1 hp2
    obtain ⟨c, hc, hco, hlast⟩ := key k₂ (by omega)
    have hl := hlast k₁ hk1 hk2 hp1
    obtain ⟨c₀, c', hc₀, hcg, hcl, -⟩ := hst k₂ (hInf _)
    rw [hp2, hc] at hc₀; cases hc₀
    rw [hp2] at hcl
    rcases ccAlg_lstep hcg hcl with ⟨h1, o', hop, rfl⟩ | ⟨h1, x, hop, rfl⟩ |
        ⟨b, h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩ | ⟨h1, hop, rfl⟩
    · rw [h1] at hco; cases hco
    · rcases hl with ⟨b, hb⟩ | hb <;> rw [h1] at hb <;> cases hb
    · exact hnoret k₂ (by omega) hp2 b hop
    · rcases hl with ⟨b, hb⟩ | hb <;> rw [h1] at hb <;> cases hb
    · exact hnoret k₂ (by omega) hp2 false hop
  rcases hfair p ⟨n, rfl⟩ with hinf | ⟨n', hn', hidle⟩
  · obtain ⟨k₁, hk₁, hp1⟩ := hinf (n + 1)
    obtain ⟨k₂, hk₂, hp2⟩ := hinf (k₁ + 1)
    exact hnot2 k₁ k₂ (by omega) (by omega) hp1 hp2
  · by_cases hn'n : n' ≤ n
    · exact hn' n hn'n rfl
    · obtain ⟨c, hc, hco, -⟩ := key n' (by omega)
      obtain ⟨s, hs⟩ := hidle
      rw [hc] at hs; cases hs; cases hco

end Podc.CCvsDSMSeparation
