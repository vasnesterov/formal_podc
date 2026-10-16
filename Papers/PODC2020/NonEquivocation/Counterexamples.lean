import Papers.PODC2020.NonEquivocation.PSL

/-!
# Lemmas 4.7/4.8 fail if `v` may be `⊥`; so does line 8 of Algorithm 2 under that reading

Madsen–Debois, PODC 2020, Lemma 4.7 ("no consistent majority for `⊥` can exist") and line 8 of
Algorithm 2 with `v` ranging over values *and* `⊥`.

Instance (`n = 3`, `t = 1`, two rounds, weak non-equivocation): processes `0, 1` are non-faulty,
`2` is faulty; all private values are `v`; process `2` behaves correctly except that it omits all its
messages to `0`. Then `Q = {0, 2}` is a consistent `2`-majority **for `⊥`** at process `0`
(`|Q| = 2 = t + 1`, and the only admissible route is `0|2`, which carries `⊥`; the routes `0|0|2`,
`0|2|2` have consecutive duplicates). The proof of Lemma 4.7 overlooks that the only non-faulty
member of `Q` may be the decider itself. Meanwhile `{1, 2}` is a consistent `2`-majority for `v`
at process `1` (so Lemma 4.8 fails too under this reading), and a line 8 that allows `v = ⊥` makes
`0` output `⊥` (not even a value) and `1` output `v`. The type-consistent reading `v ∈ V` (line 2:
"⊥ ∉ V") is the one used in `PSL.lean`, under which Algorithm 2 is correct.
Algorithm 1 (and Algorithm 2 with genuine values, `PSL.lean`) handle this run correctly.
-/

namespace NonEquivocation

open Classical

variable {V : Type*} [OmitVal V]

/-- The run: everybody correct with private value `v`, except that `2` omits everything to `0`. -/
def cexSys (v : V) : ExecSys Unit (Fin 3) V where
  input _ _ := some v
  nb _ _ := ()
  om _ _ y x := y = 2 ∧ x = 0

/-- The message map of the counterexample. -/
noncomputable def cexσ (v : V) : MsgMap (Fin 3) V := (cexSys v).σ ()

lemma cex_wne (v : V) (k : ℕ) : wne k {2} (cexσ v) :=
  (cexSys v).wne_of (fun y hy => ⟨rfl, fun _ x h => hy (by simp [h.1])⟩) k

/-- Line 8 of Algorithm 2 under the reading where `v` may be `⊥`: `some o` if there is a consistent
majority for `o : Option V`, `none` if there is none. -/
noncomputable def line8Lit {P : Type*} (t : ℕ) (S : Finset P) (τ : List P → Option V) (p q : P) :
    Option (Option V) :=
  if h : ∃ o, ∃ Q ⊆ S, MajOpt t τ p q Q o then some h.choose else none

omit [OmitVal V] in
lemma majOpt_direct {P : Type*} {t : ℕ} {τ : List P → Option V} {p q : P} {Q : Finset P}
    {o : Option V} (h : MajOpt t τ p q Q o) (hpq : p ≠ q) : τ [q] = o :=
  h.2 [] (by simp) (by simp) (seq_pair.2 hpq)

omit [OmitVal V] in
/-- The only route `p|w|q` with `w` over `{p, q}`, `|w| ≤ 1` and without consecutive duplicates
is `p|q`. -/
lemma majOpt_pair {τ : List (Fin 3) → Option V} {p q : Fin 3} (hpq : p ≠ q) :
    MajOpt 1 τ p q {p, q} (τ [q]) := by
  refine ⟨by rw [Finset.card_pair hpq], fun w hw hl hs => ?_⟩
  match w, hw, hl, hs with
  | [], _, _, _ => rfl
  | [x], hw, _, hs =>
    exfalso
    have hx := hw x (by simp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [List.cons_append, List.nil_append, Seq, List.isChain_cons_cons] at hs
    rcases hx with rfl | rfl
    · exact hs.1 rfl
    · exact hs.2.1 rfl
  | _ :: _ :: _, _, hl, _ => simp at hl

/-- **Lemma 4.7 is false** (with `v` ranging over `V ∪ {⊥}`, as printed): in an admissible run with
`n = 3 > 2t = 2` and `t + 1 = 2` rounds, the non-faulty process `0` has a consistent majority for `⊥`. -/
theorem lemma_4_7_false (v : V) :
    wne 2 {2} (cexσ v) ∧ (0 : Fin 3) ∉ ({2} : Finset (Fin 3)) ∧
      MajOpt 1 (loc (cexσ v) 0) 0 2 {0, 2} none := by
  refine ⟨cex_wne v 2, by decide, ?_⟩
  have h := majOpt_pair (τ := loc (cexσ v) 0) (p := 0) (q := 2) (by decide)
  have e : loc (cexσ v) 0 [2] = none := by
    simp [loc, cexσ, ExecSys.σ_cons_cons, cexSys]
  rwa [e] at h

/-- **Line 8 with `v = ⊥` allowed violates agreement** (and outputs `⊥ ∉ V`): in the run above the
non-faulty `0` decides `⊥` at line 8 while the non-faulty `1` decides `v`. -/
theorem literal_line8_fails (v : V) :
    line8Lit 1 Finset.univ (loc (cexσ v) 0) 0 2 = some none ∧
      line8Lit 1 Finset.univ (loc (cexσ v) 1) 1 2 = some (some v) := by
  have val : ∀ (p : Fin 3) (o : Option V), p ≠ 2 → loc (cexσ v) p [2] = o →
      line8Lit 1 Finset.univ (loc (cexσ v) p) p 2 = some o := by
    intro p o hp ho
    have hex : ∃ o, ∃ Q ⊆ Finset.univ, MajOpt 1 (loc (cexσ v) p) p 2 Q o :=
      ⟨_, _, Finset.subset_univ _, majOpt_pair hp⟩
    simp only [line8Lit, hex, ↓reduceDIte, Option.some.injEq]
    obtain ⟨Q, -, hQ⟩ := hex.choose_spec
    rw [← majOpt_direct hQ hp, ho]
  exact ⟨val 0 none (by decide) (by simp [loc, cexσ, ExecSys.σ_cons_cons, cexSys]),
    val 1 (some v) (by decide) (by simp [loc, cexσ, ExecSys.σ_cons_cons, cexSys])⟩

end NonEquivocation
