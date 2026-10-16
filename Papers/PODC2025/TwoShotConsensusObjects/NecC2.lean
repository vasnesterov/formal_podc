import Papers.PODC2025.TwoShotConsensusObjects.NecC2Lemmas
import Papers.PODC2025.TwoShotConsensusObjects.NecReduction

/-!
# Necessity — Proposition 2: the class `C₂`

If at the critical configuration `fg` and `gf` are indistinguishable to both processes, then
either the object satisfies the properties of `C₂`, or consensus can be solved with one copy of
`O` fewer (the minimality argument of the paper, used here as an induction on the number of
copies).

The paper's graph `G` has the *operations* as nodes; here nodes are pairs (process, operation)
(`Adj`), which makes the graph bipartite. With operations as nodes a path may switch sides at an
operation available to both processes, and the parity argument of the paper ("`cᵢ ∈ m(p₀)` for
even `i`") would fail; the bipartite version is what the proof needs.
-/

namespace TwoShotCons

open Cslib.SharedMemory Cslib.SharedMemory.Recoverable

set_option linter.unusedSectionVars false

/-- A path of a `ReflTransGen` chain as a function. -/
lemma exists_walk {α : Type*} {r : α → α → Prop} {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ (n : ℕ) (w : ℕ → α), w 0 = a ∧ w n = b ∧ ∀ j < n, r (w j) (w (j + 1)) := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | tail _ hbc ih =>
    obtain ⟨n, w, h0, hn, hw⟩ := ih
    rename_i c _
    refine ⟨n + 1, fun j => if j ≤ n then w j else c, by simp [h0], by simp, fun j hj => ?_⟩
    by_cases hjn : j + 1 ≤ n
    · simp only [show j ≤ n by omega, hjn, if_true]; exact hw j (by omega)
    · have : j = n := by omega
      subst this
      simp only [le_refl, if_true, show ¬ j + 1 ≤ j by omega, if_false, hn]
      exact hbc

lemma own_succ (i : ℕ) : own (i + 1) = 1 - own i := by
  unfold own
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · have : (i + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (i + 1) % 2 = 0 := by omega
    simp [h, this]

variable {ιR ιS : Type} [DecidableEq ιR] [DecidableEq ιS] {R : ιR → ObjSpec} {O : ObjSpec}
  {A : Alg 2 (withRW (ιS := ιS) R O)}

lemma noAcc_of_accCount_zero {C : Cfg A} {r : Fin 2} {i : ιR ⊕ ιS} {t : ℕ}
    (h : accCount C (solo r t) r i = 0) : ∀ t' < t, objOf (run C (solo r t')) r ≠ some i := by
  intro t' ht' hacc
  have hs : solo r t = solo r t' ++ [Ev.step r] ++ solo r (t - t' - 1) := by
    simp only [solo, List.append_assoc, List.singleton_append, ← List.replicate_succ,
      ← List.replicate_add]
    congr 1; omega
  rw [hs, accCount_append, accCount_append] at h
  have : accCount (run C (solo r t')) [Ev.step r] r i = 1 := by simp [accCount_cons, hacc]
  omega

namespace KSetup

variable (S : KSetup A)

/-- Adjacency in the bipartite version of the paper's graph `G`. -/
def Adj (u v : Fin 2 × O.Op) : Prop :=
  (u.1 = 0 ∧ v.1 = 1 ∧ S.Edge u.2 v.2) ∨ (u.1 = 1 ∧ v.1 = 0 ∧ S.Edge v.2 u.2)

lemma adj_symm : Symmetric S.Adj := by
  rintro u v (⟨h0, h1, he⟩ | ⟨h1, h0, he⟩)
  · exact Or.inr ⟨h1, h0, he⟩
  · exact Or.inl ⟨h0, h1, he⟩

/-- Connectivity in the graph. -/
def Conn (u v : Fin 2 × O.Op) : Prop := Relation.ReflTransGen S.Adj u v

lemma conn_symm {u v : Fin 2 × O.Op} (h : S.Conn u v) : S.Conn v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head (S.adj_symm hbc) ih

lemma edge_mem {m : Fin 2 → Set O.Op} (hm : Allowed m A) {c c' : O.Op} (he : S.Edge c c') :
    c ∈ m 0 ∧ c' ∈ m 1 := by
  obtain ⟨γ, hγ, -, ⟨κ, hc⟩, ⟨κ', hc'⟩⟩ := he
  have hB : S.Branch 0 (run S.F γ) := ((S.branch_one 0).next 1).ext γ hγ
  exact ⟨S.allowed_of_branch hm hB hc, S.allowed_of_branch hm hB hc'⟩

/-- **Assembling class `C₂`** from a path `c₁ … f'` in the graph. -/
theorem c2_of_conn (hA : WFConsensus A) (h2 : TwoShot A) {m : Fin 2 → Set O.Op}
    (hm : Allowed m A)
    (h0 : ¬ Dist O S.s 0 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    (h1 : ¬ Dist O S.s 1 [(0, S.op 0), (1, S.op 1)] [(1, S.op 1), (0, S.op 0)])
    {c0 c1 f' g' : O.Op} (he01 : S.Edge c0 c1) (heFG : S.Edge f' g')
    (D3 : DistBoth O S.s [(0, S.op 0), (0, c0), (1, S.op 1), (1, c1)]
      [(1, S.op 1), (0, S.op 0), (0, c0), (1, c1)])
    (D4 : Dist O S.s 1 [(0, S.op 0), (0, c0), (1, S.op 1)] [(1, S.op 1)] ∨
      DistBoth O S.s [(0, S.op 0), (0, c0), (1, S.op 1), (1, c1)]
        [(1, S.op 1), (0, S.op 0), (1, c1), (0, c0)])
    (D5 : DistBoth O S.s [(1, S.op 1), (1, g'), (0, S.op 0), (0, f')]
      [(0, S.op 0), (1, S.op 1), (1, g'), (0, f')])
    (D6 : Dist O S.s 0 [(1, S.op 1), (1, g'), (0, S.op 0)] [(0, S.op 0)] ∨
      DistBoth O S.s [(1, S.op 1), (1, g'), (0, S.op 0), (0, f')]
        [(0, S.op 0), (1, S.op 1), (0, f'), (1, g')])
    (hconn : S.Conn (1, c1) (0, f')) : C2Cond O m := by
  classical
  obtain ⟨n, w, hw0, hwn, hw⟩ := exists_walk hconn
  have hside : ∀ j ≤ n, (w j).1 = own (j + 1) := by
    intro j hj
    induction j with
    | zero => rw [hw0]; rfl
    | succ j ih =>
      have := ih (by omega)
      rw [own_succ, ← this]
      rcases hw j (by omega) with ⟨ha, hb, -⟩ | ⟨ha, hb, -⟩
      · rw [ha, hb]; rfl
      · rw [ha, hb]; rfl
  have hnodd : Odd n := by
    have := hside n le_rfl
    rw [hwn] at this
    unfold own at this
    split_ifs at this with h
    · exact Nat.odd_iff.2 (by omega)
    · simp at this
  set N := n + 2 with hN
  let c : ℕ → O.Op := fun i => if i = 0 then c0 else if i ≤ n + 1 then (w (i - 1)).2 else g'
  have hc0 : c 0 = c0 := by simp [c]
  have hc1 : c 1 = c1 := by simp [c, hw0]
  have hcN : c N = g' := by simp [c, hN]
  have hcN1 : c (N - 1) = f' := by
    have : N - 1 = n + 1 := by omega
    simp [c, this, hwn]
  have hcmid : ∀ i, 1 ≤ i → i ≤ n + 1 → c i = (w (i - 1)).2 := by
    intro i h1 h2; simp [c, show i ≠ 0 by omega, h2]
  have hownN : own N = 1 := by
    obtain ⟨r, hr⟩ := hnodd
    unfold own; rw [if_neg (by omega)]
  have hown0 : own 0 = 0 := rfl
  have hown1 : own 1 = 1 := rfl
  -- consecutive operations are adjacent
  have hpair : ∀ i < N, S.Adj (own i, c i) (own (i + 1), c (i + 1)) := by
    intro i hi
    rcases Nat.lt_or_ge i 1 with h | h
    · have : i = 0 := by omega
      subst this
      exact Or.inl ⟨rfl, rfl, by rw [hc0, hc1]; exact he01⟩
    rcases Nat.lt_or_ge i (n + 1) with h' | h'
    · have hu : (own i, c i) = w (i - 1) := by
        have := hside (i - 1) (by omega)
        rw [show i - 1 + 1 = i by omega] at this
        exact Prod.ext this.symm (hcmid i h (by omega))
      have hv : (own (i + 1), c (i + 1)) = w i := by
        have := hside i (by omega)
        refine Prod.ext this.symm ?_
        rw [hcmid (i + 1) (by omega) (by omega), show i + 1 - 1 = i by omega]
      rw [hu, hv]
      have := hw (i - 1) (by omega)
      rwa [show i - 1 + 1 = i by omega] at this
    · have : i = n + 1 := by omega
      subst this
      have hu : own (n + 1) = 0 := by rw [← hside n le_rfl, hwn]
      have hv : own (n + 1 + 1) = 1 := hownN
      refine Or.inl ⟨hu, hv, ?_⟩
      simp only
      rw [show n + 1 + 1 = N by omega, hcN, show c (n + 1) = c (N - 1) by congr 1, hcN1]
      exact heFG
  refine ⟨S.s, S.op 0, S.op 1, N, c, ?_, S.allowed_crit hm 0, S.allowed_crit hm 1, ?_, h0, h1,
    ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨r, hr⟩ := hnodd; exact ⟨r + 1, by omega⟩
  · intro i hi
    rcases Nat.lt_or_ge i N with h | h
    · rcases hpair i h with ⟨ha, -, he⟩ | ⟨ha, -, he⟩
      · simp only at ha he; rw [ha]; exact (S.edge_mem hm he).1
      · simp only at ha he; rw [ha]; exact (S.edge_mem hm he).2
    · have : i = N := by omega
      subst this
      rw [hcN, hownN]; exact (S.edge_mem hm heFG).2
  · intro i hi
    rcases hpair i hi with ⟨ha, hb, he⟩ | ⟨ha, hb, he⟩
    · simp only at ha hb he
      rw [ha, hb]
      exact S.edge_dist hA h2 h0 h1 he
    · simp only at ha hb he
      rw [ha, hb]
      obtain ⟨e1, e2, e3, e4⟩ := S.edge_dist hA h2 h0 h1 he
      exact ⟨e4, e3, e2, e1⟩
  · rw [hc0, hc1]; exact D3
  · rw [hc0, hc1]; exact D4
  · rw [hcN, hcN1]; exact D5
  · rw [hcN, hcN1]; exact D6

end KSetup

end TwoShotCons
