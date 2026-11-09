import Papers.PODC2020.SelfStabHighDynamics.Alg2.Round

/-!
# Algorithm 2: executions (Lemmas 5–9, Corollary 7)

We fix a dynamic graph `G` with vertex set `V` (`IsDG V G`) and an initial configuration `γ` of
Algorithm 2 for `V`. Times are 0-indexed: `exec … t` is the configuration at the end of Round `t`
(the paper's "beginning of Round `t + 1`"), and the paper's Round `Δ + i` (`i ≥ 1`) is the step
from `exec … t` to `exec … (t + 1)` with `t ≥ Δ`.
-/

namespace Podc.SelfStabHighDynamics.Alg2

open Cslib.HeardOf Cslib.DynNet
open StabilizingLEDynamic (DG IsDG)

variable {ι : Type*} [LinearOrder ι] {Δ : ℕ}

theorem sent_finite (s : MSt ι) : (sent Δ s).Finite :=
  s.mem.toFinset.finite_toSet.subset fun x hx => by simpa using hx.1

/-- The pairs received by `p` in round `t`, in processing order. -/
noncomputable def mbx (Δ : ℕ) (G : DG ι) (γ : ι → MSt ι) (t : ℕ) (p : ι) : List (ι × ℕ) :=
  (rfin (sent Δ) p (msgs (G t) ((alg Δ).exec G γ t) p)).toList

variable {V : Finset ι} {G : DG ι} {γ : ι → MSt ι}

theorem exec_succ (G : DG ι) (γ : ι → MSt ι) (t : ℕ) (p : ι) :
    (alg Δ).exec G γ (t + 1) p = round Δ p ((alg Δ).exec G γ t p) (mbx Δ G γ t p) := by
  change next (alg Δ).step (G t) ((alg Δ).exec G γ t) p = _
  simp only [next, alg, mbx, msgs_self, Option.getD_some]

theorem mem_mbx (hG : IsDG V G) {t : ℕ} {p : ι} {x : ι × ℕ} :
    x ∈ mbx Δ G γ t p ↔ ∃ r, G t r p ∧ x ∈ ((alg Δ).exec G γ t r).mem ∧ x.2 < Δ := by
  rw [mbx, Finset.mem_toList, mem_rfin_msgs sent_finite hG]
  rfl

theorem mem_S {p : ι} {s : MSt ι} :
    s ∈ (alg Δ).S V p ↔ s.n = V.card ∧ Inv s.n s.mem ∧ ∀ x ∈ s.mem, x.2 ≤ Δ := by
  simp only [alg, Inv, Set.mem_ofPred_eq, and_assoc]

/-- The configurations of Algorithm 2 for `V` are invariant (`n = |V|`, at most `n` pairs with
distinct identifiers, timestamps `≤ Δ`). -/
theorem exec_cfg (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V) (t : ℕ) :
    (alg Δ).exec G γ t ∈ (alg Δ).Cfg V := by
  induction t with
  | zero => exact hγ
  | succ t ih =>
    intro p hp
    obtain ⟨hn, hinv, hle⟩ := mem_S.1 (ih p hp)
    have hpos : 0 < ((alg Δ).exec G γ t p).n := hn ▸ Finset.card_pos.2 ⟨p, hp⟩
    rw [exec_succ]
    refine mem_S.2 ⟨hn, inv_round hpos hinv, round_le hle fun x hx _ => ?_⟩
    obtain ⟨r, -, -, h⟩ := (mem_mbx hG).1 hx
    exact h.le

/-- After every round, `⟨id(p), 0⟩ ∈ members(p)` (line 7). -/
theorem self_mem (G : DG ι) (γ : ι → MSt ι) (t : ℕ) (p : ι) :
    (p, 0) ∈ ((alg Δ).exec G γ (t + 1) p).mem := by
  rw [exec_succ]; exact round_self

theorem lid_exec_succ (G : DG ι) (γ : ι → MSt ι) (t : ℕ) (p : ι) :
    ((alg Δ).exec G γ (t + 1) p).lid = minKey ((alg Δ).exec G γ (t + 1) p).mem p := by
  rw [exec_succ]; rfl

/-! ### Lemma 5 and Corollary 7 -/

/-- **Lemma 5** (0-indexed: `exec … t` is the beginning of Round `t + 1`). Timestamps of a fake
identifier `f` are at least `min(Δ, t)` after `t` rounds. No assumption on the initial
configuration is needed. -/
theorem fake_ge (hG : IsDG V G) {f : ι} (hf : f ∉ V) :
    ∀ t, ∀ p ∈ V, ∀ x ∈ ((alg Δ).exec G γ t p).mem, x.1 = f → min Δ t ≤ x.2 := by
  intro t
  induction t with
  | zero => intro p _ x _ _; simp
  | succ t ih =>
    intro p hp
    rw [exec_succ]
    have hfp : f ≠ p := fun h => hf (h ▸ hp)
    have := round_ge (Δ := Δ) (s := (alg Δ).exec G γ t p) (mb := mbx Δ G γ t p) hfp
      (L := min Δ t) (ih p hp) (fun x hx hxf => by
        obtain ⟨r, hr, hx, -⟩ := (mem_mbx hG).1 hx
        exact ih r (hG t r p hr).1 x hx hxf)
    intro x hx hxf
    have := this x hx hxf
    omega

/-- **Corollary 7.** From time `Δ` on, every pair sent by a process carries a real identifier. -/
theorem sent_mem (hG : IsDG V G) {t : ℕ} (ht : Δ ≤ t) {p : ι} (hp : p ∈ V) {x : ι × ℕ}
    (hx : x ∈ sent Δ ((alg Δ).exec G γ t p)) : x.1 ∈ V := by
  by_contra hf
  have := fake_ge hG hf t p hp x hx.1 rfl
  have := hx.2
  omega

theorem mbx_mem (hG : IsDG V G) {t : ℕ} (ht : Δ ≤ t) {p : ι} {x : ι × ℕ}
    (hx : x ∈ mbx Δ G γ t p) : x.1 ∈ V := by
  obtain ⟨r, hr, hx, hlt⟩ := (mem_mbx hG).1 hx
  exact sent_mem hG ht (hG t r p hr).1 ⟨hx, hlt⟩

/-! ### Lemma 6 -/

variable (hG : IsDG V G) (hγ : γ ∈ (alg Δ).Cfg V)
include hG hγ

theorem Tail.exec_succ {t : ℕ} (ht : Δ ≤ t) {p : ι} (hp : p ∈ V) {k : ι} {B : ℕ}
    (h : Tail V ((alg Δ).exec G γ t p).mem k B) :
    Tail V ((alg Δ).exec G γ (t + 1) p).mem k (B + 1) := by
  obtain ⟨hn, hinv, -⟩ := mem_S.1 (exec_cfg hG hγ t p hp)
  rw [Alg2.exec_succ]
  exact h.round hp hn hinv fun x hx _ => mbx_mem hG ht hx

theorem Tail.exec_add {t : ℕ} (ht : Δ ≤ t) {p : ι} (hp : p ∈ V) {k : ι} {B : ℕ}
    (h : Tail V ((alg Δ).exec G γ t p).mem k B) (u : ℕ) :
    Tail V ((alg Δ).exec G γ (t + u) p).mem k (B + u) := by
  induction u with
  | zero => exact h
  | succ u ih => exact (ih.exec_succ hG hγ (by omega) hp).mono (by omega)

/-- A pair `⟨q, ts⟩` received by `p ≠ q` in round `t ≥ Δ` (0-indexed) is, after the round, in a
suffix of real identifiers of `members(p)`, with timestamp `≤ ts + 1`. -/
theorem tail_recv {t : ℕ} (ht : Δ ≤ t) {p : ι} (hp : p ∈ V) {x : ι × ℕ}
    (hx : x ∈ mbx Δ G γ t p) (hxp : x.1 ≠ p) :
    Tail V ((alg Δ).exec G γ (t + 1) p).mem x.1 (x.2 + 1) := by
  obtain ⟨hn, hinv, -⟩ := mem_S.1 (exec_cfg hG hγ t p hp)
  rw [Alg2.exec_succ]
  exact tail_round_recv hp hn hinv (fun x hx _ => mbx_mem hG ht hx) hx hxp

omit hG hγ in
theorem tail_self {t : ℕ} {p : ι} (hp : p ∈ V) :
    Tail V ((alg Δ).exec G γ (t + 1) p).mem p 0 := by
  rw [Alg2.exec_succ]; exact tail_round_self hp

/-- **Lemma 6.** If `p ∈ V` receives an identifier `q` in a round `t ≥ Δ` (0-indexed, i.e. the
paper's Round `Δ + i`, `i ≥ 1`), or `q = p`, then `q ∈ members(p)` forever after this round. -/
theorem persist {t : ℕ} (ht : Δ ≤ t) {p q : ι} (hp : p ∈ V)
    (hins : q = p ∨ ∃ r, G t r p ∧ ∃ ts, (q, ts) ∈ sent Δ ((alg Δ).exec G γ t r)) :
    ∀ u > t, q ∈ keys ((alg Δ).exec G γ u p).mem := by
  intro u hu
  obtain ⟨u, rfl⟩ : ∃ u', u = t + 1 + u' := ⟨u - (t + 1), by omega⟩
  have h : ∃ B, Tail V ((alg Δ).exec G γ (t + 1) p).mem q B := by
    by_cases hqp : q = p
    · exact ⟨0, by subst hqp; exact tail_self hp⟩
    · obtain ⟨r, hr, ts, hs, hlt⟩ := hins.resolve_left hqp
      exact ⟨_, tail_recv hG hγ ht hp (x := (q, ts)) ((mem_mbx hG).2 ⟨r, hr, hs, hlt⟩) hqp⟩
  obtain ⟨B, h⟩ := h
  exact (h.exec_add hG hγ (by omega) hp u).mem_keys

/-! ### Lemma 7 -/

/-- **Lemma 7** (0-indexed). If `j ≥ Δ`, `j ≥ 1` and there is a journey from `q` to `p` of temporal
length `≤ Δ` starting at time `j` (the paper's `t(q, p) = j`), then `q ∈ members(p)` from time
`j + Δ` on. -/
theorem mem_of_tdist {p q : ι} (hq : q ∈ V) {j : ℕ} (hj : Δ ≤ j) (hj1 : 1 ≤ j)
    (hd : tdist G j q p ≤ Δ) : ∀ t ≥ j + Δ, q ∈ keys ((alg Δ).exec G γ t p).mem := by
  have hJ : Journey G j q (j + Δ) p := tdist_le_iff.1 hd
  have key : p ∈ V ∧ Tail V ((alg Δ).exec G γ (j + Δ) p).mem q (j + Δ - j) := by
    refine hJ.of_inv (P := fun τ a => a ∈ V ∧ Tail V ((alg Δ).exec G γ τ a).mem q (τ - j))
      ⟨hq, ?_⟩ ?_
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      exact (tail_self hq).mono (Nat.zero_le _)
    · rintro τ a b hjτ hτ ⟨ha, hT⟩ (rfl | hab)
      · exact ⟨ha, (hT.exec_succ hG hγ (by omega) ha).mono (by omega)⟩
      · have hb : b ∈ V := (hG τ a b hab).2.1
        refine ⟨hb, ?_⟩
        by_cases hqb : q = b
        · subst hqb; exact (tail_self hq).mono (Nat.zero_le _)
        · obtain ⟨ts, hts, hmem⟩ := hT.exists
          have hx : (q, ts) ∈ mbx Δ G γ τ b := (mem_mbx hG).2 ⟨a, hab, hmem, by simp; omega⟩
          exact (tail_recv hG hγ (by omega) hb hx hqb).mono (by simp; omega)
  intro t ht
  obtain ⟨u, rfl⟩ : ∃ u, t = j + Δ + u := ⟨t - (j + Δ), by omega⟩
  exact (key.2.exec_add hG hγ (by omega) key.1 u).mem_keys

end Podc.SelfStabHighDynamics.Alg2
