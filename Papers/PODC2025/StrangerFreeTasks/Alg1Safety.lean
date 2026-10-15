import Papers.PODC2025.StrangerFreeTasks.Alg1SafetySnapshot
import Papers.PODC2025.StrangerFreeTasks.Alg1SafetyObliterate

/-!
# Safety of Algorithm 1

Algorithm 1 solves `k`-bounded lattice agreement (safety: validity, self-inclusion and
containment), for every `k` and every (possibly infinite) set of processes `P`.

The paper only sketches the containment argument ("`k` processes are not enough to obliterate
all `k + 1` registers before they have to read the whole array"). The proof here:
* (Lemma B, `sInv_of_run`) an output `S` with `|S| ≤ k` comes from a successful double collect,
  so there is a past configuration in which every register's `seen` set equals `S`;
* (Lemma A, `card_union_of_obliterate`) if all registers are `S`-dirty at `C₁` and all are
  `S`-clean at a later `C₂`, then the registers at `C₂` together have seen `≥ k + 1` processes;
* two outputs `S_p, S_q` of size `≤ k` have such past configurations, ordered in time, say
  `C_p` before `C_q`; if `S_p ⊄ S_q`, all registers are `S_p`-clean at `C_q`, so `|S_q| ≥ k + 1`
  by Lemma A, a contradiction.

One-shotness of the execution is not needed.
-/

namespace Cslib.SharedMemory.StrangerFree

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {k : ℕ}

/-- Outputs are the current `out` of a process that has decided. -/
lemma out_of_outputs {α : List (Label P (laObj P))} {C : Cfg P k}
    (h : (alg1 k).run α = some C) {p : P} {o : Finset P} (ho : outputs α p = some o) :
    (C.loc p).phase = .done ∧ o = (C.loc p).out := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.1 ho
  exact (bInv_of_run h).resp p o (by rw [ht]; exact List.mem_cons_self)

/-- Containment for two decision points ordered in time. -/
lemma subset_of_prefix {α γ : List (Label P (laObj P))} {C₁ C₂ : Cfg P k} {A B : Finset P}
    (h₁ : (alg1 k).run α = some C₁) (h₂ : (alg1 k).run (α ++ γ) = some C₂)
    (hA : ∀ r, (C₁.mem r).seen = A) (hB : ∀ r, (C₂.mem r).seen = B) (hBk : B.card ≤ k) :
    A ⊆ B := by
  by_contra hAB
  have := card_union_of_obliterate h₁ h₂ (S := A) (fun r => (hA r).ge)
    (fun r => by rw [hB r]; exact hAB) (U := B) (fun r => (hB r).le)
  omega

/-- Containment of outputs of size at most `k`. -/
theorem alg1_containment {α : List (Label P (laObj P))} {C : Cfg P k}
    (h : (alg1 k).run α = some C) {p q : P} (hp : (C.loc p).phase = .done)
    (hq : (C.loc q).phase = .done) (hpk : (C.loc p).out.card ≤ k)
    (hqk : (C.loc q).out.card ≤ k) :
    (C.loc p).out ⊆ (C.loc q).out ∨ (C.loc q).out ⊆ (C.loc p).out := by
  have hS := sInv_of_run h
  obtain ⟨Cp, ⟨αp, βp, hαp, hrp⟩, hsp⟩ := hS.done p hp hpk
  obtain ⟨Cq, ⟨αq, βq, hαq, hrq⟩, hsq⟩ := hS.done q hq hqk
  have h1 : αp <+: α := ⟨βp, hαp.symm⟩
  have h2 : αq <+: α := ⟨βq, hαq.symm⟩
  rcases List.prefix_or_prefix_of_prefix h1 h2 with ⟨γ, hγ⟩ | ⟨γ, hγ⟩
  · subst hγ; exact Or.inl (subset_of_prefix hrp hrq hsp hsq hqk)
  · subst hγ; exact Or.inr (subset_of_prefix hrq hrp hsq hsp hpk)

/-- **Algorithm 1 solves `k`-bounded lattice agreement** (safety part of Theorem 1 of the
paper): validity, self-inclusion and containment hold in every finite execution, for every
`k` and every set of processes. -/
theorem alg1_solves (k : ℕ) {P : Type} [DecidableEq P] :
    (alg1 (P := P) k).Solves (boundedLA P k) := by
  rintro α ⟨C, hC⟩ - p o ho
  have hB := bInv_of_run hC
  obtain ⟨hpd, rfl⟩ := out_of_outputs hC ho
  refine ⟨fun q hq => ?_, ?_, fun p' o' ho' hk hk' => ?_⟩
  · rw [hB.out_eq p hpd] at hq
    have := hB.seen_inv p (by simp [hpd]) q hq
    change (opsOf α q).head? ≠ none
    rwa [ne_eq, List.head?_eq_none_iff]
  · rw [hB.out_eq p hpd]; exact hB.self p
  · obtain ⟨hpd', rfl⟩ := out_of_outputs hC ho'
    exact alg1_containment hC hpd hpd' hk hk'

end Cslib.SharedMemory.StrangerFree
