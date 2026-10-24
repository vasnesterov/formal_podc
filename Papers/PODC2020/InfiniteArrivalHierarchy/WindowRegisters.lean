import Papers.PODC2020.InfiniteArrivalHierarchy.Objects
import Podc.Computability.Distributed.SharedMemory.Arrival.Valency

/-!
# Window registers are not universal in the infinite arrival model (Section 6)

Perrin, Mostéfaoui, Bonin, *Extending the Wait-free Hierarchy to Multi-Threaded Systems*,
PODC 2020: Lemma 8, Lemma 9 and Proposition 5 (`MA₃[WReg]` is not universal).

Model: processes `ℕ` (infinite arrival: every infinite schedule is allowed), arbitrarily many
window registers of arbitrary sizes (`windowObj (W i) (w i)`, the size and the value type of each
register being fixed by the algorithm; registers are `1`-window registers), all allocated and
initialised at set-up (infinite memory allocation). Processes start with their binary inputs.

* `crit_write_same` (**Lemma 9**): in an `n`-critical execution, `p₀, …, p_{n-1}` are all poised
  to write to the same `k`-window register, with `k ≥ n`;
* `window_not_consensus` (**Proposition 5**): no algorithm solves binary consensus (agreement, weak
  validity, wait-freedom) with window registers in the infinite arrival model.

Lemma 8 is `Cslib.SharedMemory.Arrival.exists_crit` (for any finite set of processes).
-/

namespace Podc.InfiniteArrivalHierarchy

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

/-- Window registers `windowObj (W i) (w i)`, `i : ι`. -/
abbrev WT {ι : Type} (W : ι → Type) (w : ι → ℕ) : ι → ObjSpec := fun i => windowObj (W i) (w i)

/-- The processes `p₀, …, p_{n-1}`. -/
def below (n : ℕ) : Set ℕ := {p | p < n}

lemma below_mono {n n' : ℕ} (h : n ≤ n') : below n ⊆ below n' :=
  fun _ hp => lt_of_lt_of_le hp h

variable {ι : Type} [DecidableEq ι] {W : ι → Type} {w : ι → ℕ}
  {A : Alg (WT W w) ℕ Bool Bool}

/-- A block write: processes `ws` (distinct), all poised to write on the window register `i`,
take one step each. -/
lemma run_block (C : Cfg A) (i : ι) (ws : List ℕ) (hnd : ws.Nodup) (v : ℕ → W i)
    (k : ℕ → List (W i) → A.L)
    (h : ∀ r ∈ ws, A.act (C.loc r) = .access i (.write (v r)) (k r)) :
    (A.run C ws).mem = Function.update C.mem i
      ((windowObj (W i) (w i)).runOps (C.mem i) (ws.map (fun r => .write (v r)))) ∧
    ∀ r, (A.run C ws).loc r = if r ∈ ws then k r [] else C.loc r := by
  induction ws generalizing C with
  | nil =>
    exact ⟨(Function.update_eq_self _ _).symm, fun r => by simp⟩
  | cons r ws ih =>
    have hr := h r (by simp)
    have hnd' := (List.nodup_cons.1 hnd)
    have h' : ∀ q ∈ ws, A.act ((C.step r).loc q) = .access i (.write (v q)) (k q) := by
      intro q hq
      have hqr : q ≠ r := fun e => hnd'.1 (e ▸ hq)
      rw [Cfg.step_loc_other C hqr]; exact h q (by simp [hq])
    obtain ⟨ih1, ih2⟩ := ih (C.step r) hnd'.2 h'
    rw [Alg.run_cons]
    refine ⟨?_, fun q => ?_⟩
    · rw [ih1, Cfg.step_of_access hr]
      simp only [Function.update_idem, Function.update_self]
      rfl
    · rw [ih2]
      by_cases hq : q ∈ ws
      · have : q ∈ r :: ws := by simp [hq]
        simp [hq, this]
      · by_cases hqr : q = r
        · subst hqr
          simp [hq, Cfg.step_loc_self_of_access hr]
        · simp [hq, hqr, Cfg.step_loc_other C hqr]

lemma access_inj {L : Type} {i j : ι} {o : (WT W w i).Op} {o' : (WT W w j).Op}
    {k : (WT W w i).Resp → L} {k' : (WT W w j).Resp → L} {Y : Type}
    (h : (Act.access i o k : Act (WT W w) L Y) = Act.access j o' k') : i = j := by
  cases h; rfl

section Lemma9

variable (hag : Agreement A (fun _ => True)) (hwf : WaitFree A (fun s => (Set.range s).Finite))
include hag hwf

/-- A process of `Q` in a bivalent execution is poised on some object. -/
lemma Biv.exists_poised {Q : Set ℕ} {x : ℕ → Bool} {α : List ℕ} (hb : Biv A Q x α) {p : ℕ}
    (hp : p ∈ Q) : ∃ i o k, A.act ((A.exec x α).loc p) = .access i o k := by
  rcases Cfg.out_or_poised (A.exec x α) p with ⟨v, hv⟩ | ⟨i, o, k, h⟩
  · exact absurd hv (hb.not_out hag (Or.inr hp) v)
  · exact ⟨i, o, k, h⟩

/-- The pair argument of Lemma 9: two processes of opposite teams of a critical execution are
both poised to write to the same window register. -/
lemma crit_pair {Q : Set ℕ} {x : ℕ → Bool} {α : List ℕ} (hc : Crit A Q x α) {r s : ℕ}
    (hrQ : r ∈ Q) (hsQ : s ∈ Q)
    (hr : ¬ CanDec A Q x (α ++ [r]) true) (hs : ¬ CanDec A Q x (α ++ [s]) false) :
    ∃ i, (∃ v k, A.act ((A.exec x α).loc r) = .access i (.write v) k) ∧
      (∃ v k, A.act ((A.exec x α).loc s) = .access i (.write v) k) := by
  have hrs : r ≠ s := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_canDec hwf hrQ x (α ++ [r])
    cases v
    · exact hs hv
    · exact hr hv
  set C := A.exec x α with hC
  have hexec1 : ∀ a b : ℕ, A.exec x (α ++ [a] ++ [b]) = (C.step a).step b := by
    intro a b; rw [Alg.exec_concat, Alg.exec_concat]
  have hexec0 : ∀ a : ℕ, A.exec x (α ++ [a] ++ []) = C.step a := by
    intro a; rw [List.append_nil, Alg.exec_concat]
  have hsQ' : ∀ q ∈ [s], q ∈ Q := by simp [hsQ]
  have hrQ' : ∀ q ∈ [r], q ∈ Q := by simp [hrQ]
  obtain ⟨i, o, k, hri⟩ := Biv.exists_poised hag hwf hc.1 hrQ
  obtain ⟨j, o', k', hsj⟩ := Biv.exists_poised hag hwf hc.1 hsQ
  by_cases hij : i = j
  · subst hij
    cases o with
    | read =>
      exfalso
      have h := Cfg.step_step_agreeOn_of_readOnly C hri (by simp) hrs
      exact false_of_agreeOn hwf hr hs hsQ' (by simp) hsQ (β := [s]) (γ := [])
        (by rw [hexec1, hexec0]; exact h)
    | write v =>
      cases o' with
      | read =>
        exfalso
        have h := Cfg.step_step_agreeOn_of_readOnly C hsj (by simp) hrs.symm
        exact false_of_agreeOn hwf hr hs (by simp) hrQ' hrQ (β := []) (γ := [r])
          (by rw [hexec1, hexec0]; exact h.symm)
      | write v' => exact ⟨i, ⟨v, k, hri⟩, ⟨v', k', hsj⟩⟩
  · exfalso
    have hcomm := Cfg.step_comm C ⟨o, k, hri⟩ ⟨o', k', hsj⟩ hrs hij
    exact false_of_agreeOn hwf hr hs hsQ' hrQ' hrQ (β := [s]) (γ := [r])
      (by rw [hexec1, hexec1, hcomm]; exact AgreeOn.refl _ _)

/-- **Lemma 9.** In an `n`-critical execution, the processes `p₀, …, p_{n-1}` are all poised to
write to the same window register, of size `k ≥ n`. -/
theorem crit_write_same {n : ℕ} {x : ℕ → Bool} {α : List ℕ} (hc : Crit A (below n) x α) :
    ∃ i, n ≤ w i ∧ ∀ p < n, ∃ v k, A.act ((A.exec x α).loc p) = .access i (.write v) k := by
  classical
  obtain ⟨p₀, hp₀, q₀, hq₀, -, hp₀t, -, hq₀f⟩ := Crit.exists_teams hwf hag hc
  obtain ⟨i, ⟨v₀, k₀, hpi⟩, ⟨vq, kq, hqi⟩⟩ := crit_pair hag hwf hc hp₀ hq₀ hp₀t hq₀f
  set C := A.exec x α with hC
  -- every process of `below n` writes to `i`
  have hall : ∀ p < n, ∃ v k, A.act (C.loc p) = .access i (.write v) k := by
    intro p hp
    obtain ⟨v, hv⟩ := exists_canDec hwf (show p ∈ below n from hp) x (α ++ [p])
    cases v
    · have hpt : ¬ CanDec A (below n) x (α ++ [p]) true := fun ht => hc.2 p hp ⟨hv, ht⟩
      obtain ⟨j, ⟨v, k, hpj⟩, ⟨v', k', hqj⟩⟩ := crit_pair hag hwf hc hp hq₀ hpt hq₀f
      have : j = i := access_inj (hqj.symm.trans hqi)
      subst this; exact ⟨v, k, hpj⟩
    · have hpf : ¬ CanDec A (below n) x (α ++ [p]) false := fun hf => hc.2 p hp ⟨hf, hv⟩
      obtain ⟨j, ⟨v', k', hp₀j⟩, ⟨v, k, hpj⟩⟩ := crit_pair hag hwf hc hp₀ hp hp₀t hpf
      have : j = i := access_inj (hp₀j.symm.trans hpi)
      subst this; exact ⟨v, k, hpj⟩
  refine ⟨i, ?_, hall⟩
  by_contra hlt
  push Not at hlt
  have : Nonempty (W i) := ⟨v₀⟩
  have : Nonempty ((WT W w i).Resp → A.L) := ⟨k₀⟩
  choose! vv kk hvk using hall
  have hpq : p₀ ≠ q₀ := by
    rintro rfl
    obtain ⟨v, hv⟩ := exists_canDec hwf hp₀ x (α ++ [p₀])
    cases v
    · exact hq₀f hv
    · exact hp₀t hv
  -- the other processes, starting with `q₀`
  set rest := ((List.range n).erase p₀).erase q₀ with hrest
  have hnd0 : ((List.range n).erase p₀).Nodup := (List.nodup_range).erase _
  have hq₀mem : q₀ ∈ (List.range n).erase p₀ :=
    (List.Nodup.mem_erase_iff (List.nodup_range)).2 ⟨hpq.symm, List.mem_range.2 hq₀⟩
  have hothers_nd : (q₀ :: rest).Nodup :=
    List.nodup_cons.2 ⟨hnd0.not_mem_erase, hnd0.erase _⟩
  have hothers_len : (q₀ :: rest).length = n - 1 := by
    rw [List.length_cons, hrest, List.length_erase_of_mem hq₀mem,
      List.length_erase_of_mem (List.mem_range.2 hp₀), List.length_range]
    have : 2 ≤ n := by
      rcases Nat.lt_or_ge p₀ q₀ with h | h
      · exact lt_of_le_of_lt (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) h)) hq₀
      · have : q₀ < p₀ := lt_of_le_of_ne h (Ne.symm hpq)
        exact lt_of_le_of_lt (Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le _) this)) hp₀
    omega
  have hothers_mem : ∀ r ∈ q₀ :: rest, r < n ∧ r ≠ p₀ := by
    intro r hr
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨hq₀, hpq.symm⟩
    · have h1 := List.mem_of_mem_erase hr
      have h2 := (List.Nodup.mem_erase_iff (List.nodup_range)).1 h1
      exact ⟨List.mem_range.1 h2.2, h2.1⟩
  have hwrites : ∀ D : Cfg A, (∀ r ∈ q₀ :: rest, D.loc r = C.loc r) →
      ∀ r ∈ q₀ :: rest, A.act (D.loc r) = .access i (.write (vv r)) (kk r) := by
    intro D hD r hr
    rw [hD r hr]; exact hvk r (hothers_mem r hr).1
  -- the two executions
  have hA := run_block (C.step p₀) i (q₀ :: rest) hothers_nd vv kk
    (hwrites _ (fun r hr => Cfg.step_loc_other C (hothers_mem r hr).2))
  have hB := run_block C i (q₀ :: rest) hothers_nd vv kk (hwrites _ (fun _ _ => rfl))
  have hp₀w := hvk p₀ hp₀
  have hagree : AgreeOn {q₀} (A.exec x (α ++ [p₀] ++ (q₀ :: rest)))
      (A.exec x (α ++ [q₀] ++ rest)) := by
    have e1 : A.exec x (α ++ [p₀] ++ (q₀ :: rest)) = A.run (C.step p₀) (q₀ :: rest) := by
      rw [Alg.exec_append, Alg.exec_concat]
    have e2 : A.exec x (α ++ [q₀] ++ rest) = A.run C (q₀ :: rest) := by
      rw [List.append_assoc, Alg.exec_append]; rfl
    rw [e1, e2]
    refine ⟨?_, fun r hr => ?_⟩
    · rw [hA.1, hB.1, Cfg.step_of_access hp₀w]
      simp only [Function.update_idem, Function.update_self]
      congr 1
      set vals := (q₀ :: rest).map vv with hvals
      have hmap : ∀ s : List (W i), (q₀ :: rest).map (fun r => (WinOp.write (vv r) : WinOp (W i)))
          = vals.map WinOp.write := fun _ => by simp [hvals]
      rw [hmap (C.mem i)]
      have hlen : w i ≤ vals.length := by
        rw [hvals, List.length_map, hothers_len]; omega
      obtain ⟨u, us, hu⟩ : ∃ u us, vals = u :: us := ⟨vv q₀, rest.map vv, by simp [hvals]⟩
      show (windowObj (W i) (w i)).runOps (C.mem i) ((vv p₀ :: vals).map WinOp.write) = _
      have key : ∀ t : List (W i), (t ++ vals).drop ((t ++ vals).length - w i) =
          vals.drop (vals.length - w i) := fun t => List.drop_length_sub_append_eq t hlen
      rw [hu, windowObj_runOps_writes, windowObj_runOps_writes,
        show C.mem i ++ vv p₀ :: u :: us = (C.mem i ++ [vv p₀]) ++ vals by simp [hu],
        show C.mem i ++ u :: us = C.mem i ++ vals by simp [hu], key, key]
    · simp only [Set.mem_singleton_iff] at hr
      subst hr
      rw [hA.2, hB.2]
      simp
  have hβ : ∀ r ∈ q₀ :: rest, r ∈ below n := fun r hr => (hothers_mem r hr).1
  have hγ : ∀ r ∈ rest, r ∈ below n := fun r hr => hβ r (List.mem_cons_of_mem _ hr)
  exact false_of_agreeOn hwf hp₀t hq₀f hβ hγ hq₀ hagree

end Lemma9

/-! ### Proposition 5 -/

/-- A stage of the construction of Proposition 5: an `n`-critical execution. -/
structure Stage (A : Alg (WT W w) ℕ Bool Bool) (x : ℕ → Bool) where
  /-- The execution. -/
  α : List ℕ
  /-- The number of processes. -/
  n : ℕ
  pos : 0 < n
  crit : Crit A (below n) x α

/-- **Proposition 5** (`MA₃[WReg]` is not universal). No algorithm using (any number of) window
registers of (any) sizes solves binary consensus — agreement, weak validity and wait-freedom —
in the infinite arrival model with infinite memory allocation. -/
theorem window_not_consensus (hag : Agreement A anySched) (hval : WeakValidity A anySched)
    (hwf : WaitFree A infArrival) : False := by
  classical
  have hag' : Agreement A (fun _ => True) := hag
  have hwf' : WaitFree A (fun s => (Set.range s).Finite) := fun x s _ => hwf x s trivial
  -- inputs: `p₀` proposes `false`, every other process `true`
  let x : ℕ → Bool := fun p => decide (p ≠ 0)
  -- a solo run of `p` decides its input
  have hsolo : ∀ p < 2, CanDec A (below 2) x [] (x p) := by
    intro p hp
    obtain ⟨m, v, hout⟩ := exists_solo_out hwf' x [] p
    let x' : ℕ → Bool := fun _ => x p
    have hag0 : AgreeOn {p} (A.initCfg x) (A.initCfg x') :=
      Alg.initCfg_agreeOn (fun q hq => by simp at hq; subst hq; rfl)
    have hrep : ∀ s ∈ List.replicate (m + 1) p, s ∈ ({p} : Set ℕ) := fun s hs => by
      rw [List.eq_of_mem_replicate hs]; rfl
    have h2 := Alg.run_agreeOn hag0 hrep
    have hout' : (A.exec x' ([] ++ List.replicate (m + 1) p)).Out p v :=
      (h2.out_iff (by rfl) v).1 hout
    have hv : v = x p := hval (x p) x' _ trivial (fun _ => rfl) p (by simp) v hout'
    subst hv
    exact ⟨List.replicate (m + 1) p, fun s hs => by rw [List.eq_of_mem_replicate hs]; exact hp,
      p, by simp, hout⟩
  have hb0 := hsolo 0 (by omega)
  have hb1 := hsolo 1 (by omega)
  have hbiv0 : Biv A (below 2) x [] := ⟨by simpa [x] using hb0, by simpa [x] using hb1⟩
  obtain ⟨β₀, -, hc₀⟩ := exists_crit hwf' hag' (Set.finite_lt_nat 2) hbiv0
  -- one stage of the construction: `p₀` takes a step in the extension
  have hnext : ∀ S : Stage A x, ∃ S' : Stage A x, ∃ β, S'.α = S.α ++ β ∧ 0 ∈ β := by
    intro S
    obtain ⟨i, hni, hall⟩ := crit_write_same hag' hwf' S.crit
    have hbiv : Biv A (below (w i + 1)) x S.α := S.crit.1.mono (below_mono (by omega))
    obtain ⟨β, -, hc⟩ := exists_crit hwf' hag' (Set.finite_lt_nat _) hbiv
    obtain ⟨i', hni', hall'⟩ := crit_write_same hag' hwf' hc
    refine ⟨⟨S.α ++ β, w i + 1, by omega, hc⟩, β, rfl, ?_⟩
    by_contra h0
    obtain ⟨v, k, h1⟩ := hall 0 S.pos
    obtain ⟨v', k', h2⟩ := hall' 0 (by omega)
    rw [Alg.exec_append, Alg.run_loc_other _ _ h0] at h2
    have := access_inj (h1.symm.trans h2)
    subst this
    omega
  choose nxt β hβ h0 using hnext
  let S0 : Stage A x := ⟨[] ++ β₀, 2, by omega, hc₀⟩
  let st : ℕ → Stage A x := fun k => nxt^[k] S0
  have hsucc : ∀ k, (st (k + 1)).α = (st k).α ++ β (st k) := fun k => by
    simp only [st, Function.iterate_succ_apply']; exact hβ _
  have hlen : ∀ k, k ≤ (st k).α.length := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      rw [hsucc, List.length_append]
      have : β (st k) ≠ [] := List.ne_nil_of_mem (h0 (st k))
      have := List.length_pos_of_ne_nil this
      omega
  obtain ⟨s, hs⟩ := exists_seq_of_chain (fun k => (st k).α)
    (fun k => by simp only [hsucc]; exact List.prefix_append _ _) hlen
  have hinf : InfOften s 0 := by
    intro N
    have h1 := hs (N + 1)
    simp only [hsucc, List.length_append, pre_add] at h1
    rw [hs N] at h1
    have h2 := List.append_cancel_left h1
    have h3 : 0 ∈ pre (fun t => s ((st N).α.length + t)) (β (st N)).length := by
      rw [h2]; exact h0 (st N)
    obtain ⟨u, -, hsu⟩ := mem_pre.1 h3
    exact ⟨_ + u, by have := hlen N; omega, hsu⟩
  obtain ⟨t, v, hout⟩ := hwf x s trivial 0 hinf
  apply (st t).crit.1.not_out hag' (Or.inr (st t).pos) v
  obtain ⟨τ, hτ⟩ := pre_prefix s (hlen t)
  rw [hs t] at hτ
  rw [← hτ, Alg.exec_append]
  exact Alg.Cfg.Out.run hout τ

end Podc.InfiniteArrivalHierarchy
