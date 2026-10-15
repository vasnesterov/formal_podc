import Papers.PODC2026.CanonicalRoundByzantine.Main

/-!
# Corollary 10 of [AFW26] (reliable / consistent broadcast), directly and for every `n > f ≥ 1`

The paper derives Corollary 10 ("for `n ≤ 5f` any canonical-round algorithm for reliable or
consistent broadcast has an execution in which some correct process does not terminate by round `K`,
and such an algorithm is not communication-closed") from Theorem 1 via Algorithm 3 (crusader
agreement from `n` parallel consistent broadcasts). Algorithm 3 is only correct for `n > 4f`
(Theorem 9), so this proof covers only `4f < n ≤ 5f`.

The statement is nevertheless true, for **every** `n > f ≥ 1`, by a direct argument already hinted at
in the introduction of the paper: in canonical rounds the adversary can let every process hear
`n - f` processes other than the (correct) sender in each of the first `K` rounds. Then no other
process has any information about the sender's input by round `K`, but validity forces it to accept
that input. We formalize this with only the *validity* property of broadcast for a correct sender
(`bcastSpec`), which both reliable and consistent broadcast satisfy, and without any Byzantine
process.
-/

namespace Podc2026.CanonicalRound

open Cslib.Byzantine.CanonicalRounds Finset

variable {n : ℕ} {V R M : Type*}

/-- Broadcast from the designated sender `s` (input `I s`; the inputs of other processes are
ignored), validity for a correct sender: a correct process only accepts the sender's input. This
is implied by the validity property of reliable broadcast [Bracha] and of consistent broadcast. -/
def bcastSpec (s : Fin n) : Spec n V V := fun I F d =>
  s ∉ F → ∀ p ∉ F, ∀ o, d p = some o → o = I s

section

variable (alg : CanonAlg n V R M V) {f : ℕ}

/-- In a clean schedule without Byzantine processes in which nobody hears `s`, the histories of the
processes other than `s` do not depend on the input of `s`. -/
theorem clean_indep {s : Fin n} {H : Finset (Fin n)} (hs : s ∉ H) {I I' : Fin n → V}
    (hI : ∀ p, p ≠ s → I p = I' p) (byz : ℕ → Fin n → Fin n → M) (ρ : Tape n R) (r : ℕ) :
    ∀ p, p ≠ s → clean alg I ∅ (fun _ => H) byz ρ r p = clean alg I' ∅ (fun _ => H) byz ρ r p := by
  induction r with
  | zero => intro p _; rfl
  | succ r ih =>
    intro p hp
    rw [clean_succ, clean_succ, ih p hp]
    congr 2
    apply List.map_congr_left
    intro q hq
    have hqs : q ≠ s := fun h => hs (h ▸ (mem_hearList.1 hq))
    simp only [cmsg, Finset.notMem_empty, if_false, hI q hqs, ih q hqs]

theorem exists_hear (s : Fin n) (hf : 1 ≤ f) (hfn : f < n) :
    ∃ H : Finset (Fin n), H.card = n - f ∧ s ∉ H := by
  obtain ⟨H, hH, hc⟩ := Finset.exists_subset_card_eq (s := univ.erase s) (n := n - f)
    (by rw [card_erase_of_mem (mem_univ s), card_univ, Fintype.card_fin]; omega)
  exact ⟨H, hc, fun h => by simpa using hH h⟩

/-- The key step: with a schedule in which nobody hears the sender, a process `p ≠ s` that has
decided at the end of stage `K` contradicts validity in one of two executions differing only in
the sender's input. -/
theorem bcast_contra {vw : Log n R M → Log n R M} (s : Fin n) (hsafe : alg.Safe f (bcastSpec s))
    (hf : f < n) {H : Finset (Fin n)} (hH : H.card = n - f) (hs : s ∉ H) {lateFrom : ℕ}
    (hl : 1 ≤ lateFrom) (hv : ViewOK alg vw)
    (hdec : ∀ p v l, alg.decision p v l = alg.decision p v (vw l)) (K : ℕ)
    (hdrop : lateFrom ≤ K → ∀ l q r' m, r' < rnd l → vw (l ++ [.recv q r' m]) = vw l)
    {v v' : V} (hvv : v ≠ v') (ρ : Tape n R) {p : Fin n} (hp : p ≠ s) :
    let I : Fin n → V := fun _ => v
    let A : Adversary n R M := schedule ∅ (fun _ => H) (fun _ _ q _ => alg.msg q v []) lateFrom
    (alg.decision p v ((alg.exec f I ρ A ((K + 1) * stageLen n)).log p)).isSome → False := by
  intro I A hdecp
  let I' : Fin n → V := Function.update (fun _ => v) s v'
  have hI : ∀ q, q ≠ s → I q = I' q := fun q hq => by simp [I, I', hq]
  have hadm : ∀ J : Fin n → V, alg.Admissible f J A := fun J =>
    schedule_admissible alg f J ∅ (fun _ => H) _ lateFrom hf hl (by simp) (fun _ _ => hH)
      (fun _ _ q _ => alg.msg q v []) (fun _ _ _ _ _ _ hq => absurd hq (Finset.notMem_empty _))
  have hbm : ∀ ρ : Tape n R, BmOK (∅ : Finset (Fin n)) (fun _ => H) (fun _ q _ => alg.msg q v []) ρ
      (fun _ _ q _ => alg.msg q v []) := fun _ _ _ _ _ _ hq => absurd hq (Finset.notMem_empty _)
  have inv := fun J => stageInv_exec alg f J ∅ (fun _ => H) (fun _ q _ => alg.msg q v []) ρ
    lateFrom (fun _ _ q _ => alg.msg q v []) hf hl hv (fun _ _ => hH) (hbm ρ) K hdrop K le_rfl
  have hlog : vw ((alg.exec f I ρ A ((K + 1) * stageLen n)).log p) =
      vw ((alg.exec f I' ρ A ((K + 1) * stageLen n)).log p) := by
    rw [(inv I).view p (by simp), (inv I').view p (by simp)]
    exact clean_indep alg hs hI _ ρ K p hp
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hdecp
  have h1 := hsafe I A (hadm I) ρ ((K + 1) * stageLen n) (by simp [A, schedule]) p
    (by simp [A, schedule]) o ho
  have ho' : alg.decision p (I' p) ((alg.exec f I' ρ A ((K + 1) * stageLen n)).log p) = some o := by
    rw [hdec, ← hlog, ← hdec, show I' p = v by simp [I', hp]]; exact ho
  have h2 := hsafe I' A (hadm I') ρ ((K + 1) * stageLen n) (by simp [A, schedule]) p
    (by simp [A, schedule]) o ho'
  simp only [I, I', Function.update_self] at h1 h2
  exact hvv (h1.symm.trans h2)

/-- **Corollary 10 of [AFW26]** (first part), for every `n > f ≥ 1`: any canonical-round algorithm
for reliable or consistent broadcast (only validity for a correct sender is used) has, for every
`K`, an admissible execution — with a correct sender and no Byzantine process — in which, for every
tape, some correct process does not terminate by round `K`. -/
theorem corollary10 (s : Fin n) (hf1 : 1 ≤ f) (hfn : f < n) (hsafe : alg.Safe f (bcastSpec s))
    {v v' : V} (hvv : v ≠ v') (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, ¬ alg.AllDecideBy f I ρ A K := by
  obtain ⟨H, hH, hs⟩ := exists_hear s hf1 hfn
  obtain ⟨p, hp⟩ : ∃ p : Fin n, p ≠ s := by
    by_cases h : s.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [← h'])⟩
  refine ⟨fun _ => v, schedule ∅ (fun _ => H) (fun _ _ q _ => alg.msg q v []) (K + 1),
    schedule_admissible alg f _ ∅ (fun _ => H) _ (K + 1) hfn (by omega) (by simp) (fun _ _ => hH)
      (fun _ _ q _ => alg.msg q v []) (fun _ _ _ _ _ _ hq => absurd hq (Finset.notMem_empty _)),
    fun ρ hall => ?_⟩
  have hdrop : K + 1 ≤ K → ∀ (l : Log n R M) q r' m, r' < rnd l → id (l ++ [.recv q r' m]) = id l :=
    fun h => absurd h (by omega)
  refine bcast_contra alg s hsafe hfn hH hs (by omega) (viewOK_id alg) (fun _ _ _ => rfl) K hdrop
    hvv ρ hp ?_
  obtain ⟨k, hk⟩ := hall p (by simp [schedule])
  have hle := fun k' (h : k' ≤ max k ((K + 1) * stageLen n)) =>
    (alg.le_exec f (fun _ => v) ρ (schedule ∅ (fun _ => H) (fun _ _ q _ => alg.msg q v []) (K + 1))
      h).log p
  have inv := stageInv_exec alg f (fun _ => v) ∅ (fun _ => H) (fun _ q _ => alg.msg q v []) ρ
    (K + 1) (fun _ _ q _ => alg.msg q v []) hfn (by omega) (viewOK_id alg) (fun _ _ => hH)
    (fun _ _ _ _ _ hq => absurd hq (Finset.notMem_empty _)) K hdrop K le_rfl
  exact Decisions.decision_isSome_of_decidesBy alg hk (hle k (le_max_left _ _))
    (hle _ (le_max_right _ _)) (by rw [inv.round p (by simp)])

/-- **Corollary 10 of [AFW26]** (second part), for every `n > f ≥ 1`: a communication-closed
canonical-round algorithm for reliable or consistent broadcast has an admissible execution (correct
sender, no Byzantine process) in which, for every tape, some correct process never terminates. -/
theorem corollary10_commClosed (s : Fin n) (hcc : alg.CommClosed) (hf1 : 1 ≤ f) (hfn : f < n)
    (hsafe : alg.Safe f (bcastSpec s)) {v v' : V} (hvv : v ≠ v') :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, ¬ alg.AllDecide f I ρ A := by
  obtain ⟨H, hH, hs⟩ := exists_hear s hf1 hfn
  obtain ⟨p, hp⟩ : ∃ p : Fin n, p ≠ s := by
    by_cases h : s.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by simp [Fin.ext_iff] at h'; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => h (by rw [← h'])⟩
  refine ⟨fun _ => v, schedule ∅ (fun _ => H) (fun _ _ q _ => alg.msg q v []) 1,
    schedule_admissible alg f _ ∅ (fun _ => H) _ 1 hfn le_rfl (by simp) (fun _ _ => hH)
      (fun _ _ q _ => alg.msg q v []) (fun _ _ _ _ _ _ hq => absurd hq (Finset.notMem_empty _)),
    fun ρ hall => ?_⟩
  obtain ⟨k, hk⟩ := hall p (by simp [schedule])
  have hS : 1 ≤ stageLen n := by unfold stageLen; nlinarith
  have hk' : k ≤ (k + 1) * stageLen n := le_trans (by omega) (Nat.le_mul_of_pos_right _ hS)
  refine bcast_contra alg s hsafe hfn hH hs le_rfl (viewOK_cc alg hcc)
    (Decisions.decision_ccView alg hcc) k (fun _ => ccView_drop) hvv ρ hp ?_
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 hk
  rw [Decisions.decision_mono alg ((alg.le_exec f (fun _ => v) ρ _ hk').log p) ho]; rfl

end

end Podc2026.CanonicalRound
