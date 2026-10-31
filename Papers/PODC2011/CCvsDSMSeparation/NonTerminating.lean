import Papers.PODC2011.CCvsDSMSeparation.Trace

/-!
# Termination cannot be dropped (Corollary 6.14 as stated)

Corollary 6.14 is stated for "any deterministic algorithm" that solves the signaling problem
(the word *terminating* of Theorem 6.2 is missing in the statement, although its proof assumes
it). Without termination the claim is false: in `spinAlg`, `Poll()` spins forever on a variable
in the caller's own module and `Signal()` returns at once. Specification 4.1 only constrains
calls that *return*, so `spinAlg` solves the signaling problem, yet no execution has a single
RMR in the DSM model (`spinAlg_solves`, `spinAlg_rmr`). The algorithm uses only reads, hence it
is also an algorithm "using atomic reads and writes, and either CAS or LL/SC".
-/

namespace Podc.CCvsDSMSeparation

/-- Local states of `spinAlg`. -/
inductive SpinLoc
  | idle
  | spin
  | sigDone

/-- `Poll()` busy-waits forever on the caller's own variable; `Signal()` returns immediately. -/
def spinAlg (N : ℕ) : Algorithm N (Fin N) Unit SpinLoc where
  home := id
  memInit := fun _ => ()
  locInit := fun _ => .idle
  invoke := fun _ _ o => match o with
    | .poll => .spin
    | .signal => .sigDone
  act := fun p s => match s with
    | .spin => .read p fun _ => .spin
    | .sigDone => .ret false .idle
    | .idle => .ret false .idle

variable {N : ℕ}

/-- The reachable local states of `spinAlg`. -/
def SpinGood : LState SpinLoc → Prop
  | (.idle, none) => True
  | (.spin, some .poll) => True
  | (.sigDone, some .signal) => True
  | _ => False

lemma spin_lstep {p : Fin N} {c c' : LState SpinLoc} {op : Op (Fin N) Unit} (hg : SpinGood c)
    (h : (spinAlg N).lstep p c op = some c') : SpinGood c' := by
  rcases c with ⟨_ | _ | _, _ | o⟩ <;> simp only [SpinGood] at hg <;> (try cases o) <;>
    cases op <;> simp [Algorithm.lstep, spinAlg] at h <;>
    (try (obtain ⟨-, rfl⟩ := h)) <;> simp_all [SpinGood]
  all_goals (rename_i o; cases o <;> trivial)

lemma spin_good {τ : List (Ev N (Fin N) Unit)} (hv : (spinAlg N).Valid τ) (p : Fin N) :
    ∃ c, (spinAlg N).state τ p = some c ∧ SpinGood c := by
  induction τ using List.reverseRecOn with
  | nil => exact ⟨_, rfl, trivial⟩
  | append_singleton τ e ih =>
    rw [Algorithm.valid_snoc] at hv
    by_cases hp : e.p = p
    · subst hp
      obtain ⟨c, hc, hg⟩ := ih hv.1
      have h1 := hv.2.1
      rw [(spinAlg N).lrun_snoc] at h1
      change (((spinAlg N).state τ e.p).bind fun c => (spinAlg N).lstep e.p c e.op).isSome at h1
      rw [hc, Option.bind_some, Option.isSome_iff_exists] at h1
      obtain ⟨c', hc'⟩ := h1
      refine ⟨c', ?_, spin_lstep hg hc'⟩
      rw [(spinAlg N).state_snoc_self, hc, Option.bind_some, hc']
    · rw [(spinAlg N).state_snoc_ne _ _ hp]; exact ih hv.1

/-- `spinAlg` solves the signaling problem (vacuously: no call to `Poll()` ever returns). -/
theorem spinAlg_solves : (spinAlg N).Solves := by
  intro τ p b hv _ hbusy
  exfalso
  obtain ⟨s, hs⟩ := hbusy
  obtain ⟨c, hc, hg⟩ := spin_good (Algorithm.Valid.of_append _ hv) p
  rw [hs] at hc; cases hc
  have h1 := ((Algorithm.valid_snoc _ _ _).1 hv).2.1
  simp only at h1
  rw [(spinAlg N).lrun_snoc] at h1
  change (((spinAlg N).state τ p).bind fun c => (spinAlg N).lstep p c (.ret b)).isSome at h1
  rw [hs, Option.bind_some] at h1
  rcases s with _ | _ | _ <;> simp [SpinGood] at hg
  simp [Algorithm.lstep, spinAlg] at h1

/-- No execution of `spinAlg` has an RMR in the DSM model. -/
theorem spinAlg_rmr {τ : List (Ev N (Fin N) Unit)} (hv : (spinAlg N).Valid τ) :
    (spinAlg N).rmr τ = 0 := by
  rw [Algorithm.rmr_eq_zero_iff]
  intro e he
  obtain ⟨τ₁, τ₂, rfl⟩ := List.append_of_mem he
  have hv' : (spinAlg N).Valid (τ₁ ++ [e]) := Algorithm.Valid.of_prefix _ hv ⟨τ₂, by simp⟩
  have h1 := ((Algorithm.valid_snoc _ _ _).1 hv').2.1
  rw [(spinAlg N).lrun_snoc] at h1
  change (((spinAlg N).state τ₁ e.p).bind fun c => (spinAlg N).lstep e.p c e.op).isSome at h1
  rcases e with ⟨p, op⟩
  rcases hc : (spinAlg N).state τ₁ p with _ | ⟨s, _ | o⟩ <;> simp only [hc] at h1
  · simp at h1
  · cases op <;> simp [Algorithm.lstep] at h1
    rfl
  · cases op <;> try rfl
    · rcases s with _ | _ | _ <;> simp [Algorithm.lstep, spinAlg] at h1
      simp only [Ev.remote, Op.remoteFor, Op.var, spinAlg, id]
      rw [← h1]; simp
    · rcases s with _ | _ | _ <;> simp [Algorithm.lstep, spinAlg] at h1

/-- **Corollary 6.14 (and Theorem 6.2) need termination.** There is a deterministic read-only
algorithm solving the signaling problem in which no execution has an RMR in the DSM model; in
particular, for every `c`, every execution with `k` participants incurs at most `c·k` RMRs. -/
theorem corollary_6_14_needs_terminating (N : ℕ) :
    ∃ A : Algorithm N (Fin N) Unit SpinLoc, A.Solves ∧
      ∀ c τ, A.Valid τ → A.rmr τ ≤ c * (par τ).card :=
  ⟨spinAlg N, spinAlg_solves, fun c τ hv => by rw [spinAlg_rmr hv]; exact Nat.zero_le _⟩

end Podc.CCvsDSMSeparation
