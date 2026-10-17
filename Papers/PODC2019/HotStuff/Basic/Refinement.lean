import Papers.PODC2019.HotStuff.Basic.Handlers
import Cslib.Computability.Distributed.Byzantine.PartialSync.Log

/-!
# Basic HotStuff implementation refines the abstract system

For every run of the partially synchronous model whose Byzantine replicas respect
unforgeability (`Run.AuthValid`), the abstraction of the global state at any time `τ` (local
states of correct replicas, votes cast by correct replicas) is reachable in the abstract system
of `Defs.lean`. Hence the abstract safety theorem applies to the implementation.

* `tok_origin`: a partial signature of a correct replica on `q` that appears anywhere (in a
  message of a correct replica, or relayed by a Byzantine one) was cast by that replica: `q` is
  among its votes. This is where unforgeability of (threshold) signatures is used.
* `abs_reach`: the refinement.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {leader : ℕ → P}
variable (R : Run P (Msg P C) (Inp C))

/-! ### Local facts along a run -/

theorem st_succ_eq (τ : ℕ) (p : P) :
    R.st (hotstuff f leader) (τ + 1) p = stepR f leader p (R.st (hotstuff f leader) τ p)
      (R.inbox (hotstuff f leader) p τ) :=
  R.st_succ _ τ p

/-- The step from `τ` to `τ + 1`, after receiving, as a handler step. -/
theorem hstep_at (F : Finset P) (V : Set (P × QC C)) (τ : ℕ) (p : P) :
    HStep f F V p (recv (R.st (hotstuff f leader) τ p) (R.inbox (hotstuff f leader) p τ))
      (R.st (hotstuff f leader) (τ + 1) p) := by
  rw [st_succ_eq]; exact hstep_stepR V p _ _

/-- The replica buffers are message logs: every step appends the received messages. -/
theorem hotstuff_logs :
    (hotstuff f leader : Algorithm P (Msg P C) (RState P C) (Inp C) Unit).Logs RState.buf where
  log_init _ _ := rfl
  log_step p s ib := ⟨received ib, (hstep_stepR (F := ∅) ∅ p s ib).buf, fun _ _ => mem_received⟩

theorem st_buf (τ : ℕ) (p q : P) (m : Msg P C) :
    (q, m) ∈ (R.st (hotstuff f leader) τ p).buf ↔
      ∃ ρ < τ, m ∈ R.inbox (hotstuff f leader) p ρ q :=
  hotstuff_logs.mem_log_iff R τ p q m

theorem st_clock (τ : ℕ) (p : P) : (R.st (hotstuff f leader) τ p).clock = τ := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [(hstep_at R ∅ ∅ τ p).clock]; simp [recv, ih]

theorem st_inp (τ : ℕ) (p : P) : (R.st (hotstuff f leader) τ p).inp = R.inp p := by
  induction τ with
  | zero => rfl
  | succ τ ih => rw [(hstep_at R ∅ ∅ τ p).inp]; simp [recv, ih]

theorem votes_mono {σ τ : ℕ} (h : σ ≤ τ) (p : P) :
    (R.st (hotstuff f leader) σ p).votes ⊆ (R.st (hotstuff f leader) τ p).votes := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            exact le_rfl
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · exact (ih (by omega)).trans (hstep_at R ∅ ∅ τ p).votes
    · obtain rfl : σ = τ + 1 := by omega
      exact le_rfl

theorem view_mono {σ τ : ℕ} (h : σ ≤ τ) (p : P) :
    (R.st (hotstuff f leader) σ p).view ≤ (R.st (hotstuff f leader) τ p).view := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            exact le_rfl
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · exact (ih (by omega)).trans (hstep_at R ∅ ∅ τ p).view
    · obtain rfl : σ = τ + 1 := by omega
      exact le_rfl

theorem committed_mono {σ τ : ℕ} (h : σ ≤ τ) (p : P) :
    (R.st (hotstuff f leader) σ p).committed ⊆ (R.st (hotstuff f leader) τ p).committed := by
  induction τ with
  | zero => obtain rfl : σ = 0 := by omega
            exact le_rfl
  | succ τ ih =>
    rcases Nat.lt_or_ge σ (τ + 1) with h' | h'
    · exact (ih (by omega)).trans (hstep_at R ∅ ∅ τ p).committed
    · obtain rfl : σ = τ + 1 := by omega
      exact le_rfl

theorem st_tokOK (τ : ℕ) (p : P) : TokOK p (R.st (hotstuff f leader) τ p) := by
  induction τ with
  | zero =>
    refine ⟨fun q m hm k hk => ?_, by simp [hotstuff, RState.init], by simp [hotstuff, RState.init]⟩
    simp only [hotstuff, RState.init] at hm
    rw [mem_to1 hm] at hk
    simp [Msg.toks] at hk
  | succ τ ih => exact (hstep_at R ∅ ∅ τ p).tok (ih.recv p _)

/-- The implementation is unforging: it only sends its own tokens and tokens it has received. -/
theorem hotstuff_unforging : (hotstuff (C := C) f leader).Unforging auth := by
  intro R p τ q m hm k hk
  rcases (st_tokOK R τ p).out q m hm k hk with h | ⟨⟨q', m'⟩, hqm, hk'⟩
  · exact Or.inl h.1
  · obtain ⟨ρ, hρ, hin⟩ := (st_buf R τ p q' m').mp hqm
    exact Or.inr ⟨ρ, hρ, q', m', hin, hk'⟩

/-! ### Origin of signature tokens -/

variable {R}

/-- **Unforgeability.** A token `(i, q)` of a correct replica `i` occurring in a message sent by
a correct replica at time `σ` was cast by `i` as a vote by time `σ`. -/
theorem tok_origin (hA : R.AuthValid auth (hotstuff f leader)) :
    ∀ σ, ∀ c ∉ R.faulty, ∀ r, ∀ m ∈ R.out (hotstuff f leader) c σ r, ∀ k ∈ m.toks,
      k.1 ∉ R.faulty → k.2 ∈ (R.st (hotstuff f leader) σ k.1).votes := by
  intro σ
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
    intro c hc r m hm k hk hk1
    rw [Run.out_of_correct _ _ hc] at hm
    rcases (st_tokOK R σ c).out r m hm k hk with h | ⟨⟨q', m'⟩, hqm, hk'⟩
    · rw [h.1]; exact h.2
    · obtain ⟨ρ, hρ, hin⟩ := (st_buf R σ c q' m').mp hqm
      obtain ⟨σ', hσ', -, hm'⟩ := Run.mem_inbox.mp hin
      by_cases hq' : q' ∈ R.faulty
      · rw [Run.out_of_faulty _ _ hq'] at hm'
        rcases hA q' hq' σ' c hc m' hm' k hk' with h | ⟨σ'', hσ'', c'', hc'', r'', m'', hm'', hk''⟩
        · exact absurd h hk1
        · exact votes_mono R (by omega) _ (ih σ'' (by omega) c'' hc'' r'' m'' hm'' k hk'' hk1)
      · exact votes_mono R (by omega) _ (ih σ' (by omega) q' hq' c m' hm' k hk' hk1)

/-- Votes cast by correct replicas up to time `τ` (the abstract `votes`). -/
def Vab (R : Run P (Msg P C) (Inp C)) (f : ℕ) (leader : ℕ → P) (τ : ℕ) : Set (P × QC C) :=
  {x | x.1 ∉ R.faulty ∧ x.2 ∈ (R.st (hotstuff f leader) τ x.1).votes}

theorem Vab_mono {σ τ : ℕ} (h : σ ≤ τ) : Vab R f leader σ ⊆ Vab R f leader τ :=
  fun x hx => ⟨hx.1, votes_mono R h _ hx.2⟩

/-- A locally valid QC in a message received by a correct replica by time `τ` is valid in the
abstract sense at time `τ`. -/
theorem valid_of_received (hA : R.AuthValid auth (hotstuff f leader)) {p : P}
    (hp : p ∉ R.faulty) {τ ρ : ℕ} (hρ : ρ ≤ τ) {q : P} {m : Msg P C}
    (hm : m ∈ R.inbox (hotstuff f leader) p ρ q) {j : QCm P C} (hj : j ∈ m.qcs)
    (hok : j.ok f) : Valid f R.faulty (Vab R f leader τ) j.qc := by
  rcases hok with h | h
  · exact Or.inl h
  refine Or.inr (h.trans (Finset.card_le_card fun i hi => ?_))
  rw [mem_signers]
  by_cases hiF : i ∈ R.faulty
  · exact Or.inl hiF
  right
  have hk : (i, j.qc) ∈ m.toks := Msg.toks_of_qcs hj ⟨hi, rfl⟩
  refine ⟨hiF, ?_⟩
  obtain ⟨σ', hσ', -, hm'⟩ := Run.mem_inbox.mp hm
  by_cases hq : q ∈ R.faulty
  · rw [Run.out_of_faulty _ _ hq] at hm'
    rcases hA q hq σ' p hp m hm' _ hk with h | ⟨σ'', hσ'', c'', hc'', r'', m'', hm'', hk''⟩
    · exact absurd h hiF
    · exact votes_mono R (by omega) _ (tok_origin hA σ'' c'' hc'' r'' m'' hm'' _ hk'' hiF)
  · exact votes_mono R (by omega) _ (tok_origin hA σ' q hq p m hm' _ hk hiF)

/-- The buffer of a correct replica after receiving at time `τ` is valid w.r.t. `Vab τ`. -/
theorem bufValid_at (hA : R.AuthValid auth (hotstuff f leader)) {p : P} (hp : p ∉ R.faulty)
    (τ : ℕ) : BufValid f R.faulty (Vab R f leader τ)
      (recv (R.st (hotstuff f leader) τ p) (R.inbox (hotstuff f leader) p τ)) := by
  intro q m hqm j hj hok
  simp only [recv, List.mem_append, mem_received] at hqm
  rcases hqm with hqm | hqm
  · obtain ⟨ρ, hρ, hin⟩ := (st_buf R τ p q m).mp hqm
    exact valid_of_received hA hp (by omega) hin hj hok
  · exact valid_of_received hA hp le_rfl hqm hj hok

/-! ### The refinement -/

theorem LStep.mono' {F : Finset P} {V V' : Set (P × QC C)} (h : V ⊆ V') {l l' : Loc C}
    {o : Option (QC C)} (hs : LStep f F V l l' o) : LStep f F V' l l' o := by
  cases hs with
  | prepVote x j h0 hj hx hs => exact .prepVote _ x j h0 (hj.mono h) hx hs
  | prepSkip h0 => exact .prepSkip _ h0
  | precommitVote q h1 hq ht hv => exact .precommitVote _ q h1 (hq.mono h) ht hv
  | commitVote q h2 hq ht hv => exact .commitVote _ q h2 (hq.mono h) ht hv
  | decide q h3 hq ht hv => exact .decide _ q h3 (hq.mono h) ht hv
  | newView v hv => exact .newView _ v hv

/-- The votes of replica `r` as a set of pairs. -/
def pairs (r : P) (m : Set (QC C)) : Set (P × QC C) := {x | x.1 = r ∧ x.2 ∈ m}

theorem lift_LR {F : Finset P} {V : Set (P × QC C)} {r : P} (hr : r ∉ F) (L : P → Loc C)
    (W : Set (P × QC C)) {a a' : Loc C × Set (QC C)}
    (h : LR f F V a a') (hV : V ⊆ W ∪ pairs r a.2) :
    Relation.ReflTransGen (Step f F) ⟨Function.update L r a.1, W ∪ pairs r a.2⟩
      ⟨Function.update L r a'.1, W ∪ pairs r a'.2⟩ ∧ a.2 ⊆ a'.2 := by
  induction h with
  | refl => exact ⟨Relation.ReflTransGen.refl, le_rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨ih, hm⟩ := ih
    obtain ⟨o, hst, hc⟩ := hbc
    refine ⟨ih.tail ?_, hm.trans (by rw [hc]; exact Set.subset_union_left)⟩
    have hV' : V ⊆ W ∪ pairs r b.2 := hV.trans (Set.union_subset_union_right _
      (fun x hx => ⟨hx.1, hm hx.2⟩))
    have := Step.mk (f := f) (F := F) ⟨Function.update L r b.1, W ∪ pairs r b.2⟩ r c.1 o hr
      (by simpa using hst.mono' hV')
    convert this using 2
    · simp
    · rw [hc]; ext ⟨x1, x2⟩
      simp only [pairs, Set.mem_union, Set.mem_ofPred_eq, mem_newVotes]
      tauto

/-- The abstraction of the global state at time `τ`. -/
noncomputable def absSt (R : Run P (Msg P C) (Inp C)) (f : ℕ) (leader : ℕ → P) (τ : ℕ) : St P C :=
  ⟨fun r => if r ∈ R.faulty then Loc.init else (R.st (hotstuff f leader) τ r).toLoc,
    Vab R f leader τ⟩

/-- Intermediate abstract state: replicas in `S` have taken their step `τ → τ + 1`. -/
noncomputable def mixSt (R : Run P (Msg P C) (Inp C)) (f : ℕ) (leader : ℕ → P) (τ : ℕ) (S : Finset P) :
    St P C :=
  ⟨fun r => if r ∈ R.faulty then Loc.init else
      (R.st (hotstuff f leader) (if r ∈ S then τ + 1 else τ) r).toLoc,
    {x | x.1 ∉ R.faulty ∧ x.2 ∈ (R.st (hotstuff f leader) (if x.1 ∈ S then τ + 1 else τ) x.1).votes}⟩

theorem mix_step (hA : R.AuthValid auth (hotstuff f leader)) (τ : ℕ) :
    ∀ S : Finset P, (∀ r ∈ S, r ∉ R.faulty) →
      Relation.ReflTransGen (Step f R.faulty) (mixSt R f leader τ ∅) (mixSt R f leader τ S) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _; exact Relation.ReflTransGen.refl
  | @insert r S hrS ih =>
    intro hS
    have hr : r ∉ R.faulty := hS r (Finset.mem_insert_self _ _)
    refine (ih fun x hx => hS x (Finset.mem_insert_of_mem hx)).trans ?_
    set L : P → Loc C := (mixSt R f leader τ S).loc
    set W : Set (P × QC C) := {x | x.1 ≠ r ∧ x ∈ (mixSt R f leader τ S).votes}
    have hst := hstep_at (f := f) (leader := leader) R R.faulty (Vab R f leader τ) τ r
    have hlr := hst.lr (bufValid_at hA hr τ)
    simp only [recv_toLoc] at hlr
    have key := (lift_LR hr L W hlr ?_).1
    · convert key using 2
      · funext x
        by_cases hx : x = r
        · subst hx; simp [mixSt, L, hrS, hr, recv]
        · simp [mixSt, L, hx]
      · ext x
        by_cases hx : x.1 = r
        · simp [mixSt, W, pairs, hx, hrS, hr, recv]
        · simp [mixSt, W, pairs, hx]
      · funext x
        by_cases hx : x = r
        · subst hx; simp [mixSt, L, hr]
        · simp [mixSt, L, hx]
      · ext x
        by_cases hx : x.1 = r
        · simp [mixSt, W, pairs, hx, hr]
        · simp [mixSt, W, pairs, hx]
    · intro x hx
      by_cases hxr : x.1 = r
      · right; exact ⟨hxr, by simpa [recv, hxr] using hx.2⟩
      · left
        refine ⟨hxr, hx.1, ?_⟩
        split_ifs
        · exact votes_mono R (Nat.le_succ τ) _ hx.2
        · exact hx.2

/-- **Refinement.** In every run whose adversary respects unforgeability, the abstraction of the
state at any time is reachable in the abstract system. -/
theorem abs_reach (hA : R.AuthValid auth (hotstuff f leader)) (τ : ℕ) :
    Reach f R.faulty (absSt R f leader τ) := by
  induction τ with
  | zero =>
    have : absSt R f leader 0 = St.init := by
      simp only [absSt, St.init, Vab]
      congr 1
      · funext r; split_ifs <;> rfl
      · ext x; simp [hotstuff, RState.init]
    rw [this]; exact Relation.ReflTransGen.refl
  | succ τ ih =>
    have h0 : mixSt R f leader τ ∅ = absSt R f leader τ := by
      simp [mixSt, absSt, Vab]
    have h1 : mixSt R f leader τ (Finset.univ.filter (· ∉ R.faulty)) = absSt R f leader (τ + 1) := by
      simp only [mixSt, absSt, Vab]
      congr 1
      · funext r; by_cases hr : r ∈ R.faulty <;> simp [hr]
      · ext x; by_cases hr : x.1 ∈ R.faulty <;> simp [hr]
    have := mix_step hA τ (Finset.univ.filter (· ∉ R.faulty)) (by simp)
    rw [h0, h1] at this
    exact ih.trans this

end HotStuff.Basic
