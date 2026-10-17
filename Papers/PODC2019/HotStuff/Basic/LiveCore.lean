import Papers.PODC2019.HotStuff.Basic.LiveRun

/-!
# Basic HotStuff: the core of the liveness argument (Lemma 3 and the voting rule)

A proposal of a *correct* leader passes the `safeNode` check of every correct replica, for the
lock the replica holds when it evaluates the proposal (in any view, at any time — no synchrony is
needed for this part). This is the content of Lemma 3 and of the first half of the proof of
Theorem 4.

Note the case distinction: if the leader's `highQC` has a *higher* view than the replica's lock,
the liveness rule (Line 27 of Algorithm 1) applies, as the paper says; if it has the *same* view,
the liveness rule fails (it is a strict inequality) and it is the safety rule (Line 26) that
applies, because two valid QCs of the same view are on the same node.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync Cslib.Quorum

variable {P C : Type*} [Fintype P] [DecidableEq P] {f : ℕ} {leader : ℕ → P}
variable {R : Run P (Msg P C) (Inp C)} {δ : ℕ}

theorem valid_of_buf (hA : R.AuthValid auth (hotstuff f leader)) {r : P} (hr : r ∉ R.faulty)
    {T : ℕ} {q : P} {m : Msg P C} (hm : (q, m) ∈ (R.st (hotstuff f leader) T r).buf)
    {c : QCm P C} (hc : c ∈ m.qcs) (hok : c.ok f) : Valid f R.faulty (Vab R f leader T) c.qc := by
  obtain ⟨ρ, hρ, hin⟩ := (st_buf R T r q m).mp hm
  exact valid_of_received hA hr hρ.le hin hc hok

/-- **Lemma 3 / core of Theorem 4.** -/
theorem safeNode_of_correct_leader (hR : R.Valid f δ)
    (hA : R.AuthValid auth (hotstuff f leader)) (h3 : 3 * f < Fintype.card P) {v T : ℕ}
    (hℓ : leader v ∉ R.faulty) {x : Node C} {j : QCm P C}
    (hx : (v, x, j) ∈ (R.st (hotstuff f leader) T (leader v)).props)
    {r : P} (hr : r ∉ R.faulty) {l : QC C} (hlv : l.view < v)
    (hl : l = QC.genesis ∨ ∃ c q, c.ok f ∧ c.qc = l ∧ l.ty = .precommit ∧
      (q, Msg.cert c) ∈ (R.st (hotstuff f leader) T r).buf) :
    SafeNode l x j.qc := by
  have hF := hR.card_faulty
  have h2 : 2 * f < Fintype.card P := by omega
  obtain ⟨-, -, hxe, -, ⟨S, hS, hS'⟩, hjsrc, -⟩ := (st_LI R T (leader v)).props_ok v x j hx
  have hsuf : j.qc.node <:+ x := by rw [hxe]; exact List.suffix_cons _ _
  rcases hl with rfl | ⟨c, q, hcok, hcl, hlty, hcbuf⟩
  · left; exact List.nil_suffix
  have hlvalid : Valid f R.faulty (Vab R f leader T) l := by
    rw [← hcl]; exact valid_of_buf hA hr hcbuf (by simp [Msg.qcs]) hcok
  have hI := (abs_reach hA T).inv
  rcases hlvalid.elim (fun h => Or.inl h) (fun h => Or.inr h) with hgen | hcard
  · left; rw [hgen.2]; exact List.nil_suffix
  obtain ⟨i, hiS, hisig, hiF⟩ := exists_mem_inter_notMem_of_three_mul_lt h3 hF hS hcard
  rw [mem_signers] at hisig
  have hvi : l ∈ (R.st (hotstuff f leader) T i).votes := (hisig.resolve_left hiF).2
  obtain ⟨j', -, hj'v, hj'buf⟩ := hS' i hiS
  have hsent := genuine' hiF hj'buf
  obtain ⟨-, -, hdom⟩ := (st_LI R T i).nv_sent _ _ _ hsent
  have hle : l.view ≤ j.qc.view := (hdom l hvi hlty (by omega)).trans hj'v
  rcases Nat.lt_or_ge l.view j.qc.view with hlt | hge
  · exact Or.inr hlt
  · left
    have heq : l.view = j.qc.view := le_antisymm hle hge
    rcases hjsrc with rfl | ⟨q', hq'⟩
    · have : l.node = [] := hI.node_of_view_zero hF h2 hlvalid (by rw [heq]; rfl)
      rw [this]; exact List.nil_suffix
    · have hjv : Valid f R.faulty (Vab R f leader T) j.qc :=
        valid_of_buf hA hℓ hq' (by simp [Msg.qcs]) ((st_LI R T (leader v)).props_ok v x j hx).2.2.2.1
      have := hI.node_eq hF h3 hlvalid hjv heq
      rw [this]; exact hsuf

end HotStuff.Basic
