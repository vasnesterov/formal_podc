import Papers.PODC2014.MultiMessageBroadcastMAC.Lemmas

/-!
# Theorem 3.4: BMMB solves the multi-message broadcast problem

The MMB specification of §3.2.2 (`Exec.SolvesMMB`), for executions with arbitrary (online)
`arrive` events: (a) every message that arrives at `i` is delivered at every node of `i`'s
component of `G`; (b) every node delivers every message at most once, and only after it arrived
somewhere. Only termination of broadcasts is needed (here: the acknowledgment bound).
-/

namespace Podc.MultiMessageBroadcastMAC

variable {V M : Type*}

namespace Exec

variable [DecidableEq V] {G G' : SimpleGraph V} (α : Exec G G' M)

/-- `deliver(m)_j` is performed at event `n`: event `n` adds `m` to `j`'s log. -/
def Delivers (n : ℕ) (j : V) (m : M) : Prop :=
  m ∉ (α.cfg n).log j ∧ m ∈ (α.cfg (n + 1)).log j

/-- The multi-message broadcast specification of §3.2.2. Part (a) asks for delivery at every node
of the source's connected component of `G`, as in the problem statement of §2 (`G` need not be
connected). -/
def SolvesMMB : Prop :=
  (∀ n i m, α.ev n = .arrive i m → ∀ j, G.Reachable i j → ∃ n', α.Delivers n' j m) ∧
  (∀ j m n n', α.Delivers n j m → α.Delivers n' j m → n = n') ∧
  (∀ n j m, α.Delivers n j m → ∃ n' ≤ n, ∃ i, α.ev n' = .arrive i m)

variable {α}

open Config

/-- Every pending broadcast is eventually acknowledged. -/
lemma exists_acks_gt {Fack : ℝ} (hA : α.AckBound Fack) {i : V} {n : ℕ} (h : (α.cfg n).Busy i) :
    ∃ n', (α.cfg n).acks i < (α.cfg n').acks i := by
  obtain ⟨s, -, hf, he⟩ := α.exists_fresh h
  obtain ⟨n', -, hlt⟩ := hA i s hf
  exact ⟨n', he ▸ hlt⟩

lemma exists_acks_ge {Fack : ℝ} (hA : α.AckBound Fack) (i : V) (n k : ℕ) :
    ∃ n' ≥ n, min ((α.cfg n).log i).length ((α.cfg n).acks i + k) ≤ (α.cfg n').acks i := by
  induction k with
  | zero => exact ⟨n, le_rfl, by simp⟩
  | succ k ih =>
    obtain ⟨n', hn', h⟩ := ih
    by_cases hb : (α.cfg n').Busy i
    · obtain ⟨n'', h''⟩ := exists_acks_gt hA hb
      rcases le_total n' n'' with hle | hle
      · exact ⟨n'', hn'.trans hle, by omega⟩
      · have := (α.mono hle).acks_le i
        omega
    · refine ⟨n', hn', ?_⟩
      have := ((α.mono hn').log_prefix i).length_le
      unfold Busy at hb
      omega

/-- Every message a node got is eventually acknowledged by it. -/
lemma exists_acked {Fack : ℝ} (hA : α.AckBound Fack) {i : V} {n : ℕ} {m : M}
    (hm : m ∈ (α.cfg n).log i) : ∃ n', (α.cfg n').Acked i m := by
  obtain ⟨n', hn', h⟩ := exists_acks_ge hA i n ((α.cfg n).log i).length
  refine ⟨n', ?_⟩
  have hpre := (α.mono hn').log_prefix i
  obtain ⟨p, hp, rfl⟩ := List.getElem_of_mem hm
  unfold Acked
  rw [hpre.getElem hp]
  have hidx : p < (((α.cfg n').log i).take ((α.cfg n').acks i)).length := by
    rw [List.length_take]; have := hpre.length_le; omega
  have := List.getElem_mem hidx
  rwa [List.getElem_take] at this

/-- Every message a node got eventually reaches its `G`-neighbours. -/
lemma exists_mem_log_of_adj {Fack : ℝ} (hA : α.AckBound Fack) {i j : V} (hij : G.Adj i j)
    {n : ℕ} {m : M} (hm : m ∈ (α.cfg n).log i) : ∃ n', m ∈ (α.cfg n').log j := by
  obtain ⟨n', h⟩ := exists_acked hA hm
  exact ⟨n', (α.inv n').acked_nbr i j hij m h⟩

/-- Every message a node got eventually reaches its whole component of `G`. -/
lemma exists_mem_log_of_reachable {Fack : ℝ} (hA : α.AckBound Fack) {i j : V}
    (hij : G.Reachable i j) {n : ℕ} {m : M} (hm : m ∈ (α.cfg n).log i) :
    ∃ n', m ∈ (α.cfg n').log j := by
  obtain ⟨p⟩ := hij
  induction p generalizing n with
  | nil => exact ⟨n, hm⟩
  | cons h p ih =>
    obtain ⟨n', hn'⟩ := exists_mem_log_of_adj hA h hm
    exact ih hn'

lemma exists_delivers {j : V} {m : M} {n : ℕ} (hm : m ∈ (α.cfg n).log j) :
    ∃ n', α.Delivers n' j m := by
  classical
  have hex : ∃ n, m ∈ (α.cfg n).log j := ⟨n, hm⟩
  have hspec := Nat.find_spec hex
  rcases hk : Nat.find hex with _ | k
  · rw [hk] at hspec; simp at hspec
  · refine ⟨k, Nat.find_min hex (by omega), ?_⟩
    rw [← hk]; exact hspec

/-- **Theorem 3.4**: the BMMB protocol solves the MMB problem (in every execution satisfying the
acknowledgment bound; no assumption on `G'`, no progress bound). -/
theorem theorem_3_4 {Fack : ℝ} (hA : α.AckBound Fack) : α.SolvesMMB := by
  refine ⟨fun n i m hn j hij => ?_, fun j m n n' h h' => ?_, fun n j m h => ?_⟩
  · obtain ⟨n', hn'⟩ := exists_mem_log_of_reachable hA hij (α.mem_log_arrive hn)
    exact exists_delivers hn'
  · by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact h'.1 (((α.mono (show n + 1 ≤ n' by omega)).log_prefix j).subset h.2)
    · exact h.1 (((α.mono (show n' + 1 ≤ n by omega)).log_prefix j).subset h'.2)
  · obtain ⟨n', hn', i, hi⟩ := α.arrives_before_of_mem_log h.2
    exact ⟨n', by omega, i, hi⟩

end Exec

end Podc.MultiMessageBroadcastMAC
