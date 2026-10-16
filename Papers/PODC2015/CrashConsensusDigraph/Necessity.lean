import Papers.PODC2015.CrashConsensusDigraph.SyncModel

/-!
# Theorem 1: crash consensus requires `f` CT node connectivity

If some algorithm solves crash consensus on `G` with at most `f` crash faults (for an input
domain containing two distinct values), then `G` satisfies `f` crash-tolerant node connectivity.

Proof (the paper's argument made precise). Otherwise, by `ctConn_iff_oneReach`, there are `F`
with `|F| ≤ f` and `i, j ∉ F` without a common ancestor in `G_F`. Let `Sᵢ`, `Sⱼ` be the sets of
ancestors of `i`, `j` in `G_F` (disjoint). Crash `F` before the start (round `0`, reaching nobody)
and give input `a` to `Sᵢ` and `b` to the other nodes. `Sᵢ` only hears from `Sᵢ`, so `i` cannot
distinguish this execution from the one where all inputs are `a`, and decides `a` by validity
there; likewise `j` decides `b`, contradicting agreement. The paper says "the only input value
learned by `x` is `0`, so `0` should be the output of `x`"; the indistinguishability with the
all-`a` execution is what makes this step rigorous (`state_eq_of_closed`).
-/

open Finset

set_option linter.unusedSectionVars false

namespace CrashConsensusDigraph

open AsyncApproxBCDirected

variable {V I M S : Type*} [DecidableEq V] {G : Digraph V}

/-- The adversary crashing exactly the nodes of `F`, before they send anything. -/
def crashAtStart (F : Finset V) : Adversary V where
  crash u := if u ∈ F then some 0 else none
  part _ _ := False

theorem crashAtStart_admissible {F : Finset V} {f : ℕ} (hF : F.card ≤ f) :
    (crashAtStart F).Admissible f :=
  ⟨F, hF, fun u c h => by by_contra hu; simp [crashAtStart, hu] at h⟩

theorem crashAtStart_correct {F : Finset V} {u : V} (hu : u ∉ F) :
    (crashAtStart F).crash u = none := by simp [crashAtStart, hu]

theorem notMem_of_delivers_crashAtStart {F : Finset V} {r : ℕ} {u w : V}
    (h : Delivers G (crashAtStart F) r u w) : u ∉ F := by
  intro hu
  rcases h.2 0 (by simp [crashAtStart, hu]) with h | h
  · omega
  · exact h.2

/-- **Theorem 1.** If exact (crash) consensus is solvable on `G` with at most `f` crash faults,
for inputs in a set `In` containing two distinct values, then `G` satisfies `f` CT node
connectivity. -/
theorem theorem1 [Fintype V] {f : ℕ} {In : Set I} {a b : I} (ha : a ∈ In) (hb : b ∈ In)
    (hab : a ≠ b) {alg : Algorithm V I M S I} (h : SolvesOn G f In alg) : CTConn G f := by
  classical
  rw [ctConn_iff_oneReach]
  intro F i j hF hi hj
  by_contra hcon
  push Not at hcon
  set adv : Adversary V := crashAtStart F with hadv_def
  have hadv : adv.Admissible f := crashAtStart_admissible hF
  set Si : Set V := {x | Reaches G F x i}
  set Sj : Set V := {x | Reaches G F x j}
  have hclosed : ∀ (T : Set V), (∀ x y, G.Adj x y → x ∉ F → y ∈ T → x ∈ T) →
      ∀ r u w, Delivers G adv r u w → w ∈ T → u ∈ T :=
    fun T hT r u w hd hw => hT u w hd.adj (notMem_of_delivers_crashAtStart hd) hw
  have hSi : ∀ x y, G.Adj x y → x ∉ F → y ∈ Si → x ∈ Si :=
    fun x y e hx hy => Reaches.head e hx hy
  have hSj : ∀ x y, G.Adj x y → x ∉ F → y ∈ Sj → x ∈ Sj :=
    fun x y e hx hy => Reaches.head e hx hy
  -- the mixed execution
  set inp : V → I := fun x => if Reaches G F x i then a else b
  have hinp : ∀ u, inp u ∈ In := fun u => by simp only [inp]; split_ifs <;> assumption
  obtain ⟨hterm, hagr, -⟩ := h adv hadv inp hinp
  obtain ⟨oi, hoi⟩ := hterm i (crashAtStart_correct hi)
  obtain ⟨oj, hoj⟩ := hterm j (crashAtStart_correct hj)
  -- `i` decides `a`
  have hia : oi = a := by
    obtain ⟨-, -, hval⟩ := h adv hadv (fun _ => a) (fun _ => ha)
    have hst := state_eq_of_closed (alg := alg) (hclosed Si hSi)
      (inp := inp) (inp' := fun _ => a) (fun u hu => by simp [inp, show Reaches G F u i from hu])
    have : Decides G alg adv (fun _ => a) i oi :=
      (decides_congr fun r => hst r i (Reaches.refl hi)).mp hoi
    obtain ⟨w, hw⟩ := hval i oi (crashAtStart_correct hi) this
    exact hw.symm
  -- `j` decides `b`
  have hjb : oj = b := by
    obtain ⟨-, -, hval⟩ := h adv hadv (fun _ => b) (fun _ => hb)
    have hst := state_eq_of_closed (alg := alg) (hclosed Sj hSj)
      (inp := inp) (inp' := fun _ => b) (fun u hu => by
        have : ¬ Reaches G F u i := fun h' => hcon u hu h'
        simp [inp, this])
    have : Decides G alg adv (fun _ => b) j oj :=
      (decides_congr fun r => hst r j (Reaches.refl hj)).mp hoj
    obtain ⟨w, hw⟩ := hval j oj (crashAtStart_correct hj) this
    exact hw.symm
  exact hab (hia ▸ hjb ▸ hagr i j oi oj (crashAtStart_correct hi) (crashAtStart_correct hj) hoi hoj)

end CrashConsensusDigraph
