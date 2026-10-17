import Papers.PODC2026.LocalComputable.Concrete
import Mathlib.Order.Interval.Finset.Nat

/-!
# Monotonicity of the locality (Definition 3.5)

Definition 3.5 claims that the locality `T` of an algorithm (the worst-case number of rounds over
`n`-node networks) is non-decreasing, "since the set of graphs with `n₁` nodes is contained in the
class of graphs with `n₂` nodes". That justification is not literally right (an `n₁`-node graph is
not an `n₂`-node graph), but the claim holds in the model of Section 3 (no information on `n`):
adding an isolated node with a fresh identifier (possible since identifiers range over
`[1, n^c]`, `c ≥ 1`) does not change the views of the other nodes. So every node of an `n`-node
network stops within the time bound `T(m)` of any larger size `m ≥ n` (`stops_of_le`).
-/

namespace LocalComputable

open PNet VTree

/-- Add an isolated node with identifier `f` and input `0`. -/
def PNet.pad (G : PNet) (f : ℕ) : PNet := ⟨G.n + 1, G.nbr ++ [[]], G.id ++ [f], G.inp ++ [0]⟩

namespace PNet

variable {Δ c k : ℕ} {G : PNet}

theorem pad_nbrOf (hG : G.WF Δ c k) (f : ℕ) {v : ℕ} (hv : v < G.n) :
    (G.pad f).nbrOf v = G.nbrOf v := by
  simp only [pad, nbrOf, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [hG.len_nbr]; exact hv)]

theorem pad_idOf (hG : G.WF Δ c k) (f : ℕ) {v : ℕ} (hv : v < G.n) :
    (G.pad f).idOf v = G.idOf v := by
  simp only [pad, idOf, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [hG.len_id]; exact hv)]

theorem pad_inpOf (hG : G.WF Δ c k) (f : ℕ) {v : ℕ} (hv : v < G.n) :
    (G.pad f).inpOf v = G.inpOf v := by
  simp only [pad, inpOf, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [hG.len_inp]; exact hv)]

theorem pad_nbrOf_last (hG : G.WF Δ c k) (f : ℕ) : (G.pad f).nbrOf G.n = [] := by
  simp [pad, nbrOf, List.getD_eq_getElem?_getD, hG.len_nbr]

theorem pad_idOf_last (hG : G.WF Δ c k) (f : ℕ) : (G.pad f).idOf G.n = f := by
  simp [pad, idOf, List.getD_eq_getElem?_getD, hG.len_id]

theorem pad_inpOf_last (hG : G.WF Δ c k) (f : ℕ) : (G.pad f).inpOf G.n = 0 := by
  simp [pad, inpOf, List.getD_eq_getElem?_getD, hG.len_inp]

/-- Views of old nodes are unchanged by padding. -/
theorem fview_pad (hG : G.WF Δ c k) (f : ℕ) :
    ∀ t {v : ℕ}, v < G.n → fview (G.pad f) v t = fview G v t := by
  intro t
  induction t with
  | zero => intro v hv; simp [fview, pad_nbrOf hG f hv, pad_idOf hG f hv, pad_inpOf hG f hv]
  | succ t ih =>
    intro v hv
    simp only [fview, pad_nbrOf hG f hv, pad_idOf hG f hv, pad_inpOf hG f hv]
    congr 1
    exact List.map_congr_left fun u hu => ih (hG.nbr_lt v hv u hu)

/-- Padding with a fresh identifier in range keeps the network well formed. -/
theorem pad_wf (hG : G.WF Δ c k) (hk : 1 ≤ k) {f : ℕ} (hf1 : 1 ≤ f) (hf2 : f ≤ (G.n + 1) ^ c)
    (hfresh : ∀ v < G.n, G.idOf v ≠ f) : (G.pad f).WF Δ c k := by
  have hn : (G.pad f).n = G.n + 1 := rfl
  have cases_v : ∀ v, v < G.n + 1 → v < G.n ∨ v = G.n := fun v hv => by omega
  refine ⟨by simp [pad, hG.len_nbr], by simp [pad, hG.len_id], by simp [pad, hG.len_inp],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases cases_v v hv with hv | rfl
    · rw [pad_nbrOf hG f hv]; exact hG.nodup v hv
    · rw [pad_nbrOf_last hG f]; exact List.nodup_nil
  · intro v hv
    rcases cases_v v hv with hv | rfl
    · rw [pad_nbrOf hG f hv]; exact hG.deg_le v hv
    · rw [pad_nbrOf_last hG f]; simp
  · intro v hv u hu
    rcases cases_v v hv with hv | rfl
    · rw [pad_nbrOf hG f hv] at hu; rw [hn]; exact Nat.lt_succ_of_lt (hG.nbr_lt v hv u hu)
    · rw [pad_nbrOf_last hG f] at hu; simp at hu
  · intro v hv
    rcases cases_v v hv with hv | rfl
    · rw [pad_nbrOf hG f hv]; exact hG.irrefl v hv
    · rw [pad_nbrOf_last hG f]; simp
  · intro v hv u hu
    rcases cases_v v hv with hv | rfl
    · rw [pad_nbrOf hG f hv] at hu
      have hu' := hG.nbr_lt v hv u hu
      rw [pad_nbrOf hG f hu']
      exact hG.symm v hv u hu
    · rw [pad_nbrOf_last hG f] at hu; simp at hu
  · intro u hu v hv huv
    rcases cases_v u hu with hu | rfl <;> rcases cases_v v hv with hv | rfl
    · rw [pad_idOf hG f hu, pad_idOf hG f hv] at huv; exact hG.id_inj u hu v hv huv
    · rw [pad_idOf hG f hu, pad_idOf_last hG f] at huv; exact absurd huv (hfresh u hu)
    · rw [pad_idOf hG f hv, pad_idOf_last hG f] at huv; exact absurd huv.symm (hfresh v hv)
    · rfl
  · intro v hv
    rcases cases_v v hv with hv | rfl
    · rw [pad_idOf hG f hv]; exact hG.id_pos v hv
    · rw [pad_idOf_last hG f]; exact hf1
  · intro v hv
    rw [hn]
    rcases cases_v v hv with hv | rfl
    · rw [pad_idOf hG f hv]
      exact (hG.id_le v hv).trans (Nat.pow_le_pow_left (Nat.le_succ _) c)
    · rw [pad_idOf_last hG f]; exact hf2
  · intro v hv
    rcases cases_v v hv with hv | rfl
    · rw [pad_inpOf hG f hv]; exact hG.inp_lt v hv
    · rw [pad_inpOf_last hG f]; exact hk

/-- A fresh identifier in `[1, (n+1)^c]` exists (`c ≥ 1`). -/
theorem exists_fresh (hc : 1 ≤ c) (G : PNet) :
    ∃ f, 1 ≤ f ∧ f ≤ (G.n + 1) ^ c ∧ ∀ v < G.n, G.idOf v ≠ f := by
  classical
  have hcard : ((Finset.range G.n).image G.idOf).card < (Finset.Icc 1 ((G.n + 1) ^ c)).card := by
    calc ((Finset.range G.n).image G.idOf).card ≤ G.n := by
          simpa using Finset.card_image_le (s := Finset.range G.n) (f := G.idOf)
      _ < G.n + 1 := Nat.lt_succ_self _
      _ ≤ (G.n + 1) ^ c := Nat.le_self_pow (by omega) _
      _ = (Finset.Icc 1 ((G.n + 1) ^ c)).card := by simp
  obtain ⟨f, hf, hfn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_Icc] at hf
  refine ⟨f, hf.1, hf.2, fun v hv h => hfn ?_⟩
  exact Finset.mem_image.mpr ⟨v, Finset.mem_range.mpr hv, h⟩

end PNet

/-- Every well-formed network embeds, with unchanged views of its nodes, into a well-formed
network with any larger number of nodes. -/
theorem exists_pad {Δ c k : ℕ} (hc : 1 ≤ c) (hk : 1 ≤ k) :
    ∀ d (G : PNet), G.WF Δ c k → ∃ G' : PNet, G'.WF Δ c k ∧ G'.n = G.n + d ∧
      ∀ v < G.n, ∀ t, fview G' v t = fview G v t := by
  intro d
  induction d with
  | zero => intro G hG; exact ⟨G, hG, rfl, fun _ _ _ => rfl⟩
  | succ d ih =>
    intro G hG
    obtain ⟨f, hf1, hf2, hfr⟩ := PNet.exists_fresh hc G
    have hG1 := PNet.pad_wf hG hk hf1 hf2 hfr
    obtain ⟨G', hG', hn, hv⟩ := ih _ hG1
    refine ⟨G', hG', by rw [hn]; simp [PNet.pad]; omega, fun v hvn t => ?_⟩
    rw [hv v (by simp [PNet.pad]; omega) t, PNet.fview_pad hG f t hvn]

/-- **Definition 3.5 (claim): the locality is non-decreasing.** In the concrete model with
`c ≥ 1`, `k ≥ 1`: if every node of every network stops by `T(size)`, then every node of an
`n`-node network also stops by `T(m)` for every `m ≥ n`. Hence the minimal (worst-case) locality
function is non-decreasing. -/
theorem stops_of_le {Δ c k : ℕ} (hc : 1 ≤ c) (hk : 1 ≤ k) {Out : Type*} (A : Alg VTree Out)
    (T : ℕ → ℕ)
    (hA : ∀ (G : Net Δ c k) (v : ℕ), v < (concreteModel Δ c k).size G →
      ((concreteModel Δ c k).out A G v (T ((concreteModel Δ c k).size G))).isSome)
    (G : Net Δ c k) {v : ℕ} (hv : v < (concreteModel Δ c k).size G) {m : ℕ}
    (hm : (concreteModel Δ c k).size G ≤ m) :
    ((concreteModel Δ c k).out A G v (T m)).isSome := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨G', hG', hn, hview⟩ := exists_pad hc hk d G.1 G.2
  have h := hA ⟨G', hG'⟩ v (by change v < G'.n; rw [hn]; change v < G.1.n at hv; omega)
  change ((concreteModel Δ c k).out A ⟨G', hG'⟩ v (T G'.n)).isSome at h
  rw [hn] at h
  rwa [Model.out_congr A (show (concreteModel Δ c k).view ⟨G', hG'⟩ v _ =
    (concreteModel Δ c k).view G v _ from hview v hv _)] at h

end LocalComputable
