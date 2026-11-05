import Podc.Computability.Distributed.NIS.Views
import Podc.Computability.Distributed.NIS.Subdivision

-- CSLib candidate: Cslib/Computability/Distributed/NIS/Layers.lean
-- (staged by Papers/PODC2020/WhyExtensionBased)
/-!
# The layer graphs `G_r` of an NIS protocol

Alistarh, Aspnes, Ellen, Gelashvili, Zhu, *Why extension-based proofs fail*, Section 4.

The vertices of `G_r` are the states of processes after exactly `r` rounds, together with the states
of processes that terminated after fewer rounds (`Vtx δ r`). Two vertices are adjacent if they belong
to different processes and occur together in some reachable configuration (`Adj δ r`). By the
truncation lemma this is the paper's graph `G_r` (configurations reachable by `r`-round schedules).

The *carrier* `car r x` of a vertex `x` of `G_{r+1}` is the result of its last scan if `x` is a new
vertex (performed `r + 1` rounds), and `{x}` if `x` is a terminated vertex of `G_r`. The structural
facts used by the distance lemmas of `Subdivision.lean`:
* `Adj.car_cases`: the carriers of two adjacent vertices of `G_{r+1}` lie in a common clique of `G_r`;
* `Adj.nested`: two adjacent new vertices have nested carriers;
* `Occ.mem_car`, `Occ.seen_iff_car`: carriers consist of active vertices of `G_r`; a new vertex has seen
  `a` iff some vertex of its carrier has.

`adj_congr` (the graph `G_r` only depends on the protocol below round `r`) and `adj_transfer` (an
edge to a vertex whose past is unaffected survives when more states are terminated) make the graphs
usable for an adversary that defines the protocol lazily.
-/

namespace Cslib.NIS

open St Subdiv

variable {P X Y : Type} [DecidableEq P]

/-- `s` is a vertex of `G_r`: a settled state after exactly `r` rounds, or a terminated state after
fewer rounds. -/
def Vtx (δ : Protocol P X Y) (r : ℕ) (s : St P X) : Prop :=
  s.Settled ∧ (s.rounds = r ∨ (s.rounds < r ∧ decided δ s ≠ none))

/-- `s` occurs in some reachable configuration. -/
def Occ (δ : Protocol P X Y) (s : St P X) : Prop := ∃ E, Reach δ E ∧ E s.pid = s

/-- Adjacency in `G_r`. -/
def Adj (δ : Protocol P X Y) (r : ℕ) (u v : St P X) : Prop :=
  u.pid ≠ v.pid ∧ Vtx δ r u ∧ Vtx δ r v ∧ ∃ E, Reach δ E ∧ E u.pid = u ∧ E v.pid = v

/-- The own state of a new vertex one level down (the value it wrote before its last scan). -/
def own (r : ℕ) (s : St P X) : St P X :=
  if s.rounds = r + 1 then (s.view s.pid).getD s else s

/-- The carrier of a vertex of `G_{r+1}` in `G_r`. -/
def car (r : ℕ) (s : St P X) : Set (St P X) :=
  if s.rounds = r + 1 then {z | z = own r s ∨ ∃ k, s.view k = some z} else {s}

/-- Terminated vertices of `G_r` with output `a` (the paper's `T_r(a)`). -/
def Tset (δ : Protocol P X Y) (r : ℕ) (a : Y) : Set (St P X) :=
  {s | Vtx δ r s ∧ Occ δ s ∧ decided δ s = some a}

/-- Vertices of `G_r` that have not seen the input `a` (the vertex set of the paper's `N_r(a)`, by
its Lemma 5.3). -/
def Uset (δ : Protocol P X Y) (r : ℕ) (a : X) : Set (St P X) :=
  {s | Vtx δ r s ∧ Occ δ s ∧ ¬ Seen a s}

variable {δ δ' : Protocol P X Y} {r : ℕ}

lemma own_mem_car (s : St P X) : own r s ∈ car r s := by
  unfold car
  split_ifs with h <;> simp [own, h]

/-- The `j`-th state of a reachable configuration belongs to process `j`. -/
lemma Rch.pid_eq {E : Config P X} (hE : Rch E) (j : P) : (E j).pid = j :=
  hE.pid_anc (St.mem_anc_self _)

/-- A settled current state with at most `r` rounds is unchanged by truncation to level `r`. -/
lemma Rch.trunc_self {E : Config P X} (hE : Rch E) {j : P} (hs : (E j).Settled)
    (hr : (E j).rounds ≤ r) : Cslib.NIS.trunc r E j = E j := by
  unfold Cslib.NIS.trunc
  apply St.cut_of_depth_le
  rw [hE.depth_settled (St.mem_anc_self _) hs]
  omega

/-- Truncation to level `r` puts a process into its settled ancestor with `r` rounds. -/
lemma Rch.trunc_anc {E : Config P X} (hE : Rch E) {j : P} {z : St P X} (hz : z ∈ (E j).anc)
    (hs : z.Settled) (hr : z.rounds = r) : Cslib.NIS.trunc r E j = z := by
  unfold Cslib.NIS.trunc
  exact St.cut_eq_of_mem_anc hz (by rw [hE.depth_settled hz hs, hr])

omit [DecidableEq P] in
lemma Vtx.rounds_le {s : St P X} (h : Vtx δ r s) : s.rounds ≤ r := by
  rcases h.2 with h | h <;> omega

omit [DecidableEq P] in
/-- A vertex of `G_{r+1}` with fewer than `r + 1` rounds is a terminated vertex of `G_r`. -/
lemma Vtx.of_succ {s : St P X} (h : Vtx δ (r + 1) s) (hr : s.rounds ≠ r + 1) :
    Vtx δ r s ∧ decided δ s ≠ none := by
  rcases h with ⟨hs, h | ⟨hlt, hd⟩⟩
  · exact absurd h hr
  · refine ⟨⟨hs, ?_⟩, hd⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
    · exact Or.inr ⟨h, hd⟩
    · exact Or.inl h

/-- Shape and carrier of a settled state with `r + 1` rounds of a reachable configuration: it is the
result `scan (upd s) v` of a scan, `own r x = s`, and the carrier is the set of values in `v`. -/
lemma Rch.car_eq {E : Config P X} (hE : Rch E) {j : P} {x : St P X} (hx : x ∈ (E j).anc)
    (hxs : x.Settled) (hxr : x.rounds = r + 1) :
    ∃ s v, x = scan (upd s) v ∧ s.rounds = r ∧ v j = some s ∧ own r x = s ∧
      ∀ c, c ∈ car r x ↔ ∃ k, v k = some c := by
  have hpid := hE.pid_anc hx
  cases x with
  | init i a => simp [St.rounds] at hxr
  | upd s => exact absurd hxs (St.not_settled_upd s)
  | scan s v =>
    obtain ⟨s', rfl, -, hv⟩ := hE.scan_shape hx
    have hr : s'.rounds = r := by simpa [St.rounds] using hxr
    have hown : own r (scan (upd s') v) = s' := by
      simp [own, hxr, hpid, hv]
    refine ⟨s', v, rfl, hr, hv, hown, fun c => ?_⟩
    simp only [car, hxr, ite_true, hown, Set.mem_ofPred_eq, St.view_scan]
    constructor
    · rintro (rfl | h)
      · exact ⟨j, hv⟩
      · exact h
    · exact Or.inr

/-- Elements of the carrier of a settled state with `r + 1` rounds of a reachable configuration
are settled ancestors (with `r` rounds) of the current states of their processes, and lie in the
causal past of the state. -/
lemma Rch.mem_car {E : Config P X} (hE : Rch E) {j : P} {x : St P X} (hx : x ∈ (E j).anc)
    (hxs : x.Settled) (hxr : x.rounds = r + 1) {c : St P X} (hc : c ∈ car r x) :
    c ∈ (E c.pid).anc ∧ c.Settled ∧ c.rounds = r ∧ InPast c x := by
  obtain ⟨s, v, rfl, hsr, -, -, hcar⟩ := hE.car_eq hx hxs hxr
  obtain ⟨k, hk⟩ := (hcar c).1 hc
  obtain ⟨hu, hcr, hcs⟩ := hE.view_write hx hk
  have hca : c ∈ (E k).anc := St.anc_subset_of_mem hu (by simp [St.anc, St.mem_anc_self])
  rw [hE.pid_anc hca]
  exact ⟨hca, hcs, hcr.trans hsr, InPast.scanView hk (InPast.upd (InPast.refl c))⟩

lemma Adj.symm {u v : St P X} (h : Adj δ r u v) : Adj δ r v u := by
  obtain ⟨hne, hu, hv, E, hE, hEu, hEv⟩ := h
  exact ⟨Ne.symm hne, hv, hu, E, hE, hEv, hEu⟩

lemma adj_symm : ∀ u v : St P X, Adj δ r u v → Adj δ r v u := fun _ _ h => h.symm

lemma Adj.occ_left {u v : St P X} (h : Adj δ r u v) : Occ δ u := by
  obtain ⟨-, -, -, E, hE, hEu, -⟩ := h
  exact ⟨E, hE, hEu⟩

lemma Adj.occ_right {u v : St P X} (h : Adj δ r u v) : Occ δ v :=
  h.symm.occ_left

/-- Two vertices of `G_r` occurring in the same reachable configuration are adjacent. -/
lemma Reach.adj {E : Config P X} (hE : Reach δ E) {i j : P} (hij : i ≠ j) (hi : Vtx δ r (E i))
    (hj : Vtx δ r (E j)) : Adj δ r (E i) (E j) := by
  have hR := hE.rch
  exact ⟨by rw [hR.pid_eq, hR.pid_eq]; exact hij, hi, hj, E, hE, by rw [hR.pid_eq],
    by rw [hR.pid_eq]⟩

/-- Settled ancestors of current states after `r` rounds are pairwise adjacent in `G_r`. -/
lemma Reach.adj_of_anc {E : Config P X} (hE : Reach δ E) {i j : P} (hij : i ≠ j) {z z' : St P X}
    (hz : z ∈ (E i).anc) (hz' : z' ∈ (E j).anc) (hs : z.Settled) (hs' : z'.Settled)
    (hr : z.rounds = r) (hr' : z'.rounds = r) : Adj δ r z z' := by
  have hR := hE.rch
  have h := (hE.trunc r).adj hij (r := r) (by rw [hR.trunc_anc hz hs hr]; exact ⟨hs, Or.inl hr⟩)
    (by rw [hR.trunc_anc hz' hs' hr']; exact ⟨hs', Or.inl hr'⟩)
  rwa [hR.trunc_anc hz hs hr, hR.trunc_anc hz' hs' hr'] at h

lemma Reach.occ_of_anc {E : Config P X} (hE : Reach δ E) {i : P} {z : St P X}
    (hz : z ∈ (E i).anc) : Occ δ z := by
  have hR := hE.rch
  have hzp : z.pid = i := hR.pid_anc hz
  by_cases hs : z.Settled
  · exact ⟨Cslib.NIS.trunc z.rounds E, hE.trunc _, by rw [hzp]; exact hR.trunc_anc hz hs rfl⟩
  cases z with
  | init j a => exact absurd trivial hs
  | scan s v => exact absurd trivial hs
  | upd s =>
    have hss : s.Settled := hR.upd_settled hz
    have hsa : s ∈ (E i).anc := St.anc_subset_of_mem hz (by simp [St.anc, St.mem_anc_self])
    have hT : Cslib.NIS.trunc s.rounds E i = s := hR.trunc_anc hsa hss rfl
    have hne : s ≠ E i := by
      intro h
      have := St.depth_le_of_mem_anc hz
      rw [← h] at this
      simp [St.depth] at this
    have hact : decided δ (Cslib.NIS.trunc s.rounds E i) = none := by
      rw [hT]; exact hE.past_active (InPast.of_mem_anc hsa) hne
    refine ⟨Cslib.NIS.step (Cslib.NIS.trunc s.rounds E) i, (hE.trunc _).step hact, ?_⟩
    rw [hzp, step_self]
    rcases stepState_cases (Cslib.NIS.trunc s.rounds E) i with ⟨s', h1, -⟩ | ⟨-, h2⟩
    · rw [hT] at h1; subst h1; exact absurd hss (St.not_settled_upd _)
    · rw [h2, hT]

lemma Occ.past_active {s z : St P X} (hs : Occ δ s) (hz : InPast z s) (hne : z ≠ s) :
    decided δ z = none := by
  obtain ⟨E, hE, hEs⟩ := hs
  rw [← hEs] at hz hne
  exact hE.past_active hz hne

/-- The carrier of an occurring new vertex consists of active, occurring vertices of `G_r`. -/
lemma Occ.mem_car {x : St P X} (hx : Occ δ x) (hxs : x.Settled) (hxr : x.rounds = r + 1)
    {c : St P X} (hc : c ∈ car r x) :
    Vtx δ r c ∧ Occ δ c ∧ decided δ c = none ∧ c.rounds = r ∧ InPast c x := by
  obtain ⟨E, hE, hEx⟩ := hx
  have hxa : x ∈ (E x.pid).anc := by rw [hEx]; exact St.mem_anc_self _
  obtain ⟨hca, hcs, hcr, hpast⟩ := hE.rch.mem_car hxa hxs hxr hc
  refine ⟨⟨hcs, Or.inl hcr⟩, hE.occ_of_anc hca, ?_, hcr, hpast⟩
  refine Occ.past_active ⟨E, hE, hEx⟩ hpast ?_
  rintro rfl
  omega

lemma Occ.own_view {x : St P X} (hx : Occ δ x) (hxs : x.Settled) (hxr : x.rounds = r + 1) :
    x.view x.pid = some (own r x) := by
  obtain ⟨E, hE, hEx⟩ := hx
  have hxa : x ∈ (E x.pid).anc := by rw [hEx]; exact St.mem_anc_self _
  obtain ⟨s, v, hxeq, -, hv, hown, -⟩ := hE.rch.car_eq hxa hxs hxr
  rw [hown, ← hv, hxeq]
  rfl

/-- A new vertex has seen `a` iff a vertex of its carrier has. -/
lemma Occ.seen_iff_car {x : St P X} (hx : Occ δ x) (hxs : x.Settled) (hxr : x.rounds = r + 1)
    (a : X) : Seen a x ↔ ∃ c ∈ car r x, Seen a c := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨E, hE, hEx⟩ := hx
    have hxa : x ∈ (E x.pid).anc := by rw [hEx]; exact St.mem_anc_self _
    obtain ⟨s, v, hxeq, -, -, hown, hcar⟩ := hE.rch.car_eq hxa hxs hxr
    rw [hxeq] at hi
    rcases hi with _ | _ | h | ⟨hk, h⟩
    · rcases h with _ | h
      exact ⟨s, hown ▸ own_mem_car x, i, h⟩
    · rcases h with _ | h
      exact ⟨_, (hcar _).2 ⟨_, hk⟩, i, h⟩
  · rintro ⟨c, hc, hsc⟩
    exact hsc.mono (hx.mem_car hxs hxr hc).2.2.2.2

/-- Elements of the carrier of a vertex `u` of `G_{r+1}` occurring in a reachable configuration `E`
are vertices of `G_r`, namely the states of their processes in the truncation of `E` to level `r`. -/
lemma car_trunc {E : Config P X} (hE : Reach δ E) {u c : St P X} (hu : E u.pid = u)
    (hv : Vtx δ (r + 1) u) (hc : c ∈ car r u) : Cslib.NIS.trunc r E c.pid = c ∧ Vtx δ r c := by
  have hR := hE.rch
  have hua : u ∈ (E u.pid).anc := by rw [hu]; exact St.mem_anc_self _
  by_cases hr : u.rounds = r + 1
  · obtain ⟨hca, hcs, hcr, -⟩ := hR.mem_car hua hv.1 hr hc
    exact ⟨hR.trunc_anc hca hcs hcr, hcs, Or.inl hcr⟩
  · have hcu : c = u := by simpa [car, hr] using hc
    subst hcu
    obtain ⟨hvr, -⟩ := hv.of_succ hr
    refine ⟨(hR.trunc_self (by rw [hu]; exact hv.1) (by rw [hu]; exact hvr.rounds_le)).trans hu,
      hvr⟩

/-- **Carrier lemma**: the carriers of adjacent vertices of `G_{r+1}` lie in a common clique of
`G_r`. -/
lemma Adj.car_cases {u w : St P X} (h : Adj δ (r + 1) u w) {c d : St P X} (hc : c ∈ car r u)
    (hd : d ∈ car r w) : c = d ∨ Adj δ r c d := by
  obtain ⟨-, hu, hw, E, hE, hEu, hEw⟩ := h
  obtain ⟨hc1, hc2⟩ := car_trunc hE hEu hu hc
  obtain ⟨hd1, hd2⟩ := car_trunc hE hEw hw hd
  by_cases hcd : c.pid = d.pid
  · left
    rw [← hc1, ← hd1, hcd]
  · right
    have := (hE.trunc r).adj hcd (by rw [hc1]; exact hc2) (by rw [hd1]; exact hd2)
    rwa [hc1, hd1] at this

/-- Adjacent new vertices have nested carriers. -/
lemma Adj.nested {u w : St P X} (h : Adj δ (r + 1) u w) (hu : decided δ (own r u) = none)
    (hw : decided δ (own r w) = none) : car r u ⊆ car r w ∨ car r w ⊆ car r u := by
  obtain ⟨-, hvu, hvw, E, hE, hEu, hEw⟩ := h
  have hR := hE.rch
  have hnew : ∀ {x : St P X}, Vtx δ (r + 1) x → decided δ (own r x) = none → x.rounds = r + 1 := by
    intro x hx hd
    by_contra hr
    have : own r x = x := by simp [own, hr]
    exact (hx.of_succ hr).2 (this ▸ hd)
  have hua : u ∈ (E u.pid).anc := by rw [hEu]; exact St.mem_anc_self _
  have hwa : w ∈ (E w.pid).anc := by rw [hEw]; exact St.mem_anc_self _
  obtain ⟨s, v, hus, hsr, -, -, hcu⟩ := hR.car_eq hua hvu.1 (hnew hvu hu)
  obtain ⟨s', v', hws, hsr', -, -, hcw⟩ := hR.car_eq hwa hvw.1 (hnew hvw hw)
  rw [hus] at hua
  rw [hws] at hwa
  rcases hR.view_nested hua hwa (hsr.trans hsr'.symm) with h | h
  · left
    intro c hc
    obtain ⟨k, hk⟩ := (hcu c).1 hc
    exact (hcw c).2 ⟨k, h k c hk⟩
  · right
    intro c hc
    obtain ⟨k, hk⟩ := (hcw c).1 hc
    exact (hcu c).2 ⟨k, h k c hk⟩

omit [DecidableEq P] in
/-- Vertices of `G_r` only depend on the protocol on states of fewer than `r` rounds. -/
lemma vtx_congr' (hδ : ∀ s : St P X, s.rounds < r → decided δ s = decided δ' s) {u : St P X} :
    Vtx δ r u ↔ Vtx δ' r u := by
  unfold Vtx
  constructor
  · rintro ⟨hs, h | ⟨hlt, hd⟩⟩
    · exact ⟨hs, Or.inl h⟩
    · exact ⟨hs, Or.inr ⟨hlt, by rwa [← hδ u hlt]⟩⟩
  · rintro ⟨hs, h | ⟨hlt, hd⟩⟩
    · exact ⟨hs, Or.inl h⟩
    · exact ⟨hs, Or.inr ⟨hlt, by rwa [hδ u hlt]⟩⟩

/-- `G_r` (vertices, edges, occurrences of vertices of `G_r`) only depends on the protocol on states
of fewer than `r` rounds. -/
lemma adj_congr (hδ : ∀ s : St P X, s.rounds < r → decided δ s = decided δ' s) {u v : St P X} :
    Adj δ r u v ↔ Adj δ' r u v := by
  have key : ∀ {δ δ' : Protocol P X Y}, (∀ s : St P X, s.rounds < r → decided δ s = decided δ' s) →
      Adj δ r u v → Adj δ' r u v := by
    intro δ δ' hδ h
    obtain ⟨hne, hu, hv, E, hE, hEu, hEv⟩ := h
    have hR := hE.rch
    refine ⟨hne, (vtx_congr' hδ).1 hu, (vtx_congr' hδ).1 hv, Cslib.NIS.trunc r E,
      hE.trunc_congr r hδ, ?_, ?_⟩
    · exact (hR.trunc_self (by rw [hEu]; exact hu.1) (by rw [hEu]; exact hu.rounds_le)).trans hEu
    · exact (hR.trunc_self (by rw [hEv]; exact hv.1) (by rw [hEv]; exact hv.rounds_le)).trans hEv
  exact ⟨key hδ, key fun s hs => (hδ s hs).symm⟩

lemma vtx_congr (hδ : ∀ s : St P X, s.rounds < r → decided δ s = decided δ' s) {u : St P X} :
    Vtx δ r u ↔ Vtx δ' r u :=
  vtx_congr' hδ

lemma occ_congr {u : St P X} (hu : u.Settled)
    (hδ : ∀ s : St P X, s.rounds < u.rounds → decided δ s = decided δ' s) :
    Occ δ u ↔ Occ δ' u := by
  have key : ∀ {δ δ' : Protocol P X Y},
      (∀ s : St P X, s.rounds < u.rounds → decided δ s = decided δ' s) → Occ δ u → Occ δ' u := by
    intro δ δ' hδ h
    obtain ⟨E, hE, hEu⟩ := h
    exact ⟨Cslib.NIS.trunc u.rounds E, hE.trunc_congr _ hδ,
      (hE.rch.trunc_self (by rw [hEu]; exact hu) (by rw [hEu])).trans hEu⟩
  exact ⟨key hδ, key fun s hs => (hδ s hs).symm⟩

/-- **Persistence of edges.** An edge `x — w` of `G_r(δ)` is an edge of `G_r(δ')` if `x` still occurs
under `δ'`, the strict causal past of `w` is still active, and both are still vertices. -/
lemma adj_transfer {x w : St P X} (h : Adj δ r x w) (hx : Occ δ' x)
    (hw : ∀ z, InPast z w → z ≠ w → decided δ' z = none) (hvx : Vtx δ' r x) (hvw : Vtx δ' r w) :
    Adj δ' r x w := by
  obtain ⟨hne, -, -, E, hE, hEx, hEw⟩ := h
  obtain ⟨E', hE', hE'A⟩ := hE.rch.exists_reach (δ' := δ') {x.pid, w.pid} (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro i (rfl | rfl) z hz hne'
    · rw [hEx] at hz hne'
      exact hx.past_active hz hne'
    · rw [hEw] at hz hne'
      exact hw z hz hne')
  exact ⟨hne, hvx, hvw, E', hE', by rw [hE'A _ (by simp), hEx], by rw [hE'A _ (by simp), hEw]⟩

/-! ## Instantiating the abstract distance lemmas -/

/-- Lemma 4.11 for `G_r`, `G_{r+1}`. -/
theorem far_layer {A B A' B' : Set (St P X)} (hA : ∀ x ∈ A', car r x ⊆ A)
    (hB : ∀ x ∈ B', car r x ⊆ B) {d : ℕ} (h : Far (Adj δ r) A B d) :
    Far (Adj δ (r + 1)) A' B' d :=
  Far.subdiv (car r) (own r) own_mem_car (fun _ _ h _ hc _ hd => h.car_cases hc hd) hA hB h

/-- Lemma 4.13 for `G_r`, `G_{r+1}`: `act` = not terminated. -/
theorem far_layer_succ {A B A' B' : Set (St P X)} (hA : ∀ x ∈ A', car r x ⊆ A)
    (hB : ∀ x ∈ B', car r x ⊆ B) {d : ℕ} (h : Far (Adj δ r) A B d)
    (hcut : ActCut (Adj δ r) (fun s => decided δ s = none) A B) :
    Far (Adj δ (r + 1)) A' B' (d + 1) :=
  Far.subdiv_succ (car r) (own r) (fun s => decided δ s = none) own_mem_car
    (fun _ _ h _ hc _ hd => h.car_cases hc hd) (fun _ _ h hx hy => h.nested hx hy) hA hB h hcut

/-- Carriers of terminated vertices of `G_{r+1}` that already were vertices of `G_r`. -/
lemma car_Tset {a : Y} (hnew : ∀ s : St P X, s.rounds = r + 1 → decided δ s = none) :
    ∀ x ∈ Tset δ (r + 1) a, car r x ⊆ Tset δ r a := by
  rintro x ⟨hv, ho, hd⟩ c hc
  have hr : x.rounds ≠ r + 1 := fun h => by simp [hnew x h] at hd
  have hcx : c = x := by simpa [car, hr] using hc
  subst hcx
  exact ⟨(hv.of_succ hr).1, ho, hd⟩

lemma car_Uset (a : X) : ∀ x ∈ Uset δ (r + 1) a, car r x ⊆ Uset δ r a := by
  rintro x ⟨hv, ho, hns⟩ c hc
  by_cases hr : x.rounds = r + 1
  · obtain ⟨hcv, hco, -, -, -⟩ := ho.mem_car hv.1 hr hc
    exact ⟨hcv, hco, fun hs => hns ((ho.seen_iff_car hv.1 hr a).2 ⟨c, hc, hs⟩)⟩
  · have hcx : c = x := by simpa [car, hr] using hc
    subst hcx
    exact ⟨(hv.of_succ hr).1, ho, hns⟩

end Cslib.NIS
