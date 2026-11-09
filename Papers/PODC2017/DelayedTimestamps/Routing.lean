import Podc.Computability.Distributed.MessagePassing.Causality.VectorClock
import Cslib.Foundations.Combinatorics.SimpleGraph.VertexConnectivity

/-!
# Adversarial executions for the online lower bounds (Appendix B)

Building blocks for the executions used in the proofs of Lemmas 1–4 of Vaidya–Kulkarni:

* `hop l u v`: `u` sends a message to `v`, which receives it immediately.
* `route l p`: forward a token along the walk `p` (one `hop` per edge).
* `routeAll l ws`: forward a token from the start of every walk `w ∈ ws` to their common end `r`.
* `gather`: the resulting execution (followed by a final local event at `r`) is well formed, uses
  only edges of `G`, adds events only at processes on the walks, and every `j ∈ js` happened-before
  the final event.
* `not_hb_of_last`: a computation event after which its process takes no further step
  happened-before no event.

The paper floods messages with carefully chosen channel delays; routing along explicit walks
that avoid the victim process `p_k` gives the same causal structure directly.
-/

namespace Podc.DelayedTimestamps

set_option linter.unusedSectionVars false

open Cslib.Causality

variable {P : Type*} [DecidableEq P]

/-- `u` sends a message to `v`, which receives it immediately. -/
def hop (l : Exec P) (u v : P) : Exec P := l ++ [.send u v, .recv v l.length]

lemma hop_length (l : Exec P) (u v : P) : (hop l u v).length = l.length + 2 := by
  simp [hop]

lemma getElem?_hop (l : Exec P) (u v : P) (i : ℕ) :
    (hop l u v)[i]? = if i < l.length then l[i]? else if i = l.length then some (.send u v)
      else if i = l.length + 1 then some (.recv v l.length) else none := by
  unfold hop
  split_ifs with h1 h2 h3
  · exact List.getElem?_append_left h1
  · subst h2; simp
  · subst h3; simp
  · rw [List.getElem?_eq_none]; simp; omega

lemma hop_wf {l : Exec P} (hl : l.WF) (u v : P) : (hop l u v).WF := by
  constructor
  · intro j p m h
    rw [getElem?_hop] at h
    split_ifs at h with h1 h2 h3
    · exact hl.recv_lt h
    · cases h
    · cases h; omega
  · intro j p m h
    rw [getElem?_hop] at h
    split_ifs at h with h1 h2 h3
    · obtain ⟨q, hq⟩ := hl.recv_send h
      refine ⟨q, ?_⟩
      rw [getElem?_hop]
      simp only [(hl.recv_lt h).trans h1, ↓reduceIte]
      exact hq
    · cases h
    · cases h
      exact ⟨u, by rw [getElem?_hop]; simp⟩
  · intro j j' p p' m h h'
    rw [getElem?_hop] at h h'
    split_ifs at h h' with h1 h2 h3 h4 h5 h6 h7 h8 h9 <;> (try cases h) <;> (try cases h')
    all_goals first
      | exact hl.recv_unique h h'
      | (have := hl.recv_lt h; omega)
      | (have := hl.recv_lt h'; omega)
      | omega

lemma hop_onGraph {G : SimpleGraph P} {l : Exec P} (hl : l.OnGraph G) {u v : P} (huv : G.Adj u v) :
    (hop l u v).OnGraph G := by
  intro j p q h
  rw [getElem?_hop] at h
  split_ifs at h with h1 h2 h3 <;> first | exact hl h | (cases h; exact huv) | cases h

lemma hop_procAt_lt {l : Exec P} {u v : P} {i : ℕ} (hi : i < l.length) :
    (hop l u v).procAt i = l.procAt i := Exec.procAt_append_of_lt _ hi

lemma hop_procAt_new {l : Exec P} {u v : P} {i : ℕ} {x : P} (hi : l.length ≤ i)
    (h : (hop l u v).procAt i = some x) : x = u ∨ x = v := by
  obtain ⟨a, ha, rfl⟩ := Exec.procAt_eq_some.1 h
  rw [getElem?_hop] at ha
  split_ifs at ha with h1 h2 h3 <;> first | omega | (cases ha; simp)

/-- After a hop, information at `u` (before the hop) has reached `v`. -/
lemma hop_reach {l : Exec P} {u v : P} {x y : ℕ} (hy : y < l.length)
    (hyu : l.procAt y = some u) (hxy : l.HBeq x y) :
    (hop l u v).procAt (l.length + 1) = some v ∧ (hop l u v).HBeq x (l.length + 1) := by
  have hs : (hop l u v)[l.length]? = some (.send u v) := by rw [getElem?_hop]; simp
  have hr : (hop l u v)[l.length + 1]? = some (.recv v l.length) := by rw [getElem?_hop]; simp
  refine ⟨Exec.procAt_of_get hr, ?_⟩
  have h1 : (hop l u v).HB y l.length :=
    Exec.hb_of_lt hy (by rw [hop_procAt_lt hy]; exact hyu) (Exec.procAt_of_get hs)
  have h2 : (hop l u v).HB l.length (l.length + 1) := .of_step (.msg hr)
  exact Or.inr ((hxy.append _).trans_hb (h1.trans h2))

/-- Forward a token along a walk. -/
def route {G : SimpleGraph P} : Exec P → {u v : P} → G.Walk u v → Exec P
  | l, _, _, .nil => l
  | l, u, _, .cons (v := w) _ p => route (hop l u w) p

section Route

variable {G : SimpleGraph P}

lemma route_prefix (l : Exec P) {u v : P} (p : G.Walk u v) : ∃ rest, route l p = l ++ rest := by
  induction p generalizing l with
  | nil => exact ⟨[], by simp [route]⟩
  | @cons a b c h p ih =>
    obtain ⟨rest, hr⟩ := ih (hop l a b)
    exact ⟨[Act.send a b, Act.recv b l.length] ++ rest, by simp only [route]; rw [hr]; simp [hop]⟩

lemma route_wf {l : Exec P} (hl : l.WF) {u v : P} (p : G.Walk u v) : (route l p).WF := by
  induction p generalizing l with
  | nil => exact hl
  | cons h p ih => exact ih (hop_wf hl _ _)

lemma route_onGraph {l : Exec P} (hl : l.OnGraph G) {u v : P} (p : G.Walk u v) :
    (route l p).OnGraph G := by
  induction p generalizing l with
  | nil => exact hl
  | cons h p ih => exact ih (hop_onGraph hl h)

lemma route_procAt_new {l : Exec P} {u v : P} (p : G.Walk u v) {i : ℕ} {x : P}
    (hi : l.length ≤ i) (h : (route l p).procAt i = some x) : x ∈ p.support := by
  induction p generalizing l with
  | nil => exact absurd (Exec.lt_length_of_procAt h) (by simp [route]; omega)
  | @cons a b c hab p ih =>
    simp only [route] at h
    by_cases hi' : (hop l a b).length ≤ i
    · exact List.mem_cons_of_mem _ (ih hi' h)
    · obtain ⟨rest, hr⟩ := route_prefix (hop l a b) p
      rw [hr, Exec.procAt_append_of_lt _ (by omega)] at h
      rcases hop_procAt_new hi h with rfl | rfl
      · simp
      · simp

lemma route_reach {l : Exec P} (hwf : l.WF) {u v : P} (p : G.Walk u v) {x y : ℕ}
    (hy : y < l.length) (hyu : l.procAt y = some u) (hxy : l.HBeq x y) :
    ∃ y', y' < (route l p).length ∧ (route l p).procAt y' = some v ∧ (route l p).HBeq x y' := by
  induction p generalizing l y with
  | nil => exact ⟨y, hy, hyu, hxy⟩
  | @cons a b c hab p ih =>
    obtain ⟨h1, h2⟩ := hop_reach (v := b) hy hyu hxy
    exact ih (hop_wf hwf a b) (by rw [hop_length]; omega) h1 h2

end Route

/-- Forward a token from the start `w.1` of every walk `w ∈ ws` to `r` along `w.2`. -/
def routeAll {G : SimpleGraph P} {r : P} (l : Exec P) (ws : List (Σ j : P, G.Walk j r)) :
    Exec P :=
  ws.foldl (fun l w => route l w.2) l

section RouteAll

variable {G : SimpleGraph P} {r : P}

lemma routeAll_cons (l : Exec P) (w : Σ j : P, G.Walk j r) (ws : List (Σ j : P, G.Walk j r)) :
    routeAll l (w :: ws) = routeAll (route l w.2) ws := rfl

lemma routeAll_prefix (l : Exec P) (ws : List (Σ j : P, G.Walk j r)) :
    ∃ rest, routeAll l ws = l ++ rest := by
  induction ws generalizing l with
  | nil => exact ⟨[], by simp [routeAll]⟩
  | cons w ws ih =>
    obtain ⟨r1, h1⟩ := route_prefix l w.2
    obtain ⟨r2, h2⟩ := ih (route l w.2)
    exact ⟨r1 ++ r2, by rw [routeAll_cons, h2, h1]; simp⟩

lemma routeAll_wf {l : Exec P} (hl : l.WF) (ws : List (Σ j : P, G.Walk j r)) :
    (routeAll l ws).WF := by
  induction ws generalizing l with
  | nil => exact hl
  | cons w ws ih => exact ih (route_wf hl w.2)

lemma routeAll_onGraph {l : Exec P} (hl : l.OnGraph G) (ws : List (Σ j : P, G.Walk j r)) :
    (routeAll l ws).OnGraph G := by
  induction ws generalizing l with
  | nil => exact hl
  | cons w ws ih => exact ih (route_onGraph hl w.2)

lemma routeAll_procAt_new {l : Exec P} (ws : List (Σ j : P, G.Walk j r)) {i : ℕ} {x : P}
    (hi : l.length ≤ i) (h : (routeAll l ws).procAt i = some x) :
    ∃ w ∈ ws, x ∈ w.2.support := by
  induction ws generalizing l with
  | nil => exact absurd (Exec.lt_length_of_procAt h) (by simp [routeAll]; omega)
  | cons w ws ih =>
    rw [routeAll_cons] at h
    by_cases hi' : (route l w.2).length ≤ i
    · obtain ⟨w', hw', hx⟩ := ih hi' h
      exact ⟨w', List.mem_cons_of_mem _ hw', hx⟩
    · obtain ⟨rest, hr⟩ := routeAll_prefix (route l w.2) ws
      rw [hr, Exec.procAt_append_of_lt _ (by omega)] at h
      exact ⟨w, List.mem_cons_self, route_procAt_new w.2 hi h⟩

lemma routeAll_reach {l : Exec P} (hwf : l.WF) (ws : List (Σ j : P, G.Walk j r))
    {w : Σ j : P, G.Walk j r} (hw : w ∈ ws) {x y : ℕ}
    (hy : y < l.length) (hyj : l.procAt y = some w.1) (hxy : l.HBeq x y) :
    ∃ y', y' < (routeAll l ws).length ∧ (routeAll l ws).procAt y' = some r ∧
      (routeAll l ws).HBeq x y' := by
  induction ws generalizing l y with
  | nil => simp at hw
  | cons w₀ ws ih =>
    rw [routeAll_cons]
    obtain ⟨rest, hr⟩ := route_prefix l w₀.2
    rcases List.mem_cons.1 hw with rfl | hw
    · obtain ⟨y', hy', hyr, hxy'⟩ := route_reach hwf w.2 hy hyj hxy
      obtain ⟨rest', hr'⟩ := routeAll_prefix (route l w.2) ws
      refine ⟨y', ?_, ?_, ?_⟩
      · rw [hr']; simp; omega
      · rw [hr', Exec.procAt_append_of_lt _ hy']; exact hyr
      · rw [hr']; exact hxy'.append _
    · refine ih (route_wf hwf w₀.2) hw (y := y) ?_ ?_ ?_
      · rw [hr]; simp; omega
      · rw [hr, Exec.procAt_append_of_lt _ hy]; exact hyj
      · rw [hr]; exact hxy.append _

end RouteAll

/-- A computation event after which its process takes no step happened-before no event. -/
lemma not_hb_of_last {ex : Exec P} (hwf : ex.WF) {i : ℕ} {k : P} (hi : ex[i]? = some (.comp k))
    (hlast : ∀ j, i < j → ex.procAt j ≠ some k) (j : ℕ) : ¬ ex.HB i j := by
  intro h
  obtain ⟨x, hx, -⟩ := Relation.TransGen.head'_iff.1 h
  cases hx with
  | po h =>
    obtain ⟨h1, -, h3, -⟩ := Exec.prev_spec h
    exact hlast _ h1 (h3 ▸ Exec.procAt_of_get hi)
  | msg h =>
    obtain ⟨q, hq⟩ := hwf.recv_send h
    rw [hi] at hq
    cases hq

lemma getElem?_append_single (R : Exec P) (a : Act P) (j : ℕ) :
    (R ++ [a])[j]? = if j < R.length then R[j]? else if j = R.length then some a else none := by
  split_ifs with h1 h2
  · exact List.getElem?_append_left h1
  · subst h2; simp
  · rw [List.getElem?_eq_none]; simp; omega

lemma append_comp_wf {R : Exec P} (hR : R.WF) (r : P) : (R ++ [Act.comp r]).WF := by
  constructor
  · intro j p m h
    rw [getElem?_append_single] at h
    split_ifs at h with h1
    · exact hR.recv_lt h
    · simp at h
  · intro j p m h
    rw [getElem?_append_single] at h
    split_ifs at h with h1
    · obtain ⟨q, hq⟩ := hR.recv_send h
      exact ⟨q, by rw [Exec.getElem?_append_of_lt _ ((hR.recv_lt h).trans h1)]; exact hq⟩
    · simp at h
  · intro j j' p p' m h h'
    rw [getElem?_append_single] at h h'
    split_ifs at h h' with h1 h2 <;> first | exact hR.recv_unique h h' | simp at h | simp at h'

lemma append_comp_onGraph {G : SimpleGraph P} {R : Exec P} (hR : R.OnGraph G) (r : P) :
    (R ++ [Act.comp r]).OnGraph G := by
  intro j p q h
  rw [getElem?_append_single] at h
  split_ifs at h with h1
  · exact hR h
  · simp at h

/-- The gathering execution: forward tokens from all `j ∈ js` to `r` along walks avoiding `k`,
then let `r` take a final local step. -/
theorem gather {G : SimpleGraph P} {pre : Exec P} (hwf : pre.WF) (hG : pre.OnGraph G)
    {r : P} (ws : List (Σ j : P, G.Walk j r)) (pos : P → ℕ)
    (hpos : ∀ w ∈ ws, pos w.1 < pre.length ∧ pre.procAt (pos w.1) = some w.1) :
    (routeAll pre ws ++ [Act.comp r]).WF ∧ (routeAll pre ws ++ [Act.comp r]).OnGraph G ∧
      (∃ rest, routeAll pre ws ++ [Act.comp r] = pre ++ rest) ∧
      (∀ w ∈ ws, (routeAll pre ws ++ [Act.comp r]).HB (pos w.1) (routeAll pre ws).length) ∧
      (routeAll pre ws ++ [Act.comp r])[(routeAll pre ws).length]? = some (Act.comp r) ∧
      (∀ i x, pre.length ≤ i → (routeAll pre ws ++ [Act.comp r]).procAt i = some x →
        x = r ∨ ∃ w ∈ ws, x ∈ w.2.support) := by
  have hRwf := routeAll_wf hwf ws
  have hlast : (routeAll pre ws ++ [Act.comp r])[(routeAll pre ws).length]? = some (Act.comp r) := by
    simp
  refine ⟨append_comp_wf hRwf r, append_comp_onGraph (routeAll_onGraph hG ws) r, ?_, ?_, hlast,
    ?_⟩
  · obtain ⟨rest, hr⟩ := routeAll_prefix pre ws
    exact ⟨rest ++ [Act.comp r], by simp [hr]⟩
  · intro w hw
    obtain ⟨hp1, hp2⟩ := hpos w hw
    obtain ⟨y, hy, hyr, hxy⟩ := routeAll_reach hwf ws hw hp1 hp2 (Exec.HBeq.refl _)
    refine (hxy.append [Act.comp r]).trans_hb (Exec.hb_of_lt hy ?_ (Exec.procAt_of_get hlast))
    rw [Exec.procAt_append_of_lt _ hy]; exact hyr
  · intro i x hi h
    by_cases hiR : i < (routeAll pre ws).length
    · rw [Exec.procAt_append_of_lt _ hiR] at h
      exact Or.inr (routeAll_procAt_new ws hi h)
    · obtain ⟨a, ha, rfl⟩ := Exec.procAt_eq_some.1 h
      rw [getElem?_append_single] at ha
      split_ifs at ha with h1
      cases ha
      exact Or.inl rfl

end Podc.DelayedTimestamps
