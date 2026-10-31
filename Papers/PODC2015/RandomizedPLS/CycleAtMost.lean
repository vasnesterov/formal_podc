import Papers.PODC2015.RandomizedPLS.Biconnectivity

/-!
# Longest cycle, `cycle-at-most-c`: lower bounds of Theorem 5.6

`G = Chain.G m c` (Figure 3a): `m` disjoint `c`-cycles `B_q = ((q,0), (q,1), …, (q,c-1))`,
consecutive ones joined by the edge `{(q,0), (q+1,0)}`; `n = m·c` nodes, identities
`q·c + t`. (The paper allows a last cycle with fewer nodes so that `n` need not be a multiple
of `c`; we take `n = m·c`.) Port numbers are consistently ordered: `(q,t)` has its successor
`(q,t+1)` on port `0` and its predecessor on port `1`.

* `cycleAtMost_G`: every simple cycle of `G` has at most `c` nodes. The joining edges are bridges,
  so a cycle never uses them and stays inside one `B_q`.
* The copies are the edges `H_q = {(q,1), (q,2)}`, `q < m` (`r = m = n/c`).
* Crossing `H_i` and `H_j` creates the cycle `(i,2) … (i,c-1) (i,0) (i,1) (j,2) … (j,0) (j,1)` with
  `2c` nodes (`not_cycleAtMost_cross`); the crossing stays connected.
* `thm_5_6_det`, `thm_5_6_rand`: Theorem 5.6 (lower bounds).
-/

namespace Podc.RandomizedPLS

open Classical

variable {S : Type}

/-- `cycle-at-most-k` (Section 5.3): every simple cycle has at most `k` nodes. -/
def CycleAtMost (k : ℕ) (c : Config S) : Prop :=
  ∀ v, ∀ p : c.graph.Walk v v, p.IsCycle → p.length ≤ k

namespace Chain

/-- Adjacency on a `c`-cycle `0, …, c-1`. -/
def cyc (c s t : ℕ) : Prop :=
  s ≠ t ∧ (s + 1 = t ∨ t + 1 = s ∨ (s = 0 ∧ t + 1 = c) ∨ (t = 0 ∧ s + 1 = c))

/-- Adjacency of the chain of cycles. -/
def chAdj {m c : ℕ} (x y : Fin m × Fin c) : Prop :=
  (x.1 = y.1 ∧ cyc c x.2.val y.2.val) ∨
    (x.2.val = 0 ∧ y.2.val = 0 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val))

/-- The successor on a `c`-cycle. -/
def nxt {c : ℕ} (t : Fin c) : Fin c :=
  ⟨if t.val + 1 = c then 0 else t.val + 1, by split_ifs <;> omega⟩

/-- The predecessor on a `c`-cycle. -/
def prv {c : ℕ} (t : Fin c) : Fin c :=
  ⟨if t.val = 0 then c - 1 else t.val - 1, by split_ifs <;> omega⟩

lemma nxt_val {c : ℕ} (t : Fin c) : (nxt t).val = if t.val + 1 = c then 0 else t.val + 1 := rfl

lemma prv_val {c : ℕ} (t : Fin c) : (prv t).val = if t.val = 0 then c - 1 else t.val - 1 := rfl

/-- The first ports of `(q, t)`: its successor, then its predecessor on the cycle `B_q`. -/
def front (m c : ℕ) (x : Fin m × Fin c) : List (Fin m × Fin c) :=
  if 3 ≤ c then [(x.1, nxt x.2), (x.1, prv x.2)] else []

lemma front_spec {m c : ℕ} (x w : Fin m × Fin c) (hw : w ∈ front m c x) : chAdj x w := by
  unfold front at hw
  have := x.2.2
  split_ifs at hw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> left <;> refine ⟨rfl, ?_⟩ <;> unfold cyc <;>
      simp only [nxt_val, prv_val] <;> split_ifs <;> omega
  · simp at hw

lemma front_nodup {m c : ℕ} (x : Fin m × Fin c) : (front m c x).Nodup := by
  unfold front
  have := x.2.2
  split_ifs
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      and_true, Prod.mk.injEq, true_and, Fin.ext_iff, nxt_val, prv_val, not_false_eq_true]
    split_ifs <;> omega
  · simp

lemma chAdj_symm {m c : ℕ} (x y : Fin m × Fin c) (h : chAdj x y) : chAdj y x := by
  unfold chAdj cyc at *
  rcases h with ⟨h1, h2⟩ | h
  · exact Or.inl ⟨h1.symm, by omega⟩
  · exact Or.inr (by omega)

lemma chAdj_irrefl {m c : ℕ} (x : Fin m × Fin c) : ¬ chAdj x x := by
  unfold chAdj cyc; omega

/-- The chain of `m` cycles of `c` nodes (Figure 3a). -/
@[reducible] noncomputable def G (m c : ℕ) : Config ℕ :=
  mkConfig (fun x y : Fin m × Fin c => chAdj x y) chAdj_symm chAdj_irrefl (front m c)
    front_spec front_nodup (fun x => x.1.val * c + x.2.val)

lemma G_adj {m c : ℕ} (x y : Fin m × Fin c) : (G m c).graph.Adj x y ↔ chAdj x y :=
  mkConfig_adj x y

/-- The node `(q, 1 + b)`. -/
def e {m c : ℕ} (hc : 3 ≤ c) (q : Fin m) (b : Bool) : Fin m × Fin c :=
  (q, ⟨1 + b.toNat, by cases b <;> simp <;> omega⟩)

lemma port_e {m c : ℕ} (hc : 3 ≤ c) (q : Fin m) (b : Bool) :
    (G m c).port (e hc q b) (e hc q !b) = b.toNat := by
  have hf : ∀ x, front m c x = [(x.1, nxt x.2), (x.1, prv x.2)] := fun x => by
    unfold front; rw [ite_eq_left hc]
  cases b
  · have h2 : e hc q true = ((e hc q false).1, nxt (e hc q false).2) :=
      Prod.ext rfl (Fin.ext (by simp [e, nxt_val]; omega))
    have hmem : e hc q (!false) ∈ front m c (e hc q false) := by
      rw [hf, Bool.not_false, h2]; simp
    refine (mkConfig_port (st := fun x : Fin m × Fin c => x.1.val * c + x.2.val) hmem).trans ?_
    rw [hf, Bool.not_false, h2, List.idxOf_cons_self]
    rfl
  · have h1 : e hc q false = ((e hc q true).1, prv (e hc q true).2) :=
      Prod.ext rfl (Fin.ext (by simp [e, prv_val]))
    have hne : ((e hc q true).1, nxt (e hc q true).2) ≠ ((e hc q true).1, prv (e hc q true).2) := by
      intro h
      have := congrArg (fun p => p.2.val) h
      simp only [nxt_val, prv_val, e, Bool.toNat_true] at this
      split_ifs at this <;> omega
    have hmem : e hc q (!true) ∈ front m c (e hc q true) := by
      rw [hf, Bool.not_true, h1]; simp
    refine (mkConfig_port (st := fun x : Fin m × Fin c => x.1.val * c + x.2.val) hmem).trans ?_
    rw [hf, Bool.not_true, h1, List.idxOf_cons_ne _ hne, List.idxOf_cons_self]
    rfl

/-- The `m` copies `H_q = {(q,1), (q,2)}`. -/
@[reducible] noncomputable def K (m c : ℕ) (hc : 3 ≤ c) : Copies (G m c) m :=
  edgeCopies (G m c) m (e hc)
    (fun i h => by simp [e, Fin.ext_iff] at h)
    (fun i j a b hij h => hij (by simp only [e, Prod.mk.injEq] at h; exact h.1))
    (fun i j a b hij h => by
      have h' := (G_adj _ _).1 h
      simp only [chAdj, e] at h'
      cases a <;> cases b <;> simp at h' <;> omega)
    (fun i => (G_adj _ _).2 (Or.inl ⟨rfl, by simp only [cyc, e]; simp⟩))
    (fun i j b => by rw [port_e, port_e])

lemma K_s {m c : ℕ} (hc : 3 ≤ c) : (K m c hc).s = 1 := edgeCopies_s

variable {m c : ℕ} {hc : 3 ≤ c}

lemma isArc_iff {i j : Fin m} (x w : Fin m × Fin c) :
    (K m c hc).IsArc i j x w ↔ (x.1 = i ∨ x.1 = j) ∧ w.1 = x.1 ∧
      ((x.2.val = 1 ∧ w.2.val = 2) ∨ (x.2.val = 2 ∧ w.2.val = 1)) := by
  refine Iff.trans edgeCopies_isArc ?_
  constructor
  · rintro ⟨k, hk, b, rfl, rfl⟩
    rcases hk with rfl | rfl <;> cases b <;> simp [e]
  · rcases x with ⟨q, t⟩
    rcases w with ⟨q', t'⟩
    rintro ⟨hx, hw, h⟩
    simp only at hx hw h
    have key : ∀ b : Bool, t.val = 1 + b.toNat → t'.val = 1 + (!b).toNat →
        e hc q b = (q, t) ∧ e hc q (!b) = (q', t') := fun b h1 h2 =>
      ⟨Prod.ext rfl (Fin.ext h1.symm), Prod.ext hw.symm (Fin.ext h2.symm)⟩
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨q, hx, false, key false (by simp [h1]) (by simp [h2])⟩
    · exact ⟨q, hx, true, key true (by simp [h1]) (by simp [h2])⟩

/-- Uncrossed edges survive in the crossing. -/
lemma cross_adj_of {i j : Fin m} (hij : i ≠ j) {x y : Fin m × Fin c} (h : chAdj x y)
    (hn : ¬ (x.1 = y.1 ∧ ((x.2.val = 1 ∧ y.2.val = 2) ∨ (x.2.val = 2 ∧ y.2.val = 1)))) :
    ((K m c hc).cross i j hij).graph.Adj x y := by
  rw [Copies.cross_adj_iff]
  refine Or.inl ⟨(G_adj _ _).2 h, fun ha => hn ?_⟩
  rw [isArc_iff] at ha
  exact ⟨ha.2.1.symm, ha.2.2⟩

/-- The new edges `{(i,1), (j,2)}` and `{(j,1), (i,2)}` of the crossing. -/
lemma cross_adj_new {i j : Fin m} (hij : i ≠ j) (k k' : Fin m) (hk : (k = i ∧ k' = j) ∨
    (k = j ∧ k' = i)) : ((K m c hc).cross i j hij).graph.Adj (e hc k false) (e hc k' true) := by
  rw [Copies.cross_adj_iff]
  right
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [show e hc k' true = (K m c hc).emb k' true from rfl, (K m c hc).swap_emb_right hij]
    exact (edgeCopies_isArc).2 ⟨k, Or.inl rfl, false, rfl, rfl⟩
  · rw [show e hc k' true = (K m c hc).emb k' true from rfl, (K m c hc).swap_emb_left]
    exact (edgeCopies_isArc).2 ⟨k, Or.inr rfl, false, rfl, rfl⟩

/-- The potential used to show connectivity: walk along the cycle (never through the edge
`{1, 2}`) to `(q, 0)`, then along the joining edges to `(0, 0)`. -/
def pot (c : ℕ) {m : ℕ} (x : Fin m × Fin c) : ℕ ×ₗ ℕ :=
  toLex (x.1.val, if x.2.val = 0 then 0 else if x.2.val = 1 then 1 else c + 1 - x.2.val)

lemma descent (hm : 0 < m) (x : Fin m × Fin c) (hx : x ≠ (⟨0, hm⟩, ⟨0, by omega⟩)) :
    ∃ y, chAdj x y ∧
      ¬ (x.1 = y.1 ∧ ((x.2.val = 1 ∧ y.2.val = 2) ∨ (x.2.val = 2 ∧ y.2.val = 1))) ∧
      pot c y < pot c x := by
  rcases x with ⟨q, t⟩
  have hq := q.2
  have ht := t.2
  by_cases ht0 : t.val = 0
  · have hq0 : q.val ≠ 0 := fun h => hx (Prod.ext (Fin.ext h) (Fin.ext ht0))
    refine ⟨(⟨q.val - 1, by omega⟩, t), Or.inr ⟨ht0, ht0, Or.inr ?_⟩, ?_, ?_⟩
    · show q.val - 1 + 1 = q.val; omega
    · rintro ⟨h, -⟩
      have := congrArg Fin.val h
      dsimp only at this; omega
    · rw [pot, pot, Prod.Lex.toLex_lt_toLex]; left; show q.val - 1 < q.val; omega
  by_cases ht1 : t.val = 1
  · refine ⟨(q, ⟨0, by omega⟩), Or.inl ⟨rfl, ?_⟩, ?_, ?_⟩
    · show cyc c t.val 0; unfold cyc; omega
    · rintro ⟨-, h⟩; dsimp only at h; omega
    · rw [pot, pot, Prod.Lex.toLex_lt_toLex]; right; refine ⟨rfl, ?_⟩; dsimp only
      rw [ite_eq_left rfl, ite_eq_right ht0, ite_eq_left ht1]; omega
  by_cases htc : t.val + 1 = c
  · refine ⟨(q, ⟨0, by omega⟩), Or.inl ⟨rfl, ?_⟩, ?_, ?_⟩
    · show cyc c t.val 0; unfold cyc; omega
    · rintro ⟨-, h⟩; dsimp only at h; omega
    · rw [pot, pot, Prod.Lex.toLex_lt_toLex]; right; refine ⟨rfl, ?_⟩; dsimp only
      rw [ite_eq_left rfl, ite_eq_right ht0, ite_eq_right ht1]; omega
  · refine ⟨(q, ⟨t.val + 1, by omega⟩), Or.inl ⟨rfl, ?_⟩, ?_, ?_⟩
    · show cyc c t.val (t.val + 1); unfold cyc; omega
    · rintro ⟨-, h⟩; dsimp only at h; omega
    · rw [pot, pot, Prod.Lex.toLex_lt_toLex]; right; refine ⟨rfl, ?_⟩; dsimp only
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right ht0, ite_eq_right ht1]; omega

lemma fcon_G (hm : 0 < m) (hc : 3 ≤ c) : Fcon (G m c) :=
  connected_of_descent (G := (G m c).graph) ((⟨0, hm⟩, ⟨0, by omega⟩) : Fin m × Fin c) (pot c)
    (fun x hx => by
      obtain ⟨y, h1, -, h3⟩ := descent (hc := hc) hm x hx
      exact ⟨y, (G_adj _ _).2 h1, h3⟩)

lemma cross_connected (hm : 0 < m) {i j : Fin m} (hij : i ≠ j) :
    ((K m c hc).cross i j hij).Connected :=
  connected_of_descent (G := ((K m c hc).cross i j hij).graph)
    ((⟨0, hm⟩, ⟨0, by omega⟩) : Fin m × Fin c) (pot c)
    (fun x hx => by
      obtain ⟨y, h1, h2, h3⟩ := descent (hc := hc) hm x hx
      exact ⟨y, cross_adj_of hij h1 h2, h3⟩)

/-- The joining edges are bridges: no simple cycle uses an edge between two different cycles. -/
lemma same_block_of_mem_edges {u : Fin m × Fin c} {p : (G m c).graph.Walk u u} (hp : p.IsCycle)
    {x y : Fin m × Fin c} (he : s(x, y) ∈ p.edges) : x.1 = y.1 := by
  by_contra hne
  have hadj := (G_adj _ _).1 (p.adj_of_mem_edges he)
  have hj : x.2.val = 0 ∧ y.2.val = 0 ∧ (x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) := by
    rcases hadj with ⟨h, -⟩ | h
    · exact absurd h hne
    · exact h
  have hbr : (G m c).graph.IsBridge s(x, y) := by
    rw [SimpleGraph.isBridge_iff]
    intro hr
    let lo := min x.1.val y.1.val
    have hcl : ∀ a b, ((G m c).graph.deleteEdges {s(x, y)}).Adj a b →
        a ∈ {w : Fin m × Fin c | w.1.val ≤ lo} → b ∈ {w : Fin m × Fin c | w.1.val ≤ lo} := by
      intro a b hab ha
      rw [SimpleGraph.deleteEdges_adj, G_adj, Set.mem_singleton_iff] at hab
      simp only [Set.mem_ofPred_eq] at ha ⊢
      by_contra hb
      obtain ⟨h1 | h1, h2⟩ := hab
      · have : a.1.val = b.1.val := by rw [h1.1]
        omega
      · apply h2
        have hab1 : a.1.val + 1 = b.1.val := by omega
        rw [Sym2.eq_iff]
        rcases hj.2.2 with h | h
        · left; exact ⟨Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)),
            Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))⟩
        · right; exact ⟨Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)),
            Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))⟩
    rcases hj.2.2 with h | h
    · have := mem_of_reachable_of_closed _ hcl hr (by simp only [Set.mem_ofPred_eq, lo]; omega)
      simp only [Set.mem_ofPred_eq, lo] at this; omega
    · have := mem_of_reachable_of_closed _ hcl hr.symm (by simp only [Set.mem_ofPred_eq, lo]; omega)
      simp only [Set.mem_ofPred_eq, lo] at this; omega
  exact hbr.notMem_edges_of_isCycle hp he

end Chain

open Chain

/-- `cycle-at-most-c(G) = TRUE`: every simple cycle of the chain stays in one `c`-cycle. -/
lemma cycleAtMost_G (m c : ℕ) : CycleAtMost c (Chain.G m c) := by
  intro v p hp
  have hblock := support_eq_of_edges Prod.fst p (fun x y h => same_block_of_mem_edges hp h)
  have hnd := hp.support_nodup
  have h1 : (p.support.tail.map Prod.snd).Nodup := hnd.map_on fun a ha b hb h =>
    Prod.ext ((hblock a (List.mem_of_mem_tail ha)).trans
      (hblock b (List.mem_of_mem_tail hb)).symm) h
  have h2 := h1.length_le_card
  simp only [List.length_map, Fintype.card_fin, SimpleGraph.Walk.length_support,
    List.length_tail] at h2
  simpa using h2

/-- The crossings contain a simple cycle with `2c` nodes. -/
lemma not_cycleAtMost_cross {m c : ℕ} (hc : 3 ≤ c) {i j : Fin m} (hij : i ≠ j) :
    ¬ CycleAtMost c ((Chain.K m c hc).cross i j hij) := by
  intro h
  -- positions `2, 3, …, c-1, 0, 1` on a cycle
  let τ : ℕ → Fin c := fun k =>
    ⟨if k + 2 < c then k + 2 else if k + 2 - c < c then k + 2 - c else 0, by split_ifs <;> omega⟩
  let f : ℕ → Fin m × Fin c := fun k => if k < c then (i, τ k) else (j, τ (k - c))
  have hτ : ∀ k, (τ k).val = if k + 2 < c then k + 2 else if k + 2 - c < c then k + 2 - c else 0 :=
    fun k => rfl
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  obtain ⟨v, p, hp, hl⟩ := exists_cycle_of_seq
    (G := ((Chain.K m c hc).cross i j hij).graph) f (2 * c - 1) (by omega)
    (fun a ha b hb hab => by
      simp only [f] at hab
      split_ifs at hab <;> simp only [Prod.mk.injEq, Fin.ext_iff, hτ] at hab <;>
        split_ifs at hab <;> omega)
    (fun k hk => by
      by_cases h1 : k + 1 = c
      · have hf1 : f k = e hc i false := by
          simp only [f, e]; rw [ite_eq_left (by omega)]; congr 1; ext; simp [hτ]; split_ifs <;> omega
        have hf2 : f (k + 1) = e hc j true := by
          simp only [f, e]; rw [ite_eq_right (by omega)]; congr 1; ext; simp [hτ]; split_ifs <;> omega
        rw [hf1, hf2]
        exact cross_adj_new hij i j (Or.inl ⟨rfl, rfl⟩)
      · apply cross_adj_of hij
        · simp only [f]
          split_ifs with ha hb hb
          · left; refine ⟨rfl, ?_⟩; unfold cyc; rw [hτ, hτ]; split_ifs <;> omega
          · omega
          · omega
          · left; refine ⟨rfl, ?_⟩; unfold cyc; rw [hτ, hτ]; split_ifs <;> omega
        · simp only [f]
          split_ifs with ha hb hb <;> simp only [hτ] <;> split_ifs <;> omega)
    (by
      have hf1 : f (2 * c - 1) = e hc j false := by
        simp only [f, e]; rw [ite_eq_right (by omega)]; congr 1; ext; simp [hτ]; split_ifs <;> omega
      have hf2 : f 0 = e hc i true := by
        simp only [f, e]; rw [ite_eq_left (by omega)]; congr 1; ext; simp [hτ]; split_ifs <;> omega
      rw [hf1, hf2]
      exact cross_adj_new hij j i (Or.inr ⟨rfl, rfl⟩))
  have := h v p hp
  omega

/-- The crossings refute `(F_con, cycle-at-most-c)`. -/
lemma refuted_cross_cycleAtMost {m c : ℕ} (hc : 3 ≤ c) {i j : Fin m} (hij : i ≠ j) :
    Refuted Fcon (CycleAtMost c) ((Chain.K m c hc).cross i j hij) :=
  Or.inl ⟨cross_connected (Fin.pos i) hij, not_cycleAtMost_cross hc hij⟩

lemma chainG_state_injective (m c : ℕ) : Function.Injective (Chain.G m c).state := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  change a.val * c + b.val = a'.val * c + b'.val at h
  have hb := b.2; have hb' := b'.2
  have e : ∀ x y : ℕ, y < c → (x * c + y) / c = x := fun x y hy => by
    rw [add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hy, zero_add]
  have h1 : a.val = a'.val := by rw [← e a.val b.val hb, ← e a'.val b'.val hb', h]
  have h2 : b.val = b'.val := by rw [h1] at h; omega
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

lemma card_chainG (m c : ℕ) : Fintype.card (Chain.G m c).V = m * c := by
  change Fintype.card (Fin m × Fin c) = m * c
  simp

/-- **Theorem 5.6 of [BFP15]** (deterministic lower bound). Let `F` be any family containing the
connected configurations with distinct identities (e.g. `F_con`). For `c ≥ 3`, every proof-labeling
scheme for `(F, cycle-at-most-c)` whose labels on legal `n`-node configurations have at most
`κ(n)` bits satisfies `log₂ (n/c) ≤ 2 (κ(n) + 1)` for every multiple `n = m·c` of `c`, i.e.
`κ = Ω(log (n/c))`. -/
theorem thm_5_6_det {F : Config ℕ → Prop} (hFF : ∀ c, Fcon c → Function.Injective c.state → F c)
    {c : ℕ} {ver : Verifier ℕ} {prover : ∀ G : Config ℕ, G.V → List Bool}
    (h : IsPLS ver prover F (CycleAtMost c)) (κ : ℕ → ℕ)
    (hκ : LabelBound prover F (CycleAtMost c) (fun G => κ (Fintype.card G.V)))
    (hc : 3 ≤ c) (m : ℕ) (hm : 0 < m) :
    Real.logb 2 ((m * c) / c : ℕ) ≤ 2 * (κ (m * c) + 1) := by
  have hF := hFF _ (fcon_G hm hc) (chainG_state_injective m c)
  have hP := cycleAtMost_G m c
  have := thm_4_4_log h hF hP (Chain.K m c hc) (κ (m * c))
    (fun v => by simpa [card_chainG] using hκ _ hF hP v)
    (fun i j hij => (refuted_cross_cycleAtMost hc hij).mono hFF (chainG_state_injective m c))
  rw [Nat.mul_div_cancel _ (by omega)]
  simpa [Chain.K_s] using this

/-- **Theorem 5.6 of [BFP15]** (randomized lower bound, one-sided schemes). Let `F` be any family
containing the connected configurations with distinct identities. For `c ≥ 3`, every
one-sided RPLS for `(F, cycle-at-most-c)` whose certificates on legal `n`-node configurations
have at most `κ(n)` bits satisfies `log₂ (n/c) ≤ 2 · 2^(κ(n)+1)` for every multiple `n = m·c` of
`c`, i.e. `κ = Ω(log log (n/c))`. -/
theorem thm_5_6_rand {F : Config ℕ → Prop}
    (hFF : ∀ c, Fcon c → Function.Injective c.state → F c)
    {c : ℕ} {L : Type} {σ : RScheme ℕ L} {prover : ∀ G : Config ℕ, G.V → L}
    (h : IsOneSided σ prover F (CycleAtMost c)) (κ : ℕ → ℕ)
    (hκ : CertBound σ prover F (CycleAtMost c) (fun G => κ (Fintype.card G.V)))
    (hc : 3 ≤ c) (m : ℕ) (hm : 0 < m) :
    Real.logb 2 ((m * c) / c : ℕ) ≤ 2 * 2 ^ (κ (m * c) + 1) := by
  have hF := hFF _ (fcon_G hm hc) (chainG_state_injective m c)
  have hP := cycleAtMost_G m c
  have := prop_4_8_log h hF hP (Chain.K m c hc) (κ (m * c))
    (fun v ω i hi => by simpa [card_chainG] using hκ _ hF hP v ω i hi)
    (fun i j hij => (refuted_cross_cycleAtMost hc hij).mono hFF (chainG_state_injective m c))
  rw [Nat.mul_div_cancel _ (by omega)]
  simpa [Chain.K_s] using this

end Podc.RandomizedPLS
