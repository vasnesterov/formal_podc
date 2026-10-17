import Papers.PODC2013.CongestedCliqueRouting.Knowledge
import Podc.Foundations.Combinatorics.Matrix.Birkhoff
import Papers.PODC2013.CongestedCliqueRouting.Assign

/-!
# Communication primitives on a clique of `s²` nodes

The node set `V` is identified with `Fin s × Fin s` via `e`: node `node e a b` is member `b` of
group `a` (the groups are the sets `W` of size `√n` of the paper). Packets have three slots.

* `ga1`/`ga2`: every node announces a vector `x v : Fin s → ℕ` to all members of its group, in two
  rounds (a fixed, data-independent pattern; used for Steps 1/3 of Algorithm 2, Corollary 3.5 and
  Corollary 3.4).
* `bc`: node `(a, j)` announces one number to all nodes.
* `c33a`/`c33b`: Corollary 3.3 — two-round delivery inside every group, through intermediate nodes
  of the whole clique, when the routing pattern is known inside the group. Every message carries
  its target member and a tag.
* `scatter`: a node holding at most `s` messages of every class `x` sends them, one per edge, to
  the members of group `x`.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

section Matrices

variable {α β ι : Type*} [Fintype α] [DecidableEq α] [Fintype β] [Fintype ι]

open Classical in
/-- A split of `A` into `|ι|` parts with row and column sums `≤ D` (König), if possible. -/
noncomputable def splitParts (ι : Type*) [Fintype ι] (A : α → α → ℕ) (D : ℕ) :
    ι → α → α → ℕ :=
  if h : (∀ i, ∑ j, A i j ≤ Fintype.card ι * D) ∧ (∀ j, ∑ i, A i j ≤ Fintype.card ι * D) then
    Classical.choose (Matrix.exists_split_parts A D h.1 h.2)
  else 0

lemma splitParts_spec {A : α → α → ℕ} {D : ℕ}
    (hr : ∀ i, ∑ j, A i j ≤ Fintype.card ι * D) (hc : ∀ j, ∑ i, A i j ≤ Fintype.card ι * D) :
    (∀ i j, ∑ x, splitParts ι A D x i j = A i j) ∧
      (∀ x i, ∑ j, splitParts ι A D x i j ≤ D) ∧ (∀ x j, ∑ i, splitParts ι A D x i j ≤ D) := by
  unfold splitParts
  rw [dif_pos ⟨hr, hc⟩]
  exact Classical.choose_spec (Matrix.exists_split_parts A D hr hc)

open Classical in
/-- A solution of the transportation problem with row sums `r` and column sums `c`. -/
noncomputable def transportOf (r : α → ℕ) (c : β → ℕ) : α → β → ℕ :=
  if h : ∑ i, r i = ∑ j, c j then Classical.choose (Matrix.exists_transport r c h) else 0

lemma transportOf_spec {r : α → ℕ} {c : β → ℕ} (h : ∑ i, r i = ∑ j, c j) :
    (∀ i, ∑ j, transportOf r c i j = r i) ∧ (∀ j, ∑ i, transportOf r c i j = c j) := by
  unfold transportOf
  rw [dif_pos h]
  exact Classical.choose_spec (Matrix.exists_transport r c h)

end Matrices

variable {V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] {s : ℕ}

section Grid

variable (e : V ≃ Fin s × Fin s)

/-- The group of a node. -/
def grp (v : V) : Fin s := (e v).1
/-- The index of a node inside its group. -/
def mem (v : V) : Fin s := (e v).2
/-- Member `b` of group `a`. -/
def node (a b : Fin s) : V := e.symm (a, b)

@[simp] lemma grp_node (a b : Fin s) : grp e (node e a b) = a := by simp [grp, node]
@[simp] lemma mem_node (a b : Fin s) : mem e (node e a b) = b := by simp [mem, node]
@[simp] lemma node_grp_mem (v : V) : node e (grp e v) (mem e v) = v := by simp [grp, mem, node]

lemma eq_node_iff {v : V} {a b : Fin s} : v = node e a b ↔ grp e v = a ∧ mem e v = b := by
  constructor
  · rintro rfl; simp
  · rintro ⟨rfl, rfl⟩; simp

lemma card_V (e : V ≃ Fin s × Fin s) : Fintype.card V = s * s := by
  rw [Fintype.card_congr e]; simp

/-- Sum over all nodes as a double sum over groups and members. -/
lemma sum_V {β : Type*} [AddCommMonoid β] (f : V → β) :
    ∑ v, f v = ∑ a, ∑ b, f (node e a b) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv e _ _ (fun v => by simp [node])).trans rfl

end Grid

/-! ### Packets -/

/-- The empty packet. -/
def pkt0 : Packet M 3 := fun _ => none
/-- A packet carrying one number. -/
def pNum (k : ℕ) : Packet M 3 := ![some (Item.num k), none, none]
/-- A packet carrying one message. -/
def pMsg (m : M) : Packet M 3 := ![some (Item.msg m), none, none]
/-- A packet carrying a message and a tag. -/
def pMsgNum (m : M) (k : ℕ) : Packet M 3 := ![some (Item.msg m), some (Item.num k), none]
/-- A packet carrying a message, a target member and a tag. -/
def pMsg3 (m : M) (y k : ℕ) : Packet M 3 :=
  ![some (Item.msg m), some (Item.num y), some (Item.num k)]

/-- The number in slot `0` (or `0`). -/
def numAt (p : Packet M 3) : ℕ :=
  match p 0 with
  | some (Item.num k) => k
  | _ => 0

@[simp] lemma numAt_pNum (k : ℕ) : numAt (pNum k : Packet M 3) = k := by
  simp [numAt, pNum]

@[simp] lemma msgsOf_pkt0 : msgsOf (pkt0 : Packet M 3) = ∅ := by
  ext m; simp [mem_msgsOf, pkt0]

@[simp] lemma msgsOf_pNum (k : ℕ) : msgsOf (pNum k : Packet M 3) = ∅ := by
  ext m; simp only [mem_msgsOf, notMem_empty, iff_false, not_exists]
  intro i; fin_cases i <;> simp [pNum]

@[simp] lemma msgsOf_pMsg (m : M) : msgsOf (pMsg m : Packet M 3) = {m} := by
  ext m'; simp only [mem_msgsOf, mem_singleton]
  constructor
  · rintro ⟨i, hi⟩; fin_cases i <;> simp_all [pMsg]
  · rintro rfl; exact ⟨0, by simp [pMsg]⟩

@[simp] lemma msgsOf_pMsgNum (m : M) (k : ℕ) : msgsOf (pMsgNum m k : Packet M 3) = {m} := by
  ext m'; simp only [mem_msgsOf, mem_singleton]
  constructor
  · rintro ⟨i, hi⟩; fin_cases i <;> simp_all [pMsgNum]
  · rintro rfl; exact ⟨0, by simp [pMsgNum]⟩

@[simp] lemma msgsOf_pMsg3 (m : M) (y k : ℕ) : msgsOf (pMsg3 m y k : Packet M 3) = {m} := by
  ext m'; simp only [mem_msgsOf, mem_singleton]
  constructor
  · rintro ⟨i, hi⟩; fin_cases i <;> simp_all [pMsg3]
  · rintro rfl; exact ⟨0, by simp [pMsg3]⟩

lemma nums_pNum {k k' : ℕ} {i : Fin 3} (h : (pNum k : Packet M 3) i = some (Item.num k')) :
    k' = k := by
  fin_cases i <;> simp_all [pNum]

lemma nums_pMsg {m : M} {k' : ℕ} {i : Fin 3} (h : (pMsg m : Packet M 3) i = some (Item.num k')) :
    False := by
  fin_cases i <;> simp_all [pMsg]

lemma nums_pMsgNum {m : M} {k k' : ℕ} {i : Fin 3}
    (h : (pMsgNum m k : Packet M 3) i = some (Item.num k')) : k' = k := by
  fin_cases i <;> simp_all [pMsgNum]

lemma nums_pMsg3 {m : M} {y k k' : ℕ} {i : Fin 3}
    (h : (pMsg3 m y k : Packet M 3) i = some (Item.num k')) : k' = y ∨ k' = k := by
  fin_cases i <;> simp_all [pMsg3]

/-! ### Received messages of a round -/

/-- Messages received by `v` from the packet vector `P`. -/
def rcvd {B : ℕ} (P : V → V → Packet M B) (v : V) : Finset M :=
  univ.biUnion fun u => msgsOf (P u v)

lemma mem_rcvd {B : ℕ} {P : V → V → Packet M B} {v : V} {m : M} :
    m ∈ rcvd P v ↔ ∃ u, m ∈ msgsOf (P u v) := by
  simp [rcvd]

lemma card_rcvd_le {B : ℕ} {P : V → V → Packet M B} {v : V}
    (h : ∀ u, (msgsOf (P u v)).card ≤ 1) : (rcvd P v).card ≤ Fintype.card V := by
  calc (rcvd P v).card ≤ ∑ u, (msgsOf (P u v)).card := card_biUnion_le
    _ ≤ ∑ _u : V, 1 := sum_le_sum fun u _ => h u
    _ = Fintype.card V := by simp

/-! ### Group announcement (two rounds) -/

section GA

variable (e : V ≃ Fin s × Fin s)

/-- Round 1: node `v` sends `x v j` to node `(j, mem v)`. -/
def ga1 (x : V → Fin s → ℕ) (v w : V) : Packet M 3 :=
  if mem e w = mem e v then pNum (x v (grp e w)) else pkt0

/-- Round 2: node `p` forwards to `w` what it received from member `mem p` of `w`'s group. -/
def ga2 (P : V → V → Packet M 3) (p w : V) : Packet M 3 :=
  P (node e (grp e w) (mem e p)) p

lemma ga2_ga1 (x : V → Fin s → ℕ) (j b : Fin s) (w : V) :
    ga2 e (ga1 e x) (node e j b) w = (pNum (x (node e (grp e w) b) j) : Packet M 3) := by
  simp [ga2, ga1]

lemma msgsOf_ga1 (x : V → Fin s → ℕ) (v w : V) : msgsOf (ga1 e x v w : Packet M 3) = ∅ := by
  unfold ga1; split_ifs <;> simp

lemma msgsOf_ga2_ga1 (x : V → Fin s → ℕ) (v w : V) :
    msgsOf (ga2 e (ga1 e x) v w : Packet M 3) = ∅ := by
  simp [ga2, msgsOf_ga1]

lemma nums_ga1 {x : V → Fin s → ℕ} {v w : V} {i : Fin 3} {k : ℕ}
    (h : (ga1 e x v w : Packet M 3) i = some (Item.num k)) : ∃ j, k = x v j := by
  unfold ga1 at h
  split_ifs at h
  · exact ⟨_, nums_pNum h⟩
  · simp [pkt0] at h

lemma nums_ga2_ga1 {x : V → Fin s → ℕ} {v w : V} {i : Fin 3} {k : ℕ}
    (h : (ga2 e (ga1 e x) v w : Packet M 3) i = some (Item.num k)) : ∃ u j, k = x u j := by
  unfold ga2 at h
  obtain ⟨j, hj⟩ := nums_ga1 e h
  exact ⟨_, j, hj⟩

/-- Broadcast: node `(a, j)` sends `T a j` to everybody. -/
def bc (T : Fin s → Fin s → ℕ) (v _w : V) : Packet M 3 := pNum (T (grp e v) (mem e v))

end GA

/-! ### Corollary 3.3: two-round routing inside the groups -/

section Cor33

variable (e : V ≃ Fin s × Fin s)

/-- Round 1: send the message `m` with target member `y` and tag `k` to the intermediate node. -/
def c33a : Option (M × ℕ × ℕ) → Packet M 3
  | some (m, y, k) => pMsg3 m y k
  | none => pkt0

/-- The (message, tag) pairs in a round-1 packet that are meant for `w`. -/
def parse3 (p : Packet M 3) (w : V) : Finset (M × ℕ) :=
  match p 0, p 1, p 2 with
  | some (Item.msg m), some (Item.num y), some (Item.num k) =>
      if y = (mem e w : ℕ) then {(m, k)} else ∅
  | _, _, _ => ∅

/-- Candidates an intermediate node may forward to `w`: messages from `w`'s group meant for
`w`. -/
def cand (recv : V → Packet M 3) (w : V) : Finset (M × ℕ) :=
  (univ.filter fun u => grp e u = grp e w).biUnion fun u => parse3 e (recv u) w

/-- Round 2: the intermediate node forwards (message, tag) to its target. -/
noncomputable def c33b (recv : V → Packet M 3) (w : V) : Packet M 3 :=
  match pick (cand e recv w) with
  | some (m, k) => pMsgNum m k
  | none => pkt0

/-- Decoding a round-2 packet. -/
def decode2 (p : Packet M 3) : Finset (M × ℕ) :=
  match p 0, p 1 with
  | some (Item.msg m), some (Item.num k) => {(m, k)}
  | _, _ => ∅

/-- All (message, tag) pairs received by `w` in round 2. -/
def tagged (P : V → V → Packet M 3) (w : V) : Finset (M × ℕ) :=
  univ.biUnion fun c => decode2 (P c w)

lemma mem_parse3 {p : Packet M 3} {w : V} {m : M} {k : ℕ} :
    (m, k) ∈ parse3 e p w ↔ p 0 = some (Item.msg m) ∧ p 1 = some (Item.num (mem e w : ℕ)) ∧
      p 2 = some (Item.num k) := by
  unfold parse3
  split
  · rename_i m' y k' h0 h1 h2
    rw [h0, h1, h2]
    split_ifs with hy
    · subst hy; simp [eq_comm]
    · simp only [notMem_empty, false_iff, Option.some.injEq, Item.msg.injEq, Item.num.injEq]
      rintro ⟨-, h, -⟩; exact hy h
  · rename_i hne
    simp only [notMem_empty, false_iff]
    rintro ⟨h0, h1, h2⟩
    exact hne _ _ _ h0 h1 h2

lemma parse3_c33a (r : Option (M × ℕ × ℕ)) (w : V) :
    parse3 e (c33a r) w =
      match r with
      | some (m, y, k) => if y = (mem e w : ℕ) then {(m, k)} else ∅
      | none => ∅ := by
  rcases r with _ | ⟨m, y, k⟩
  · simp [c33a, parse3, pkt0]
  · simp [c33a, parse3, pMsg3]

lemma mem_parse3_c33a {r : Option (M × ℕ × ℕ)} {w : V} {m : M} {k : ℕ} :
    (m, k) ∈ parse3 e (c33a r) w ↔ r = some (m, (mem e w : ℕ), k) := by
  rw [parse3_c33a]
  rcases r with _ | ⟨m', y, k'⟩
  · simp
  · by_cases hy : y = (mem e w : ℕ)
    · subst hy; simp [eq_comm]
    · simp [hy]

@[simp] lemma decode2_pMsgNum (m : M) (k : ℕ) : decode2 (pMsgNum m k : Packet M 3) = {(m, k)} := by
  simp [decode2, pMsgNum]

@[simp] lemma decode2_pkt0 : decode2 (pkt0 : Packet M 3) = ∅ := by
  simp [decode2, pkt0]

lemma msgsOf_c33a (r : Option (M × ℕ × ℕ)) :
    msgsOf (c33a r) ⊆ (match r with | some (m, _, _) => {m} | none => ∅) := by
  rcases r with _ | ⟨m, y, k⟩ <;> simp [c33a]

/-- Uniqueness hypothesis of Corollary 3.3: for every intermediate node `c` and target `w`,
at most one member of `w`'s group sends `c` a message meant for `w`. -/
def C33Unique (rel : V → V → Option (M × ℕ × ℕ)) : Prop :=
  ∀ c u u' (m m' : M) (y k k' : ℕ), grp e u = grp e u' →
    rel u c = some (m, y, k) → rel u' c = some (m', y, k') → u = u'

lemma cand_c33a_eq {rel : V → V → Option (M × ℕ × ℕ)} (hu : C33Unique e rel) {c u w : V}
    {m : M} {k : ℕ} (hgrp : grp e u = grp e w) (hr : rel u c = some (m, (mem e w : ℕ), k)) :
    cand e (fun u' => c33a (rel u' c)) w = {(m, k)} := by
  ext ⟨m', k'⟩
  simp only [cand, mem_biUnion, mem_filter, mem_univ, true_and, mem_parse3_c33a,
    mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨u', hu', hr'⟩
    have := hu c u u' m m' _ k k' (hgrp.trans hu'.symm) hr hr'
    subst this
    rw [hr] at hr'
    simp only [Option.some.injEq, Prod.mk.injEq] at hr'
    exact ⟨hr'.1.symm, hr'.2.2.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨u, hgrp, hr⟩

lemma c33b_c33a_eq {rel : V → V → Option (M × ℕ × ℕ)} (hu : C33Unique e rel) {c u w : V}
    {m : M} {k : ℕ} (hgrp : grp e u = grp e w) (hr : rel u c = some (m, (mem e w : ℕ), k)) :
    c33b e (fun u' => c33a (rel u' c)) w = pMsgNum m k := by
  simp [c33b, cand_c33a_eq e hu hgrp hr, pick_singleton]

lemma c33b_cases (recv : V → Packet M 3) (w : V) :
    c33b e recv w = pkt0 ∨
      ∃ m k, (m, k) ∈ cand e recv w ∧ c33b e recv w = pMsgNum m k := by
  unfold c33b
  rcases h : pick (cand e recv w) with _ | ⟨m, k⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨m, k, pick_mem h, rfl⟩

/-- What `w` receives in round 2 of Corollary 3.3. -/
lemma mem_tagged_c33 {rel : V → V → Option (M × ℕ × ℕ)} (hu : C33Unique e rel) {w : V}
    {m : M} {k : ℕ} :
    (m, k) ∈ tagged (fun c w' => c33b e (fun u => c33a (rel u c)) w') w ↔
      ∃ u c, grp e u = grp e w ∧ rel u c = some (m, (mem e w : ℕ), k) := by
  constructor
  · intro h
    simp only [tagged, mem_biUnion, mem_univ, true_and] at h
    obtain ⟨c, hc⟩ := h
    rcases c33b_cases e (fun u => c33a (rel u c)) w with h0 | ⟨m', k', hmk, h1⟩
    · rw [h0, decode2_pkt0] at hc; simp at hc
    · rw [h1, decode2_pMsgNum, mem_singleton] at hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hc
      simp only [cand, mem_biUnion, mem_filter, mem_univ, true_and, mem_parse3_c33a] at hmk
      obtain ⟨u, hu1, hu2⟩ := hmk
      exact ⟨u, c, hu1, hu2⟩
  · rintro ⟨u, c, hgrp, hr⟩
    simp only [tagged, mem_biUnion, mem_univ, true_and]
    exact ⟨c, by rw [c33b_c33a_eq e hu hgrp hr]; simp⟩

lemma msgsOf_c33b {recv : V → Packet M 3} {w : V} {m : M}
    (h : m ∈ msgsOf (c33b e recv w)) : ∃ u, m ∈ msgsOf (recv u) := by
  rcases c33b_cases e recv w with h0 | ⟨m', k', hmk, h1⟩
  · rw [h0] at h; simp at h
  · rw [h1, msgsOf_pMsgNum, mem_singleton] at h
    subst h
    simp only [cand, mem_biUnion, mem_filter, mem_univ, true_and] at hmk
    obtain ⟨u, -, hu⟩ := hmk
    refine ⟨u, ?_⟩
    rw [mem_msgsOf]
    exact ⟨0, ((mem_parse3 e).1 hu).1⟩

lemma card_msgsOf_c33b_le (recv : V → Packet M 3) (w : V) : (msgsOf (c33b e recv w)).card ≤ 1 := by
  rcases c33b_cases e recv w with h0 | ⟨m', k', -, h1⟩
  · rw [h0]; simp
  · rw [h1]; simp

lemma nums_c33b {recv : V → Packet M 3} {w : V} {i : Fin 3} {k : ℕ}
    (h : c33b e recv w i = some (Item.num k)) : ∃ u, recv u 2 = some (Item.num k) := by
  rcases c33b_cases e recv w with h0 | ⟨m', k', hmk, h1⟩
  · rw [h0] at h; simp [pkt0] at h
  · rw [h1] at h
    have := nums_pMsgNum h
    subst this
    simp only [cand, mem_biUnion, mem_filter, mem_univ, true_and] at hmk
    obtain ⟨u, -, hu⟩ := hmk
    exact ⟨u, ((mem_parse3 e).1 hu).2.2⟩

/-- Relaying through intermediate nodes: node with messages `H`, target members `yy`, tags `tag`
and capacities `cap y c` (how many messages for member `y` go through intermediate node `c`)
sends to `c` the message assigned to it. -/
noncomputable def relayOf [Nonempty V] (H : Finset M) (yy : M → Fin s) (tag : M → ℕ)
    (cap : Fin s → V → ℕ) (c : V) : Option (M × ℕ × ℕ) :=
  (pick (H.filter fun m => assign H yy cap m = c)).map fun m => (m, (yy m : ℕ), tag m)

variable [Nonempty V] {H : Finset M} {yy : M → Fin s} {tag : M → ℕ} {cap : Fin s → V → ℕ}

lemma relayOf_some (hcap : ∀ y, (H.filter fun m => yy m = y).card ≤ ∑ c, cap y c)
    (hrow : ∀ c, ∑ y, cap y c ≤ 1) {m : M} (hm : m ∈ H) :
    relayOf H yy tag cap (assign H yy cap m) = some (m, (yy m : ℕ), tag m) := by
  unfold relayOf
  have hcard : (H.filter fun m' => assign H yy cap m' = assign H yy cap m).card ≤ 1 := by
    rw [card_filter_eq_sum_fiber _ (fun m' => assign H yy cap m') yy]
    refine le_trans ?_ (hrow (assign H yy cap m))
    refine sum_le_sum fun y _ => ?_
    have := assign_le hcap y (assign H yy cap m)
    refine le_trans (card_le_card fun x hx => ?_) this
    simp only [mem_filter] at hx ⊢
    exact ⟨hx.1, hx.2.2, hx.2.1⟩
  rw [pick_eq_some_of_card_le_one (a := m) hcard (by simp [hm])]
  rfl

lemma relayOf_spec (hcap : ∀ y, (H.filter fun m => yy m = y).card ≤ ∑ c, cap y c)
    {c : V} {m : M} {y k : ℕ} (h : relayOf H yy tag cap c = some (m, y, k)) :
    m ∈ H ∧ y = (yy m : ℕ) ∧ k = tag m ∧ 1 ≤ cap (yy m) c := by
  unfold relayOf at h
  rcases hp : pick (H.filter fun m => assign H yy cap m = c) with _ | m'
  · rw [hp] at h; simp at h
  · rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hm := pick_mem hp
    simp only [mem_filter] at hm
    refine ⟨hm.1, rfl, rfl, ?_⟩
    have := assign_le hcap (yy m') c
    refine le_trans ?_ this
    exact card_pos.2 ⟨m', by simp [hm.1, hm.2]⟩

lemma msgsOf_c33a_relayOf {c : V} {m : M} (h : m ∈ msgsOf (c33a (relayOf H yy tag cap c))) :
    m ∈ H := by
  have := msgsOf_c33a (relayOf H yy tag cap c) h
  rcases hr : relayOf H yy tag cap c with _ | ⟨m', y, k⟩
  · rw [hr] at this; simp at this
  · rw [hr] at this
    simp only [mem_singleton] at this
    subst this
    unfold relayOf at hr
    rcases hp : pick (H.filter fun m => assign H yy cap m = c) with _ | m''
    · rw [hp] at hr; simp at hr
    · rw [hp] at hr
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      rw [← hr.1]
      exact (mem_filter.1 (pick_mem hp)).1

end Cor33

/-! ### Scatter (one round) -/

section Scatter

variable (e : V ≃ Fin s × Fin s) [NeZero s] {β : Type*} [DecidableEq β]

/-- Slot of an element of `H` inside its class. -/
noncomputable def slot (H : Finset β) (cls : β → ℕ) : β → Fin s :=
  assign H cls fun _ _ => 1

/-- Node holding `H` (classes `cls`, messages `toM`) sends to `z` the element of class `grp z`
with slot `mem z`. -/
noncomputable def scatter (H : Finset β) (cls : β → ℕ) (toM : β → M) (z : V) : Packet M 3 :=
  match pick (H.filter fun b => cls b = (grp e z : ℕ) ∧ slot H cls b = mem e z) with
  | some b => pMsg (toM b)
  | none => pkt0

lemma scatter_eq {H : Finset β} {cls : β → ℕ} {toM : β → M}
    (hcap : ∀ k, (H.filter fun b => cls b = k).card ≤ s) {b : β} (hb : b ∈ H)
    (hlt : cls b < s) :
    scatter e H cls toM (node e ⟨cls b, hlt⟩ (slot H cls b)) = pMsg (toM b) := by
  unfold scatter
  have hcap' : ∀ k, (H.filter fun b => cls b = k).card ≤ ∑ _p : Fin s, 1 := by
    intro k; simpa using hcap k
  have hcard : (H.filter fun b' => cls b' = (grp e (node e ⟨cls b, hlt⟩ (slot H cls b)) : ℕ) ∧
      slot H cls b' = mem e (node e ⟨cls b, hlt⟩ (slot H cls b))).card ≤ 1 := by
    simp only [grp_node, mem_node]
    exact assign_le hcap' (cls b) (slot H cls b)
  rw [pick_eq_some_of_card_le_one (a := b) hcard (by simp [hb])]

lemma msgsOf_scatter {H : Finset β} {cls : β → ℕ} {toM : β → M} {z : V} {m : M}
    (h : m ∈ msgsOf (scatter e H cls toM z)) :
    ∃ b ∈ H, toM b = m ∧ cls b = (grp e z : ℕ) ∧ slot H cls b = mem e z := by
  unfold scatter at h
  rcases hp : pick (H.filter fun b => cls b = (grp e z : ℕ) ∧ slot H cls b = mem e z)
    with _ | b
  · rw [hp] at h; simp at h
  · rw [hp] at h
    simp only [msgsOf_pMsg, mem_singleton] at h
    have := pick_mem hp
    simp only [mem_filter] at this
    exact ⟨b, this.1, h.symm, this.2.1, this.2.2⟩

lemma card_msgsOf_scatter_le (H : Finset β) (cls : β → ℕ) (toM : β → M) (z : V) :
    (msgsOf (scatter e H cls toM z)).card ≤ 1 := by
  unfold scatter
  cases pick (H.filter fun b => cls b = (grp e z : ℕ) ∧ slot H cls b = mem e z) <;> simp

lemma nums_scatter {H : Finset β} {cls : β → ℕ} {toM : β → M} {z : V} {i : Fin 3} {k : ℕ}
    (h : scatter e H cls toM z i = some (Item.num k)) : False := by
  unfold scatter at h
  revert h
  cases pick (H.filter fun b => cls b = (grp e z : ℕ) ∧ slot H cls b = mem e z) with
  | none => simp [pkt0]
  | some b => exact fun h => nums_pMsg h

end Scatter

end CongestedCliqueRouting
