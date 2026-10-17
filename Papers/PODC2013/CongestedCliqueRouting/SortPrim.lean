import Papers.PODC2013.CongestedCliqueRouting.Compose
import Papers.PODC2013.CongestedCliqueRouting.SquareMain

/-!
# Communication primitives for sorting (packets given by lists)

* `rr1`/`rr2`: Corollary 3.3 with an arbitrary, *known* routing pattern: in round 1 every node
  sends each of its keys `x`, together with (the number of) its target `tg x`, to an intermediate
  node `via x`; in round 2 the intermediate nodes forward the keys to their targets. Several keys
  may share an edge (at most `B` items per packet), so receivers may get several times `n` keys.
* `gak1`/`fwdP`: every node announces up to `s` keys to all members of its group (two rounds).
* `gan1`/`fwdP`: the same with numbers.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace CongestedCliqueRouting

open Finset

variable {V M : Type*} [Fintype V] [DecidableEq V] [DecidableEq M] {B : ℕ}

lemma mem_msgsOf_ofList {l : List (Item M)} (h : l.length ≤ B) {m : M} :
    m ∈ msgsOf (ofList l : Packet M B) ↔ Item.msg m ∈ l := by
  rw [mem_msgsOf]
  constructor
  · rintro ⟨i, hi⟩; exact ofList_eq_some hi
  · intro hm
    obtain ⟨i, hi, hl⟩ := List.getElem_of_mem hm
    refine ⟨⟨i, lt_of_lt_of_le hi h⟩, ?_⟩
    show l[i]? = _
    rw [List.getElem?_eq_getElem hi, hl]

lemma msgsOf_ofList_sub {l : List (Item M)} {m : M} (h : m ∈ msgsOf (ofList l : Packet M B)) :
    Item.msg m ∈ l := by
  obtain ⟨i, hi⟩ := mem_msgsOf.1 h
  exact ofList_eq_some hi

@[simp] lemma msgsOf_ofList_nil : msgsOf (ofList [] : Packet M B) = ∅ := by
  ext m
  simp only [notMem_empty, iff_false]
  intro h
  have := msgsOf_ofList_sub h
  simp at this

@[simp] lemma msgsOf_ofList_num (k : ℕ) : msgsOf (ofList [Item.num k] : Packet M B) = ∅ := by
  ext m
  simp only [notMem_empty, iff_false]
  intro h
  have := msgsOf_ofList_sub h
  simp only [List.mem_cons, List.mem_nil_iff, or_false, reduceCtorEq] at this

/-! ### Relay routing with a known pattern -/

section RR

variable (enc : V → ℕ)

/-- The (key, encoded target) list sent to intermediate node `c`. -/
noncomputable def rrList (H : Finset M) (via tg : M → V) (c : V) : List (M × ℕ) :=
  ((H.filter fun x => via x = c).toList).map fun x => (x, enc (tg x))

/-- Round 1: keys with their targets to the intermediate nodes. -/
noncomputable def rr1 (H : Finset M) (via tg : M → V) (c : V) : Packet M B :=
  ofList ((rrList enc H via tg c).flatMap fun p => [Item.msg p.1, Item.num p.2])

/-- Keys an intermediate node forwards to `w`. -/
noncomputable def fwd (recv : V → Packet M B) (w : V) : Finset M :=
  univ.biUnion fun u =>
    (((pairsL (toL (recv u))).filter fun p => p.2 = enc w).map Prod.fst).toFinset

/-- Round 2: forwarding. -/
noncomputable def rr2 (recv : V → Packet M B) (w : V) : Packet M B :=
  ofList ((fwd enc recv w).toList.map Item.msg)

variable {enc}

lemma length_rr1 (H : Finset M) (via tg : M → V) (c : V) :
    ((rrList enc H via tg c).flatMap fun p => [Item.msg p.1, Item.num p.2]).length =
      2 * (H.filter fun x => via x = c).card := by
  simp [rrList, List.length_flatMap, mul_comm]

lemma pairsL_rr1 {H : Finset M} {via tg : M → V} {c : V}
    (hlen : 2 * (H.filter fun x => via x = c).card ≤ B) :
    pairsL (toL (rr1 enc H via tg c : Packet M B)) = rrList enc H via tg c := by
  unfold rr1
  rw [toL_ofList (by rw [length_rr1]; exact hlen), pairsL_flatten]

lemma mem_fwd_rr1 (henc : Function.Injective enc) {H : V → Finset M} {via tg : V → M → V}
    {c w : V} (hlen : ∀ u, 2 * ((H u).filter fun x => via u x = c).card ≤ B) {x : M} :
    x ∈ fwd enc (fun u => (rr1 enc (H u) (via u) (tg u) c : Packet M B)) w ↔
      ∃ u, x ∈ H u ∧ via u x = c ∧ tg u x = w := by
  simp only [fwd, mem_biUnion, mem_univ, true_and, List.mem_toFinset, List.mem_map,
    List.mem_filter, pairsL_rr1 (hlen _)]
  constructor
  · rintro ⟨u, ⟨y, k⟩, ⟨hyk, hk⟩, rfl⟩
    simp only [rrList, List.mem_map, mem_toList, mem_filter] at hyk
    obtain ⟨z, ⟨hz, hzc⟩, hzx⟩ := hyk
    simp only [Prod.mk.injEq] at hzx
    obtain ⟨rfl, rfl⟩ := hzx
    simp only [decide_eq_true_eq] at hk
    exact ⟨u, hz, hzc, henc hk⟩
  · rintro ⟨u, hx, hc, rfl⟩
    refine ⟨u, (x, enc (tg u x)), ⟨?_, by simp⟩, rfl⟩
    simp only [rrList, List.mem_map, mem_toList, mem_filter]
    exact ⟨x, ⟨hx, hc⟩, rfl⟩

lemma msgsOf_rr2 {recv : V → Packet M B} {w : V} (hlen : (fwd enc recv w).card ≤ B) {x : M} :
    x ∈ msgsOf (rr2 enc recv w : Packet M B) ↔ x ∈ fwd enc recv w := by
  unfold rr2
  rw [mem_msgsOf_ofList (by simpa using hlen)]
  simp

lemma msgsOf_rr2_sub {recv : V → Packet M B} {w : V} {x : M}
    (h : x ∈ msgsOf (rr2 enc recv w : Packet M B)) : x ∈ fwd enc recv w := by
  have := msgsOf_ofList_sub h
  simpa using this

lemma msgsOf_rr1_sub {H : Finset M} {via tg : M → V} {c : V} {x : M}
    (h : x ∈ msgsOf (rr1 enc H via tg c : Packet M B)) : x ∈ H := by
  have := msgsOf_ofList_sub h
  simp only [rrList, List.mem_flatMap, List.mem_map, mem_toList, mem_filter, List.mem_cons,
    Item.msg.injEq, reduceCtorEq, List.mem_nil_iff, or_false, Prod.exists] at this
  obtain ⟨a, b, ⟨y, ⟨hy, -⟩, hyx⟩, rfl⟩ := this
  simp only [Prod.mk.injEq] at hyx
  rw [← hyx.1]; exact hy

/-- Keys forwarded by an intermediate node were received by it. -/
lemma fwd_sub {recv : V → Packet M B} {w : V} {x : M} (h : x ∈ fwd enc recv w) :
    ∃ u, x ∈ msgsOf (recv u) := by
  simp only [fwd, mem_biUnion, mem_univ, true_and, List.mem_toFinset, List.mem_map,
    List.mem_filter, Prod.exists, exists_and_right, exists_eq_right] at h
  obtain ⟨u, k, hk, -⟩ := h
  refine ⟨u, ?_⟩
  -- an element of `pairsL (toL p)` comes from a message item of `p`
  have key : ∀ l : List (Item M), (x, k) ∈ pairsL l → Item.msg x ∈ l := by
    intro l
    induction l using pairsL.induct with
    | case1 y j rest ih =>
      intro h
      simp only [pairsL, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, -⟩ | h
      · simp
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h))
    | case2 l hl =>
      intro h
      rw [pairsL.eq_2 l hl] at h
      simp at h
  have := key _ hk
  rw [mem_msgsOf]
  simp only [toL, List.reduceOption_mem_iff, List.mem_ofFn] at this
  exact this

lemma nums_rr1 {H : Finset M} {via tg : M → V} {c : V} {i : Fin B} {k : ℕ}
    (h : (rr1 enc H via tg c : Packet M B) i = some (Item.num k)) : ∃ x, k = enc (tg x) := by
  have := ofList_eq_some h
  simp only [rrList, List.mem_flatMap, List.mem_map, mem_toList, mem_filter, List.mem_cons,
    reduceCtorEq, Item.num.injEq, List.mem_nil_iff, or_false, false_or, Prod.exists] at this
  obtain ⟨a, b, ⟨y, -, hyx⟩, rfl⟩ := this
  simp only [Prod.mk.injEq] at hyx
  exact ⟨y, hyx.2.symm⟩

lemma nums_rr2 {recv : V → Packet M B} {w : V} {i : Fin B} {k : ℕ}
    (h : (rr2 enc recv w : Packet M B) i = some (Item.num k)) : False := by
  have := ofList_eq_some h
  simp at this

end RR

/-! ### Group announcements with lists -/

section GAL

variable {s : ℕ} (e : V ≃ Fin s × Fin s)

/-- Round 2 of a group announcement: `p` forwards to `w` what it got from member `mem p` of
`w`'s group. -/
def fwdP (P : V → V → Packet M B) (p w : V) : Packet M B := P (node e (grp e w) (mem e p)) p

/-- Round 1 of a key announcement: `v` sends its `j`-th key to node `(j, mem v)`. -/
def gak1 (sel : V → Fin s → Option M) (v w : V) : Packet M B :=
  if mem e w = mem e v then ofList ((sel v (grp e w)).toList.map Item.msg) else ofList []

/-- Round 1 of a number announcement. -/
def gan1 (x : V → Fin s → ℕ) (v w : V) : Packet M B :=
  if mem e w = mem e v then ofList [Item.num (x v (grp e w))] else ofList []

/-- The number in a one-item packet. -/
def numOfL (p : Packet M B) : ℕ :=
  match toL p with
  | [Item.num k] => k
  | _ => 0

lemma fwdP_gak1 (sel : V → Fin s → Option M) (j b : Fin s) (w : V) :
    fwdP e (gak1 e sel) (node e j b) w =
      (ofList ((sel (node e (grp e w) b) j).toList.map Item.msg) : Packet M B) := by
  simp [fwdP, gak1]

lemma fwdP_gan1 (x : V → Fin s → ℕ) (j b : Fin s) (w : V) :
    fwdP e (gan1 e x) (node e j b) w = (ofList [Item.num (x (node e (grp e w) b) j)] : Packet M B) := by
  simp [fwdP, gan1]

lemma numOfL_num (hB : 1 ≤ B) (k : ℕ) : numOfL (ofList [Item.num k] : Packet M B) = k := by
  simp [numOfL, toL_ofList (show [Item.num k].length ≤ B by simpa using hB)]

/-- What `w` receives in round 2 of a key announcement: the keys of its group-mates. -/
lemma rcvd_fwdP_gak1 (hB : 1 ≤ B) (sel : V → Fin s → Option M) (w : V) {x : M} :
    x ∈ rcvd (fwdP e (gak1 e sel) : V → V → Packet M B) w ↔
      ∃ b j, sel (node e (grp e w) b) j = some x := by
  rw [mem_rcvd]
  constructor
  · rintro ⟨p, hp⟩
    rw [← node_grp_mem e p, fwdP_gak1, mem_msgsOf_ofList (by
      rcases sel (node e (grp e w) (mem e p)) (grp e p) with _ | y <;> simp [hB])] at hp
    rcases h : sel (node e (grp e w) (mem e p)) (grp e p) with _ | y
    · simp [h] at hp
    · simp only [h, Option.toList_some, List.map_cons, List.map_nil, List.mem_cons,
        Item.msg.injEq, List.mem_nil_iff, or_false] at hp
      subst hp
      exact ⟨_, _, h⟩
  · rintro ⟨b, j, h⟩
    refine ⟨node e j b, ?_⟩
    rw [fwdP_gak1, mem_msgsOf_ofList (by simp [h, hB]), h]
    simp

lemma msgsOf_gan1 (x : V → Fin s → ℕ) (v w : V) :
    msgsOf (gan1 e x v w : Packet M B) = ∅ := by
  ext m
  simp only [notMem_empty, iff_false]
  intro hm
  unfold gan1 at hm
  split_ifs at hm <;>
  · have := msgsOf_ofList_sub hm
    simp at this

lemma nums_gan1 {x : V → Fin s → ℕ} {v w : V} {i : Fin B} {k : ℕ}
    (h : (gan1 e x v w : Packet M B) i = some (Item.num k)) : ∃ j, k = x v j := by
  unfold gan1 at h
  split_ifs at h
  · have := ofList_eq_some h
    simp only [List.mem_cons, Item.num.injEq, List.mem_nil_iff, or_false] at this
    exact ⟨_, this⟩
  · have := ofList_eq_some h
    simp at this

lemma msgsOf_gak1_sub {sel : V → Fin s → Option M} {v w : V} {x : M}
    (h : x ∈ msgsOf (gak1 e sel v w : Packet M B)) : ∃ j, sel v j = some x := by
  unfold gak1 at h
  split_ifs at h
  · have := msgsOf_ofList_sub h
    simp only [List.mem_map, Option.mem_toList, Item.msg.injEq, exists_eq_right] at this
    exact ⟨_, this⟩
  · have := msgsOf_ofList_sub h
    simp at this

lemma nums_gak1 {sel : V → Fin s → Option M} {v w : V} {i : Fin B} {k : ℕ}
    (h : (gak1 e sel v w : Packet M B) i = some (Item.num k)) : False := by
  unfold gak1 at h
  split_ifs at h <;>
  · have := ofList_eq_some h
    simp at this

end GAL

end CongestedCliqueRouting
