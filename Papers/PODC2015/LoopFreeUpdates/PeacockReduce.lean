import Papers.PODC2015.LoopFreeUpdates.PeacockSelect

/-!
# Peacock (§4): one double round and node merging

Let `C` be a good selection (the nodes updated in an odd round). A node is *inside* `C` if it lies
strictly inside the interval `(pos₁ c, pos₁ (out₂ c))` of some `c ∈ C`. After the odd round the walk
from `s` visits exactly the nodes that are not inside `C` (`reach_iff_not_inside`), so the even
round updates the nodes inside `C` that are not themselves in `C` (`prune C`, Lemma 3).

*Node merging.* An updated node is merged into the target of its new rule. After the two rounds the
merged network is again a line (Lemma 3): it is the instance `reduce` on the *kept* nodes (neither in
`C` nor inside `C`), whose old and new routes are the restrictions of the old and new routes. The key
facts are
* `rlf_of_reduce`: a relaxed loop-free state `Y` of the merged instance gives the relaxed loop-free
  state `C ∪ prune C ∪ Y` of the original one (this justifies the merging);
* `reduce_length` (Lemma 2): `3 N' + 1 ≤ 2 N` where `N`, `N'` are the numbers of nodes before and
  after the double round.
-/

set_option linter.unusedSectionVars false

namespace Podc.LoopFreeUpdates

open Relation

variable {V : Type*} [DecidableEq V]

theorem getLast?_filter_of {l : List V} {p : V → Bool} {d : V} (h : l.getLast? = some d)
    (hp : p d = true) : (l.filter p).getLast? = some d := by
  rw [List.getLast?_filter]
  rw [← List.head?_reverse] at h
  cases hr : l.reverse with
  | nil => rw [hr] at h; simp at h
  | cons a t =>
    rw [hr] at h
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    simp [hp]

namespace Instance

variable (I : Instance V)

/-! ### Inside, kept and pruned nodes -/

/-- `v` lies strictly inside the interval of some selected node. -/
def Inside (C : Finset V) (v : V) : Prop := ∃ c ∈ C, I.pos₁ c < I.pos₁ v ∧ I.pos₁ v < I.dpos c

instance (C : Finset V) : DecidablePred (I.Inside C) := fun v => by unfold Inside; infer_instance

/-- The nodes that survive the double round (and node merging). -/
def Keep (C : Finset V) (v : V) : Prop := v ∉ C ∧ ¬ I.Inside C v

instance (C : Finset V) : DecidablePred (I.Keep C) := fun v => by unfold Keep; infer_instance

/-- The nodes updated in the even round: those inside `C` that are not in `C`. -/
def prune (C : Finset V) : Finset V := I.nodes.filter (fun v => v ∉ C ∧ I.Inside C v)

variable {I} {C : Finset V}

theorem mem_prune {v : V} : v ∈ I.prune C ↔ v ∈ I.old ∧ v ∉ C ∧ I.Inside C v := by
  simp [prune, I.mem_nodes]

theorem not_keep_of_mem_prune {v : V} (h : v ∈ I.prune C) : ¬ I.Keep C v :=
  fun hk => hk.2 ((mem_prune).1 h).2.2

theorem mem_of_not_keep {v : V} (hv : v ∈ I.old) (h : ¬ I.Keep C v) : v ∈ C ∪ I.prune C := by
  unfold Keep at h
  by_cases hc : v ∈ C
  · exact Finset.mem_union_left _ hc
  · exact Finset.mem_union_right _ ((mem_prune).2 ⟨hv, hc, by tauto⟩)

namespace GoodSelection

variable (hC : I.GoodSelection C)
include hC

theorem not_inside_of_mem {c : V} (hc : c ∈ C) : ¬ I.Inside C c := by
  rintro ⟨c', hc', h1, h2⟩
  have hne : c' ≠ c := by rintro rfl; omega
  have := hC.disj c' hc' c hc hne
  have := hC.fwd c hc
  omega

theorem not_inside_dpos {c w : V} (hc : c ∈ C) (hw : I.out₂ c = some w) : ¬ I.Inside C w := by
  rintro ⟨c', hc', h1, h2⟩
  rw [← I.dpos_of_out₂ hw] at h1 h2
  have := hC.fwd c hc
  have := hC.fwd c' hc'
  by_cases hne : c' = c
  · subst hne; omega
  · have := hC.disj c' hc' c hc hne
    omega

theorem not_inside_out₁ {v w : V} (hv : ¬ I.Inside C v) (hvC : v ∉ C) (hw : I.out₁ v = some w) :
    ¬ I.Inside C w := by
  rintro ⟨c', hc', h1, h2⟩
  obtain ⟨hvm, -, hpw⟩ := I.out₁_spec hw
  rw [hpw] at h1 h2
  by_cases he : I.pos₁ c' = I.pos₁ v
  · have := I.pos₁_inj (I.mem_old_of_fwd (hC.fwd c' hc')) hvm he
    subst this; exact hvC hc'
  · exact hv ⟨c', hc', by omega, by omega⟩

theorem s_not_inside : ¬ I.Inside C I.s := by
  rintro ⟨c', -, h1, -⟩
  rw [I.pos₁_s] at h1; omega

theorem keep_d : I.Keep C I.d := by
  refine ⟨fun hd => ?_, ?_⟩
  · have := hC.fwd _ hd
    have := I.dpos_lt_of_fwd this
    rw [I.pos₁_d] at *; omega
  · rintro ⟨c', hc', h1, h2⟩
    have := I.dpos_lt_of_fwd (hC.fwd c' hc')
    rw [I.pos₁_d] at *; omega

/-! ### The head of the merged line -/

/-- Following the new route from `s` through selected nodes: the old route before the first kept
node of the new route contains no kept node. -/
theorem chain (j : ℕ) (hj : j < I.new.length) (hpre : ∀ (i : ℕ) (hi : i < j),
    ¬ I.Keep C (I.new[i]'(by omega))) :
    ¬ I.Inside C I.new[j] ∧ ∀ x ∈ I.old, I.pos₁ x < I.pos₁ I.new[j] → ¬ I.Keep C x := by
  induction j with
  | zero =>
    have h0 : I.new[0] = I.s := by rw [I.s_eq_new_head, List.head_eq_getElem]
    rw [h0, I.pos₁_s]
    exact ⟨hC.s_not_inside, fun x _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ j ih =>
    obtain ⟨hin, hbefore⟩ := ih (by omega) (fun i hi => hpre i (by omega))
    have hjC : I.new[j] ∈ C := by
      by_contra h
      exact hpre j (by omega) ⟨h, hin⟩
    have hout := I.out₂_getElem j hj
    have hdp := I.dpos_of_out₂ hout
    refine ⟨hC.not_inside_dpos hjC hout, fun x hx hlt => ?_⟩
    rw [← hdp] at hlt
    have hjm : I.new[j] ∈ I.old := (I.mem_new_iff).1 (List.getElem_mem _)
    rcases lt_trichotomy (I.pos₁ x) (I.pos₁ I.new[j]) with h | h | h
    · exact hbefore x hx h
    · rw [I.pos₁_inj hx hjm h]; exact hpre j (by omega)
    · exact fun hk => hk.2 ⟨_, hjC, h, hlt⟩

theorem head_eq_filter :
    (I.old.filter (fun v => decide (I.Keep C v))).head? =
      (I.new.filter (fun v => decide (I.Keep C v))).head? := by
  have hd : I.d ∈ I.new.filter (fun v => decide (I.Keep C v)) := by
    simp [I.mem_new_iff, I.d_mem, hC.keep_d]
  obtain ⟨w, hw⟩ : ∃ w, (I.new.filter (fun v => decide (I.Keep C v))).head? = some w :=
    Option.ne_none_iff_exists'.1 (by
      intro h; rw [List.head?_eq_none_iff] at h; rw [h] at hd; simp at hd)
  rw [hw]
  obtain ⟨hwm, hkw, hbef⟩ := (head?_filter_eq_some_iff I.nodup_new).1 hw
  have hwo : w ∈ I.old := (I.mem_new_iff).1 hwm
  have hj : I.pos₂ w < I.new.length := List.idxOf_lt_length_of_mem hwm
  obtain ⟨-, hall⟩ := hC.chain (I.pos₂ w) hj (fun i hi => by
    have := hbef (I.new[i]'(by omega)) (List.getElem_mem _)
      (by rw [I.nodup_new.idxOf_getElem]; exact hi)
    simpa using this)
  rw [I.getElem_pos₂ hwo] at hall
  refine (head?_filter_eq_some_iff I.nodup).2 ⟨hwo, hkw, fun x hx hlt => ?_⟩
  simpa using hall x hx hlt

/-! ### The merged instance -/

theorem getLast?_old : I.old.getLast? = some I.d := List.getLast?_eq_some_getLast I.ne_nil

end GoodSelection

variable (I)

/-- The merged network after a double round of Peacock with selection `C`: the line on the kept
nodes (Lemma 3: "the subsequent merge operation re-establishes the line topology"). -/
def reduce (hC : I.GoodSelection C) : Instance V where
  old := I.old.filter (fun v => decide (I.Keep C v))
  new := I.new.filter (fun v => decide (I.Keep C v))
  nodup := I.nodup.filter _
  perm := I.perm.filter _
  ne_nil := by
    intro h
    have : I.d ∈ I.old.filter (fun v => decide (I.Keep C v)) := by
      simp [I.d_mem, hC.keep_d]
    rw [h] at this; simp at this
  head_eq := hC.head_eq_filter
  getLast_eq := by
    rw [getLast?_filter_of hC.getLast?_old (by simpa using hC.keep_d),
      getLast?_filter_of (by rw [← I.getLast_eq]; exact hC.getLast?_old) (by simpa using hC.keep_d)]

variable {I}

namespace GoodSelection

variable (hC : I.GoodSelection C)
include hC

theorem reduce_old : (I.reduce hC).old = I.old.filter (fun v => decide (I.Keep C v)) := rfl

theorem mem_reduce_old {v : V} : v ∈ (I.reduce hC).old ↔ v ∈ I.old ∧ I.Keep C v := by
  simp [reduce_old]

theorem reduce_d : (I.reduce hC).d = I.d := by
  have h := getLast?_filter_of (p := fun v => decide (I.Keep C v)) hC.getLast?_old
    (by simpa using hC.keep_d)
  rw [← reduce_old hC, List.getLast?_eq_some_getLast (I.reduce hC).ne_nil] at h
  exact Option.some_injective _ h

theorem reduce_s_spec : (I.reduce hC).s ∈ I.old ∧ I.Keep C (I.reduce hC).s ∧
    ∀ x ∈ I.old, I.pos₁ x < I.pos₁ (I.reduce hC).s → ¬ I.Keep C x := by
  have h : (I.old.filter (fun v => decide (I.Keep C v))).head? = some (I.reduce hC).s :=
    List.head?_eq_some_head (I.reduce hC).ne_nil
  obtain ⟨h1, h2, h3⟩ := (head?_filter_eq_some_iff I.nodup).1 h
  exact ⟨h1, by simpa using h2, fun x hx hlt => by simpa using h3 x hx hlt⟩

/-! ### Walks -/

/-- In any state in which the selected nodes are updated, a node that is not inside `C` reaches
the next kept node on the old route. -/
theorem walk_to_keep {B : Finset V} (hCB : C ⊆ B) :
    ∀ (n : ℕ) (v w : V), I.pos₁ w - I.pos₁ v = n → v ∈ I.old → ¬ I.Inside C v →
      w ∈ I.old → I.Keep C w → I.pos₁ v ≤ I.pos₁ w →
      (∀ x ∈ I.old, I.pos₁ v ≤ I.pos₁ x → I.pos₁ x < I.pos₁ w → ¬ I.Keep C x) →
      ReflTransGen (I.Step B) v w := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v w hn hv hvin hw hkw hle hbet
    by_cases heq : I.pos₁ v = I.pos₁ w
    · rw [I.pos₁_inj hv hw heq]
    · have hvC : v ∈ C := by
        by_contra h
        exact hbet v hv le_rfl (by omega) ⟨h, hvin⟩
      have hf := hC.fwd v hvC
      obtain ⟨y, hy, hpy⟩ := I.out₂_of_fwd hf
      have hym := (I.out₂_spec hy).2.1
      have hyw : I.pos₁ y ≤ I.pos₁ w := by
        by_contra h
        exact hkw.2 ⟨v, hvC, by omega, by omega⟩
      have hstep : I.Step B v y := by unfold Step; rw [I.fwd_of_mem (hCB hvC), hy]
      exact ReflTransGen.head hstep (ih (I.pos₁ w - I.pos₁ y) (by omega) y w rfl hym
        (hC.not_inside_dpos hvC hy) hw hkw hyw (fun x hx h1 h2 => hbet x hx (by omega) h2))

/-- Lemma 3 (correctness of the even round): updating the selected nodes and any subset of the
pruned nodes leaves the destination reachable from every node that is not inside `C`. -/
theorem reach_d_even {X : Finset V} (hX : X ⊆ I.prune C) :
    ∀ (n : ℕ) (v : V), I.old.length - I.pos₁ v = n → v ∈ I.old → ¬ I.Inside C v →
      ReflTransGen (I.Step (C ∪ X)) v I.d := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hn hv hvin
    by_cases hvd : v = I.d
    · rw [hvd]
    by_cases hvC : v ∈ C
    · obtain ⟨y, hy, hpy⟩ := I.out₂_of_fwd (hC.fwd v hvC)
      have hym := (I.out₂_spec hy).2.1
      have hstep : I.Step (C ∪ X) v y := by
        unfold Step; rw [I.fwd_of_mem (Finset.mem_union_left _ hvC), hy]
      have := hC.fwd v hvC
      have := I.pos₁_lt hym
      exact ReflTransGen.head hstep (ih _ (by omega) y rfl hym (hC.not_inside_dpos hvC hy))
    · obtain ⟨y, hy⟩ := I.out₁_of_ne_d hv hvd
      obtain ⟨-, hym, hpy⟩ := I.out₁_spec hy
      have hvX : v ∉ C ∪ X := by
        rw [Finset.mem_union, not_or]
        exact ⟨hvC, fun h => hvin ((mem_prune).1 (hX h)).2.2⟩
      have hstep : I.Step (C ∪ X) v y := by
        unfold Step; rw [I.fwd_of_not_mem hvX, hy]
      have := I.pos₁_lt hym
      exact ReflTransGen.head hstep (ih _ (by omega) y rfl hym (hC.not_inside_out₁ hvin hvC hy))

/-- **Lemma 3** (even round): after the selected nodes `C` have been updated, any subset of the
nodes inside `C` (exactly the nodes off the `s`–`d` walk, see `reach_iff_not_inside`) can be
updated simultaneously without creating a loop reachable from `s`. -/
theorem even_round {X : Finset V} (hX : X ⊆ I.prune C) : I.RelaxedLoopFree (C ∪ X) :=
  I.relaxedLoopFree_of_reach (hC.reach_d_even hX _ I.s rfl I.s_mem hC.s_not_inside)

/-- **Odd round**: any subset of the selected nodes can be updated simultaneously, even without
creating any loop (their new rules all point forward). -/
theorem odd_round {X : Finset V} (hX : X ⊆ C) : I.LoopFree X :=
  I.loopFree_of_dashedFwd (fun v hv _ => (I.fwd_iff_dashedFwd v).1 (hC.fwd v (hX hv)))

/-! ### Simulation of the merged network -/

/-- One step of the merged network is simulated by a walk in the original network, in which all
merged (non-kept) nodes are already updated. -/
theorem step_sim (Y : Finset V) {u w : V} (h : (I.reduce hC).Step Y u w) :
    ReflTransGen (I.Step (C ∪ I.prune C ∪ Y)) u w := by
  set B := C ∪ I.prune C ∪ Y
  have hnk : ∀ x ∈ I.old, ¬ I.Keep C x → x ∈ B := fun x hx hk =>
    Finset.mem_union_left _ (mem_of_not_keep hx hk)
  unfold Step Instance.fwd at h
  split_ifs at h with hu
  · -- `u` uses its new rule: follow the new route through merged nodes
    obtain ⟨hum, hwm, hku, hkw, hlt, hbet⟩ := nextIn_filter I.nodup_new h
    have huo := (I.mem_new_iff).1 hum
    have hwo := (I.mem_new_iff).1 hwm
    have hr := I.reach_new (A := B) (a := I.pos₂ u) (b := I.pos₂ w) hlt.le
      (List.idxOf_lt_length_of_mem hwm) (fun j hj h1 h2 => by
        apply I.fwd_of_mem
        rcases Nat.lt_or_eq_of_le h1 with h1 | h1
        · apply hnk _ ((I.mem_new_iff).1 (List.getElem_mem _))
          have := hbet I.new[j] (List.getElem_mem _)
          simp only [I.nodup_new.idxOf_getElem] at this
          simpa using this h1 h2
        · subst h1
          simp only [I.getElem_pos₂ huo]
          exact Finset.mem_union_right _ hu)
    simp only [I.getElem_pos₂ huo] at hr
    convert hr using 1
    exact (I.getElem_pos₂ hwo).symm
  · -- `u` uses its old rule
    obtain ⟨huo, hwo, hku, hkw, hlt, hbet⟩ := nextIn_filter I.nodup h
    simp only [decide_eq_true_eq] at hku hkw
    have hud : u ≠ I.d := by
      rintro rfl
      have := I.pos₁_lt hwo
      have := I.pos₁_d
      unfold pos₁ at *; omega
    obtain ⟨y, hy⟩ := I.out₁_of_ne_d huo hud
    obtain ⟨-, hym, hpy⟩ := I.out₁_spec hy
    have huB : u ∉ B := by
      simp only [B, Finset.mem_union, not_or]
      exact ⟨⟨hku.1, not_keep_of_mem_prune.mt (not_not.2 hku)⟩, hu⟩
    have hstep : I.Step B u y := by unfold Step; rw [I.fwd_of_not_mem huB, hy]
    refine ReflTransGen.head hstep (hC.walk_to_keep (B := B)
      (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx)) _ y w rfl hym
      (hC.not_inside_out₁ hku.2 hku.1 hy) hwo hkw (by unfold pos₁ at *; omega)
      (fun x hx h1 h2 => ?_))
    have := hbet x hx (by unfold pos₁ at *; omega) h2
    simpa using this

/-- Node merging is sound: if the merged network is relaxed loop-free in state `Y`, then the
original network is relaxed loop-free in state `C ∪ prune C ∪ Y`. -/
theorem rlf_of_reduce {Y : Finset V} (h : (I.reduce hC).RelaxedLoopFree Y) :
    I.RelaxedLoopFree (C ∪ I.prune C ∪ Y) := by
  set B := C ∪ I.prune C ∪ Y
  rw [relaxedLoopFree_iff] at h ⊢
  have key : ∀ a b, ReflTransGen ((I.reduce hC).Step Y) a b → ReflTransGen (I.Step B) a b := by
    intro a b hab
    induction hab with
    | refl => exact ReflTransGen.refl
    | tail _ hst ih => exact ih.trans (hC.step_sim Y hst)
  have h' := key _ _ h
  rw [hC.reduce_d] at h'
  obtain ⟨hsm, hks, hbef⟩ := hC.reduce_s_spec
  refine ReflTransGen.trans ?_ h'
  exact hC.walk_to_keep (B := B) (fun x hx => Finset.mem_union_left _ (Finset.mem_union_left _ hx))
    _ I.s _ rfl I.s_mem hC.s_not_inside hsm hks (by rw [I.pos₁_s]; omega)
    (fun x hx _ h2 => hbef x hx h2)

end GoodSelection

end Instance

end Podc.LoopFreeUpdates
