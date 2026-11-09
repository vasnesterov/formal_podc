import Papers.PODC2018.BeepingLeaderElection.Lemma1

set_option linter.unusedSectionVars false

/-!
# Theorem 2 and Theorem 3 (phase level), for the repaired rule priority

Let `l` be the node with the maximum identifier `X` and `A = α(X)`. Following the proof of Theorem 8
of [Casteigts et al.] (which the paper adapts as Theorem 2):

* every prefix is a prefix of some `α(id_w)` (`exists_alpha`, Lemma 5 of [Casteigts et al.]), hence
  lexicographically at most `A`;
* a node whose prefix is a prefix of `A` is never suspicious and never deletes or changes letters
  (`not_susp_of_prefix`, `step_of_prefix`);
* `l` appends one bit of `A` per phase and stays a candidate (`run_leader`);
* a prefix equal to `A` never changes (`stable`);
* if a node holds `A` from phase `T` on, each neighbour holds `A` from phase `T + 2` on (`hop`).

Hence after `|α(X)| + 2r` phases every node at distance `≤ r` from `l` holds `α(X)` (`theorem_2`,
stronger than the paper's `|α(X)| + 6r`, `theorem_2_paper`), and `l` is the unique candidate and the
unique leader, every node computing `leaderId = α⁻¹(prefix) = X` (`theorem_3_phases`).
-/

namespace Podc.BeepingLeaderElection

/-! ### Local facts about `ruleStep` -/

section local_facts

variable {pr : Priority} {Y : Word} {s : NState} {R : Finset (Word × Bool)}

theorem Act.apply_length_le (a : Act) (x : Word) : (a.apply x).length ≤ x.length + 1 := by
  cases a <;> simp [Act.apply]; omega

theorem ruleStep_length_le : (ruleStep pr Y s R).pre.length ≤ s.pre.length + 1 := by
  rw [ruleStep_pre]; exact Act.apply_length_le _ _

theorem ruleStep_cand_imp (h : (ruleStep pr Y s R).cand = true) : s.cand = true := by
  unfold ruleStep at h; dsimp only at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> simp_all

theorem ruleStep_cand_prefix (h : (ruleStep pr Y s R).cand = true) (hs : s.pre <+: Y) :
    (ruleStep pr Y s R).pre <+: Y := by
  unfold ruleStep at h ⊢; dsimp only at h ⊢
  split_ifs at h ⊢ with h1 h2 h3 h4 h5
  all_goals simp_all
  obtain ⟨t, rfl⟩ := hs
  have : t ≠ [] := by rintro rfl; simp at h5
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil this
  simp

/-- Rule outcome when no rule 1–5 is triggered. -/
theorem ruleStep_quiet (h0 : ¬ 0 < delAmount pr s.pre R)
    (h1 : ¬ ∃ m ∈ R, chgBy s.pre m.1 = true) (h2 : ¬ ∃ m ∈ R, s.pre ++ [true] <+: m.1)
    (h3 : ¬ ∃ m ∈ R, s.pre ++ [false] <+: m.1) :
    ruleStep pr Y s R = if s.cand = true ∧ s.pre.length < Y.length then
      ⟨s.pre ++ [Y.getD s.pre.length false], false, true⟩ else ⟨s.pre, false, s.cand⟩ := by
  unfold ruleStep; dsimp only
  simp only [h0, h1, h2, h3, ite_false]

/-- Lemma 5 of [Casteigts et al.], one step: if all received words and the own word are prefixes of
words of a family `P` (closed under prefixes), and a candidate's word is a prefix of its own `Y ∈ P`,
then the new word is in `P`. -/
theorem ruleStep_mem {P : Word → Prop} (hP : ∀ x y, x <+: y → P y → P x)
    (hR : ∀ m ∈ R, P m.1) (hs : P s.pre) (hc : s.cand = true → s.pre <+: Y) (hY : P Y) :
    P (ruleStep pr Y s R).pre := by
  unfold ruleStep; dsimp only
  split_ifs with h1 h2 h3 h4 h5
  · exact hP _ _ (List.take_prefix _ _) hs
  · obtain ⟨m, hm, hc'⟩ := h2
    obtain ⟨z, y', hz, hy⟩ := chgBy_eq_true_iff.1 hc'
    refine hP _ _ ?_ (hR m hm)
    rw [hz, hy]; simp
  · obtain ⟨m, hm, h⟩ := h3; exact hP _ _ h (hR m hm)
  · obtain ⟨m, hm, h⟩ := h4; exact hP _ _ h (hR m hm)
  · obtain ⟨t, ht⟩ := hc h5.1
    refine hP _ _ ?_ hY
    rw [← ht]
    have : t ≠ [] := by rintro rfl; simp [← ht] at h5
    obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil this
    simp [List.getD_eq_getElem?_getD]
  · exact hs

end local_facts

theorem prefix_le {x y : Word} (h : x <+: y) : x ≤ y := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => simp
  | cons c t =>
    apply le_of_lt
    have := (append_lt_append_iff x (x := []) (y := c :: t)).2 (List.nil_lt_cons c t)
    simpa using this

/-! ### The execution -/

section Network

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (ident : V → ℕ)

/-- Shorthand: the configuration after `t` phases (repaired priority). -/
local notation "C" => run G Priority.maxDelete ident

theorem run_succ (t : ℕ) : C (t + 1) = phase G .maxDelete ident (C t) := rfl

theorem length_le (t : ℕ) (v : V) : (C t v).pre.length ≤ t := by
  induction t generalizing v with
  | zero => simp [run, NState.init]
  | succ t ih =>
    rw [run_succ]
    exact ruleStep_length_le.trans (by have := ih v; omega)

theorem cand_prefix (t : ℕ) (v : V) (h : (C t v).cand = true) : (C t v).pre <+: alpha (ident v) := by
  induction t generalizing v with
  | zero => simp [run, NState.init]
  | succ t ih =>
    rw [run_succ] at h ⊢
    exact ruleStep_cand_prefix h (ih v (ruleStep_cand_imp h))

/-- **Lemma 5 of [Casteigts et al.]**: every prefix is a prefix of some node's α-identifier. -/
theorem exists_alpha (t : ℕ) (v : V) : ∃ w, (C t v).pre <+: alpha (ident w) := by
  induction t generalizing v with
  | zero => exact ⟨v, by simp [run, NState.init]⟩
  | succ t ih =>
    rw [run_succ]
    refine ruleStep_mem (P := fun x => ∃ w, x <+: alpha (ident w))
      (fun x y hxy ⟨w, hw⟩ => ⟨w, hxy.trans hw⟩) (fun m hm => ?_) (ih v)
      (cand_prefix G ident t v) ⟨v, List.prefix_refl _⟩
    obtain ⟨u, -, rfl⟩ := (mem_received G).1 hm
    exact ih u

variable {l : V} (hmax : ∀ v, ident v ≤ ident l)
include hmax

/-- Every prefix is lexicographically at most `α(X)`. -/
theorem le_alpha_max (t : ℕ) (v : V) : (C t v).pre ≤ alpha (ident l) := by
  obtain ⟨w, hw⟩ := exists_alpha G ident t v
  exact (prefix_le hw).trans (alpha_strictMono.monotone (hmax w))

/-- No prefix branches higher than `α(X)`. -/
theorem not_high {z : Word} (hz : z ++ [false] <+: alpha (ident l)) (t : ℕ) (v : V) :
    ¬ z ++ [true] <+: (C t v).pre := by
  intro h
  have h1 := le_alpha_max G ident hmax t v
  have h2 : alpha (ident l) < (C t v).pre := by
    obtain ⟨a, ha⟩ := hz
    obtain ⟨b, hb⟩ := h
    rw [← ha, ← hb, List.append_assoc, List.append_assoc, append_lt_append_iff]
    simp [List.cons_lt_cons_iff]
  exact absurd h1 (not_le.2 h2)

/-- No prefix is a proper extension of `α(X)` (prefix-freeness of the α-encoding). -/
theorem not_ext (t : ℕ) (v : V) {b : Bool} : ¬ alpha (ident l) ++ [b] <+: (C t v).pre := by
  intro h
  obtain ⟨w, hw⟩ := exists_alpha G ident t v
  have h2 := (prefix_append_self _ _).trans (h.trans hw)
  have := alpha_prefix_alpha h2
  rw [this] at h
  have := (h.trans hw).length_le
  simp at this

/-- A node whose prefix is a prefix of `α(X)` is not suspicious. -/
theorem not_susp_of_prefix (n t : ℕ) (v : V) (hn : (C t v).pre.length = n)
    (hp : (C t v).pre <+: alpha (ident l)) : (C t v).susp = false := by
  induction n using Nat.strong_induction_on generalizing t v with
  | _ n ih =>
  by_contra hs
  rw [Bool.not_eq_false] at hs
  have hS := (invariants G ident t).2 v hs
  rcases actOf_delOrChg (Y := alpha (ident v)) hS with ha | ha
  · generalize hau : actOf .maxDelete (alpha (ident v)) (C t v) (received G (C t) v) = a at ha
    cases a with
    | del k =>
      obtain ⟨hk0, hk⟩ := actOf_del_iff.1 hau
      have hpre : (C (t + 1) v).pre = (Act.del k).apply (C t v).pre := by
        rw [run_succ, phase_pre, hau]
      have hsus : (C (t + 1) v).susp = true := by rw [run_succ, phase_susp, hau]; rfl
      refine absurd (ih _ ?_ (t + 1) v rfl ?_) (by rw [hsus]; simp)
      · have := delAmount_le_length G (C t) v
        rw [hpre, Act.del_length, hk]; omega
      · rw [hpre]; exact (Act.del_prefix _ _).trans hp
    | _ => simp at ha
  · obtain ⟨z, hz⟩ := actOf_chg_last ha
    have hpre : (C (t + 1) v).pre = z ++ [true] := by
      rw [run_succ, phase_pre, ha, hz, Act.chg_apply]
    exact not_high G ident hmax (hz ▸ hp) (t + 1) v (by rw [hpre])

/-- The action of a node whose prefix is a prefix of `α(X)` is not a deletion or a change. -/
theorem step_of_prefix (t : ℕ) (v : V) (hp : (C t v).pre <+: alpha (ident l)) :
    (actOf .maxDelete (alpha (ident v)) (C t v) (received G (C t) v)).isDel = false ∧
      actOf .maxDelete (alpha (ident v)) (C t v) (received G (C t) v) ≠ .chg := by
  generalize hau : actOf .maxDelete (alpha (ident v)) (C t v) (received G (C t) v) = a
  have hpre : (C (t + 1) v).pre = a.apply (C t v).pre := by rw [run_succ, phase_pre, hau]
  have hsus : (C (t + 1) v).susp = a.isDel := by rw [run_succ, phase_susp, hau]
  cases a with
  | del k =>
    exfalso
    have := not_susp_of_prefix G ident hmax _ (t + 1) v rfl
      (by rw [hpre]; exact (Act.del_prefix _ _).trans hp)
    rw [hsus] at this; simp at this
  | chg =>
    exfalso
    obtain ⟨z, hz⟩ := actOf_chg_last hau
    exact not_high G ident hmax (hz ▸ hp) (t + 1) v (by rw [hpre, hz, Act.chg_apply])
  | _ => simp


/-- Shorthand for the action of `v` in phase `t + 1`. -/
local notation "act" t:max v:max =>
  actOf Priority.maxDelete (alpha (ident v)) (C t v) (received G (C t) v)

omit hmax in
theorem next_pre (t : ℕ) (v : V) : (C (t + 1) v).pre = (act t v).apply (C t v).pre := by
  rw [run_succ, phase_pre]

omit hmax in
theorem next_susp (t : ℕ) (v : V) : (C (t + 1) v).susp = (act t v).isDel := by
  rw [run_succ, phase_susp]

omit hmax in
theorem allowed_at (t : ℕ) {u v : V} (huv : G.Adj v u) :
    Allowed (act t v) (C t v).pre (C t v).susp (C t u).pre (C t u).susp :=
  allowed_of_inv G (invariants G ident t).1 (invariants G ident t).2 _ huv

/-- A node one bit behind `α(X)`-holding neighbour catches up by one bit. -/
theorem catch_up {t : ℕ} {u v : V} (huv : G.Adj v u) (hu : (C t u).pre = alpha (ident l))
    {b : Bool} {rest : Word} (hA : alpha (ident l) = (C t v).pre ++ b :: rest) :
    (C (t + 1) v).pre = (C t v).pre ++ [b] := by
  have hp : (C t v).pre <+: alpha (ident l) := ⟨_, hA.symm⟩
  obtain ⟨hnd, hnc⟩ := step_of_prefix G ident hmax t v hp
  have hal := allowed_at G ident t huv
  rw [next_pre]
  generalize ha : act t v = a at hnd hnc hal
  cases a with
  | del k => simp at hnd
  | chg => exact absurd rfl hnc
  | app c =>
    simp only [Act.app_apply]
    cases b
    · cases c
      · rfl
      · exfalso
        refine not_high G ident hmax (z := (C t v).pre) ⟨rest, by rw [hA]; simp⟩ (t + 1) v ?_
        rw [next_pre, ha]; simp
    · rcases hal.r4 rest (by rw [hu, hA]) with h | h | h
      · simp at h
      · simp at h
      · cases h; rfl
  | null =>
    exfalso
    cases b
    · exact hal.r5 rest (by rw [hu, hA]) rfl
    · rcases hal.r4 rest (by rw [hu, hA]) with h | h | h <;> simp at h

/-- A prefix equal to `α(X)` never changes. -/
theorem stable_succ {t : ℕ} {v : V} (hv : (C t v).pre = alpha (ident l)) :
    (C (t + 1) v).pre = alpha (ident l) := by
  obtain ⟨hnd, hnc⟩ := step_of_prefix G ident hmax t v (hv ▸ List.prefix_refl _)
  have hn := next_pre G ident t v
  generalize ha : act t v = a at hnd hnc hn
  cases a with
  | del k => simp at hnd
  | chg => exact absurd rfl hnc
  | app c =>
    exfalso; apply not_ext G ident hmax (t + 1) v (b := c)
    rw [hn, hv]; simp
  | null => rw [hn, hv]; rfl

theorem stable {t t' : ℕ} (htt' : t ≤ t') {v : V} (hv : (C t v).pre = alpha (ident l)) :
    (C t' v).pre = alpha (ident l) := by
  induction t', htt' using Nat.le_induction with
  | base => exact hv
  | succ t' _ ih => exact stable_succ G ident hmax ih

/-- A node `p 0` next to a node holding `α(X) = p 1` changes to `p 1`. -/
theorem fix_low {t : ℕ} {u v : V} (huv : G.Adj v u) (hu : (C t u).pre = alpha (ident l))
    {p r : Word} (hA : alpha (ident l) = p ++ true :: r) (hv : (C t v).pre = p ++ [false]) :
    (C (t + 1) v).pre = p ++ [true] := by
  have hal := allowed_at G ident t huv
  have hn := next_pre G ident t v
  have hs := next_susp G ident t v
  rcases hal.r3 p r hv (by rw [hu, hA]) with h | h
  · exfalso
    generalize ha : act t v = a at h hn hs
    cases a with
    | del k =>
      obtain ⟨hk1, -, -⟩ := hal.del_bound k ha
      have hpre : (C (t + 1) v).pre <+: alpha (ident l) := by
        rw [hn, hv, hA]
        exact (Act.del_prefix_of_le (by simpa using hk1)).trans (prefix_append_self _ _)
      have := not_susp_of_prefix G ident hmax _ (t + 1) v rfl hpre
      rw [hs] at this; simp at this
    | _ => simp at h
  · rw [hn, h, hv, Act.chg_apply]


/-- The node with the maximum identifier appends one bit of `α(X)` per phase and stays a candidate. -/
theorem run_leader (t : ℕ) :
    (C t l).pre = (alpha (ident l)).take t ∧ (C t l).cand = true := by
  induction t with
  | zero => simp [run, NState.init]
  | succ t ih =>
    obtain ⟨hx, hc⟩ := ih
    have hp : (C t l).pre <+: alpha (ident l) := hx ▸ List.take_prefix _ _
    obtain ⟨hnd, hnc⟩ := step_of_prefix G ident hmax t l hp
    have hR : ∀ m ∈ received G (C t) l, ∀ b, ¬ (C t l).pre ++ [b] <+: m.1 := by
      intro m hm b hb
      obtain ⟨u, -, rfl⟩ := (mem_received G).1 hm
      rcases Nat.lt_or_ge t (alpha (ident l)).length with ht | ht
      · have h1 := hb.length_le
        have h2 := length_le G ident t u
        simp [hx] at h1; omega
      · rw [hx, List.take_of_length_le ht] at hb
        exact not_ext G ident hmax t u hb
    have h0 : ¬ 0 < delAmount .maxDelete (C t l).pre (received G (C t) l) := fun h => by
      rw [actOf_of_pos h] at hnd; simp at hnd
    have h1 : ¬ ∃ m ∈ received G (C t) l, chgBy (C t l).pre m.1 = true := fun h => by
      rcases actOf_delOrChg (Y := alpha (ident l)) (Or.inr h) with h' | h'
      · rw [hnd] at h'; simp at h'
      · exact hnc h'
    have hq := ruleStep_quiet (pr := .maxDelete) (Y := alpha (ident l)) h0 h1
      (fun ⟨m, hm, h⟩ => hR m hm true h) (fun ⟨m, hm, h⟩ => hR m hm false h)
    rw [run_succ]
    show (ruleStep _ _ _ _).pre = _ ∧ (ruleStep _ _ _ _).cand = true
    rw [hq]
    split_ifs with h
    · refine ⟨?_, rfl⟩
      have hlt : t < (alpha (ident l)).length := by
        have := h.2; rw [hx, List.length_take] at this; omega
      rw [hx, List.take_add_one, List.getElem?_eq_getElem hlt, List.length_take,
        min_eq_left hlt.le]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    · refine ⟨?_, hc⟩
      have hle : (alpha (ident l)).length ≤ t := by
        by_contra hlt; apply h; refine ⟨hc, ?_⟩; rw [hx, List.length_take]; omega
      simp only
      rw [hx, List.take_of_length_le hle, List.take_of_length_le (by omega)]

/-- `α(X)` reaches the maximum-identifier node after `|α(X)|` phases. -/
theorem leader_pre {t : ℕ} (ht : (alpha (ident l)).length ≤ t) : (C t l).pre = alpha (ident l) := by
  rw [(run_leader G ident hmax t).1, List.take_of_length_le ht]

/-- One hop: if `u` holds `α(X)` from phase `T` on, its neighbour `v` holds it from `T + 2` on. -/
theorem hop {T : ℕ} {u v : V} (huv : G.Adj v u)
    (hT : ∀ t, T ≤ t → (C t u).pre = alpha (ident l)) : (C (T + 2) v).pre = alpha (ident l) := by
  have hF := (invariants G ident T).1 v u huv
  rw [hT T le_rfl] at hF
  have hu1 := hT (T + 1) (by omega)
  have hu0 := hT T le_rfl
  have st1 : (C (T + 1) v).pre = alpha (ident l) → (C (T + 2) v).pre = alpha (ident l) :=
    stable_succ G ident hmax
  have st0 : (C T v).pre = alpha (ident l) → (C (T + 2) v).pre = alpha (ident l) :=
    fun h => stable G ident hmax (by omega) h
  rcases hF with hF | hF
  · -- `F y A`
    rcases hF with h | ⟨w, hw, h1, h2⟩ | ⟨p, c, hyp, hA⟩ | ⟨p, w, hyp, hA, -⟩ | ⟨w, hw, -, -, hs⟩
    · exact st0 h
    · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (l := w) (by omega))
      have c1 := catch_up G ident hmax huv hu0 hw
      rcases rest with _ | ⟨b', rest'⟩
      · exact st1 (by rw [c1, hw])
      · have hrest' : rest' = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at h2; omega)
        subst hrest'
        have c2 := catch_up G ident hmax huv hu1 (b := b') (rest := []) (by rw [c1, hw]; simp)
        rw [c2, c1, hw]; simp
    · have c1 := fix_low G ident hmax huv hu0 (r := [c]) (by simp [hA]) hyp
      have c2 := catch_up G ident hmax huv hu1 (b := c) (rest := []) (by rw [c1, hA]; simp)
      rw [c2, c1, hA]; simp
    · exact absurd (by rw [hyp]) (not_high G ident hmax (z := p) ⟨w, by rw [hA]; simp⟩ T v)
    · exfalso
      have := not_susp_of_prefix G ident hmax _ T v rfl ⟨w, hw.symm⟩
      rw [hs] at this; simp at this
  · -- `F A y`
    rcases hF with h | ⟨w, hw, h1, -⟩ | ⟨p, c, hA, hyp⟩ | ⟨p, w, hA, hyp, hw3⟩ | ⟨w, hw, h3, -⟩
    · exact st0 h.symm
    · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (l := w) (by omega))
      exact absurd ⟨rest, by rw [hw]; simp⟩ (not_ext G ident hmax T v (b := b))
    · exact absurd (by rw [hyp]; exact ⟨[c], by simp⟩)
        (not_high G ident hmax (z := p) ⟨[], by rw [hA]; simp⟩ T v)
    · rcases eq_or_ne w [] with rfl | hw0
      · exact st1 (by rw [fix_low G ident hmax huv hu0 (r := []) (by rw [hA]) hyp, hA])
      · have hal := allowed_at G ident T huv
        obtain ⟨k, hk, hkw⟩ := hal.r2 p w [] hyp (by rw [hu0, hA]) hw0
        obtain ⟨hk1, hk3, -⟩ := hal.del_bound k hk
        have hn := next_pre G ident T v
        have hs := next_susp G ident T v
        rw [hk] at hn hs
        rcases hkw.lt_or_eq with hlt | heq
        · exfalso
          have hpre : (C (T + 1) v).pre <+: alpha (ident l) := by
            rw [hn, hyp, hA]
            exact (Act.del_prefix_of_le (by simp; omega)).trans (prefix_append_self _ _)
          have := not_susp_of_prefix G ident hmax _ (T + 1) v rfl hpre
          rw [hs] at this; simp at this
        · have h1 : (C (T + 1) v).pre = p ++ [false] := by
            rw [hn, hyp, ← heq, show p ++ false :: w = (p ++ [false]) ++ w by simp]
            exact Act.del_apply_append_eq rfl
          rw [fix_low G ident hmax huv hu1 (r := []) (by rw [hA]) h1, hA]
    · obtain ⟨b, rest, rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (l := w) (by omega))
      exact absurd ⟨rest, by rw [hw]; simp⟩ (not_ext G ident hmax T v (b := b))

/-- Along a walk of length `r` from `v` to the maximum-identifier node, `v` holds `α(X)` from phase
`|α(X)| + 2r` on. -/
theorem walk_bound (n : ℕ) : ∀ (v : V) (p : G.Walk v l), p.length ≤ n → ∀ t,
    (alpha (ident l)).length + 2 * p.length ≤ t → (C t v).pre = alpha (ident l) := by
  induction n with
  | zero =>
    intro v p hp t ht
    cases p with
    | nil => exact leader_pre G ident hmax (by simpa using ht)
    | cons h q => simp at hp
  | succ n ih =>
    intro v p hp t ht
    cases p with
    | nil => exact leader_pre G ident hmax (by simpa using ht)
    | cons h q =>
      simp only [SimpleGraph.Walk.length_cons] at hp ht
      refine stable G ident hmax (t := (alpha (ident l)).length + 2 * q.length + 2) (by omega) ?_
      exact hop G ident hmax h fun t' ht' => ih _ q (by omega) t' ht'


end Network

section Main

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (ident : V → ℕ)

/-- **Theorem 2** (beeping version of Theorem 10 of [5]), with the repaired rule priority and the
constant `2` of [Casteigts et al., Theorem 8] instead of `6`: let `l` be the node with the maximum
identifier `X`. After `|α(X)| + 2r` phases, every node at distance `r` from `l` has
`prefix = α(X)`. -/
theorem theorem_2 (hconn : G.Connected) {l : V} (hmax : ∀ v, ident v ≤ ident l) (v : V) {t : ℕ}
    (ht : (alpha (ident l)).length + 2 * G.dist l v ≤ t) :
    (run G .maxDelete ident t v).pre = alpha (ident l) := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v l
  rw [SimpleGraph.dist_comm] at ht
  exact walk_bound G ident hmax _ v p le_rfl t (by omega)

/-- **Theorem 2** with the paper's constant: after `|α(X)| + 6r` phases all nodes within distance `r`
of the maximum-identifier node `l` have `prefix = α(X)`. -/
theorem theorem_2_paper (hconn : G.Connected) {l : V} (hmax : ∀ v, ident v ≤ ident l) (r : ℕ)
    (v : V) (hv : G.dist l v ≤ r) {t : ℕ} (ht : (alpha (ident l)).length + 6 * r ≤ t) :
    (run G .maxDelete ident t v).pre = alpha (ident l) :=
  theorem_2 G ident hconn hmax v (by omega)

/-- **Theorem 2, second part / Theorem 3 (phase count)**: with unique identifiers, from phase
`|α(X)| + 2D` on (`D` the diameter) every node has `prefix = α(X)` and computes
`leaderId = α⁻¹(prefix) = X`, and the maximum-identifier node `l` is the unique candidate and the
unique leader. Since `|α(X)| = 2⌊log₂ X⌋ + 3`, this is `O(D + log N)` phases. -/
theorem theorem_3_phases (hconn : G.Connected) (hinj : Function.Injective ident) {l : V}
    (hmax : ∀ v, ident v ≤ ident l) {t : ℕ} (ht : (alpha (ident l)).length + 2 * G.diam ≤ t) :
    (∀ v, (run G .maxDelete ident t v).pre = alpha (ident l)) ∧
    (∀ v, alphaInv (run G .maxDelete ident t v).pre = some (ident l)) ∧
    (∀ v, (run G .maxDelete ident t v).cand = true ↔ v = l) ∧
    (∀ v, leader ident (run G .maxDelete ident t) v ↔ v = l) := by
  have hne : Nonempty V := ⟨l⟩
  have hdiam : G.ediam ≠ ⊤ := SimpleGraph.connected_iff_ediam_ne_top.1 hconn
  have hpre : ∀ v, (run G .maxDelete ident t v).pre = alpha (ident l) := fun v =>
    theorem_2 G ident hconn hmax v (by have := SimpleGraph.dist_le_diam hdiam (u := l) (v := v); omega)
  have hcand : ∀ v, (run G .maxDelete ident t v).cand = true ↔ v = l := by
    intro v
    constructor
    · intro hc
      have := cand_prefix G ident t v hc
      rw [hpre v] at this
      exact hinj (alpha_prefix_alpha this).symm
    · rintro rfl; exact (run_leader G ident hmax t).2
  refine ⟨hpre, fun v => by rw [hpre v, alphaInv_alpha], hcand, fun v => ?_⟩
  constructor
  · exact fun h => (hcand v).1 h.1
  · rintro rfl; exact ⟨(hcand _).2 rfl, hpre _⟩

end Main

end Podc.BeepingLeaderElection
