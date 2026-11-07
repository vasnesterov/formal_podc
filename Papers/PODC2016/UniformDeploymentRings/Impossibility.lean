import Papers.PODC2016.UniformDeploymentRings.Model

/-!
# Theorem 5: no uniform deployment with termination detection without knowledge of `k` or `n`

We formalize the replication argument of Theorem 5 of [Shibata et al., PODC 2016].

Fix an algorithm `A` (the same for all rings: the agents know neither `k` nor `n`) and assume it
solves the problem with termination detection in every ring. In the ring `R` with `n = 2` nodes
and `k = 2` agents (one per node), the round-robin execution reaches a configuration at some time
`T` where both agents are halted, one at each node. Consider the ring `R'` with `N = 4(q+1)` nodes,
`q = T`, and `K = 2(q+1)` agents on the nodes `0, …, 2q+1`. We replay the execution of `R` in
`R'`: every atomic action at node `v` of `R` is performed at every node `j ≡ v (mod 2)` of `R'` in
the *window* `[t, 2(q+1))`, which shrinks by one node per step since only the node `0` of `R'`
lacks a predecessor behaving as in `R` (Lemma 1 of the paper). At time `T` the nodes `2q` and
`2q+1` of `R'` look like the two nodes of `R`: each holds a halted agent. Halted agents never
move, but in `R'` uniform deployment requires the agents to be exactly `N / K = 2` apart — a
contradiction.

Our replay is asynchronous (any schedule of `R` is replayed), so the paper's simplifying
assumption that agents move synchronously is not needed.
-/

namespace Podc.UniformDeploymentRings

open Function

section Replay

variable (A : Algorithm)

/-- Agreement of a configuration `D` of `R'` (`N` nodes) with a configuration `C` of `R`
(`2` nodes) on the window `[t, W)`. -/
def Agree {N K : ℕ} (W t : ℕ) (D : Config A N (Fin K)) (C : Config A 2 (Fin 2)) : Prop :=
  ∀ j : ℕ, t ≤ j → j < W → (D (j : ZMod N)).Alike (C (j : ZMod 2))

variable {A}

theorem Agree.mono {N K W t t' : ℕ} {D : Config A N (Fin K)} {C : Config A 2 (Fin 2)}
    (h : Agree A W t D C) (ht : t ≤ t') : Agree A W t' D C :=
  fun j hj hjW => h j (le_trans ht hj) hjW

theorem Local.Alike.haltedStay {ι ι' : Type} {L : Local A ι} {L' : Local A ι'}
    (h : L.Alike L') (hL' : ∃ x ∈ L'.stay, A.halted x.st = true) :
    ∃ x ∈ L.stay, A.halted x.st = true := by
  obtain ⟨x, hx, hh⟩ := hL'
  have h2 := congrArg Local.stay h
  simp only [Local.map] at h2
  have : x.map A (fun _ => ()) ∈ L.stay.map (Agent.map A fun _ => ()) := by
    rw [h2]; exact List.mem_map_of_mem hx
  obtain ⟨y, hy, hyx⟩ := List.mem_map.1 this
  have hst := congrArg Agent.st hyx
  simp only [Agent.map_st] at hst
  exact ⟨y, hy, hst ▸ hh⟩

theorem Local.Alike.push {ι ι' : Type} {L : Local A ι} {L' : Local A ι'} (h : L.Alike L')
    {o : Option (Agent A ι)} {o' : Option (Agent A ι')}
    (ho : o.map (Agent.map A fun _ => ()) = o'.map (Agent.map A fun _ => ())) :
    (L.push A o).Alike (L'.push A o') := by
  unfold Local.Alike at *
  rw [← Local.push_map, ← Local.push_map, h, ho]

theorem natCast_zmod2_eq_iff (j : ℕ) (v : ZMod 2) : ((j : ZMod 2) = v) ↔ j % 2 = v.val := by
  constructor
  · rintro rfl; exact (ZMod.val_natCast 2 j).symm
  · intro h; apply ZMod.val_injective; rw [ZMod.val_natCast, h]

theorem natCast_zmod2_eq_iff' (i j : ℕ) : ((i : ZMod 2) = (j : ZMod 2)) ↔ i = j % 2 ∨ i % 2 = j % 2 := by
  constructor
  · intro h; right; rw [natCast_zmod2_eq_iff, ZMod.val_natCast] at h; exact h
  · rintro (h | h)
    · rw [natCast_zmod2_eq_iff, ZMod.val_natCast, h, Nat.mod_mod]
    · rw [natCast_zmod2_eq_iff, ZMod.val_natCast]; exact h

theorem natCast_inj_lt {N i j : ℕ} (hi : i < N) (hj : j < N) :
    ((i : ZMod N) = (j : ZMod N)) ↔ i = j := by
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt hi, ZMod.val_natCast_of_lt hj] at this
  · rintro rfl; rfl

/-- One step of `R` (action at slot `s` of node `v`, producing `r`) is replayed in `R'` at all
nodes `2c + v` of the window. -/
theorem replay_step {N K q t : ℕ} [NeZero N] (hN : 2 * (q + 1) + 1 < N)
    (D₀ : Config A N (Fin K)) (hD₀ : (allIds D₀).Nodup) (l : List (Fin K))
    (C : Config A 2 (Fin 2)) (v : ZMod 2) (s : Slot) {r} (hr : (C v).act A s = some r)
    (hag : Agree A (2 * (q + 1)) t (l.foldl (step A) D₀) C) :
    ∃ l' : List (Fin K), Agree A (2 * (q + 1)) (t + 1) ((l ++ l').foldl (step A) D₀)
      (stepAt A C v s) := by
  have hv1 : v ≠ v + 1 := by intro h; have := congrArg (· - v) h; simp at this
  have hv1' : v + 1 ≠ v := Ne.symm hv1
  have hCv : stepAt A C v s v = r.1 := stepAt_apply_self hr hv1
  have hCv1 : stepAt A C v s (v + 1) = (C (v + 1)).push A r.2 := stepAt_apply_succ hr hv1'
  have hvv : v.val < 2 := ZMod.val_lt v
  -- `upd m j`: node `j` has already been updated by the replays at copies `c < m`
  let upd : ℕ → ℕ → Prop := fun m j =>
    ∃ c < m, t ≤ 2 * c + v.val ∧ (j = 2 * c + v.val ∨ j = 2 * c + v.val + 1)
  let PA : ℕ → Config A N (Fin K) → Prop := fun m D =>
    ∀ j : ℕ, t ≤ j → j < 2 * (q + 1) →
      (upd m j → (D (j : ZMod N)).Alike (stepAt A C v s (j : ZMod 2))) ∧
      (¬ upd m j → (D (j : ZMod N)).Alike (C (j : ZMod 2)))
  have loop : ∀ m ≤ q + 1, ∃ l' : List (Fin K), PA m ((l ++ l').foldl (step A) D₀) := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨[], fun j hj hjW => ⟨fun ⟨c, hc, _⟩ => absurd hc (Nat.not_lt_zero _), fun _ => ?_⟩⟩
      simpa using hag j hj hjW
    | succ m ih =>
      intro hm
      obtain ⟨l', hl'⟩ := ih (by omega)
      set D := (l ++ l').foldl (step A) D₀ with hD
      by_cases htu : t ≤ 2 * m + v.val
      · -- replay at node `u = 2m + v`
        set u := 2 * m + v.val with hu
        have huW : u < 2 * (q + 1) := by omega
        have hnu : ¬ upd m u := by
          rintro ⟨c, hc, _, h | h⟩ <;> omega
        have hAu := (hl' u htu huW).2 hnu
        have hu2 : (u : ZMod 2) = v := by
          rw [natCast_zmod2_eq_iff]; omega
        rw [hu2] at hAu
        have hact := hAu.act s
        rw [hr] at hact
        obtain ⟨r', hr', hrr⟩ : ∃ r', (D (u : ZMod N)).act A s = some r' ∧
            (r'.1.map A (fun _ => ()), r'.2.map (Agent.map A fun _ => ())) =
              (r.1.map A (fun _ => ()), r.2.map (Agent.map A fun _ => ())) := by
          rcases h' : (D (u : ZMod N)).act A s with _ | r'
          · rw [h'] at hact; simp at hact
          · rw [h'] at hact; simp only [Option.map_some, Option.some.injEq] at hact
            exact ⟨r', rfl, hact⟩
        -- the actor of `R'` at slot `s` of node `u`
        obtain ⟨x', hx'⟩ : ∃ x', (D (u : ZMod N)).actor A s = some x' := by
          unfold Local.act at hr'
          rcases h' : (D (u : ZMod N)).actor A s with _ | x'
          · simp [h'] at hr'
          · exact ⟨x', rfl⟩
        have hnd : (allIds D).Nodup := by rw [hD, allIds_foldl]; exact hD₀
        refine ⟨l' ++ [x'.id], ?_⟩
        rw [← List.append_assoc, List.foldl_append, List.foldl_cons, List.foldl_nil, ← hD,
          step_eq_stepAt hnd hx']
        have hNu : (u : ZMod N) ≠ (u : ZMod N) + 1 := by
          intro h; have := congrArg (· - (u : ZMod N)) h
          simp only [sub_self, add_sub_cancel_left] at this
          have h1 := congrArg ZMod.val this
          rw [ZMod.val_zero, ZMod.val_one_eq_one_mod, Nat.one_mod_eq_one.2 (by omega)] at h1
          omega
        have hDu : stepAt A D (u : ZMod N) s (u : ZMod N) = r'.1 := stepAt_apply_self hr' hNu
        have hDu1 : stepAt A D (u : ZMod N) s ((u : ZMod N) + 1) =
            (D ((u : ZMod N) + 1)).push A r'.2 := stepAt_apply_succ hr' (Ne.symm hNu)
        have hr1 : r'.1.Alike r.1 := congrArg Prod.fst hrr
        have hr2 := congrArg Prod.snd hrr
        intro j hj hjW
        by_cases hj1 : j = u
        · subst hj1
          refine ⟨fun _ => ?_, fun hn => absurd ⟨m, by omega, htu, Or.inl rfl⟩ hn⟩
          rw [hDu, hu2, hCv]; exact hr1
        · by_cases hj2 : j = u + 1
          · subst hj2
            refine ⟨fun _ => ?_, fun hn => absurd ⟨m, by omega, htu, Or.inr rfl⟩ hn⟩
            have hnu1 : ¬ upd m (u + 1) := by
              rintro ⟨c, hc, _, h | h⟩ <;> omega
            have hA1 := (hl' (u + 1) (by omega) hjW).2 hnu1
            have hu12 : ((u + 1 : ℕ) : ZMod 2) = v + 1 := by push_cast; rw [hu2]
            rw [hu12] at hA1 ⊢
            push_cast
            rw [hDu1, hCv1]
            push_cast at hA1
            exact hA1.push hr2
          · have hne1 : (j : ZMod N) ≠ (u : ZMod N) := by
              rw [Ne, natCast_inj_lt (by omega) (by omega)]; exact hj1
            have hne2 : (j : ZMod N) ≠ (u : ZMod N) + 1 := by
              have : (u : ZMod N) + 1 = ((u + 1 : ℕ) : ZMod N) := by push_cast; rfl
              rw [this, Ne, natCast_inj_lt (by omega) (by omega)]; exact hj2
            rw [stepAt_apply_of_ne hne1 hne2]
            have hupd : upd (m + 1) j ↔ upd m j := by
              constructor
              · rintro ⟨c, hc, htc, h⟩
                refine ⟨c, ?_, htc, h⟩
                rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
                · exact hc
                · rcases h with h | h <;> omega
              · rintro ⟨c, hc, htc, h⟩; exact ⟨c, by omega, htc, h⟩
            rw [hupd]; exact hl' j hj hjW
      · -- copy `m` lies outside the window: nothing to do
        refine ⟨l', fun j hj hjW => ?_⟩
        have hupd : upd (m + 1) j ↔ upd m j := by
          constructor
          · rintro ⟨c, hc, htc, h⟩
            refine ⟨c, ?_, htc, h⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hc | rfl
            · exact hc
            · omega
          · rintro ⟨c, hc, htc, h⟩; exact ⟨c, by omega, htc, h⟩
        rw [hupd]; exact hl' j hj hjW
  obtain ⟨l', hl'⟩ := loop (q + 1) le_rfl
  refine ⟨l', fun j hj hjW => ((hl' j (by omega) hjW).1 ?_)⟩
  -- every node of the new window has been updated
  by_cases hjv : j % 2 = v.val
  · exact ⟨(j - v.val) / 2, by omega, by omega, Or.inl (by omega)⟩
  · exact ⟨(j - v.val - 1) / 2, by omega, by omega, Or.inr (by omega)⟩

end Replay

/-- The window of `R'` agrees with `R` along the whole execution of `R`. -/
theorem replay {A : Algorithm} {N K q : ℕ} [NeZero N] (hN : 2 * (q + 1) + 1 < N)
    (D₀ : Config A N (Fin K)) (hD₀ : (allIds D₀).Nodup) (C₀ : Config A 2 (Fin 2))
    (hC₀ : (allIds C₀).Nodup) (σ : ℕ → Fin 2) (h0 : Agree A (2 * (q + 1)) 0 D₀ C₀) :
    ∀ t, ∃ l : List (Fin K), Agree A (2 * (q + 1)) t (l.foldl (step A) D₀) (exec A C₀ σ t)
  | 0 => ⟨[], h0⟩
  | t + 1 => by
    obtain ⟨l, hl⟩ := replay hN D₀ hD₀ C₀ hC₀ σ h0 t
    have hnd : (allIds (exec A C₀ σ t)).Nodup := by rw [allIds_exec]; exact hC₀
    by_cases he : ∃ p : ZMod 2 × Slot,
        (((exec A C₀ σ t) p.1).actor A p.2).map Agent.id = some (σ t)
    · obtain ⟨⟨v, s⟩, hp⟩ := he
      obtain ⟨x, hx, hxid⟩ := Option.map_eq_some_iff.1 hp
      have hst : exec A C₀ σ (t + 1) = stepAt A (exec A C₀ σ t) v s := by
        rw [exec, ← hxid, step_eq_stepAt hnd hx]
      rw [hst]
      rcases hr : ((exec A C₀ σ t) v).act A s with _ | r
      · rw [stepAt_of_act_none hr]; exact ⟨l, hl.mono (Nat.le_succ t)⟩
      · obtain ⟨l', hl'⟩ := replay_step hN D₀ hD₀ l _ v s hr hl
        exact ⟨l ++ l', hl'⟩
    · have hst : exec A C₀ σ (t + 1) = exec A C₀ σ t := by
        simp only [exec, step, he, ↓reduceDIte]
      rw [hst]; exact ⟨l, hl.mono (Nat.le_succ t)⟩

/-- **Theorem 5** of [Shibata et al., PODC 2016]: no algorithm solves the uniform deployment problem
with termination detection when the agents know neither `k` nor `n`, i.e. no single algorithm
solves it in every ring of `n` nodes with `2 ≤ k ≤ n` agents placed at distinct nodes. -/
theorem theorem_5 (A : Algorithm) :
    ¬ ∀ (n k : ℕ) (home : Fin k → ZMod n), 2 ≤ k → k ≤ n → Function.Injective home →
      SolvesTD A n k home := by
  intro hsol
  /- The ring `R`: two nodes, one agent on each. -/
  let homeR : Fin 2 → ZMod 2 := fun a => (a.val : ZMod 2)
  have hinjR : Injective homeR := by decide
  let σR : ℕ → Fin 2 := fun t => ⟨t % 2, Nat.mod_lt _ (by norm_num)⟩
  have hfairR : Fair σR := fun a N => ⟨2 * N + a.val, by omega, by ext; simp [σR]; omega⟩
  obtain ⟨⟨T, hT⟩, hfin⟩ := hsol 2 2 homeR le_rfl le_rfl hinjR σR hfairR
  obtain ⟨hqe, huni⟩ := hfin T hT
  set C₀ := initConfig A 2 homeR with hC₀
  set E := exec A C₀ σR with hE
  have hndR : (allIds C₀).Nodup := allIds_initConfig_nodup (A := A) homeR
  -- at time `T` both nodes of `R` hold a halted agent
  have hR : ∀ j : ZMod 2, HaltedAt (E T) j := by
    have h0 : (0 : Fin 2) ∈ allIds (E T) := by
      rw [hE, allIds_exec]
      unfold allIds
      rw [Multiset.mem_sum]
      exact ⟨0, Finset.mem_univ _, by simp [hC₀, initConfig, Local.ids, homeR]⟩
    unfold allIds at h0
    obtain ⟨v, -, hv⟩ := Multiset.mem_sum.1 h0
    simp only [Local.ids, hqe v, List.map_nil, Multiset.coe_nil, add_zero, Multiset.mem_coe] at hv
    have hocc : occ A (E T) v ≠ 0 := by
      unfold occ; intro h; rw [List.length_eq_zero_iff] at h; simp [h] at hv
    obtain ⟨d, hd, hd0, hocc1, -⟩ := huni.2 v hocc
    have hd1 : d = 1 := by omega
    subst hd1
    have hocc' : ∀ w, occ A (E T) w ≠ 0 → HaltedAt (E T) w := by
      intro w hw
      obtain ⟨x, hx⟩ := List.exists_mem_of_length_pos (Nat.pos_of_ne_zero hw)
      exact ⟨x, hx, hT w x (List.mem_append_left _ hx)⟩
    intro j
    have key : ∀ a b : ZMod 2, a = b ∨ a = b + 1 := by decide
    rcases key j v with rfl | rfl
    · exact hocc' _ hocc
    · exact hocc' _ (by simpa using hocc1)
  /- The ring `R'`: `N = 4(q+1)` nodes, `K = 2(q+1)` agents on the nodes `0, …, 2q+1`. -/
  set q := T
  set N := 4 * (q + 1) with hN
  set K := 2 * (q + 1) with hK
  have : NeZero N := ⟨by omega⟩
  let homeR' : Fin K → ZMod N := fun a => (a.val : ZMod N)
  have hinjR' : Injective homeR' := fun a b h =>
    Fin.ext ((natCast_inj_lt (by omega) (by omega)).1 h)
  set D₀ := initConfig A K homeR' with hD₀
  have hnd' : (allIds D₀).Nodup := allIds_initConfig_nodup (A := A) homeR'
  have h0 : Agree A (2 * (q + 1)) 0 D₀ C₀ := by
    intro j _ hj
    have e1 : (List.finRange K).filter (fun a => decide (homeR' a = (j : ZMod N))) =
        [⟨j, hj⟩] := filter_finRange_eq_singleton _ _ fun a => by
      simp only [decide_eq_true_eq, homeR']
      rw [natCast_inj_lt (by omega) (by omega)]
      exact ⟨fun h => Fin.ext h, fun h => by rw [h]⟩
    have e2 : (List.finRange 2).filter (fun a => decide (homeR a = (j : ZMod 2))) =
        [⟨j % 2, Nat.mod_lt _ (by norm_num)⟩] := filter_finRange_eq_singleton _ _ fun a => by
      simp only [decide_eq_true_eq, homeR]
      rw [natCast_zmod2_eq_iff' a.val j]
      constructor
      · intro h; ext; simp; have := a.isLt; omega
      · intro h; subst h; simp
    simp only [Local.Alike, hD₀, hC₀, initConfig, e1, e2, Local.map]
    rfl
  obtain ⟨l, hl⟩ := replay (by omega) D₀ hnd' C₀ hndR σR h0 T
  /- the corresponding nodes `2q` and `2q + 1` of `R'` hold halted agents -/
  have hR' : ∀ j : ℕ, j < 2 → HaltedAt (l.foldl (step A) D₀) ((2 * q + j : ℕ) : ZMod N) := by
    intro j hj
    exact (hl (2 * q + j) (by omega) (by omega)).haltedStay (hR _)
  /- a fair schedule of `R'` starting with the replay -/
  let σ' : ℕ → Fin K := fun t =>
    if h : t < l.length then l[t] else ⟨(t - l.length) % K, Nat.mod_lt _ (by omega)⟩
  have hfair' : Fair σ' := by
    intro a M
    refine ⟨l.length + K * M + a.val, by nlinarith [a.isLt], ?_⟩
    simp only [σ', show ¬ (l.length + K * M + a.val < l.length) by omega, ↓reduceDIte]
    ext; simp only
    rw [show l.length + K * M + a.val - l.length = a.val + K * M by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt a.isLt]
  have hpre : exec A D₀ σ' l.length = l.foldl (step A) D₀ := by
    rw [exec_eq_foldl D₀ σ' l (fun i hi => by simp [σ', hi]) l.length le_rfl, List.take_length]
  obtain ⟨⟨T₂, hT₂⟩, hfin'⟩ := hsol N K homeR' (by omega) (by omega) hinjR' σ' hfair'
  set T₃ := max T₂ l.length
  have hT₃ : AllHalted A (exec A D₀ σ' T₃) := by
    rw [show T₃ = T₂ + (T₃ - T₂) by omega, exec_of_allHalted hT₂]; exact hT₂
  obtain ⟨-, huni'⟩ := hfin' T₃ hT₃
  have hocc : ∀ j : ℕ, j < 2 → occ A (exec A D₀ σ' T₃) ((2 * q + j : ℕ) : ZMod N) ≠ 0 := by
    intro j hj
    have := (hpre ▸ hR' j hj).exec (T₃ - l.length)
    rw [show l.length + (T₃ - l.length) = T₃ by omega] at this
    obtain ⟨x, hx, -⟩ := this
    unfold occ; intro h; rw [List.length_eq_zero_iff] at h
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
    simp [h] at hx
  obtain ⟨d, hd, -, -, hgap⟩ := huni'.2 _ (hocc 0 (by norm_num))
  have hNK : N / K = 2 := by
    rw [hN, hK, show 4 * (q + 1) = 2 * (2 * (q + 1)) by ring, Nat.mul_div_cancel _ (by omega)]
  have hNK' : (N + K - 1) / K = 2 := by
    rw [hN, hK]; apply Nat.div_eq_of_lt_le <;> omega
  have hd2 : d = 2 := by rcases hd with h | h <;> omega
  subst hd2
  have := hgap 1 (by norm_num) (by norm_num)
  rw [← hD₀] at this
  apply hocc 1 (by norm_num)
  push_cast at this ⊢
  simpa using this

end Podc.UniformDeploymentRings
