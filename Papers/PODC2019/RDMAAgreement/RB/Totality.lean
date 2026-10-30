import Papers.PODC2019.RDMAAgreement.RB.Fair

/-!
# Algorithm 2 — Property (4) of Definition 1 (totality)

If a correct process delivers `(k, m)` from `q`, every correct process eventually delivers some
`(k, m')` from `q`.

Key lemma `deliver_of_slot`: if, from time `T` on, the slot `L2Proof[x,κ,q]` of a correct process
`x` holds a valid L2 proof (and every pending write to it is a valid L2 proof), then every correct
thread `(r,q)` working on key `κ` eventually delivers: within one complete `try_deliver` it reads
that slot afresh.
-/

set_option linter.unusedSectionVars false

namespace Podc.RDMAAgreement.RB

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable {F : Finset P} {f : ℕ}

open St

/-- All candidates of the pending read of thread `(r,q)` are valid L2 proofs for its key. -/
def GoodL2 (f : ℕ) (s : St P M) (r q : P) : Prop :=
  ∀ v ∈ s.cand r q, ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key r q) m ρ

open Classical in
/-- The measure of `mu3` as a function of the program counter. -/
noncomputable def mu3c (x : P) (good : Prop) : PC P M → ℕ
  | .wrCopy _ _ => 0
  | .rdL2 i todo =>
    if i = x ∧ good then 1
    else if x ∈ todo then todo.card + 1 else todo.card + 2 * Fintype.card P + 2
  | .rdSnd => Fintype.card P + 2
  | .wrEcho _ => Fintype.card P + 1
  | .rdVal _ todo _ => todo.card + Fintype.card P + 2
  | .wrL1 _ => Fintype.card P + 1
  | .rdL1 _ todo _ => todo.card + Fintype.card P + 2
  | .wrL2 _ => Fintype.card P + 1

/-- Number of steps of thread `(r,q)` until it delivers, given a stable valid L2 proof in
`L2Proof[x,κ,q]` (at most one stale scan, the rest of a `try_deliver`, and one fresh scan). -/
noncomputable def mu3 (f : ℕ) (x r q : P) (s : St P M) : ℕ :=
  mu3c x (GoodL2 f s r q) (s.pc r q)

lemma card_erase_univ (j : P) : (Finset.univ.erase j).card + 1 = Fintype.card P := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have := Fintype.card_pos_iff.2 ⟨j⟩; omega

/-- A fresh read of the stable slot only has valid candidates. -/
lemma good_of_fresh {s s' : St P M} {r q x : P} {κ : ℕ} (E : ThrEffect s s' r q)
    (hslot : SlotOK f s' x κ q) {todo : Finset P} (hpc : s'.pc r q = .rdL2 x todo)
    (hk : s'.key r q = κ) : GoodL2 f s' r q := by
  intro v hv
  rcases E.cand_self ⟨.l2, x, κ, q⟩ (by rw [hpc, hk]; rfl) v hv with rfl | hv
  · obtain ⟨ρ, m, h1, h2⟩ := hslot.1; exact ⟨ρ, m, h1, hk ▸ h2⟩
  · obtain ⟨ρ, m, h1, h2⟩ := hslot.2 v hv; exact ⟨ρ, m, h1, hk ▸ h2⟩

/-- The measure at the start of a `try_deliver` is at most `n`. -/
lemma mu3_start {s s' : St P M} {r q x j : P} {κ : ℕ} (E : ThrEffect s s' r q)
    (hslot : SlotOK f s' x κ q) (hpc : s'.pc r q = PC.start j) (hk : s'.key r q = κ) :
    mu3 f x r q s' ≤ Fintype.card P := by
  have hc := card_erase_univ j
  unfold mu3; rw [hpc]; simp only [PC.start, mu3c]
  by_cases hj : j = x
  · subst hj; rw [if_pos ⟨rfl, good_of_fresh E hslot hpc hk⟩]; omega
  · rw [if_neg (by tauto), if_pos (Finset.mem_erase.2 ⟨Ne.symm hj, Finset.mem_univ _⟩)]; omega

lemma mu3_eq {x r q : P} {s : St P M} {c : PC P M} (h : s.pc r q = c) :
    mu3 f x r q s = mu3c x (GoodL2 f s r q) c := by
  unfold mu3; rw [h]

open Classical in
lemma mu3_thr {s s' : St P M} {r q x : P} {κ : ℕ} (h : Step F f s (.thr r q) s')
    (hslot : SlotOK f s' x κ q) (hk : s.key r q = κ) :
    κ ≤ s'.last r q ∨ mu3 f x r q s' < mu3 f x r q s := by
  have E := h.thrEffect
  have hn := Fintype.card_pos_iff.2 ⟨r⟩
  have hst : ∀ j, s'.pc r q = PC.start j → s'.key r q = κ →
      mu3 f x r q s' ≤ Fintype.card P := fun j hpc hk' => mu3_start E hslot hpc hk'
  cases h.tstep with
  | found i todo ρ m hpc hv hval hpc' hk' =>
    right; rw [mu3_eq hpc', mu3_eq hpc]; simp only [mu3c]; split_ifs <;> omega
  | next i j todo v hpc hv hnv hj hpc' hk' =>
    right
    have hcard := Finset.card_erase_of_mem hj
    have hpos : 0 < todo.card := Finset.card_pos.2 ⟨j, hj⟩
    rw [mu3_eq hpc', mu3_eq hpc]; simp only [mu3c]
    by_cases hA : i = x ∧ GoodL2 f s r q
    · exfalso; obtain ⟨ρ, m, rfl, hv'⟩ := hA.2 v hv; exact hnv ⟨ρ, m, rfl, hv'⟩
    rw [if_neg hA]
    by_cases hjx : j = x
    · subst hjx
      rw [if_pos ⟨rfl, good_of_fresh E hslot hpc' (hk'.trans hk)⟩, if_pos hj]; omega
    · rw [if_neg (by tauto)]
      by_cases hxt : x ∈ todo
      · rw [if_pos (Finset.mem_erase.2 ⟨Ne.symm hjx, hxt⟩), if_pos hxt]; omega
      · rw [if_neg (fun hm => hxt (Finset.mem_of_mem_erase hm)), if_neg hxt]; omega
  | endS i v hpc hv hnv _ hpc' =>
    right; rw [mu3_eq hpc', mu3_eq hpc]; simp only [mu3c]
    by_cases hA : i = x ∧ GoodL2 f s r q
    · exfalso; obtain ⟨ρ, m, rfl, hv'⟩ := hA.2 v hv; exact hnv ⟨ρ, m, rfl, hv'⟩
    rw [if_neg hA, if_neg (Finset.notMem_empty _)]; simp; omega
  | endV i j v hpc hv hnv _ hpc' =>
    right
    have hc := card_erase_univ j
    rw [mu3_eq hpc', mu3_eq hpc]; simp only [mu3c]
    by_cases hA : i = x ∧ GoodL2 f s r q
    · exfalso; obtain ⟨ρ, m, rfl, hv'⟩ := hA.2 v hv; exact hnv ⟨ρ, m, rfl, hv'⟩
    rw [if_neg hA, if_neg (Finset.notMem_empty _)]; simp; omega
  | endL i j v hpc hv hnv _ hpc' =>
    right
    have hc := card_erase_univ j
    rw [mu3_eq hpc', mu3_eq hpc]; simp only [mu3c]
    by_cases hA : i = x ∧ GoodL2 f s r q
    · exfalso; obtain ⟨ρ, m, rfl, hv'⟩ := hA.2 v hv; exact hnv ⟨ρ, m, rfl, hv'⟩
    rw [if_neg hA, if_neg (Finset.notMem_empty _)]; simp; omega
  | copy j ρ m hpc hlast =>
    left; simp [St.key] at hk; omega
  | sndOk v c hpc _ _ _ _ hpc' =>
    right; rw [mu3_eq hpc', mu3_eq hpc]; simp [mu3c]
  | sndBad j v hpc _ _ hpc' hk' =>
    right; have := hst j hpc' (hk'.trans hk); rw [mu3_eq hpc] at *; simp only [mu3c]; omega
  | echo j b hpc hpc' hk' =>
    right; have := hst j hpc' (hk'.trans hk); rw [mu3_eq hpc] at *; simp only [mu3c]; omega
  | valNext i j todo acc v hpc hv hj hpc' =>
    right
    have hcard := Finset.card_erase_of_mem hj
    have hpos : 0 < todo.card := Finset.card_pos.2 ⟨j, hj⟩
    rw [mu3_eq hpc', mu3_eq hpc]; simp only [mu3c]; omega
  | valOk i acc v b hpc _ _ _ hpc' =>
    right; rw [mu3_eq hpc', mu3_eq hpc]; simp [mu3c]
  | valBad i j acc v hpc _ _ hpc' hk' =>
    right; have := hst j hpc' (hk'.trans hk); rw [mu3_eq hpc] at *; simp only [mu3c]; simp; omega
  | l1Done j π hpc hpc' hk' =>
    right; have := hst j hpc' (hk'.trans hk); rw [mu3_eq hpc] at *; simp only [mu3c]; omega
  | l1Next i j todo acc v hpc hv hj hpc' =>
    right
    have hcard := Finset.card_erase_of_mem hj
    have hpos : 0 < todo.card := Finset.card_pos.2 ⟨j, hj⟩
    rw [mu3_eq hpc', mu3_eq hpc]; simp only [mu3c]; omega
  | l1Ok i acc v S m hpc _ _ _ hpc' =>
    right; rw [mu3_eq hpc', mu3_eq hpc]; simp [mu3c]
  | l1Bad i j acc v hpc _ _ hpc' hk' =>
    right; have := hst j hpc' (hk'.trans hk); rw [mu3_eq hpc] at *; simp only [mu3c]; simp; omega
  | l2Done j ρ hpc hpc' hk' =>
    right; have := hst j hpc' (hk'.trans hk); rw [mu3_eq hpc] at *; simp only [mu3c]; omega

lemma mu3_other {s s' : St P M} {ℓ : Label P M} {r q x : P} {κ : ℕ} (h : Step F f s ℓ s')
    (hℓ : ℓ ≠ .thr r q) (hslot : SlotOK f s' x κ q) (hx : x ∉ F) (hk : s.key r q = κ) :
    mu3 f x r q s' ≤ mu3 f x r q s := by
  have hl : s'.loc r q = s.loc r q := by
    by_cases hT : ∃ p q, ℓ = .thr p q
    · obtain ⟨p, q', rfl⟩ := hT
      exact h.frame_thr.1 r q (by rintro ⟨rfl, rfl⟩; exact hℓ rfl)
    · push_neg at hT; exact (h.frame_other hT).1 r q
  simp only [St.loc, Loc.mk.injEq] at hl
  have hk' : s'.key r q = s.key r q := by simp [St.key, hl.2.1]
  unfold mu3; rw [hl.1]
  cases hpc : s.pc r q with
  | rdL2 i todo =>
    simp only [mu3c]
    by_cases hA : i = x ∧ GoodL2 f s r q
    · obtain ⟨rfl, hg⟩ := hA
      have hg' : GoodL2 f s' r q := by
        intro v hv
        have hread : (s.pc r q).rd q (s.key r q) = some ⟨.l2, i, κ, q⟩ := by rw [hpc, hk]; rfl
        have hnew : v ∈ s.cand r q ∨ v ∈ s'.pendW ⟨.l2, i, κ, q⟩ := by
          by_cases hT : ∃ p q, ℓ = .thr p q
          · obtain ⟨p, q', rfl⟩ := hT
            rcases h.thrEffect.cand_other r q (by rintro ⟨rfl, rfl⟩; exact hℓ rfl) v hv with
              h1 | ⟨r', e1, e2⟩
            · exact Or.inl h1
            · rw [hread] at e2; cases e2; exact Or.inr (Or.inl ⟨p, q', e1⟩)
          · push_neg at hT
            cases h with
            | bcast =>
              simp only [St.tick, St.doBcast, mem_addCand] at hv
              rcases hv with hv | ⟨e, -⟩
              · exact Or.inl hv
              · rw [hread] at e; cases e
            | byz hp hr0 =>
              simp only [St.tick, St.write, mem_addCand] at hv
              rcases hv with hv | ⟨e, -⟩
              · exact Or.inl hv
              · rw [hread] at e; cases e; simp only at hr0; exact absurd (hr0 ▸ hp) hx
            | bret => exact Or.inl (by simpa [St.tick, St.write] using hv)
            | bretIdle => exact Or.inl (by simpa [St.tick] using hv)
            | _ => exact absurd rfl (hT _ _)
        rcases hnew with hv | hv
        · rw [hk']; exact hg v hv
        · obtain ⟨ρ, m, h1, h2⟩ := hslot.2 v hv; exact ⟨ρ, m, h1, by rw [hk', hk]; exact h2⟩
      rw [if_pos ⟨rfl, hg'⟩, if_pos ⟨rfl, hg⟩]
    · rw [if_neg hA]; split_ifs <;> omega
  | _ => simp [mu3c]

/-- **Key liveness lemma.** If from time `T` on the slot `L2Proof[x,κ,q]` of a correct `x` is
stable and valid, a correct thread `(r,q)` working on key `κ` eventually delivers key `κ`. -/
theorem deliver_of_slot [Inhabited P] (e : Exec (M := M) F f) (hfair : e.Fair) {r q x : P}
    {κ T : ℕ} (hr : r ∉ F) (hx : x ∉ F) (hslot : ∀ t ≥ T, SlotOK f (e.s t) x κ q)
    (hk : (e.s T).key r q = κ) : ∃ t ≥ T, κ ≤ (e.s t).last r q := by
  refine eventually_of_measure (q := q) e hfair hr (fun t => κ ≤ (e.s t).last r q)
    (fun t => mu3 f x r q (e.s t)) T fun t ht hG => ?_
  have hkt : (e.s t).key r q = κ := by
    have := e.last_mono r q ht; simp [St.key] at hk ⊢; omega
  by_cases hl : e.ℓ t = .thr r q
  · have h := e.step t; rw [hl] at h
    rcases mu3_thr h (hslot (t + 1) (by omega)) hkt with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ⟨fun _ => h1, h1.le⟩
  · exact Or.inr ⟨fun h => absurd h hl, mu3_other (e.step t) hl (hslot (t + 1) (by omega)) hx hkt⟩

/-- The slot of a delivered key of a correct process is stable and valid. -/
lemma slotOK_of_dlv [Inhabited P] (hF : F.card ≤ f) {s : St P M} (hs : Reachable F f s) {p q : P}
    {κ : ℕ} {m : M} (hp : p ∉ F) (hd : s.dlv p q κ = some m) : SlotOK f s p κ q := by
  obtain ⟨ρ, hρ, hv⟩ := (InvF.reach hF hs).slot p hp q κ m hd
  refine ⟨⟨ρ, m, hρ, hv⟩, fun v hv => ?_⟩
  exfalso
  have hle := ((InvF.reach hF hs).dlvIff p hp q κ).1 (by rw [hd]; simp)
  rcases hv with ⟨p', q', hw⟩ | ⟨p', b, -, hr, -⟩
  · cases hc : s.pc p' q' <;> simp [hc, PC.wr] at hw <;>
      (obtain ⟨⟨rfl, rfl, rfl⟩, -⟩ := hw; simp [St.key] at hle; omega)
  · cases hr

/-- **Property (4) of Definition 1 (totality).** In a fair execution with `|F| ≤ f`, if a correct
process delivers `(k, m)` from `q`, then every correct process eventually delivers `(k, m')` from
`q` for some `m'`. -/
theorem Exec.totality [Inhabited P] (hF : F.card ≤ f) (e : Exec (M := M) F f) (hfair : e.Fair)
    {p q r : P} {k : ℕ} {m : M} {t0 : ℕ} (hp : p ∉ F) (hr : r ∉ F)
    (hd : (e.s t0).dlv p q k = some m) : ∃ t m', (e.s t).dlv r q k = some m' := by
  have IF0 := InvF.reach hF (e.reach t0)
  have hk := (IF0.dlvIff p hp q k).1 (by rw [hd]; simp)
  have claim : ∀ k', k' ≤ k → ∃ t, k' ≤ (e.s t).last r q := by
    intro k'
    induction k' with
    | zero => exact fun _ => ⟨0, Nat.zero_le _⟩
    | succ k' ih =>
      intro hk'
      obtain ⟨t1, ht1⟩ := ih (by omega)
      set T := max t0 t1
      have hT1 : k' ≤ (e.s T).last r q := le_trans ht1 (e.last_mono r q (le_max_right _ _))
      by_cases hdone : k' + 1 ≤ (e.s T).last r q
      · exact ⟨T, hdone⟩
      obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.1
        ((IF0.dlvIff p hp q (k' + 1)).2 ⟨by omega, by omega⟩)
      have hslot : ∀ t ≥ T, SlotOK f (e.s t) p (k' + 1) q := fun t ht =>
        slotOK_of_dlv hF (e.reach t) hp ((e.grows (le_trans (le_max_left _ _) ht)).1 p hp q _ _ hm')
      obtain ⟨t, -, ht⟩ := deliver_of_slot e hfair hr hp hslot (by simp [St.key]; omega)
      exact ⟨t, ht⟩
  obtain ⟨t, ht⟩ := claim k le_rfl
  obtain ⟨m', hm'⟩ := Option.ne_none_iff_exists'.1
    (((InvF.reach hF (e.reach t)).dlvIff r hr q k).2 ⟨hk.1, ht⟩)
  exact ⟨t, m', hm'⟩

end Podc.RDMAAgreement.RB
