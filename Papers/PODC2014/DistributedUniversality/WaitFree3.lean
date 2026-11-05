import Papers.PODC2014.DistributedUniversality.WaitFree2

/-!
# Theorem 3 (wait-freedom)
-/

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode} {s s' : St n k} {a : Act n k}
variable {x : Fin k} {j : Fin n} {s0 L : ℕ} {e : Op n} {ρ : ℕ}

/-- The window closes: the next operation appended to `G x` is the helped operation `X`. -/
theorem Wst.close (hM : M.Good) (hI : Inv M s) (h : stepFn M s a = some s')
    (F : Frozen s x j s0 L e ρ) (W : Wst s x j s0 e ρ) (hlen : (s'.G x).length = L + 1) :
    (j, s0) ∈ s'.G x := by
  rcases GB_cases h x with ⟨hG, -⟩ | ⟨mm, hpcG, hxm, htag, hnin, heq, hG, hB⟩
  · rw [hG, F.len] at hlen; omega
  set w := (s.loc a.proc).acop x
  set β := (s.loc a.proc).r
  have hfin : s.finR β x a.proc = some (true, w) := by
    rw [hI.A.finR_loc a.proc (by simp [hpcG]) x, htag]
  obtain ⟨q, hq⟩ := hI.B.GS1 x (L - 1) ρ e F.born F.last
  have hL : 1 ≤ L := by
    have := (List.getElem?_eq_some_iff.1 F.last).1; have := F.len; omega
  have hwG : w ∉ s.G x := by rw [← heq]; exact hnin
  have hβ : ρ + 1 ≤ β := by
    by_contra hlt
    push Not at hlt
    rcases lt_trichotomy (β + 1) ρ with h1 | h1 | h1
    · have := hI.B.GS3 x (L - 1) ρ β w F.born h1 (hI.A.unif_of_commit hM hfin)
      exact hwG (List.mem_of_mem_take this)
    · have := hI.B.GS4 x (L - 1) ρ β w F.born h1 (hI.A.unif_of_commit hM hfin)
      exact hwG (List.mem_of_mem_take this)
    · have hβρ : β = ρ := by omega
      rw [hβρ] at hfin
      have := hI.A.finR_agree hM hq hfin
      apply hwG
      rw [this]
      have hx : L - 1 < (s.G x).length := by rw [F.len]; omega
      have := F.last
      rw [List.getElem?_eq_getElem hx] at this
      simp only [Option.some.injEq] at this
      rw [← this]; exact List.getElem_mem hx
  rcases W.fin_val hI hβ hfin with h1 | h1
  · exfalso; apply hwG; rw [h1]
    have hx : L - 1 < (s.G x).length := by rw [F.len]; omega
    have := F.last
    rw [List.getElem?_eq_getElem hx] at this
    simp only [Option.some.injEq] at this
    rw [← this]; exact List.getElem_mem hx
  · rw [hG, ← h1]; simp

end Podc.DistributedUniversality

namespace Podc.DistributedUniversality

variable {n k : ℕ} {M : Mode}

theorem Exec.G_mono (e : Exec M n k) (x : Fin k) {t t' : ℕ} (htt : t ≤ t') :
    (e.st t).G x <+: (e.st t').G x := by
  induction htt with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (G_prefix (e.step _) x)

theorem Exec.born_mono (e : Exec M n k) (x : Fin k) {t t' : ℕ} (htt : t ≤ t') :
    (e.st t).born x <+: (e.st t').born x := by
  induction htt with
  | refl => exact List.prefix_refl _
  | step _ ih => exact ih.trans (born_prefix (e.step _) x)

theorem Exec.finR_mono' (e : Exec M n k) {t t' : ℕ} (htt : t ≤ t') {r : ℕ} {x : Fin k} {p : Fin n}
    {tw : Bool × Op n} (h : (e.st t).finR r x p = some tw) : (e.st t').finR r x p = some tw := by
  induction htt with
  | refl => exact h
  | step _ ih => exact (InvA.of_reachable (e.reachable _)).finR_mono (e.step _) _ _ _ _ ih

theorem Exec.G_len_succ (e : Exec M n k) (x : Fin k) (t : ℕ) :
    ((e.st (t + 1)).G x).length ≤ ((e.st t).G x).length + 1 := by
  rcases GB_cases (e.step t) x with ⟨h1, -⟩ | ⟨-, -, -, -, -, -, h1, -⟩ <;> rw [h1] <;> simp

/-- **Theorem 3** (wait-freedom, with the helping lines L1–L5): in every infinite execution,
every correct process completes infinitely many operations on every object that executes
infinitely many operations (whose sequence `G x` grows without bound). Holds for Figure 1 and
Figure 2 and for `(k, ℓ)`-SC objects. -/
theorem theorem_3 (hℓ : 1 ≤ M.ℓ) (hℓk : M.ℓ ≤ k) (hM : M.Good) (hhelp : M.help = true)
    (e : Exec M n k) {j : Fin n} (hj : e.Correct j) {x : Fin k}
    (hx : ∀ N, ∃ t, N ≤ ((e.st t).G x).length) : e.CompletesInf j x := by
  classical
  have hk : 0 < k := by omega
  have hInv : ∀ t, Inv M (e.st t) := fun t => Reachable.invAll hM (e.reachable t)
  by_contra hno
  unfold Exec.CompletesInf at hno
  push Not at hno
  obtain ⟨N0, hN0⟩ := hno
  let cnt : ℕ → ℕ := fun t => ((e.st t).loc j).cnt x
  have hbound : ∀ t, cnt t ≤ N0 + 1 := by
    intro t; by_contra hc; push Not at hc
    exact (hInv t).ret_of_cnt (c := N0) (by simp only [cnt] at hc; omega) (hN0 N0 t le_rfl)
  obtain ⟨t1, ht1⟩ := e.round_unbounded hℓ hk hj 1
  have hinit : ∀ t, t1 ≤ t → ((e.st t).loc j).pc ≠ .init := by
    intro t ht hpc
    have := ((hInv t).A.init_r j).1 hpc
    have := e.round_mono j ht; omega
  have hmono : ∀ t t', t1 ≤ t → t ≤ t' → cnt t ≤ cnt t' := by
    intro t t' ht htt
    induction htt with
    | refl => exact le_rfl
    | step hle ih =>
      exact ih.trans (InvC.cnt_mono (hInv _).A (hInv _).B (hInv _).C hM (e.step _) j x
        (hinit _ (ht.trans hle)))
  -- the counter of `p_j` on `x` stabilizes
  obtain ⟨t0, ht01, hconst⟩ : ∃ t0, t1 ≤ t0 ∧ ∀ t, t0 ≤ t → cnt t = cnt t0 := by
    by_contra hnc
    push Not at hnc
    have : ∀ d, ∃ t, t1 ≤ t ∧ d ≤ cnt t := by
      intro d
      induction d with
      | zero => exact ⟨t1, le_rfl, Nat.zero_le _⟩
      | succ d ih =>
        obtain ⟨t, ht, hd⟩ := ih
        obtain ⟨t', htt, hne⟩ := hnc t ht
        have := hmono t t' ht htt
        exact ⟨t', ht.trans htt, by omega⟩
    obtain ⟨t, -, ht⟩ := this (N0 + 2)
    have := hbound t; omega
  set s0 := cnt t0
  -- `X = (j, s0)` never enters `G x`
  have hnX : ∀ t, (j, s0) ∉ (e.st t).G x := by
    intro t hX
    have hX2 : (j, s0) ∈ (e.st (max t t0)).G x := (e.G_mono x (le_max_left _ _)).subset hX
    obtain ⟨y, hy, hye⟩ := List.getElem_of_mem hX2
    have hby : y < ((e.st (max t t0)).born x).length := by
      rw [(hInv _).B.born_len]; exact hy
    obtain ⟨q, hq⟩ := (hInv _).B.GS1 x y _ _ (List.getElem?_eq_getElem hby)
      (by rw [List.getElem?_eq_getElem hy, hye])
    set β := ((e.st (max t t0)).born x)[y]
    obtain ⟨t3, ht3⟩ := e.round_unbounded hℓ hk hj (max (β + 2) (((e.st (max t t0)).loc j).r))
    have hr3 : β + 2 ≤ ((e.st (max t3 (max t t0))).loc j).r :=
      (le_max_left _ _).trans (ht3.trans (e.round_mono j (le_max_left _ _)))
    set t4 := max t3 (max t t0)
    have hq4 := e.finR_mono' (le_max_right t3 _) hq
    have hU := (hInv t4).A.unif_of_commit hM hq4
    have hk4 := (hInv t4).B.know j β x _ hU (Or.inl (by omega))
    have hc4 : cnt t4 = s0 := hconst t4 (le_trans (le_max_right _ _) (le_max_right _ _))
    exact Reachable.myOpNin hM (e.reachable t4) j x (by simp only [cnt] at hc4; rw [hc4]; exact hk4)
  -- choose the length `L ≡ j (mod n)`
  have hn : 0 < n := j.pos
  set L := (((e.st t0).G x).length + 1) * n + j.val with hLdef
  have hLj : L % n = j.val := by
    rw [hLdef, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
  have hL0 : ((e.st t0).G x).length < L := by
    rw [hLdef]; nlinarith
  -- the window opens at `τ`
  have hexL : ∃ t, L ≤ ((e.st t).G x).length := hx L
  set τ := Nat.find hexL
  have hτ : L ≤ ((e.st τ).G x).length := Nat.find_spec hexL
  have hτmin : ∀ t < τ, ((e.st t).G x).length < L := fun t ht => by
    have := Nat.find_min hexL ht; omega
  have hτ0 : t0 < τ := by
    by_contra hle; push Not at hle
    have := (e.G_mono x hle).length_le; omega
  obtain ⟨τ0, hτeq⟩ : ∃ τ0, τ = τ0 + 1 := ⟨τ - 1, by omega⟩
  have hlen0 : ((e.st τ0).G x).length + 1 = L := by
    have h1 := hτmin τ0 (by omega)
    have h2 := e.G_len_succ x τ0
    rw [← hτeq] at h2; omega
  have hlenτ : ((e.st τ).G x).length = L := by
    have h2 := e.G_len_succ x τ0; rw [← hτeq] at h2; omega
  obtain ⟨eo, heo⟩ : ∃ eo, ((e.st τ).G x)[L - 1]? = some eo :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ((e.st τ).born x)[L - 1]? = some ρ :=
    ⟨_, List.getElem?_eq_getElem (by rw [(hInv τ).B.born_len]; omega)⟩
  -- the window closes at `τ'`
  have hexL1 : ∃ t, L + 1 ≤ ((e.st t).G x).length := hx (L + 1)
  set τ' := Nat.find hexL1
  have hτ' : L + 1 ≤ ((e.st τ').G x).length := Nat.find_spec hexL1
  have hτ'min : ∀ t < τ', ((e.st t).G x).length < L + 1 := fun t ht => by
    have := Nat.find_min hexL1 ht; omega
  have hττ' : τ < τ' := by
    by_contra hle; push Not at hle
    have := (e.G_mono x hle).length_le; omega
  obtain ⟨τ1, hτ1eq⟩ : ∃ τ1, τ' = τ1 + 1 := ⟨τ' - 1, by omega⟩
  -- frozen facts in the window
  have hfrozen : ∀ t, τ ≤ t → t ≤ τ1 → Frozen (e.st t) x j s0 L eo ρ := by
    intro t ht1 ht2
    have hlt : ((e.st t).G x).length = L := by
      have h1 := (e.G_mono x ht1).length_le
      have h2 := hτ'min t (by omega)
      omega
    have hGeq : (e.st t).G x = (e.st τ).G x :=
      ((e.G_mono x ht1).eq_of_length (by rw [hlt, hlenτ])).symm
    have hBeq : (e.st t).born x = (e.st τ).born x :=
      ((e.born_mono x ht1).eq_of_length (by
        rw [(hInv t).B.born_len, (hInv τ).B.born_len, hlt, hlenτ])).symm
    refine ⟨hlt, by rw [hGeq]; exact heo, by rw [hBeq]; exact hρ, ?_, hinit t (by omega), hnX t⟩
    exact hconst t (by omega)
  -- the helping invariant holds throughout the window
  have hW : ∀ d, τ + d ≤ τ1 → Wst (e.st (τ + d)) x j s0 eo ρ := by
    intro d
    induction d with
    | zero =>
      intro h0
      have hstep := e.step τ0
      rw [← hτeq] at hstep
      exact Wst.start hM hhelp hLj (hInv τ0) hstep hlen0 (hfrozen τ le_rfl (by omega))
        (hconst τ0 (by omega)) (hinit τ0 (by omega))
    | succ d ih =>
      intro hd
      exact Wst.step hM hhelp hLj (hInv _) (e.step (τ + d)) (hfrozen _ (by omega) (by omega))
        (hfrozen _ (by omega) hd) (ih (by omega))
  have hW1 := hW (τ1 - τ) (by omega)
  rw [show τ + (τ1 - τ) = τ1 by omega] at hW1
  have hclose := Wst.close hM (hInv τ1) (e.step τ1) (hfrozen τ1 (by omega) le_rfl) hW1 (by
    have h2 := e.G_len_succ x τ1
    have h3 : L + 1 ≤ ((e.st (τ1 + 1)).G x).length := by rw [← hτ1eq]; exact hτ'
    have := (hfrozen τ1 (by omega) le_rfl).len
    omega)
  exact hnX _ hclose

end Podc.DistributedUniversality
