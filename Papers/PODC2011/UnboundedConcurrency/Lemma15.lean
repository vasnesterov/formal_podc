import Papers.PODC2011.UnboundedConcurrency.Lemma14

/-!
# Lemma 15: the two critical operations are not writes to the same iterator stack

Afek–Morrison–Wertheim, PODC 2011, Section 5.3. Suppose that after `α a b` only `u` and after
`α b a` only `¬u` can be decided, and that `a` and `b` are both poised to write (values `v_a`,
`v_b`) to the same iterator stack `O`. The two executions differ only in `O`'s value sequence:
`[v_b, v_a, …]` versus `[v_a, v_b, …]` (and in the local states of `a`, `b`). We build two
infinite executions, extending `α a b` and `α b a` by the *same* schedule, in which a fresh
victim process `R` takes infinitely many steps but can never tell them apart, hence never
decides — contradicting wait-freedom. Throughout, the memories differ only in two adjacent
entries of `O`'s value sequence (the *window*, positions `w + 1, w + 2`), swapped; a read is
*distinguishing* if the iterator it reads points into the window.

**Repaired construction.** Whenever `R` is about to perform a distinguishing read, we unblock it
with fresh processes, each run solo until it is about to perform a distinguishing read or a write
to `O`:
* a distinguishing read is executed and its process is never scheduled again (the read changes the
  memory in the same way in both executions);
* a process about to write is kept pending; once there are two pending writers, both writes are
  executed, shifting the window two positions down, past `R`'s iterator.
After each distinguishing read we check whether `R`'s read is still distinguishing (other
processes may read `R`'s iterator). Distinguishing reads strictly decrease the potential
`Φ = Σ_iterators (w + 3 - pos)` while no write is executed, so `R` is unblocked after finitely
many fresh processes.

The paper's construction differs in two points that make it fail as written: it freezes a new
process at *any* read with an old iterator (so new processes may be frozen forever without any
progress, e.g. if each first reads an exhausted iterator), and it lets `R` read only after two
writes, although the frozen readers may have advanced `R`'s iterator so that after the two writes
it points into the window again.
-/

namespace Podc.UnboundedConcurrency

open Cslib.SharedMemory Cslib.SharedMemory.Arrival

set_option linter.unusedSectionVars false

/-! ### The window relation on iterator stack states -/

section Window

variable {V : Type}

/-- `l₂` is `l₁` with the entries `w` and `w + 1` (0-based) swapped. -/
def SwapAt (w : ℕ) (l₁ l₂ : List V) : Prop := ∀ k, l₂[k]? = l₁[Equiv.swap w (w + 1) k]?

/-- The iterator stack states differ only by the swap of the window `w + 1, w + 2` (1-based) of
the value sequence. -/
def StRel (w : ℕ) (s₁ s₂ : ISState V) : Prop := s₁.its = s₂.its ∧ SwapAt w s₁.vals s₂.vals

/-- A read of an iterator at position `q` is distinguishing for the window `w`. -/
def InWin (w q : ℕ) : Prop := q = w + 1 ∨ q = w + 2

lemma swap_succ (w j : ℕ) :
    Equiv.swap (w + 1) (w + 1 + 1) (j + 1) = Equiv.swap w (w + 1) j + 1 := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

lemma SwapAt.cons {w : ℕ} {l₁ l₂ : List V} (h : SwapAt w l₁ l₂) (v : V) :
    SwapAt (w + 1) (v :: l₁) (v :: l₂) := by
  intro k
  cases k with
  | zero =>
    have : Equiv.swap (w + 1) (w + 1 + 1) 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
    rw [this]; rfl
  | succ j => rw [swap_succ]; simpa using h j

lemma StRel.write {w : ℕ} {s₁ s₂ : ISState V} (h : StRel w s₁ s₂) (v : V) :
    StRel (w + 1) (s₁.δ (.write v)).1 (s₂.δ (.write v)).1 ∧
      (s₁.δ (.write v)).2 = (s₂.δ (.write v)).2 := by
  obtain ⟨hi, hv⟩ := h
  refine ⟨⟨by simp [hi], by simpa using hv.cons v⟩, by simp [hi]⟩

lemma StRel.read {w : ℕ} {s₁ s₂ : ISState V} (h : StRel w s₁ s₂) (k : ℕ) :
    StRel w (s₁.δ (.read k)).1 (s₂.δ (.read k)).1 := by
  obtain ⟨hi, hv⟩ := h
  rcases lt_or_ge k s₁.its.length with hk | hk
  · have hk2 : k < s₂.its.length := hi ▸ hk
    rw [ISState.δ_read_of_lt _ hk, ISState.δ_read_of_lt _ hk2]
    refine ⟨?_, hv⟩
    simp only
    have : s₁.its[k] = s₂.its[k] := by simp [hi]
    rw [this, hi]
  · rw [ISState.δ_read_of_le _ hk, ISState.δ_read_of_le _ (hi ▸ hk)]
    exact ⟨hi, hv⟩

lemma StRel.read_resp {w : ℕ} {s₁ s₂ : ISState V} (h : StRel w s₁ s₂) (k : ℕ)
    (hk : ∀ q, s₁.its[k]? = some q → ¬ InWin w q) :
    (s₁.δ (.read k)).2 = (s₂.δ (.read k)).2 := by
  obtain ⟨hi, hv⟩ := h
  rcases lt_or_ge k s₁.its.length with hk1 | hk1
  · have hk2 : k < s₂.its.length := hi ▸ hk1
    rw [ISState.δ_read_of_lt _ hk1, ISState.δ_read_of_lt _ hk2]
    have he : s₁.its[k] = s₂.its[k] := by simp [hi]
    have hnw := hk _ (List.getElem?_eq_getElem hk1)
    simp only [ISResp.val.injEq]
    rw [← he]
    unfold ISState.at
    unfold InWin at hnw
    by_cases h0 : s₁.its[k] = 0
    · simp [h0]
    · simp only [h0, ite_false]
      rw [hv]
      congr 1
      exact (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)).symm
  · rw [ISState.δ_read_of_le _ hk1, ISState.δ_read_of_le _ (hi ▸ hk1)]

/-- The potential: the total distance of the iterators to the bottom of the window. -/
def pot (w : ℕ) (s : ISState V) : ℕ := (s.its.map (fun q => w + 3 - q)).sum

lemma sum_set_add (l : List ℕ) {k : ℕ} (a : ℕ) (h : k < l.length) :
    (l.set k a).sum + l[k] = l.sum + a := by
  induction l generalizing k with
  | nil => simp at h
  | cons b l ih =>
    cases k with
    | zero => simp; omega
    | succ k => simp at h ⊢; have := ih (k := k) h; omega

lemma pot_read_le (w : ℕ) (s : ISState V) (k : ℕ) : pot w (s.δ (.read k)).1 ≤ pot w s := by
  rcases lt_or_ge k s.its.length with hk | hk
  · rw [ISState.δ_read_of_lt _ hk]
    unfold pot
    simp only [List.map_set]
    have := sum_set_add (s.its.map (fun q => w + 3 - q)) (w + 3 - (s.its[k] + 1))
      (k := k) (by simpa using hk)
    simp only [List.getElem_map] at this
    omega
  · rw [ISState.δ_read_of_le _ hk]

lemma pot_read_lt (w : ℕ) (s : ISState V) {k q : ℕ} (hq : s.its[k]? = some q) (hw : InWin w q) :
    pot w (s.δ (.read k)).1 < pot w s := by
  have hk : k < s.its.length := by
    by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hq; cases hq
  have hq' : s.its[k] = q := by rw [List.getElem?_eq_getElem hk] at hq; exact Option.some.inj hq
  rw [ISState.δ_read_of_lt _ hk]
  unfold pot
  simp only [List.map_set]
  have := sum_set_add (s.its.map (fun q => w + 3 - q)) (w + 3 - (s.its[k] + 1))
    (k := k) (by simpa using hk)
  simp only [List.getElem_map] at this
  simp only [hq'] at this ⊢
  unfold InWin at hw
  omega

end Window

variable {R S : Type} [DecidableEq R] [DecidableEq S] {B : R → ObjSpec} {W : S → Type}
  {A : Alg (ST B W) ℕ Bool Bool}

/-! ### Related configurations -/

section Rel

variable (s : S)

/-- The two configurations agree off the iterator stack `s`, are related by `StRel w` on it, and
the processes outside `Z` have the same local states. -/
def Rel15 (w : ℕ) (Z : Finset ℕ) (C D : Cfg A) : Prop :=
  (∀ j, j ≠ .inr s → C.mem j = D.mem j) ∧ StRel w (stk C s) (stk D s) ∧
    ∀ p ∉ Z, C.loc p = D.loc p

/-- `p` is poised on a distinguishing read of `s` (for the window `w`). -/
def Dist (w : ℕ) (C : Cfg A) (p : ℕ) : Prop :=
  ∃ k q kk, A.act (C.loc p) = .access (.inr s) (ISOp.read k) kk ∧
    (stk C s).its[k]? = some q ∧ InWin w q

/-- `p` is poised to write to `s`. -/
def WriteS (C : Cfg A) (p : ℕ) : Prop :=
  ∃ v kk, A.act (C.loc p) = .access (.inr s) (ISOp.write v) kk

variable {s}

lemma act_read_inj {L : Type} {s : S} {k k' : ℕ} {kk kk' : ISResp (W s) → L} {Y : Type}
    (h : (Act.access (Sum.inr s) (ISOp.read k) kk : Act (ST B W) L Y) =
      Act.access (Sum.inr s) (ISOp.read k') kk') : k = k' := by
  cases h; rfl

lemma loc_rel_step {w : ℕ} {Z Z' : Finset ℕ} {C D : Cfg A} {p : ℕ}
    (h : Rel15 s w Z C D) (hZ : Z ⊆ Z') (hp : p ∉ Z' → (C.step p).loc p = (D.step p).loc p) :
    ∀ q ∉ Z', (C.step p).loc q = (D.step p).loc q := by
  intro q hq
  by_cases hqp : q = p
  · subst hqp; exact hp hq
  · rw [loc_step_ne hqp, loc_step_ne hqp]; exact h.2.2 q (fun h' => hq (hZ h'))

/-- A step of an unconstrained process that is neither a distinguishing read nor a write to
`s`. -/
lemma Rel15.step_safe {w : ℕ} {Z : Finset ℕ} {C D : Cfg A} {p : ℕ} (h : Rel15 s w Z C D)
    (hp : p ∉ Z) (hd : ¬ Dist s w C p) (hwr : ¬ WriteS s C p) :
    Rel15 s w Z (C.step p) (D.step p) := by
  obtain ⟨h1, h2, h3⟩ := step_off (Pst' := StRel w) (h.2.2 p hp) h.1 (fun o kk hact => by
      cases o with
      | write v => exact absurd ⟨v, kk, hact⟩ hwr
      | read k =>
        exact ⟨h.2.1.read k, h.2.1.read_resp k (fun q hq hw => hd ⟨k, q, kk, hact, hq, hw⟩)⟩)
    (fun _ => h.2.1)
  exact ⟨h2, h3, loc_rel_step h (subset_refl _) (fun _ => h1)⟩

/-- A write to `s` of an unconstrained process shifts the window. -/
lemma Rel15.step_write {w : ℕ} {Z : Finset ℕ} {C D : Cfg A} {p : ℕ} (h : Rel15 s w Z C D)
    (hp : p ∉ Z) (hwr : WriteS s C p) :
    Rel15 s (w + 1) Z (C.step p) (D.step p) := by
  obtain ⟨v, kk, hact⟩ := hwr
  obtain ⟨h1, h2, h3⟩ := step_off (Pst' := StRel (w + 1)) (h.2.2 p hp) h.1
    (fun o kk' hact' => by
      rw [hact] at hact'
      cases hact'
      exact h.2.1.write v)
    (fun hn => absurd ⟨_, _, hact⟩ hn)
  exact ⟨h2, h3, loc_rel_step h (subset_refl _) (fun _ => h1)⟩

/-- Any step that is not a write to `s`, after which its process is constrained no more. -/
lemma Rel15.step_freeze {w : ℕ} {Z : Finset ℕ} {C D : Cfg A} {p : ℕ} (h : Rel15 s w Z C D)
    (hp : p ∉ Z) (hwr : ¬ WriteS s C p) :
    Rel15 s w (insert p Z) (C.step p) (D.step p) := by
  have hloc := h.2.2 p hp
  rcases Arrival.Cfg.out_or_poised C p with ⟨v, hv⟩ | ⟨i, o, k, hact⟩
  · have hv' : D.Out p v := by unfold Cfg.Out at *; rwa [← hloc]
    rw [Arrival.Cfg.step_of_out hv, Arrival.Cfg.step_of_out hv']
    exact ⟨h.1, h.2.1, fun q hq => h.2.2 q (fun h' => hq (Finset.mem_insert_of_mem h'))⟩
  · have hact' : A.act (D.loc p) = .access i o k := hloc ▸ hact
    refine ⟨fun j hj => ?_, ?_, loc_rel_step h (Finset.subset_insert _ _)
      (fun hn => absurd (Finset.mem_insert_self _ _) hn)⟩
    · by_cases hji : j = i
      · subst hji
        rw [Arrival.Cfg.step_mem_self_of_access hact, Arrival.Cfg.step_mem_self_of_access hact',
          h.1 j hj]
      · rw [Arrival.Cfg.step_mem_other hact hji, Arrival.Cfg.step_mem_other hact' hji]
        exact h.1 j hj
    · by_cases hi : i = .inr s
      · subst hi
        unfold stk stkM
        rw [Arrival.Cfg.step_mem_self_of_access hact, Arrival.Cfg.step_mem_self_of_access hact']
        cases o with
        | write v => exact absurd ⟨v, k, hact⟩ hwr
        | read k' => exact h.2.1.read k'
      · unfold stk stkM
        rw [Arrival.Cfg.step_mem_other hact (Ne.symm hi),
          Arrival.Cfg.step_mem_other hact' (Ne.symm hi)]
        exact h.2.1

/-- Steps of a process `p` that is not a write to `s` do not increase the potential. -/
lemma pot_step_le {w : ℕ} {C : Cfg A} {p : ℕ} (hwr : ¬ WriteS s C p) :
    pot w (stk (C.step p) s) ≤ pot w (stk C s) := by
  rcases Arrival.Cfg.out_or_poised C p with ⟨v, hv⟩ | ⟨i, o, k, hact⟩
  · rw [Arrival.Cfg.step_of_out hv]
  · by_cases hi : i = .inr s
    · subst hi
      unfold stk stkM
      rw [Arrival.Cfg.step_mem_self_of_access hact]
      cases o with
      | write v => exact absurd ⟨v, k, hact⟩ hwr
      | read k' => exact pot_read_le w _ k'
    · unfold stk stkM
      rw [Arrival.Cfg.step_mem_other hact (Ne.symm hi)]

/-- A distinguishing read strictly decreases the potential. -/
lemma pot_step_lt {w : ℕ} {C : Cfg A} {p : ℕ} (hd : Dist s w C p) :
    pot w (stk (C.step p) s) < pot w (stk C s) := by
  obtain ⟨k, q, kk, hact, hq, hw⟩ := hd
  unfold stk stkM
  rw [Arrival.Cfg.step_mem_self_of_access hact]
  exact pot_read_lt w _ hq hw

/-- A step of `p` that is not a read of iterator `k` of `s` does not change iterator `k`. -/
lemma its_step_of_not_read {C : Cfg A} {p k : ℕ} (hk : k < (stk C s).its.length)
    (hnr : ∀ kk, A.act (C.loc p) ≠ .access (.inr s) (ISOp.read k) kk) :
    (stk (C.step p) s).its[k]? = (stk C s).its[k]? := by
  rcases Arrival.Cfg.out_or_poised C p with ⟨v, hv⟩ | ⟨i, o, kk, hact⟩
  · rw [Arrival.Cfg.step_of_out hv]
  · by_cases hi : i = .inr s
    · subst hi
      unfold stk stkM
      rw [Arrival.Cfg.step_mem_self_of_access hact]
      cases o with
      | write v =>
        show ((C.mem (.inr s) : ISState (W s)).its ++ [1])[k]? = _
        exact List.getElem?_append_left hk
      | read k' =>
        have hkk : k' ≠ k := fun e => hnr kk (by rw [hact, e])
        show ((C.mem (.inr s) : ISState (W s)).δ (.read k')).1.its[k]? = _
        rcases lt_or_ge k' (C.mem (.inr s) : ISState (W s)).its.length with h | h
        · rw [ISState.δ_read_of_lt _ h]
          exact List.getElem?_set_ne hkk
        · rw [ISState.δ_read_of_le _ h]
    · unfold stk stkM
      rw [Arrival.Cfg.step_mem_other hact (Ne.symm hi)]

lemma not_writeS_of_dist {w : ℕ} {C : Cfg A} {p : ℕ} (hd : Dist s w C p) : ¬ WriteS s C p := by
  obtain ⟨k, q, kk, hact, -⟩ := hd
  rintro ⟨v, kk', hact'⟩
  rw [hact] at hact'
  cases hact'

lemma loc_exec_append {x : ℕ → Bool} {α τ : List ℕ} {p : ℕ} (h : p ∉ τ) :
    (A.exec x (α ++ τ)).loc p = (A.exec x α).loc p := by
  rw [Alg.exec_append, Alg.run_loc_other _ _ h]

lemma WriteS.of_loc {C C' : Cfg A} {p : ℕ} (h : WriteS s C p) (he : C'.loc p = C.loc p) :
    WriteS s C' p := by
  obtain ⟨v, kk, hact⟩ := h; exact ⟨v, kk, he ▸ hact⟩

end Rel

/-! ### The construction -/

section Construction

variable (hwf : WaitFree A (fun s => (Set.range s).Finite)) {x : ℕ → Bool} {B₁ B₂ : List ℕ}
  {u : Bool} (h₁ : Uni A x B₁ u) (h₂ : Uni A x B₂ (!u)) {s : S} (r : ℕ)
include hwf h₁ h₂

/-- **Unblocking the victim.** If the victim `r` is poised on a distinguishing read, fresh
processes can be scheduled (the same schedule after `B₁` and after `B₂`) so that the
configurations stay related, `r` stays unconstrained and does not move, and its next read is no
longer distinguishing. `pend` is a fresh process already poised to write to `s`. -/
lemma unblock : ∀ (N : ℕ) (σ : List ℕ) (w : ℕ) (Z : Finset ℕ) (pend : Option ℕ),
    2 * pot w (stk (A.exec x (B₁ ++ σ)) s) + (if pend = none then 1 else 0) = N →
    Rel15 s w Z (A.exec x (B₁ ++ σ)) (A.exec x (B₂ ++ σ)) → r ∉ Z →
    Dist s w (A.exec x (B₁ ++ σ)) r →
    (∀ q, pend = some q → q ∉ Z ∧ q ≠ r ∧ WriteS s (A.exec x (B₁ ++ σ)) q) →
    ∃ σ' w' Z', Rel15 s w' Z' (A.exec x (B₁ ++ σ ++ σ')) (A.exec x (B₂ ++ σ ++ σ')) ∧
      r ∉ Z' ∧ ¬ Dist s w' (A.exec x (B₁ ++ σ ++ σ')) r ∧ r ∉ σ' := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro σ w Z pend hN hrel hrZ hdist hpend
  set C₀ := A.exec x (B₁ ++ σ) with hC₀
  obtain ⟨kR, qR, kkR, hactR, hqR, hwR⟩ := hdist
  -- a fresh process
  obtain ⟨F, hF⟩ := exists_fresh (B₁ ++ σ ++ (r :: Z.toList ++ pend.toList))
  simp only [List.mem_append, List.mem_cons, Finset.mem_toList, Option.mem_toList, not_or]
    at hF
  obtain ⟨⟨-, -⟩, ⟨hFr, hFZ⟩, hFpend⟩ := hF
  -- run it solo until it is about to perform a distinguishing read or a write to `s`
  let Rel' : Cfg A → Cfg A → Prop := fun C D => Rel15 s w Z C D ∧
    pot w (stk C s) ≤ pot w (stk C₀ s) ∧ (stk C s).its[kR]? = some qR
  let Bad : Cfg A → Prop := fun C => Dist s w C F ∨ WriteS s C F
  have hstep : ∀ C D, Rel' C D → ¬ Bad C → Rel' (C.step F) (D.step F) := by
    intro C D ⟨hR, hpot, hits⟩ hbad
    simp only [Bad, not_or] at hbad
    have hk : kR < (stk C s).its.length := by
      by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hits; cases hits
    refine ⟨hR.step_safe hFZ hbad.1 hbad.2, le_trans (pot_step_le hbad.2) hpot, ?_⟩
    rw [its_step_of_not_read hk (fun kk h => hbad.1 ⟨kR, qR, kk, h, hits, hwR⟩)]
    exact hits
  obtain ⟨n, -, hbad, hrel', hpot₁, hits₁⟩ := solo_reach hwf Rel' Bad F hstep
    (fun C D h => h.1.2.2 F hFZ) (h₁.append σ) (h₂.append σ) ⟨hrel, le_refl _, hqR⟩
  set C₁ := A.exec x (B₁ ++ σ ++ List.replicate n F) with hC₁
  have hFrep : ∀ q, q ≠ F → q ∉ List.replicate n F := fun q hq h =>
    hq (List.eq_of_mem_replicate h)
  have hlocR₁ : C₁.loc r = C₀.loc r := loc_exec_append (hFrep r (Ne.symm hFr))
  have hdist₁ : Dist s w C₁ r := ⟨kR, qR, kkR, hlocR₁ ▸ hactR, hits₁, hwR⟩
  have e₀ : ∀ B, A.exec x (B ++ (σ ++ List.replicate n F)) = A.exec x (B ++ σ ++ List.replicate n F) :=
    fun B => by rw [List.append_assoc]
  rcases hbad with hdF | hwF
  · -- a distinguishing read: execute it and constrain `F` no more
    have hrel₂ := hrel'.step_freeze hFZ (not_writeS_of_dist hdF)
    have hpot₂ := pot_step_lt hdF
    have e₁ : ∀ B, A.exec x (B ++ σ ++ (List.replicate n F ++ [F])) =
        (A.exec x (B ++ σ ++ List.replicate n F)).step F := fun B => by
      rw [← List.append_assoc, Alg.exec_concat]
    have e₁' : ∀ B, A.exec x (B ++ (σ ++ (List.replicate n F ++ [F]))) =
        (A.exec x (B ++ σ ++ List.replicate n F)).step F := fun B => by
      rw [← List.append_assoc, e₁]
    by_cases hd₂ : Dist s w (C₁.step F) r
    · obtain ⟨σ'', w', Z', h1, h2, h3, h4⟩ := ih
        (2 * pot w (stk (A.exec x (B₁ ++ (σ ++ (List.replicate n F ++ [F])))) s) +
          (if pend = none then 1 else 0))
        (by rw [← hN, e₁', ← hC₁]; split_ifs <;> omega)
        (σ ++ (List.replicate n F ++ [F])) w (insert F Z) pend rfl
        (by rw [e₁', e₁']; exact hrel₂)
        (by simp [Finset.mem_insert, hrZ, Ne.symm hFr])
        (by rw [e₁']; exact hd₂)
        (fun q hq => by
          obtain ⟨hqZ, hqr, hqW⟩ := hpend q hq
          have hqF : q ≠ F := fun e => hFpend (by rw [← e]; exact hq)
          refine ⟨by simp [hqZ, hqF], hqr, hqW.of_loc ?_⟩
          rw [← List.append_assoc, loc_exec_append (by simp [hqF])])
      refine ⟨List.replicate n F ++ [F] ++ σ'', w', Z', by simpa [List.append_assoc] using h1,
        h2, by simpa [List.append_assoc] using h3, ?_⟩
      intro h
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
      rcases h with (⟨-, h⟩ | h) | h
      exacts [hFr h.symm, hFr h.symm, h4 h]
    · refine ⟨List.replicate n F ++ [F], w, insert F Z, by rw [e₁, e₁]; exact hrel₂,
        by simp [Finset.mem_insert, hrZ, Ne.symm hFr], by rw [e₁]; exact hd₂, ?_⟩
      intro h
      simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at h
      rcases h with ⟨-, h⟩ | h
      exacts [hFr h.symm, hFr h.symm]
  · rcases hp : pend with _ | W
    · -- the first pending writer
      obtain ⟨σ'', w', Z', h1, h2, h3, h4⟩ := ih
        (2 * pot w (stk (A.exec x (B₁ ++ (σ ++ List.replicate n F))) s))
        (by rw [← hN, hp, e₀, ← hC₁]; simp only [ite_true]; omega)
        (σ ++ List.replicate n F) w Z (some F) (by simp)
        (by rw [e₀, e₀]; exact hrel')
        hrZ (by rw [e₀]; exact hdist₁)
        (fun q hq => by
          simp only [Option.some.injEq] at hq; subst hq
          exact ⟨hFZ, hFr, by rw [e₀]; exact hwF⟩)
      refine ⟨List.replicate n F ++ σ'', w', Z', by simpa [List.append_assoc] using h1, h2,
        by simpa [List.append_assoc] using h3, ?_⟩
      intro h
      simp only [List.mem_append, List.mem_replicate] at h
      rcases h with ⟨-, h⟩ | h
      exacts [hFr h.symm, h4 h]
    · -- two pending writers: execute both writes
      obtain ⟨hWZ, hWr, hWS⟩ := hpend W hp
      have hWF : W ≠ F := fun e => hFpend (by rw [hp, e])
      have hWS₁ : WriteS s C₁ W := hWS.of_loc (loc_exec_append (hFrep W hWF))
      have hrel₃ := hrel'.step_write hWZ hWS₁
      have hFS : WriteS s (C₁.step W) F := hwF.of_loc (loc_step_ne (Ne.symm hWF))
      have hrel₄ := hrel₃.step_write hFZ hFS
      have e₂ : ∀ B, A.exec x (B ++ σ ++ (List.replicate n F ++ [W, F])) =
          ((A.exec x (B ++ σ ++ List.replicate n F)).step W).step F := fun B => by
        rw [show B ++ σ ++ (List.replicate n F ++ [W, F]) =
          B ++ σ ++ List.replicate n F ++ [W] ++ [F] by simp, Alg.exec_concat, Alg.exec_concat]
      refine ⟨List.replicate n F ++ [W, F], w + 1 + 1, Z, by rw [e₂, e₂]; exact hrel₄, hrZ, ?_, ?_⟩
      · rw [e₂]
        rintro ⟨k', q', kk', hact', hq', hw'⟩
        have hloc : ((C₁.step W).step F).loc r = C₀.loc r := by
          rw [loc_step_ne (fun e => hFr e.symm), loc_step_ne hWr.symm, hlocR₁]
        have hact'' : A.act (((C₁.step W).step F).loc r) =
            .access (.inr s) (ISOp.read k') kk' := hact'
        rw [hloc, hactR] at hact''
        have hk' := act_read_inj hact''
        subst hk'
        have hk : kR < (stk C₁ s).its.length := by
          by_contra h; push Not at h; rw [List.getElem?_eq_none h] at hits₁; cases hits₁
        have e2 : (stk (C₁.step W) s).its[kR]? = some qR := by
          rw [its_step_of_not_read hk (fun kk h => by
            obtain ⟨v, kk'', hv⟩ := hWS₁; rw [hv] at h; cases h)]
          exact hits₁
        have hk₂ : kR < (stk (C₁.step W) s).its.length := by
          by_contra h; push Not at h; rw [List.getElem?_eq_none h] at e2; cases e2
        have e3 : (stk ((C₁.step W).step F) s).its[kR]? = some qR := by
          rw [its_step_of_not_read hk₂ (fun kk h => by
              obtain ⟨v, kk'', hv⟩ := hFS; rw [hv] at h; cases h)]
          exact e2
        have hq'' : (stk ((C₁.step W).step F) s).its[kR]? = some q' := hq'
        rw [e3] at hq''
        cases hq''
        unfold InWin at hw' hwR
        omega
      · intro h
        simp only [List.mem_append, List.mem_replicate, List.mem_cons, List.not_mem_nil,
          or_false] at h
        rcases h with ⟨-, h⟩ | h | h
        exacts [hFr h.symm, hWr h.symm, hFr h.symm]

omit hwf h₁ h₂ in
/-- A step of an unconstrained process that is not a distinguishing read keeps the
configurations related (the window moves if it is a write). -/
lemma Rel15.step_nondist {w : ℕ} {Z : Finset ℕ} {C D : Cfg A} {p : ℕ} (h : Rel15 s w Z C D)
    (hp : p ∉ Z) (hd : ¬ Dist s w C p) : ∃ w', Rel15 s w' Z (C.step p) (D.step p) := by
  by_cases hwr : WriteS s C p
  · exact ⟨w + 1, h.step_write hp hwr⟩
  · exact ⟨w, h.step_safe hp hd hwr⟩

omit hwf h₁ h₂ in
lemma exec_snoc (B σ : List ℕ) (p : ℕ) :
    A.exec x (B ++ σ ++ [p]) = (A.exec x (B ++ σ)).step p := Alg.exec_concat _ _ _

/-- **One round**: the victim `r` takes a step, and the configurations stay related. -/
lemma round {σ : List ℕ} {w : ℕ} {Z : Finset ℕ}
    (hrel : Rel15 s w Z (A.exec x (B₁ ++ σ)) (A.exec x (B₂ ++ σ))) (hrZ : r ∉ Z) :
    ∃ σ' w' Z', Rel15 s w' Z' (A.exec x (B₁ ++ σ ++ σ')) (A.exec x (B₂ ++ σ ++ σ')) ∧
      r ∉ Z' ∧ r ∈ σ' := by
  by_cases hd : Dist s w (A.exec x (B₁ ++ σ)) r
  · obtain ⟨σ₁, w₁, Z₁, h1, h2, h3, -⟩ := unblock hwf h₁ h₂ r _ σ w Z none rfl hrel hrZ hd
      (by simp)
    obtain ⟨w₂, h⟩ := h1.step_nondist h2 h3
    refine ⟨σ₁ ++ [r], w₂, Z₁, ?_, h2, by simp⟩
    rw [← List.append_assoc, ← List.append_assoc, exec_snoc, exec_snoc]
    exact h
  · obtain ⟨w₂, h⟩ := hrel.step_nondist hrZ hd
    exact ⟨[r], w₂, Z, by rw [exec_snoc, exec_snoc]; exact h, hrZ, by simp⟩

/-- A stage of the construction of Lemma 15. -/
structure Stage15 (A : Alg (ST B W) ℕ Bool Bool) (x : ℕ → Bool) (B₁ B₂ : List ℕ) (s : S)
    (r : ℕ) where
  /-- The common extension. -/
  σ : List ℕ
  /-- The window. -/
  w : ℕ
  /-- The constrained processes. -/
  Z : Finset ℕ
  rel : Rel15 s w Z (A.exec x (B₁ ++ σ)) (A.exec x (B₂ ++ σ))
  hr : r ∉ Z

omit hwf in
/-- **The infinite construction.** If the executions `B₁` (only `u`) and `B₂` (only `¬u`) are
related with the victim `r` unconstrained, then wait-freedom in the unbounded concurrency model
fails: `r` takes infinitely many steps without deciding. -/
theorem false_of_rel15 (hwfi : WaitFree A infArrival) {w : ℕ} {Z : Finset ℕ}
    (hrel : Rel15 s w Z (A.exec x B₁) (A.exec x B₂)) (hrZ : r ∉ Z) : False := by
  classical
  have hwf : WaitFree A (fun s => (Set.range s).Finite) := fun x s _ => hwfi x s trivial
  have hnext : ∀ St : Stage15 A x B₁ B₂ s r, ∃ St' : Stage15 A x B₁ B₂ s r, ∃ τ,
      St'.σ = St.σ ++ τ ∧ r ∈ τ := by
    intro St
    obtain ⟨τ, w', Z', h1, h2, h3⟩ := round hwf h₁ h₂ r St.rel St.hr
    exact ⟨⟨St.σ ++ τ, w', Z', by simpa [List.append_assoc] using h1, h2⟩, τ, rfl, h3⟩
  choose nxt τ hτ hrτ using hnext
  let S0 : Stage15 A x B₁ B₂ s r := ⟨[], w, Z, by simpa using hrel, hrZ⟩
  let st : ℕ → Stage15 A x B₁ B₂ s r := fun k => nxt^[k] S0
  have hsucc : ∀ k, (st (k + 1)).σ = (st k).σ ++ τ (st k) := fun k => by
    simp only [st, Function.iterate_succ_apply']; exact hτ _
  let f : ℕ → List ℕ := fun k => B₁ ++ (st k).σ
  have hsucc' : ∀ k, f (k + 1) = f k ++ τ (st k) := fun k => by
    simp only [f, hsucc, List.append_assoc]
  have hlen : ∀ k, k ≤ (f k).length := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih =>
      rw [hsucc', List.length_append]
      have := List.length_pos_of_ne_nil (List.ne_nil_of_mem (hrτ (st k)))
      omega
  obtain ⟨sch, hs⟩ := exists_seq_of_chain f
    (fun k => by rw [hsucc']; exact List.prefix_append _ _) hlen
  have hinf : InfOften sch r := by
    intro N
    have h1 := hs (N + 1)
    rw [hsucc', List.length_append, pre_add, hs N] at h1
    have h2 := List.append_cancel_left h1
    have h3 : r ∈ pre (fun t => sch ((f N).length + t)) (τ (st N)).length := by
      rw [h2]; exact hrτ (st N)
    obtain ⟨v, -, hsv⟩ := mem_pre.1 h3
    exact ⟨_ + v, by have := hlen N; omega, hsv⟩
  obtain ⟨t, v, hout⟩ := hwfi x sch trivial r hinf
  -- `r` outputs after stage `t + 1`, with the same local state in both executions
  set St := st (t + 1)
  have hout₁ : (A.exec x (B₁ ++ St.σ)).Out r v := by
    obtain ⟨ρ, hρ⟩ := pre_prefix sch (le_trans (Nat.le_succ t) (hlen (t + 1)))
    rw [hs (t + 1)] at hρ
    show (A.exec x (f (t + 1))).Out r v
    rw [← hρ, Alg.exec_append]
    exact Alg.Cfg.Out.run hout ρ
  have hout₂ : (A.exec x (B₂ ++ St.σ)).Out r v := by
    unfold Cfg.Out; rw [← St.rel.2.2 r St.hr]; exact hout₁
  have hrσ : r ∈ St.σ := by
    simp only [St, hsucc]; exact List.mem_append_right _ (hrτ _)
  exact false_of_out_both h₁ h₂ hrσ hrσ hout₁ hout₂

end Construction

/-- **Lemma 15** of [AMW11]. If after `α a b` only `u` and after `α b a` only `¬u` can be
decided, then `a` and `b` are not both poised to write to the same iterator stack (in the
unbounded concurrency model). -/
theorem lemma_15 (hwfi : WaitFree A infArrival) {x : ℕ → Bool} {α : List ℕ} {a b : ℕ} {u : Bool}
    (h₁ : Uni A x (α ++ [a, b]) u) (h₂ : Uni A x (α ++ [b, a]) (!u)) (hab : a ≠ b) {s : S}
    {va vb : W s} {ka kb : ISResp (W s) → A.L}
    (ha : A.act ((A.exec x α).loc a) = .access (.inr s) (ISOp.write va) ka)
    (hb : A.act ((A.exec x α).loc b) = .access (.inr s) (ISOp.write vb) kb) : False := by
  set C := A.exec x α with hC
  have e1 : A.exec x (α ++ [a, b]) = (C.step a).step b := by
    rw [show α ++ [a, b] = α ++ [a] ++ [b] by simp, Alg.exec_concat, Alg.exec_concat]
  have e2 : A.exec x (α ++ [b, a]) = (C.step b).step a := by
    rw [show α ++ [b, a] = α ++ [b] ++ [a] by simp, Alg.exec_concat, Alg.exec_concat]
  have hb' : A.act ((C.step a).loc b) = .access (.inr s) (ISOp.write vb) kb := by
    rw [loc_step_ne (Ne.symm hab)]; exact hb
  have ha' : A.act ((C.step b).loc a) = .access (.inr s) (ISOp.write va) ka := by
    rw [loc_step_ne hab]; exact ha
  obtain ⟨r, hr⟩ := exists_fresh (α ++ [a, b])
  have hra : r ≠ a := fun e => hr (by simp [e])
  have hrb : r ≠ b := fun e => hr (by simp [e])
  refine false_of_rel15 h₁ h₂ r hwfi (s := s) (w := 0) (Z := {a, b}) ?_ (by simp [hra, hrb])
  rw [e1, e2]
  refine ⟨fun j hj => ?_, ?_, fun p hp => ?_⟩
  · rw [Arrival.Cfg.step_mem_other hb' hj, Arrival.Cfg.step_mem_other ha hj,
      Arrival.Cfg.step_mem_other ha' hj, Arrival.Cfg.step_mem_other hb hj]
  · unfold stk stkM
    rw [Arrival.Cfg.step_mem_self_of_access hb', Arrival.Cfg.step_mem_self_of_access ha,
      Arrival.Cfg.step_mem_self_of_access ha', Arrival.Cfg.step_mem_self_of_access hb]
    refine ⟨by simp, fun k => ?_⟩
    rcases k with _ | _ | k
    · simp
    · simp
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      simp
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    rw [loc_step_ne hp.2, loc_step_ne hp.1, loc_step_ne hp.1, loc_step_ne hp.2]

end Podc.UnboundedConcurrency
