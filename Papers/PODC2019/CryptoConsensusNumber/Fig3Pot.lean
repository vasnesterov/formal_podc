import Papers.PODC2019.CryptoConsensusNumber.Fig3Lin

/-!
# Figure 3: a potential for wait-freedom

Fix a process `p` executing the loop for its transfer `tx` (account `a = tx.a`), and assume
`tx` is undecided. The potential

`Φ_M = Σ_q β_q + (n·(tx.r + 1) − Ψ) + Δ_M`

never increases, where

* `β_q` is the number of tuples a process `q` that collected `R_a` *without* seeing `tx`
  can still get decided (`|collected|`, plus the registers still to be read);
* `Ψ` counts the "slots" `(originator, round ≤ tx.r)` of decided tuples of account `a`
  (a process that saw `tx` proposes a tuple at least as old as `tx`, which fills a new slot);
* `Δ_M` is the number of decided rounds `< M` of account `a`.

Every first proposal to some `kC_a[r]` increases `Δ_M` by at most one and decreases one of
the other two terms.
-/

set_option linter.unusedSectionVars false

namespace CryptoCons.Fig3

open Cslib.SharedMemory

set_option allowUnsafeReducibility true in
attribute [local reducible] atSpec snapObj kConsObj

variable {n : ℕ} {Acct : Type} [DecidableEq Acct] {μ : Acct → Finset (Fin n)} {q₀ : Acct → ℕ}
  {k : ℕ}

section Pot

variable (p : Fin n) (tx : Tx n Acct)

/-- The potential of a process `q`: positive only if `q` is looping (or collecting) for the
account of `tx` without having seen `tx`. -/
def beta (l : Loc n Acct) : ℕ :=
  match l.pc with
  | .coll tx' i acc =>
    if tx'.a = tx.a ∧ p.val < i.val ∧ tx ∉ acc then acc.card + (n - i.val) else 0
  | .snap tx' c => if tx'.a = tx.a ∧ tx ∉ c ∧ tx ∉ l.com tx.a then c.card else 0
  | .prop tx' c _ => if tx'.a = tx.a ∧ tx ∉ c ∧ tx ∉ l.com tx.a then c.card else 0
  | .upd tx' c d => if tx'.a = tx.a ∧ tx ∉ c ∧ tx ∉ l.com tx.a then
      (c \ Option.toFinset (Option.map Prod.fst d)).card else 0
  | _ => 0

open Classical in
/-- Number of filled slots `(originator, round ≤ tx.r)` among the decided tuples of `tx.a`. -/
noncomputable def Psi (m : Mem n Acct k) : ℕ :=
  (Finset.univ.filter (fun sr : Fin n × Fin (tx.r + 1) =>
    ∃ r t b, Dec m tx.a r = some (t, b) ∧ t.p = sr.1 ∧ t.r = sr.2.val)).card

/-- Number of decided rounds `< M` of account `tx.a`. -/
def Delta (M : ℕ) (m : Mem n Acct k) : ℕ :=
  ((Finset.range M).filter (fun r => Dec m tx.a r ≠ none)).card

/-- The potential. -/
noncomputable def Phi (M : ℕ) (C : Cfg μ q₀ k) : ℕ :=
  ∑ q, beta p tx (C.loc q) + (n * (tx.r + 1) - Psi tx C.mem) + Delta tx M C.mem

end Pot

/-! ## Basic properties -/

lemma Psi_le (tx : Tx n Acct) (m : Mem n Acct k) : Psi tx m ≤ n * (tx.r + 1) := by
  unfold Psi
  calc _ ≤ (Finset.univ : Finset (Fin n × Fin (tx.r + 1))).card := Finset.card_le_card (by simp)
    _ = n * (tx.r + 1) := by simp

lemma Psi_mono (tx : Tx n Acct) {m m' : Mem n Acct k}
    (h : ∀ r d, Dec m tx.a r = some d → Dec m' tx.a r = some d) :
    Psi tx m ≤ Psi tx m' := by
  unfold Psi
  apply Finset.card_le_card
  intro sr hsr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsr ⊢
  obtain ⟨r, t, b, h1, h2, h3⟩ := hsr
  exact ⟨r, t, b, h _ _ h1, h2, h3⟩

lemma Psi_lt (tx : Tx n Acct) {m m' : Mem n Acct k}
    (h : ∀ r d, Dec m tx.a r = some d → Dec m' tx.a r = some d)
    (s : Fin n × Fin (tx.r + 1))
    (hs : ¬ ∃ r t b, Dec m tx.a r = some (t, b) ∧ t.p = s.1 ∧ t.r = s.2.val)
    (hs' : ∃ r t b, Dec m' tx.a r = some (t, b) ∧ t.p = s.1 ∧ t.r = s.2.val) :
    Psi tx m < Psi tx m' := by
  unfold Psi
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨s, by simpa using hs', by simpa using hs⟩
  · intro sr hsr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hsr ⊢
    obtain ⟨r, t, b, h1, h2, h3⟩ := hsr
    exact ⟨r, t, b, h _ _ h1, h2, h3⟩

lemma Delta_le_succ (tx : Tx n Acct) (M : ℕ) {m m' : Mem n Acct k} (r₀ : ℕ)
    (h : ∀ r, r ≠ r₀ → Dec m' tx.a r = Dec m tx.a r) :
    Delta tx M m' ≤ Delta tx M m + 1 := by
  unfold Delta
  calc _ ≤ (insert r₀ ((Finset.range M).filter (fun r => Dec m tx.a r ≠ none))).card := by
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert] at hr ⊢
        by_cases hr0 : r = r₀
        · exact Or.inl hr0
        · exact Or.inr ⟨hr.1, by rw [← h r hr0]; exact hr.2⟩
    _ ≤ _ := Finset.card_insert_le _ _

lemma Delta_eq (tx : Tx n Acct) (M : ℕ) {m m' : Mem n Acct k}
    (h : ∀ r, Dec m' tx.a r = Dec m tx.a r) : Delta tx M m' = Delta tx M m := by
  unfold Delta; congr 1; exact Finset.filter_congr (fun r _ => by rw [h])

lemma Psi_eq (tx : Tx n Acct) {m m' : Mem n Acct k}
    (h : ∀ r, Dec m' tx.a r = Dec m tx.a r) : Psi tx m' = Psi tx m := by
  exact le_antisymm (Psi_mono tx (fun r d hd => by rw [h] at hd; exact hd))
    (Psi_mono tx (fun r d hd => by rw [h]; exact hd))

lemma sum_update_le {f : Fin n → ℕ} (s : Fin n) {v i j : ℕ} (h : v + i ≤ f s + j) :
    ∑ q, Function.update f s v q + i ≤ ∑ q, f q + j := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ s), Finset.sdiff_singleton_eq_erase,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  omega

lemma sum_beta_update (p : Fin n) (tx : Tx n Acct) (C : Cfg μ q₀ k) (s : Fin n)
    (l' : Loc n Acct) (i j : ℕ) (h : beta p tx l' + i ≤ beta p tx (C.loc s) + j) :
    ∑ q, beta p tx (Function.update C.loc s l' q) + i ≤ ∑ q, beta p tx (C.loc q) + j := by
  have e : (fun q => beta p tx (Function.update C.loc s l' q)) =
      Function.update (fun q => beta p tx (C.loc q)) s (beta p tx l') := by
    funext q; by_cases hq : q = s
    · subst hq; simp
    · simp [Function.update_of_ne hq]
  rw [show (∑ q, beta p tx (Function.update C.loc s l' q)) =
    ∑ q, Function.update (fun q => beta p tx (C.loc q)) s (beta p tx l') q from by rw [← e]]
  exact sum_update_le s h

/-- Steps that do not change the decisions of `tx.a` and do not increase the stepper's
potential. -/
lemma Phi_le_of_local (p : Fin n) (tx : Tx n Acct) (M : ℕ) (C : Cfg μ q₀ k) (s : Fin n)
    (l' : Loc n Acct) (pd : Fin n → Option (ATOp (Fin n) Acct)) (m' : Mem n Acct k)
    (hDec : ∀ r, Dec m' tx.a r = Dec C.mem tx.a r) (hb : beta p tx l' ≤ beta p tx (C.loc s)) :
    Phi p tx M (⟨Function.update C.loc s l', pd, m'⟩ : Cfg μ q₀ k) ≤ Phi p tx M C := by
  unfold Phi
  simp only
  rw [Psi_eq tx hDec, Delta_eq tx M hDec]
  have := sum_beta_update p tx C s l' 0 0 (by simpa using hb)
  omega

/-! ## β along the transitions -/

section Beta

variable (p : Fin n) (tx : Tx n Acct)

lemma beta_coll (l : Loc n Acct) (tx' : Tx n Acct) (i : Fin n) (acc : Finset (Tx n Acct))
    (v : Option (Tx n Acct)) (hpc : l.pc = .coll tx' i acc)
    (hv : tx'.a = tx.a → i = p → v = some tx)
    (hlast : ¬ i.val + 1 < n → tx' ∈ (acc ∪ Option.toFinset v) \ l.com tx'.a) :
    beta p tx (if h : i.val + 1 < n then
        { l with pc := .coll tx' ⟨i.val + 1, h⟩ (acc ∪ Option.toFinset v) }
      else { l with pc := loopCheck tx' ((acc ∪ Option.toFinset v) \ l.com tx'.a) l.hist }) ≤
      beta p tx l := by
  have hcard : (acc ∪ Option.toFinset v).card ≤ acc.card + 1 := by
    calc _ ≤ acc.card + (Option.toFinset v).card := Finset.card_union_le _ _
      _ ≤ acc.card + 1 := by cases v <;> simp
  have hi := i.isLt
  by_cases hin : i.val + 1 < n
  · simp only [hin, dite_true, beta, hpc]
    split_ifs with h1 h2 h2
    · omega
    · obtain ⟨ha, hpi, htx⟩ := h1
      have hpi' : p.val < i.val := by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hpi with h | h
        · exact h
        · exfalso; have := hv ha (Fin.ext h.symm); rw [this] at htx; simp at htx
      have : tx ∉ acc := fun h => htx (Finset.mem_union_left _ h)
      exact absurd ⟨ha, hpi', this⟩ h2
    · exact Nat.zero_le _
    · exact le_rfl
  · simp only [hin, dite_false, beta, hpc]
    have hmem := hlast hin
    have hlc : loopCheck tx' ((acc ∪ Option.toFinset v) \ l.com tx'.a) l.hist =
        .snap tx' ((acc ∪ Option.toFinset v) \ l.com tx'.a) := by simp [loopCheck, hmem]
    rw [hlc]
    simp only
    split_ifs with h1 h2 h2
    · calc _ ≤ (acc ∪ Option.toFinset v).card := Finset.card_le_card Finset.sdiff_subset
        _ ≤ acc.card + 1 := hcard
        _ ≤ _ := by omega
    · exfalso
      obtain ⟨ha, htxc, htxcom⟩ := h1
      apply h2
      refine ⟨ha, ?_, ?_⟩
      · have : p.val ≤ i.val := by have := p.isLt; omega
        rcases Nat.lt_or_eq_of_le this with h | h
        · exact h
        · exfalso; have := hv ha (Fin.ext h.symm)
          apply htxc; rw [Finset.mem_sdiff]; rw [ha]
          exact ⟨Finset.mem_union_right _ (by simp [this]), htxcom⟩
      · intro h; apply htxc; rw [Finset.mem_sdiff, ha]
        exact ⟨Finset.mem_union_left _ h, htxcom⟩
    · exact Nat.zero_le _
    · exact le_rfl

lemma beta_upd (l : Loc n Acct) (tx' : Tx n Acct) (c : Finset (Tx n Acct))
    (d : Option (Tx n Acct × Bool)) (hpc : l.pc = .upd tx' c d) :
    beta p tx (updLoc l tx' c d) ≤ beta p tx l := by
  set D := Option.toFinset (Option.map Prod.fst d) with hD
  have hpc' : (updLoc l tx' c d).pc = loopCheck tx' (c \ (l.com tx'.a ∪ D)) l.hist := rfl
  by_cases hin : tx' ∈ c \ (l.com tx'.a ∪ D)
  · have h1 : (updLoc l tx' c d).pc = .snap tx' (c \ (l.com tx'.a ∪ D)) := by
      rw [hpc']; simp [loopCheck, hin]
    unfold beta; rw [h1, hpc]; simp only
    by_cases h4 : tx'.a = tx.a ∧ tx ∉ c \ (l.com tx'.a ∪ D) ∧ tx ∉ (updLoc l tx' c d).com tx.a
    · rw [ite_eq_left h4]
      obtain ⟨ha, htx1, htx2⟩ := h4
      have hcom : (updLoc l tx' c d).com tx.a = l.com tx.a ∪ D := by
        simp [updLoc, ← ha, hD]
      rw [hcom, Finset.mem_union, not_or] at htx2
      have hold : tx'.a = tx.a ∧ tx ∉ c ∧ tx ∉ l.com tx.a := by
        refine ⟨ha, fun h => htx1 ?_, htx2.1⟩
        rw [Finset.mem_sdiff, ha, Finset.mem_union, not_or]; exact ⟨h, htx2.1, htx2.2⟩
      rw [ite_eq_left hold]
      exact Finset.card_le_card (by
        intro t ht
        simp only [Finset.mem_sdiff, Finset.mem_union, not_or] at ht ⊢
        exact ⟨ht.1, ht.2.2⟩)
    · rw [ite_eq_right h4]; exact Nat.zero_le _
  · have h1 : (updLoc l tx' c d).pc = .ret (.inl (decide ((tx', true) ∈ l.hist))) := by
      rw [hpc']; simp [loopCheck, hin]
    unfold beta; rw [h1]; exact Nat.zero_le _

end Beta

/-! ## The potential does not increase -/

lemma PC.posted_of_loopC {pc : PC n Acct} {tx : Tx n Acct} {c : Finset (Tx n Acct)}
    (h : pc.loopC = some (tx, c)) : pc.posted = some tx := by
  cases pc <;> simp_all [PC.loopC, PC.posted]

lemma Tx.r_le_of_key_le {t t' : Tx n Acct} (h : t.key ≤ t'.key) : t.r ≤ t'.r := by
  unfold Tx.key at h
  rcases Prod.Lex.toLex_le_toLex.1 h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

section PhiStep

variable {C : Cfg μ q₀ k} {K : Set (Tx n Acct)} {p : Fin n} {tx : Tx n Acct}
  {c₀ : Finset (Tx n Acct)}

lemma phi_prop (hM : MInv μ C K) (hund : ∀ r b, Dec C.mem tx.a r ≠ some (tx, b)) (M : ℕ)
    {q : Fin n} {tx' : Tx n Acct} {c : Finset (Tx n Acct)} {pr : Tx n Acct × Bool}
    (hpc : (C.loc q).pc = .prop tx' c pr) :
    Phi p tx M (propCfg C q tx' c pr) ≤ Phi p tx M C := by
  have hq := hM.proc q
  obtain ⟨hprc, hkey⟩ := hq.prop tx' c pr hpc
  obtain ⟨-, hcK⟩ := hq.loop tx' c (by simp [hpc, PC.loopC])
  set a' := tx'.a with ha'
  set ρ := (C.loc q).rnd a' with hρ
  set dn := (Dec C.mem a' ρ).getD pr with hdn
  set l' : Loc n Acct := { C.loc q with pc := .upd tx' c (some dn), hist := (C.loc q).hist ∪ {dn} }
    with hl'
  have hDec' : ∀ r, Dec (propCfg C q tx' c pr).mem tx.a r =
      if (tx.a, r) = (a', ρ) then some dn else Dec C.mem tx.a r := by
    intro r; simp only [propCfg, Dec, KC_update_KC]; split_ifs <;> rfl
  have hext : ∀ r d, Dec C.mem tx.a r = some d → Dec (propCfg C q tx' c pr).mem tx.a r = some d := by
    intro r d h; rw [hDec']; split_ifs with he
    · simp only [Prod.mk.injEq] at he; rw [he.1, he.2] at h; simp [hdn, h]
    · exact h
  have hbeta : beta p tx l' + (if tx'.a = tx.a ∧ tx ∉ c ∧ tx ∉ (C.loc q).com tx.a then
      (if dn.1 ∈ c then 1 else 0) else 0) ≤ beta p tx (C.loc q) := by
    unfold beta; rw [hpc]; simp only [hl']
    split_ifs with h1 h2
    · have hsub : {dn.1} ⊆ c := by simpa using h2
      have h3 := Finset.card_sdiff_add_card_eq_card hsub
      rw [Finset.card_singleton] at h3
      simp only [Option.map_some, Option.toFinset_some]
      omega
    · simp only [Option.map_some, Option.toFinset_some, add_zero]
      exact Finset.card_le_card Finset.sdiff_subset
    · simp
  have hloc : (propCfg C q tx' c pr).loc = Function.update C.loc q l' := rfl
  by_cases hfirst : tx'.a = tx.a ∧ Dec C.mem a' ρ = none
  · obtain ⟨ha, hnone⟩ := hfirst
    have hdnpr : dn = pr := by simp [hdn, hnone]
    have hDel := Delta_le_succ tx M (m := C.mem) (m' := (propCfg C q tx' c pr).mem) ρ
      (fun r hr => by rw [hDec', ite_eq_right (by simp [ha, hr])])
    have hPsi := Psi_mono tx hext
    have hPsiN := Psi_le tx (propCfg C q tx' c pr).mem
    unfold Phi
    rw [hloc]
    by_cases hbad : tx'.a = tx.a ∧ tx ∉ c ∧ tx ∉ (C.loc q).com tx.a
    · rw [ite_eq_left hbad, hdnpr, ite_eq_left hprc] at hbeta
      have := sum_beta_update p tx C q l' 1 0 (by simpa using hbeta)
      omega
    · rw [ite_eq_right hbad] at hbeta
      have htxc : tx ∈ c := by
        by_contra htxc
        apply hbad
        refine ⟨ha, htxc, fun hcom => ?_⟩
        obtain ⟨r, -, b, hb⟩ := (hq.com tx.a tx).1 hcom
        exact hund r b hb
      have hrr : pr.1.r ≤ tx.r := Tx.r_le_of_key_le (hkey tx htxc)
      have hlt := Psi_lt tx hext (pr.1.p, ⟨pr.1.r, by omega⟩)
        (by
          rintro ⟨r, t, b, h1, h2, h3⟩
          obtain ⟨htK, hta⟩ := hM.decK _ _ _ _ h1
          obtain ⟨hprK, hpra, -⟩ := hcK pr.1 hprc
          have := hM.kInj t htK pr.1 hprK (by rw [hta, hpra, ha', ha]) h2 h3
          subst this
          exact hM.undec_of_loop (by simp [hpc, PC.loopC]) hprc hnone r b
            (by rw [hpra, ha', ha]; exact h1))
        ⟨ρ, pr.1, pr.2, by rw [hDec', ite_eq_left (by rw [ha', ha]), hdnpr], rfl, rfl⟩
      have := sum_beta_update p tx C q l' 0 0 (by simpa using hbeta)
      omega
  · have hsame : ∀ r, Dec (propCfg C q tx' c pr).mem tx.a r = Dec C.mem tx.a r := by
      intro r; rw [hDec']; split_ifs with he
      · simp only [Prod.mk.injEq] at he
        have ha : tx'.a = tx.a := he.1.symm
        have hnn : Dec C.mem a' ρ ≠ none := fun h => hfirst ⟨ha, h⟩
        obtain ⟨d0, hd0⟩ := Option.ne_none_iff_exists'.1 hnn
        rw [he.1, he.2, hd0]; simp [hdn, hd0]
      · rfl
    have := Phi_le_of_local p tx M C q l' (propCfg C q tx' c pr).pend
      (propCfg C q tx' c pr).mem hsame (by omega)
    exact this

/-- The potential does not increase along any step, as long as `p` is in the loop for `tx`
and `tx` is undecided. -/
lemma phi_step (hk : KShared μ k) (hM : MInv μ C K) (hp : (C.loc p).pc.loopC = some (tx, c₀))
    (hund : ∀ r b, Dec C.mem tx.a r ≠ some (tx, b)) (M : ℕ) {C' : Cfg μ q₀ k}
    (ℓ : Label (Fin n) (AT μ q₀)) (h : (impl μ q₀ k).step C ℓ = some C') :
    Phi p tx M C' ≤ Phi p tx M C := by
  cases ℓ with
  | inv q o =>
    obtain ⟨h0, ha, -⟩ := Impl.step_inv h
    rw [step_inv_eq o h0 ha] at h
    cases h
    apply Phi_le_of_local p tx M C q _ _ C.mem (fun _ => rfl)
    have : beta p tx ((impl μ q₀ k).invoke q (C.loc q) o) = 0 := by
      cases o with
      | read a => simp [impl, beta]
      | transfer p' a b x =>
        simp only [impl]; split_ifs <;> simp [beta]
    rw [this]; exact Nat.zero_le _
  | ret q r =>
    obtain ⟨h0, hpc, rfl⟩ := step_ret_eq h (fun hi => (hM.proc q).idle.2 hi)
    exact Phi_le_of_local p tx M C q _ _ C.mem (fun _ => rfl) (by simp [beta])
  | tau q =>
    have h0 := (Impl.step_tau h).1
    have hq := hM.proc q
    cases hpc : (C.loc q).pc with
    | idle => rw [step_tau_idle_none hpc] at h; cases h
    | ret r => rw [step_tau_ret_none r hpc] at h; cases h
    | rscan a =>
      rw [step_rscan a h0 hpc] at h; cases h
      exact Phi_le_of_local p tx M C q _ _ C.mem (fun _ => rfl) (by simp [beta])
    | write tx' =>
      rw [step_write tx' h0 hpc] at h; cases h
      exact Phi_le_of_local p tx M C q _ _ _ (fun r => Dec_update_Reg _ _ _ r) (by simp [beta])
    | coll tx' i acc =>
      rw [step_coll tx' i acc h0 hpc] at h; cases h
      refine Phi_le_of_local p tx M C q _ _ C.mem (fun _ => rfl) ?_
      have hreg : Reg C.mem tx.a p = some tx :=
        (hM.proc p).reg tx (PC.posted_of_loopC hp)
      exact beta_coll p tx (C.loc q) tx' i acc _ hpc
        (fun ha hi => by rw [ha, hi]; exact hreg) (fun hi => hM.coll_last hpc hi)
    | snap tx' c =>
      rw [step_snap tx' c h0 hpc] at h; cases h
      refine Phi_le_of_local p tx M C q _ _ C.mem (fun _ => rfl) ?_
      unfold beta; rw [hpc]
    | prop tx' c pr =>
      rw [step_prop' h0 hpc (hM.cnt_lt hk hpc)] at h; cases h
      exact phi_prop hM hund M hpc
    | upd tx' c d =>
      rw [step_upd tx' c d h0 hpc] at h; cases h
      exact Phi_le_of_local p tx M C q _ _ _ (fun r => Dec_update_AS _ _ _)
        (beta_upd p tx (C.loc q) tx' c d hpc)

end PhiStep

end CryptoCons.Fig3
