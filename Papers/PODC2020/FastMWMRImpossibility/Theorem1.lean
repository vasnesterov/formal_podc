import Papers.PODC2020.FastMWMRImpossibility.Executions
import Papers.PODC2020.FastMWMRImpossibility.Lin

/-!
# Theorem 1: no fast-write (W1R2) multi-writer atomic register

The chain argument of §3 of the paper, made rigorous. Let `w₁ ≠ w₂` be writers writing `a ≠ b`
and `r₁ ≠ r₂` readers.

* **Atomicity facts** (`ret_agree`, `ret_seq₁₂`, `ret_seq₂₁`): in every execution of
  `Executions.lean`, both reads return the same value; if `W₁` precedes `W₂` (resp. `W₂` precedes
  `W₁`), they return `b` (resp. `a`).
* **Phase 1 (chain `α`).** `F i` = value returned by `r₁` when servers `s < i` received `W₂`
  first and the others `W₁` first, and the second round of `r₁` is not disturbed by `r₂`. Note
  that the first round-trip of `r₂` *is* part of these executions: it is a blind message (its
  content is fixed), so including it costs nothing and removes the need for the "sieve" of §4.
  `F 0 = b`, `F n = a`, so there is a critical server `c` with `F c ≠ F (c + 1)`.
* **Phase 2 (chain `β`).** `β_k(x)`: the second-round message of `r₂` reaches the servers
  `s < k` before the one of `r₁`, never reaches `c`, and `r₂` does not use the first-round reply
  of `c`. At `k = n`, `r₂` cannot distinguish the two write orders at `c`.
* **Phase 3 (zigzag chain).** `β_k ≈ temp_k ≈ γ_k = γ'_k ≈ temp'_k ≈ β_{k+1}`.
-/

namespace Podc.FastMWMR

open Cslib.SharedMemory Cslib.AsyncMP

variable {n : ℕ} {W R V Msg Rep LW LR : Type}
variable [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep]
variable (A : W1R2Alg n W R V Msg Rep LW LR) (t : ℕ) (v₀ : V)

namespace W1R2Alg

/-! ### Atomicity facts -/

section Atomicity

variable {w₁ w₂ : W} {r₁ r₂ : R} (hw : w₁ ≠ w₂) (hr : r₁ ≠ r₂) (a b : V)

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
lemma tail_reads [DecidableEq W] [DecidableEq R] (v₁ v₂ : V) (p : Node n W R) :
    ∀ o ∈ opsOf ([.inv (.rd r₁) .read, .inv (.rd r₂) .read, .ret (.rd r₁) v₁, .ret (.rd r₂) v₂] :
      List (Label (Node n W R) (register V v₀))) p, o = .read := by
  intro o ho
  simp only [opsOf_cons, opsOf_nil, Label.invOf_inv, Label.invOf_ret] at ho
  split_ifs at ho <;> simp_all

include hw hr in
/-- In the concurrent executions, both reads return the same value. -/
lemma ret_agree (hlin : (A.protocol t v₀).Linearizable) (x : Fin n → Bool) (j : Option (Fin n))
    (pat : Fin n → Pat) (hv : ReadValid n t j pat) :
    A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) j pat = A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b x) j pat := by
  obtain ⟨C, hR, hc, hs, hrd⟩ := A.reach_writes_conc t v₀ (R := R) hw a b x
  obtain ⟨C', hR'⟩ := A.reach_reads t v₀ hR hc hr _ hs (hrd r₁) (hrd r₂) j pat hv
  obtain ⟨L, hL⟩ := hlin _ _ hR'
  have hww : (Node.wr w₁ : Node n W R) ≠ .wr w₂ := by simpa using hw
  have hrr : (Node.rd r₁ : Node n W R) ≠ .rd r₂ := by simpa using hr
  have key : ∀ (r : R) (v : V),
      opsOf ([.inv (.rd r₁) .read, .inv (.rd r₂) .read, .ret (.rd r₁) (A.ret₁ r₁ r₂
        (A.wlog w₁ w₂ a b x) j pat), .ret (.rd r₂) (A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b x) j pat)] :
        List (Label (Node n W R) (register V v₀))) (.rd r) = [.read] →
      respsOf ([.inv (.rd r₁) .read, .inv (.rd r₂) .read, .ret (.rd r₁) (A.ret₁ r₁ r₂
        (A.wlog w₁ w₂ a b x) j pat), .ret (.rd r₂) (A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b x) j pat)] :
        List (Label (Node n W R) (register V v₀))) (.rd r) = [v] →
      v = linState (A := register V v₀) L := fun r v hop hres =>
    resp_eq_of_writes_first (w₁ := .wr w₁) (w₂ := .wr w₂) (a := a) (b := b)
      (by simp [hw.symm]) (by simp [hw])
      (fun p h1 h2 => by simp [Ne.symm h1, Ne.symm h2])
      (by simp) (by simp) (fun p => tail_reads v₀ _ _ p) (by simp) (by simp) (by simp) hop hres hL
  rw [key r₁ (A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) j pat) (by simp [hr.symm]) (by simp [hr.symm]),
    key r₂ (A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b x) j pat) (by simp [hr]) (by simp [hr])]

include hr in
/-- If the write of `wA` precedes the write of `wB` in real time, both reads return the value
written by `wB`. -/
lemma ret_seq (hlin : (A.protocol t v₀).Linearizable) {wA wB : W} (hAB : wA ≠ wB) (u u' : V)
    (j : Option (Fin n)) (pat : Fin n → Pat) (hv : ReadValid n t j pat) :
    A.ret₁ r₁ r₂ (fun s => [(.wr wA, A.wMsg wA (A.initW wA) u s),
      (.wr wB, A.wMsg wB (A.initW wB) u' s)]) j pat = u' := by
  have hAB' : (Node.wr wB : Node n W R) ≠ .wr wA := by simpa using hAB.symm
  set ℓ : Fin n → List (Node n W R × Msg) := fun s => [(.wr wA, A.wMsg wA (A.initW wA) u s),
      (.wr wB, A.wMsg wB (A.initW wB) u' s)] with hℓ
  obtain ⟨C₁, hR₁, hc₁, hs₁, ho₁⟩ := A.reach_write_solo t v₀ Protocol.Reach.init rfl u
    (w := wA) (st := A.initW wA) (k := 0) rfl (fun _ => []) (fun _ => rfl)
  obtain ⟨C₂, hR₂, hc₂, hs₂, ho₂⟩ := A.reach_write_solo t v₀ hR₁ hc₁ u'
    (w := wB) (st := A.initW wB) (k := 0) (by rw [ho₁ _ (by simp) hAB']; rfl) _ hs₁
  obtain ⟨C', hR'⟩ := A.reach_reads t v₀ hR₂ hc₂ hr ℓ (fun s => by simp [hs₂ s, ℓ])
    (by rw [ho₂ _ (by simp) (by simp), ho₁ _ (by simp) (by simp)]; rfl)
    (by rw [ho₂ _ (by simp) (by simp), ho₁ _ (by simp) (by simp)]; rfl) j pat hv
  simp only [List.nil_append, List.cons_append] at hR'
  obtain ⟨L, hL⟩ := hlin _ _ (by
    rw [show ∀ l : List (Label (Node n W R) (register V v₀)),
      Label.inv (Node.wr wA) (RWOp.write u) :: Label.ret (Node.wr wA) u ::
        Label.inv (Node.wr wB) (RWOp.write u') :: Label.ret (Node.wr wB) u' :: l =
      [Label.inv (Node.wr wA) (RWOp.write u), Label.ret (Node.wr wA) u,
        Label.inv (Node.wr wB) (RWOp.write u'), Label.ret (Node.wr wB) u'] ++ l from
      fun _ => rfl] at hR'
    exact hR')
  have h₁ : opsOf ([.inv (.wr wA) (.write u), .ret (.wr wA) u, .inv (.wr wB) (.write u'),
      .ret (.wr wB) u'] : List (Label (Node n W R) (register V v₀))) (.wr wA) = [.write u] := by
    simp [hAB.symm]
  have h₂ : opsOf ([.inv (.wr wA) (.write u), .ret (.wr wA) u, .inv (.wr wB) (.write u'),
      .ret (.wr wB) u'] : List (Label (Node n W R) (register V v₀))) (.wr wB) = [.write u'] := by
    simp [hAB]
  have hO : ∀ p, p ≠ .wr wA → p ≠ .wr wB → opsOf ([.inv (.wr wA) (.write u), .ret (.wr wA) u,
      .inv (.wr wB) (.write u'), .ret (.wr wB) u'] : List (Label (Node n W R) (register V v₀)))
      p = [] := fun p h1 h2 => by simp [Ne.symm h1, Ne.symm h2]
  have hT := fun p => tail_reads v₀ (r₁ := r₁) (r₂ := r₂) (W := W) (n := n)
    (A.ret₁ r₁ r₂ ℓ j pat) (A.ret₂ r₁ r₂ ℓ j pat) p
  rw [resp_eq_of_writes_first h₁ h₂ hO (by simp) (by simp) hT (r := .rd r₁) (by simp) (by simp)
    (by simp) (by simp [hr.symm]) (v := A.ret₁ r₁ r₂ ℓ j pat) (by simp [hr.symm]) hL]
  refine linState_eq_of_last_write (x := (.wr wB, 0)) hL (by simp [opOf, hAB]) (by simp [Completed])
    (fun z hz hzw hne => ?_)
  rcases write_id_of_mem h₁ h₂ hO hT hL hz hzw with h | h
  · rw [h]
    refine ⟨[.inv (.wr wA) (.write u), .ret (.wr wA) u], [.inv (.wr wB) (.write u'),
      .ret (.wr wB) u', .inv (.rd r₁) .read, .inv (.rd r₂) .read, .ret (.rd r₁) (A.ret₁ r₁ r₂ ℓ j pat),
      .ret (.rd r₂) (A.ret₂ r₁ r₂ ℓ j pat)], by simp, by simp [Completed], ?_⟩
    simp [Invoked, hAB]
  · exact absurd h hne

end Atomicity

/-! ### Indistinguishability: what each reader's returned value depends on -/

section Congr

variable {r₁ r₂ : R}

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
/-- `r₁` cannot distinguish two schedules in which, at every server, its second-round message is
delivered or not alike, and is preceded by the one of `r₂` alike. -/
lemma ret₁_congr (ℓ : Fin n → List (Node n W R × Msg)) {j j' : Option (Fin n)}
    {pat pat' : Fin n → Pat} (hdel : ∀ s, (pat s).del1 = (pat' s).del1)
    (hf2 : ∀ s, (pat s).del1 = true → (pat s = .first2 ↔ pat' s = .first2))
    (hj : ∀ s, (pat s).del1 = true → pat s = .first2 → A.p₂ r₁ r₂ ℓ j s = A.p₂ r₁ r₂ ℓ j' s) :
    A.ret₁ r₁ r₂ ℓ j pat = A.ret₁ r₁ r₂ ℓ j' pat' := by
  unfold ret₁ V₂
  rw [List.filter_congr (fun s _ => hdel s)]
  congr 2
  refine List.map_congr_left fun s hs => ?_
  have hd : (pat s).del1 = true := (hdel s).trans (List.mem_filter.1 hs).2
  by_cases h2 : pat s = .first2
  · simp [h2, (hf2 s hd).1 h2, hj s hd h2]
  · simp [h2, mt (hf2 s hd).2 h2]

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
/-- `r₂` cannot distinguish two schedules in which, at every server, its second-round message is
delivered or not alike, and is preceded by the one of `r₁` alike. -/
lemma ret₂_congr (ℓ : Fin n → List (Node n W R × Msg)) (j : Option (Fin n))
    {pat pat' : Fin n → Pat} (hdel : ∀ s, (pat s).del2 = (pat' s).del2)
    (hf1 : ∀ s, (pat s).del2 = true → (pat s = .first1 ↔ pat' s = .first1)) :
    A.ret₂ r₁ r₂ ℓ j pat = A.ret₂ r₁ r₂ ℓ j pat' := by
  unfold ret₂ U₂
  rw [List.filter_congr (fun s _ => hdel s)]
  congr 2
  refine List.map_congr_left fun s hs => ?_
  have hd : (pat s).del2 = true := (hdel s).trans (List.mem_filter.1 hs).2
  by_cases h1 : pat s = .first1
  · simp [h1, (hf1 s hd).1 h1]
  · simp [h1, mt (hf1 s hd).2 h1]

omit [DecidableEq W] [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] in
/-- If `r₂` skips server `c` in both round-trips and its second-round messages are never preceded
by those of `r₁`, then `r₂` cannot distinguish two write phases that differ only at `c`. -/
lemma ret₂_congr_log {ℓ ℓ' : Fin n → List (Node n W R × Msg)} (c : Fin n)
    (hℓ : ∀ s, s ≠ c → ℓ s = ℓ' s) {pat : Fin n → Pat} (hc : (pat c).del2 = false)
    (hf1 : ∀ s, pat s ≠ .first1) :
    A.ret₂ r₁ r₂ ℓ (some c) pat = A.ret₂ r₁ r₂ ℓ' (some c) pat := by
  have hU : A.U₁ r₁ r₂ ℓ (some c) = A.U₁ r₁ r₂ ℓ' (some c) := by
    unfold U₁
    refine List.map_congr_left fun s hs => ?_
    have : s ≠ c := by
      have := (List.mem_filter.1 hs).2; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq] at this
      exact Ne.symm this
    rw [hℓ s this]
  have hp₂ : A.p₂ r₁ r₂ ℓ (some c) = A.p₂ r₁ r₂ ℓ' (some c) := by
    funext s; simp only [p₂, hU]
  unfold ret₂
  rw [hU]
  congr 2
  unfold U₂
  refine List.map_congr_left fun s hs => ?_
  have hsc : s ≠ c := by
    rintro rfl; have := (List.mem_filter.1 hs).2; rw [hc] at this; exact Bool.false_ne_true this
  simp [base, hℓ s hsc, hf1 s, hp₂]

end Congr

/-! ### Admissible schedules -/

lemma length_le_filter_add_one {α : Type} (l : List α) (hl : l.Nodup) (q : α → Bool)
    (c : Option α) (h : ∀ s ∈ l, some s ≠ c → q s = true) :
    l.length ≤ (l.filter q).length + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    by_cases hqa : q a = true
    · rw [List.filter_cons_of_pos hqa]
      have := ih hl.2 (fun s hs => h s (by simp [hs]))
      simp only [List.length_cons]; omega
    · rw [List.filter_cons_of_neg hqa]
      have hac : some a = c := by
        by_contra hne; exact hqa (h a (by simp) hne)
      have hall : l.filter q = l := List.filter_eq_self.2 fun s hs => h s (by simp [hs]) (by
        rw [← hac]; intro he; exact hl.1 (Option.some.inj he ▸ hs))
      rw [hall]; simp

/-- A schedule in which each round-trip misses at most one server is admissible (`t ≥ 1`). -/
lemma readValid_of {t : ℕ} (ht : 1 ≤ t) (j : Option (Fin n)) (pat : Fin n → Pat)
    (c₁ c₂ : Option (Fin n)) (h₁ : ∀ s, some s ≠ c₁ → (pat s).del1 = true)
    (h₂ : ∀ s, some s ≠ c₂ → (pat s).del2 = true) : W1R2Alg.ReadValid n t j pat := by
  have key : ∀ (q : Fin n → Bool) (c : Option (Fin n)), (∀ s, some s ≠ c → q s = true) →
      n ≤ ((List.finRange n).filter q).length + t := fun q c hq => by
    have := length_le_filter_add_one (List.finRange n) (List.nodup_finRange n) q c
      (fun s _ => hq s)
    simp only [List.length_finRange] at this; omega
  refine ⟨key _ c₁ h₁, key _ c₂ h₂, key _ j fun s hs => ?_⟩
  simpa using Ne.symm hs

/-! ### The chains -/

/-- Write orders of chain `α`: the servers `s < i` received `W₂` first. -/
def χ (i : ℕ) : Fin n → Bool := fun s => decide (i ≤ s.val)

/-- Second-round schedules of chain `β`: `p₂` never reaches the critical server `c` (and `r₂`
ignores the first-round reply of `c`); at the other servers `s`, `p₂` arrives before `p₁` iff
`s < k`. -/
def patβ (c : Fin n) (k : ℕ) : Fin n → Pat :=
  fun s => if s = c then .only1 else if s.val < k then .first2 else .first1

section Zigzag

/-- Closes the side goals of case analyses on schedules (contradictory cases by `omega`). -/
local macro "pat_tac" : tactic =>
  `(tactic|
    first
    | rfl
    | (simp; done)
    | (exfalso
       subst_vars
       first
       | omega
       | (simp_all; done)
       | (simp_all; omega)
       | (simp_all [Fin.ext_iff]; done)
       | (simp_all [Fin.ext_iff]; omega)))

variable {w₁ w₂ : W} {r₁ r₂ : R} (hw : w₁ ≠ w₂) (hr : r₁ ≠ r₂) (a b : V)

include hw hr in
/-- **Phase 3 of the proof** (§3.4): consecutive executions of chain `β` are linked by the
horizontal link `β_k ≈ temp_k ≈ γ_k` and the diagonal link `γ'_k ≈ temp'_k ≈ β_{k+1}`, with
`γ_k = γ'_k`. -/
lemma zigzag (ht : 1 ≤ t) (hlin : (A.protocol t v₀).Linearizable) (x : Fin n → Bool)
    (c : Fin n) (k : ℕ) (hk : k < n) :
    A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) (some c) (patβ c k) =
      A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) (some c) (patβ c (k + 1)) := by
  set ℓ := A.wlog w₁ w₂ a b x
  by_cases hkc : k = c.val
  · congr 1
    funext s
    simp only [patβ]
    split_ifs <;> pat_tac
  obtain ⟨s', hs'v⟩ : ∃ s' : Fin n, s'.val = k := ⟨⟨k, hk⟩, rfl⟩
  have hsc : s' ≠ c := fun h => hkc (by rw [← hs'v, h])
  have agree := fun (pat : Fin n → Pat) (hv : ReadValid n t (some c) pat) =>
    A.ret_agree t v₀ hw hr a b hlin x (some c) pat hv
  set temp : Fin n → Pat := fun s => if s = s' then .only1 else if s = c then .first1 else
    patβ c k s
  set γ : Fin n → Pat := fun s => if s = s' then .none else if s = c then .first1 else
    patβ c k s
  set temp' : Fin n → Pat := fun s => if s = s' then .only2 else patβ c (k + 1) s
  set γ' : Fin n → Pat := fun s => if s = s' then .none else if s = c then .first1 else
    patβ c (k + 1) s
  have hγ : γ = γ' := by
    funext s
    simp only [γ, γ', patβ]
    split_ifs <;> pat_tac
  -- the five executions are admissible
  have vβ : ∀ k', ReadValid n t (some c) (patβ c k') := fun k' =>
    readValid_of ht _ _ none (some c) (fun s _ => by simp only [patβ]; split_ifs <;> rfl)
      (fun s hs => by
        simp only [patβ]
        split_ifs with h
        · exact absurd (congrArg some h) hs
        · rfl
        · rfl)
  have vtemp : ReadValid n t (some c) temp :=
    readValid_of ht _ _ none (some s')
      (fun s _ => by simp only [temp, patβ]; split_ifs <;> rfl)
      (fun s hs => by
        simp only [temp, patβ]
        split_ifs with h1 h2 h3
        · exact absurd (congrArg some h1) hs
        all_goals rfl)
  have vγ : ReadValid n t (some c) γ :=
    readValid_of ht _ _ (some s') (some s')
      (fun s hs => by
        simp only [γ, patβ]
        split_ifs with h1
        · exact absurd (congrArg some h1) hs
        all_goals rfl)
      (fun s hs => by
        simp only [γ, patβ]
        split_ifs <;> first | exact absurd (congrArg some ‹_›) hs | pat_tac)
  have vtemp' : ReadValid n t (some c) temp' :=
    readValid_of ht _ _ (some s') (some c)
      (fun s hs => by
        simp only [temp', patβ]
        split_ifs with h1
        · exact absurd (congrArg some h1) hs
        all_goals rfl)
      (fun s hs => by
        simp only [temp', patβ]
        split_ifs with h1 h2
        · rfl
        · exact absurd (congrArg some h2) hs
        all_goals rfl)
  -- horizontal link
  have e₁ : A.ret₁ r₁ r₂ ℓ (some c) (patβ c k) = A.ret₁ r₁ r₂ ℓ (some c) temp :=
    A.ret₁_congr ℓ
      (fun s => by
        simp only [temp, patβ]; split_ifs <;> pat_tac)
      (fun s _ => by
        simp only [temp, patβ]
        split_ifs <;> pat_tac)
      (fun _ _ _ => rfl)
  have e₃ : A.ret₂ r₁ r₂ ℓ (some c) temp = A.ret₂ r₁ r₂ ℓ (some c) γ :=
    A.ret₂_congr ℓ _
      (fun s => by simp only [temp, γ]; split_ifs <;> rfl)
      (fun s _ => by simp only [temp, γ]; split_ifs <;> simp)
  -- diagonal link
  have e₅ : A.ret₁ r₁ r₂ ℓ (some c) γ' = A.ret₁ r₁ r₂ ℓ (some c) temp' :=
    A.ret₁_congr ℓ
      (fun s => by
        simp only [γ', temp', patβ]
        split_ifs <;> pat_tac)
      (fun s _ => by
        simp only [γ', temp', patβ]
        split_ifs <;> pat_tac)
      (fun _ _ _ => rfl)
  have e₇ : A.ret₂ r₁ r₂ ℓ (some c) temp' = A.ret₂ r₁ r₂ ℓ (some c) (patβ c (k + 1)) :=
    A.ret₂_congr ℓ _
      (fun s => by
        simp only [temp', patβ]
        split_ifs <;> pat_tac)
      (fun s _ => by
        simp only [temp', patβ]
        split_ifs <;> pat_tac)
  rw [e₁, agree _ vtemp, e₃, ← agree _ vγ, hγ, e₅, agree _ vtemp', e₇, ← agree _ (vβ _)]

end Zigzag

lemma readValid_patβ {t : ℕ} (ht : 1 ≤ t) (c : Fin n) (k : ℕ) :
    ReadValid n t (some c) (patβ c k) :=
  readValid_of ht _ _ none (some c) (fun s _ => by simp only [patβ]; split_ifs <;> rfl)
    (fun s hs => by
      simp only [patβ]
      split_ifs with h
      · exact absurd (congrArg some h) hs
      · rfl
      · rfl)

end W1R2Alg

open W1R2Alg in
/-- **Theorem 1 (W1R2 impossibility)** of Huang–Huang–Wei (PODC 2020): let `t ≥ 1`, `W ≥ 2` and
`R ≥ 2`; there is no fast write (W1R2) atomic register implementation.

Formally: for any number `n` of servers, any `t ≥ 1`, at least two writers, at least two readers
and at least two values, the asynchronous message-passing protocol induced by any W1R2 algorithm
(writes: one round-trip, reads: two round-trips, clients waiting for `n - t` replies per
round-trip) has a reachable execution whose history is not linearizable. -/
theorem theorem_1 {n t : ℕ} (ht : 1 ≤ t) {W R V Msg Rep LW LR : Type} [DecidableEq W]
    [DecidableEq R] [DecidableEq Msg] [DecidableEq Rep] (hW : ∃ w₁ w₂ : W, w₁ ≠ w₂)
    (hR : ∃ r₁ r₂ : R, r₁ ≠ r₂) [Nontrivial V] (v₀ : V) (A : W1R2Alg n W R V Msg Rep LW LR) :
    ¬ (A.protocol t v₀).Linearizable := by
  intro hlin
  obtain ⟨w₁, w₂, hw⟩ := hW
  obtain ⟨r₁, r₂, hr⟩ := hR
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  -- Phase 1: chain `α` and the critical server `c`
  set F : ℕ → V := fun i => A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b (χ i)) none (fun _ => .first1)
  have vF : ReadValid n t none (fun _ : Fin n => Pat.first1) :=
    readValid_of ht _ _ none none (fun _ _ => rfl) (fun _ _ => rfl)
  have hF0 : F 0 = b := by
    have := A.ret_seq t v₀ hr hlin hw a b none _ vF
    convert this using 2
    funext s; simp [wlog, χ]
  have hFn : F n = a := by
    have := A.ret_seq t v₀ hr hlin hw.symm b a none _ vF
    convert this using 2
    funext s; simp [wlog, χ, s.isLt]
  obtain ⟨i, hi, hne⟩ : ∃ i < n, F i ≠ F (i + 1) := by
    by_contra hcon
    push Not at hcon
    have : ∀ i ≤ n, F i = F 0 := by
      intro i hi
      induction i with
      | zero => rfl
      | succ i ih => rw [← hcon i (by omega), ih (by omega)]
    exact hab (by rw [← hFn, this n le_rfl, hF0])
  set c : Fin n := ⟨i, hi⟩
  -- Phase 2: chain `β`
  have start : ∀ x, A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) (some c) (patβ c 0) =
      A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) none (fun _ => .first1) := fun x =>
    A.ret₁_congr _ (fun s => by simp only [patβ]; split_ifs <;> rfl)
      (fun s _ => by simp only [patβ]; split_ifs <;> simp; omega)
      (fun s _ h => by simp only [patβ] at h; split_ifs at h; simp_all)
  have stop : A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b (χ i)) (some c) (patβ c n) =
      A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b (χ (i + 1))) (some c) (patβ c n) := by
    refine A.ret₂_congr_log c (fun s hs => ?_) (by simp [patβ, Pat.del2]) (fun s => ?_)
    · have : s.val ≠ i := fun h => hs (Fin.ext h)
      have hiff : (i ≤ s.val) ↔ (i + 1 ≤ s.val) := by omega
      simp only [wlog, χ, hiff]; rfl
    · simp only [patβ]; split_ifs <;> simp_all [s.isLt]
  -- Phase 3: the zigzag chain collapses chain `β`
  have chain : ∀ x, A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) (some c) (patβ c 0) =
      A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) (some c) (patβ c n) := fun x => by
    have : ∀ k ≤ n, A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) (some c) (patβ c 0) =
        A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b x) (some c) (patβ c k) := by
      intro k hk
      induction k with
      | zero => rfl
      | succ k ih => rw [ih (by omega), A.zigzag t v₀ hw hr a b ht hlin x c k (by omega)]
    exact this n le_rfl
  apply hne
  calc F i = A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b (χ i)) (some c) (patβ c 0) := (start _).symm
    _ = A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b (χ i)) (some c) (patβ c n) := chain _
    _ = A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b (χ i)) (some c) (patβ c n) :=
      A.ret_agree t v₀ hw hr a b hlin _ _ _ (readValid_patβ ht c n)
    _ = A.ret₂ r₁ r₂ (A.wlog w₁ w₂ a b (χ (i + 1))) (some c) (patβ c n) := stop
    _ = A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b (χ (i + 1))) (some c) (patβ c n) :=
      (A.ret_agree t v₀ hw hr a b hlin _ _ _ (readValid_patβ ht c n)).symm
    _ = A.ret₁ r₁ r₂ (A.wlog w₁ w₂ a b (χ (i + 1))) (some c) (patβ c 0) := (chain _).symm
    _ = F (i + 1) := start _

end Podc.FastMWMR
