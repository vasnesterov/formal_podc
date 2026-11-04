import Papers.PODC2014.EventualLinParadox.ImplModel
import Papers.PODC2014.EventualLinParadox.Lemma17

/-!
# Proposition 18: eventually linearizable fetch&increment is as hard as linearizable

If an `n`-process implementation `A` of fetch&increment from a set of atomic (linearizable)
base objects is eventually linearizable and non-blocking, then there is an `n`-process
linearizable non-blocking implementation of fetch&increment from the same base objects (with
other initial states): the algorithm `A` itself, started from a "stable" configuration `C₀`,
with responses shifted by the number `v₀` of operations performed before `C₀`.

* `cntEntries`, `Legal.fai_resp`, `legal_fai_of_resp`: legality for fetch&increment.
* `Stable`, `claim1` — Claim 1 (a stable node exists), from Lemma 17.
* `prop18` — Proposition 18.
-/

namespace Podc.EventualLinParadox

/-! ### Legal sequential histories of fetch&increment -/

section FaiLegal

variable {P X : Type}

/-- The number of entries of `S` before position `k`. -/
noncomputable def cntEntries {Res : Type} (S : SeqHist Res) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => (S i).isSome).card

lemma cntEntries_succ {Res : Type} (S : SeqHist Res) (k : ℕ) :
    cntEntries S (k + 1) = cntEntries S k + if (S k).isSome then 1 else 0 := by
  unfold cntEntries
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

/-- In a legal fetch&increment sequential history, the response of each entry is the number of
entries before it. -/
lemma Legal.fai_resp {H : History P Unit Unit ℕ} {S : SeqHist ℕ}
    (h : Legal (fun _ => fai) H S) {k a r : ℕ} (hk : S k = some (a, r)) : r = cntEntries S k := by
  obtain ⟨hinv, hq⟩ := h
  obtain ⟨q, hq0, hqs⟩ := hq ()
  have key : ∀ k, q k = cntEntries S k := by
    intro k
    induction k with
    | zero => simpa [cntEntries, fai] using hq0
    | succ k ih =>
      rw [cntEntries_succ, ← ih]
      have := hqs k
      cases hSk : S k with
      | none => simp only [hSk, SeqStep] at this; simp [this]
      | some e =>
        obtain ⟨b, rb⟩ := e
        rw [hSk] at this
        obtain ⟨p, x, op, hb⟩ := hinv k b rb hSk
        obtain ⟨p', op', -, h1, h2⟩ := this.onObj ⟨p, op, hb⟩
        simp [h2]
  have := hqs k
  rw [hk] at this
  obtain ⟨p, x, op, hb⟩ := hinv k a r hk
  obtain ⟨p', op', -, h1, -⟩ := this.onObj ⟨p, op, hb⟩
  rw [h1, key]

/-- Conversely, a sequential history of invoked operations in which every response is the
number of earlier entries is legal for fetch&increment. -/
lemma legal_fai_of_resp {H : History P Unit Unit ℕ} {S : SeqHist ℕ}
    (hinv : ∀ k a r, S k = some (a, r) → Invoked H a)
    (hresp : ∀ k a r, S k = some (a, r) → r = cntEntries S k) : Legal (fun _ => fai) H S := by
  refine ⟨hinv, fun x => ⟨cntEntries S, by simp [cntEntries, fai], fun k => ?_⟩⟩
  cases hSk : S k with
  | none => simp [SeqStep, cntEntries_succ, hSk]
  | some e =>
    obtain ⟨a, r⟩ := e
    obtain ⟨p, y, op, ha⟩ := hinv k a r hSk
    left
    refine ⟨p, op, by cases x; cases y; exact ha, hresp k a r hSk, ?_⟩
    simp [cntEntries_succ, hSk]

/-- The operations of the entries of `S` before position `k`. -/
noncomputable def opsBefore {Res : Type} (S : SeqHist Res) (k : ℕ) : Finset ℕ :=
  ((Finset.range k).filter fun i => (S i).isSome).image fun i => ((S i).map Prod.fst).getD 0

lemma mem_opsBefore {Res : Type} {S : SeqHist Res} {k a : ℕ} :
    a ∈ opsBefore S k ↔ ∃ i < k, ∃ r, S i = some (a, r) := by
  simp only [opsBefore, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨i, ⟨hi, hs⟩, rfl⟩
    obtain ⟨⟨b, r⟩, hb⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨i, hi, r, by simp [hb]⟩
  · rintro ⟨i, hi, r, h⟩
    exact ⟨i, ⟨hi, by simp [h]⟩, by simp [h]⟩

lemma card_opsBefore {Res : Type} {S : SeqHist Res} (hnd : S.Nodup) (k : ℕ) :
    (opsBefore S k).card = cntEntries S k := by
  unfold opsBefore cntEntries
  apply Finset.card_image_of_injOn
  intro i hi j hj hij
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hi hj
  obtain ⟨⟨a, r⟩, ha⟩ := Option.isSome_iff_exists.1 hi.2
  obtain ⟨⟨b, r'⟩, hb⟩ := Option.isSome_iff_exists.1 hj.2
  simp only [ha, hb, Option.map_some, Option.getD_some] at hij
  subst hij
  exact hnd i j a r r' ha hb

end FaiLegal



/-! ### Linearizations around a solo phase -/

section Phase

variable {P : Type}

/-- If operation `k` (invoked after `t`) responds at `J` and nothing is invoked in `(k, J]`,
then in every `t`-linearization the operations before `k` were invoked before `k`. -/
lemma opsBefore_subset {H : History P Unit Unit ℕ} {t : ℕ} {S : SeqHist ℕ}
    (hS : IsTLin (fun _ => fai) H t S) {k J : ℕ} (htk : t ≤ k) (hkJ : k < J)
    (hJ : ∃ r, H J = some (.res k r))
    (hnoinv : ∀ i, k < i → i ≤ J → ∀ p x op, H i ≠ some (.inv p x op)) {ko r : ℕ}
    (hko : S ko = some (k, r)) :
    ∀ b ∈ opsBefore S ko, b < k ∧ Invoked H b := by
  intro b hb
  obtain ⟨i, hi, rb, hib⟩ := mem_opsBefore.1 hb
  have hbinv := hS.legal.1 i b rb hib
  have hbk : b ≠ k := fun h => by subst h; have := hS.nodup i ko b rb r hib hko; omega
  refine ⟨?_, hbinv⟩
  by_contra hge; push_neg at hge
  rcases lt_or_ge J b with hJb | hbJ
  · obtain ⟨rJ, hrJ⟩ := hJ
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ := hS.rt k b J rJ hrJ (by omega) hJb hbinv ⟨i, rb, hib⟩
    have e1 := hS.nodup k1 ko k r1 r h1 hko
    have e2 := hS.nodup k2 i b r2 rb h2 hib
    omega
  · obtain ⟨p, x, op, hp⟩ := hbinv
    exact hnoinv b (by omega) hbJ p x op hp

lemma finset_bound {F : Finset ℕ} {Q : ℕ → ℕ → Prop} (h : ∀ e ∈ F, ∃ k, Q e k) :
    ∃ M, ∀ e ∈ F, ∃ k < M, Q e k := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a F ha ih =>
    obtain ⟨M, hM⟩ := ih (fun e he => h e (Finset.mem_insert_of_mem he))
    obtain ⟨k, hk⟩ := h a (Finset.mem_insert_self a F)
    refine ⟨max M (k + 1), fun e he => ?_⟩
    rcases Finset.mem_insert.1 he with rfl | he
    · exact ⟨k, by omega, hk⟩
    · obtain ⟨k', hk', hq⟩ := hM e he; exact ⟨k', by omega, hq⟩

end Phase

/-! ### Claim 1: a stable node exists -/

section Claim1

variable {P X BOp BRes L Q : Type} [DecidableEq P] [DecidableEq X]
  (A : Impl P Unit ℕ X BOp BRes L) (B : X → ObjType Q BOp BRes) (m₀ : X → Q)

/-- The node of the execution tree reached by the first `n` steps of `lab` is **stable**: every
execution through it is `n`-linearizable. -/
def Stable (lab : ℕ → Option (ALab P Unit BRes Q)) (n : ℕ) : Prop :=
  ∀ lab', (atSys A B m₀).Proper lab' → (∀ k < n, lab' k = lab k) →
    TLinearizable (fun _ => fai) ((atSys A B m₀).hist lab') n

/-- The hypothesis of Claim 1 provided by Lemma 17. -/
def Lemma17Stmt (P : Type) : Prop :=
  ∀ H : History P Unit Unit ℕ, WellFormed H → ∀ t t₀, TLinearizable (fun _ => fai) H t₀ →
    (∀ m, TLinearizable (fun _ => fai) (take H m) t) → TLinearizable (fun _ => fai) H t

lemma proper_none : (atSys A B m₀).Proper (fun _ => none) := fun _ _ h => by cases h

/-- **Claim 1** (in the proof of Proposition 18): some node of the execution tree is stable.
(No König's lemma is needed: the proof builds an infinite path directly.) -/
theorem claim1 (h17 : Lemma17Stmt P)
    (hEL : (atSys A B m₀).IsEventuallyLinearizable (atSys A B m₀).Proper fai) :
    ∃ lab n, (atSys A B m₀).Proper lab ∧ Stable A B m₀ lab n := by
  classical
  set S := atSys A B m₀ with hSdef
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ (lab : ℕ → Option (ALab P Unit BRes Q)) (n : ℕ), S.Proper lab →
      ∃ lab' m, S.Proper lab' ∧ (∀ k < n, lab' k = lab k) ∧ n < m ∧
        ¬ TLinearizable (fun _ => fai) (take (S.hist lab') m) n := by
    intro lab n hlab
    have := hcon lab n hlab
    simp only [Stable, not_forall] at this
    obtain ⟨lab', hp', hag, hnot⟩ := this
    have hWF := at_wellFormed_hist A B m₀ lab'
    obtain ⟨t₀, ht₀⟩ := (hEL lab' hp').2
    have : ¬ ∀ m, TLinearizable (fun _ => fai) (take (S.hist lab') m) n :=
      fun h => hnot (h17 _ hWF n t₀ ht₀ h)
    push_neg at this
    obtain ⟨m, hm⟩ := this
    refine ⟨lab', m, hp', hag, ?_, hm⟩
    by_contra hle; push_neg at hle
    exact hm ((tLinearizable_take_self (fun _ => ⟨0, rfl⟩) (fun _ => fai_deterministic.total)
      hWF m).mono hle)
  let PL := {lab : ℕ → Option (ALab P Unit BRes Q) // S.Proper lab} × ℕ
  choose f g hf using fun (x : PL) => hstep x.1.1 x.2 x.1.2
  let next : PL → PL := fun x => (⟨f x, (hf x).1⟩, g x)
  let sq : ℕ → PL := fun i => next^[i] (⟨fun _ => none, proper_none A B m₀⟩, 0)
  have hsucc : ∀ i, sq (i + 1) = next (sq i) := fun i => Function.iterate_succ_apply' _ _ _
  have hlt : ∀ i, (sq i).2 < (sq (i + 1)).2 := fun i => by rw [hsucc]; exact (hf (sq i)).2.2.1
  have hge : ∀ i, i ≤ (sq i).2 := by
    intro i; induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => have := hlt i; omega
  have hmono : ∀ i j, i ≤ j → (sq i).2 ≤ (sq j).2 := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j _ ih => exact ih.trans (hlt j).le
  have hagree : ∀ i j, i ≤ j → ∀ k < (sq i).2, (sq j).1.1 k = (sq i).1.1 k := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro k _; rfl
    | succ j hij ih =>
      intro k hk
      rw [hsucc]
      exact ((hf (sq j)).2.1 k (lt_of_lt_of_le hk (hmono i j hij))).trans (ih k hk)
  let lim : ℕ → Option (ALab P Unit BRes Q) := fun k => (sq (k + 1)).1.1 k
  have hlim : ∀ i k, k < (sq i).2 → lim k = (sq i).1.1 k := by
    intro i k hk
    show (sq (k + 1)).1.1 k = _
    rcases le_total (k + 1) i with h | h
    · exact (hagree (k + 1) i h k (by have := hge (k + 1); omega)).symm
    · exact hagree i (k + 1) h k hk
  have hproper : S.Proper lim := by
    intro k l hl
    have h1 : ∀ n < (sq (k + 1)).2, lim n = (sq (k + 1)).1.1 n := fun n hn => hlim _ n hn
    have hk : k < (sq (k + 1)).2 := by have := hge (k + 1); omega
    rw [S.cfg_congr h1 k hk.le]
    rw [h1 k hk] at hl
    exact (sq (k + 1)).1.2 k l hl
  obtain ⟨t, ht⟩ := (hEL lim hproper).2
  have h1 : TLinearizable (fun _ => fai) (S.hist lim) (sq t).2 := ht.mono (hge t)
  have h2 := h1.prefix (fun _ => fai_deterministic.total) (at_wellFormed_hist A B m₀ lim)
    (sq (t + 1)).2
  have h3 : take (S.hist lim) (sq (t + 1)).2 = take (S.hist (sq (t + 1)).1.1) (sq (t + 1)).2 := by
    funext k
    simp only [take_apply]
    split_ifs with hk
    · exact S.hist_congr (fun n hn => hlim _ n hn) hk
    · rfl
  rw [h3] at h2
  have := (hf (sq t)).2.2.2
  rw [hsucc] at h2
  exact this h2

end Claim1

/-! ### The idle schedule: finish pending operations, then let `p₀` run alone -/

section Sched

variable {P X BOp BRes L Q : Type} [DecidableEq P] [DecidableEq X]
  (A : Impl P Unit ℕ X BOp BRes L) (B : X → ObjType Q BOp BRes) (m₀ : X → Q)
  (hB : ∀ x, (B x).Total) (p₀ : P)

/-- The next label of process `q`: its next local step or return, or its base access with a
response chosen by the (total) specification. -/
noncomputable def nextLab (c : ACfg P L X Q) (q : P) : ALab P Unit BRes Q :=
  match A.act q (c.loc q) with
  | .call x o _ => .acc q (Classical.choose (hB x (c.mem x) o))
      (Classical.choose (Classical.choose_spec (hB x (c.mem x) o)))
  | _ => .step q

lemma nextLab_enabled {c : ACfg P L X Q} {q : P} (hq : c.pend q ≠ none) (n : ℕ) :
    atStep A B n c (nextLab A B hB c q) ≠ none := by
  unfold nextLab
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hq
  cases hact : A.act q (c.loc q) with
  | call x o k =>
    simp only [atStep, ha, hact]
    rw [if_pos (Classical.choose_spec (Classical.choose_spec (hB x (c.mem x) o)))]
    simp
  | loc l => simp [atStep, ha, hact]
  | ret r l => simp [atStep, ha, hact]

/-- The scheduler: some pending process takes its next step; if no process is pending, `p₀`
invokes `fetch&inc`. -/
noncomputable def idleSched (_ : ℕ) (c : ACfg P L X Q) : Option (ALab P Unit BRes Q) := by
  classical
  exact if h : ∃ q, c.pend q ≠ none then some (nextLab A B hB c (Classical.choose h))
    else some (.inv p₀ ())

lemma idleSched_enabled (k : ℕ) (c : ACfg P L X Q) (l : ALab P Unit BRes Q)
    (hl : idleSched A B hB p₀ k c = some l) : atStep A B k c l ≠ none := by
  classical
  unfold idleSched at hl
  split_ifs at hl with h
  · cases hl; exact nextLab_enabled A B hB (Classical.choose_spec h) k
  · cases hl
    push_neg at h
    simp [atStep, h p₀]

lemma idleSched_isSome (k : ℕ) (c : ACfg P L X Q) : idleSched A B hB p₀ k c ≠ none := by
  classical
  unfold idleSched; split_ifs <;> simp

lemma idleSched_of_pend {k : ℕ} {c : ACfg P L X Q} (h : ∃ q, c.pend q ≠ none) :
    ∃ q, c.pend q ≠ none ∧ idleSched A B hB p₀ k c = some (nextLab A B hB c q) := by
  classical
  refine ⟨Classical.choose h, Classical.choose_spec h, ?_⟩
  unfold idleSched; rw [dif_pos h]

lemma idleSched_of_idle {k : ℕ} {c : ACfg P L X Q} (h : ∀ q, c.pend q = none) :
    idleSched A B hB p₀ k c = some (.inv p₀ ()) := by
  classical
  unfold idleSched
  rw [dif_neg (by push_neg; exact h)]

lemma nextLab_ne_inv (c : ACfg P L X Q) (q p : P) (op : Unit) : nextLab A B hB c q ≠ .inv p op := by
  unfold nextLab; split <;> simp

end Sched

/-! ### The execution through a node followed by the idle schedule -/

section Run

variable {P X BOp BRes L Q : Type} [DecidableEq P] [DecidableEq X] [Fintype P]
  (A : Impl P Unit ℕ X BOp BRes L) (B : X → ObjType Q BOp BRes) (m₀ : X → Q)
  (hB : ∀ x, (B x).Total) (p₀ : P) (labC : ℕ → Option (ALab P Unit BRes Q)) (t : ℕ)

/-- The execution that follows `labC` for `t` steps and then the idle schedule. -/
noncomputable abbrev runLab : ℕ → Option (ALab P Unit BRes Q) :=
  (atSys A B m₀).sched labC t (idleSched A B hB p₀)

/-- The history of `runLab`. -/
noncomputable abbrev runHist : History P Unit Unit ℕ := (atSys A B m₀).hist (runLab A B m₀ hB p₀ labC t)

/-- The pending operations along `runLab`. -/
noncomputable abbrev runPend : ℕ → P → Option ℕ :=
  fun n => ((atSys A B m₀).cfg (runLab A B m₀ hB p₀ labC t) n).pend

local notation "𝓛" => runLab A B m₀ hB p₀ labC t
local notation "𝓗" => runHist A B m₀ hB p₀ labC t
local notation "𝓟" => runPend A B m₀ hB p₀ labC t

lemma runLab_proper (h : (atSys A B m₀).Proper labC) : (atSys A B m₀).Proper 𝓛 :=
  (atSys A B m₀).proper_sched h t (idleSched_enabled A B hB p₀)

lemma runLab_agree : ∀ k < t, 𝓛 k = labC k := fun _ hk => (atSys A B m₀).sched_of_lt labC _ hk

lemma runLab_of_ge {k : ℕ} (hk : t ≤ k) :
    𝓛 k = idleSched A B hB p₀ k ((atSys A B m₀).cfg 𝓛 k) :=
  (atSys A B m₀).sched_of_ge labC _ hk

lemma runLab_ne_none {k : ℕ} (hk : t ≤ k) : 𝓛 k ≠ none := by
  rw [runLab_of_ge A B m₀ hB p₀ labC t hk]; exact idleSched_isSome A B hB p₀ _ _

lemma pendInv_run : ∀ n, PendInv 𝓗 𝓟 n :=
  pendInv_all (fun _ => rfl) (at_pendStep A B m₀ _)

/-- After `t`, a step taken while some operation is pending is not an invocation. -/
lemma run_step_pending {k : ℕ} (hk : t ≤ k) (h : ∃ q, (𝓟) k q ≠ none) :
    (𝓗 k = none ∧ (𝓟) (k + 1) = (𝓟) k) ∨
    (∃ q a r, 𝓗 k = some (.res a r) ∧ (𝓟) k q = some a ∧
      (𝓟) (k + 1) = Function.update ((𝓟) k) q none) := by
  rcases at_pendStep A B m₀ 𝓛 k with h1 | ⟨p, x, op, h2, -⟩ | h3
  · exact Or.inl h1
  · exfalso
    have := (at_hist_inv A B m₀ h2).1
    rw [runLab_of_ge A B m₀ hB p₀ labC t hk] at this
    obtain ⟨q, -, hq⟩ := idleSched_of_pend A B hB p₀ (k := k) h
    rw [hq] at this
    exact nextLab_ne_inv A B hB _ q p op (Option.some_injective _ this)
  · exact Or.inr h3

/-- From any time `N ≥ t`, all operations eventually complete (non-blocking). -/
lemma reach_idle (hNB : (atSys A B m₀).NonBlocking (atSys A B m₀).Proper)
    (hC : (atSys A B m₀).Proper labC) :
    ∀ N, t ≤ N → ∃ T, N ≤ T ∧ ∀ q, (𝓟) T q = none := by
  classical
  let ps : ℕ → Finset P := fun n => Finset.univ.filter fun q => (𝓟) n q ≠ none
  suffices H : ∀ c N, (ps N).card = c → t ≤ N → ∃ T, N ≤ T ∧ ∀ q, (𝓟) T q = none from
    fun N hN => H _ N rfl hN
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro N hcN htN
  by_cases hidle : ∀ q, (𝓟) N q = none
  · exact ⟨N, le_rfl, hidle⟩
  push_neg at hidle
  obtain ⟨q, hq⟩ := hidle
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hq
  obtain ⟨haN, ⟨x, op, hHa⟩, hnores⟩ := (pendInv_run A B m₀ hB p₀ labC t N).pend_spec q a ha
  obtain ⟨j, hjN, b, r, hj⟩ := hNB 𝓛 (runLab_proper A B m₀ hB p₀ labC t hC) N a q op
    (by cases x; exact hHa) haN hnores
    (fun N' => ⟨max N' t, le_max_left _ _, runLab_ne_none A B m₀ hB p₀ labC t (le_max_right _ _)⟩)
  -- up to `j`, either we became idle or the pending set only shrank
  have hmid : ∀ k, N ≤ k → k ≤ j → (∃ T, N ≤ T ∧ ∀ q, (𝓟) T q = none) ∨ ps k ⊆ ps N := by
    intro k hNk hkj
    induction k, hNk using Nat.le_induction with
    | base => exact Or.inr subset_rfl
    | succ k hNk ihk =>
      rcases ihk (by omega) with h | h
      · exact Or.inl h
      by_cases hk : ∀ q, (𝓟) k q = none
      · exact Or.inl ⟨k, hNk, hk⟩
      push_neg at hk
      refine Or.inr (fun q' hq' => h ?_)
      simp only [ps, Finset.mem_filter, Finset.mem_univ, true_and] at hq' ⊢
      rcases run_step_pending A B m₀ hB p₀ labC t (by omega) hk with ⟨-, he⟩ | ⟨q'', a', r', -, -, he⟩
      · rw [he] at hq'; exact hq'
      · rw [he, Function.update_apply] at hq'
        split_ifs at hq' with hh
        · exact absurd rfl hq'
        · exact hq'
  rcases hmid j hjN le_rfl with h | hsub
  · exact h
  by_cases hk : ∀ q, (𝓟) j q = none
  · exact ⟨j, hjN, hk⟩
  push_neg at hk
  rcases run_step_pending A B m₀ hB p₀ labC t (by omega) hk with ⟨he, -⟩ | ⟨q', a', r', -, hqa, he⟩
  · have : (𝓗) j = some (.res b r) := hj
    rw [he] at this; cases this
  have hlt : (ps (j + 1)).card < c := by
    rw [← hcN]
    refine lt_of_lt_of_le (Finset.card_lt_card ?_) (Finset.card_le_card hsub)
    refine ⟨fun q'' hq'' => ?_, fun hcon => ?_⟩
    · simp only [ps, Finset.mem_filter, Finset.mem_univ, true_and] at hq'' ⊢
      rw [he, Function.update_apply] at hq''
      split_ifs at hq'' with hh
      · exact absurd rfl hq''
      · exact hq''
    · have : q' ∈ ps (j + 1) := hcon (by simp [ps, hqa])
      simp [ps, he] at this
  obtain ⟨T, hT, hidle⟩ := ih _ hlt (j + 1) rfl (by omega)
  exact ⟨T, by omega, hidle⟩

/-- From an idle configuration after `t`, `p₀` invokes `fetch&inc` and runs it alone to
completion; afterwards the system is idle again. -/
lemma idle_phase (hNB : (atSys A B m₀).NonBlocking (atSys A B m₀).Proper)
    (hC : (atSys A B m₀).Proper labC) {k : ℕ} (hk : t ≤ k) (hidle : ∀ q, (𝓟) k q = none) :
    (𝓗) k = some (.inv p₀ () ()) ∧ ∃ j, k < j ∧ (∃ r, (𝓗) j = some (.res k r)) ∧
      (∀ i, k < i → i ≤ j → ∀ p x op, (𝓗) i ≠ some (.inv p x op)) ∧
      (∀ q, (𝓟) (j + 1) q = none) := by
  classical
  have hlab : 𝓛 k = some (.inv p₀ ()) := by
    rw [runLab_of_ge A B m₀ hB p₀ labC t hk]
    exact idleSched_of_idle A B hB p₀ hidle
  have hHk : (𝓗) k = some (.inv p₀ () ()) := by
    show (atSys A B m₀).hist 𝓛 k = _
    rw [atSys_hist, hlab]
    have : ((atSys A B m₀).cfg 𝓛 k).pend p₀ = none := hidle p₀
    simp [atStep, this]
  refine ⟨hHk, ?_⟩
  have hP1 : (𝓟) (k + 1) = Function.update ((𝓟) k) p₀ (some k) := by
    rcases at_pendStep A B m₀ 𝓛 k with ⟨h1, -⟩ | ⟨p, x, op, h2, -, h3⟩ | ⟨p, a, r, h2, -⟩
    · have : (𝓗) k = none := h1; rw [hHk] at this; cases this
    · have : (𝓗) k = some (.inv p x op) := h2
      rw [hHk] at this; cases this; exact h3
    · have : (𝓗) k = some (.res a r) := h2; rw [hHk] at this; cases this
  have hWF := at_wellFormed_hist A B m₀ 𝓛
  have hex : ∃ j, k + 1 ≤ j ∧ ∃ b r, (𝓗) j = some (.res b r) := by
    obtain ⟨j, hj, b, r, h⟩ := hNB 𝓛 (runLab_proper A B m₀ hB p₀ labC t hC) (k + 1) k p₀ ()
      hHk (by omega) (fun j hj r hjr => by have := (hWF.res_inv k j r hjr).1; omega)
      (fun N' => ⟨max N' t, le_max_left _ _, runLab_ne_none A B m₀ hB p₀ labC t (le_max_right _ _)⟩)
    exact ⟨j, hj, b, r, h⟩
  set j := Nat.find hex with hjdef
  obtain ⟨hkj, b, r, hjr⟩ := Nat.find_spec hex
  have hmin : ∀ i, k + 1 ≤ i → i < j → ∀ b r, (𝓗) i ≠ some (.res b r) := by
    intro i hi hij b r h
    exact Nat.find_min hex hij ⟨hi, b, r, h⟩
  have hsingle : ∀ i, k + 1 ≤ i → i ≤ j → (𝓟) i = Function.update ((𝓟) k) p₀ (some k) := by
    intro i hi hij
    induction i, hi using Nat.le_induction with
    | base => exact hP1
    | succ i hi ih =>
      have hpi := ih (by omega)
      have hpend : ∃ q, (𝓟) i q ≠ none := ⟨p₀, by rw [hpi]; simp⟩
      rcases run_step_pending A B m₀ hB p₀ labC t (by omega) hpend with ⟨-, he⟩ | ⟨q, a, r, he, -⟩
      · rw [he, hpi]
      · exact absurd he (hmin i (by omega) (by omega) a r)
  have hnoinv : ∀ i, k < i → i ≤ j → ∀ p x op, (𝓗) i ≠ some (.inv p x op) := by
    intro i hi hij p x op h
    have hpi := hsingle i (by omega) hij
    have hpend : ∃ q, (𝓟) i q ≠ none := ⟨p₀, by rw [hpi]; simp⟩
    rcases run_step_pending A B m₀ hB p₀ labC t (by omega) hpend with ⟨he, -⟩ | ⟨q, a, r, he, -⟩
    · rw [he] at h; cases h
    · rw [he] at h; cases h
  have hpj := hsingle j (by omega) le_rfl
  have hpend : ∃ q, (𝓟) j q ≠ none := ⟨p₀, by rw [hpj]; simp⟩
  rcases run_step_pending A B m₀ hB p₀ labC t (by omega) hpend with ⟨he, -⟩ | ⟨q, a, r', he, hqa, hj1⟩
  · rw [he] at hjr; cases hjr
  have hq : q = p₀ := by
    by_contra hne; rw [hpj, Function.update_of_ne hne, hidle q] at hqa; cases hqa
  rw [hq] at hqa hj1
  rw [hpj] at hqa; simp at hqa; subst hqa
  refine ⟨j, by omega, ⟨r', he⟩, hnoinv, fun q' => ?_⟩
  rw [hj1, hpj]
  by_cases hq' : q' = p₀
  · rw [hq']; simp
  · simp [Function.update_of_ne hq', hidle q']

/-- The operations invoked before position `T` along `runLab`. -/
noncomputable def early (T : ℕ) : Finset ℕ := by
  classical exact (Finset.range T).filter fun a => Invoked (𝓗) a

lemma mem_early {T a : ℕ} : a ∈ early A B m₀ hB p₀ labC t T ↔ a < T ∧ Invoked (𝓗) a := by
  classical
  simp [early]

/-- After a stable node, `p₀`'s solo operations eventually return exactly the number of
operations invoked before them: there is a solo phase `[k, J]` of `p₀` starting and ending in
idle configurations whose operation returns `|early k|`. -/
theorem exists_good_phase (hNB : (atSys A B m₀).NonBlocking (atSys A B m₀).Proper)
    (hC : (atSys A B m₀).Proper labC) (hstab : Stable A B m₀ labC t) :
    ∃ k J, t ≤ k ∧ k < J ∧ (𝓗) k = some (.inv p₀ () ()) ∧
      (𝓗) J = some (.res k (early A B m₀ hB p₀ labC t k).card) ∧
      (∀ i, k < i → i ≤ J → ∀ p x op, (𝓗) i ≠ some (.inv p x op)) ∧
      (∀ q, (𝓟) (J + 1) q = none) := by
  classical
  obtain ⟨T1, hT1, hidle1⟩ := reach_idle A B m₀ hB p₀ labC t hNB hC t le_rfl
  have hph := fun k (hk : t ≤ k) (hi : ∀ q, (𝓟) k q = none) =>
    (idle_phase A B m₀ hB p₀ labC t hNB hC hk hi).2
  choose! J hJ using hph
  let I : ℕ → ℕ := fun s => (fun k => J k + 1)^[s] T1
  have hIsucc : ∀ s, I (s + 1) = J (I s) + 1 := fun s => Function.iterate_succ_apply' _ _ _
  have hIgood : ∀ s, t ≤ I s ∧ ∀ q, (𝓟) (I s) q = none := by
    intro s
    induction s with
    | zero => exact ⟨hT1, hidle1⟩
    | succ s ih =>
      rw [hIsucc]
      obtain ⟨h1, -, -, h4⟩ := hJ _ ih.1 ih.2
      exact ⟨by omega, h4⟩
  have hIinv : ∀ s, (𝓗) (I s) = some (.inv p₀ () ()) := fun s =>
    (idle_phase A B m₀ hB p₀ labC t hNB hC (hIgood s).1 (hIgood s).2).1
  obtain ⟨S, hS⟩ := hstab 𝓛 (runLab_proper A B m₀ hB p₀ labC t hC) (runLab_agree A B m₀ hB p₀ labC t)
  have hmem : ∀ s, ∃ k r, S k = some (I s, r) := fun s => by
    obtain ⟨-, ⟨r, hr⟩, -⟩ := hJ _ (hIgood s).1 (hIgood s).2
    exact hS.complete _ _ _ hr
  choose pos rpos hpos using hmem
  have hposlt : ∀ s, pos s < pos (s + 1) := by
    intro s
    obtain ⟨hlt, ⟨r, hr⟩, -, -⟩ := hJ _ (hIgood s).1 (hIgood s).2
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ := hS.rt (I s) (I (s + 1)) (J (I s)) r hr
      (by have := (hIgood s).1; omega) (by rw [hIsucc]; omega) ⟨p₀, (), (), hIinv (s + 1)⟩
      ⟨_, _, hpos (s + 1)⟩
    have e1 := hS.nodup k1 (pos s) _ r1 (rpos s) h1 (hpos s)
    have e2 := hS.nodup k2 (pos (s + 1)) _ r2 (rpos (s + 1)) h2 (hpos (s + 1))
    omega
  have hposmono : StrictMono pos := strictMono_nat_of_lt_succ hposlt
  have hposge : ∀ s, s ≤ pos s := fun s => hposmono.id_le s
  have hF : ∀ e ∈ early A B m₀ hB p₀ labC t (I 0), ∃ k, ∃ r, S k = some (e, r) := by
    intro e he
    obtain ⟨he1, p, x, op, hp⟩ := (mem_early A B m₀ hB p₀ labC t).1 he
    obtain ⟨j, -, r, hr⟩ := (pendInv_run A B m₀ hB p₀ labC t (I 0)).done p e x op he1 hp
      (by rw [(hIgood 0).2 p]; simp)
    exact hS.complete _ _ _ hr
  obtain ⟨M, hM⟩ := finset_bound hF
  have hearly : ∀ s, ∀ e ∈ early A B m₀ hB p₀ labC t (I s),
      e ∈ early A B m₀ hB p₀ labC t (I 0) ∨ ∃ s' < s, e = I s' := by
    intro s
    induction s with
    | zero => exact fun e he => Or.inl he
    | succ s ih =>
      intro e he
      obtain ⟨he1, p, x, op, hp⟩ := (mem_early A B m₀ hB p₀ labC t).1 he
      rw [hIsucc] at he1
      rcases lt_trichotomy e (I s) with h | h | h
      · rcases ih e ((mem_early A B m₀ hB p₀ labC t).2 ⟨h, p, x, op, hp⟩) with h' | ⟨s', hs', h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨s', by omega, h'⟩
      · exact Or.inr ⟨s, by omega, h⟩
      · obtain ⟨-, -, hnoinv, -⟩ := hJ _ (hIgood s).1 (hIgood s).2
        exact absurd hp (hnoinv e h (by omega) p x op)
  obtain ⟨hlt, ⟨r, hr⟩, hnoinv, hidle'⟩ := hJ _ (hIgood M).1 (hIgood M).2
  have hsub1 : ∀ b ∈ opsBefore S (pos M), b ∈ early A B m₀ hB p₀ labC t (I M) := by
    intro b hb
    obtain ⟨h1, h2⟩ := opsBefore_subset hS (hIgood M).1 hlt ⟨r, hr⟩ hnoinv (hpos M) b hb
    exact (mem_early A B m₀ hB p₀ labC t).2 ⟨h1, h2⟩
  have hsub2 : ∀ e ∈ early A B m₀ hB p₀ labC t (I M), e ∈ opsBefore S (pos M) := by
    intro e he
    rcases hearly M e he with h | ⟨s', hs', rfl⟩
    · obtain ⟨k, hk, r', hk'⟩ := hM e h
      exact mem_opsBefore.2 ⟨k, by have := hposge M; omega, r', hk'⟩
    · exact mem_opsBefore.2 ⟨pos s', hposmono hs', rpos s', hpos s'⟩
  have hcard : (early A B m₀ hB p₀ labC t (I M)).card = cntEntries S (pos M) := by
    rw [← card_opsBefore hS.nodup]
    congr 1
    ext e; exact ⟨hsub2 e, hsub1 e⟩
  obtain ⟨k', hk'⟩ := hS.resp _ _ _ hr (by have := (hIgood M).1; omega)
  have e1 := hS.nodup k' (pos M) _ r (rpos M) hk' (hpos M)
  subst e1
  have hresp := hS.legal.fai_resp hk'
  refine ⟨I M, J (I M), (hIgood M).1, hlt, hIinv M, ?_, hnoinv, hidle'⟩
  rw [hcard, ← hresp]; exact hr

end Run

/-! ### The shifted implementation `A'` and the simulation -/

section Shift

variable {P X BOp BRes L Q : Type} [DecidableEq P] [DecidableEq X]
  (A : Impl P Unit ℕ X BOp BRes L) (B : X → ObjType Q BOp BRes)

/-- Decrease the response of a return action by `v₀`. -/
def shiftAct (v₀ : ℕ) : Action X BOp BRes ℕ L → Action X BOp BRes ℕ L
  | .ret r l => .ret (r - v₀) l
  | a => a

/-- The algorithm `A` with initial local states `loc₀` and responses decreased by `v₀` (the
paper's `A'`: "a process executes the algorithm `A` for fetch&inc until it obtains a result `v`,
and then it returns `v − v₀`"). -/
def shiftImpl (loc₀ : P → L) (v₀ : ℕ) : Impl P Unit ℕ X BOp BRes L where
  locInit := loc₀
  invoke := A.invoke
  act p l := shiftAct v₀ (A.act p l)

/-- Configurations of `A` (at time `T₀ + k`) and of `A'` (at time `k`) correspond. -/
structure SimRel (T₀ : ℕ) (cA c' : ACfg P L X Q) : Prop where
  loc : cA.loc = c'.loc
  mem : cA.mem = c'.mem
  pend : ∀ p, cA.pend p = (c'.pend p).map (T₀ + ·)

/-- Events of `A` (at time `T₀ + k`) and of `A'` (at time `k`) correspond. -/
def EvRel (T₀ v₀ : ℕ) : Option (Ev P Unit Unit ℕ) → Option (Ev P Unit Unit ℕ) → Prop
  | none, none => True
  | some (.inv p x op), some (.inv p' x' op') => p = p' ∧ x = x' ∧ op = op'
  | some (.res a r), some (.res a' r') => a = T₀ + a' ∧ r' = r - v₀
  | _, _ => False

lemma step_sim {T₀ v₀ : ℕ} {loc₀ : P → L} {cA c' : ACfg P L X Q} (h : SimRel T₀ cA c') (k : ℕ)
    (l : ALab P Unit BRes Q) :
    Option.Rel (fun o o' => SimRel T₀ o.1 o'.1 ∧ EvRel T₀ v₀ o.2.1 o'.2.1)
      (atStep A B (T₀ + k) cA l) (atStep (shiftImpl A loc₀ v₀) B k c' l) := by
  obtain ⟨locA, pendA, memA⟩ := cA
  obtain ⟨loc', pend', mem'⟩ := c'
  obtain ⟨hl, hm, hp⟩ := h
  simp only at hl hm hp
  subst hl hm
  cases l with
  | inv p op =>
    simp only [atStep]
    rcases hq : pend' p with _ | a
    · have : pendA p = none := by rw [hp p, hq]; rfl
      rw [if_pos this, if_pos rfl]
      refine Option.Rel.some ⟨⟨rfl, rfl, fun q => ?_⟩, ⟨rfl, rfl, rfl⟩⟩
      simp only [Function.update_apply]
      split_ifs <;> simp [hp q]
    · have : pendA p ≠ none := by rw [hp p, hq]; simp
      rw [if_neg this, if_neg (by simp)]
      exact Option.Rel.none
  | step p =>
    simp only [atStep]
    rcases hq : pend' p with _ | a
    · have : pendA p = none := by rw [hp p, hq]; rfl
      rw [this]; exact Option.Rel.none
    · have : pendA p = some (T₀ + a) := by rw [hp p, hq]; rfl
      rw [this]
      simp only [shiftImpl]
      cases hact : A.act p (locA p) with
      | call x o kk => simp only [shiftAct]; exact Option.Rel.none
      | loc l' =>
        simp only [shiftAct]
        exact Option.Rel.some ⟨⟨rfl, rfl, hp⟩, trivial⟩
      | ret r l' =>
        simp only [shiftAct]
        refine Option.Rel.some ⟨⟨rfl, rfl, fun q => ?_⟩, ⟨rfl, rfl⟩⟩
        simp only [Function.update_apply]
        split_ifs <;> simp [hp q]
  | acc p r q =>
    simp only [atStep]
    rcases hq : pend' p with _ | a
    · have : pendA p = none := by rw [hp p, hq]; rfl
      rw [this]; exact Option.Rel.none
    · have : pendA p = some (T₀ + a) := by rw [hp p, hq]; rfl
      rw [this]
      simp only [shiftImpl]
      cases hact : A.act p (locA p) with
      | call x o kk =>
        simp only [shiftAct]
        split_ifs with hδ
        · exact Option.Rel.some ⟨⟨rfl, rfl, hp⟩, trivial⟩
        · exact Option.Rel.none
      | loc l' => simp only [shiftAct]; exact Option.Rel.none
      | ret r' l' => simp only [shiftAct]; exact Option.Rel.none

/-- `pre` before time `T₀`, then `lab'` shifted by `T₀`. -/
def catLab {Lab : Type} (pre lab' : ℕ → Option Lab) (T₀ : ℕ) : ℕ → Option Lab :=
  fun k => if k < T₀ then pre k else lab' (k - T₀)

lemma catLab_lt {Lab : Type} (pre lab' : ℕ → Option Lab) {T₀ k : ℕ} (h : k < T₀) :
    catLab pre lab' T₀ k = pre k := if_pos h

lemma catLab_add {Lab : Type} (pre lab' : ℕ → Option Lab) (T₀ k : ℕ) :
    catLab pre lab' T₀ (T₀ + k) = lab' k := by
  simp [catLab]

variable {m₀ m₀' : X → Q} {pre : ℕ → Option (ALab P Unit BRes Q)} {T₀ v₀ : ℕ} {loc₀ : P → L}

/-- The execution of `A` that runs `pre` up to `T₀` and then the steps of an execution `lab'`
of `A'` corresponds step by step to `lab'`. -/
lemma sim_run (hinit : SimRel T₀ ((atSys A B m₀).cfg pre T₀) ⟨loc₀, fun _ => none, m₀'⟩)
    (lab' : ℕ → Option (ALab P Unit BRes Q)) :
    ∀ k, SimRel T₀ ((atSys A B m₀).cfg (catLab pre lab' T₀) (T₀ + k))
      ((atSys (shiftImpl A loc₀ v₀) B m₀').cfg lab' k) := by
  intro k
  induction k with
  | zero =>
    rw [Nat.add_zero, (atSys A B m₀).cfg_congr (fun n hn => catLab_lt pre lab' hn) T₀ le_rfl]
    exact hinit
  | succ k ih =>
    rw [← Nat.add_assoc, atSys_cfg_succ, atSys_cfg_succ, catLab_add]
    rcases lab' k with _ | l
    · exact ih
    · have := step_sim A B (v₀ := v₀) (loc₀ := loc₀) ih k l
      simp only [Option.bind_some]
      revert this
      generalize atStep A B (T₀ + k) _ l = o1
      generalize atStep (shiftImpl A loc₀ v₀) B k _ l = o2
      intro this
      cases this with
      | some h => exact h.1
      | none => exact ih

lemma sim_hist (hinit : SimRel T₀ ((atSys A B m₀).cfg pre T₀) ⟨loc₀, fun _ => none, m₀'⟩)
    (lab' : ℕ → Option (ALab P Unit BRes Q)) (k : ℕ) :
    EvRel T₀ v₀ ((atSys A B m₀).hist (catLab pre lab' T₀) (T₀ + k))
      ((atSys (shiftImpl A loc₀ v₀) B m₀').hist lab' k) := by
  rw [atSys_hist, atSys_hist, catLab_add]
  rcases lab' k with _ | l
  · trivial
  · have := step_sim A B (v₀ := v₀) (loc₀ := loc₀) (sim_run A B (v₀ := v₀) hinit lab' k) k l
    simp only [Option.bind_some]
    revert this
    generalize atStep A B (T₀ + k) _ l = o1
    generalize atStep (shiftImpl A loc₀ v₀) B k _ l = o2
    intro this
    cases this with
    | some h => exact h.2
    | none => trivial

lemma sim_enabled (hinit : SimRel T₀ ((atSys A B m₀).cfg pre T₀) ⟨loc₀, fun _ => none, m₀'⟩)
    (lab' : ℕ → Option (ALab P Unit BRes Q)) (k : ℕ) (l : ALab P Unit BRes Q) :
    atStep A B (T₀ + k) ((atSys A B m₀).cfg (catLab pre lab' T₀) (T₀ + k)) l ≠ none ↔
      atStep (shiftImpl A loc₀ v₀) B k ((atSys (shiftImpl A loc₀ v₀) B m₀').cfg lab' k) l ≠ none := by
  have := step_sim A B (v₀ := v₀) (loc₀ := loc₀) (sim_run A B (v₀ := v₀) hinit lab' k) k l
  revert this
  generalize atStep A B (T₀ + k) _ l = o1
  generalize atStep (shiftImpl A loc₀ v₀) B k _ l = o2
  intro this
  cases this <;> simp

lemma evRel_inv {e e' : Option (Ev P Unit Unit ℕ)} (h : EvRel T₀ v₀ e e') {p : P} {x op : Unit} :
    e' = some (.inv p x op) ↔ e = some (.inv p x op) := by
  rcases e with _ | (⟨p1, x1, op1⟩ | ⟨a1, r1⟩) <;> rcases e' with _ | (⟨p2, x2, op2⟩ | ⟨a2, r2⟩) <;>
    simp_all [EvRel]

lemma evRel_res' {e e' : Option (Ev P Unit Unit ℕ)} (h : EvRel T₀ v₀ e e') {a' r' : ℕ}
    (he' : e' = some (.res a' r')) : ∃ r, e = some (.res (T₀ + a') r) ∧ r' = r - v₀ := by
  subst he'
  rcases e with _ | (⟨p1, x1, op1⟩ | ⟨a1, r1⟩) <;> simp_all [EvRel]

lemma evRel_res {e e' : Option (Ev P Unit Unit ℕ)} (h : EvRel T₀ v₀ e e') {a r : ℕ}
    (he : e = some (.res a r)) : ∃ a', a = T₀ + a' ∧ e' = some (.res a' (r - v₀)) := by
  subst he
  rcases e' with _ | (⟨p1, x1, op1⟩ | ⟨a1, r1⟩) <;> simp_all [EvRel]

open Classical in
/-- The history-level core of Proposition 18: if a `t`-linearization of `H''` has operation `k`
(a solo operation invoked after `t`, responding at `J` with the number `v₀ - 1` of operations
invoked before it, nothing being invoked in `(k, J]`), then the history `H'` of the steps after
`J` (with responses decreased by `v₀`) is linearizable: drop the first `v₀` operations. -/
lemma lin_of_phase {H'' H' : History P Unit Unit ℕ} {t k J v₀ : ℕ} {S : SeqHist ℕ}
    (hS : IsTLin (fun _ => fai) H'' t S) (htk : t ≤ k) (hkJ : k < J)
    (hv₀ : v₀ = ((Finset.range k).filter (Invoked H'')).card + 1)
    (hres : H'' J = some (.res k (v₀ - 1)))
    (hnoinv : ∀ i, k < i → i ≤ J → ∀ p x op, H'' i ≠ some (.inv p x op))
    (hrel : ∀ n, EvRel (J + 1) v₀ (H'' (J + 1 + n)) (H' n)) : Linearizable (fun _ => fai) H' := by
  classical
  set T₀ := J + 1 with hT₀
  set E := (Finset.range k).filter (Invoked H'') with hE
  obtain ⟨po, hpo⟩ := hS.resp k J (v₀ - 1) hres (by omega)
  -- the operations before `k` in `S` are exactly those invoked before `k`
  have hbefore : opsBefore S po = E := by
    apply Finset.eq_of_subset_of_card_le
    · intro b hb
      obtain ⟨h1, h2⟩ := opsBefore_subset hS htk hkJ ⟨_, hres⟩ hnoinv hpo b hb
      simp [hE, h1, h2]
    · rw [card_opsBefore hS.nodup, ← hS.legal.fai_resp hpo]; omega
  have hlate : ∀ i a r, S i = some (a, r) → T₀ ≤ a → po < i := by
    intro i a r hi ha
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ :=
      hS.rt k a J (v₀ - 1) hres (by omega) (by omega) (hS.legal.1 i a r hi) ⟨i, r, hi⟩
    have e1 := hS.nodup k1 po k r1 _ h1 hpo
    have e2 := hS.nodup k2 i a r2 r h2 hi
    omega
  have hearly : ∀ i a r, S i = some (a, r) → a < T₀ → a ∈ insert k E := by
    intro i a r hi ha
    have hinv := hS.legal.1 i a r hi
    rcases lt_trichotomy a k with h | h | h
    · simp [hE, h, hinv]
    · simp [h]
    · obtain ⟨p, x, op, hp⟩ := hinv
      exact absurd hp (hnoinv a h (by omega) p x op)
  -- the sequential history of the late operations
  let S' : SeqHist ℕ := fun i => match S i with
    | some (a, r) => if T₀ ≤ a then some (a - T₀, r - v₀) else none
    | none => none
  have hS' : ∀ i a' r', S' i = some (a', r') ↔ ∃ r, S i = some (T₀ + a', r) ∧ r' = r - v₀ := by
    intro i a' r'
    simp only [S']
    rcases hi : S i with _ | ⟨a, r⟩
    · simp
    · simp only
      split_ifs with h
      · constructor
        · intro he; cases he; exact ⟨r, by rw [Nat.add_sub_cancel' h], rfl⟩
        · rintro ⟨r0, he, rfl⟩; cases he; simp
      · simp only [reduceCtorEq, false_iff, not_exists, not_and]
        intro r0 he; cases he; omega
  have hS'nd : S'.Nodup := by
    intro i j a r1 r2 h1 h2
    obtain ⟨r1', h1', -⟩ := (hS' i a r1).1 h1
    obtain ⟨r2', h2', -⟩ := (hS' j a r2).1 h2
    exact hS.nodup i j _ _ _ h1' h2'
  have hcount : ∀ i a r, S i = some (a, r) → T₀ ≤ a → r = v₀ + cntEntries S' i := by
    intro i a r hi ha
    have hpi := hlate i a r hi ha
    rw [hS.legal.fai_resp hi, ← card_opsBefore hS.nodup, ← card_opsBefore hS'nd]
    have hkE : k ∉ E := by simp [hE]
    have hdisj : Disjoint (insert k E) ((opsBefore S' i).image (T₀ + ·)) := by
      rw [Finset.disjoint_left]
      intro b hb hb'
      obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hb'
      rcases Finset.mem_insert.1 hb with h | h
      · omega
      · simp [hE] at h; omega
    have heq : opsBefore S i = insert k E ∪ (opsBefore S' i).image (T₀ + ·) := by
      ext b
      simp only [Finset.mem_union, Finset.mem_image, mem_opsBefore]
      constructor
      · rintro ⟨i', hi', rb, hb⟩
        by_cases hbT : T₀ ≤ b
        · right
          refine ⟨b - T₀, ⟨i', hi', rb - v₀, (hS' i' _ _).2 ⟨rb, by rw [Nat.add_sub_cancel' hbT]; exact hb, rfl⟩⟩,
            Nat.add_sub_cancel' hbT⟩
        · left; exact hearly i' b rb hb (by omega)
      · rintro (hb | ⟨a', ⟨i', hi', r', h'⟩, rfl⟩)
        · rcases Finset.mem_insert.1 hb with rfl | hb
          · exact ⟨po, hpi, _, hpo⟩
          · rw [← hbefore, mem_opsBefore] at hb
            obtain ⟨i', hi', r', h'⟩ := hb
            exact ⟨i', by omega, r', h'⟩
        · obtain ⟨r0, h0, -⟩ := (hS' i' a' r').1 h'
          exact ⟨i', hi', r0, h0⟩
    rw [heq, Finset.card_union_of_disjoint hdisj, Finset.card_insert_of_notMem hkE,
      Finset.card_image_of_injective _ (add_right_injective T₀)]
    omega
  refine ⟨S', ⟨hS'nd, legal_fai_of_resp ?_ ?_, ?_, ?_, ?_⟩⟩
  · intro i a' r' h
    obtain ⟨r, h1, -⟩ := (hS' i a' r').1 h
    obtain ⟨p, x, op, hp⟩ := hS.legal.1 i _ r h1
    exact ⟨p, x, op, (evRel_inv (hrel a')).2 hp⟩
  · intro i a' r' h
    obtain ⟨r, h1, rfl⟩ := (hS' i a' r').1 h
    rw [hcount i _ r h1 (by omega)]; omega
  · intro a' j r' hj
    obtain ⟨r, hr, -⟩ := evRel_res' (hrel j) hj
    obtain ⟨i, r0, hi⟩ := hS.complete _ _ _ hr
    exact ⟨i, r0 - v₀, (hS' i a' _).2 ⟨r0, hi, rfl⟩⟩
  · intro a' b' j r' hj _ hjb hb hbm
    obtain ⟨r, hr, -⟩ := evRel_res' (hrel j) hj
    obtain ⟨p, x, op, hp⟩ := hb
    obtain ⟨ib, rb, hib⟩ := hbm
    obtain ⟨rb0, hib0, -⟩ := (hS' ib b' rb).1 hib
    obtain ⟨k1, k2, r1, r2, h12, h1, h2⟩ := hS.rt _ _ _ r hr (by omega) (by omega)
      ⟨p, x, op, (evRel_inv (hrel b')).1 hp⟩ ⟨ib, rb0, hib0⟩
    exact ⟨k1, k2, r1 - v₀, r2 - v₀, h12, (hS' k1 a' _).2 ⟨r1, h1, rfl⟩,
      (hS' k2 b' _).2 ⟨r2, h2, rfl⟩⟩
  · intro a' j r' hj _
    obtain ⟨r, hr, rfl⟩ := evRel_res' (hrel j) hj
    obtain ⟨i, hi⟩ := hS.resp _ _ _ hr (by omega)
    exact ⟨i, (hS' i a' _).2 ⟨r, hi, rfl⟩⟩

end Shift

/-! ### Proposition 18 -/

section Final

variable {P X BOp BRes L Q : Type} [DecidableEq P] [DecidableEq X]
  (A : Impl P Unit ℕ X BOp BRes L) (B : X → ObjType Q BOp BRes) (m₀ : X → Q)

theorem prop18_of_fintype [Fintype P] (hB : ∀ x, (B x).Total) (p₀ : P) (h17 : Lemma17Stmt P)
    (hEL : (atSys A B m₀).IsEventuallyLinearizable (atSys A B m₀).Proper fai)
    (hNB : (atSys A B m₀).NonBlocking (atSys A B m₀).Proper) :
    ∃ (loc₀ : P → L) (m₀' : X → Q) (v₀ : ℕ),
      (atSys (shiftImpl A loc₀ v₀) B m₀').IsLinearizable
        (atSys (shiftImpl A loc₀ v₀) B m₀').Proper fai ∧
      (atSys (shiftImpl A loc₀ v₀) B m₀').NonBlocking (atSys (shiftImpl A loc₀ v₀) B m₀').Proper := by
  classical
  obtain ⟨labC, t, hC, hstab⟩ := claim1 A B m₀ h17 hEL
  obtain ⟨k, J, htk, hkJ, hinv, hres, hnoinv, hidle⟩ :=
    exists_good_phase A B m₀ hB p₀ labC t hNB hC hstab
  set lab := runLab A B m₀ hB p₀ labC t with hlab
  set T₀ := J + 1 with hT₀
  set v₀ := (early A B m₀ hB p₀ labC t k).card + 1 with hv₀
  set C₀ := (atSys A B m₀).cfg lab T₀ with hC₀
  have hinit : SimRel T₀ ((atSys A B m₀).cfg lab T₀) ⟨C₀.loc, fun _ => none, C₀.mem⟩ :=
    ⟨rfl, rfl, fun p => by show _ = none; exact hidle p⟩
  have hproper : ∀ lab', (atSys (shiftImpl A C₀.loc v₀) B C₀.mem).Proper lab' →
      (atSys A B m₀).Proper (catLab lab lab' T₀) := by
    intro lab' hp' n l hl
    by_cases hn : n < T₀
    · rw [catLab_lt _ _ hn] at hl
      rw [(atSys A B m₀).cfg_congr (fun i hi => catLab_lt lab lab' (lt_trans hi hn)) n le_rfl]
      exact runLab_proper A B m₀ hB p₀ labC t hC n l hl
    · obtain ⟨n', rfl⟩ : ∃ n', n = T₀ + n' := ⟨n - T₀, by omega⟩
      rw [catLab_add] at hl
      exact (sim_enabled A B (v₀ := v₀) hinit lab' n' l).2 (hp' n' l hl)
  have hhist : ∀ lab' n, n < T₀ →
      (atSys A B m₀).hist (catLab lab lab' T₀) n = (atSys A B m₀).hist lab n := fun lab' n hn =>
    (atSys A B m₀).hist_congr (fun i hi => catLab_lt lab lab' hi) hn
  refine ⟨C₀.loc, C₀.mem, v₀, ?_, ?_⟩
  · intro lab' hp'
    obtain ⟨S, hS⟩ := hstab _ (hproper lab' hp') (fun n hn => by
      rw [catLab_lt _ _ (by omega)]; exact runLab_agree A B m₀ hB p₀ labC t n hn)
    refine lin_of_phase hS htk hkJ ?_ ?_ ?_ (fun n => sim_hist A B (v₀ := v₀) hinit lab' n)
    · rw [hv₀]
      congr 2
      ext a
      simp only [mem_early, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
        obtain ⟨p, x, op, hp⟩ := h2
        exact ⟨p, x, op, (hhist lab' a (by omega)).trans hp⟩
      · rintro ⟨h1, h2⟩; refine ⟨h1, ?_⟩
        obtain ⟨p, x, op, hp⟩ := h2
        exact ⟨p, x, op, (hhist lab' a (by omega)).symm.trans hp⟩
    · rw [hhist lab' J (by omega)]
      convert hres using 3
      omega
    · intro i hi hiJ p x op h
      rw [hhist lab' i (by omega)] at h
      exact hnoinv i hi hiJ p x op h
  · intro lab' hp' N a p op ha haN hnores hinf
    have hp'' := hproper lab' hp'
    have hrel := sim_hist A B (v₀ := v₀) hinit lab'
    have hWF := at_wellFormed_hist A B m₀ (catLab lab lab' T₀)
    obtain ⟨j, hj, b, r, hjr⟩ := hNB _ hp'' (T₀ + N) (T₀ + a) p op
      ((evRel_inv (hrel a)).1 ha) (by omega) (fun j hj r hjr => by
        by_cases hjT : j < T₀
        · have := (hWF.res_inv _ j r hjr).1; omega
        · obtain ⟨j', rfl⟩ : ∃ j', j = T₀ + j' := ⟨j - T₀, by omega⟩
          obtain ⟨a'', ha'', hj'⟩ := evRel_res (hrel j') hjr
          have : a'' = a := by omega
          subst this
          exact hnores j' (by omega) _ hj')
      (fun N' => by
        obtain ⟨n, hn, hne⟩ := hinf N'
        exact ⟨T₀ + n, by omega, by rw [catLab_add]; exact hne⟩)
    obtain ⟨j', rfl⟩ : ∃ j', j = T₀ + j' := ⟨j - T₀, by omega⟩
    obtain ⟨b', -, hb'⟩ := evRel_res (hrel j') hjr
    exact ⟨j', by omega, b', r - v₀, hb'⟩

/-- **Proposition 18** of [Guerraoui–Ruppert, PODC 2014]. If an `n`-process implementation `A`
of a fetch&increment object (initialized to `0`) from atomic base objects of types `B x`
(with total operations, initial states `m₀`) is eventually linearizable and non-blocking, then
there is an `n`-process linearizable non-blocking implementation of fetch&increment from the
same base objects: `A` itself, with initial local states `loc₀`, initial base-object states
`m₀'` (those of a stable configuration `C₀`) and responses decreased by `v₀`. -/
theorem prop18 [Finite P] [Nonempty P] (hB : ∀ x, (B x).Total)
    (hEL : (atSys A B m₀).IsEventuallyLinearizable (atSys A B m₀).Proper fai)
    (hNB : (atSys A B m₀).NonBlocking (atSys A B m₀).Proper) :
    ∃ (loc₀ : P → L) (m₀' : X → Q) (v₀ : ℕ),
      (atSys (shiftImpl A loc₀ v₀) B m₀').IsLinearizable
        (atSys (shiftImpl A loc₀ v₀) B m₀').Proper fai ∧
      (atSys (shiftImpl A loc₀ v₀) B m₀').NonBlocking (atSys (shiftImpl A loc₀ v₀) B m₀').Proper := by
  haveI := Fintype.ofFinite P
  exact prop18_of_fintype A B m₀ hB (Classical.arbitrary P)
    (fun _ hH _ _ h₀ hpre => lemma17 hH h₀ hpre) hEL hNB

end Final

/-- **Corollary 19, reduction step.** If no linearizable non-blocking implementation of
fetch&increment from atomic objects of types `B` exists (with any initial states), then no
eventually linearizable non-blocking one exists either. Corollary 19 is the instance with two
processes and read/write registers; its hypothesis is the classical fact that registers and a
linearizable fetch&increment solve two-process consensus while registers alone cannot
[Herlihy 1991, Loui–Abu-Amara 1987], which we do not formalize. -/
theorem cor19_of_no_linearizable {P X BOp BRes Q : Type} [DecidableEq P] [DecidableEq X]
    [Finite P] [Nonempty P] (B : X → ObjType Q BOp BRes) (hB : ∀ x, (B x).Total)
    (hno : ∀ (L : Type) (A : Impl P Unit ℕ X BOp BRes L) (m₀ : X → Q),
      ¬ ((atSys A B m₀).IsLinearizable (atSys A B m₀).Proper fai ∧
        (atSys A B m₀).NonBlocking (atSys A B m₀).Proper))
    (L : Type) (A : Impl P Unit ℕ X BOp BRes L) (m₀ : X → Q) :
    ¬ ((atSys A B m₀).IsEventuallyLinearizable (atSys A B m₀).Proper fai ∧
      (atSys A B m₀).NonBlocking (atSys A B m₀).Proper) := by
  rintro ⟨hEL, hNB⟩
  obtain ⟨loc₀, m₀', v₀, h1, h2⟩ := prop18 A B m₀ hB hEL hNB
  exact hno L (shiftImpl A loc₀ v₀) m₀' ⟨h1, h2⟩

end Podc.EventualLinParadox
