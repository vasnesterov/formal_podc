import Papers.PODC2016.CollaborativeListSpec.LowerBound

/-!
# Theorems 8 and 9 (metadata overhead lower bound), statements

Numbering of the TCS 2021 version; in the PODC 2016 version these are Theorems 4 and 5.
-/

namespace Podc.CollaborativeListSpec

/-! ### Counting -/

theorem append_true_replicate_inj {l₁ l₂ : List Bool} {k₁ k₂ : ℕ}
    (h : l₁ ++ true :: List.replicate k₁ false = l₂ ++ true :: List.replicate k₂ false) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons b l₂ =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have : true ∈ List.replicate k₁ false := by rw [h.2]; simp
      simp at this
  | cons a l₁ ih =>
    cases l₂ with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      have : true ∈ List.replicate k₂ false := by rw [← h.2]; simp
      simp at this
    | cons b l₂ =>
      simp only [List.cons_append, List.cons.injEq] at h
      rw [h.1, ih h.2]

/-- **The counting step of Theorem 9.** If `2^d` objects are pairwise distinct, then for every
injective encoding into bit strings one of them takes at least `d` bits. -/
theorem exists_long_code {d : ℕ} {α : Type} {f : (Fin d → Bool) → α} (hf : Function.Injective f)
    {enc : α → List Bool} (henc : Function.Injective enc) : ∃ v, d ≤ (enc (f v)).length := by
  by_contra hcon
  push_neg at hcon
  let pad : (Fin d → Bool) → List.Vector Bool d := fun v =>
    ⟨enc (f v) ++ true :: List.replicate (d - 1 - (enc (f v)).length) false, by
      have := hcon v; simp; omega⟩
  have hinj : Function.Injective pad := by
    intro v v' h
    have h' := congrArg Subtype.val h
    exact hf (henc (append_true_replicate_inj h'))
  have hbij := (Fintype.bijective_iff_injective_and_card pad).2 ⟨hinj, by simp⟩
  obtain ⟨v, hv⟩ := hbij.2 ⟨List.replicate d false, by simp⟩
  have h1 : (pad v).1 = List.replicate d false := by rw [hv]
  have hmem : true ∈ List.replicate d false := by
    rw [← h1]; simp [pad]
  simp at hmem

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U] {P : Protocol Rep (LOp U) (List U) Q M}

/-- Deletion indicator. -/
def isDelB {Rep U : Type} : Act Rep (LOp U) → Bool
  | .doOp _ (.del _) => true
  | _ => false

theorem numDel_eq {Rep U : Type} (α : List (Act Rep (LOp U))) : numDel α = α.countP isDelB := by
  unfold numDel isDelB; rfl

theorem numDel_pre_succ (g : ℕ → Act Rep (LOp U)) (n : ℕ) :
    numDel (pre g (n + 1)) = numDel (pre g n) + if isDelB (g n) then 1 else 0 := by
  rw [numDel_eq, numDel_eq, pre_succ, List.countP_append]
  simp [List.countP_cons]

theorem isDelB_iff (a : Act Rep (LOp U)) : isDelB a = true ↔ ∃ r x, a = .doOp r (.del x) := by
  rcases a with ⟨r, ⟨x, k⟩ | x | _⟩ | r | ⟨r, s⟩ <;> simp [isDelB]

namespace Params

variable (E : Params Rep U) (w : ℕ → Bool)

theorem numDel_act (n : ℕ) : numDel (pre (E.act w) n) =
    (min n (5 * E.d + 7) - min n (3 * E.d + 5)) + if E.odd = true ∧ 5 * E.d + 9 ≤ n then 1 else 0 := by
  induction n with
  | zero => simp [numDel, pre]
  | succ n ih =>
    rw [numDel_pre_succ, ih]
    have key : isDelB (E.act w n) = true ↔
        (3 * E.d + 5 ≤ n ∧ n < 5 * E.d + 7) ∨ (E.odd = true ∧ n = 5 * E.d + 8) := by
      rw [isDelB_iff]
      constructor
      · rintro ⟨r, x, h⟩
        obtain ⟨-, ⟨t, ht, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨ho, rfl, -⟩⟩ := (E.act_del_iff w).1 h
        · left; omega
        · left; omega
        · right; exact ⟨ho, rfl⟩
      · rintro (⟨h1, h2⟩ | ⟨ho, rfl⟩)
        · rcases Nat.even_or_odd (n - (3 * E.d + 5)) with ⟨t, ht⟩ | ⟨t, ht⟩
          · exact ⟨_, _, (E.act_del_iff w).2 ⟨rfl, Or.inl ⟨t, by omega, Or.inl ⟨by omega, rfl⟩⟩⟩⟩
          · exact ⟨_, _, (E.act_del_iff w).2 ⟨rfl, Or.inl ⟨t, by omega, Or.inr ⟨by omega, rfl⟩⟩⟩⟩
        · exact ⟨_, _, E.act_delBee w ho⟩
    cases ho : E.odd
    · simp only [ho, Bool.false_eq_true, false_and, or_false, if_false, add_zero] at key ⊢
      by_cases h : isDelB (E.act w n) = true
      · rw [if_pos h]; have := key.1 h; omega
      · rw [if_neg h]; have := mt key.2 h; omega
    · simp only [ho, true_and] at key ⊢
      by_cases h : isDelB (E.act w n) = true
      · rw [if_pos h]; have := key.1 h; split_ifs <;> omega
      · rw [if_neg h]; have := mt key.2 h; split_ifs <;> omega

theorem gr_lt {p : ℕ} (h : p < E.Lα) : E.gr w p = E.act w p := by rw [gr, if_pos h]

theorem gr_Lα : E.gr w E.Lα = .doOp E.r1 .read := by rw [gr, if_neg (lt_irrefl _)]

theorem pre_gr : pre (E.gr w) E.Lα = pre (E.act w) E.Lα :=
  pre_congr (g := E.gr w) (g' := E.act w) (n := E.Lα) (fun p hp => E.gr_lt w hp)

variable {w}

/-- The execution `α_w` followed by a read of `R₁`: admitted, well-formed, and the read returns `∗`
("Finally, we read the list at `R₁`, observing that it is `∗`"). -/
theorem alpha_read (hP : PushBased P Weak (LBAdm P)) :
    P.WF (pre (E.gr w) (E.Lα + 1)) ∧ LBAdm P (pre (E.gr w) (E.Lα + 1)) ∧
      rval P (E.gr w) E.Lα = [E.Star] := by
  obtain ⟨hwf, hadm⟩ := E.alpha_ok (w := w) hP E.Lα le_rfl
  rw [← E.pre_gr w] at hwf hadm
  have hnr : ∀ (q : ℕ) (r : Rep) (s : ℕ), (pre (E.gr w) (E.Lα + 1))[q]? ≠ some (.recv r s) := by
    intro q r s h
    rw [pre_getElem?] at h; split_ifs at h with hq
    have h := Option.some.inj h
    by_cases hq' : q < E.Lα
    · rw [E.gr_lt w hq'] at h; exact E.act_ne_recv w h
    · rw [show q = E.Lα by omega, E.gr_Lα] at h; cases h
  have hwf' : P.WF (pre (E.gr w) (E.Lα + 1)) := WF_pre_succ.2 ⟨hwf, by rw [E.gr_Lα]; trivial⟩
  have hadm' : LBAdm P (pre (E.gr w) (E.Lα + 1)) := by
    refine ⟨causalAtomic_of_noRecv hnr, E.uniqueIns_of_insAt (i := 0) (fun q hq r x k h => ?_),
      DelOK_pre_succ hadm.2.2 (fun r a h => by rw [E.gr_Lα] at h; cases h)⟩
    by_cases hq' : q < E.Lα
    · rw [E.gr_lt w hq'] at h; exact E.insAt_of_act w h
    · rw [show q = E.Lα by omega, E.gr_Lα] at h; cases h
  refine ⟨hwf', hadm', ?_⟩
  obtain ⟨lo, -, hc, hirr, -⟩ := hP.spec _ hwf' hadm'
  have hrep : ∀ p < E.Lα + 1, (E.gr w p).rep = E.r1 := by
    intro p hp; unfold gr; split_ifs
    · exact E.act_rep w p
    · rfl
  have hmem : ∀ x, x ∈ rval P (E.gr w) E.Lα ↔ x = E.Star := by
    intro x
    rw [mem_rval_of_single hrep (visHB_absWF _) hc (by omega) (E.gr_Lα w)]
    have hi : (∃ q ≤ E.Lα, ∃ k, E.gr w q = .doOp E.r1 (.ins x k)) ↔
        ∃ q ≤ E.Lα, ∃ k, E.act w q = .doOp E.r1 (.ins x k) := by
      constructor
      · rintro ⟨q, hq, k, h⟩
        rcases hq.lt_or_eq with hq | rfl
        · exact ⟨q, hq.le, k, by rwa [E.gr_lt w hq] at h⟩
        · rw [E.gr_Lα] at h; cases h
      · rintro ⟨q, hq, k, h⟩
        obtain ⟨-, h'⟩ := (E.act_ins_iff w).1 h
        have : q < E.Lα := by
          rw [Lα_eq]; rcases h' with ⟨t, ht, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨rfl, -⟩ | ⟨ho, rfl, -⟩
          all_goals (try split_ifs) <;> simp_all <;> omega
        exact ⟨q, hq, k, by rwa [E.gr_lt w this]⟩
    have hd : (∃ q ≤ E.Lα, E.gr w q = .doOp E.r1 (.del x)) ↔
        ∃ q ≤ E.Lα, E.act w q = .doOp E.r1 (.del x) := by
      constructor
      · rintro ⟨q, hq, h⟩
        rcases hq.lt_or_eq with hq | rfl
        · exact ⟨q, hq.le, by rwa [E.gr_lt w hq] at h⟩
        · rw [E.gr_Lα] at h; cases h
      · rintro ⟨q, hq, h⟩
        obtain ⟨-, h'⟩ := (E.act_del_iff w).1 h
        have : q < E.Lα := by
          rw [Lα_eq]; rcases h' with ⟨t, ht, ⟨rfl, -⟩ | ⟨rfl, -⟩⟩ | ⟨ho, rfl, -⟩
          all_goals (try split_ifs) <;> simp_all <;> omega
        exact ⟨q, hq, by rwa [E.gr_lt w this]⟩
    rw [hi, hd, E.insB_iff, E.delB_iff]
    have hL : 5 * E.d + 8 ≤ E.Lα ∧ (E.odd = true → 5 * E.d + 10 ≤ E.Lα) := by
      rw [Lα_eq]; constructor <;> [omega; (intro h; simp [h])]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h1 with ⟨t, ht, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩ | ⟨ho, -, rfl⟩
      · exact absurd (Or.inl ⟨t, ht, Or.inl ⟨by omega, rfl⟩⟩) h2
      · exact absurd (Or.inl ⟨t, ht, Or.inr ⟨by omega, rfl⟩⟩) h2
      · rfl
      · exact absurd (Or.inr ⟨ho, by have := hL.2 ho; omega, rfl⟩) h2
    · rintro rfl
      refine ⟨Or.inr (Or.inl ⟨by omega, rfl⟩), ?_⟩
      rintro (⟨t, -, ⟨-, h⟩ | ⟨-, h⟩⟩ | ⟨-, -, h⟩) <;> simp at h
  have hnd := nodup_of_pairwise (hc _ _ _ _ (hist_pre_eq (P := P) (show E.Lα < E.Lα + 1 by omega)
    (E.gr_Lα w))).2.1 hirr
  have hp := (List.perm_ext_iff_of_nodup hnd (List.nodup_singleton E.Star)).2 (by simpa using hmem)
  exact List.perm_singleton.1 hp

theorem buf_none (w : ℕ → Bool) : ((P.exec (pre (E.act w) E.Lα)).st E.r1).2 = none := by
  have h1 : 1 ≤ E.Lα := by rw [Lα_eq]; omega
  obtain ⟨m, hm⟩ : ∃ m, E.Lα = m + 1 := ⟨E.Lα - 1, by omega⟩
  rw [hm, pre_succ, Protocol.exec_concat, show m = E.Lα - 1 by omega, E.act_last w]
  simp [Protocol.step]

end Params

/-- The bits `w 1, …, w d` of a string `v : Fin d → Bool` (other positions are `false`). -/
def bitsOf {d : ℕ} (v : Fin d → Bool) (j : ℕ) : Bool :=
  if h : 1 ≤ j ∧ j ≤ d then v ⟨j - 1, by omega⟩ else false

theorem bitsOf_inj {d : ℕ} {v v' : Fin d → Bool}
    (h : ∀ j, 1 ≤ j → j ≤ d → bitsOf v j = bitsOf v' j) : v = v' := by
  funext ⟨k, hk⟩
  have := h (k + 1) (by omega) (by omega)
  simpa [bitsOf, hk, Nat.succ_le_of_lt hk] using this

/-- **Theorem 9** (TCS 2021 numbering; Theorem 5 of PODC 2016). Let `R` be a push-based protocol
with at least three replicas that satisfies the weak list specification. For every `D ≥ 4` and
every replica `R₁` there is an execution with exactly `D` deletions, satisfying causal atomic
broadcast (and the user assumptions), and a state `σ` of `R₁` in it, reached before `R₁` receives any
message, whose user-visible content is the one-element list `[u]` (`u` fixed in advance) and whose
internal state needs at least `⌊(D - 2)/2⌋` bits in any injective binary encoding: its metadata
overhead is `Ω(D)`.

The protocol only has to be push-based (in particular, correct) on executions with causal atomic
broadcast that respect the user assumptions (`LBAdm`), which makes the hypothesis weaker than the
paper's (see `theorem9_causal` for the paper's form). The list universe `U` is infinite. -/
theorem theorem9 [Fintype Rep] [Infinite U] (hn : 3 ≤ Fintype.card Rep)
    (hP : PushBased P Weak (LBAdm P)) :
    ∃ u : U, ∀ D, 4 ≤ D → ∀ r₁ : Rep, ∀ enc : Q → List Bool, Function.Injective enc →
      ∃ α : List (Act Rep (LOp U)), P.WF α ∧ CausalAtomic α ∧ UserOK P α ∧ numDel α = D ∧
        ∃ n ≤ α.length, (∀ q < n, ∀ s, α[q]? ≠ some (.recv r₁ s)) ∧
          ((P.exec (α.take n)).st r₁).2 = none ∧
          P.resp r₁ ((P.exec (α.take n)).st r₁) .read = [u] ∧
          (D - 2) / 2 ≤ (enc ((P.exec (α.take n)).st r₁).1).length := by
  let sym := Infinite.natEmbedding U
  refine ⟨sym 1, fun D hD r₁ enc henc => ?_⟩
  obtain ⟨r₂, r₃, h12, h13, h23⟩ : ∃ r₂ r₃ : Rep, r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ := by
    obtain ⟨a, b, c, hab, hac, hbc⟩ := (Fintype.two_lt_card_iff (α := Rep)).1 (by omega)
    by_cases ha : a = r₁
    · subst ha; exact ⟨b, c, hab, hac, hbc⟩
    by_cases hb : b = r₁
    · subst hb; exact ⟨a, c, Ne.symm hab, hbc, hac⟩
    · exact ⟨a, b, Ne.symm ha, Ne.symm hb, hab⟩
  let E : Params Rep U := ⟨(D - 2) / 2, decide (D % 2 = 1), r₁, r₂, r₃, sym, sym.injective,
    h12, h13, h23⟩
  let F : (Fin E.d → Bool) → Q := fun v => ((P.exec (pre (E.act (bitsOf v)) E.Lα)).st r₁).1
  have hF : Function.Injective F := by
    intro v v' h
    apply bitsOf_inj
    apply E.state_determines_bits hP
    rw [Prod.ext_iff]
    exact ⟨h, by rw [E.buf_none, E.buf_none]⟩
  obtain ⟨v, hv⟩ := exists_long_code hF henc
  obtain ⟨hwf, hadm, hread⟩ := E.alpha_read (w := bitsOf v) hP
  have htake : (pre (E.gr (bitsOf v)) (E.Lα + 1)).take E.Lα = pre (E.act (bitsOf v)) E.Lα := by
    rw [pre_take, min_eq_left (by omega), E.pre_gr]
  refine ⟨_, hwf, hadm.1, hadm.2, ?_, E.Lα, by simp, ?_, ?_, ?_, ?_⟩
  · rw [numDel_pre_succ, E.gr_Lα, E.pre_gr, E.numDel_act]
    simp only [isDelB, Bool.false_eq_true, if_false, add_zero]
    have hL := Params.Lα_eq E
    show (min E.Lα (5 * ((D - 2) / 2) + 7) - min E.Lα (3 * ((D - 2) / 2) + 5)) +
      (if decide (D % 2 = 1) = true ∧ 5 * ((D - 2) / 2) + 9 ≤ E.Lα then 1 else 0) = D
    have hL' : E.Lα = 5 * ((D - 2) / 2) + 8 + if D % 2 = 1 then 2 else 0 := by
      rw [hL]; simp [E]
    rw [hL']
    split_ifs <;> simp_all <;> omega
  · intro q hq s h
    rw [pre_getElem?_of_lt _ (by omega), E.gr_lt _ hq] at h
    exact E.act_ne_recv _ (Option.some.inj h)
  · rw [htake]; exact E.buf_none _
  · rw [htake]
    have : rval P (E.gr (bitsOf v)) E.Lα = P.resp r₁ ((P.exec (pre (E.act (bitsOf v)) E.Lα)).st r₁) .read := by
      simp only [rval, E.gr_Lα, E.pre_gr]; rfl
    rw [← this, hread]; rfl
  · rw [htake]; exact hv

/-- **Theorem 9** in the paper's form: the protocol is push-based on all executions with causal
broadcast (Definition 13 as stated). -/
theorem theorem9_causal [Fintype Rep] [Infinite U] (hn : 3 ≤ Fintype.card Rep)
    (hP : PushBased P Weak (fun α => CausalBroadcast α ∧ UserOK P α)) :
    ∃ u : U, ∀ D, 4 ≤ D → ∀ r₁ : Rep, ∀ enc : Q → List Bool, Function.Injective enc →
      ∃ α : List (Act Rep (LOp U)), P.WF α ∧ CausalAtomic α ∧ UserOK P α ∧ numDel α = D ∧
        ∃ n ≤ α.length, (∀ q < n, ∀ s, α[q]? ≠ some (.recv r₁ s)) ∧
          ((P.exec (α.take n)).st r₁).2 = none ∧
          P.resp r₁ ((P.exec (α.take n)).st r₁) .read = [u] ∧
          (D - 2) / 2 ≤ (enc ((P.exec (α.take n)).st r₁).1).length :=
  theorem9 hn (hP.mono fun _ h => ⟨h.1.causal, h.2⟩)

end Podc.CollaborativeListSpec

namespace Podc.CollaborativeListSpec

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U] {P : Protocol Rep (LOp U) (List U) Q M}

/-- The metadata overhead of a state `σ = (q, m)` of replica `r` (Section 3.3): the size of the
internal state `q` in the encoding `enc`, divided by the size (measured by `sz`) of the list `w`
such that `do(read, w)` is enabled in `σ`. -/
def metadataOverhead (P : Protocol Rep (LOp U) (List U) Q M) (enc : Q → List Bool)
    (sz : List U → ℕ) (r : Rep) (σ : Q × Option M) : ℚ :=
  ((enc σ.1).length : ℚ) / (sz (P.resp r σ .read) : ℚ)

/-- **Theorem 8** (TCS 2021; Theorem 4 of PODC 2016): the worst-case metadata overhead of a
push-based protocol with `n ≥ 3` replicas satisfying the weak list specification, over executions
with `D` deletions, is `Ω(D)`: for every injective encoding of internal states and every size
measure of lists there is `c > 0` such that for all `D ≥ 4` some execution with `D` deletions
(and causal atomic broadcast) has a replica state with metadata overhead at least `c · D`. -/
theorem theorem8 [Fintype Rep] [Infinite U] (hn : 3 ≤ Fintype.card Rep)
    (hP : PushBased P Weak (fun α => CausalBroadcast α ∧ UserOK P α))
    (enc : Q → List Bool) (henc : Function.Injective enc) (sz : List U → ℕ)
    (hsz : ∀ l, l ≠ [] → 0 < sz l) :
    ∃ c : ℚ, 0 < c ∧ ∀ D, 4 ≤ D →
      ∃ α : List (Act Rep (LOp U)), P.WF α ∧ CausalAtomic α ∧ UserOK P α ∧ numDel α = D ∧
        ∃ r n, n ≤ α.length ∧ c * D ≤ metadataOverhead P enc sz r ((P.exec (α.take n)).st r) := by
  obtain ⟨u, hu⟩ := theorem9_causal hn hP
  have hs : 0 < sz [u] := hsz _ (by simp)
  obtain ⟨r₁⟩ : Nonempty Rep := Fintype.card_pos_iff.1 (by omega)
  refine ⟨1 / (5 * sz [u]), by positivity, fun D hD => ?_⟩
  obtain ⟨α, hwf, hca, hu', hdel, n, hn', -, -, hread, hlen⟩ := hu D hD r₁ enc henc
  refine ⟨α, hwf, hca, hu', hdel, r₁, n, hn', ?_⟩
  unfold metadataOverhead
  rw [hread]
  have h5 : (D : ℚ) ≤ 5 * ((D - 2) / 2 : ℕ) := by exact_mod_cast (by omega : D ≤ 5 * ((D - 2) / 2))
  have hl : (((D - 2) / 2 : ℕ) : ℚ) ≤ (enc ((P.exec (α.take n)).st r₁).1).length := by
    exact_mod_cast hlen
  have hs' : (0 : ℚ) < sz [u] := by exact_mod_cast hs
  rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hs']
  nlinarith

end Podc.CollaborativeListSpec
