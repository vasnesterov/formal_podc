import Papers.PODC2016.CollaborativeListSpec.SpecFacts
import Papers.PODC2016.CollaborativeListSpec.EncodingActs

/-!
# The encoding execution `α_w` (proof of Theorem 9, "Encoding w")

For a push-based protocol satisfying the weak list specification (on executions with causal
atomic broadcast and the user assumptions), every prefix of `α_w` is a well-formed admitted
execution (the sends are enabled because the protocol is push-based), and the responses of `R₁`
during the insertion phase are the intended lists `L_j` and `L_∗`.
-/

namespace Podc.CollaborativeListSpec

variable {Rep U Q M : Type} [DecidableEq Rep] [DecidableEq U]

/-- The executions admitted in the lower bound: causal atomic broadcast and the user
assumptions. -/
def LBAdm (P : Protocol Rep (LOp U) (List U) Q M) (α : List (Act Rep (LOp U))) : Prop :=
  CausalAtomic α ∧ UserOK P α

variable {P : Protocol Rep (LOp U) (List U) Q M}

/-- Extending `DelOK` by one event. -/
theorem DelOK_pre_succ {g : ℕ → Act Rep (LOp U)} {n : ℕ} (h : DelOK P (pre g n))
    (hn : ∀ r a, g n = .doOp r (.del a) → ∃ q < n, ∃ op v, P.hist (pre g n) q = some (r, op, v) ∧
      a ∈ v ∧ ∀ q', q < q' → q' < n → ∀ op', g q' ≠ .doOp r op') :
    DelOK P (pre g (n + 1)) := by
  intro p r a hp
  rw [pre_getElem?] at hp
  split_ifs at hp with hpn
  have hgp := Option.some.inj hp
  rcases Nat.lt_succ_iff_lt_or_eq.1 hpn with hpn | rfl
  · obtain ⟨q, hqp, op, v, hq, ha, hbet⟩ := h p r a (by rw [pre_getElem?_of_lt g hpn, hgp])
    refine ⟨q, hqp, op, v, ?_, ha, ?_⟩
    · rw [← hist_pre (m := n) (by omega) (by omega)]; exact hq
    · intro q' h1 h2 op'
      have := hbet q' h1 h2 op'
      rwa [pre_getElem?_of_lt g (by omega)] at this ⊢
  · obtain ⟨q, hqp, op, v, hq, ha, hbet⟩ := hn r a hgp
    refine ⟨q, hqp, op, v, ?_, ha, ?_⟩
    · rw [← hist_pre (m := p) (by omega) (by omega)]; exact hq
    · intro q' h1 h2 op'
      rw [pre_getElem?_of_lt g (by omega)]
      simpa using hbet q' h1 h2 op'

/-- Executions without receive events satisfy causal atomic broadcast. -/
theorem causalAtomic_of_noRecv {α : List (Act Rep (LOp U))}
    (h : ∀ (q : ℕ) (r : Rep) (s : ℕ), α[q]? ≠ some (Act.recv r s)) : CausalAtomic α :=
  ⟨fun _ _ _ _ _ _ _ hq => absurd hq (h _ _ _), fun _ _ _ _ hq => absurd hq (h _ _ _),
    fun _ _ _ _ _ _ _ hq => absurd hq (h _ _ _)⟩

/-- A criterion for causal atomic broadcast: there is a broadcast order (ranks `rk` of the send
events, consistent with happens-before) and every replica `r` receives the first `c r` messages
of this order, in order, at the increasing positions `pos r 0 < pos r 1 < …`. -/
theorem causalAtomic_of_rank {α : List (Act Rep (LOp U))} (rk : ℕ → ℕ) (c : Rep → ℕ)
    (pos : Rep → ℕ → ℕ) (hmono : ∀ r k k', k < k' → k' < c r → pos r k < pos r k')
    (hrecv : ∀ q r s, α[q]? = some (Act.recv r s) ↔ ∃ k < c r, q = pos r k ∧ IsSend α s ∧ rk s = k)
    (hinj : ∀ s s', IsSend α s → IsSend α s' → rk s = rk s' → s = s')
    (hhb : ∀ s s', IsSend α s → IsSend α s' → HB α s s' → rk s < rk s') : CausalAtomic α := by
  refine ⟨?_, ?_, ?_⟩
  · intro s s' r q hs hs' hss hq
    obtain ⟨k, hk, rfl, -, rfl⟩ := (hrecv _ _ _).1 hq
    have hlt := hhb s s' hs hs' hss
    exact ⟨pos r (rk s), hmono r _ _ hlt hk, (hrecv _ _ _).2 ⟨rk s, by omega, rfl, hs, rfl⟩⟩
  · intro q q' r s hq hq'
    obtain ⟨k, -, rfl, -, rfl⟩ := (hrecv _ _ _).1 hq
    obtain ⟨k', -, rfl, -, hk'⟩ := (hrecv _ _ _).1 hq'
    rw [hk']
  · intro r r' s s' q₁ q₂ q₃ h₁ h₂ h12 h₃
    obtain ⟨k₁, hk₁, rfl, hs, rfl⟩ := (hrecv _ _ _).1 h₁
    obtain ⟨k₂, hk₂, rfl, hs', rfl⟩ := (hrecv _ _ _).1 h₂
    obtain ⟨k₃, hk₃, rfl, -, hk₃'⟩ := (hrecv _ _ _).1 h₃
    subst hk₃'
    have hlt : rk s < rk s' := by
      by_contra hc
      rcases Nat.lt_or_ge (rk s') (rk s) with h | h
      · exact absurd h12 (not_lt.2 (hmono r _ _ h hk₁).le)
      · obtain rfl := hinj s s' hs hs' (by omega)
        exact lt_irrefl _ h12
    exact ⟨pos r' (rk s), hmono r' _ _ hlt hk₃, (hrecv _ _ _).2 ⟨rk s, by omega, rfl, hs, rfl⟩⟩

namespace Params

variable (E : Params Rep U) (w : ℕ → Bool)

theorem pre_act_noRecv (n q : ℕ) (r : Rep) (s : ℕ) : (pre (E.act w) n)[q]? ≠ some (.recv r s) := by
  rw [pre_getElem?]; split_ifs
  · simpa using E.act_ne_recv w
  · simp

/-- Where the elements of the construction are inserted (`i` selects `γ_w^i`). -/
def InsAt (i q : ℕ) (x : U) : Prop :=
  (∃ t ≤ E.d, (q = 3 * t ∧ x = E.Op t) ∨ (q = 3 * t + 1 ∧ x = E.Cl t)) ∨
    (q = 3 * E.d + 3 ∧ x = E.Star) ∨ (E.odd = true ∧ q = 5 * E.d + 7 ∧ x = E.Bee) ∨
    (q = E.Lα + 2 * i + 1 ∧ x = E.X)

theorem insAt_unique {i q q' : ℕ} {x : U} (h : E.InsAt i q x) (h' : E.InsAt i q' x) : q = q' := by
  unfold InsAt at h h'
  rcases h with ⟨t, ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases h' with ⟨t', ht', ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ | ⟨rfl, h⟩ | ⟨-, rfl, h⟩ | ⟨rfl, h⟩ <;>
  simp at h <;> omega

theorem uniqueIns_of_insAt {g : ℕ → Act Rep (LOp U)} {n i : ℕ}
    (hg : ∀ q < n, ∀ r x k, g q = .doOp r (.ins x k) → E.InsAt i q x) : UniqueIns (pre g n) := by
  intro p q r r' a k k' hp hq
  rw [pre_getElem?] at hp hq
  split_ifs at hp hq with h1 h2
  exact E.insAt_unique (hg p h1 r a k (Option.some.inj hp)) (hg q h2 r' a k' (Option.some.inj hq))

theorem insAt_of_act {i q : ℕ} {r : Rep} {x : U} {k : ℕ} (h : E.act w q = .doOp r (.ins x k)) :
    E.InsAt i q x := by
  obtain ⟨-, ⟨t, ht, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩ | ⟨rfl, rfl, -⟩ | ⟨ho, rfl, rfl, -⟩⟩ :=
    (E.act_ins_iff w).1 h
  · exact Or.inl ⟨t, ht, Or.inl ⟨rfl, rfl⟩⟩
  · exact Or.inl ⟨t, ht, Or.inr ⟨rfl, rfl⟩⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨ho, rfl, rfl⟩))

/-- The elements inserted at or before position `p` of `α_w`. -/
theorem insB_iff (p : ℕ) (x : U) :
    (∃ q ≤ p, ∃ k, E.act w q = .doOp E.r1 (.ins x k)) ↔
      (∃ t ≤ E.d, (3 * t ≤ p ∧ x = E.Op t) ∨ (3 * t + 1 ≤ p ∧ x = E.Cl t)) ∨
      (3 * E.d + 3 ≤ p ∧ x = E.Star) ∨ (E.odd = true ∧ 5 * E.d + 7 ≤ p ∧ x = E.Bee) := by
  constructor
  · rintro ⟨q, hqp, k, hq⟩
    obtain ⟨-, ⟨t, ht, ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩⟩ | ⟨rfl, rfl, -⟩ | ⟨ho, rfl, rfl, -⟩⟩ :=
      (E.act_ins_iff w).1 hq
    · exact Or.inl ⟨t, ht, Or.inl ⟨hqp, rfl⟩⟩
    · exact Or.inl ⟨t, ht, Or.inr ⟨hqp, rfl⟩⟩
    · exact Or.inr (Or.inl ⟨hqp, rfl⟩)
    · exact Or.inr (Or.inr ⟨ho, hqp, rfl⟩)
  · rintro (⟨t, ht, ⟨hp, rfl⟩ | ⟨hp, rfl⟩⟩ | ⟨hp, rfl⟩ | ⟨ho, hp, rfl⟩)
    · exact ⟨3 * t, hp, _, E.act_Op w ht⟩
    · exact ⟨3 * t + 1, hp, _, E.act_Cl w ht⟩
    · exact ⟨_, hp, _, E.act_Star w⟩
    · exact ⟨_, hp, _, E.act_Bee w ho⟩

/-- The elements deleted at or before position `p` of `α_w`. -/
theorem delB_iff (p : ℕ) (x : U) :
    (∃ q ≤ p, E.act w q = .doOp E.r1 (.del x)) ↔
      (∃ t ≤ E.d, (3 * E.d + 5 + 2 * t ≤ p ∧ x = E.Op t) ∨ (3 * E.d + 6 + 2 * t ≤ p ∧ x = E.Cl t)) ∨
      (E.odd = true ∧ 5 * E.d + 8 ≤ p ∧ x = E.Bee) := by
  constructor
  · rintro ⟨q, hqp, hq⟩
    obtain ⟨-, ⟨t, ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, rfl, rfl⟩⟩ := (E.act_del_iff w).1 hq
    · exact Or.inl ⟨t, ht, Or.inl ⟨hqp, rfl⟩⟩
    · exact Or.inl ⟨t, ht, Or.inr ⟨hqp, rfl⟩⟩
    · exact Or.inr ⟨ho, hqp, rfl⟩
  · rintro (⟨t, ht, ⟨hp, rfl⟩ | ⟨hp, rfl⟩⟩ | ⟨ho, hp, rfl⟩)
    · exact ⟨_, hp, E.act_delOp w ht⟩
    · exact ⟨_, hp, E.act_delCl w ht⟩
    · exact ⟨_, hp, E.act_delBee w ho⟩

theorem act_del_unique {q p : ℕ} {r r' : Rep} {x : U} (hq : E.act w q = .doOp r (.del x))
    (hp : E.act w p = .doOp r' (.del x)) : q = p := by
  obtain ⟨-, h⟩ := (E.act_del_iff w).1 hq
  obtain ⟨-, h'⟩ := (E.act_del_iff w).1 hp
  rcases h with ⟨t, ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨-, rfl, rfl⟩ <;>
  rcases h' with ⟨t', ht', ⟨rfl, h⟩ | ⟨rfl, h⟩⟩ | ⟨-, rfl, h⟩ <;>
  simp at h <;> omega

variable {w}

/-- **Encoding.** Every prefix of `α_w` is a well-formed admitted execution. -/
theorem alpha_ok (hP : PushBased P Weak (LBAdm P)) :
    ∀ n ≤ E.Lα, P.WF (pre (E.act w) n) ∧ LBAdm P (pre (E.act w) n) := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun p hp => by simp at hp, causalAtomic_of_noRecv (E.pre_act_noRecv w 0),
      E.uniqueIns_of_insAt (i := 0) (fun q _ r x k h => E.insAt_of_act w h), ?_⟩
    intro p r a hp; simp [pre] at hp
  | succ n ih =>
    intro hn
    obtain ⟨hwf, hadm⟩ := ih (by omega)
    have pend : ∀ m, m + 1 = n → P.Pending (pre (E.act w) n) m E.r1 →
        ((P.exec (pre (E.act w) n)).st E.r1).2.isSome := by
      rintro m rfl ⟨-, h⟩
      rwa [pre_take, min_eq_left le_rfl] at h
    have getα : ∀ q < n, (pre (E.act w) n)[q]? = some (E.act w q) :=
      fun q hq => pre_getElem?_of_lt _ hq
    have nohb : ∀ p x, E.act w p = .doOp E.r1 (.del x) →
        ¬ ∃ q r', HB (pre (E.act w) n) q p ∧ (pre (E.act w) n)[q]? = some (.doOp r' (.del x)) := by
      rintro p x hp ⟨q, r', hqp, hq⟩
      rw [pre_getElem?] at hq; split_ifs at hq with hqn
      have := E.act_del_unique w (Option.some.inj hq) hp
      subst this; exact HB.irrefl q hqp
    obtain ⟨lo, -, hc, -, -⟩ := hP.spec _ hwf hadm
    have memb := fun {q : ℕ} {op : LOp U} (hq : q < n) (hg : E.act w q = .doOp E.r1 op) (x : U) =>
      mem_rval_of_single (P := P) (n := n) (fun p _ => E.act_rep w p) (visHB_absWF _) hc hq hg x
    refine ⟨WF_pre_succ.2 ⟨hwf, ?_⟩, causalAtomic_of_noRecv (E.pre_act_noRecv w _),
      E.uniqueIns_of_insAt (i := 0) (fun q _ r x k h => E.insAt_of_act w h),
      DelOK_pre_succ hadm.2.2 ?_⟩
    · rcases hact : E.act w n with ⟨r, op⟩ | r | ⟨r, s⟩
      · trivial
      · obtain ⟨rfl, ⟨t, ht, rfl⟩ | rfl | hlast⟩ := (E.act_send_iff w (by omega)).1 hact
        · exact pend (3 * t + 1) rfl (hP.ins _ hwf hadm _ _ _ _ (by rw [getα _ (by omega), E.act_Cl w ht]))
        · exact pend (3 * E.d + 3) rfl (hP.ins _ hwf hadm _ _ _ _ (by rw [getα _ (by omega), E.act_Star w]))
        · cases ho : E.odd
          · have hn' : n = 3 * E.d + 6 + 2 * E.d + 1 := by rw [hlast, Lα_eq, ho]; simp; omega
            subst hn'
            exact pend _ rfl (hP.del _ hwf hadm _ _ _ (by rw [getα _ (by omega), E.act_delCl w le_rfl])
              (nohb _ _ (E.act_delCl w le_rfl)))
          · have hn' : n = 5 * E.d + 8 + 1 := by rw [hlast, Lα_eq, ho]; simp
            subst hn'
            exact pend _ rfl (hP.del _ hwf hadm _ _ _ (by rw [getα _ (by omega), E.act_delBee w ho])
              (nohb _ _ (E.act_delBee w ho)))
      · exact absurd hact (E.act_ne_recv w)
    · intro r a hact
      obtain ⟨rfl, ⟨t, ht, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ | ⟨ho, rfl, rfl⟩⟩ := (E.act_del_iff w).1 hact
      · -- deletion of `[_t`
        rcases Nat.eq_zero_or_pos t with rfl | htpos
        · refine ⟨3 * E.d + 3, by omega, _, _, hist_pre_eq (by omega) (E.act_Star w), ?_, ?_⟩
          · rw [memb (by omega) (E.act_Star w), E.insB_iff, E.delB_iff]
            refine ⟨Or.inl ⟨0, by omega, Or.inl ⟨by omega, rfl⟩⟩, ?_⟩
            rintro (⟨t', _, ⟨h, h'⟩ | ⟨h, h'⟩⟩ | ⟨_, h, h'⟩) <;> simp at h' <;> omega
          · intro q' h1 h2 op'
            obtain rfl : q' = 3 * E.d + 4 := by omega
            rw [E.act_send_star w]; simp
        · obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
          have hq : E.act w (3 * E.d + 6 + 2 * t') = .doOp E.r1 (.del (E.Cl t')) :=
            E.act_delCl w (by omega)
          refine ⟨3 * E.d + 6 + 2 * t', by omega, _, _, hist_pre_eq (by omega) hq, ?_, ?_⟩
          · rw [memb (by omega) hq, E.insB_iff, E.delB_iff]
            refine ⟨Or.inl ⟨t' + 1, ht, Or.inl ⟨by omega, rfl⟩⟩, ?_⟩
            rintro (⟨t'', _, ⟨h, h'⟩ | ⟨h, h'⟩⟩ | ⟨_, h, h'⟩) <;> simp at h' <;> omega
          · intro q' h1 h2; omega
      · -- deletion of `]_t`
        have hq := E.act_delOp w ht
        refine ⟨3 * E.d + 5 + 2 * t, by omega, _, _, hist_pre_eq (by omega) hq, ?_, ?_⟩
        · rw [memb (by omega) hq, E.insB_iff, E.delB_iff]
          refine ⟨Or.inl ⟨t, ht, Or.inr ⟨by omega, rfl⟩⟩, ?_⟩
          rintro (⟨t'', _, ⟨h, h'⟩ | ⟨h, h'⟩⟩ | ⟨_, h, h'⟩) <;> simp at h' <;> omega
        · intro q' h1 h2; omega
      · -- deletion of `b`
        have hq := E.act_Bee w ho
        refine ⟨5 * E.d + 7, by omega, _, _, hist_pre_eq (by omega) hq, ?_, ?_⟩
        · rw [memb (by omega) hq, E.insB_iff, E.delB_iff]
          refine ⟨Or.inr (Or.inr ⟨ho, le_rfl, rfl⟩), ?_⟩
          rintro (⟨t'', _, ⟨h, h'⟩ | ⟨h, h'⟩⟩ | ⟨_, h, h'⟩) <;> simp at h' <;> omega
        · intro q' h1 h2; omega

/-- **Encoding, responses.** During the insertion phase the responses of `R₁` are the intended
lists: after `ins [ⱼ` it is `A_j [ⱼ B_j`, after `ins ]ⱼ` it is `L_j`, after `ins ∗` it is `L_∗`. -/
theorem rval_insert_phase (hP : PushBased P Weak (LBAdm P)) :
    (∀ j ≤ E.d, rval P (E.act w) (3 * j) = (E.AB w j).1 ++ [E.Op j] ++ (E.AB w j).2 ∧
      rval P (E.act w) (3 * j + 1) = E.L w j) ∧
    rval P (E.act w) (3 * E.d + 3) = E.Lstar w := by
  obtain ⟨hwf, hadm⟩ := E.alpha_ok hP (3 * E.d + 4) (by rw [Lα_eq]; omega)
  obtain ⟨lo, -, hc, hirr, htr⟩ := hP.spec _ hwf hadm
  have hh := fun {p : ℕ} {op : LOp U} (hp : p < 3 * E.d + 4) (hg : E.act w p = .doOp E.r1 op) =>
    hist_pre_eq (P := P) (n := 3 * E.d + 4) hp hg
  have memb : ∀ {p : ℕ} {op : LOp U}, p ≤ 3 * E.d + 3 → E.act w p = .doOp E.r1 op → ∀ x,
      x ∈ rval P (E.act w) p ↔ (∃ t ≤ E.d, (3 * t ≤ p ∧ x = E.Op t) ∨ (3 * t + 1 ≤ p ∧ x = E.Cl t)) ∨
        (3 * E.d + 3 ≤ p ∧ x = E.Star) := by
    intro p op hp hg x
    rw [mem_rval_of_single (P := P) (n := 3 * E.d + 4) (fun p _ => E.act_rep w p)
      (visHB_absWF _) hc (by omega) hg x, E.insB_iff, E.delB_iff]
    constructor
    · rintro ⟨h | h | ⟨-, h, -⟩, -⟩
      · exact Or.inl h
      · exact Or.inr h
      · omega
    · intro h
      refine ⟨h.elim Or.inl (fun h => Or.inr (Or.inl h)), ?_⟩
      rintro (⟨t, _, ⟨h, -⟩ | ⟨h, -⟩⟩ | ⟨-, h, -⟩) <;> omega
  have step : ∀ {p : ℕ} {op : LOp U} {l : List U} {a : U} {k : ℕ}, p ≤ 3 * E.d + 3 →
      E.act w p = .doOp E.r1 op → op = .ins a k → l.Pairwise lo →
      (∀ x, x ∈ rval P (E.act w) p ↔ x ∈ l ∨ x = a) → a ∉ l →
      rval P (E.act w) p = l.insertIdx (min k l.length) a := by
    intro p op l a k hp hg hop hl hmem ha
    have h := hc p _ _ _ (hh (by omega) hg)
    exact eq_insertIdx_of_weak hl h.2.1 hirr (htr p _ _ _ (hh (by omega) hg)).1 hmem ha
      (h.2.2 a k hop)
  have hL : ∀ j ≤ E.d, rval P (E.act w) (3 * j) = (E.AB w j).1 ++ [E.Op j] ++ (E.AB w j).2 ∧
      rval P (E.act w) (3 * j + 1) = E.L w j := by
    intro j
    induction j with
    | zero =>
      intro _
      have h0 : rval P (E.act w) 0 = [E.Op 0] := by
        have := step (l := []) (by omega) (E.act_Op w (t := 0) (by omega)) rfl List.Pairwise.nil
          (by
            intro x; rw [memb (by omega) (E.act_Op w (t := 0) (by omega))]
            constructor
            · rintro (⟨t, _, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ | ⟨h, -⟩)
              · obtain rfl : t = 0 := by omega
                simp
              · omega
              · omega
            · rintro (h | rfl)
              · simp at h
              · exact Or.inl ⟨0, by omega, Or.inl ⟨le_rfl, rfl⟩⟩)
          (by simp)
        simpa using this
      refine ⟨by simpa [AB] using h0, ?_⟩
      have := step (l := [E.Op 0]) (by omega) (E.act_Cl w (t := 0) (by omega)) rfl
        (by rw [← h0]; exact (hc 0 _ _ _ (hh (by omega) (E.act_Op w (t := 0) (by omega)))).2.1)
        (by
          intro x; rw [memb (by omega) (E.act_Cl w (t := 0) (by omega))]
          constructor
          · rintro (⟨t, _, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ | ⟨h, -⟩)
            · obtain rfl : t = 0 := by omega
              simp
            · obtain rfl : t = 0 := by omega
              simp
            · omega
          · rintro (h | rfl)
            · simp at h; subst h; exact Or.inl ⟨0, by omega, Or.inl ⟨by omega, rfl⟩⟩
            · exact Or.inl ⟨0, by omega, Or.inr ⟨le_rfl, rfl⟩⟩)
        (by simp)
      rw [this]; simp [L, AB, lenA]
    | succ j ih =>
      intro hj
      obtain ⟨-, ih2⟩ := ih (by omega)
      have hprev : (E.AB w (j + 1)).1 ++ (E.AB w (j + 1)).2 = rval P (E.act w) (3 * j + 1) := by
        rw [AB_succ_append, ih2]
      have hOp := E.act_Op w hj
      have hCl := E.act_Cl w hj
      have h1 := step (l := (E.AB w (j + 1)).1 ++ (E.AB w (j + 1)).2) (by omega) hOp rfl
        (by rw [hprev]; exact (hc _ _ _ _ (hh (by omega) (E.act_Cl w (t := j) (by omega)))).2.1)
        (by
          intro x; rw [memb (by omega) hOp, mem_AB]
          constructor
          · rintro (⟨t, _, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ | ⟨h, -⟩)
            · rcases Nat.lt_or_ge t (j + 1) with h' | h'
              · exact Or.inl ⟨t, h', Or.inl rfl⟩
              · obtain rfl : t = j + 1 := by omega
                exact Or.inr rfl
            · exact Or.inl ⟨t, by omega, Or.inr rfl⟩
            · omega
          · rintro (⟨t, ht, rfl | rfl⟩ | rfl)
            · exact Or.inl ⟨t, by omega, Or.inl ⟨by omega, rfl⟩⟩
            · exact Or.inl ⟨t, by omega, Or.inr ⟨by omega, rfl⟩⟩
            · exact Or.inl ⟨j + 1, hj, Or.inl ⟨le_rfl, rfl⟩⟩)
        (by rw [mem_AB]; rintro ⟨t, ht, h | h⟩ <;> simp at h <;> omega)
      have h1' : rval P (E.act w) (3 * (j + 1)) =
          (E.AB w (j + 1)).1 ++ [E.Op (j + 1)] ++ (E.AB w (j + 1)).2 := by
        rw [h1, min_eq_left (by simp [lenA]), lenA, ← Nat.add_zero (List.length _),
          insertIdx_append_length_add]
        simp
      refine ⟨h1', ?_⟩
      have h2 := step (l := (E.AB w (j + 1)).1 ++ [E.Op (j + 1)] ++ (E.AB w (j + 1)).2) (by omega)
        hCl rfl (by rw [← h1']; exact (hc _ _ _ _ (hh (by omega) hOp)).2.1)
        (by
          intro x; rw [memb (by omega) hCl]
          simp only [List.mem_append, List.mem_singleton]
          have hAB := (mem_AB (E := E) (w := w) (j := j + 1) (x := x))
          simp only [List.mem_append] at hAB
          constructor
          · rintro (⟨t, _, ⟨h, rfl⟩ | ⟨h, rfl⟩⟩ | ⟨h, -⟩)
            · rcases Nat.lt_or_ge t (j + 1) with h' | h'
              · rcases hAB.2 ⟨t, h', Or.inl rfl⟩ with h | h
                · exact Or.inl (Or.inl (Or.inl h))
                · exact Or.inl (Or.inr h)
              · obtain rfl : t = j + 1 := by omega
                exact Or.inl (Or.inl (Or.inr rfl))
            · rcases Nat.lt_or_ge t (j + 1) with h' | h'
              · rcases hAB.2 ⟨t, h', Or.inr rfl⟩ with h | h
                · exact Or.inl (Or.inl (Or.inl h))
                · exact Or.inl (Or.inr h)
              · obtain rfl : t = j + 1 := by omega
                exact Or.inr rfl
            · omega
          · rintro (((h | rfl) | h) | rfl)
            · obtain ⟨t, ht, rfl | rfl⟩ := hAB.1 (Or.inl h)
              · exact Or.inl ⟨t, by omega, Or.inl ⟨by omega, rfl⟩⟩
              · exact Or.inl ⟨t, by omega, Or.inr ⟨by omega, rfl⟩⟩
            · exact Or.inl ⟨j + 1, hj, Or.inl ⟨by omega, rfl⟩⟩
            · obtain ⟨t, ht, rfl | rfl⟩ := hAB.1 (Or.inr h)
              · exact Or.inl ⟨t, by omega, Or.inl ⟨by omega, rfl⟩⟩
              · exact Or.inl ⟨t, by omega, Or.inr ⟨by omega, rfl⟩⟩
            · exact Or.inl ⟨j + 1, hj, Or.inr ⟨le_rfl, rfl⟩⟩)
        (by
          have := (mem_AB (E := E) (w := w) (j := j + 1) (x := E.Cl (j + 1)))
          simp only [List.mem_append, List.mem_singleton] at this ⊢
          rintro ((h | h) | h)
          · obtain ⟨t, ht, h | h⟩ := this.1 (Or.inl h) <;> simp at h; omega
          · simp at h
          · obtain ⟨t, ht, h | h⟩ := this.1 (Or.inr h) <;> simp at h; omega)
      rw [h2, min_eq_left (by simp [lenA]), ← insertIdx_Cl]
  refine ⟨hL, ?_⟩
  have hS := E.act_Star w
  have h3 := step (l := E.L w E.d) le_rfl hS rfl
    (by rw [← (hL E.d le_rfl).2]; exact (hc _ _ _ _ (hh (by omega) (E.act_Cl w le_rfl))).2.1)
    (by
      intro x; rw [memb le_rfl hS, mem_L]
      constructor
      · rintro (⟨t, ht, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ | ⟨-, rfl⟩)
        · exact Or.inl ⟨t, ht, Or.inl rfl⟩
        · exact Or.inl ⟨t, ht, Or.inr rfl⟩
        · exact Or.inr rfl
      · rintro (⟨t, ht, rfl | rfl⟩ | rfl)
        · exact Or.inl ⟨t, ht, Or.inl ⟨by omega, rfl⟩⟩
        · exact Or.inl ⟨t, ht, Or.inr ⟨by omega, rfl⟩⟩
        · exact Or.inr ⟨le_rfl, rfl⟩)
    (by rw [mem_L]; rintro ⟨t, -, h | h⟩ <;> simp at h)
  rw [h3, min_eq_left (by simp [L, lenA]), insertIdx_Star]

end Params

end Podc.CollaborativeListSpec
