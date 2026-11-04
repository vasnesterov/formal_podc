import Papers.PODC2014.WritableObjects.Lemma48Local

/-!
# Lemma 4.8, part 4: the invariant

The proof of Lemma 4.8 is an invariant proof over the reachable configurations of the model of
Figure 4.5, with the ghost state described in `Algorithm.lean`. The invariant `Inv` collects:

* local invariants of the queues and of the current `Write` (Claims 4.9–4.15, 4.21);
* `ptrProt`: an index in `Ptr` is protected (Claims 4.22, 4.23);
* `swf`/`swdone`: the transcript-level form of "no `SWrite` on `A[i]` after `i` was put into use";
* `hint`, `hint'`: an index stored in `H_p[q]` or `H'_p[q]` is protected (Claims 4.16, 4.17);
* `reset`: the reset mechanism of lines 44–45 (used in Claim 4.25(b));
* `pair`: the two hint entries were written by the same `Write` (Claims 4.19, 4.24);
* `exec`: the state of each pending `Exec` (Claims 4.18, 4.20, 4.24, 4.25 and the two cases of
  the proof of Lemma 4.8);
* transcript-level invariants that give the conclusion: `CondC`, the template automaton, the
  "not in use" condition and the pairing of `Oper` invocations with their responses.
-/

namespace Podc.WritableObjects.WF

open Cslib.SharedMemory

variable {n : ℕ} {T : ObjSpec}

/-- The transcript-level form of condition (C2): every `A[i].SWrite` invoked in `tr` returned
before point `ts`. -/
def SWF (tr : List (Ev (Fin n) (Idx n) T)) (i : Idx n) (ts : ℕ) : Prop :=
  ∀ a p v, tr[a]? = some (.swinv p i v) → ∃ b r, a < b ∧ b < ts ∧ tr[b]? = some (.aret p i r)

/-- Phases of `Exec` between line 35 and line 44 (line 44 not yet executed). -/
def pre44 : PC n T → Bool
  | .e36 .. | .e37 .. | .e39 .. | .e40 .. | .e43 .. | .eOp .. | .e44 .. => true
  | _ => false

/-- The number of `Exec` calls of `q` that have executed line 44 (= the last epoch that did). -/
def done44 (l : Loc n T) : ℕ := if pre44 l.pc then l.m - 1 else l.m

/-- The control state of the template (Figure 4.4) corresponding to a program counter. -/
def absPC : PC n T → PSt (Idx n) T
  | .idle => .idle
  | .w27 v | .w29 v _ | .w31 v _ | .w13 v _ => .wBeg v
  | .wSW v f => .wSW v f
  | .w14 v f | .w15 v f .. | .w16 v f .. | .w18 v f .. | .w19 v f | .w20 v f .. | .w23 v f =>
    .wPtr v f
  | .w21 v .. | .wRet v => .wEnd v
  | .e34 o | .e35 o _ | .e36 o _ | .e37 o .. | .e39 o .. | .e40 o .. | .e43 o .. => .eBeg o
  | .eOp _ i .. => .eOp i
  | .e44 _ r | .e45 _ r | .eRet r => .eEnd r

/-- Local invariant: `H_p[q].m18 ≤ m19` at lines 20–21. -/
def M18c : PC n T → ℕ → Prop
  | .w20 _ _ _ m19 _, m18 => m18 ≤ m19
  | .w21 _ _ _ m19 _ _, m18 => m18 ≤ m19
  | _, _ => True

variable [NeZero n]

/-- The epoch read in line 14 (at lines 15–18). -/
def m14Of : PC n T → Option ℕ
  | .w15 _ _ _ m14 | .w16 _ _ _ m14 _ | .w18 _ _ _ m14 _ _ => some m14
  | _ => none

/-- Epochs read in line 14 dominate the epochs recorded in `H'_p[ctr]` (time is monotone). -/
def Mono (c : Cfg n T) (p : Fin n) : Prop :=
  ∀ m14, m14Of (c.loc p).pc = some m14 →
    ∀ b, c.hH' p (cq (c.loc p).ctr) = some b → b.m19 ≤ m14

/-- `(s, m14)` at lines 15–18. -/
def smOf : PC n T → Option (ℤ × ℕ)
  | .w15 _ _ s m14 | .w16 _ _ s m14 _ | .w18 _ _ s m14 _ _ => some (s, m14)
  | _ => none

/-- `olds` at lines 16–18. -/
def oldsOf : PC n T → Option (Option ℤ)
  | .w16 _ _ _ _ olds | .w18 _ _ _ _ olds _ => some olds
  | _ => none

/-- `olds'` at line 18. -/
def olds'Of : PC n T → Option (Option ℤ)
  | .w18 _ _ _ _ _ olds' => some olds'
  | _ => none

/-- `(s', m19, τ19)` at lines 20–21. -/
def s19Of : PC n T → Option (ℤ × ℕ × ℕ)
  | .w20 _ _ s' m19 τ19 | .w21 _ _ s' m19 τ19 _ => some (s', m19, τ19)
  | _ => none

/-- Invariants of the local values read in lines 14–19. -/
def LocRd (c : Cfg n T) (p : Fin n) : Prop :=
  (∀ s m14, smOf (c.loc p).pc = some (s, m14) →
    s = Sval n m14 ∧ m14 ≤ (c.loc (cq (c.loc p).ctr)).m) ∧
  (∀ olds, oldsOf (c.loc p).pc = some olds →
    ∀ h, c.hH p (cq (c.loc p).ctr) = some h → olds = some h.s) ∧
  (∀ olds', olds'Of (c.loc p).pc = some olds' →
    ∀ b, c.hH' p (cq (c.loc p).ctr) = some b → olds' = some b.s) ∧
  (∀ v f s m14 olds olds', (c.loc p).pc = .w18 v f s m14 olds olds' →
    (some s ≠ olds ∨ some s ≠ olds')) ∧
  (∀ s' m19 τ19, s19Of (c.loc p).pc = some (s', m19, τ19) →
    s' = Sval n m19 ∧ m19 ≤ (c.loc (cq (c.loc p).ctr)).m ∧
    (m19 = (c.loc (cq (c.loc p).ctr)).m → (c.loc (cq (c.loc p).ctr)).τ35 ≤ τ19) ∧
    τ19 ≤ c.tr.length)

/-! ## The state of an `Exec` -/

/-- `q`'s latest event is its `Exec` invocation at position `eq`. -/
def EqOK (c : Cfg n T) (q : Fin n) : Prop :=
  (c.loc q).eq < c.tr.length ∧ (∃ o, c.tr[(c.loc q).eq]? = some (.einv q o)) ∧
    ∀ k (hk : k < c.tr.length), (c.loc q).eq < k → (c.tr[k]).proc ≠ q

/-- After line 35: `x = S_q`, and the write to `S_q` happened after the invocation. -/
def WinOK (c : Cfg n T) (q : Fin n) (x : ℕ) : Prop :=
  (x : ℤ) = c.S q ∧ 1 ≤ (c.loc q).m ∧ (c.loc q).eq < (c.loc q).τ35 ∧
    (c.loc q).τ35 ≤ c.tr.length

/-- The writer `p` will not overwrite a valid hint for `q` (the `p`-side of Claim 4.18). -/
def PSide (c : Cfg n T) (p q : Fin n) (x : ℤ) : Prop :=
  match (c.loc p).pc with
  | .w15 _ _ _ m14 => cq (c.loc p).ctr = q → m14 = (c.loc q).m
  | .w16 _ _ _ m14 olds => cq (c.loc p).ctr = q → m14 = (c.loc q).m ∧ olds = some x
  | .w18 .. | .w19 .. | .w20 .. | .w21 .. => cq (c.loc p).ctr ≠ q
  | _ => True

/-- A *stable hint* `(j, x)` from `p` for `q` (Claims 4.18, 4.20): both hint entries hold
`(j, x)`, written by the same `Write`, and `p` will not change them while `S_q = x`. -/
def Bcore (c : Cfg n T) (p q : Fin n) (x : ℤ) (j : Idx n) : Prop :=
  ∃ h b, c.hH p q = some h ∧ c.hH' p q = some b ∧ h.f = j ∧ b.f = j ∧ h.w = b.w ∧ h.s = x ∧
    b.s = x ∧ PSide c p q x

/-- Direct protection of `i` by the announcement `Annc[q] = i` (case 1 of Lemma 4.8). -/
def Dcore (c : Cfg n T) (q : Fin n) (i : Idx n) : Prop :=
  c.annc q = some i ∧ (c.loc i.1).SlotProt i 1 q

/-- `i` has been put into use by its owner before point `ts` and not chosen again since. -/
def PPok (c : Cfg n T) (i : Idx n) (ts : ℕ) : Prop :=
  ∃ π, (c.loc i.1).pp i = some π ∧ π + 1 ≤ ts

/-- Progress of the `Write` of `p` with `ctr ≡ q` started after `q` read `Ptr` (Claim 4.20). -/
def Cprog (c : Cfg n T) (p q : Fin n) (x : ℤ) (g : ℕ) : Prop :=
  g < (c.loc p).ctr → cq (c.loc p).ctr = q →
  match (c.loc p).pc with
  | .w15 _ _ _ m14 => m14 = (c.loc q).m
  | .w16 _ _ _ m14 olds => m14 = (c.loc q).m ∧ olds = (c.hH p q).map HE.s
  | .w18 _ _ _ m14 _ _ => m14 = (c.loc q).m
  | .w19 _ f => ∃ h, c.hH p q = some h ∧ h.f = f ∧ h.s = x ∧ h.w = (c.loc p).ctr
  | .w20 _ f _ m19 _ =>
    (∃ h, c.hH p q = some h ∧ h.f = f ∧ h.s = x ∧ h.w = (c.loc p).ctr) ∧ m19 = (c.loc q).m
  | .w21 _ f _ m19 _ _ =>
    (∃ h, c.hH p q = some h ∧ h.f = f ∧ h.s = x ∧ h.w = (c.loc p).ctr) ∧ m19 = (c.loc q).m
  | .w23 _ _ => ∃ j, Bcore c p q x j
  | _ => True

/-- Between lines 36 and 37 of `Exec` by `q` (index `i` read from `Ptr`, `g = ctr_p` then):
the owner has not completed a `Write` with `ctr ≡ q` since (Claim 4.20 / (4.32)). -/
def A1 (c : Cfg n T) (q : Fin n) (x : ℤ) (i : Idx n) (g ts : ℕ) : Prop :=
  (c.loc i.1).Prot i (4 * (g + 2 * n + 1)) ∧ PPok c i ts ∧ g ≤ (c.loc i.1).ctr ∧
    (∀ w, g < w → w < (c.loc i.1).ctr → cq w ≠ q) ∧ Cprog c i.1 q x g

/-- For the current `Write` of `p` with `ctr ≡ q` that started after write `w`: its line 14
read happened in the current epoch of `q`. -/
def M14c (c : Cfg n T) (p q : Fin n) (w : ℕ) : Prop :=
  ∀ m14, m14Of (c.loc p).pc = some m14 → cq (c.loc p).ctr = q → w < (c.loc p).ctr →
    m14 = (c.loc q).m

/-- After line 39 of `Exec` by `q` read the hint `h = (j, x)` from `H_p[q]` (Claim 4.24): if `q`
reads `(j, x)` from `H'_p[q]`, then `H_p[q]` holds `(j, x)` from the same `Write`. -/
def I39 (c : Cfg n T) (p q : Fin n) (x : ℤ) (h : HE n) : Prop :=
  ∃ a, c.hH p q = some a ∧ h.w ≤ a.w ∧
    (a.w = h.w → a.f = h.f ∧ a.s = x ∧ ∀ b, c.hH' p q = some b → b.f = h.f → b.w = h.w) ∧
    (h.w < a.w → (a.f = h.f → a.s = x) ∧
      (∀ b, c.hH' p q = some b → b.f = h.f → b.s = x → b.w = a.w ∧ a.f = h.f ∧ a.s = x) ∧
      M14c c p q a.w)

/-- After line 40: `q` committed to the exec-index `i` with point `ts` (Lemma 4.8). -/
def Commit (c : Cfg n T) (q : Fin n) (x : ℤ) (i : Idx n) (ts : ℕ) : Prop :=
  (c.loc q).eq < ts ∧ ts ≤ c.tr.length ∧ ptrAt c.tr ts = some i ∧ PPok c i ts ∧
    (Dcore c q i ∨ Bcore c i.1 q x i)

/-- The invariant of a process executing `Exec`. -/
def ExecInv (c : Cfg n T) (q : Fin n) : Prop :=
  match (c.loc q).pc with
  | .e34 _ => EqOK c q
  | .e35 _ x => EqOK c q ∧ (x : ℤ) = (c.S q + 1) % (2 * n : ℤ)
  | .e36 _ x => EqOK c q ∧ WinOK c q x
  | .e37 _ x i g ts => EqOK c q ∧ WinOK c q x ∧ (c.loc q).eq < ts ∧ ts ≤ c.tr.length ∧
      ∀ i', i = some i' → ptrAt c.tr ts = some i' ∧
        (A1 c q x i' g ts ∨ ∃ j, Bcore c i'.1 q x j)
  | .e39 _ x i _ ts => EqOK c q ∧ WinOK c q x ∧ (c.loc q).eq < ts ∧ ts ≤ c.tr.length ∧
      ∀ i', i = some i' → ptrAt c.tr ts = some i' ∧ c.annc q = some i' ∧
        ((Dcore c q i' ∧ PPok c i' ts) ∨ ∃ j, Bcore c i'.1 q x j)
  | .e40 _ x i _ ts hv => EqOK c q ∧ WinOK c q x ∧ (c.loc q).eq < ts ∧ ts ≤ c.tr.length ∧
      ptrAt c.tr ts = some i ∧ c.annc q = some i ∧
      ((Dcore c q i ∧ PPok c i ts) ∨ ∃ h, hv = some h ∧ c.hH i.1 q = some h ∧ Bcore c i.1 q x h.f) ∧
      ∀ h, hv = some h → h.s = x → I39 c i.1 q x h
  | .e43 _ x i ts => EqOK c q ∧ WinOK c q x ∧ Commit c q x i ts
  | .eOp x i ts t => WinOK c q x ∧ Commit c q x i ts ∧ ts ≤ t
  | .e44 x _ | .e45 x _ => WinOK c q x
  | _ => True

/-- The template automaton up to the current point, ending in the abstract control states. -/
def TemplateUpTo (W : Writable T) (c : Cfg n T) : Prop :=
  ∃ σ : Fin n → ℕ → PSt (Idx n) T, ∀ p, σ p 0 = .idle ∧
    (∀ t (ht : t < c.tr.length),
      (c.tr[t].proc = p → PStep W owner p (σ p t) c.tr[t] (σ p (t + 1))) ∧
      (c.tr[t].proc ≠ p → σ p (t + 1) = σ p t)) ∧
    σ p c.tr.length = absPC (c.loc p).pc

/-- The invariant. -/
structure Inv (W : Writable T) (c : Cfg n T) : Prop where
  qok : ∀ p, QOK p (c.loc p).qs
  chosen : ∀ p f, curF (c.loc p).pc = some f →
    f.1 = p ∧ (c.loc p).Prot f (4 * ((c.loc p).ctr + 2 * n + 2)) ∧ (c.loc p).lc f = (c.loc p).ctr
  prePtr : ∀ p f, curF (c.loc p).pc = some f → isPrePtr (c.loc p).pc → (c.loc p).pp f = none
  w21 : ∀ p v f s' m19 τ19 π, (c.loc p).pc = .w21 v f s' m19 τ19 π →
    (c.loc p).pp f = some π ∧ τ19 ≤ π
  ptrEq : c.ptr = ptrAt c.tr c.tr.length
  sEq : ∀ q, c.S q = Sval n (c.loc q).m
  tau35 : ∀ q, (c.loc q).τ35 ≤ c.tr.length
  ptrProt : ∀ i, c.ptr = some i → (c.loc i.1).Prot i (4 * ((c.loc i.1).ctr + 2 * n + 1)) ∧
    (c.loc i.1).pp i ≠ none ∧
    ∀ v f s' m19 τ19 π, (c.loc i.1).pc = .w21 v f s' m19 τ19 π → f = i
  swf : ∀ p i π, (c.loc p).pp i = some π →
    i.1 = p ∧ c.tr[π]? = some (.ptr p i) ∧ SWF c.tr i (π + 1)
  swdone : ∀ a p i v, c.tr[a]? = some (.swinv p i v) →
    (∃ b r, a < b ∧ b < c.tr.length ∧ c.tr[b]? = some (.aret p i r)) ∨
      ∃ v', (c.loc p).pc = .wSW v' i
  hint : ∀ p q h, c.hH p q = some h → h.f.1 = p ∧ (c.loc p).SlotProt h.f 2 q ∧
    (c.loc p).lc h.f = h.w ∧ h.s = Sval n h.m14 ∧ h.m14 ≤ h.m18 ∧ h.m18 ≤ (c.loc q).m ∧
    (h.w < (c.loc p).ctr ∨
      (h.w = (c.loc p).ctr ∧ isW1921 (c.loc p).pc ∧ cq (c.loc p).ctr = q))
  hint' : ∀ p q b, c.hH' p q = some b → b.f.1 = p ∧ (c.loc p).SlotProt b.f 3 q ∧
    (c.loc p).lc b.f = b.w ∧ b.w < (c.loc p).ctr ∧ (c.loc p).pp b.f = some b.π ∧
    b.s = Sval n b.m19 ∧ b.m19 ≤ (c.loc q).m ∧ (b.m19 = (c.loc q).m → (c.loc q).τ35 ≤ b.π)
  reset : ∀ p q h, c.hH p q = some h → ∀ e, h.m18 < e → e ≤ done44 (c.loc q) →
    (e - 1) % n ≠ p.val
  pairIn : ∀ p q, isW1921 (c.loc p).pc → cq (c.loc p).ctr = q → ∀ h, c.hH p q = some h →
    h.w = (c.loc p).ctr ∧ curF (c.loc p).pc = some h.f ∧ M18c (c.loc p).pc h.m18
  pairOut : ∀ p q, ¬ (isW1921 (c.loc p).pc ∧ cq (c.loc p).ctr = q) → ∀ h b,
    c.hH p q = some h → c.hH' p q = some b → h.w = b.w ∧ h.f = b.f ∧ h.m18 ≤ b.m19
  mono : ∀ p, Mono c p
  locRd : ∀ p, LocRd c p
  exec : ∀ q, ExecInv c q
  condC : CondC c.tr
  tmpl : TemplateUpTo W c
  notInUse : ∀ t p f v, c.tr[t]? = some (.swinv p f v) → ptrAt c.tr t ≠ some f
  opRet : ∀ t q i o, c.tr[t]? = some (.opinv q i o) →
    (∃ c' r, t < c' ∧ c.tr[c']? = some (.aret q i r)) ∨ ∃ x ts, (c.loc q).pc = .eOp x i ts t

end Podc.WritableObjects.WF
