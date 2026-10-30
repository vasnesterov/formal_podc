import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Set.Insert

/-!
# Algorithm 2 (Reliable Broadcast) of "The Impact of RDMA on Agreement" — the model

Aguilera, Ben-David, Guerraoui, Marathe, Zablotchi, PODC 2019 (arXiv:1905.12143v2), §4.1.1 and
Appendix A. This file fixes the model; `Safety.lean` and `Liveness.lean` prove the four properties
of Definition 1 (Lemma 4.1).

## Model

* **Processes** `P` (a `Fintype`, `n = |P|`), Byzantine set `F : Finset P`; the thresholds of the
  algorithm ("majority") are `f + 1`. The resilience hypotheses `|F| ≤ f`, `2f + 1 ≤ n` are
  assumptions of the theorems, not of the model.
* **Asynchronous shared memory** of SWMR registers `Value[p,k,q]`, `L1Proof[p,k,q]`,
  `L2Proof[p,k,q]` (`Reg`), all holding a `Val` (`⊥`, a signed copy, an L1 proof or an L2 proof;
  a value of the wrong shape is ignored by every reader, exactly like an ill-formed bit string).
* **Regular registers.** A read or write by a correct process has an invocation and a response.
  A pending read of `r` keeps a *candidate set* (`St.cand`): at invocation it is the current value
  of `r` together with the values of all pending writes to `r`; every write to `r` invoked while
  the read is pending is added; at the response the adversary returns *any* candidate. This is
  exactly Lamport's regular register ("the last value written before the read started, or the
  value of a write overlapping the read"); it also covers two overlapping writes of the same owner
  to the same register, which happens in Algorithm 2 (see `differencies`). A write updates the
  current value at its response.
* **Granularity.** Each step of a correct thread completes its pending memory operation, performs
  local computation, and invokes the next operation of that thread. (Invoking the next operation
  as early as possible only enlarges candidate sets, so it is no restriction on the adversary.)
* **Correct processes** run Algorithm 2: one *broadcast thread* (`broadcast(k,m)` with
  consecutive keys `k = 1, 2, …`, the next one only after the previous returned) and, for every
  sender `q`, one *delivery thread* `(p,q)` looping `try_deliver(q)`. The loops `for i ∈ Π` read
  the slots one by one in an arbitrary (adversarial) order.
* **Byzantine processes** (`p ∈ F`) write anything, at any time, any number of times, but only to
  their own registers (atomically). Their written values must respect unforgeability.
* **Signatures** are unforgeable and transferable, modelled abstractly: a term is a structured
  value whose signatures are listed by `Val.sigs`; the ghost set `St.signed` contains the
  signatures correct processes actually produced. A Byzantine write must not contain a signature
  of a correct process outside `St.signed` (`SigOK`); Byzantine processes may sign anything.
  A process's signature on its own broadcast `(k,m)` also serves as its endorsement (counter-
  signature) of that copy, so that `Value[p,k,p]` holds a valid echo of `p` after line 12 as well
  as after line 40.
* **Fairness** (for liveness only, `Exec.Fair`): every delivery thread of a correct process takes
  infinitely many steps and every pending broadcast write of a correct process completes.

## Charitable reading of the pseudocode (see `notes.md` / `differencies.md`)

* `try_deliver(q)` works on key `k = last[q] + 1` (the paper uses `k = last[q]` with
  `last[q] = 0` initially and first key `1`, so nothing would ever be delivered);
* `state` is per sender; line 30 delivers the message of the proof found at line 16;
* line 38 accepts a value carrying `q`'s signature on `(k, m)`; line 40 writes `p`'s
  endorsement of that signed pair; line 47 accepts from slot `i` an endorsement by `i` of a pair
  signed by `q` with key `k`;
* "majority" means `f + 1`; an L1 proof is valid for `(q,k,m)` if it has `≥ f+1` endorsements of
  `q`'s signed `(k,m)` (distinct, hence by distinct endorsers), an L2 proof if it has valid L1
  proofs for one `(q,k,m)` by `≥ f+1` distinct authors; at line 62 the process signs any such
  subset of the L1 proofs it collected.
-/

namespace Podc.RDMAAgreement.RB

/-! ### Terms -/

/-- `q`'s signature on the pair `(k, m)`: the signed message broadcast at line 12. -/
structure Base (P M : Type) where
  sender : P
  key : ℕ
  msg : M
deriving DecidableEq

/-- An endorsement (signed copy) by `signer` of the signed pair `base` (lines 12 and 40). -/
structure Copy (P M : Type) where
  signer : P
  base : Base P M
deriving DecidableEq

/-- An L1 proof: a set of copies, signed by `author` (line 51). -/
structure L1 (P M : Type) where
  author : P
  copies : Finset (Copy P M)
deriving DecidableEq

/-- An L2 proof: a set of L1 proofs, signed by `author` (line 63). -/
structure L2 (P M : Type) where
  author : P
  proofs : Finset (L1 P M)
deriving DecidableEq

/-- Register contents. -/
inductive Val (P M : Type)
  | bot
  | cp (c : Copy P M)
  | p1 (π : L1 P M)
  | p2 (ρ : L2 P M)

/-- What a signature signs. -/
inductive Sig (P M : Type)
  | base (b : Base P M)
  | endorse (b : Base P M)
  | l1 (π : L1 P M)
  | l2 (ρ : L2 P M)

/-- Signatures contained in a copy. -/
def Copy.sigs {P M : Type} (c : Copy P M) : Set (P × Sig P M) :=
  {(c.base.sender, .base c.base), (c.signer, .endorse c.base)}

/-- Signatures contained in an L1 proof. -/
def L1.sigs {P M : Type} (π : L1 P M) : Set (P × Sig P M) :=
  {x | x = (π.author, .l1 π) ∨ ∃ c ∈ π.copies, x ∈ c.sigs}

/-- Signatures contained in an L2 proof. -/
def L2.sigs {P M : Type} (ρ : L2 P M) : Set (P × Sig P M) :=
  {x | x = (ρ.author, .l2 ρ) ∨ ∃ π ∈ ρ.proofs, x ∈ π.sigs}

/-- Signatures contained in a register value. -/
def Val.sigs {P M : Type} : Val P M → Set (P × Sig P M)
  | .bot => ∅
  | .cp c => c.sigs
  | .p1 π => π.sigs
  | .p2 ρ => ρ.sigs

/-- Unforgeability: every signature of a correct process in `v` was produced by it. -/
def SigOK {P M : Type} (F : Finset P) (signed : Set (P × Sig P M)) (v : Val P M) : Prop :=
  ∀ x ∈ v.sigs, x.1 ∉ F → x ∈ signed

/-- A valid L1 proof for `(q, k, m)` ("majority" = `f + 1`). Copies with the same base are
distinct iff their endorsers are, so the endorsers are distinct. -/
def L1Valid {P M : Type} (f : ℕ) (q : P) (k : ℕ) (m : M) (π : L1 P M) : Prop :=
  f + 1 ≤ π.copies.card ∧ ∀ c ∈ π.copies, c.base = ⟨q, k, m⟩

/-- A valid L2 proof for `(q, k, m)`: valid L1 proofs for `(q,k,m)` by `≥ f+1` distinct authors. -/
def L2Valid {P M : Type} [DecidableEq P] (f : ℕ) (q : P) (k : ℕ) (m : M) (ρ : L2 P M) : Prop :=
  f + 1 ≤ (ρ.proofs.image L1.author).card ∧ ∀ π ∈ ρ.proofs, L1Valid f q k m π

/-! ### Registers and program counters -/

inductive Kind
  | val | l1 | l2
deriving DecidableEq

/-- Register `X[owner, key, sender]`, `X ∈ {Value, L1Proof, L2Proof}`. -/
structure Reg (P : Type) where
  kind : Kind
  owner : P
  key : ℕ
  sender : P
deriving DecidableEq

/-- Per-sender state of Algorithm 2 (line 9). -/
inductive Phase
  | wfs | wfl1 | wfl2
deriving DecidableEq

/-- Program counter of a delivery thread `(p, q)`; it always designates the pending memory
operation. `todo` is the set of slots still to be read in the current loop `for i ∈ Π`,
`acc` the set collected so far (`checkedVals` / `checkedL1Proofs`). -/
inductive PC (P M : Type)
  /-- line 16: reading `L2Proof[i,k,q]` -/
  | rdL2 (i : P) (todo : Finset P)
  /-- line 18: writing the valid L2 proof `ρ` for message `m` to `L2Proof[p,k,q]` -/
  | wrCopy (ρ : L2 P M) (m : M)
  /-- line 37: reading `Value[q,k,q]` -/
  | rdSnd
  /-- line 40: writing the endorsement of `b` to `Value[p,k,q]` -/
  | wrEcho (b : Base P M)
  /-- line 46: reading `Value[i,k,q]` -/
  | rdVal (i : P) (todo : Finset P) (acc : Finset (Copy P M))
  /-- line 52: writing the L1 proof `π` to `L1Proof[p,k,q]` -/
  | wrL1 (π : L1 P M)
  /-- line 58: reading `L1Proof[i,k,q]` -/
  | rdL1 (i : P) (todo : Finset P) (acc : Finset (L1 P M))
  /-- line 64: writing the L2 proof `ρ` to `L2Proof[p,k,q]` -/
  | wrL2 (ρ : L2 P M)

section Defs

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]

/-- The register read by a pending read of thread `(p,q)` working on key `k`. -/
def PC.rd (q : P) (k : ℕ) : PC P M → Option (Reg P)
  | .rdL2 i _ => some ⟨.l2, i, k, q⟩
  | .rdSnd => some ⟨.val, q, k, q⟩
  | .rdVal i _ _ => some ⟨.val, i, k, q⟩
  | .rdL1 i _ _ => some ⟨.l1, i, k, q⟩
  | _ => none

/-- The register and value of a pending write of thread `(p,q)` working on key `k`. -/
def PC.wr (p q : P) (k : ℕ) : PC P M → Option (Reg P × Val P M)
  | .wrCopy ρ _ => some (⟨.l2, p, k, q⟩, .p2 ρ)
  | .wrEcho b => some (⟨.val, p, k, q⟩, .cp ⟨p, b⟩)
  | .wrL1 π => some (⟨.l1, p, k, q⟩, .p1 π)
  | .wrL2 ρ => some (⟨.l2, p, k, q⟩, .p2 ρ)
  | _ => none

/-- Start of `try_deliver`: first read of the loop of `checkL2proof`, at slot `j`. -/
def PC.start (j : P) : PC P M := .rdL2 j (Finset.univ.erase j)

/-- Line 47 (charitable): add the value read from `Value[i,k,q]` to `checkedVals` if it is an
endorsement by `i` of a pair signed by `q` with key `k`. -/
def addVal (i q : P) (k : ℕ) : Val P M → Finset (Copy P M) → Finset (Copy P M)
  | .cp c, acc => if c.signer = i ∧ c.base.sender = q ∧ c.base.key = k then insert c acc else acc
  | _, acc => acc

/-- Lines 59–60: collect the L1 proofs read (validity is checked when the L2 proof is formed). -/
def addL1 : Val P M → Finset (L1 P M) → Finset (L1 P M)
  | .p1 π, acc => insert π acc
  | _, acc => acc

end Defs

/-- Global state: shared memory, local states of correct processes, and ghost variables. -/
structure St (P M : Type) where
  /-- global clock (ghost): number of steps taken so far -/
  now : ℕ
  /-- current value of every register -/
  mem : Reg P → Val P M
  /-- program counter of delivery thread `(p, q)` -/
  pc : P → P → PC P M
  /-- `last[q]` of process `p` -/
  last : P → P → ℕ
  /-- `state[q]` of process `p` -/
  phase : P → P → Phase
  /-- candidate set of the pending read of thread `(p,q)` (regular-register semantics) -/
  cand : P → P → Set (Val P M)
  /-- (ghost) time at which the current L1 scan of thread `(p,q)` started -/
  scanT : P → P → ℕ
  /-- key of the last broadcast of `p` -/
  bnext : P → ℕ
  /-- pending broadcast write of `p` (line 12) -/
  bpend : P → Option (Base P M)
  /-- (ghost) signatures produced by correct processes -/
  signed : Set (P × Sig P M)
  /-- (ghost) `bc p k = some m` iff `p` broadcast `(k, m)` -/
  bc : P → ℕ → Option M
  /-- (ghost) `dlv p q k = some m` iff `p` delivered `(k, m)` from `q` -/
  dlv : P → P → ℕ → Option M
  /-- (ghost) the signed pair echoed by `p` for `(q,k)` (line 40) -/
  echo : P → P → ℕ → Option (Base P M)
  /-- (ghost) time at which the echo write of `p` for `(q,k)` completed -/
  echoT : P → P → ℕ → Option ℕ
  /-- (ghost) the pair supported by the L1 proof of `p` for `(q,k)` and the start time of the
  scan it was built from -/
  l1 : P → P → ℕ → Option (Base P M × ℕ)

namespace St

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]

/-- Two-argument function update. -/
def upd2 {X : Type} (g : P → P → X) (p q : P) (x : X) : P → P → X :=
  Function.update g p (Function.update (g p) q x)

/-- Three-argument function update. -/
def upd3 {X : Type} (g : P → P → ℕ → X) (p q : P) (k : ℕ) (x : X) : P → P → ℕ → X :=
  Function.update g p (Function.update (g p) q (Function.update (g p q) k x))

variable (s : St P M)

/-- The key thread `(p,q)` currently works on (charitable: `last[q] + 1`). -/
def key (p q : P) : ℕ := s.last p q + 1

/-- Values of the pending writes to `r`. -/
def pendW (r : Reg P) : Set (Val P M) :=
  {v | (∃ p q, (s.pc p q).wr p q (s.key p q) = some (r, v)) ∨
       ∃ p b, s.bpend p = some b ∧ r = ⟨.val, p, b.key, p⟩ ∧ v = .cp ⟨p, b⟩}

/-- A write of `v` to `r` is invoked: `v` becomes a candidate of every pending read of `r`. -/
def addCand (r : Reg P) (v : Val P M) : P → P → Set (Val P M) :=
  fun p q => if (s.pc p q).rd q (s.key p q) = some r then insert v (s.cand p q) else s.cand p q

/-- Thread `(p,q)` moves to program counter `c` and invokes the corresponding operation. -/
def go (p q : P) (c : PC P M) : St P M :=
  let s1 : St P M := { s with pc := upd2 s.pc p q c }
  match c.rd q (s.key p q), c.wr p q (s.key p q) with
  | some r, _ => { s1 with cand := upd2 s1.cand p q (insert (s1.mem r) (s1.pendW r)) }
  | none, some (r, v) => { s1 with cand := s1.addCand r v }
  | none, none => s1

/-- A write to `r` responds: the current value becomes `v`. -/
def write (r : Reg P) (v : Val P M) : St P M := { s with mem := Function.update s.mem r v }

/-- A correct process signs. -/
def sign (x : P × Sig P M) : St P M := { s with signed := insert x s.signed }

/-- Lines 30–32: deliver `(k, m)` from `q`, increment `last[q]`, reset `state[q]`. -/
def deliver (p q : P) (m : M) : St P M :=
  { s with dlv := upd3 s.dlv p q (s.key p q) (some m), last := upd2 s.last p q (s.last p q + 1),
           phase := upd2 s.phase p q .wfs }

/-- Set `state[q]` of `p`. -/
def setPhase (p q : P) (ph : Phase) : St P M := { s with phase := upd2 s.phase p q ph }

/-- Line 12: `p` signs `(k, m)` (`k` = next key) and invokes the write of `Value[p,k,p]`. -/
def doBcast (p : P) (m : M) : St P M :=
  let b : Base P M := ⟨p, s.bnext p + 1, m⟩
  { s with bnext := Function.update s.bnext p (s.bnext p + 1),
           bc := Function.update s.bc p (Function.update (s.bc p) (s.bnext p + 1) (some m)),
           signed := insert (p, .base b) (insert (p, .endorse b) s.signed),
           bpend := Function.update s.bpend p (some b),
           cand := s.addCand ⟨.val, p, s.bnext p + 1, p⟩ (.cp ⟨p, b⟩) }

/-- Advance the clock. -/
def tick : St P M := { s with now := s.now + 1 }

/-- Initial state: every delivery thread starts `try_deliver` on key `1`. -/
def init [Inhabited P] : St P M where
  now := 0
  mem := fun _ => .bot
  pc := fun _ _ => PC.start default
  last := fun _ _ => 0
  phase := fun _ _ => .wfs
  cand := fun _ _ => {.bot}
  scanT := fun _ _ => 0
  bnext := fun _ => 0
  bpend := fun _ => none
  signed := ∅
  bc := fun _ _ => none
  dlv := fun _ _ _ => none
  echo := fun _ _ _ => none
  echoT := fun _ _ _ => none
  l1 := fun _ _ _ => none

end St

/-- Step labels: a step of delivery thread `(p,q)`, a broadcast invocation / response of `p`,
or a write of a Byzantine process. -/
inductive Label (P M : Type)
  | thr (p q : P)
  | bcast (p : P) (m : M)
  | bret (p : P)
  | byz (p : P) (r : Reg P) (v : Val P M)

section Step

variable {P M : Type} [Fintype P] [DecidableEq P] [DecidableEq M]
variable (F : Finset P) (f : ℕ)

open St

/-- One step of the system (Algorithm 2 for correct processes, arbitrary own-register writes
respecting unforgeability for Byzantine ones). -/
inductive Step : St P M → Label P M → St P M → Prop
  /-- lines 16–18: a valid L2 proof is read; write it to the own slot -/
  | l2Found {s : St P M} {p q i : P} {todo v ρ m} (hp : p ∉ F) (hpc : s.pc p q = .rdL2 i todo)
      (hv : v ∈ s.cand p q) (hρ : v = .p2 ρ) (hval : L2Valid f q (s.key p q) m ρ) :
      Step s (.thr p q) ((s.go p q (.wrCopy ρ m)).tick)
  /-- line 15: the slot read holds no valid L2 proof; read the next slot -/
  | l2Next {s : St P M} {p q i j : P} {todo v} (hp : p ∉ F) (hpc : s.pc p q = .rdL2 i todo)
      (hv : v ∈ s.cand p q) (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key p q) m ρ)
      (hj : j ∈ todo) :
      Step s (.thr p q) ((s.go p q (.rdL2 j (todo.erase j))).tick)
  /-- line 20, `state = WaitForSender`: read `Value[q,k,q]` (line 37) -/
  | l2EndS {s : St P M} {p q i : P} {v} (hp : p ∉ F) (hpc : s.pc p q = .rdL2 i ∅)
      (hv : v ∈ s.cand p q) (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key p q) m ρ)
      (hph : s.phase p q = .wfs) :
      Step s (.thr p q) ((s.go p q .rdSnd).tick)
  /-- line 20, `state = WaitForL1Proof`: start the scan of the `Value` slots (line 45) -/
  | l2EndV {s : St P M} {p q i j : P} {v} (hp : p ∉ F) (hpc : s.pc p q = .rdL2 i ∅)
      (hv : v ∈ s.cand p q) (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key p q) m ρ)
      (hph : s.phase p q = .wfl1) :
      Step s (.thr p q)
        ({ s.go p q (.rdVal j (Finset.univ.erase j) ∅) with
            scanT := upd2 s.scanT p q s.now }.tick)
  /-- line 20, `state = WaitForL2Proof`: start the scan of the `L1Proof` slots (line 57) -/
  | l2EndL {s : St P M} {p q i j : P} {v} (hp : p ∉ F) (hpc : s.pc p q = .rdL2 i ∅)
      (hv : v ∈ s.cand p q) (hnv : ¬ ∃ ρ m, v = .p2 ρ ∧ L2Valid f q (s.key p q) m ρ)
      (hph : s.phase p q = .wfl2) :
      Step s (.thr p q) ((s.go p q (.rdL1 j (Finset.univ.erase j) ∅)).tick)
  /-- line 18 completes; lines 30–33: deliver and start the next `try_deliver` -/
  | copyDone {s : St P M} {p q j : P} {ρ m} (hp : p ∉ F) (hpc : s.pc p q = .wrCopy ρ m) :
      Step s (.thr p q)
        ((((s.write ⟨.l2, p, s.key p q, q⟩ (.p2 ρ)).deliver p q m).go p q (PC.start j)).tick)
  /-- lines 37–40: a valid signed pair is read; sign it and write it to the own slot -/
  | sndOk {s : St P M} {p q : P} {v c} (hp : p ∉ F) (hpc : s.pc p q = .rdSnd)
      (hv : v ∈ s.cand p q) (hc : v = .cp c) (hs : c.base.sender = q)
      (hk : c.base.key = s.key p q) :
      Step s (.thr p q)
        ((({ s with echo := upd3 s.echo p q (s.key p q) (some c.base) }.sign
            (p, .endorse c.base)).go p q (.wrEcho c.base)).tick)
  /-- lines 38–39: nothing valid read; return -/
  | sndBad {s : St P M} {p q j : P} {v} (hp : p ∉ F) (hpc : s.pc p q = .rdSnd)
      (hv : v ∈ s.cand p q)
      (hbad : ¬ ∃ c, v = .cp c ∧ c.base.sender = q ∧ c.base.key = s.key p q) :
      Step s (.thr p q) ((s.go p q (PC.start j)).tick)
  /-- line 40 completes; line 41 -/
  | echoDone {s : St P M} {p q j : P} {b} (hp : p ∉ F) (hpc : s.pc p q = .wrEcho b) :
      Step s (.thr p q)
        (((({ s.write ⟨.val, p, s.key p q, q⟩ (.cp ⟨p, b⟩) with
              echoT := upd3 s.echoT p q (s.key p q) (some s.now) }).setPhase p q .wfl1).go p q
            (PC.start j)).tick)
  /-- lines 46–48, not the last slot -/
  | valNext {s : St P M} {p q i j : P} {todo acc v} (hp : p ∉ F)
      (hpc : s.pc p q = .rdVal i todo acc) (hv : v ∈ s.cand p q) (hj : j ∈ todo) :
      Step s (.thr p q)
        ((s.go p q (.rdVal j (todo.erase j) (addVal i q (s.key p q) v acc))).tick)
  /-- lines 46–52, last slot, the check of line 50 succeeds: sign and write the L1 proof -/
  | valOk {s : St P M} {p q i : P} {acc v b} (hp : p ∉ F) (hpc : s.pc p q = .rdVal i ∅ acc)
      (hv : v ∈ s.cand p q) (hcard : f + 1 ≤ (addVal i q (s.key p q) v acc).card)
      (hb : ∀ c ∈ addVal i q (s.key p q) v acc, c.base = b) :
      Step s (.thr p q)
        ((({ s with l1 := upd3 s.l1 p q (s.key p q) (some (b, s.scanT p q)) }.sign
            (p, .l1 ⟨p, addVal i q (s.key p q) v acc⟩)).go p q
            (.wrL1 ⟨p, addVal i q (s.key p q) v acc⟩)).tick)
  /-- lines 46–50, last slot, the check of line 50 fails: return -/
  | valBad {s : St P M} {p q i j : P} {acc v} (hp : p ∉ F) (hpc : s.pc p q = .rdVal i ∅ acc)
      (hv : v ∈ s.cand p q)
      (hbad : ¬ (f + 1 ≤ (addVal i q (s.key p q) v acc).card ∧
                ∃ b, ∀ c ∈ addVal i q (s.key p q) v acc, c.base = b)) :
      Step s (.thr p q) ((s.go p q (PC.start j)).tick)
  /-- line 52 completes; line 53 -/
  | l1Done {s : St P M} {p q j : P} {π} (hp : p ∉ F) (hpc : s.pc p q = .wrL1 π) :
      Step s (.thr p q)
        ((((s.write ⟨.l1, p, s.key p q, q⟩ (.p1 π)).setPhase p q .wfl2).go p q
            (PC.start j)).tick)
  /-- lines 58–60, not the last slot -/
  | l1Next {s : St P M} {p q i j : P} {todo acc v} (hp : p ∉ F)
      (hpc : s.pc p q = .rdL1 i todo acc) (hv : v ∈ s.cand p q) (hj : j ∈ todo) :
      Step s (.thr p q) ((s.go p q (.rdL1 j (todo.erase j) (addL1 v acc))).tick)
  /-- lines 58–64, last slot, `f+1` valid L1 proofs for one value: sign and write an L2 proof -/
  | l1Ok {s : St P M} {p q i : P} {acc v S m} (hp : p ∉ F) (hpc : s.pc p q = .rdL1 i ∅ acc)
      (hv : v ∈ s.cand p q) (hS : S ⊆ addL1 v acc) (hval : L2Valid f q (s.key p q) m ⟨p, S⟩) :
      Step s (.thr p q) (((s.sign (p, .l2 ⟨p, S⟩)).go p q (.wrL2 ⟨p, S⟩)).tick)
  /-- lines 58–62, last slot, not enough valid L1 proofs: return -/
  | l1Bad {s : St P M} {p q i j : P} {acc v} (hp : p ∉ F) (hpc : s.pc p q = .rdL1 i ∅ acc)
      (hv : v ∈ s.cand p q)
      (hbad : ¬ ∃ S m, S ⊆ addL1 v acc ∧ L2Valid f q (s.key p q) m ⟨p, S⟩) :
      Step s (.thr p q) ((s.go p q (PC.start j)).tick)
  /-- line 64 completes: return -/
  | l2Done {s : St P M} {p q j : P} {ρ} (hp : p ∉ F) (hpc : s.pc p q = .wrL2 ρ) :
      Step s (.thr p q) (((s.write ⟨.l2, p, s.key p q, q⟩ (.p2 ρ)).go p q (PC.start j)).tick)
  /-- line 11–12: `broadcast(k, m)` is invoked (`k` = previous key + 1) -/
  | bcast {s : St P M} {p : P} {m : M} (hp : p ∉ F) (hidle : s.bpend p = none) :
      Step s (.bcast p m) ((s.doBcast p m).tick)
  /-- the write of line 12 completes; `broadcast` returns -/
  | bret {s : St P M} {p : P} {b} (hp : p ∉ F) (hb : s.bpend p = some b) :
      Step s (.bret p)
        ({ s.write ⟨.val, p, b.key, p⟩ (.cp ⟨p, b⟩) with
            bpend := Function.update s.bpend p none }.tick)
  /-- no broadcast pending: no-op -/
  | bretIdle {s : St P M} {p : P} (hp : p ∉ F) (hidle : s.bpend p = none) :
      Step s (.bret p) s.tick
  /-- a Byzantine process writes (atomically) any unforgeable value to one of its registers -/
  | byz {s : St P M} {p : P} {r : Reg P} {v : Val P M} (hp : p ∈ F) (hr : r.owner = p)
      (hv : SigOK F s.signed v) :
      Step s (.byz p r v) ({ s.write r v with cand := s.addCand r v }.tick)

/-- Reachable states. -/
inductive Reachable [Inhabited P] : St P M → Prop
  | init : Reachable St.init
  | step {s s' : St P M} {ℓ : Label P M} : Reachable s → Step F f s ℓ s' → Reachable s'

/-- An infinite execution. -/
structure Exec [Inhabited P] where
  s : ℕ → St P M
  ℓ : ℕ → Label P M
  init : s 0 = St.init
  step : ∀ t, Step F f (s t) (ℓ t) (s (t + 1))

/-- Fairness: every delivery thread of a correct process takes infinitely many steps, and every
correct process takes infinitely many broadcast-response steps (so every pending broadcast write
of a correct process completes). -/
def Exec.Fair [Inhabited P] (e : Exec (M := M) F f) : Prop :=
  (∀ p ∉ F, ∀ q : P, ∀ t, ∃ t' ≥ t, e.ℓ t' = .thr p q) ∧
  (∀ p ∉ F, ∀ t, ∃ t' ≥ t, e.ℓ t' = .bret p)

end Step

end Podc.RDMAAgreement.RB
