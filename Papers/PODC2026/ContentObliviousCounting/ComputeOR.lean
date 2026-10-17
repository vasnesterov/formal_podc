import Cslib.Computability.Distributed.ContentOblivious.Mirror
import Mathlib

/-!
# Algorithm 9 (`ComputeOR`) and Theorem 21

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260), §6.2: Algorithm 9 `ComputeOR(bool)`, Lemmas 18–20, Theorem 21.

**Model.** Oriented ring `ZMod n` (`n ≥ 1`; `Port1 = true` is the clockwise port), asynchronous
content-oblivious pulses, adversarial scheduler (`Cslib.ContentOblivious.Step`), no failures,
deterministic nodes, exactly one leader. The input of a node is `(isLeader, bool)`.

**Encoding of the pseudo-code.** A node has a program counter `pc` = number of blocking receives
completed so far: `pc = 0` is the receive of line 7, `pc = 1` the second receive (line 11 or 18 for
the leader, line 22 for a non-leader with `bool = true`, line 26 for a non-leader with
`bool = false`), `pc = 2` the barrier receive (line 32 or 34), and `pc = 3` means "returned".
Port-specific receives are modelled by `ready` (lines 11, 18: port 1; line 22: port `1 - q`;
lines 32, 34: port 0); the receives of lines 7 and 26 accept any port. Each reception executes the
code up to the next receive (sends and assignments of `q` and `ans`).

**Proof method.** In every reachable configuration, node `v` has completed `π v` receives, and
the ports of these receives are those of a fixed *role* `typ v` (which depends only on the inputs
and on the position of `v`; e.g. in the all-false case every node receives on ports `1, 1, 0`).
The invariant is proved by showing that a pulse in transit always arrives at the expected port of
a node willing to read it; this follows from the channel inequalities between neighbours (checked
by `decide` over all pairs of adjacent roles) and, in the three exceptional situations, from a
propagation argument around the ring. This covers all interleavings (in fact the execution is
unique: at most one pulse is in transit).
-/

namespace Podc.ContentOblivious.ComputeOR

open Cslib.ContentOblivious Finset

/-- Local state of Algorithm 9. -/
structure St where
  /-- input: is this node the leader -/
  ldr : Bool
  /-- input `bool` -/
  b : Bool
  /-- number of blocking receives completed (`3` = returned) -/
  pc : ℕ
  /-- the port `q` of the first reception (line 7) -/
  q : Bool
  /-- the variable `ans` -/
  ans : Bool
  deriving DecidableEq

/-- Lines 1–6. -/
def init (a : Bool × Bool) : St × (Bool → ℕ) :=
  (⟨a.1, a.2, 0, false, true⟩, if a.1 then onePulse a.2 else fun _ => 0)

/-- Reception of a pulse on port `j`, and the code executed up to the next receive. -/
def recv (s : St) (j : Bool) : St × (Bool → ℕ) :=
  match s.pc with
  | 0 => -- line 7, then lines 9–17 (leader) or 20–25 (non-leader)
    ({ s with pc := 1, q := j },
      if s.ldr then onePulse (!j && !s.b) else if s.b then onePulse true else onePulse (!j))
  | 1 =>
    if s.ldr then ({ s with pc := 2, ans := !s.q }, onePulse true) -- lines 11–12 / 18, then line 31
    else if s.b then ({ s with pc := 2 }, onePulse false) -- lines 22–23
    else ({ s with pc := 2, ans := !(j && s.q) }, onePulse (!j)) -- lines 26–29
  | _ => ({ s with pc := 3 }, if s.ldr then fun _ => 0 else onePulse true) -- lines 32 / 34–35, 36

/-- The port(s) on which the node waits. -/
def ready (s : St) (j : Bool) : Bool :=
  match s.pc with
  | 0 => true
  | 1 => if s.ldr then j else if s.b then j == !s.q else true
  | 2 => !j
  | _ => false

/-- **Algorithm 9** (`ComputeOR`) as a procedure with input `(isLeader, bool)`. -/
abbrev proc : Proc (Bool × Bool) Bool where
  State := St
  init := init
  recv := recv
  ready := ready
  terminated s := decide (3 ≤ s.pc)
  result s := if 3 ≤ s.pc then some s.ans else none
  terminated_eq s := by by_cases h : 3 ≤ s.pc <;> simp [h]

/-! ## Roles -/

/-- The roles of nodes: `L18`, `N18` (leader / non-leader, all inputs false, Lemma 18);
`L19`, `A`, `J`, `B0`, `B1` (Lemma 19: the leader, the false nodes strictly between the leader and
the first true node `J` counter-clockwise, `J`, the remaining nodes with input false / true);
`L20`, `N0`, `N1` (Lemma 20: leader, non-leaders with input false / true). -/
inductive Role
  | L18 | N18 | L19 | A | J | B0 | B1 | L20 | N0 | N1
  deriving DecidableEq

namespace Role

instance : Fintype Role :=
  ⟨{L18, N18, L19, A, J, B0, B1, L20, N0, N1}, by intro r; cases r <;> decide⟩

/-- `(isLeader, bool, port of 1st reception, port of 2nd reception)`. -/
def data : Role → Bool × Bool × Bool × Bool
  | L18 => (true, false, true, true)
  | N18 => (false, false, true, true)
  | L19 => (true, false, false, true)
  | A => (false, false, true, false)
  | J => (false, true, true, false)
  | B0 => (false, false, false, true)
  | B1 => (false, true, false, true)
  | L20 => (true, true, false, true)
  | N0 => (false, false, false, true)
  | N1 => (false, true, false, true)

def ldr (r : Role) : Bool := r.data.1
def b (r : Role) : Bool := r.data.2.1
def q (r : Role) : Bool := r.data.2.2.1
def u (r : Role) : Bool := r.data.2.2.2

/-- The output of a node of this role. -/
def fans (r : Role) : Bool := if r.ldr then !r.q else if r.b then true else !(r.q && r.u)

/-- Port of the `m`-th reception (from `0`). -/
def hist (r : Role) (m : ℕ) : Bool :=
  match m with
  | 0 => r.q
  | 1 => r.u
  | _ => false

/-- State of a node of role `r` after `m` receptions. -/
def mk (r : Role) (m : ℕ) : St :=
  ⟨r.ldr, r.b, m, if 1 ≤ m then r.q else false, if 2 ≤ m then r.fans else true⟩

/-- Pulses sent at the `m`-th reception. -/
def step (r : Role) (m : ℕ) : Bool → ℕ := (recv (r.mk m) (r.hist m)).2

/-- Pulses sent on port `p` after `m` receptions. -/
def sentR (r : Role) (m : ℕ) (p : Bool) : ℕ :=
  (init (r.ldr, r.b)).2 p + (if 1 ≤ m then r.step 0 p else 0) +
    (if 2 ≤ m then r.step 1 p else 0) + (if 3 ≤ m then r.step 2 p else 0)

/-- Pulses received on port `p` after `m` receptions. -/
def recvdR (r : Role) (m : ℕ) (p : Bool) : ℕ :=
  (if 1 ≤ m ∧ r.hist 0 = p then 1 else 0) + (if 2 ≤ m ∧ r.hist 1 = p then 1 else 0) +
    (if 3 ≤ m ∧ r.hist 2 = p then 1 else 0)

/-- Adjacent roles `(typ v, typ (v + 1))`. -/
def Adj : Role → Role → Bool
  | N18, N18 | N18, L18 | L18, N18 | L18, L18 => true
  | A, A | J, A | A, L19 | J, L19 | L19, B0 | L19, B1 | B0, B0 | B0, B1 | B1, B0 | B1, B1
  | B0, J | B1, J | L19, J => true
  | N0, N0 | N0, N1 | N1, N0 | N1, N1 | N0, L20 | N1, L20 | L20, N0 | L20, N1 | L20, L20 => true
  | _, _ => false

/-- Channel inequalities on the link from a node of role `r` with `m` receptions to its clockwise
neighbour of role `r'` with `m'` receptions. -/
def LC (r : Role) (m : ℕ) (r' : Role) (m' : ℕ) : Prop :=
  r'.recvdR m' false ≤ r.sentR m true ∧ r.recvdR m true ≤ r'.sentR m' false

instance (r : Role) (m : ℕ) (r' : Role) (m' : ℕ) : Decidable (LC r m r' m') := by
  unfold LC; infer_instance

/-- Thresholds for the three propagation arguments. -/
def θ1 (r : Role) : ℕ := if r.ldr then 2 else 3
def θ2 : Role → ℕ
  | L19 | J | B0 | B1 => 1
  | A => 2
  | _ => 0
def θ3 : Role → ℕ
  | L20 => 1
  | N0 | N1 => 2
  | _ => 0

/-! ### Finite checks -/

lemma mk_zero (r : Role) : r.mk 0 = (init (r.ldr, r.b)).1 := by cases r <;> decide

lemma sentR_zero (r : Role) (p : Bool) : r.sentR 0 p = (init (r.ldr, r.b)).2 p := by
  simp [sentR]

lemma recvdR_zero (r : Role) (p : Bool) : r.recvdR 0 p = 0 := by simp [recvdR]

theorem recv_mk : ∀ r : Role, ∀ m < 3, recv (r.mk m) (r.hist m) = (r.mk (m + 1), r.step m) := by
  decide

theorem sentR_succ : ∀ r : Role, ∀ m < 3, ∀ p, r.sentR (m + 1) p = r.sentR m p + r.step m p := by
  decide

theorem recvdR_succ : ∀ r : Role, ∀ m < 3, ∀ p,
    r.recvdR (m + 1) p = r.recvdR m p + if p = r.hist m then 1 else 0 := by
  decide

/-! Checks over all pairs of adjacent roles `r` (node `v`, `m` receptions) and `r'` (node
`v + 1`, `m'` receptions). The hypothesis `r.ldr → r'.ldr → m = m'` accounts for the 1-node ring
(where `v + 1 = v`). -/

/-- A pulse in transit to `Port0` of `v + 1` arrives at an expected port of a node willing to read
it, except in two situations excluded by `chain1` and `chain2`. -/
theorem good0 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true →
    (r.ldr = true → r'.ldr = true → (m : ℕ) = m') → LC r m r' m' →
    r'.recvdR m' false < r.sentR m true →
    ((m' : ℕ) < 3 ∧ r'.hist m' = false ∧ ready (r'.mk m') false = true) ∨
      (r'.ldr = true ∧ (m : ℕ) = 3 ∧ (m' : ℕ) = 1) ∨ (r' = Role.J ∧ (m : ℕ) = 1 ∧ (m' : ℕ) = 0) := by
  decide

/-- A pulse in transit to `Port1` of `v` arrives at an expected port of a node willing to read it,
except in one situation excluded by `chain3`. -/
theorem good1 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true →
    (r.ldr = true → r'.ldr = true → (m : ℕ) = m') → LC r m r' m' →
    r.recvdR m true < r'.sentR m' false →
    ((m : ℕ) < 3 ∧ r.hist m = true ∧ ready (r.mk m) true = true) ∨
      (r = Role.L20 ∧ r'.ldr = false ∧ (m : ℕ) = 0 ∧ (m' : ℕ) = 2) := by
  decide

theorem chain1 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true → r'.ldr = false →
    LC r m r' m' → θ1 r' ≤ m' → θ1 r ≤ m := by
  decide

theorem chain2 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true → r' ≠ Role.J →
    (r.ldr = true → r'.ldr = true → (m : ℕ) = m') → LC r m r' m' → θ2 r' ≤ m' → θ2 r ≤ m := by
  decide

theorem chain2_start : ∀ r : Role, Adj r Role.J = true → θ2 r ≤ 1 := by decide

theorem chain3 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true → r.ldr = false →
    LC r m r' m' → θ3 r ≤ m → θ3 r' ≤ m' := by
  decide

theorem chain3_start : ∀ r : Role, Adj Role.L20 r = true → r.ldr = false → θ3 r ≤ 2 := by decide

theorem chain4 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true → r.ldr = false →
    LC r m r' m' → (m' : ℕ) = 3 → (m : ℕ) = 3 := by
  decide

theorem clean0 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true →
    (r.ldr = true → r'.ldr = true → (m : ℕ) = m') → LC r m r' m' → (m : ℕ) = 3 → (m' : ℕ) < 3 →
    ready (r'.mk m') false = true → r'.recvdR m' false < r.sentR m true := by
  decide

theorem clean1 : ∀ r r' : Role, ∀ m m' : Fin 4, Adj r r' = true →
    (r.ldr = true → r'.ldr = true → (m : ℕ) = m') → LC r m r' m' → (m' : ℕ) = 3 → (m : ℕ) < 3 →
    ready (r.mk m) true = true → r.recvdR m true < r'.sentR m' false := by
  decide

theorem count : ∀ r : Role, ∀ m : Fin 4,
    r.sentR m false + r.sentR m true =
      r.recvdR m false + r.recvdR m true + (if r.ldr = true ∧ (m : ℕ) < 3 then 1 else 0) := by
  decide

theorem sent_le : ∀ r : Role, ∀ m : Fin 4, r.sentR m false + r.sentR m true ≤ 3 := by decide

theorem sent_three : ∀ r : Role, r.sentR 3 false + r.sentR 3 true = 3 := by decide

theorem mk_pc (r : Role) (m : ℕ) : (r.mk m).pc = m := rfl

theorem mk_ans (r : Role) : (r.mk 3).ans = r.fans := rfl

end Role

/-! ## The invariant -/

open Role

lemma θ1_le (r : Role) : θ1 r ≤ 3 := by cases r <;> decide

variable {n : ℕ} [NeZero n]

/-- A role assignment compatible with the inputs `x`. -/
structure Typing (x : ZMod n → Bool × Bool) (typ : ZMod n → Role) : Prop where
  adj : ∀ v, Adj (typ v) (typ (v + 1)) = true
  inp : ∀ v, x v = ((typ v).ldr, (typ v).b)
  uniqL : ∀ u v, (typ u).ldr = true → (typ v).ldr = true → u = v
  uniqJ : ∀ u v, typ u = Role.J → typ v = Role.J → u = v
  exL : ∃ ℓ, (typ ℓ).ldr = true

/-- The configuration in which node `v` has role `typ v` and has completed `π v` receptions. -/
def cfgOf (typ : ZMod n → Role) (π : ZMod n → ℕ) : Config (ZMod n) St where
  st v := (typ v).mk (π v)
  sent p := (typ p.1).sentR (π p.1) p.2
  recvd p := (typ p.1).recvdR (π p.1) p.2

variable {x : ZMod n → Bool × Bool} {typ : ZMod n → Role}

omit [NeZero n] in
lemma recvd_le {c : Config (ZMod n) St} (hr : proc.Reach (oriented n) x c) (p : ZMod n × Bool) :
    c.recvd p ≤ c.sent ((oriented n).peer p) :=
  Reach.recvd_le (W := oriented n) (A := proc.toAlgo) hr p

omit [NeZero n] in
lemma lc {π : ZMod n → ℕ} (hr : proc.Reach (oriented n) x (cfgOf typ π)) (v : ZMod n) :
    LC (typ v) (π v) (typ (v + 1)) (π (v + 1)) := by
  constructor
  · have := recvd_le hr (v + 1, false)
    simpa [cfgOf] using this
  · have := recvd_le hr (v, true)
    simpa [cfgOf] using this

omit [NeZero n] in
lemma ldr_cond (T : Typing x typ) (π : ZMod n → ℕ) (v : ZMod n) :
    (typ v).ldr = true → (typ (v + 1)).ldr = true → π v = π (v + 1) := fun h1 h2 =>
  congrArg π (T.uniqL _ _ h1 h2)

/-- Every pulse in transit is expected: it arrives at the port of the next reception of a node
willing to read it. -/
theorem expected (T : Typing x typ) {π : ZMod n → ℕ} (hπ : ∀ v, π v < 4)
    (hr : proc.Reach (oriented n) x (cfgOf typ π)) (w : ZMod n) (j : Bool)
    (ht : (cfgOf typ π).recvd (w, j) < (cfgOf typ π).sent ((oriented n).peer (w, j))) :
    π w < 3 ∧ (typ w).hist (π w) = j ∧ ready ((typ w).mk (π w)) j = true := by
  let f : ZMod n → Fin 4 := fun v => ⟨π v, hπ v⟩
  cases j
  · -- a pulse arriving at `Port0` of `w`, from `w - 1`
    have hw : w - 1 + 1 = w := sub_add_cancel w 1
    have hlc := lc hr (w - 1)
    have hcond := ldr_cond T π (w - 1)
    have hadj := T.adj (w - 1)
    rw [hw] at hlc hcond hadj
    have ht' : (typ w).recvdR (π w) false < (typ (w - 1)).sentR (π (w - 1)) true := by
      simpa [cfgOf] using ht
    rcases good0 (typ (w - 1)) (typ w) (f (w - 1)) (f w) hadj hcond hlc ht' with h | h | h
    · exact h
    · -- the leader waits at its second receive while its counter-clockwise neighbour returned
      exfalso
      obtain ⟨hl, h1, h2⟩ := h
      change π (w - 1) = 3 at h1; change π w = 1 at h2
      have := Ring.chain_ccw_all (fun u => θ1 (typ u) ≤ π u) (w - 1) (fun u hu hS => by
        have hu' : u + 1 ≠ w := fun e => hu (by rw [← e, add_sub_cancel_right])
        have hnl : (typ (u + 1)).ldr = false := by
          by_contra hc; exact hu' (T.uniqL _ _ (by simpa using hc) hl)
        exact chain1 (typ u) (typ (u + 1)) (f u) (f (u + 1)) (T.adj u) hnl (lc hr u) hS)
        (by show θ1 _ ≤ π (w - 1); rw [h1]; exact θ1_le _) w
      have e : θ1 (typ w) = 2 := by simp [θ1, hl]
      simp only [e] at this; omega
    · -- `J` has not received yet while its clockwise neighbour has
      exfalso
      obtain ⟨hJ, h1, h2⟩ := h
      change π (w - 1) = 1 at h1; change π w = 0 at h2
      have := Ring.chain_ccw_all (fun u => θ2 (typ u) ≤ π u) (w - 1) (fun u hu hS => by
        have hu' : u + 1 ≠ w := fun e => hu (by rw [← e, add_sub_cancel_right])
        have hnJ : typ (u + 1) ≠ Role.J := fun hc => hu' (T.uniqJ _ _ hc hJ)
        exact chain2 (typ u) (typ (u + 1)) (f u) (f (u + 1)) (T.adj u) hnJ (ldr_cond T π u)
          (lc hr u) hS)
        (by
          have := chain2_start (typ (w - 1)) (by rw [← hJ]; exact hadj)
          show θ2 _ ≤ π (w - 1); omega) w
      simp only [hJ] at this; simp only [θ2] at this; omega
  · -- a pulse arriving at `Port1` of `w`, from `w + 1`
    have ht' : (typ w).recvdR (π w) true < (typ (w + 1)).sentR (π (w + 1)) false := by
      simpa [cfgOf] using ht
    rcases good1 (typ w) (typ (w + 1)) (f w) (f (w + 1)) (T.adj w) (ldr_cond T π w) (lc hr w)
      ht' with h | h
    · exact h
    · -- the leader (`bool = true`) has not received yet while its clockwise neighbour already
      -- received the counter-clockwise wave
      exfalso
      obtain ⟨hL, hnl, h1, h2⟩ := h
      change π w = 0 at h1; change π (w + 1) = 2 at h2
      have hl : (typ w).ldr = true := by rw [hL]; rfl
      have := Ring.chain_cw_all (fun u => θ3 (typ u) ≤ π u) w (fun u hu hS => by
        have hnl' : (typ u).ldr = false := by
          by_contra hc; exact hu (T.uniqL _ _ (by simpa using hc) hl)
        exact chain3 (typ u) (typ (u + 1)) (f u) (f (u + 1)) (T.adj u) hnl' (lc hr u) hS)
        (by
          have := chain3_start (typ (w + 1)) (by rw [← hL]; exact T.adj w) hnl
          show θ3 _ ≤ π (w + 1); omega) w
      simp only [hL] at this; simp only [θ3] at this; omega

omit [NeZero n] in
lemma deliver_cfgOf {π : ZMod n → ℕ} (w : ZMod n) (hw : π w < 3) :
    deliver proc.toAlgo (cfgOf typ π) w ((typ w).hist (π w)) =
      cfgOf typ (Function.update π w (π w + 1)) := by
  have hrecv := recv_mk (typ w) (π w) hw
  ext v
  · by_cases h : v = w
    · subst h; simp [deliver, cfgOf, hrecv]
    · simp [deliver, cfgOf, h]
  · rcases v with ⟨v, p⟩
    by_cases h : v = w
    · subst h; simp [deliver, cfgOf, hrecv, sentR_succ _ _ hw]
    · simp [deliver, cfgOf, h]
  · rcases v with ⟨v, p⟩
    by_cases h : v = w
    · subst h; simp [deliver, cfgOf, recvdR_succ _ _ hw]
    · simp [deliver, cfgOf, h]

/-- **Invariant**: every reachable configuration is of the form `cfgOf typ π`. -/
theorem reach_inv (T : Typing x typ) {c : Config (ZMod n) St} (hc : proc.Reach (oriented n) x c) :
    ∃ π : ZMod n → ℕ, (∀ v, π v < 4) ∧ c = cfgOf typ π := by
  refine Prog.Reach.induction (motive := fun c => ∃ π : ZMod n → ℕ, (∀ v, π v < 4) ∧
    c = cfgOf typ π) ?_ ?_ hc
  · refine ⟨fun _ => 0, fun _ => by norm_num, ?_⟩
    ext v
    · simp [Prog.initCfg, cfgOf, T.inp v, Role.mk_zero]
    · simp [Prog.initCfg, cfgOf, T.inp, sentR_zero]
    · simp [Prog.initCfg, cfgOf, recvdR_zero]
  · intro c c' hr hs ih
    obtain ⟨π, hπ, rfl⟩ := ih
    obtain ⟨w, j, hen⟩ := hs
    obtain ⟨h3, hj, -⟩ := expected T hπ hr w j hen.2.2
    subst hj
    refine ⟨Function.update π w (π w + 1), fun v => ?_, deliver_cfgOf w h3⟩
    rw [Function.update_apply]; split_ifs <;> [omega; exact hπ v]

lemma totalSent_cfgOf (π : ZMod n → ℕ) :
    totalSent (cfgOf typ π) = ∑ v, ((typ v).sentR (π v) false + (typ v).sentR (π v) true) := by
  simp [totalSent, sum_ports, cfgOf]

lemma totalRecvd_cfgOf (π : ZMod n → ℕ) :
    totalRecvd (cfgOf typ π) = ∑ v, ((typ v).recvdR (π v) false + (typ v).recvdR (π v) true) := by
  simp [totalRecvd, sum_ports, cfgOf]

lemma totalSent_eq (π : ZMod n → ℕ) (hπ : ∀ v, π v < 4) :
    totalSent (cfgOf typ π) = totalRecvd (cfgOf typ π) +
      ∑ v, (if (typ v).ldr = true ∧ π v < 3 then 1 else 0) := by
  rw [totalSent_cfgOf, totalRecvd_cfgOf, ← sum_add_distrib]
  exact sum_congr rfl fun v _ => count (typ v) ⟨π v, hπ v⟩

lemma totalSent_le' (π : ZMod n → ℕ) (hπ : ∀ v, π v < 4) : totalSent (cfgOf typ π) ≤ 3 * n := by
  rw [totalSent_cfgOf]
  calc ∑ v, ((typ v).sentR (π v) false + (typ v).sentR (π v) true) ≤ ∑ _v : ZMod n, 3 :=
        sum_le_sum fun v _ => sent_le (typ v) ⟨π v, hπ v⟩
    _ = 3 * n := by simp [ZMod.card, mul_comm]

/-- Final configurations: quiescent, and every node has completed its three receptions. -/
theorem final_spec (T : Typing x typ) {π : ZMod n → ℕ} (hπ : ∀ v, π v < 4)
    (hr : proc.Reach (oriented n) x (cfgOf typ π)) (hf : proc.Final (oriented n) (cfgOf typ π)) :
    proc.Quiescent (oriented n) (cfgOf typ π) ∧ ∀ v, π v = 3 := by
  have hq : proc.Quiescent (oriented n) (cfgOf typ π) := by
    intro p
    by_contra hne
    have hlt := lt_of_le_of_ne (recvd_le hr p) hne
    obtain ⟨h3, -, hrd⟩ := expected T hπ hr p.1 p.2 hlt
    refine hf p.1 p.2 ⟨?_, hrd, hlt⟩
    show decide (3 ≤ ((typ p.1).mk (π p.1)).pc) = false
    rw [Role.mk_pc]; simpa using h3
  refine ⟨hq, ?_⟩
  obtain ⟨ℓ, hℓ⟩ := T.exL
  have hsum := totalSent_eq (typ := typ) π hπ
  rw [← Quiescent.totalRecvd_eq hq] at hsum
  have hzero : ∑ v, (if (typ v).ldr = true ∧ π v < 3 then 1 else 0) = 0 := by omega
  have hl3 : π ℓ = 3 := by
    have := (sum_eq_zero_iff.1 hzero) ℓ (mem_univ _)
    simp only [hℓ, true_and, ite_eq_right_iff, one_ne_zero, imp_false, not_lt] at this
    have := hπ ℓ; omega
  exact Ring.chain_ccw_all (fun u => π u = 3) ℓ (fun u hu h1 => by
    have hnl : (typ u).ldr = false := by
      by_contra hc; exact hu (T.uniqL _ _ (by simpa using hc) hℓ)
    exact chain4 (typ u) (typ (u + 1)) ⟨π u, hπ u⟩ ⟨π (u + 1), hπ (u + 1)⟩ (T.adj u) hnl
      (lc hr u) h1) hl3

theorem composable_of_typing (T : Typing x typ) : proc.Composable (oriented n) x where
  bounded := ⟨3 * n, fun c hc => by
    obtain ⟨π, hπ, rfl⟩ := reach_inv T hc
    exact totalSent_le' π hπ⟩
  final c hc hf := by
    obtain ⟨π, hπ, rfl⟩ := reach_inv T hc
    obtain ⟨hq, h3⟩ := final_spec T hπ hc hf
    exact ⟨hq, fun v => by simp [cfgOf, Role.mk_pc, h3 v]⟩
  clean c hc v j hv hrd hpeer := by
    obtain ⟨π, hπ, rfl⟩ := reach_inv T hc
    have hv3 : π v < 3 := by
      by_contra h
      have h' : 3 ≤ ((typ v).mk (π v)).pc := by rw [Role.mk_pc]; omega
      simp [cfgOf, h'] at hv
    have h3 : ∀ u, π u ≠ 3 → ¬ 3 ≤ ((typ u).mk (π u)).pc := by
      intro u hu; rw [Role.mk_pc]; have := hπ u; omega
    cases j
    · have hw : v - 1 + 1 = v := sub_add_cancel v 1
      have hlc := lc hc (v - 1)
      have hcond := ldr_cond T π (v - 1)
      have hadj := T.adj (v - 1)
      rw [hw] at hlc hcond hadj
      have := clean0 (typ (v - 1)) (typ v) ⟨π (v - 1), hπ _⟩ ⟨π v, hπ v⟩ hadj hcond hlc
        (by by_contra h; simp [cfgOf, h3 _ h] at hpeer) hv3 hrd
      simpa [cfgOf] using this
    · have := clean1 (typ v) (typ (v + 1)) ⟨π v, hπ v⟩ ⟨π (v + 1), hπ _⟩ (T.adj v)
        (ldr_cond T π v) (lc hc v) (by by_contra h; simp [cfgOf, h3 _ h] at hpeer) hv3 hrd
      simpa [cfgOf] using this

theorem returns_of_typing (T : Typing x typ) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) (hf : proc.Final (oriented n) c) (v : ZMod n) :
    proc.result (c.st v) = some (typ v).fans := by
  obtain ⟨π, hπ, rfl⟩ := reach_inv T hc
  have h3 := (final_spec T hπ hc hf).2 v
  simp [cfgOf, h3, Role.mk_pc, Role.mk_ans]

theorem totalSent_final_of_typing (T : Typing x typ) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) (hf : proc.Final (oriented n) c) :
    totalSent c = 3 * n := by
  obtain ⟨π, hπ, rfl⟩ := reach_inv T hc
  have h3 := (final_spec T hπ hc hf).2
  rw [totalSent_cfgOf]
  simp only [h3, sent_three, sum_const, card_univ, ZMod.card, smul_eq_mul, mul_comm]

theorem transit_le_one_of_typing (T : Typing x typ) {c : Config (ZMod n) St}
    (hc : proc.Reach (oriented n) x c) : totalSent c ≤ totalRecvd c + 1 := by
  obtain ⟨π, hπ, rfl⟩ := reach_inv T hc
  rw [totalSent_eq π hπ]
  obtain ⟨ℓ, hℓ⟩ := T.exL
  have : ∑ v, (if (typ v).ldr = true ∧ π v < 3 then 1 else 0) ≤ ∑ v, (if v = ℓ then 1 else 0) :=
    sum_le_sum fun v _ => by
      split_ifs with h1 h2 h2 <;> try omega
      exact absurd (T.uniqL _ _ h1.1 hℓ) h2
  simp only [sum_ite_eq', mem_univ, ite_true] at this
  omega

/-! ## The roles of the nodes -/

section typing

variable (x : ZMod n → Bool × Bool) (ℓ : ZMod n)

open Classical in
/-- The role of each node, given the inputs `x` and the leader `ℓ`. -/
noncomputable def typOf (v : ZMod n) : Role :=
  if h : ∃ k : ℕ, (x (ℓ - k)).2 = true then
    if (x ℓ).2 then (if v = ℓ then .L20 else if (x v).2 then .N1 else .N0)
    else if v = ℓ then .L19 else if (ℓ - v).val < Nat.find h then .A
      else if (ℓ - v).val = Nat.find h then .J else if (x v).2 then .B1 else .B0
  else if v = ℓ then .L18 else .N18

variable {x ℓ}

lemma exists_iff : (∃ k : ℕ, (x (ℓ - k)).2 = true) ↔ ∃ v, (x v).2 = true := by
  constructor
  · rintro ⟨k, hk⟩; exact ⟨_, hk⟩
  · rintro ⟨v, hv⟩; exact ⟨(ℓ - v).val, by simpa [ZMod.natCast_zmod_val] using hv⟩

/-- `(ℓ - v).val`, the counter-clockwise distance from `ℓ` to `v`, decreases by one along a
clockwise link. -/
lemma dist_succ (v : ZMod n) : (ℓ - v).val = ((ℓ - (v + 1)).val + (1 : ZMod n).val) % n := by
  rw [← ZMod.val_add]; congr 1; ring

lemma val_one_of_ne (h : ∃ u v : ZMod n, u ≠ v) : (1 : ZMod n).val = 1 := by
  rw [ZMod.val_one_eq_one_mod]
  apply Nat.mod_eq_of_lt
  obtain ⟨u, v, huv⟩ := h
  by_contra hn
  have : n = 1 := by have := NeZero.ne n; omega
  subst this
  exact huv (Subsingleton.elim _ _)

theorem typing (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) : Typing x (typOf x ℓ) := by
  have hldr : ∀ v, (x v).1 = decide (v = ℓ) := fun v => by
    by_cases h : v = ℓ
    · simp [h, hℓ]
    · simpa [h] using (hℓ v).not.2 h
  by_cases hex : ∃ k : ℕ, (x (ℓ - k)).2 = true
  · by_cases hb : (x ℓ).2 = true
    · -- Lemma 20
      have ht : ∀ v, typOf x ℓ v = if v = ℓ then .L20 else if (x v).2 then .N1 else .N0 := by
        intro v; simp [typOf, hex, hb]
      refine ⟨fun v => ?_, fun v => ?_, fun u v hu hv => ?_, fun u v hu hv => ?_, ⟨ℓ, ?_⟩⟩
      · rw [ht, ht]; split_ifs <;> rfl
      · rw [ht, Prod.ext_iff, hldr]
        split_ifs with h1 h2 <;> simp_all [Role.ldr, Role.b, Role.data]
      · rw [ht] at hu hv; split_ifs at hu hv with h1 h2 <;> simp_all [Role.ldr, Role.data]
      · rw [ht] at hu; split_ifs at hu
      · rw [ht]; simp [Role.ldr, Role.data]
    · -- Lemma 19
      simp only [Bool.not_eq_true] at hb
      set k0 := Nat.find hex with hk0def
      have hk0 : (x (ℓ - k0)).2 = true := Nat.find_spec hex
      have hmin : ∀ k < k0, (x (ℓ - k)).2 = false := fun k hk => by
        simpa using Nat.find_min hex hk
      have hk0pos : 0 < k0 := by
        rcases Nat.eq_zero_or_pos k0 with h | h
        · rw [h] at hk0; simp [hb] at hk0
        · exact h
      have hk0n : k0 < n := by
        by_contra hc
        have := hmin (k0 % n) (lt_of_lt_of_le (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n)))
          (not_lt.1 hc))
        rw [ZMod.natCast_mod] at this; rw [this] at hk0; cases hk0
      have hne : ∃ u v : ZMod n, u ≠ v := ⟨ℓ - k0, ℓ, fun h => by rw [h] at hk0; simp [hb] at hk0⟩
      have h1 := val_one_of_ne hne
      have ht : ∀ v, typOf x ℓ v = if v = ℓ then .L19 else if (ℓ - v).val < k0 then .A
          else if (ℓ - v).val = k0 then .J else if (x v).2 then .B1 else .B0 := by
        intro v; simp only [typOf, hex, hb, dite_true]; rfl
      have hv0 : ∀ v, (ℓ - v).val = 0 ↔ v = ℓ := fun v => by
        rw [ZMod.val_eq_zero, sub_eq_zero, eq_comm]
      have hxv : ∀ v, x (ℓ - ((ℓ - v).val : ℕ)) = x v := fun v => by
        rw [ZMod.natCast_zmod_val, sub_sub_cancel]
      refine ⟨fun v => ?_, fun v => ?_, fun u v hu hv => ?_, fun u v hu hv => ?_, ⟨ℓ, ?_⟩⟩
      · have hd := dist_succ (ℓ := ℓ) v
        rw [h1] at hd
        have hlt := ZMod.val_lt (ℓ - (v + 1))
        have hn2 : 2 ≤ n := by
          by_contra hc
          have : 1 % n = 0 := by
            have : n = 1 := by have := NeZero.ne n; omega
            subst this; rfl
          rw [ZMod.val_one_eq_one_mod] at h1; omega
        have key : ((ℓ - v).val = 0 ∧ (ℓ - (v + 1)).val = n - 1) ∨
            ((ℓ - v).val ≠ 0 ∧ (ℓ - (v + 1)).val = 0 ∧ (ℓ - v).val = 1) ∨
            ((ℓ - v).val ≠ 0 ∧ (ℓ - (v + 1)).val ≠ 0 ∧ (ℓ - v).val = (ℓ - (v + 1)).val + 1) := by
          by_cases hc : (ℓ - (v + 1)).val + 1 < n
          · rw [Nat.mod_eq_of_lt hc] at hd; omega
          · have : (ℓ - (v + 1)).val + 1 = n := by omega
            rw [this, Nat.mod_self] at hd; omega
        rw [ht, ht]
        simp only [← hv0 v, ← hv0 (v + 1)]
        split_ifs <;> first | rfl | omega
      · rw [ht, Prod.ext_iff, hldr]
        by_cases h0 : (ℓ - v).val = 0
        · have : v = ℓ := (hv0 v).1 h0
          subst this; simp [Role.ldr, Role.b, Role.data, hb]
        · have hvl : ¬ v = ℓ := fun h => h0 ((hv0 v).2 h)
          simp only [hvl, ite_false, decide_false]
          split_ifs with h2 h3 h4
          · have := hmin _ h2; rw [hxv] at this; simp [Role.ldr, Role.b, Role.data, this]
          · have e := hxv v; rw [h3] at e; rw [e] at hk0; simp [Role.ldr, Role.b, Role.data, hk0]
          · simp [Role.ldr, Role.b, Role.data, h4]
          · simp only [Bool.not_eq_true] at h4; simp [Role.ldr, Role.b, Role.data, h4]
      · rw [ht] at hu hv
        have hu' : u = ℓ := by
          by_contra hc; simp only [hc, ite_false] at hu
          split_ifs at hu <;> simp [Role.ldr, Role.data] at hu
        have hv' : v = ℓ := by
          by_contra hc; simp only [hc, ite_false] at hv
          split_ifs at hv <;> simp [Role.ldr, Role.data] at hv
        rw [hu', hv']
      · have hJ : ∀ w, typOf x ℓ w = Role.J → (ℓ - w).val = k0 := by
          intro w hw
          rw [ht] at hw
          split_ifs at hw with h2 h3 h4 h5; exact h4
        have := ZMod.val_injective n ((hJ u hu).trans (hJ v hv).symm)
        simpa using this
      · rw [ht]; simp [Role.ldr, Role.data]
  · -- Lemma 18
    have hall : ∀ v, (x v).2 = false := fun v => by
      by_contra h; exact hex ((exists_iff).2 ⟨v, by simpa using h⟩)
    have ht : ∀ v, typOf x ℓ v = if v = ℓ then .L18 else .N18 := by
      intro v; simp [typOf, hex]
    refine ⟨fun v => ?_, fun v => ?_, fun u v hu hv => ?_, fun u v hu hv => ?_, ⟨ℓ, ?_⟩⟩
    · rw [ht, ht]; split_ifs <;> rfl
    · rw [ht, Prod.ext_iff, hldr, hall]
      split_ifs with h1 <;> simp_all [Role.ldr, Role.b, Role.data]
    · rw [ht] at hu hv; split_ifs at hu hv with h1 h2 <;> simp_all [Role.ldr, Role.data]
    · rw [ht] at hu; split_ifs at hu
    · rw [ht]; simp [Role.ldr, Role.data]


lemma fans_typOf (v : ZMod n) :
    (typOf x ℓ v).fans = decide (∃ v, (x v).2 = true) := by
  by_cases hex : ∃ k : ℕ, (x (ℓ - k)).2 = true
  · have h' : ∃ v, (x v).2 = true := exists_iff.1 hex
    simp only [typOf, hex, dite_true, h', decide_true]
    split_ifs <;> rfl
  · have h' : ¬ ∃ v, (x v).2 = true := fun h => hex (exists_iff.2 h)
    simp only [typOf, hex, dite_false, h', decide_false]
    split_ifs <;> rfl

end typing

/-! ## Theorem 21 and Lemmas 18–20 -/

variable {ℓ : ZMod n}

/-- **Theorem 21** (composable ending): on the oriented ring with exactly one leader `ℓ`, for any
input bits, `ComputeOR` is composable: every execution sends a bounded number of pulses, every
final configuration is quiescent with all nodes returned, and no node still in `ComputeOR` can
read a pulse of a neighbour that has already returned. -/
theorem composable (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) : proc.Composable (oriented n) x :=
  composable_of_typing (typing hℓ)

/-- **Theorem 21** (correctness): every node returns the OR of all input bits. -/
theorem returns (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) :
    proc.Returns (oriented n) x (fun _ => decide (∃ v, (x v).2 = true)) := fun c hc hf v => by
  rw [returns_of_typing (typing hℓ) hc hf v, fans_typOf v]

/-- **Theorem 21** (message complexity): no execution sends more than `3n` pulses … -/
theorem totalSent_le (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) {c : Config (ZMod n) proc.State}
    (hc : proc.Reach (oriented n) x c) : totalSent c ≤ 3 * n := by
  obtain ⟨π, hπ, rfl⟩ := reach_inv (typing hℓ) hc
  exact totalSent_le' π hπ

/-- **Theorem 21** (message complexity): … and every complete execution sends exactly `3n`
pulses. -/
theorem totalSent_final (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) {c : Config (ZMod n) proc.State}
    (hc : proc.Reach (oriented n) x c) (hf : proc.Final (oriented n) c) : totalSent c = 3 * n :=
  totalSent_final_of_typing (typing hℓ) hc hf

/-- "At each instant of the execution of `ComputeOR` at most one pulse is present in the
network" (remark before Lemma 18). -/
theorem totalSent_le_totalRecvd_add_one (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ)
    {c : Config (ZMod n) proc.State} (hc : proc.Reach (oriented n) x c) :
    totalSent c ≤ totalRecvd c + 1 :=
  transit_le_one_of_typing (typing hℓ) hc

/-- **Lemma 18**: if all inputs are `false`, every node returns `false`. -/
theorem lemma18 (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hb : ∀ v, (x v).2 = false) :
    proc.Returns (oriented n) x (fun _ => false) := by
  have := returns hℓ
  simpa [hb] using this

/-- **Lemma 19**: if the leader's input is `false` and some node has input `true`, every node
returns `true`. -/
theorem lemma19 (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (_hl : (x ℓ).2 = false)
    (hb : ∃ v, (x v).2 = true) : proc.Returns (oriented n) x (fun _ => true) := by
  have := returns hℓ
  simpa [hb] using this

/-- **Lemma 20**: if the leader's input is `true`, every node returns `true`. -/
theorem lemma20 (hℓ : ∀ v, (x v).1 = true ↔ v = ℓ) (hl : (x ℓ).2 = true) :
    proc.Returns (oriented n) x (fun _ => true) := by
  have := returns hℓ
  simpa [show ∃ v, (x v).2 = true from ⟨ℓ, hl⟩] using this

end Podc.ContentOblivious.ComputeOR
