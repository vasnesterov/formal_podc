import Papers.PODC2026.RankingOpinions.TieShare

/-!
# Circles_TieSharing: one interaction, as a finite function

Lemmas about the status update `stUpd` of `Circles_TieSharing` (sequential reading), checked by
`decide` over all values of the finitely many relevant facts (`PR`) and statuses.

`upd o r sx sy` is the pair (new status of `x`, new status of `y`) when `x` interacts with `y`,
as initiator (`o = true`) or responder (`o = false`); `r` describes the two agents from the point
of view of `x` (`a = x`, `b = y`).
-/

namespace RankingOpinions

/-- The new statuses of `x` and of its partner `y` (`o`: is `x` the initiator?). -/
def upd (o : Bool) (r : PR) (sx sy : St) : St × St :=
  if o then stUpd false r sx sy else ((stUpd false r.swap sy sx).2, (stUpd false r.swap sy sx).1)

/-- The facts used when no exchange takes place (`pa = da`, `pb = db`). -/
def nx (da db sb kab kba sab sba qab qba : Bool) : PR :=
  ⟨false, da, db, da, db, sb, kab, kba, sab, sba, qab, qba⟩

/-- A diagonal agent at `winner` stays at `winner`; an agent becoming diagonal is at `winner`. -/
lemma upd_diag : ∀ (o ex pa pb da db sb kab kba sab sba qab qba : Bool) (sx sy : St),
    da = true → (pa = true → sx = St.win) → (pa = true → ex = false) →
    qba = false → (db = true → sb = false → qab = false) →
    (upd o ⟨ex, pa, pb, da, db, sb, kab, kba, sab, sba, qab, qba⟩ sx sy).1 = St.win := by
  decide +kernel

/-- A non-diagonal agent meeting a diagonal agent at `winner` (no exchange). -/
lemma upd_meet_diag : ∀ (o sb kab kba sab sba qab qba : Bool) (sx : St),
    (upd o (nx false true sb kab kba sab sba qab qba) sx St.win).1 =
      (if sb then St.win else St.los) ∧
    (upd o (nx false true sb kab kba sab sba qab qba) sx St.win).2 = St.win := by
  decide +kernel

/-- Without tokens, only rule (3) acts. -/
lemma upd_noTok : ∀ (o da db sb kab kba sab sba qab qba : Bool) (sx sy : St),
    sx ≠ St.ws → sy ≠ St.ws →
    (upd o (nx da db sb kab kba sab sba qab qba) sx sy).1 =
      (if db then (if sb then St.win else if !da then St.los else sx) else sx) ∧
    (upd o (nx da db sb kab kba sab sba qab qba) sx sy).1 ≠ St.ws := by
  decide +kernel

/-- How an agent gains a token (no exchange): its partner had one, and either rule (4) or rule (5)
applied. -/
lemma upd_gain : ∀ (o da db sb kab kba sab sba qab qba : Bool) (sx sy : St),
    sx ≠ St.ws → (db = true → sy ≠ St.ws) →
    (upd o (nx da db sb kab kba sab sba qab qba) sx sy).1 = St.ws →
    sy = St.ws ∧ ((kba = true ∧ sx = St.los) ∨ qba = true) := by
  decide +kernel

lemma PR.swap_swap (r : PR) : r.swap.swap = r := by cases r; rfl

/-- The same interaction seen from the partner. -/
lemma upd_swap (o : Bool) (r : PR) (sx sy : St) :
    upd (!o) r.swap sy sx = ((upd o r sx sy).2, (upd o r sx sy).1) := by
  cases o <;> simp [upd, PR.swap_swap]

/-- An agent whose bra is a majority color and which is not a loser stays so (F1). -/
lemma upd_keep_nonLos : ∀ (o db sb kab kba sab sba qab qba : Bool) (sx sy : St),
    sx ≠ St.los → (sab = true → sb = true) → (qab = true → sb = true) → (db = true → sb = true) →
    (upd o (nx false db sb kab kba sab sba qab qba) sx sy).1 ≠ St.los := by
  decide +kernel

/-- A token survives, or its partner (with a larger range) holds one. -/
lemma upd_tok_survive : ∀ (o sb kab kba sab sba qab qba : Bool) (sy : St),
    (sb = true → sab = true ∨ qba = true) → (qab = true → sab = true) →
    (upd o (nx false false sb kab kba sab sba qab qba) St.ws sy).1 = St.ws ∨
      ((upd o (nx false false sb kab kba sab sba qab qba) St.ws sy).2 = St.ws ∧ sab = true) := by
  decide +kernel

/-- The witness invariant: an agent with a given bra at `winner_spreader`/`loser` (or exchanging)
keeps this property, or passes it to a partner with the same bra. -/
lemma upd_witness : ∀ (o ex pa pb db sb kab kba sab sba qab qba : Bool) (sx sy : St),
    (db = true → sb = false) → (ex = true ∨ sx = St.ws ∨ sx = St.los) →
    let p := upd o ⟨ex, pa, pb, false, db, sb, kab, kba, sab, sba, qab, qba⟩ sx sy
    (p.1 = St.ws ∨ p.1 = St.los) ∨ (sb = true ∧ (p.2 = St.ws ∨ p.2 = St.los)) := by
  decide +kernel

/-- A loser that stops being a loser: a token appears on it or on a partner with the same bra. -/
lemma upd_los_leave : ∀ (o sb kab kba sab sba qab qba : Bool) (sy : St),
    (upd o (nx false false sb kab kba sab sba qab qba) St.los sy).1 ≠ St.los →
    (upd o (nx false false sb kab kba sab sba qab qba) St.los sy).1 = St.ws ∨
      ((upd o (nx false false sb kab kba sab sba qab qba) St.los sy).2 = St.ws ∧ sb = true) := by
  decide +kernel

/-- Meeting an agent with a strictly larger range, which is not a candidate for rules (4), (5)
towards us, removes our token. -/
lemma upd_kill : ∀ (o sb kab sab sba : Bool) (sx sy : St),
    (upd o (nx false false sb kab false sab sba true false) sx sy).1 ≠ St.ws := by
  decide +kernel

/-- An agent with the same bra as a token holder with a larger range becomes/stays a winner. -/
lemma upd_win_same : ∀ (o kab kba sba qab : Bool) (sx : St),
    (upd o (nx false false true kab kba true sba qab false) sx St.ws).1 ≠ St.los := by
  decide +kernel

/-- An agent without token, strictly inside a token holder with a different bra, becomes a
loser, and the token holder keeps its token. -/
lemma upd_lose_inside : ∀ (o kab sba : Bool) (sx : St), sx ≠ St.ws →
    (upd o (nx false false false kab false true sba true false) sx St.ws).1 = St.los ∧
    (upd o (nx false false false kab false true sba true false) sx St.ws).2 = St.ws := by
  decide +kernel

/-- A loser stays a loser if its partner, when holding a token, cannot act on it by rules (4),
(5), (7, first case). -/
lemma upd_keep_los : ∀ (o sb kab kba sab sba qab qba : Bool) (sy : St),
    (sy = St.ws → kba = false ∧ qba = false ∧ sb = false) →
    (upd o (nx false false sb kab kba sab sba qab qba) St.los sy).1 = St.los := by
  decide +kernel

/-- Token multiplication towards a loser in another sector. -/
lemma upd_mult : ∀ (o kab : Bool),
    (upd o (nx false false false kab true false false false false) St.los St.ws).1 = St.ws := by
  decide +kernel

/-- An exchange (between agents that are not diagonal afterwards) creates a token. -/
lemma upd_exch : ∀ (o pa pb sb kab kba sab sba qab qba : Bool) (sx sy : St),
    (upd o ⟨true, pa, pb, false, false, sb, kab, kba, sab, sba, qab, qba⟩ sx sy).1 = St.ws ∨
    (upd o ⟨true, pa, pb, false, false, sb, kab, kba, sab, sba, qab, qba⟩ sx sy).2 = St.ws := by
  decide +kernel

end RankingOpinions
