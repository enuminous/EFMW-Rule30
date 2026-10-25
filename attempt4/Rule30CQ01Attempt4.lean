import Ruliology.CellularAutomata.Rule30PeriodTwoSideways

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace Rule30CQ01Attempt4
open Ruliology.CellularAutomata
open Rule30Jen Rule30ZeroBoundary Rule30PeriodTwoCoupled Rule30PeriodTwoSideways
open Rule30Ether (drv drv_col0 drv_init)

/-- Exact transport of the reconstructed row. This does not prove infinite support. -/
theorem psi_two_step (R : Nat → Bool) : zrow (Psi R) 2 = Psi (R2 R) := by
  simpa only [Psi, u_R2] using (two_step_shift (fun s => !u R s))

def advanceRight (R : Nat → Bool) : Nat → (Nat → Bool)
  | 0 => R
  | n + 1 => R2 (advanceRight R n)

/-- The exact coupling at every even time, with no finite-support assumption. -/
theorem psi_even_time (R : Nat → Bool) : ∀ n,
    zrow (Psi R) (2 * n) = Psi (advanceRight R n)
  | 0 => by
    change zrow (Psi R) 0 = Psi R
    exact zrow_zero_self (Theta_wall _)
  | n + 1 => by
    funext k
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, zrow_shift,
      psi_even_time R n, psi_two_step]
    rfl

/-- Integer bit p represents right-half site p+1; b is the center boundary. -/
def rightStep (b : Bool) (r : Nat) : Nat :=
  ((r <<< 1) ||| b.toNat) ^^^ (r ||| (r >>> 1))

theorem rightStep_zero (b : Bool) (r : Nat) :
    (rightStep b r).testBit 0 = rule b (r.testBit 0) (r.testBit 1) := by
  simp only [rightStep, rule, Nat.testBit_xor, Nat.testBit_or,
    Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_bool_toNat]
  rfl

theorem rightStep_succ (b : Bool) (r p : Nat) :
    (rightStep b r).testBit (p + 1) =
      rule (r.testBit p) (r.testBit (p + 1)) (r.testBit (p + 2)) := by
  simp [rightStep, rule, Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_bool_toNat, Nat.add_left_comm]

def rightRows : Nat → Nat
  | 0 => 0
  | t + 1 => rightStep (altCol t) (rightRows t)

/-- Efficient integer evolution agrees with the official driven right half. -/
theorem rightRows_exact : ∀ t p,
    (rightRows t).testBit p = drv altCol empty t (p + 1)
  | 0, p => by simp [rightRows, drv_init, empty]
  | t + 1, 0 => by
    rw [rightRows, rightStep_zero, rightRows_exact t 0, rightRows_exact t 1]
    change rule (altCol t) (drv altCol empty t 1) (drv altCol empty t 2) = _
    rw [drv, drv_col0]
  | t + 1, p + 1 => by
    rw [rightRows, rightStep_succ, rightRows_exact t p,
      rightRows_exact t (p + 1), rightRows_exact t (p + 2)]
    rfl

theorem u_by_integer (s : Nat) : u empty s = (rightRows (2 * s + 1)).testBit 0 :=
  (rightRows_exact (2 * s + 1) 0).symm

/-- No signal outruns the rightward light-cone boundary from the empty right half. -/
theorem empty_right_beyond : ∀ t p, t < p → drv altCol empty t p = false
  | 0, p, hp => by rw [drv_init _ _ _ (by omega)]; rfl
  | t + 1, p, hp => by
    obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    rw [drv, empty_right_beyond t k (by omega),
      empty_right_beyond t (k + 1) (by omega),
      empty_right_beyond t (k + 2) (by omega)]
    rfl

/-- The leading black cell moves right at every step. Restarting is not support descent. -/
theorem empty_right_front : ∀ t, drv altCol empty (t + 1) (t + 1) = true
  | 0 => by decide +kernel
  | t + 1 => by
    rw [drv, empty_right_front t,
      empty_right_beyond (t + 1) (t + 2) (by omega),
      empty_right_beyond (t + 1) (t + 3) (by omega)]
    rfl

/-- A concrete failure of the apparent seven-sample period in the initial trace. -/
theorem period_seven_counterexample : u empty 146 ≠ u empty 153 := by
  rw [u_by_integer, u_by_integer]
  decide +kernel

/-- The visually persuasive period-seven tail starting at sample 1 is false. -/
theorem not_period_seven_from_one : ¬ ∀ s, 1 ≤ s → u empty (s + 7) = u empty s := by
  intro h
  exact period_seven_counterexample (h 146 (by omega)).symm

-- CQ01Empty remains unproved. No theorem of that type is declared here.

end Rule30CQ01Attempt4
