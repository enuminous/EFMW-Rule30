import Ruliology.CellularAutomata.Rule30Realization
import Ruliology.CellularAutomata.Rule30Prize

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Rule30SearchV2
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

def unpack (r K : Nat) (p : Int) : Bool :=
  if p + (K : Int) < 0 then false else r.testBit (p + K).toNat

def grow (r : Nat) : Nat := (r <<< 2) ^^^ ((r <<< 1) ||| r)

theorem unpack_grow (r K : Nat) (p : Int) :
    unpack (grow r) (K+1) p =
      rule (unpack r K (p-1)) (unpack r K p) (unpack r K (p+1)) := by
  by_cases hn : p + (K : Int) < -1
  · simp [unpack, show p + ((K:Int)+1) < 0 by omega,
      show p-1+(K:Int)<0 by omega, show p+(K:Int)<0 by omega,
      show p+1+(K:Int)<0 by omega, rule]
  · by_cases h0 : p + (K : Int) = -1
    · have hn0 : (p + ((K:Int)+1)).toNat = 0 := by omega
      have hn1 : (p + 1 + (K:Int)).toNat = 0 := by omega
      simp [unpack, show ¬ p+((K:Int)+1)<0 by omega,
        show p-1+(K:Int)<0 by omega, show p+(K:Int)<0 by omega,
        show ¬p+1+(K:Int)<0 by omega, hn0, hn1, grow, rule,
        Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
    · by_cases h1 : p + (K : Int) = 0
      · have hn0 : (p + ((K:Int)+1)).toNat = 1 := by omega
        have hn1 : (p + (K:Int)).toNat = 0 := by omega
        have hn2 : (p + 1 + (K:Int)).toNat = 1 := by omega
        simp [unpack, show ¬ p+((K:Int)+1)<0 by omega,
          show p-1+(K:Int)<0 by omega, show ¬p+(K:Int)<0 by omega,
          show ¬p+1+(K:Int)<0 by omega, hn0, hn1, hn2, grow, rule,
          Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft]
      · have hp : 1 ≤ p + (K:Int) := by omega
        have e1 : (p+1+(K:Int)).toNat - 2 = (p-1+(K:Int)).toNat := by omega
        have e2 : (p+1+(K:Int)).toNat - 1 = (p+(K:Int)).toNat := by omega
        have e3 : (p+((K:Int)+1)).toNat = (p+1+(K:Int)).toNat := by omega
        simp [unpack, show ¬p+((K:Int)+1)<0 by omega,
          show ¬p-1+(K:Int)<0 by omega, show ¬p+(K:Int)<0 by omega,
          show ¬p+1+(K:Int)<0 by omega, grow, rule,
          Nat.testBit_xor, Nat.testBit_or, Nat.testBit_shiftLeft,
          show (p+1+(K:Int)).toNat ≥ 2 by omega,
          show (p+1+(K:Int)).toNat ≥ 1 by omega, e1,e2,e3]

def rows (r : Nat) : Nat → Nat
  | 0 => r
  | t+1 => grow (rows r t)

theorem rows_exact (r K : Nat) : ∀ t p,
    unpack (rows r t) (K+t) p = evol (unpack r K) t p
  | 0,p => by simp [rows,evol]
  | t+1,p => by
    rw [rows, show K+(t+1)=(K+t)+1 by omega, unpack_grow,
      rows_exact r K t (p-1), rows_exact r K t p, rows_exact r K t (p+1)]
    rfl

def breaks (K : Nat) : Nat → Nat → Nat → Bool
  | 0,_,_ => false
  | h+1,t,r => if r.testBit (K+t) != decide (t%2=0) then true
               else breaks K h (t+1) (grow r)

theorem breaks_sound (K r : Nat) : ∀ h t,
    breaks K h t (rows r t) = true →
    ∃ s, t ≤ s ∧ s < t+h ∧ evol (unpack r K) s 0 ≠ decide (s%2=0) := by
  intro h
  induction h with
  | zero => intro t h; simp [breaks] at h
  | succ h ih =>
    intro t hb
    simp only [breaks] at hb
    split at hb
    · rename_i hn
      refine ⟨t, by omega, by omega, ?_⟩
      have exact := rows_exact r K t 0
      change (if (0:Int) + ((K+t:Nat):Int) < 0 then false else
        (rows r t).testBit ((0:Int) + ((K+t:Nat):Int)).toNat) = _ at exact
      rw [ite_eq_right (by omega), Int.zero_add, Int.toNat_natCast] at exact
      rw [←exact]
      simpa using hn
    · have hrec : breaks K h (t+1) (rows r (t+1)) = true := hb
      obtain ⟨s,hs,hs',hne⟩ := ih (t+1) hrec
      exact ⟨s,by omega,by omega,hne⟩

def allBreak (R H : Nat) : Bool :=
  (List.range (2^(2*R+1))).all (fun r => breaks R (H+1) 0 r)

theorem allBreak_sound (R H : Nat) (ok : allBreak R H = true)
    (r : Nat) (hr : r < 2^(2*R+1)) :
    ∃ t, t ≤ H ∧ evol (unpack r R) t 0 ≠ decide (t%2=0) := by
  have hb := List.all_eq_true.1 ok r (List.mem_range.2 hr)
  have hb' : breaks R (H+1) 0 (rows r 0) = true := hb
  obtain ⟨t,_,ht,hne⟩ := breaks_sound R r (H+1) 0 hb'
  exact ⟨t,by omega,hne⟩

/-- Exact seed reachability: a left support bound bounds the onset time. -/
theorem support_bounds_onset (T R : Nat)
    (bounded : ∀ p : Int, p < -(R:Int) → cell T p = false) : T ≤ R := by
  apply Classical.byContradiction
  intro h
  have he := cell_left_edge T
  have hz := bounded (-(T:Int)) (by omega)
  rw [hz] at he
  contradiction

theorem center_rows (r K t : Nat) :
    (rows r t).testBit (K+t) = evol (unpack r K) t 0 := by
  have h := rows_exact r K t 0
  change (if (0:Int) + ((K+t:Nat):Int) < 0 then false else
    (rows r t).testBit ((0:Int) + ((K+t:Nat):Int)).toNat) = _ at h
  rw [ite_eq_right (by omega), Int.zero_add, Int.toNat_natCast] at h
  exact h

theorem breaks_false_sound (K r : Nat) : ∀ h t,
    breaks K h t (rows r t) = false →
    ∀ s, t ≤ s → s < t+h → evol (unpack r K) s 0 = decide (s%2=0) := by
  intro h
  induction h with
  | zero => intro t hb s hs hs'; omega
  | succ h ih =>
    intro t hb s hs hs'
    simp only [breaks] at hb
    split at hb
    · contradiction
    · rename_i hn
      by_cases he : s = t
      · subst s
        rw [←center_rows]
        simpa using hn
      · have hrec : breaks K h (t+1) (rows r (t+1)) = false := hb
        exact ih (t+1) hrec s (by omega) (by omega)

def Supported (R : Nat) (x : Int → Bool) : Prop :=
  ∀ p, p < -(R:Int) ∨ (R:Int) < p → x p = false

theorem cell_right_zero : ∀ (t : Nat) (p : Int), (t:Int) < p → cell t p = false
  | 0,p,h => by simp [cell]; omega
  | t+1,p,h => by
    show rule (cell t (p-1)) (cell t p) (cell t (p+1)) = false
    rw [cell_right_zero t (p-1) (by omega), cell_right_zero t p (by omega),
      cell_right_zero t (p+1) (by omega)]
    rfl

theorem seed_row_supported (T : Nat) : Supported T (cell T) := by
  intro p hp
  cases hp with
  | inl h => exact cell_eq_false_of_lt T p h
  | inr h => exact cell_right_zero T p h

theorem restart (T : Nat) : ∀ t p, evol (cell T) t p = cell (T+t) p
  | 0,p => by simp [evol]
  | t+1,p => by
    show rule (evol (cell T) t (p-1)) (evol (cell T) t p) (evol (cell T) t (p+1)) = _
    rw [restart T t (p-1), restart T t p, restart T t (p+1)]
    rw [show T+(t+1)=(T+t)+1 by omega]
    rfl

/-- OPEN. Finite checks at selected radii do not prove this proposition. -/
def UniformFiniteAlternationEscape : Prop :=
  ∀ R x, Supported R x → ∃ t, evol x t 0 ≠ decide (t%2=0)

/-- A conditional bridge, not a proof of its open premise. -/
theorem no_alternating_tail_of_uniform_escape (h : UniformFiniteAlternationEscape) :
    ¬ ∃ T, ∀ t, cell (T+t) 0 = decide (t%2=0) := by
  rintro ⟨T,hT⟩
  obtain ⟨t,hne⟩ := h T (cell T) (seed_row_supported T)
  rw [restart] at hne
  exact hne (hT t)

theorem finite_radius_0 (r : Nat) (hr : r < 2^(2*0+1)) :
    ∃ t, t ≤ 1 ∧ evol (unpack r 0) t 0 ≠ decide (t%2=0) :=
  allBreak_sound 0 1 (by decide +kernel) r hr

theorem finite_radius_1 (r : Nat) (hr : r < 2^(2*1+1)) :
    ∃ t, t ≤ 3 ∧ evol (unpack r 1) t 0 ≠ decide (t%2=0) :=
  allBreak_sound 1 3 (by decide +kernel) r hr

theorem finite_radius_2 (r : Nat) (hr : r < 2^(2*2+1)) :
    ∃ t, t ≤ 6 ∧ evol (unpack r 2) t 0 ≠ decide (t%2=0) :=
  allBreak_sound 2 6 (by decide +kernel) r hr

theorem finite_radius_3 (r : Nat) (hr : r < 2^(2*3+1)) :
    ∃ t, t ≤ 6 ∧ evol (unpack r 3) t 0 ≠ decide (t%2=0) :=
  allBreak_sound 3 6 (by decide +kernel) r hr

theorem finite_radius_4 (r : Nat) (hr : r < 2^(2*4+1)) :
    ∃ t, t ≤ 6 ∧ evol (unpack r 4) t 0 ≠ decide (t%2=0) :=
  allBreak_sound 4 6 (by decide +kernel) r hr

theorem finite_radius_5 (r : Nat) (hr : r < 2^(2*5+1)) :
    ∃ t, t ≤ 7 ∧ evol (unpack r 5) t 0 ≠ decide (t%2=0) :=
  allBreak_sound 5 7 (by decide +kernel) r hr

theorem finite_radius_6 (r : Nat) (hr : r < 2^(2*6+1)) :
    ∃ t, t ≤ 8 ∧ evol (unpack r 6) t 0 ≠ decide (t%2=0) :=
  allBreak_sound 6 8 (by decide +kernel) r hr

theorem refuted_bound_at_radius_5 :
    ∀ t, t ≤ 6 → evol (unpack 245 5) t 0 = decide (t%2=0) := by
  intro t ht
  exact breaks_false_sound 5 245 7 0 (by decide +kernel) t (by omega) (by omega)

theorem refuted_bound_at_radius_9 :
    ∀ t, t ≤ 13 → evol (unpack 15195 9) t 0 = decide (t%2=0) := by
  intro t ht
  exact breaks_false_sound 9 15195 14 0 (by decide +kernel) t (by omega) (by omega)


end Rule30SearchV2
