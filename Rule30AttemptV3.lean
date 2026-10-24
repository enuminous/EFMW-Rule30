import Ruliology.CellularAutomata.Rule30Realization
import Ruliology.CellularAutomata.Rule30Prize
import Rule30SearchV2

/-! Exact local residual lemmas and a conditional bridge. No prize solution. -/
namespace Rule30AttemptV3
open Ruliology.CellularAutomata Rule30Jen Rule30Realization

def delta (x : Int → Bool) (p t : Nat) (i : Int) : Bool :=
  xor (evol x (t+p) i) (evol x t i)

theorem xor_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> decide

theorem local_difference (a b c da db dc : Bool) :
    xor (rule (xor a da) (xor b db) (xor c dc)) (rule a b c) =
      xor da (xor ((!c) && db) (xor ((!b) && dc) (db && dc))) := by
  cases a <;> cases b <;> cases c <;> cases da <;> cases db <;> cases dc <;> decide

theorem masked_difference (a b c a' c' : Bool) :
    xor (rule a' b c') (rule a b c) =
      xor (xor a' a) ((!b) && xor c' c) := by
  cases a <;> cases b <;> cases c <;> cases a' <;> cases c' <;> decide

theorem residual_step_when_center_matches (x : Int → Bool) (p t : Nat) (i : Int)
    (h : evol x (t+p) i = evol x t i) :
    delta x p (t+1) i =
      xor (delta x p t (i-1)) ((!evol x t i) && delta x p t (i+1)) := by
  unfold delta
  rw [show t + 1 + p = (t+p)+1 by omega]
  simp only [evol]
  rw [h]
  exact masked_difference _ _ _ _ _

theorem residual_balance (x : Int → Bool) (p t : Nat) (i : Int)
    (h : evol x (t+p) i = evol x t i)
    (hs : evol x (t+1+p) i = evol x (t+1) i) :
    delta x p t (i-1) = ((!evol x t i) && delta x p t (i+1)) := by
  have hz : delta x p (t+1) i = false := by
    unfold delta
    exact (xor_false_iff _ _).2 hs
  rw [residual_step_when_center_matches x p t i h] at hz
  exact (xor_false_iff _ _).1 hz

/-- Black center masks an arbitrary change on its right. -/
theorem masking_counterexample :
    rule false true false = rule false true true ∧
    xor false true = true := by decide

/-- Every positive lag has a global residual at the expanding left edge. -/
theorem seed_residual_edge (p t : Nat) (hp : 0 < p) :
    delta seed p t (-((t+p:Nat):Int)) = true := by
  unfold delta
  rw [evol_seed, evol_seed, cell_left_edge,
    cell_eq_false_of_lt t _ (by omega)]
  rfl

/-- Count nonzero k-bit windows, including all zero-padded boundary windows. -/
def blockCount (row span k pattern : Nat) : Nat :=
  if pattern = 0 then 0 else
  ((List.range (span+k-1)).filter (fun j =>
    (((row <<< (k-1)) >>> j) % 2^k) == pattern)).length

/-- A genuine finite Rule 30 row: black cells at -1, 0, 2, 3. -/
def rankWitness : Int → Bool := Rule30SearchV2.unpack 108 3

theorem rank_witness_alternates :
    evol rankWitness 0 0 = true ∧ evol rankWitness 1 0 = false ∧
    evol rankWitness 2 0 = true := by decide +kernel

theorem rank_witness_after_two (i : Int) :
    evol rankWitness 2 i = Rule30SearchV2.unpack 1772 5 i := by
  exact (Rule30SearchV2.rows_exact 108 3 2 i).symm

/-- All nonzero block counts of lengths 1..6 weakly increase on this transition.
Length zero is included only as a harmless finite-index implementation case. -/
theorem rank_witness_counts : ∀ k : Fin 7, ∀ p : Fin 64,
    blockCount 108 7 k.val p.val ≤ blockCount 1772 11 k.val p.val := by
  decide +kernel

def score (n : Nat) (counts weights : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | m+1 => score m counts weights + counts m * weights m

theorem score_mono (a b weights : Nat → Nat) : ∀ n,
    (∀ j, j < n → a j ≤ b j) → score n a weights ≤ score n b weights
  | 0,_ => by simp [score]
  | n+1,h => by
    simp only [score]
    exact Nat.add_le_add (score_mono a b weights n (fun j hj => h j (by omega)))
      (Nat.mul_le_mul_right (weights n) (h n (by omega)))

/-- No nonnegative integer weighting of blocks of a fixed length ≤6 can
strictly decrease on every center-alternating double step: this row defeats it. -/
theorem no_block_score_descent (k : Fin 7) (weights : Nat → Nat) :
    ¬ score 64 (blockCount 1772 11 k.val) weights <
      score 64 (blockCount 108 7 k.val) weights := by
  apply Nat.not_lt_of_ge
  apply score_mono
  intro j hj
  exact rank_witness_counts k ⟨j,hj⟩

def Supported (R : Nat) (x : Int → Bool) : Prop :=
  ∀ i, i < -(R:Int) ∨ (R:Int) < i → x i = false

def AlternatesThrough (x : Int → Bool) (H : Nat) : Prop :=
  ∀ t, t ≤ H → evol x t 0 = decide (t%2=0)

/-- OPEN: this linear bound is tested, not assumed or proved. -/
def LinearEscape : Prop :=
  ∀ R x, Supported R x → ∃ t, t ≤ 2*R+2 ∧
    evol x t 0 ≠ decide (t%2=0)

/-- OPEN: the weaker all-support escape claim. -/
def UniformEscape : Prop :=
  ∀ R x, Supported R x → ∃ t, evol x t 0 ≠ decide (t%2=0)

theorem uniform_of_linear (h : LinearEscape) : UniformEscape := by
  intro R x hx
  obtain ⟨t,_,ht⟩ := h R x hx
  exact ⟨t,ht⟩

theorem cell_right_zero : ∀ (t : Nat) (i : Int), (t:Int) < i → cell t i = false
  | 0,i,h => by simp [cell]; omega
  | t+1,i,h => by
    show rule (cell t (i-1)) (cell t i) (cell t (i+1)) = false
    rw [cell_right_zero t (i-1) (by omega), cell_right_zero t i (by omega),
      cell_right_zero t (i+1) (by omega)]
    rfl

theorem seed_supported (T : Nat) : Supported T (cell T) := by
  intro i hi
  cases hi with
  | inl h => exact cell_eq_false_of_lt T i h
  | inr h => exact cell_right_zero T i h

theorem restart (T : Nat) : ∀ t i, evol (cell T) t i = cell (T+t) i
  | 0,i => by simp [evol]
  | t+1,i => by
    show rule (evol (cell T) t (i-1)) (evol (cell T) t i) (evol (cell T) t (i+1)) = _
    rw [restart T t (i-1), restart T t i, restart T t (i+1),
      show T+(t+1)=(T+t)+1 by omega]
    rfl

theorem no_black_first_alternating_tail_of_uniform (h : UniformEscape) :
    ¬ ∃ T, ∀ t, cell (T+t) 0 = decide (t%2=0) := by
  rintro ⟨T,hT⟩
  obtain ⟨t,ht⟩ := h T (cell T) (seed_supported T)
  rw [restart] at ht
  exact ht (hT t)

/-- Exposing the gap: compiling this implication does not prove its premise. -/
theorem no_black_first_alternating_tail_of_linear (h : LinearEscape) :
    ¬ ∃ T, ∀ t, cell (T+t) 0 = decide (t%2=0) :=
  no_black_first_alternating_tail_of_uniform (uniform_of_linear h)

end Rule30AttemptV3
