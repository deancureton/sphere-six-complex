module

public import SphereSixComplex.LatticeData
public import Mathlib.Data.ZMod.Basic

/-!
# The integer twist obstruction

The obstruction integer from Section 7 and its value for the chosen twist vectors.
-/

namespace SphereSixComplex.Topology.TwistObstruction

open LatticeData

@[expose] public def v₁ : LatticeData.Lattice := epsilon

@[expose] public def v₂ : LatticeData.Lattice := -epsilon'

public def ell₀ : ℤ := 0

public def ell₁ : ℤ := gamma v₁

public def ell₂ : ℤ := gamma v₂

public theorem chosen_twist_values : (ell₀, ell₁, ell₂) = (0, 1, -1) := by
  simp [ell₀, ell₁, ell₂, v₁, v₂, gamma_epsilon, gamma_neg_epsilon']

public def obstruction (l₀ l₁ l₂ : ℤ) : ℤ := 12 * l₀ - 4 * l₁ - 3 * l₂

public def p : ℤ := obstruction ell₀ ell₁ ell₂

public theorem p_eq_neg_one : p = -1 := by
  simp [p, obstruction, ell₀, ell₁, ell₂, v₁, v₂, gamma_epsilon,
    gamma_neg_epsilon']

public theorem abs_p : |p| = 1 := by
  rw [p_eq_neg_one]
  norm_num

public theorem natAbs_p : p.natAbs = 1 := by
  rw [p_eq_neg_one]
  norm_num

public abbrev ObstructionGroup := ZMod p.natAbs

public instance instSubsingletonObstructionGroup : Subsingleton ObstructionGroup := by
  change Subsingleton (ZMod p.natAbs)
  rw [natAbs_p]
  infer_instance

public theorem obstruction_group_eq_zero (x : ObstructionGroup) : x = 0 :=
  Subsingleton.elim _ _

public theorem obstruction_group_card : Nat.card ObstructionGroup = 1 := by
  change Nat.card (ZMod p.natAbs) = 1
  rw [natAbs_p]
  simp

end SphereSixComplex.Topology.TwistObstruction
