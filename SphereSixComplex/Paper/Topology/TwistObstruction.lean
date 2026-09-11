module

public import SphereSixComplex.Paper.LatticeData
public import Mathlib.Data.ZMod.Basic

/-!
# The integer twist obstruction

The obstruction integer from Section 7 and its value for the chosen twist vectors.
-/

namespace SphereSixComplex.Topology.TwistObstruction

open LatticeData

@[expose] public def v₁ : LatticeData.Lattice := epsilon

@[expose] public def v₂ : LatticeData.Lattice := -epsilon'














end SphereSixComplex.Topology.TwistObstruction
