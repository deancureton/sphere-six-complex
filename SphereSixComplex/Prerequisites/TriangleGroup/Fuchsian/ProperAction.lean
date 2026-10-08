module

public import SphereSixComplex.Prerequisites.TriangleGroup.BinaryIndexedCoprod
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
public import ForMathlib.Topology.Algebra.ProperlyDiscontinuous
import all SphereSixComplex.Prerequisites.TriangleGroup.FreeProductTorsion

noncomputable section

namespace SphereSixComplex.TriangleGroup.FuchsianProperFreeness

open SphereSixComplex.TriangleGroup

/-- The explicit permutation representation regarded as a genuine action of `Delta`. -/
@[expose, instance_reducible] public noncomputable def fuchsianSourceMulAction :
    MulAction Delta UpperHalfPlane where
  smul g z := (fuchsianSourceAction g) z
  one_smul z := by
    change (fuchsianSourceAction 1) z = z
    rw [map_one]
    rfl
  mul_smul g h z := by
    change (fuchsianSourceAction (g * h)) z =
      (fuchsianSourceAction g) ((fuchsianSourceAction h) z)
    rw [map_mul]
    rfl

/-- Proper discontinuity on the full upper half-plane forces every point stabilizer element to
have finite order for the explicit Fuchsian action. -/
public theorem fuchsian_fixed_isOfFinOrder
    (hproper : letI := fuchsianSourceMulAction
      ProperlyDiscontinuousSMul Delta UpperHalfPlane)
    {g : Delta} {z : UpperHalfPlane} (hfixed : fuchsianSourceAction g • z = z) :
    IsOfFinOrder g := by
  let _ : MulAction Delta UpperHalfPlane := fuchsianSourceMulAction
  let _ : ProperlyDiscontinuousSMul Delta UpperHalfPlane := hproper
  apply ProperlyDiscontinuousSMul.isOfFinOrder_of_fixed_of_properlyDiscontinuous (G := Delta)
    (X := UpperHalfPlane)
  exact hfixed

/-- The explicit Fuchsian action is free at every point outside its two elliptic orbits. -/
public theorem fuchsian_fixed_regular_eq_one
    (hproper : letI := fuchsianSourceMulAction
      ProperlyDiscontinuousSMul Delta UpperHalfPlane)
    {g : Delta} {z : UpperHalfPlane} (hz : FreeProductTorsion.IsFuchsianRegularPoint z)
    (hfixed : fuchsianSourceAction g • z = z) : g = 1 := by
  exact BinaryIndexedCoprod.finiteOrder_fixed_regular_eq_one hz
    (fuchsian_fixed_isOfFinOrder hproper hfixed) hfixed





end SphereSixComplex.TriangleGroup.FuchsianProperFreeness
