module

public import SphereSixComplex.Prerequisites.Topology.CellularPointOrientation
public import SphereSixComplex.Prerequisites.Topology.CellularSquareOrientation

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicTopology
namespace SphereSixComplex.CellularHomology.IntegralComparison

public def withDiskOrientations (T : CellularHomology.IntegralComparison)
    (O : ∀ n, (cwRelativeIntegralSingularChainComplex
      (cwCharacteristicBoundaryInclusion n)).homology n ≃+ ℤ) :
    CellularHomology.IntegralComparison :=
  { T with
    diskOrientation := O
    cellBasis := fun X _ _ _ n ↦
      (Finsupp.mapRange.addEquiv ((O n).symm.trans (T.diskOrientation n))).trans
        (T.cellBasis X n)
    cellBasis_single := by
      intro X _ _ _ n e
      change T.cellBasis X n (Finsupp.mapRange ((O n).symm.trans (T.diskOrientation n))
        (map_zero _) (Finsupp.single e 1)) = _
      rw [Finsupp.mapRange_single]
      let a : ℤ := T.diskOrientation n ((O n).symm 1)
      have hs : Finsupp.single e a = a • Finsupp.single e (1 : ℤ) := by simp
      change T.cellBasis X n (Finsupp.single e a) = _
      rw [hs, map_zsmul, T.cellBasis_single]
      have ho : (O n).symm 1 = a • (T.diskOrientation n).symm 1 := by
        apply (T.diskOrientation n).injective
        simp [a]
      rw [ho]
      exact (map_zsmul _ _ _).symm }

public def normalizedDiskOrientations (T : CellularHomology.IntegralComparison) :
    ∀ n, (cwRelativeIntegralSingularChainComplex
      (cwCharacteristicBoundaryInclusion n)).homology n ≃+ ℤ
  | 0 => normalizedPointDiskOrientation
  | 1 => normalizedIntervalDiskOrientation T
  | 2 => normalizedSquareDiskOrientation
  | n + 3 => T.diskOrientation (n + 3)

public def normalized (T : CellularHomology.IntegralComparison) :
    CellularHomology.IntegralComparison :=
  T.withDiskOrientations T.normalizedDiskOrientations

public theorem normalized_diskOrientation_zero (T : CellularHomology.IntegralComparison) :
    T.normalized.diskOrientation 0 = normalizedPointDiskOrientation := rfl

public theorem normalized_diskOrientation_one (T : CellularHomology.IntegralComparison) :
    T.normalized.diskOrientation 1 = normalizedIntervalDiskOrientation T := rfl

public theorem normalized_diskOrientation_two (T : CellularHomology.IntegralComparison) :
    T.normalized.diskOrientation 2 = normalizedSquareDiskOrientation := rfl

public theorem normalized_diskOrientation_add_three (T : CellularHomology.IntegralComparison)
    (n : ℕ) : T.normalized.diskOrientation (n + 3) = T.diskOrientation (n + 3) := rfl

end SphereSixComplex.CellularHomology.IntegralComparison
