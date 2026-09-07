module

public import SphereSixComplex.Topology.CellularPointOrientation

@[expose] public section
noncomputable section
open CategoryTheory AlgebraicTopology
namespace SphereSixComplex.IntegralCWCellularHomologyFoundation

public def withDiskOrientations (T : IntegralCWCellularHomologyFoundation)
    (O : ∀ n, (CWRelativeIntegralSingularChainComplex
      (cwCharacteristicBoundaryInclusion n)).homology n ≃+ ℤ) :
    IntegralCWCellularHomologyFoundation :=
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

public def normalizedDiskOrientations (T : IntegralCWCellularHomologyFoundation) :
    ∀ n, (CWRelativeIntegralSingularChainComplex
      (cwCharacteristicBoundaryInclusion n)).homology n ≃+ ℤ
  | 0 => normalizedPointDiskOrientation
  | 1 => normalizedIntervalDiskOrientation T
  | n + 2 => T.diskOrientation (n + 2)

public def normalized (T : IntegralCWCellularHomologyFoundation) :
    IntegralCWCellularHomologyFoundation :=
  T.withDiskOrientations T.normalizedDiskOrientations

public theorem normalized_diskOrientation_zero (T : IntegralCWCellularHomologyFoundation) :
    T.normalized.diskOrientation 0 = normalizedPointDiskOrientation := rfl

public theorem normalized_diskOrientation_one (T : IntegralCWCellularHomologyFoundation) :
    T.normalized.diskOrientation 1 = normalizedIntervalDiskOrientation T := rfl

public theorem normalized_diskOrientation_add_two (T : IntegralCWCellularHomologyFoundation)
    (n : ℕ) : T.normalized.diskOrientation (n + 2) = T.diskOrientation (n + 2) := rfl

end SphereSixComplex.IntegralCWCellularHomologyFoundation
