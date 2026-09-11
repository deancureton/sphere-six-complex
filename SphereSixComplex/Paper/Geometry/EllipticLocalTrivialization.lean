module

public import SphereSixComplex.Paper.Geometry.EllipticFixedPointCriterion
public import SphereSixComplex.Prerequisites.Geometry.EllipticCayleyHomeomorph

/-!
# Actual analytic charts near the elliptic fibres

The Cayley coordinate gives the base chart.  The locally biholomorphic period-family quotient
then supplies local analytic parametrizations by the Cayley disc times the vector cover.
-/

open scoped Manifold ComplexConjugate ContDiff

namespace SphereSixComplex.Geometry.EllipticLocalTrivialization

open Complex SphereSixComplex.TriangleGroup SphereSixComplex.Periods
open SphereSixComplex.Geometry SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticFamilySpecialization

noncomputable section

/-- The open embedding that equips the unit disc with its natural complex manifold structure. -/
public theorem discValIsOpenEmbedding :
    Topology.IsOpenEmbedding ((↑) : ComplexUnitDisc → ℂ) :=
  (isOpen_lt continuous_norm continuous_const).isOpenEmbedding_subtypeVal

public instance complexUnitDiscNonempty : Nonempty ComplexUnitDisc := ⟨ComplexUnitDisc.center⟩

/-- The complex chart on the open unit disc induced by its inclusion into `ℂ`. -/
public noncomputable instance complexUnitDiscChartedSpace : ChartedSpace ℂ ComplexUnitDisc :=
  discValIsOpenEmbedding.singletonChartedSpace


public theorem cayleyDiscCoordinate_contMDiff (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (UpperHalfPlane.cayleyToDisc a) := by
  have hcomp : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (((↑) : ComplexUnitDisc → ℂ) ∘ UpperHalfPlane.cayleyToDisc a) := by
    change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (UpperHalfPlane.cayley a)
    exact contMDiff_of_mdifferentiable (UpperHalfPlane.mdifferentiable_cayley a) n
  exact hcomp.of_comp_isOpenEmbedding discValIsOpenEmbedding

public theorem cayleyInverseUpper_contMDiff (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (UpperHalfPlane.cayleyFromDisc a) := by
  have hval : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      ((↑) : ComplexUnitDisc → ℂ) :=
    contMDiff_isOpenEmbedding discValIsOpenEmbedding
  have hcomp : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (((↑) : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.cayleyFromDisc a) := by
    change ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun w : ComplexUnitDisc ↦ ((a : ℂ) - w.1 * conj (a : ℂ)) / (1 - w.1))
    exact (contMDiff_const.sub (hval.mul contMDiff_const)).div₀
      (contMDiff_const.sub hval) (by
        intro w h
        have hw : w.1 = 1 := (sub_eq_zero.mp h).symm
        have := w.2
        rw [hw] at this
        norm_num at this)
  exact hcomp.of_comp_isOpenEmbedding UpperHalfPlane.isOpenEmbedding_coe

/-- The Cayley homeomorphism is an actual biholomorphism for the natural disc manifold. -/
@[expose] public noncomputable def cayleyDiffeomorph (a : UpperHalfPlane) (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc where
  toEquiv := (UpperHalfPlane.cayleyHomeomorph a).toEquiv
  contMDiff_toFun := cayleyDiscCoordinate_contMDiff a n
  contMDiff_invFun := cayleyInverseUpper_contMDiff a n

/-- The order-three Cayley coordinate as a biholomorphism. -/
@[expose] public noncomputable def orderThreeCayleyDiffeomorph (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc :=
  cayleyDiffeomorph fuchsianOneFixedPoint n

/-- The order-four Cayley coordinate as a biholomorphism. -/
@[expose] public noncomputable def orderFourCayleyDiffeomorph (n : WithTop ℕ∞) :
    UpperHalfPlane ≃ₘ^n⟮(modelWithCornersSelf ℂ ℂ), (modelWithCornersSelf ℂ ℂ)⟯
      ComplexUnitDisc :=
  cayleyDiffeomorph fuchsianTwoFixedPoint n





@[simp]
public theorem orderThreeCayleyHomeomorph_fixedPoint :
    orderThreeCayleyHomeomorph fuchsianOneFixedPoint = ComplexUnitDisc.center := by
  apply Subtype.ext
  exact orderThreeCayley_fixedPoint

@[simp]
public theorem orderFourCayleyHomeomorph_fixedPoint :
    orderFourCayleyHomeomorph fuchsianTwoFixedPoint = ComplexUnitDisc.center := by
  apply Subtype.ext
  exact orderFourCayley_fixedPoint



end

end SphereSixComplex.Geometry.EllipticLocalTrivialization
