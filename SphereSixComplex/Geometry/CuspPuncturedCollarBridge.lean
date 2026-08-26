module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions
public import SphereSixComplex.Geometry.GlobalDeckSmoothness
public import SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood
public import SphereSixComplex.Geometry.RegularTorusFamily
public import SphereSixComplex.Geometry.FuchsianRegularTorusFamily
public import SphereSixComplex.Geometry.AtlasTransport
public import SphereSixComplex.TriangleGroup.ModularCuspEscape
public import Mathlib.Analysis.Complex.CoveringMap
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
import all Mathlib.Geometry.Manifold.LocalDiffeomorph
import all SphereSixComplex.Periods.FuchsianUniformizationBridge

/-!
# The punctured cusp collar and the global torus family

This file compares the exponential coordinates used by the toric cusp filling with the
normalized period coordinates on the punctured global family.
-/

@[expose] public section

noncomputable section

open Matrix Topology
open scoped ContDiff Manifold

namespace SphereSixComplex.Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.CuspCombinatorics
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.CuspToricPhaseAction
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Model
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions
open SphereSixComplex.Geometry.StandardInfiniteA2ToricQuantitativeRegions.BoundedPolydiscRegions
open SphereSixComplex.Geometry.EstablishedFuchsianCuspNeighborhood
open SphereSixComplex.TriangleGroup.FuchsianArithmeticTermination

/-- The two nontrivial columns of the normalized period matrix. -/
public def firstPeriodCoefficients (lambda : ParameterLattice) : IntegerPeriods :=
  ![lambda 0, lambda 1, 0, 0]

/-- The two identity columns of the normalized period matrix. -/
public def identityPeriodCoefficients (n : ParameterLattice) : IntegerPeriods :=
  ![0, 0, n 0, n 1]

/-- First-block coefficients extracted from a four-dimensional period vector. -/
public def firstParameterCoefficients (n : IntegerPeriods) : ParameterLattice :=
  ![n 0, n 1]

/-- Identity-block coefficients extracted from a four-dimensional period vector. -/
public def identityParameterCoefficients (n : IntegerPeriods) : ParameterLattice :=
  ![n 2, n 3]

public theorem integerPeriods_decompose (n : IntegerPeriods) :
    n = firstPeriodCoefficients (firstParameterCoefficients n) +
      identityPeriodCoefficients (identityParameterCoefficients n) := by
  funext i
  fin_cases i <;>
    simp [firstPeriodCoefficients, identityPeriodCoefficients,
      firstParameterCoefficients, identityParameterCoefficients]

/-- Coordinatewise exponential from additive normalized coordinates to the dense torus. -/
public def denseCuspExponential (zeta : ComplexTwoSpace) (s : ℂ) : DenseTorus :=
  ![NormalizedFuchsianCuspCoordinate.exponentialUnit
      (2 * Real.pi * Complex.I * zeta 0),
    NormalizedFuchsianCuspCoordinate.exponentialUnit
      (2 * Real.pi * Complex.I * zeta 1),
    NormalizedFuchsianCuspCoordinate.exponentialUnit
      (2 * Real.pi * Complex.I * s)]

/-- Additive three-coordinate cover used by the explicit cusp exponential. -/
public abbrev AdditiveCuspCover := ComplexTwoSpace × ℂ

public def denseCuspExponentialCover (p : AdditiveCuspCover) : DenseTorus :=
  denseCuspExponential p.1 p.2

private theorem two_pi_mul_I_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- The complex exponential is locally biholomorphic at every point.  This packages the
analytic inverse-function theorem as a manifold `PartialDiffeomorph`, so it can subsequently be
restricted and multiplied coordinatewise in the cusp exponential cover. -/
public theorem complexExp_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
      Complex.exp := by
  intro x
  let L : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ
    (Units.mk0 (Complex.exp x) (Complex.exp_ne_zero x))
  have hstrict : HasStrictFDerivAt Complex.exp (L : ℂ →L[ℂ] ℂ) x := by
    exact (Complex.hasStrictDerivAt_exp x).hasStrictFDerivAt_equiv
      (Complex.exp_ne_zero x)
  let e : OpenPartialHomeomorph ℂ ℂ := hstrict.toOpenPartialHomeomorph Complex.exp
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ℂ ℂ ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        exact (contMDiff_iff_contDiff.mpr Complex.contDiff_exp).contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        let Ly : ℂ ≃L[ℂ] ℂ := ContinuousLinearEquiv.unitsEquivAut ℂ
          (Units.mk0 (Complex.exp (e.symm y))
            (Complex.exp_ne_zero (e.symm y)))
        have hderiv : fderiv ℂ Complex.exp (e.symm y) =
            (Ly : ℂ →L[ℂ] ℂ) := by
          exact ((Complex.hasDerivAt_exp (e.symm y)).hasFDerivAt_equiv
            (Complex.exp_ne_zero (e.symm y))).fderiv
        have hanalytic : AnalyticAt ℂ e.symm y :=
          e.analyticAt_symm hy analyticAt_cexp hderiv
        exact (contMDiffAt_iff_contDiffAt.mpr hanalytic.contDiffAt).contMDiffWithinAt }
  have hx : x ∈ Φ.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hΦ := Φ.isLocalDiffeomorphAt
    (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ hx
  have heq : (Φ : ℂ → ℂ) = Complex.exp := by
    rfl
  rwa [heq] at hΦ

/-- The nonzero complex exponential, with codomain bundled as `ℂˣ`, is locally
biholomorphic for the standard open-submanifold atlas on the units. -/
public theorem exponentialUnit_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
      NormalizedFuchsianCuspCoordinate.exponentialUnit := by
  intro x
  have hlocal := complexExp_isLocalDiffeomorph x
  rw [IsLocalDiffeomorphAt.eq_def] at hlocal
  obtain ⟨Φ, hx, heq⟩ := hlocal
  let Ψ : PartialDiffeomorph (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ℂ ℂˣ ∞ :=
    { toPartialEquiv :=
        { toFun := NormalizedFuchsianCuspCoordinate.exponentialUnit
          invFun := fun u ↦ Φ.symm (u : ℂ)
          source := Φ.source
          target := {u | (u : ℂ) ∈ Φ.target}
          map_source' := by
            intro z hz
            change Complex.exp z ∈ Φ.target
            rw [heq hz]
            exact Φ.map_source hz
          map_target' := by
            intro u hu
            exact Φ.map_target hu
          left_inv' := by
            intro z hz
            change Φ.symm (Complex.exp z) = z
            rw [heq hz]
            exact Φ.left_inv hz
          right_inv' := by
            intro u hu
            apply Units.ext
            change Complex.exp (Φ.symm (u : ℂ)) = (u : ℂ)
            have hsource : Φ.symm (u : ℂ) ∈ Φ.source := Φ.map_target hu
            rw [heq hsource]
            exact Φ.right_inv hu }
      open_source := Φ.open_source
      open_target := Φ.open_target.preimage Units.isOpenEmbedding_val.continuous
      contMDiffOn_toFun := by
        have hunit : ContMDiff (modelWithCornersSelf ℂ ℂ)
            (modelWithCornersSelf ℂ ℂ) ∞
            NormalizedFuchsianCuspCoordinate.exponentialUnit := by
          apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
          exact contMDiff_iff_contDiff.mpr Complex.contDiff_exp
        exact hunit.contMDiffOn
      contMDiffOn_invFun := by
        exact Φ.contMDiffOn_invFun.comp Units.contMDiff_val.contMDiffOn
          (by intro u hu; exact hu) }
  have hΨ := Ψ.isLocalDiffeomorphAt
    (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ hx
  have hΨeq : (Ψ : ℂ → ℂˣ) =
      NormalizedFuchsianCuspCoordinate.exponentialUnit := by
    rfl
  rwa [hΨeq] at hΨ

public def scaledExponentialUnit (z : ℂ) : ℂˣ :=
  NormalizedFuchsianCuspCoordinate.exponentialUnit
    (2 * Real.pi * Complex.I * z)

/-- Scaling by `2πi` followed by the exponential remains locally biholomorphic. -/
public theorem scaledExponentialUnit_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞
      scaledExponentialUnit := by
  let c : ℂˣ := Units.mk0 (2 * Real.pi * Complex.I) two_pi_mul_I_ne_zero
  let d : ℂ ≃ₘ^∞⟮(modelWithCornersSelf ℂ ℂ),
      (modelWithCornersSelf ℂ ℂ)⟯ ℂ :=
    Diffeomorph.smul (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ c
  have hcomp : IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞
      (NormalizedFuchsianCuspCoordinate.exponentialUnit ∘ d) := by
    intro x
    exact (d.isLocalDiffeomorph x).comp (modelWithCornersSelf ℂ ℂ) ℂˣ
      (exponentialUnit_isLocalDiffeomorph (d x))
  have heq : (NormalizedFuchsianCuspCoordinate.exponentialUnit ∘ d) =
      scaledExponentialUnit := by
    funext z
    rfl
  rwa [heq] at hcomp

/-- Product of two scalar partial biholomorphisms.  Mathlib provides the product operation for
the underlying open partial homeomorphisms; this adds the corresponding complex-smooth data. -/
public noncomputable def complexPartialDiffeomorphProd
    {E E' F F' H H' G G' M N P Q : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup F'] [NormedSpace ℂ F']
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace G] [TopologicalSpace G']
    {I : ModelWithCorners ℂ E H} {I' : ModelWithCorners ℂ E' H'}
    {J : ModelWithCorners ℂ F G} {J' : ModelWithCorners ℂ F' G'}
    [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace P] [TopologicalSpace Q]
    [ChartedSpace H M] [ChartedSpace H' N]
    [ChartedSpace G P] [ChartedSpace G' Q]
    (f : PartialDiffeomorph I I' M N ∞)
    (g : PartialDiffeomorph J J' P Q ∞) :
    PartialDiffeomorph (I.prod J) (I'.prod J') (M × P) (N × Q) ∞ where
  toPartialEquiv := f.toPartialEquiv.prod g.toPartialEquiv
  open_source := f.open_source.prod g.open_source
  open_target := f.open_target.prod g.open_target
  contMDiffOn_toFun := f.contMDiffOn_toFun.prodMap g.contMDiffOn_toFun
  contMDiffOn_invFun := f.contMDiffOn_invFun.prodMap g.contMDiffOn_invFun

/-- The three coordinatewise scaled exponentials form a local biholomorphism before the
additive and dense-torus coordinates are repackaged as `ComplexModel`. -/
public theorem scaledExponentialUnitProduct_isLocalDiffeomorph :
    IsLocalDiffeomorph
      (((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)).prod
        (modelWithCornersSelf ℂ ℂ))
      (((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)).prod
        (modelWithCornersSelf ℂ ℂ)) ∞
      (Prod.map (Prod.map scaledExponentialUnit scaledExponentialUnit)
        scaledExponentialUnit) := by
  intro p
  have h₀ := scaledExponentialUnit_isLocalDiffeomorph p.1.1
  have h₁ := scaledExponentialUnit_isLocalDiffeomorph p.1.2
  have h₂ := scaledExponentialUnit_isLocalDiffeomorph p.2
  rw [IsLocalDiffeomorphAt.eq_def] at h₀ h₁ h₂ ⊢
  obtain ⟨Φ₀, hp₀, heq₀⟩ := h₀
  obtain ⟨Φ₁, hp₁, heq₁⟩ := h₁
  obtain ⟨Φ₂, hp₂, heq₂⟩ := h₂
  let Φ₀₁ := complexPartialDiffeomorphProd Φ₀ Φ₁
  let Φ := complexPartialDiffeomorphProd Φ₀₁ Φ₂
  refine ⟨Φ, ⟨⟨hp₀, hp₁⟩, hp₂⟩, ?_⟩
  intro q hq
  rcases hq with ⟨⟨hq₀, hq₁⟩, hq₂⟩
  exact Prod.ext
    (Prod.ext (heq₀ hq₀) (heq₁ hq₁)) (heq₂ hq₂)

private theorem scaledExponentialUnit_eq (z : ℂ) :
    scaledExponentialUnit z =
      (unitsHomeomorphNeZero (G₀ := ℂ)).symm
        ⟨Complex.exp (2 * Real.pi * Complex.I * z), Complex.exp_ne_zero _⟩ := by
  let e := unitsHomeomorphNeZero (G₀ := ℂ)
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  rfl

private theorem scaledExponentialUnit_isQuotientMap :
    IsQuotientMap scaledExponentialUnit := by
  let e : ℂ ≃ₜ ℂ :=
    Homeomorph.smulOfNeZero (2 * Real.pi * Complex.I) two_pi_mul_I_ne_zero
  have he : IsQuotientMap e := e.isQuotientMap
  have hexp : IsQuotientMap
      (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) :=
    Complex.isAddQuotientCoveringMap_exp.toIsQuotientMap
  have hu : IsQuotientMap (unitsHomeomorphNeZero (G₀ := ℂ)).symm :=
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.isQuotientMap
  have hcomp := hu.comp (hexp.comp he)
  convert hcomp using 1
  funext z
  rw [scaledExponentialUnit_eq]
  rfl

private theorem scaledExponentialUnit_continuous :
    Continuous scaledExponentialUnit :=
  scaledExponentialUnit_isQuotientMap.continuous

private theorem scaledExponentialUnit_isOpenMap :
    IsOpenMap scaledExponentialUnit := by
  let e : ℂ ≃ₜ ℂ :=
    Homeomorph.smulOfNeZero (2 * Real.pi * Complex.I) two_pi_mul_I_ne_zero
  have hcomp : IsOpenMap
      ((unitsHomeomorphNeZero (G₀ := ℂ)).symm ∘
        (fun z : ℂ ↦ (⟨Complex.exp z, Complex.exp_ne_zero z⟩ : {w : ℂ // w ≠ 0})) ∘ e) :=
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.isOpenMap.comp
      (Complex.isCoveringMap_exp.isOpenMap.comp e.isOpenMap)
  convert hcomp using 1
  funext z
  rw [scaledExponentialUnit_eq]
  rfl

private theorem scaledExponentialUnit_surjective :
    Function.Surjective scaledExponentialUnit :=
  scaledExponentialUnit_isQuotientMap.surjective

private def additiveCuspCoverProductHomeomorph :
    AdditiveCuspCover ≃ₜ ((ℂ × ℂ) × ℂ) where
  toFun p := ((p.1 0, p.1 1), p.2)
  invFun p := (![(p.1.1 : ℂ), p.1.2], p.2)
  left_inv p := by
    rcases p with ⟨zeta, s⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv p := by rcases p with ⟨⟨z₀, z₁⟩, s⟩; rfl
  continuous_toFun :=
    ((continuous_apply 0).comp continuous_fst).prodMk
      ((continuous_apply 1).comp continuous_fst) |>.prodMk continuous_snd
  continuous_invFun := by
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      fin_cases i
      · exact continuous_fst.comp continuous_fst
      · exact continuous_snd.comp continuous_fst
    · exact continuous_snd

private def denseTorusProductHomeomorph :
    DenseTorus ≃ₜ (((ℂˣ) × ℂˣ) × ℂˣ) where
  toFun x := ((x 0, x 1), x 2)
  invFun p := ![p.1.1, p.1.2, p.2]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨⟨x₀, x₁⟩, x₂⟩; rfl
  continuous_toFun :=
    (continuous_apply 0).prodMk (continuous_apply 1) |>.prodMk (continuous_apply 2)
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst.comp continuous_fst
    · exact continuous_snd.comp continuous_fst
    · exact continuous_snd

/-- The product repackaging of additive cusp coordinates is complex linear in both directions. -/
private noncomputable def additiveCuspCoverProductDiffeomorph :
    AdditiveCuspCover ≃ₘ^∞⟮
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ)),
      (((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)).prod
        (modelWithCornersSelf ℂ ℂ))⟯ (((ℂ × ℂ) × ℂ)) where
  toEquiv := additiveCuspCoverProductHomeomorph.toEquiv
  contMDiff_toFun := by
    have hfst : ContMDiff
        ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ ComplexTwoSpace) ∞
        (Prod.fst : AdditiveCuspCover → ComplexTwoSpace) := contMDiff_fst
    have h₀ : ContMDiff
        ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ ℂ) ∞
        (fun p : AdditiveCuspCover ↦ p.1 0) := by
      exact ((contMDiff_pi_space.mp
        (contMDiff_id : ContMDiff (modelWithCornersSelf ℂ ComplexTwoSpace)
          (modelWithCornersSelf ℂ ComplexTwoSpace) ∞ id)) 0).comp hfst
    have h₁ : ContMDiff
        ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ ℂ) ∞
        (fun p : AdditiveCuspCover ↦ p.1 1) := by
      exact ((contMDiff_pi_space.mp
        (contMDiff_id : ContMDiff (modelWithCornersSelf ℂ ComplexTwoSpace)
          (modelWithCornersSelf ℂ ComplexTwoSpace) ∞ id)) 1).comp hfst
    exact (h₀.prodMk h₁).prodMk contMDiff_snd
  contMDiff_invFun := by
    have hpi : ContMDiff
        (((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)).prod
          (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ (Fin 2 → ℂ)) ∞
        (fun p : ((ℂ × ℂ) × ℂ) ↦ ![(p.1.1 : ℂ), p.1.2]) := by
      apply contMDiff_pi_space.mpr
      intro i
      fin_cases i
      · exact contMDiff_fst.comp contMDiff_fst
      · exact contMDiff_snd.comp contMDiff_fst
    exact hpi.prodMk contMDiff_snd

@[instance_reducible] local instance cuspDenseTorusCharts :
    ChartedSpace ComplexModel DenseTorus := denseTorusCharts

/-- The product repackaging of dense-torus coordinates is biholomorphic for the standard
singleton atlas on `(C×)³`. -/
private noncomputable def denseTorusProductDiffeomorph :
    DenseTorus ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)).prod
        (modelWithCornersSelf ℂ ℂ))⟯ (((ℂˣ × ℂˣ) × ℂˣ)) := by
  let coordSmooth (i : Fin 3) : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun x : DenseTorus ↦ x i) := by
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    have hcoordinates : ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞ denseTorusComplexCoordinates := by
      simpa only [cuspDenseTorusCharts] using denseTorusComplexCoordinates_contMDiff
    convert (EuclideanSpace.proj i).contMDiff.comp hcoordinates using 1
    funext x
    rfl
  refine
    { toEquiv := denseTorusProductHomeomorph.toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · exact ((coordSmooth 0).prodMk (coordSmooth 1)).prodMk (coordSmooth 2)
  · apply ContMDiff.of_comp_isOpenEmbedding
      denseTorusComplexCoordinates_isOpenEmbedding
    have hpi : ContMDiff
        (((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)).prod
          (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ (Fin 3 → ℂ)) ∞
        (fun p : ((ℂˣ × ℂˣ) × ℂˣ) ↦
          ![((p.1.1 : ℂˣ) : ℂ), ((p.1.2 : ℂˣ) : ℂ), ((p.2 : ℂˣ) : ℂ)]) := by
      apply contMDiff_pi_space.mpr
      intro i
      fin_cases i
      · exact Units.contMDiff_val.comp (contMDiff_fst.comp contMDiff_fst)
      · exact Units.contMDiff_val.comp (contMDiff_snd.comp contMDiff_fst)
      · exact Units.contMDiff_val.comp contMDiff_snd
    have htoLp : ContMDiff (modelWithCornersSelf ℂ (Fin 3 → ℂ))
        (modelWithCornersSelf ℂ ComplexModel) ∞ (WithLp.toLp 2) :=
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 ↦ ℂ)).symm.toDiffeomorph.contMDiff
    have hmodel := htoLp.comp hpi
    apply hmodel.congr
    intro p
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl

/-- The explicit coordinatewise exponential from normalized additive cusp coordinates to the
dense algebraic torus is locally biholomorphic. -/
public theorem denseCuspExponentialCover_isLocalDiffeomorph :
    IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞ denseCuspExponentialCover := by
  let dS := additiveCuspCoverProductDiffeomorph
  let dT := denseTorusProductDiffeomorph
  let rawMap : ((ℂ × ℂ) × ℂ) → ((ℂˣ × ℂˣ) × ℂˣ) :=
    Prod.map (Prod.map scaledExponentialUnit scaledExponentialUnit)
      scaledExponentialUnit
  have hcomp : IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (dT.symm ∘ rawMap ∘ dS) := by
    intro p
    have hS := dS.isLocalDiffeomorph p
    have hraw := scaledExponentialUnitProduct_isLocalDiffeomorph (dS p)
    have hmiddle := hS.comp
      (((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ℂ)).prod
        (modelWithCornersSelf ℂ ℂ)) ((ℂˣ × ℂˣ) × ℂˣ) hraw
    exact hmiddle.comp (modelWithCornersSelf ℂ ComplexModel) DenseTorus
      (dT.symm.isLocalDiffeomorph (rawMap (dS p)))
  have heq : (dT.symm ∘ rawMap ∘ dS) = denseCuspExponentialCover := by
    funext p
    ext i
    fin_cases i <;> rfl
  rwa [heq] at hcomp

/-- The explicit coordinatewise exponential is a quotient map onto the dense algebraic torus. -/
public theorem denseCuspExponentialCover_isQuotientMap :
    IsQuotientMap denseCuspExponentialCover := by
  let f : ((ℂ × ℂ) × ℂ) → (((ℂˣ) × ℂˣ) × ℂˣ) :=
    Prod.map (Prod.map scaledExponentialUnit scaledExponentialUnit) scaledExponentialUnit
  have hfopen : IsOpenMap f :=
    (scaledExponentialUnit_isOpenMap.prodMap scaledExponentialUnit_isOpenMap).prodMap
      scaledExponentialUnit_isOpenMap
  have hfcont : Continuous f :=
    (scaledExponentialUnit_continuous.prodMap scaledExponentialUnit_continuous).prodMap
      scaledExponentialUnit_continuous
  have hfsurj : Function.Surjective f :=
    (scaledExponentialUnit_surjective.prodMap scaledExponentialUnit_surjective).prodMap
      scaledExponentialUnit_surjective
  have hfquot : IsQuotientMap f := hfopen.isQuotientMap hfcont hfsurj
  have hcomp := denseTorusProductHomeomorph.symm.isQuotientMap.comp
    (hfquot.comp additiveCuspCoverProductHomeomorph.isQuotientMap)
  convert hcomp using 1
  funext p
  rcases p with ⟨zeta, s⟩
  ext i
  fin_cases i <;> rfl

public theorem denseCuspExponentialCover_isOpenMap :
    IsOpenMap denseCuspExponentialCover := by
  let f : ((ℂ × ℂ) × ℂ) → (((ℂˣ) × ℂˣ) × ℂˣ) :=
    Prod.map (Prod.map scaledExponentialUnit scaledExponentialUnit) scaledExponentialUnit
  have hfopen : IsOpenMap f :=
    (scaledExponentialUnit_isOpenMap.prodMap scaledExponentialUnit_isOpenMap).prodMap
      scaledExponentialUnit_isOpenMap
  have hcomp := denseTorusProductHomeomorph.symm.isOpenMap.comp
    (hfopen.comp additiveCuspCoverProductHomeomorph.isOpenMap)
  convert hcomp using 1
  funext p
  rcases p with ⟨zeta, s⟩
  ext i
  fin_cases i <;> rfl

public theorem denseCuspExponentialCover_isOpenQuotientMap :
    IsOpenQuotientMap denseCuspExponentialCover :=
  ⟨denseCuspExponentialCover_isQuotientMap.surjective,
    denseCuspExponentialCover_isQuotientMap.continuous,
    denseCuspExponentialCover_isOpenMap⟩

/-- The quotient of additive normalized coordinates by the exact exponential-fibre relation is
canonically homeomorphic to the dense torus. -/
public noncomputable def additiveCuspQuotientHomeomorph :
    Quotient (Setoid.ker denseCuspExponentialCover) ≃ₜ DenseTorus := by
  let f : C(AdditiveCuspCover, DenseTorus) :=
    ⟨denseCuspExponentialCover, denseCuspExponentialCover_isQuotientMap.continuous⟩
  have hf : IsQuotientMap f := denseCuspExponentialCover_isQuotientMap
  exact hf.homeomorph

/-- The part of the dense torus lying over the punctured radius-`r` disc. -/
public def denseTorusCuspRegion (r : ℝ) : Set DenseTorus :=
  {x | ‖((x 2 : ℂˣ) : ℂ)‖ < r}

/-- The additive cover restricted to the preimage of a punctured torus disc. -/
public def additiveCuspRadiusCover (r : ℝ) : Set AdditiveCuspCover :=
  denseCuspExponentialCover ⁻¹' denseTorusCuspRegion r

public theorem mem_additiveCuspRadiusCover_iff
    (r : ℝ) (p : AdditiveCuspCover) :
    p ∈ additiveCuspRadiusCover r ↔
      Real.exp (-2 * Real.pi * p.2.im) < r := by
  change ‖Complex.exp (2 * Real.pi * Complex.I * p.2)‖ < r ↔ _
  rw [Complex.norm_exp]
  simp [Complex.mul_re]

public theorem additiveCuspRadiusCover_convex (r : ℝ) :
    Convex ℝ (additiveCuspRadiusCover r) := by
  intro p hp q hq a b ha hb hab
  rw [mem_additiveCuspRadiusCover_iff] at hp hq ⊢
  have hr : 0 < r := (Real.exp_pos _).trans hp
  have hp' : -2 * Real.pi * p.2.im < Real.log r :=
    (Real.lt_log_iff_exp_lt hr).2 hp
  have hq' : -2 * Real.pi * q.2.im < Real.log r :=
    (Real.lt_log_iff_exp_lt hr).2 hq
  apply (Real.lt_log_iff_exp_lt hr).1
  have hcomb :
      a * (-2 * Real.pi * p.2.im) + b * (-2 * Real.pi * q.2.im) <
        Real.log r := by
    by_cases ha0 : a = 0
    · subst a
      simp only [zero_add] at hab
      simpa [hab] using hq'
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      calc
        a * (-2 * Real.pi * p.2.im) + b * (-2 * Real.pi * q.2.im) <
            a * Real.log r + b * Real.log r :=
          add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hp' ha_pos)
            (mul_le_mul_of_nonneg_left (le_of_lt hq') hb)
        _ = Real.log r := by rw [← add_mul, hab, one_mul]
  convert hcomb using 1
  simp [mul_add]
  ring

/-- A basepoint in the additive cover over every positive cusp radius. -/
public noncomputable def additiveCuspRadiusPoint
    {r : ℝ} (hr : 0 < r) : additiveCuspRadiusCover r := by
  let s : ℂ := ⟨0, (1 - Real.log r) / (2 * Real.pi)⟩
  refine ⟨(0, s), ?_⟩
  rw [mem_additiveCuspRadiusCover_iff]
  apply (Real.lt_log_iff_exp_lt hr).1
  have hsim : s.im = (1 - Real.log r) / (2 * Real.pi) := rfl
  rw [hsim]
  have heq : -2 * Real.pi * ((1 - Real.log r) / (2 * Real.pi)) =
      Real.log r - 1 := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [heq]
  linarith

public theorem additiveCuspRadiusCover_connected
    {r : ℝ} (hr : 0 < r) : ConnectedSpace (additiveCuspRadiusCover r) := by
  apply isConnected_iff_connectedSpace.mp
  exact (additiveCuspRadiusCover_convex r).isConnected
    ⟨additiveCuspRadiusPoint hr, (additiveCuspRadiusPoint hr).property⟩

public def denseTorusCuspOpen (r : ℝ) : TopologicalSpace.Opens DenseTorus :=
  ⟨denseTorusCuspRegion r, by
    have hcoord : Continuous (fun x : DenseTorus ↦ ((x 2 : ℂˣ) : ℂ)) :=
      Units.continuous_val.comp (continuous_apply 2)
    exact isOpen_lt (continuous_norm.comp hcoord) continuous_const⟩

public def additiveCuspRadiusOpen (r : ℝ) : TopologicalSpace.Opens AdditiveCuspCover :=
  ⟨additiveCuspRadiusCover r,
    (denseTorusCuspOpen r).isOpen.preimage
      denseCuspExponentialCover_isOpenQuotientMap.continuous⟩

@[instance_reducible]
public noncomputable def additiveCuspRadiusCoverCharts (r : ℝ) :
    ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
  (additiveCuspRadiusOpen r).instChartedSpace

@[instance_reducible]
public noncomputable def denseTorusCuspRegionCharts (r : ℝ) :
    ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
  (denseTorusCuspOpen r).instChartedSpace

/-- The open dense-torus radius locus inherits the complex-manifold structure of the dense
algebraic torus. -/
public theorem denseTorusCuspRegion_isManifold (r : ℝ) :
    letI := denseTorusCharts
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
      denseTorus_isManifold
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := by
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorus_isManifold
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  change IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
    (denseTorusCuspOpen r)
  infer_instance

public def denseCuspExponentialRadius (r : ℝ) :
    additiveCuspRadiusCover r → denseTorusCuspRegion r :=
  (denseTorusCuspRegion r).restrictPreimage denseCuspExponentialCover

private theorem openSubtypeVal_isLocalDiffeomorph_complex
    {X : Type*} [TopologicalSpace X] [ChartedSpace ComplexModel X]
    (U : TopologicalSpace.Opens X) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (Subtype.val : U → X) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  let e := U.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) U X ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ e.target y).mp
        apply contMDiffAt_id.contMDiffWithinAt.congr_of_mem _ hy
        intro z hz
        change e (e.symm z) = z
        exact e.right_inv hz }
  have hx : x ∈ Φ.source := by
    simp [Φ, e]
  have hΦ := Φ.isLocalDiffeomorphAt
    (modelWithCornersSelf ℂ ComplexModel) (modelWithCornersSelf ℂ ComplexModel) ∞ hx
  have heq : (Φ : U → X) = Subtype.val := by
    funext y
    rfl
  rwa [heq] at hΦ

private theorem openSubtypeVal_isLocalDiffeomorph_additiveCusp
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ModelProd ComplexTwoSpace ℂ) X]
    (U : TopologicalSpace.Opens X) :
    IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      ∞ (Subtype.val : U → X) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  let e := U.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let I := (modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ)
  let Φ : PartialDiffeomorph I I U X ∞ :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ e.target y).mp
        apply contMDiffAt_id.contMDiffWithinAt.congr_of_mem _ hy
        intro z hz
        change e (e.symm z) = z
        exact e.right_inv hz }
  have hx : x ∈ Φ.source := by
    simp [Φ, e]
  have hΦ := Φ.isLocalDiffeomorphAt I I ∞ hx
  have heq : (Φ : U → X) = Subtype.val := by
    funext y
    rfl
  rwa [heq] at hΦ

/-- Inclusion of an open submanifold in the regular rank-two vector-bundle model is locally
biholomorphic. -/
private theorem openSubtypeVal_isLocalDiffeomorph_globalDeck
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ModelProd ℂ ComplexTwoSpace) X]
    (U : TopologicalSpace.Opens X) :
    IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel
      RegularSmoothnessOrder (Subtype.val : U → X) := by
  intro x
  let _ : Nonempty U := ⟨x⟩
  let e := U.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let Φ : PartialDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel U X
      RegularSmoothnessOrder :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
      contMDiffOn_invFun := by
        intro y hy
        apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ e.target y).mp
        apply contMDiffAt_id.contMDiffWithinAt.congr_of_mem _ hy
        intro z hz
        change e (e.symm z) = z
        exact e.right_inv hz }
  have hx : x ∈ Φ.source := by
    simp [Φ, e]
  have hΦ := Φ.isLocalDiffeomorphAt GlobalDeckTotalModel GlobalDeckTotalModel
    RegularSmoothnessOrder hx
  have heq : (Φ : U → X) = Subtype.val := by
    funext y
    rfl
  rwa [heq] at hΦ

private theorem isLocalDiffeomorphAt_congr_eventuallyEq_complex
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ModelProd ComplexTwoSpace ℂ) X] [ChartedSpace ComplexModel Y]
    {f g : X → Y} {x : X}
    (hf : IsLocalDiffeomorphAt
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞ f x)
    (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞ g x := by
  rw [IsLocalDiffeomorphAt.eq_def] at hf ⊢
  obtain ⟨Φ, hx, hfΦ⟩ := hf
  obtain ⟨s, hs, hfgs⟩ := hfg.exists_mem
  obtain ⟨t, hts, htopen, hxt⟩ := mem_nhds_iff.mp hs
  let Ψ : PartialDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) X Y ∞ :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left }
  refine ⟨Ψ, ⟨hx, hxt⟩, ?_⟩
  intro y hy
  change y ∈ Φ.source ∩ t at hy
  calc
    g y = f y := (hfgs (hts hy.2)).symm
    _ = Φ y := hfΦ hy.1
    _ = Ψ y := rfl

private theorem isLocalDiffeomorphAt_congr_eventuallyEq_complexToGlobalDeck
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ComplexModel X] [ChartedSpace (ModelProd ℂ ComplexTwoSpace) Y]
    {f g : X → Y} {x : X}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      GlobalDeckTotalModel RegularSmoothnessOrder f x)
    (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      GlobalDeckTotalModel RegularSmoothnessOrder g x := by
  rw [IsLocalDiffeomorphAt.eq_def] at hf ⊢
  obtain ⟨Φ, hx, hfΦ⟩ := hf
  obtain ⟨s, hs, hfgs⟩ := hfg.exists_mem
  obtain ⟨t, hts, htopen, hxt⟩ := mem_nhds_iff.mp hs
  let Ψ : PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      GlobalDeckTotalModel X Y RegularSmoothnessOrder :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left }
  refine ⟨Ψ, ⟨hx, hxt⟩, ?_⟩
  intro y hy
  change y ∈ Φ.source ∩ t at hy
  calc
    g y = f y := (hfgs (hts hy.2)).symm
    _ = Φ y := hfΦ hy.1
    _ = Ψ y := rfl

/-- Restricting a local biholomorphism to open source and target submanifolds preserves local
biholomorphicity. -/
private theorem localDiffeomorph_openRestriction
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace (ModelProd ComplexTwoSpace ℂ) X] [ChartedSpace ComplexModel Y]
    (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)
    (f : X → Y)
    (hf : IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞ f)
    (hmap : Set.MapsTo f U V) :
    IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun x : U ↦ (⟨f x, hmap x.2⟩ : V)) := by
  intro x
  have hsource := openSubtypeVal_isLocalDiffeomorph_additiveCusp U x
  have htotal : IsLocalDiffeomorphAt
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (f ∘ (Subtype.val : U → X)) x :=
    hsource.comp (modelWithCornersSelf ℂ ComplexModel) Y (hf x.1)
  let y : V := ⟨f x, hmap x.2⟩
  let hval := openSubtypeVal_isLocalDiffeomorph_complex V y
  let loc := hval.localInverse
  have hloc : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ loc (f x) := by
    change IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ loc y.1
    exact hval.localInverse_isLocalDiffeomorphAt
  have hcomp : IsLocalDiffeomorphAt
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (loc ∘ (f ∘ (Subtype.val : U → X))) x :=
    htotal.comp (modelWithCornersSelf ℂ ComplexModel) V hloc
  have hmem : (f ∘ (Subtype.val : U → X)) ⁻¹' loc.source ∈ nhds x :=
    htotal.contMDiffAt.continuousAt
      (loc.open_source.mem_nhds hval.localInverse_mem_source)
  have hevent : (loc ∘ (f ∘ (Subtype.val : U → X))) =ᶠ[nhds x]
      (fun z : U ↦ (⟨f z, hmap z.2⟩ : V)) := by
    filter_upwards [hmem] with z hz
    apply Subtype.ext
    exact hval.localInverse_right_inv hz
  exact isLocalDiffeomorphAt_congr_eventuallyEq_complex hcomp hevent

private theorem isLocalDiffeomorphAt_congr_eventuallyEq_complexModel
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ComplexModel X] [ChartedSpace ComplexModel Y]
    {f g : X → Y} {x : X}
    (hf : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f x)
    (hfg : f =ᶠ[nhds x] g) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ g x := by
  rw [IsLocalDiffeomorphAt.eq_def] at hf ⊢
  obtain ⟨Φ, hx, hfΦ⟩ := hf
  obtain ⟨s, hs, hfgs⟩ := hfg.exists_mem
  obtain ⟨t, hts, htopen, hxt⟩ := mem_nhds_iff.mp hs
  let Ψ : PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) X Y ∞ :=
    { toPartialEquiv := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).toPartialEquiv
      open_source := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_source
      open_target := (Φ.toOpenPartialHomeomorph.restrOpen t htopen).open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono Set.inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono Set.inter_subset_left }
  refine ⟨Ψ, ⟨hx, hxt⟩, ?_⟩
  intro y hy
  change y ∈ Φ.source ∩ t at hy
  calc
    g y = f y := (hfgs (hts hy.2)).symm
    _ = Φ y := hfΦ hy.1
    _ = Ψ y := rfl

/-- A local biholomorphism restricted to open complex submanifolds of its source and target is
again locally biholomorphic. -/
public theorem localDiffeomorph_openRestriction_complexModel
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ComplexModel X] [ChartedSpace ComplexModel Y]
    (U : TopologicalSpace.Opens X) (V : TopologicalSpace.Opens Y)
    (f : X → Y)
    (hf : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ f)
    (hmap : Set.MapsTo f U V) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (fun x : U ↦ (⟨f x, hmap x.2⟩ : V)) := by
  intro x
  have hsource := openSubtypeVal_isLocalDiffeomorph_complex U x
  have htotal : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (f ∘ (Subtype.val : U → X)) x :=
    hsource.comp (modelWithCornersSelf ℂ ComplexModel) Y (hf x.1)
  let y : V := ⟨f x, hmap x.2⟩
  let hval := openSubtypeVal_isLocalDiffeomorph_complex V y
  let loc := hval.localInverse
  have hloc : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ loc (f x) := by
    change IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ loc y.1
    exact hval.localInverse_isLocalDiffeomorphAt
  have hcomp : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (loc ∘ (f ∘ (Subtype.val : U → X))) x :=
    htotal.comp (modelWithCornersSelf ℂ ComplexModel) V hloc
  have hmem : (f ∘ (Subtype.val : U → X)) ⁻¹' loc.source ∈ nhds x :=
    htotal.contMDiffAt.continuousAt
      (loc.open_source.mem_nhds hval.localInverse_mem_source)
  have hevent : (loc ∘ (f ∘ (Subtype.val : U → X))) =ᶠ[nhds x]
      (fun z : U ↦ (⟨f z, hmap z.2⟩ : V)) := by
    filter_upwards [hmem] with z hz
    apply Subtype.ext
    exact hval.localInverse_right_inv hz
  exact isLocalDiffeomorphAt_congr_eventuallyEq_complexModel hcomp hevent

/-- The coordinatewise exponential remains locally biholomorphic after restriction to the
actual punctured radius collar. -/
public theorem denseCuspExponentialRadius_isLocalDiffeomorph (r : ℝ) :
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
      (additiveCuspRadiusOpen r).instChartedSpace
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞ (denseCuspExponentialRadius r) := by
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
    (additiveCuspRadiusOpen r).instChartedSpace
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  have h := localDiffeomorph_openRestriction (additiveCuspRadiusOpen r)
    (denseTorusCuspOpen r) denseCuspExponentialCover
    denseCuspExponentialCover_isLocalDiffeomorph (by
      intro x hx
      exact hx)
  change IsLocalDiffeomorph
    ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
    (modelWithCornersSelf ℂ ComplexModel) ∞ (denseCuspExponentialRadius r) at h
  exact h

public theorem denseCuspExponentialRadius_isOpenQuotientMap (r : ℝ) :
    IsOpenQuotientMap (denseCuspExponentialRadius r) :=
  denseCuspExponentialCover_isOpenQuotientMap.restrictPreimage _

public noncomputable def additiveCuspRadiusQuotientHomeomorph (r : ℝ) :
    Quotient (Setoid.ker (denseCuspExponentialRadius r)) ≃ₜ denseTorusCuspRegion r := by
  let f : C(additiveCuspRadiusCover r, denseTorusCuspRegion r) :=
    ⟨denseCuspExponentialRadius r,
      (denseCuspExponentialRadius_isOpenQuotientMap r).continuous⟩
  have hf : IsQuotientMap f :=
    (denseCuspExponentialRadius_isOpenQuotientMap r).isQuotientMap
  exact hf.homeomorph

@[simp]
public theorem additiveCuspRadiusQuotientHomeomorph_mk
    (r : ℝ) (p : additiveCuspRadiusCover r) :
    additiveCuspRadiusQuotientHomeomorph r (Quotient.mk _ p) =
      denseCuspExponentialRadius r p :=
  rfl

/-- The exponential-fibre quotient carries the atlas transported from the dense-torus radius
locus. -/
@[instance_reducible]
public noncomputable def additiveCuspRadiusQuotientCharts (r : ℝ) :
    ChartedSpace ComplexModel
      (Quotient (Setoid.ker (denseCuspExponentialRadius r))) := by
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  exact transportChartedSpace (additiveCuspRadiusQuotientHomeomorph r).symm

/-- The exact exponential-fibre quotient is biholomorphic to the radius locus in the dense
torus. -/
public noncomputable def additiveCuspRadiusQuotientDiffeomorph (r : ℝ) :
    letI := denseTorusCharts
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
      denseTorus_isManifold
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
        (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
    letI := additiveCuspRadiusQuotientCharts r
    Quotient (Setoid.ker (denseCuspExponentialRadius r))
      ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
        (modelWithCornersSelf ℂ ComplexModel)⟯ denseTorusCuspRegion r := by
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorus_isManifold
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
  let _ := additiveCuspRadiusQuotientCharts r
  exact (transportDiffeomorph (additiveCuspRadiusQuotientHomeomorph r).symm).symm

/-- The quotient projection by the exact exponential fibres is locally biholomorphic for the
transported quotient atlas. -/
public theorem additiveCuspRadiusQuotient_projection_isLocalDiffeomorph (r : ℝ) :
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
      (additiveCuspRadiusOpen r).instChartedSpace
    letI := denseTorusCharts
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
      denseTorus_isManifold
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
        (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
    letI := additiveCuspRadiusQuotientCharts r
    IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (Quotient.mk _ : additiveCuspRadiusCover r →
        Quotient (Setoid.ker (denseCuspExponentialRadius r))) := by
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
    (additiveCuspRadiusOpen r).instChartedSpace
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorus_isManifold
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
  let _ := additiveCuspRadiusQuotientCharts r
  let d := additiveCuspRadiusQuotientDiffeomorph r
  have hcomp : IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞
      ((fun y => d.symm.toEquiv y) ∘ denseCuspExponentialRadius r) := by
    intro p
    exact (denseCuspExponentialRadius_isLocalDiffeomorph r p).comp
      (modelWithCornersSelf ℂ ComplexModel)
      (Quotient (Setoid.ker (denseCuspExponentialRadius r)))
      (d.symm.isLocalDiffeomorph (denseCuspExponentialRadius r p))
  have heq : ((fun y => d.symm.toEquiv y) ∘ denseCuspExponentialRadius r) =
      (Quotient.mk _ : additiveCuspRadiusCover r →
        Quotient (Setoid.ker (denseCuspExponentialRadius r))) := by
    funext p
    change (additiveCuspRadiusQuotientHomeomorph r).symm
      (denseCuspExponentialRadius r p) = Quotient.mk _ p
    apply (additiveCuspRadiusQuotientHomeomorph r).injective
    rw [(additiveCuspRadiusQuotientHomeomorph r).apply_symm_apply]
    exact additiveCuspRadiusQuotientHomeomorph_mk r p
  rwa [heq] at hcomp

/-- The flat punctured radius locus in the toric model. -/
public def toricPuncturedRadiusOpen (M : Model) (r : ℝ) :
    TopologicalSpace.Opens M.Carrier :=
  ⟨{p | M.t p ≠ 0 ∧ ‖M.t p‖ < r},
    (isOpen_ne_fun M.t_holomorphic.continuous continuous_const).inter
      (isOpen_lt (continuous_norm.comp M.t_holomorphic.continuous) continuous_const)⟩

/-- Dense-torus inclusion restricted to the punctured radius locus. -/
public def torusEmbeddingPuncturedRadius (M : Model) (r : ℝ) :
    denseTorusCuspOpen r → toricPuncturedRadiusOpen M r :=
  fun x ↦ ⟨M.torusEmbedding x, by
    constructor
    · rw [M.t_torus]
      exact Units.ne_zero (x.1 2)
    · rw [M.t_torus]
      exact x.2⟩

/-- The dense-torus inclusion remains locally biholomorphic on the punctured radius locus. -/
public theorem torusEmbeddingPuncturedRadius_isLocalDiffeomorph
    (M : Model) (r : ℝ) :
    letI := denseTorusCharts
    letI := M.topology
    letI := M.charts
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (torusEmbeddingPuncturedRadius M r) := by
  let _ := denseTorusCharts
  let _ := M.topology
  let _ := M.charts
  have h := localDiffeomorph_openRestriction_complexModel
    (denseTorusCuspOpen r) (toricPuncturedRadiusOpen M r) M.torusEmbedding
    (M.torusEmbedding_isLocalDiffeomorph) (by
      intro x hx
      constructor
      · rw [M.t_torus]
        exact Units.ne_zero (x 2)
      · rw [M.t_torus]
        exact hx)
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) ∞
    (torusEmbeddingPuncturedRadius M r) at h
  exact h

public theorem torusEmbeddingPuncturedRadius_bijective (M : Model) (r : ℝ) :
    Function.Bijective (torusEmbeddingPuncturedRadius M r) := by
  constructor
  · intro x y hxy
    apply Subtype.ext
    apply M.torus_openEmbedding.injective
    exact congrArg Subtype.val hxy
  · intro y
    have hyRange : y.1 ∈ Set.range M.torusEmbedding := by
      rw [M.torus_range]
      exact y.2.1
    obtain ⟨x, hx⟩ := hyRange
    have hxRadius : x ∈ denseTorusCuspRegion r := by
      change ‖((x 2 : ℂˣ) : ℂ)‖ < r
      rw [← M.t_torus, hx]
      exact y.2.2
    refine ⟨⟨x, hxRadius⟩, ?_⟩
    apply Subtype.ext
    exact hx

/-- The punctured radius locus of the dense torus and its flat toric image are biholomorphic. -/
public noncomputable def torusPuncturedRadiusDiffeomorph (M : Model) (r : ℝ) :
    letI := denseTorusCharts
    letI := M.topology
    letI := M.charts
    denseTorusCuspOpen r ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ toricPuncturedRadiusOpen M r :=
  (torusEmbeddingPuncturedRadius_isLocalDiffeomorph M r).diffeomorphOfBijective
    (torusEmbeddingPuncturedRadius_bijective M r)

/-- The nonzero part of the local toric carrier, as an open complex submanifold. -/
public def puncturedLocalCarrierOpen (M : Model) (r : ℝ) :
    TopologicalSpace.Opens (LocalCarrier M r) :=
  ⟨{p | M.t p ≠ 0},
    isOpen_ne_fun (M.t_holomorphic.continuous.comp continuous_subtype_val)
      continuous_const⟩

/-- The inherited filling atlas on the punctured local carrier, exposed with the exact subtype
used by the topological collar construction. -/
@[instance_reducible]
public noncomputable def puncturedLocalCarrierCharts (M : Model) (r : ℝ) :
    letI := M.topology
    letI := M.charts
    ChartedSpace ComplexModel {p : LocalCarrier M r // M.t p ≠ 0} := by
  let _ := M.topology
  let _ := M.charts
  change ChartedSpace ComplexModel (puncturedLocalCarrierOpen M r)
  exact (puncturedLocalCarrierOpen M r).instChartedSpace

/-- Reassociate the two open-subtype conditions defining the punctured local toric carrier. -/
public def flatPuncturedRadiusEquiv (M : Model) (r : ℝ) :
    toricPuncturedRadiusOpen M r ≃ puncturedLocalCarrierOpen M r where
  toFun p := ⟨⟨p.1, by
    rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
    exact p.2.2⟩, p.2.1⟩
  invFun p := ⟨p.1.1, ⟨p.2, by
    exact mem_ball_zero_iff.mp p.1.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reassociating the nonzero and radius open-subtype conditions is biholomorphic. -/
public noncomputable def flatPuncturedRadiusDiffeomorph (M : Model) (r : ℝ) :
    letI := M.topology
    letI := M.charts
    toricPuncturedRadiusOpen M r ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ puncturedLocalCarrierOpen M r := by
  let _ := M.topology
  let _ := M.charts
  refine
    { toEquiv := flatPuncturedRadiusEquiv M r
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (puncturedLocalCarrierOpen M r) _).mp
    apply (ContMDiff.subtypeVal_comp_iff (cuspNeighborhood M r) _).mp
    exact contMDiff_subtype_val
  · apply (ContMDiff.subtypeVal_comp_iff (toricPuncturedRadiusOpen M r) _).mp
    change ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) ∞
        (fun p : puncturedLocalCarrierOpen M r ↦ (p.1.1 : M.Carrier))
    exact (contMDiff_subtype_val (I := modelWithCornersSelf ℂ ComplexModel)
        (U := cuspNeighborhood M r)).comp
          (contMDiff_subtype_val (I := modelWithCornersSelf ℂ ComplexModel)
            (U := puncturedLocalCarrierOpen M r))

/-- Dense-torus coordinates give a biholomorphism onto the punctured local toric carrier with
its atlas inherited from the actual toric filling. -/
public noncomputable def torusPuncturedLocalDiffeomorph (M : Model) (r : ℝ) :
    letI := denseTorusCharts
    letI := M.topology
    letI := M.charts
    denseTorusCuspOpen r ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ puncturedLocalCarrierOpen M r :=
  (torusPuncturedRadiusDiffeomorph M r).trans (flatPuncturedRadiusDiffeomorph M r)

/-- The exact additive exponential cover, now landing in the punctured local toric carrier with
the atlas inherited from the actual filling. -/
public noncomputable def additiveCuspToPuncturedLocal (M : Model) (r : ℝ) :
    additiveCuspRadiusOpen r → puncturedLocalCarrierOpen M r :=
  fun p ↦ torusPuncturedLocalDiffeomorph M r (denseCuspExponentialRadius r p)

/-- The additive exponential cover of the punctured local toric carrier is locally
biholomorphic. -/
public theorem additiveCuspToPuncturedLocal_isLocalDiffeomorph (M : Model) (r : ℝ) :
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
      (additiveCuspRadiusOpen r).instChartedSpace
    letI := denseTorusCharts
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI := M.topology
    letI := M.charts
    IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (additiveCuspToPuncturedLocal M r) := by
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
    (additiveCuspRadiusOpen r).instChartedSpace
  let _ := denseTorusCharts
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ := M.topology
  let _ := M.charts
  intro p
  exact (denseCuspExponentialRadius_isLocalDiffeomorph r p).comp
    (modelWithCornersSelf ℂ ComplexModel) (puncturedLocalCarrierOpen M r)
      ((torusPuncturedLocalDiffeomorph M r).isLocalDiffeomorph
        (denseCuspExponentialRadius r p))

public noncomputable def torusNonzeroHomeomorph (M : Model) :
    DenseTorus ≃ₜ {p : M.Carrier // M.t p ≠ 0} :=
  M.torus_openEmbedding.toIsEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr M.torus_range)

public noncomputable def torusNonzeroRadiusHomeomorph (M : Model) (r : ℝ) :
    denseTorusCuspRegion r ≃ₜ
      {p : {q : M.Carrier // M.t q ≠ 0} // ‖M.t p‖ < r} :=
  (torusNonzeroHomeomorph M).subtype fun x ↦ by
    change ‖((x 2 : ℂˣ) : ℂ)‖ < r ↔
      ‖M.t (M.torusEmbedding x)‖ < r
    rw [M.t_torus]

public def nestedNonzeroRadiusHomeomorph (M : Model) (r : ℝ) :
    {p : {q : M.Carrier // M.t q ≠ 0} // ‖M.t p‖ < r} ≃ₜ
      {p : LocalCarrier M r // M.t p ≠ 0} where
  toFun p := ⟨⟨p.1.1, by
    rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
    exact p.2⟩, p.1.2⟩
  invFun p := ⟨⟨p.1.1, p.2⟩, by
    exact mem_ball_zero_iff.mp p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val

/-- Dense-torus coordinates identify a punctured toric cusp disc with the corresponding open
subdomain of `(C×)³`. -/
public noncomputable def torusPuncturedLocalHomeomorph (M : Model) (r : ℝ) :
    denseTorusCuspRegion r ≃ₜ {p : LocalCarrier M r // M.t p ≠ 0} :=
  (torusNonzeroRadiusHomeomorph M r).trans (nestedNonzeroRadiusHomeomorph M r)

/-- Additive normalized coordinates modulo their exact exponential fibres give the punctured
local toric carrier. -/
public noncomputable def additiveToPuncturedLocalHomeomorph (M : Model) (r : ℝ) :
    Quotient (Setoid.ker (denseCuspExponentialRadius r)) ≃ₜ
      {p : LocalCarrier M r // M.t p ≠ 0} :=
  (additiveCuspRadiusQuotientHomeomorph r).trans (torusPuncturedLocalHomeomorph M r)

/-- The exact additive exponential-fibre quotient is biholomorphic to the punctured part of
the actual local toric carrier. -/
public noncomputable def additiveToPuncturedLocalDiffeomorph (M : Model) (r : ℝ) :
    letI := denseTorusCharts
    letI := M.topology
    letI := M.charts
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
        (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
    letI := additiveCuspRadiusQuotientCharts r
    Quotient (Setoid.ker (denseCuspExponentialRadius r))
      ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
        (modelWithCornersSelf ℂ ComplexModel)⟯ puncturedLocalCarrierOpen M r := by
  let _ := denseTorusCharts
  let _ := M.topology
  let _ := M.charts
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
  let _ := additiveCuspRadiusQuotientCharts r
  exact (additiveCuspRadiusQuotientDiffeomorph r).trans
    (torusPuncturedLocalDiffeomorph M r)

@[simp]
public theorem denseCuspExponential_apply_zero (zeta : ComplexTwoSpace) (s : ℂ) :
    denseCuspExponential zeta s 0 =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * zeta 0) := rfl

@[simp]
public theorem denseCuspExponential_apply_one (zeta : ComplexTwoSpace) (s : ℂ) :
    denseCuspExponential zeta s 1 =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * zeta 1) := rfl

@[simp]
public theorem denseCuspExponential_apply_two (zeta : ComplexTwoSpace) (s : ℂ) :
    denseCuspExponential zeta s 2 =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * s) := rfl

/-- The third exponential coordinate is exactly the normalized cusp parameter. -/
public theorem denseCuspExponential_last (zeta : ComplexTwoSpace) (s : ℂ) :
    (((denseCuspExponential zeta s 2 : ℂˣ) : ℂ)) = cuspQ s := by
  rfl

public theorem norm_cuspQ (s : ℂ) :
    ‖cuspQ s‖ = Real.exp (-2 * Real.pi * s.im) := by
  rw [cuspQ, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

public theorem mem_cuspHalfPlane_of_norm_cuspQ_lt
    {H r : ℝ} {s : ℂ} (hr : r ≤ cuspRadius H) (hq : ‖cuspQ s‖ < r) :
    s ∈ cuspHalfPlane H := by
  have hexp : Real.exp (-2 * Real.pi * s.im) <
      Real.exp (-2 * Real.pi * H) := by
    rw [← norm_cuspQ, ← cuspRadius]
    exact hq.trans_le hr
  have hlinear := Real.exp_lt_exp.mp hexp
  have hpi : 0 < Real.pi := Real.pi_pos
  change H < s.im
  nlinarith

public theorem additiveCuspRadiusCover_halfPlane
    {H r : ℝ} (hr : r ≤ cuspRadius H) (p : additiveCuspRadiusCover r) :
    p.1.2 ∈ cuspHalfPlane H := by
  apply mem_cuspHalfPlane_of_norm_cuspQ_lt hr
  exact p.2

/-- The first two period columns evaluate to the `2 × 2` period block. -/
public theorem periodVector_firstPeriodCoefficients (x : Parameters)
    (lambda : ParameterLattice) :
    periodVector x (firstPeriodCoefficients lambda) =
      (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) := by
  have hcoeff : (fun j ↦ ((firstPeriodCoefficients lambda j : ℤ) : ℂ)) =
      ![(lambda 0 : ℂ), (lambda 1 : ℂ), 0, 0] := by
    funext j
    fin_cases j <;> simp [firstPeriodCoefficients]
  have hlambda : (fun i ↦ (lambda i : ℂ)) =
      ![(lambda 0 : ℂ), (lambda 1 : ℂ)] := by
    funext i
    fin_cases i <;> rfl
  rw [periodVector, hcoeff, hlambda, periodBlock_mulVec]
  ext i
  fin_cases i <;> simp [periodMatrix, Matrix.mulVec]

/-- The identity period columns are ordinary integral translations in the two additive fibre
coordinates. -/
public theorem periodVector_identityPeriodCoefficients (x : Parameters)
    (n : ParameterLattice) :
    periodVector x (identityPeriodCoefficients n) = fun i ↦ (n i : ℂ) := by
  have hcoeff : (fun j ↦ ((identityPeriodCoefficients n j : ℤ) : ℂ)) =
      ![(0 : ℂ), 0, (n 0 : ℂ), (n 1 : ℂ)] := by
    funext j
    fin_cases j <;> simp [identityPeriodCoefficients]
  rw [periodVector, hcoeff]
  ext i
  fin_cases i <;> simp [periodMatrix, Matrix.mulVec]

public theorem exponentialUnit_add_int (z : ℂ) (n : ℤ) :
    NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * (z + (n : ℂ))) =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * z) := by
  apply Units.ext
  simp only [NormalizedFuchsianCuspCoordinate.exponentialUnit, Units.val_mk0]
  rw [show 2 * Real.pi * Complex.I * (z + (n : ℂ)) =
    2 * Real.pi * Complex.I * z +
      (2 * Real.pi * Complex.I) * (n : ℂ) by ring,
    Complex.exp_add]
  rw [mul_comm (2 * Real.pi * Complex.I) (n : ℂ),
    Complex.exp_int_mul_two_pi_mul_I]
  simp

public theorem scaledExponentialUnit_eq_iff (z w : ℂ) :
    scaledExponentialUnit z = scaledExponentialUnit w ↔
      ∃ n : ℤ, z = w + n := by
  constructor
  · intro h
    have hval := congrArg Units.val h
    change Complex.exp (2 * Real.pi * Complex.I * z) =
      Complex.exp (2 * Real.pi * Complex.I * w) at hval
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hval
    refine ⟨n, ?_⟩
    have hzero : (2 * Real.pi * Complex.I) * (z - (w + (n : ℂ))) = 0 := by
      calc
        (2 * Real.pi * Complex.I) * (z - (w + (n : ℂ))) =
            2 * Real.pi * Complex.I * z -
              2 * Real.pi * Complex.I * w -
                (n : ℂ) * (2 * Real.pi * Complex.I) := by ring
        _ = 0 := by rw [hn]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left two_pi_mul_I_ne_zero)
  · rintro ⟨n, rfl⟩
    exact exponentialUnit_add_int w n

public theorem denseCuspExponentialCover_eq_iff (p q : AdditiveCuspCover) :
    denseCuspExponentialCover p = denseCuspExponentialCover q ↔
      ∃ n₀ n₁ n₂ : ℤ,
        p.1 0 = q.1 0 + n₀ ∧ p.1 1 = q.1 1 + n₁ ∧ p.2 = q.2 + n₂ := by
  constructor
  · intro h
    obtain ⟨n₀, hn₀⟩ := (scaledExponentialUnit_eq_iff (p.1 0) (q.1 0)).mp
      (congrFun h 0)
    obtain ⟨n₁, hn₁⟩ := (scaledExponentialUnit_eq_iff (p.1 1) (q.1 1)).mp
      (congrFun h 1)
    obtain ⟨n₂, hn₂⟩ := (scaledExponentialUnit_eq_iff p.2 q.2).mp
      (congrFun h 2)
    exact ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂⟩
  · rintro ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂⟩
    ext i
    fin_cases i
    · exact congrArg Units.val ((scaledExponentialUnit_eq_iff _ _).mpr ⟨n₀, hn₀⟩)
    · exact congrArg Units.val ((scaledExponentialUnit_eq_iff _ _).mpr ⟨n₁, hn₁⟩)
    · exact congrArg Units.val ((scaledExponentialUnit_eq_iff _ _).mpr ⟨n₂, hn₂⟩)

public theorem exponentialUnit_period_split (c z s : ℂ) (n : ℤ) :
    NormalizedFuchsianCuspCoordinate.exponentialUnit
        (2 * Real.pi * Complex.I * (s * (n : ℂ) + c + z)) =
      NormalizedFuchsianCuspCoordinate.exponentialUnit
          (2 * Real.pi * Complex.I * c) *
        (NormalizedFuchsianCuspCoordinate.exponentialUnit
            (2 * Real.pi * Complex.I * z) *
          NormalizedFuchsianCuspCoordinate.exponentialUnit
              (2 * Real.pi * Complex.I * s) ^ n) := by
  apply Units.ext
  change Complex.exp (2 * Real.pi * Complex.I * (s * (n : ℂ) + c + z)) =
    Complex.exp (2 * Real.pi * Complex.I * c) *
      (Complex.exp (2 * Real.pi * Complex.I * z) *
        (Units.coeHom ℂ)
          (NormalizedFuchsianCuspCoordinate.exponentialUnit
            (2 * Real.pi * Complex.I * s) ^ n))
  rw [map_zpow]
  change Complex.exp (2 * Real.pi * Complex.I * (s * (n : ℂ) + c + z)) =
    Complex.exp (2 * Real.pi * Complex.I * c) *
      (Complex.exp (2 * Real.pi * Complex.I * z) *
        Complex.exp (2 * Real.pi * Complex.I * s) ^ n)
  rw [← Complex.exp_int_mul]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

public theorem B₀Complex_mulVec_cast (lambda : ParameterLattice) :
    NormalizedFuchsianCuspCoordinate.B₀Complex.mulVec (fun i ↦ (lambda i : ℂ)) =
      fun i ↦ (shearVector lambda i : ℂ) := by
  funext i
  simpa [NormalizedFuchsianCuspCoordinate.B₀Complex, shearVector] using
    (RingHom.map_mulVec (Int.castRingHom ℂ) SphereSixComplex.LatticeData.B₀ lambda i).symm

/-- On the normalized cusp lift, the first period block is the integral shear term plus the
holomorphic correction term. -/
public theorem periodBlock_mulVec_cusp
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (lambda : ParameterLattice) :
    (periodBlock (periodValues
        (assembledFuchsianPeriodFunctions E D).tau
        (assembledFuchsianPeriodFunctions E D).mu
        (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
          (fun i ↦ (lambda i : ℂ)) =
      fun i ↦ s * (shearVector lambda i : ℂ) +
        (N.correctionMatrix (cuspQ s)).mulVec (fun j ↦ (lambda j : ℂ)) i := by
  rw [N.periodBlock_eq_smul_B₀_add_correction s hs]
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, B₀Complex_mulVec_cast]
  rfl

/-- Integer translations in the additive fibre coordinates disappear under the exponential. -/
public theorem denseCuspExponential_add_int
    (zeta : ComplexTwoSpace) (s : ℂ) (n : ParameterLattice) :
    denseCuspExponential (zeta + fun i ↦ (n i : ℂ)) s =
      denseCuspExponential zeta s := by
  ext i
  fin_cases i
  · simpa [denseCuspExponential] using
      congrArg Units.val (exponentialUnit_add_int (zeta 0) (n 0))
  · simpa [denseCuspExponential] using
      congrArg Units.val (exponentialUnit_add_int (zeta 1) (n 1))
  · simp [denseCuspExponential]

/-- The normalized period translation becomes the phase-corrected integral toric shear after
coordinatewise exponentiation. -/
public theorem denseCuspExponential_periodBlock
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (zeta : ComplexTwoSpace)
    (lambda : ParameterLattice) :
    denseCuspExponential
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta) s =
      phaseEmbedding (N.phaseCoefficient lambda (cuspQ s)) *
        denseTorusShear lambda (denseCuspExponential zeta s) := by
  rw [periodBlock_mulVec_cusp N s hs lambda]
  ext i
  fin_cases i
  · simpa [denseCuspExponential, phaseEmbedding,
      NormalizedFuchsianCuspCoordinate.phaseCoefficient, denseTorusShear,
      _root_.add_apply] using
      congrArg Units.val
        (exponentialUnit_period_split
          ((N.correctionMatrix (cuspQ s)).mulVec (fun j ↦ (lambda j : ℂ)) 0)
          (zeta 0) s (shearVector lambda 0))
  · simpa [denseCuspExponential, phaseEmbedding,
      NormalizedFuchsianCuspCoordinate.phaseCoefficient, denseTorusShear,
      _root_.add_apply] using
      congrArg Units.val
        (exponentialUnit_period_split
          ((N.correctionMatrix (cuspQ s)).mulVec (fun j ↦ (lambda j : ℂ)) 1)
          (zeta 1) s (shearVector lambda 1))
  · simp [denseCuspExponential, phaseEmbedding, denseTorusShear]

/-- The explicit exponential point in the punctured part of a local toric cusp disc. -/
public def localCuspExponentialPoint (M : Model) (r : ℝ)
    (zeta : ComplexTwoSpace) (s : ℂ) (hs : cuspQ s ∈ Metric.ball (0 : ℂ) r) :
    LocalCarrier M r :=
  ⟨M.torusEmbedding (denseCuspExponential zeta s), by
    change M.t (M.torusEmbedding (denseCuspExponential zeta s)) ∈ Metric.ball 0 r
    rw [M.t_torus, denseCuspExponential_last]
    exact hs⟩

@[simp]
public theorem localCuspExponentialPoint_coe (M : Model) (r : ℝ)
    (zeta : ComplexTwoSpace) (s : ℂ) (hs : cuspQ s ∈ Metric.ball (0 : ℂ) r) :
    (localCuspExponentialPoint M r zeta s hs : M.Carrier) =
      M.torusEmbedding (denseCuspExponential zeta s) :=
  rfl

@[simp]
public theorem localCuspExponentialPoint_t (M : Model) (r : ℝ)
    (zeta : ComplexTwoSpace) (s : ℂ) (hs : cuspQ s ∈ Metric.ball (0 : ℂ) r) :
    M.t (localCuspExponentialPoint M r zeta s hs) = cuspQ s := by
  rw [localCuspExponentialPoint_coe, M.t_torus, denseCuspExponential_last]

@[simp]
public theorem additiveCuspToPuncturedLocal_apply
    (M : Model) (r : ℝ) (p : additiveCuspRadiusCover r) :
    (additiveCuspToPuncturedLocal M r p).1 =
      localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr p.2) := by
  apply Subtype.ext
  rfl

/-- Inclusion of a smaller toric cusp disc into a larger one. -/
public def localCarrierInclusion (M : Model) {r R : ℝ} (hrR : r ≤ R) :
    LocalCarrier M r → LocalCarrier M R :=
  fun p ↦ ⟨p, by
    rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
    exact (mem_ball_zero_iff.mp p.property).trans_le hrR⟩

public theorem localCarrierInclusion_continuous (M : Model) {r R : ℝ} (hrR : r ≤ R) :
    Continuous (localCarrierInclusion M hrR) :=
  continuous_subtype_val.subtype_mk _

public theorem localCarrierInclusion_psiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r ≤ R)
    (hRradius : R ≤ cuspRadius N.height) (lambda : ParameterLattice)
    (p : LocalCarrier M r) :
    localCarrierInclusion M hrR
        ((CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
          N M r hr (hrR.trans hRradius)).psiMap lambda p) =
      (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M R hR hRradius).psiMap lambda (localCarrierInclusion M hrR p) := by
  apply Subtype.ext
  change (((CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M r hr (hrR.trans hRradius)).psiMap lambda p : LocalCarrier M r) : M.Carrier) =
    (((CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M R hR hRradius).psiMap lambda (localCarrierInclusion M hrR p) :
        LocalCarrier M R) : M.Carrier)
  rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_coe,
    CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_coe]
  rfl

/-- Freeness and compact-overlap estimates restrict from a cusp disc to any smaller positive
disc. -/
public noncomputable def restrictActualLocalCuspQuotientWitness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualLocalCuspQuotientWitness N M) (r : ℝ)
    (hr : 0 < r) (hrW : r ≤ W.radius) :
    ActualLocalCuspQuotientWitness N M where
  radius := r
  radius_pos := hr
  radius_lt_one := lt_of_le_of_lt hrW W.radius_lt_one
  radius_le := hrW.trans W.radius_le
  phaseBound := W.phaseBound
  phaseBound_nonneg := W.phaseBound_nonneg
  phaseLogMatrix_entry_bound p i j :=
    W.phaseLogMatrix_entry_bound (localCarrierInclusion M hrW p) i j
  phaseLog_dominates p hp :=
    W.phaseLog_dominates (localCarrierInclusion M hrW p) hp
  fixedPoint := by
    constructor
    · intro lambda p hp hfixed
      apply W.fixedPoint.offCentral lambda (localCarrierInclusion M hrW p) hp
      rw [← localCarrierInclusion_psiMap N M hr W.radius_pos hrW W.radius_le]
      exact congrArg (localCarrierInclusion M hrW) hfixed
    · intro lambda p hp hfixed
      apply W.fixedPoint.central lambda (localCarrierInclusion M hrW p) hp
      rw [← localCarrierInclusion_psiMap N M hr W.radius_pos hrW W.radius_le]
      exact congrArg (localCarrierInclusion M hrW) hfixed
  compactOverlap := by
    intro K L hK hL
    let i := localCarrierInclusion M hrW
    have hKi : IsCompact (i '' K) := hK.image (localCarrierInclusion_continuous M hrW)
    have hLi : IsCompact (i '' L) := hL.image (localCarrierInclusion_continuous M hrW)
    apply (W.compactOverlap (i '' K) (i '' L) hKi hLi).subset
    rintro lambda ⟨y, ⟨x, hxK, hxy⟩, hyL⟩
    refine ⟨i y, ⟨i x, ⟨x, hxK, rfl⟩, ?_⟩, ⟨y, hyL, rfl⟩⟩
    rw [← localCarrierInclusion_psiMap N M hr W.radius_pos hrW W.radius_le,
      hxy]

/-- One common radius carrying both the actual toric quotient estimates and a precisely
invariant regular Fuchsian horodisc. -/
public structure ActualPuncturedCuspCollarWitness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) where
  localWitness : ActualLocalCuspQuotientWitness N M
  region_open : IsOpen (normalizedCuspRegion N localWitness.radius)
  region_regular : normalizedCuspRegion N localWitness.radius ⊆
    {z | IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) z}
  orbitClosure_region_regular : closure (⋃ g : Delta,
      (fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
          normalizedCuspRegion N localWitness.radius) ⊆
    {z | IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) z}
  translates_meet_only_parabolic : ∀ g : Delta,
    ((fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
        normalizedCuspRegion N localWitness.radius ∩
          normalizedCuspRegion N localWitness.radius).Nonempty →
      ∃ k : ℤ, g = g₀ ^ k

/-- The standard separated-horodisc theorem can be shrunk to the already constructed toric
quotient radius, so no independent or incompatible radius is introduced. -/
public theorem exists_actualPuncturedCuspCollarWitness
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualLocalCuspQuotientWitness N M) :
    Nonempty (ActualPuncturedCuspCollarWitness N M) := by
  obtain ⟨H⟩ := EstablishedFuchsianCuspNeighborhood.Established.data
    N W.radius W.radius_pos
  let W' := restrictActualLocalCuspQuotientWitness W H.radius H.radius_pos H.radius_le_upper
  exact ⟨⟨W', H.region_open, H.region_regular, H.orbitClosure_region_regular,
    H.translates_meet_only_parabolic⟩⟩

namespace ActualPuncturedCuspCollarWitness

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

public theorem lift_regular (W : ActualPuncturedCuspCollarWitness N M)
    {s : ℂ} (hs : s ∈ cuspHalfPlane N.height)
    (hq : ‖cuspQ s‖ < W.localWitness.radius) :
    IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s) := by
  apply W.region_regular
  exact ⟨s, ⟨hs, hq⟩, rfl⟩

public theorem closure_region_regular (W : ActualPuncturedCuspCollarWitness N M) :
    closure (normalizedCuspRegion N W.localWitness.radius) ⊆
      {z | IsRegularBasePoint
        (U := E.modularParameter.toTriangleUniformization) z} := by
  have hsub : normalizedCuspRegion N W.localWitness.radius ⊆ ⋃ g : Delta,
      (fun z : UpperHalfPlane ↦
        E.modularParameter.toTriangleUniformization.sourceAction g • z) ''
          normalizedCuspRegion N W.localWitness.radius := by
    apply Set.subset_iUnion_of_subset (1 : Delta)
    intro z hz
    exact ⟨z, hz, by simp⟩
  intro z hz
  exact W.orbitClosure_region_regular (closure_mono hsub hz)

end ActualPuncturedCuspCollarWitness

/-- The open vector-bundle region lying over the selected normalized horodisc. -/
public abbrev regularCuspBundleRegion
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :=
  {p : RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace //
    p.1.1 ∈ normalizedCuspRegion N W.localWitness.radius}

/-- The same vector-bundle region, recorded as an open set so that it inherits the actual
regular-base product atlas. -/
public noncomputable def regularCuspBundleOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    TopologicalSpace.Opens
      (RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace) :=
  ⟨{p | p.1.1 ∈ normalizedCuspRegion N W.localWitness.radius},
    W.region_open.preimage (continuous_subtype_val.comp continuous_fst)⟩

/-- The inherited complex atlas on the normalized regular vector-bundle region. -/
@[instance_reducible]
public noncomputable def regularCuspBundleRegionCharts
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        E.modularParameter.toTriangleUniformization_sourceAction
    letI := regularBaseChartedSpace hproper
    ChartedSpace (ModelProd ℂ ComplexTwoSpace) (regularCuspBundleRegion W) := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  change ChartedSpace (ModelProd ℂ ComplexTwoSpace) (regularCuspBundleOpen W)
  infer_instance

public theorem contMDiffOn_of_mdifferentiableOn_toUpperHalfPlane
    {f : ℂ → UpperHalfPlane} {s : Set ℂ} (hs : IsOpen s)
    (hf : MDiff[s] f) :
    ContMDiffOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ∞ f s := by
  have hcoeMDiff : MDiff[s] (fun z ↦ (f z : ℂ)) :=
    UpperHalfPlane.mdifferentiable_coe.comp_mdifferentiableOn hf
  have hcoeDiff : DifferentiableOn ℂ (fun z ↦ (f z : ℂ)) s := by
    rw [← mdifferentiableOn_iff_differentiableOn]
    exact hcoeMDiff
  have hcoeSmooth : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ℂ) ∞ (fun z ↦ (f z : ℂ)) s :=
    contMDiffOn_iff_contDiffOn.mpr (hcoeDiff.contDiffOn hs)
  intro z hz
  have hcomp := (UpperHalfPlane.contMDiffAt_ofComplex (n := ∞) (f z).im_pos)
    |>.comp_contMDiffWithinAt z (hcoeSmooth z hz)
  have heq : (UpperHalfPlane.ofComplex ∘ fun w ↦ (f w : ℂ)) = f := by
    funext w
    exact UpperHalfPlane.ofComplex_apply (f w)
  rw [heq] at hcomp
  exact hcomp

/-- Normalized additive coordinates are homeomorphic to the regular vector-bundle region over
the chosen horodisc. -/
public noncomputable def additiveCuspBundleHomeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius ≃ₜ regularCuspBundleRegion W where
  toFun p := ⟨(⟨N.lift p.1.2,
      W.lift_regular
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2⟩, p.1.1),
    ⟨p.1.2,
      ⟨additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p, p.2⟩, rfl⟩⟩
  invFun p := ⟨(p.1.2,
      (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ)), by
    change ‖cuspQ
      (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ)‖ <
        W.localWitness.radius
    obtain ⟨s, ⟨hs, hq⟩, hlift⟩ := p.2
    have htau : (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 :
        UpperHalfPlane) : ℂ) = s := by
      rw [← hlift]
      exact N.lift_tau s hs
    simpa only [htau] using hq⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact N.lift_tau p.1.2
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      change N.lift
        (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ) =
          p.1.1.1
      obtain ⟨s, ⟨hs, hq⟩, hlift⟩ := p.2
      have htau : (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 :
          UpperHalfPlane) : ℂ) = s := by
        rw [← hlift]
        exact N.lift_tau s hs
      rw [htau, hlift]
    · rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hlift : Continuous (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        N.lift p.1.2) :=
      N.lift_holomorphic.continuousOn.comp_continuous
        (continuous_snd.comp continuous_subtype_val)
        (fun p ↦ additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
    exact (hlift.subtype_mk _).prodMk
      (continuous_fst.comp continuous_subtype_val)
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_snd.comp continuous_subtype_val).prodMk
      (UpperHalfPlane.continuous_coe.comp
        ((assembledFuchsianPeriodFunctions E D).tau_holomorphic.continuous.comp
          (continuous_subtype_val.comp
            (continuous_fst.comp continuous_subtype_val))))

/-- Normalized additive coordinates are biholomorphic to the open regular vector-bundle region
for the inherited complex atlases on both sides. -/
public noncomputable def additiveCuspBundleDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        E.modularParameter.toTriangleUniformization_sourceAction
    letI := regularBaseChartedSpace hproper
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ)
        (additiveCuspRadiusCover W.localWitness.radius) :=
      (additiveCuspRadiusOpen W.localWitness.radius).instChartedSpace
    letI := regularCuspBundleRegionCharts W
    additiveCuspRadiusCover W.localWitness.radius
      ≃ₘ^∞⟮((modelWithCornersSelf ℂ ComplexTwoSpace).prod
          (modelWithCornersSelf ℂ ℂ)),
        ((modelWithCornersSelf ℂ ℂ).prod
          (modelWithCornersSelf ℂ ComplexTwoSpace))⟯ regularCuspBundleRegion W := by
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ)
      (additiveCuspRadiusCover W.localWitness.radius) :=
    (additiveCuspRadiusOpen W.localWitness.radius).instChartedSpace
  let _ := regularCuspBundleRegionCharts W
  refine
    { toEquiv := (additiveCuspBundleHomeomorph W).toEquiv
      contMDiff_toFun := ?_
      contMDiff_invFun := ?_ }
  · apply (ContMDiff.subtypeVal_comp_iff (regularCuspBundleOpen W) _).mp
    have hs : ContMDiff
        ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ ℂ) ∞
        (fun p : additiveCuspRadiusCover W.localWitness.radius ↦ p.1.2) :=
      contMDiff_snd.comp
        (contMDiff_subtype_val
          (I := ((modelWithCornersSelf ℂ ComplexTwoSpace).prod
            (modelWithCornersSelf ℂ ℂ)))
          (U := additiveCuspRadiusOpen W.localWitness.radius))
    have hliftOn : ContMDiffOn (modelWithCornersSelf ℂ ℂ)
        (modelWithCornersSelf ℂ ℂ) ∞ N.lift (cuspHalfPlane N.height) :=
      contMDiffOn_of_mdifferentiableOn_toUpperHalfPlane
        (isOpen_lt continuous_const Complex.continuous_im) N.lift_holomorphic
    have hlift : ContMDiff
        ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ ℂ) ∞
        (fun p : additiveCuspRadiusCover W.localWitness.radius ↦ N.lift p.1.2) := by
      rw [← contMDiffOn_univ]
      exact hliftOn.comp hs.contMDiffOn (by
        intro p hp
        exact additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
    have hbase : ContMDiff
        ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
        (modelWithCornersSelf ℂ ℂ) ∞
        (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
          (⟨N.lift p.1.2,
            W.lift_regular
              (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2⟩ :
            RegularBase (U := E.modularParameter.toTriangleUniformization))) := by
      apply (ContMDiff.subtypeVal_comp_iff (regularBaseOpen hproper) _).mp
      exact hlift
    exact hbase.prodMk (contMDiff_fst.comp
      (contMDiff_subtype_val
        (I := ((modelWithCornersSelf ℂ ComplexTwoSpace).prod
          (modelWithCornersSelf ℂ ℂ)))
        (U := additiveCuspRadiusOpen W.localWitness.radius)))
  · apply (ContMDiff.subtypeVal_comp_iff
      (additiveCuspRadiusOpen W.localWitness.radius) _).mp
    have hregionVal : ContMDiff
        ((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ComplexTwoSpace))
        ((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ComplexTwoSpace)) ∞
        (Subtype.val : regularCuspBundleRegion W →
          RegularBase (U := E.modularParameter.toTriangleUniformization) ×
            ComplexTwoSpace) :=
      contMDiff_subtype_val
        (I := ((modelWithCornersSelf ℂ ℂ).prod
          (modelWithCornersSelf ℂ ComplexTwoSpace)))
        (U := regularCuspBundleOpen W)
    have hzeta : ContMDiff
        ((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ComplexTwoSpace))
        (modelWithCornersSelf ℂ ComplexTwoSpace) ∞
        (fun p : regularCuspBundleRegion W ↦ p.1.2) :=
      contMDiff_snd.comp hregionVal
    have hbase : ContMDiff
        ((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ComplexTwoSpace))
        (modelWithCornersSelf ℂ ℂ) ∞
        (fun p : regularCuspBundleRegion W ↦ (p.1.1.1 : UpperHalfPlane)) :=
      (contMDiff_subtype_val
        (I := modelWithCornersSelf ℂ ℂ) (U := regularBaseOpen hproper)).comp
          (contMDiff_fst.comp hregionVal)
    have htau : ContMDiff
        ((modelWithCornersSelf ℂ ℂ).prod (modelWithCornersSelf ℂ ComplexTwoSpace))
        (modelWithCornersSelf ℂ ℂ) ∞
        (fun p : regularCuspBundleRegion W ↦
          (((assembledFuchsianPeriodFunctions E D).tau p.1.1.1 : UpperHalfPlane) : ℂ)) :=
      (tau_contMDiff (assembledFuchsianPeriodFunctions E D) ∞).comp hbase
    exact hzeta.prodMk htau

public theorem additiveCuspBundleMap_isOpenEmbedding
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenEmbedding (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
      (additiveCuspBundleHomeomorph W p).1) := by
  have hopen : IsOpen
      {p : RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace |
        p.1.1 ∈ normalizedCuspRegion N W.localWitness.radius} :=
    W.region_open.preimage (continuous_subtype_val.comp continuous_fst)
  exact hopen.isOpenEmbedding_subtypeVal.comp
    (additiveCuspBundleHomeomorph W).isOpenEmbedding

/-- The open part of the regular varying torus family lying over the selected normalized
horodisc. -/
public def regularCuspFamilyRegion
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
  {x | (regularTotalSpaceBase (assembledFuchsianPeriodFunctions E D) x : UpperHalfPlane) ∈
    normalizedCuspRegion N W.localWitness.radius}

public theorem regularCuspFamilyRegion_isOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpen (regularCuspFamilyRegion W) := by
  exact W.region_open.preimage
    (continuous_subtype_val.comp
      (regularTotalSpaceBase_continuous (assembledFuchsianPeriodFunctions E D)))

/-- The cusp collar inside the actual `PuncturedGlobalFamily`, defined as the image of the
selected regular horodisc. -/
public def puncturedGlobalCuspCollar
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set (PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D)) :=
  let _ := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  quotientProjection '' regularCuspFamilyRegion W

/-- The actual global cusp collar is open. -/
public theorem puncturedGlobalCuspCollar_isOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpen (puncturedGlobalCuspCollar W) := by
  let _ : MulAction Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ : ContinuousConstSMul Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction_continuousConstSMul
      (assembledFuchsianPeriodFunctions E D) hproper
  let q : RegularTotalSpace (assembledFuchsianPeriodFunctions E D) →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) := quotientProjection
  have hq : IsOpenMap q := by
    dsimp only [q]
    rw [quotientProjection.eq_def]
    exact isOpenMap_quotient_mk'_mul
  exact hq _ (regularCuspFamilyRegion_isOpen W)

/-- The additive first-period translation is exactly the actual local cusp action under the
explicit exponential map. -/
public theorem localCuspExponentialPoint_period_equivariant
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (hr : 0 < r) (hradius : r ≤ cuspRadius N.height)
    (s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (hsr : cuspQ s ∈ Metric.ball (0 : ℂ) r)
    (zeta : ComplexTwoSpace) (lambda : ParameterLattice) :
    let C := CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M r hr hradius
    C.psiMap lambda (localCuspExponentialPoint M r zeta s hsr) =
      localCuspExponentialPoint M r
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta) s hsr := by
  dsimp only
  apply Subtype.ext
  rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_coe]
  rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe]
  rw [CuspToricPhaseAction.ToricModel.phaseAction_apply, M.fanShear_torus,
    M.torusAction_torus]
  rw [M.t_torus, denseCuspExponential_last]
  change M.torusEmbedding
      (phaseEmbedding (N.phaseCoefficient lambda (cuspQ s)) *
        denseTorusShear lambda (denseCuspExponential zeta s)) = _
  exact congrArg M.torusEmbedding (denseCuspExponential_periodBlock N s hs zeta lambda).symm

/-- A normalized cusp coordinate in the regular additive vector-bundle cover. -/
public def regularCuspBundlePoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) :
    RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace :=
  (⟨N.lift s, hregular⟩, zeta)

/-- The corresponding point of the normalized varying torus family. -/
public noncomputable def regularCuspFamilyPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) :
    RegularTotalSpace (assembledFuchsianPeriodFunctions E D) :=
  Quotient.mk _ (regularCuspBundlePoint N s hregular zeta)

/-- Integral period translations give the same point in the varying torus fibre. -/
public theorem regularCuspFamilyPoint_period
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) (n : IntegerPeriods) :
    regularCuspFamilyPoint N s hregular
        (periodVector (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s)) n + zeta) =
      regularCuspFamilyPoint N s hregular zeta := by
  apply Quotient.sound
  change MulAction.orbitRel
    (FamilyPeriodGroup (regularParameterMap (assembledFuchsianPeriodFunctions E D))) _
      (regularCuspBundlePoint N s hregular
        (periodVector (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s)) n + zeta))
      (regularCuspBundlePoint N s hregular zeta)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨Multiplicative.ofAdd n, ?_⟩
  apply Prod.ext
  · rfl
  · rfl

/-- The normalized additive cusp coordinate mapped into the actual global punctured family. -/
public noncomputable def puncturedGlobalCuspPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (zeta : ComplexTwoSpace) :
    PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  Quotient.mk _ (regularCuspFamilyPoint N s hregular zeta)

/-- Translation by one normalized cusp period is the parabolic deck transformation and hence
disappears in the global triangle-group quotient. -/
public theorem puncturedGlobalCuspPoint_shift
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height)
    (hregular : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift s))
    (hregularShift : IsRegularBasePoint
      (U := E.modularParameter.toTriangleUniformization) (N.lift (s - 1)))
    (zeta : ComplexTwoSpace) :
    puncturedGlobalCuspPoint N (s - 1) hregularShift zeta =
      puncturedGlobalCuspPoint N s hregular zeta := by
  let _ : MulAction Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  apply Quotient.sound
  change MulAction.orbitRel Delta _
    (regularCuspFamilyPoint N (s - 1) hregularShift zeta)
    (regularCuspFamilyPoint N s hregular zeta)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨g₀, ?_⟩
  change regularFamilyDeckMap (assembledFuchsianPeriodFunctions E D) g₀
      (Quotient.mk _ (regularCuspBundlePoint N s hregular zeta)) =
    Quotient.mk _ (regularCuspBundlePoint N (s - 1) hregularShift zeta)
  rw [regularFamilyDeckMap_mk]
  apply Quotient.sound
  change MulAction.orbitRel
    (FamilyPeriodGroup (regularParameterMap (assembledFuchsianPeriodFunctions E D))) _
      (regularDeckMap (assembledFuchsianPeriodFunctions E D) g₀
        (regularCuspBundlePoint N s hregular zeta))
      (regularCuspBundlePoint N (s - 1) hregularShift zeta)
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨1, ?_⟩
  apply Prod.ext
  · apply Subtype.ext
    simpa [regularCuspBundlePoint, regularDeckMap] using N.lift_shift s hs
  · simp [regularCuspBundlePoint, regularDeckMap, periodTransport_gZero]

/-- The explicit normalized additive coordinate mapped to the actual global family, using the
regularity supplied by the selected cusp collar witness. -/
public noncomputable def actualPuncturedGlobalCuspPoint
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  puncturedGlobalCuspPoint N s (W.lift_regular hs hq) zeta

public theorem actualPuncturedGlobalCuspPoint_mem_collar
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) :
    actualPuncturedGlobalCuspPoint W s hs hq zeta ∈
      puncturedGlobalCuspCollar W := by
  let _ : MulAction Delta
      (RegularTotalSpace (assembledFuchsianPeriodFunctions E D)) :=
    regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  refine ⟨regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta, ?_, rfl⟩
  change ((regularTotalSpaceBase (assembledFuchsianPeriodFunctions E D)
    (regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta) :
      RegularBase (U := E.modularParameter.toTriangleUniformization)) : UpperHalfPlane) ∈
        normalizedCuspRegion N W.localWitness.radius
  rw [regularCuspFamilyPoint.eq_def, regularTotalSpaceBase_mk]
  exact ⟨s, ⟨hs, hq⟩, rfl⟩

public theorem cuspQ_add_int (s : ℂ) (n : ℤ) :
    cuspQ (s + n) = cuspQ s := by
  exact congrArg Units.val (exponentialUnit_add_int s n)

public theorem cuspHalfPlane_add_int {H : ℝ} {s : ℂ}
    (hs : s ∈ cuspHalfPlane H) (n : ℤ) : s + n ∈ cuspHalfPlane H := by
  change H < (s + (n : ℂ)).im
  simpa [cuspHalfPlane] using hs

/-- Iterating the normalized shift identifies every integral logarithm translate with the
corresponding power of the parabolic generator. -/
public theorem lift_sub_int
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (k : ℤ) :
    N.lift (s - k) =
      E.modularParameter.toTriangleUniformization.sourceAction (g₀ ^ k) • N.lift s := by
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hsPrev : s - (n : ℤ) ∈ cuspHalfPlane N.height := by
        simpa [sub_eq_add_neg] using cuspHalfPlane_add_int hs (-(n : ℤ))
      have hcalc : N.lift (s - ((n : ℂ) + 1)) =
          E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ ((n : ℤ) + 1)) • N.lift s := by
        calc
        N.lift (s - ((n : ℂ) + 1)) = N.lift ((s - (n : ℂ)) - 1) := by
          congr 1
          ring
        _ = E.modularParameter.toTriangleUniformization.sourceAction g₀ •
            N.lift (s - (n : ℤ)) := N.lift_shift _ hsPrev
        _ = E.modularParameter.toTriangleUniformization.sourceAction g₀ •
            (E.modularParameter.toTriangleUniformization.sourceAction (g₀ ^ (n : ℤ)) •
              N.lift s) :=
          congrArg _ ih
        _ = E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ ((n : ℤ) + 1)) • N.lift s := by
          rw [show g₀ ^ ((n : ℤ) + 1) = g₀ * g₀ ^ (n : ℤ) by
            calc
              g₀ ^ ((n : ℤ) + 1) = g₀ ^ (1 + (n : ℤ)) := by congr 1; omega
              _ = g₀ ^ (1 : ℤ) * g₀ ^ (n : ℤ) :=
                _root_.zpow_add g₀ 1 (n : ℤ)
              _ = g₀ * g₀ ^ (n : ℤ) := by rw [zpow_one]]
          simp [map_mul, mul_smul]
      simpa only [Int.cast_add, Int.cast_natCast, Int.cast_one] using hcalc

  | pred n ih =>
      have hsNext : s - (-(n : ℤ) - 1) ∈ cuspHalfPlane N.height := by
        convert cuspHalfPlane_add_int hs ((n : ℤ) + 1) using 1
        push_cast
        ring
      have hshift : N.lift (s - ((-(n : ℤ) : ℤ) : ℂ)) =
          E.modularParameter.toTriangleUniformization.sourceAction g₀ •
            N.lift (s - ((-(n : ℤ) - 1 : ℤ) : ℂ)) := by
        have h := N.lift_shift (s - (-(n : ℤ) - 1)) hsNext
        have heq : s - (-(n : ℂ) - 1) - 1 = s - (-(n : ℂ)) := by ring
        push_cast at h
        rw [heq] at h
        simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] using h
      have hback : N.lift (s - (-(n : ℤ) - 1)) =
          E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ •
            N.lift (s - (-(n : ℤ))) := by
        have h := congrArg (fun z ↦
          E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ • z) hshift
        simpa [map_inv, inv_smul_smul] using h.symm
      have hcalc : N.lift (s - (((-(n : ℤ) - 1 : ℤ) : ℂ))) =
          E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ (-(n : ℤ) - 1)) • N.lift s := by
        calc
        N.lift (s - (((-(n : ℤ) - 1 : ℤ) : ℂ))) =
            E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ •
              N.lift (s - (-(n : ℤ))) := by
          simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] using hback
        _ = E.modularParameter.toTriangleUniformization.sourceAction g₀⁻¹ •
            (E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ (-(n : ℤ))) • N.lift s) := by
          apply congrArg _
          simpa only [Int.cast_neg, Int.cast_natCast] using ih
        _ = E.modularParameter.toTriangleUniformization.sourceAction
              (g₀ ^ (-(n : ℤ) - 1)) • N.lift s := by
          rw [show g₀ ^ (-(n : ℤ) - 1) = g₀⁻¹ * g₀ ^ (-(n : ℤ)) by
            rw [show -(n : ℤ) - 1 = -1 + -(n : ℤ) by ring,
              _root_.zpow_add]
            simp]
          simp [map_mul, mul_smul]
      simpa only [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_one] using hcalc

/-- Canonical fibre transport is trivial on the whole parabolic cyclic subgroup. -/
public theorem periodTransport_gZero_zpow (k : ℤ) (x : PeriodDomain) :
    periodTransport (g₀ ^ k) x = 1 := by
  have hinv : ∀ y : PeriodDomain, periodTransport g₀⁻¹ y = 1 := by
    intro y
    have h := periodTransport_mul g₀ g₀⁻¹ y
    rw [mul_inv_cancel, periodTransport_one, periodTransport_gZero] at h
    simpa using h.symm
  induction k using Int.induction_on generalizing x with
  | zero => exact periodTransport_one x
  | succ n ih =>
      rw [_root_.zpow_add_one, periodTransport_mul, ih,
        periodTransport_gZero, mul_one]
  | pred n ih =>
      rw [show g₀ ^ (-(n : ℤ) - 1) = g₀ ^ (-(n : ℤ)) * g₀⁻¹ by
        rw [show -(n : ℤ) - 1 = -(n : ℤ) + -1 by ring,
          _root_.zpow_add]
        simp]
      rw [periodTransport_mul, ih, hinv, mul_one]

/-- All integral choices of the logarithm of the cusp parameter define the same global-family
point. -/
public theorem actualPuncturedGlobalCuspPoint_add_int
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (n : ℤ)
    (hsn : s + n ∈ cuspHalfPlane N.height)
    (hqn : ‖cuspQ (s + n)‖ < W.localWitness.radius) :
    actualPuncturedGlobalCuspPoint W (s + n) hsn hqn zeta =
      actualPuncturedGlobalCuspPoint W s hs hq zeta := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hn : s + (((n : ℤ) + 1 : ℤ) : ℂ) - 1 = s + (n : ℂ) := by
        push_cast
        ring
      have hsPrev : s + (n : ℂ) ∈ cuspHalfPlane N.height :=
        cuspHalfPlane_add_int hs n
      have hqPrev : ‖cuspQ (s + (n : ℂ))‖ < W.localWitness.radius := by
        have hc := cuspQ_add_int s (n : ℤ)
        exact congrArg norm hc ▸ hq
      have hsShift : s + (((n : ℤ) + 1 : ℤ) : ℂ) - 1 ∈
          cuspHalfPlane N.height := hn.symm ▸ hsPrev
      have hqShift : ‖cuspQ (s + (((n : ℤ) + 1 : ℤ) : ℂ) - 1)‖ <
          W.localWitness.radius := hn.symm ▸ hqPrev
      have hshift := puncturedGlobalCuspPoint_shift N
        (s + (((n : ℤ) + 1 : ℤ) : ℂ)) hsn
        (W.lift_regular hsn hqn)
        (W.lift_regular hsShift hqShift) zeta
      have hstep :
          actualPuncturedGlobalCuspPoint W
              (s + (((n : ℤ) + 1 : ℤ) : ℂ)) hsn hqn zeta =
            actualPuncturedGlobalCuspPoint W (s + (n : ℂ)) hsPrev hqPrev zeta := by
        change puncturedGlobalCuspPoint N _ _ _ = puncturedGlobalCuspPoint N _ _ _
        simpa only [hn] using hshift.symm
      exact hstep.trans (ih hsPrev hqPrev)
  | pred n ih =>
      have hn : s + ((-(n : ℤ) : ℤ) : ℂ) - 1 =
          s + ((-(n : ℤ) - 1 : ℤ) : ℂ) := by
        push_cast
        ring
      have hsCurrent : s + ((-(n : ℤ) : ℤ) : ℂ) ∈ cuspHalfPlane N.height :=
        cuspHalfPlane_add_int hs (-(n : ℤ))
      have hqCurrent : ‖cuspQ (s + ((-(n : ℤ) : ℤ) : ℂ))‖ <
          W.localWitness.radius := by
        have hc := cuspQ_add_int s (-(n : ℤ))
        exact congrArg norm hc ▸ hq
      have hsShift : s + ((-(n : ℤ) : ℤ) : ℂ) - 1 ∈
          cuspHalfPlane N.height := hn.symm ▸ hsn
      have hqShift : ‖cuspQ (s + ((-(n : ℤ) : ℤ) : ℂ) - 1)‖ <
          W.localWitness.radius := hn.symm ▸ hqn
      have hshift := puncturedGlobalCuspPoint_shift N
        (s + ((-(n : ℤ) : ℤ) : ℂ)) hsCurrent
        (W.lift_regular hsCurrent hqCurrent)
        (W.lift_regular hsShift hqShift) zeta
      have hstep :
          actualPuncturedGlobalCuspPoint W
              (s + ((-(n : ℤ) - 1 : ℤ) : ℂ)) hsn hqn zeta =
            actualPuncturedGlobalCuspPoint W
              (s + ((-(n : ℤ) : ℤ) : ℂ)) hsCurrent hqCurrent zeta := by
        change puncturedGlobalCuspPoint N _ _ _ = puncturedGlobalCuspPoint N _ _ _
        simpa only [hn] using hshift
      exact hstep.trans (ih hsCurrent hqCurrent)

public theorem actualPuncturedGlobalCuspPoint_add_fibre_int
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (n : ParameterLattice) :
    actualPuncturedGlobalCuspPoint W s hs hq
        (zeta + fun i ↦ (n i : ℂ)) =
      actualPuncturedGlobalCuspPoint W s hs hq zeta := by
  change Quotient.mk _
      (regularCuspFamilyPoint N s (W.lift_regular hs hq)
        (zeta + fun i ↦ (n i : ℂ))) =
    Quotient.mk _ (regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta)
  apply congrArg (Quotient.mk _)
  simpa [periodVector_identityPeriodCoefficients, add_comm] using
    regularCuspFamilyPoint_period N s (W.lift_regular hs hq) zeta
      (identityPeriodCoefficients n)

public theorem actualPuncturedGlobalCuspPoint_congr
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) {s s' : ℂ}
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (hs' : s' ∈ cuspHalfPlane N.height) (hq' : ‖cuspQ s'‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (h : s = s') :
    actualPuncturedGlobalCuspPoint W s hs hq zeta =
      actualPuncturedGlobalCuspPoint W s' hs' hq' zeta := by
  subst s'
  rfl

public theorem actualPuncturedGlobalCuspPoint_periodBlock
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (s : ℂ)
    (hs : s ∈ cuspHalfPlane N.height) (hq : ‖cuspQ s‖ < W.localWitness.radius)
    (zeta : ComplexTwoSpace) (lambda : ParameterLattice) :
    actualPuncturedGlobalCuspPoint W s hs hq
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta) =
      actualPuncturedGlobalCuspPoint W s hs hq zeta := by
  change Quotient.mk _
      (regularCuspFamilyPoint N s (W.lift_regular hs hq)
        ((periodBlock (periodValues
            (assembledFuchsianPeriodFunctions E D).tau
            (assembledFuchsianPeriodFunctions E D).mu
            (assembledFuchsianPeriodFunctions E D).beta (N.lift s))).mulVec
              (fun i ↦ (lambda i : ℂ)) + zeta)) =
    Quotient.mk _ (regularCuspFamilyPoint N s (W.lift_regular hs hq) zeta)
  apply congrArg (Quotient.mk _)
  simpa [periodVector_firstPeriodCoefficients] using
    regularCuspFamilyPoint_period N s (W.lift_regular hs hq) zeta
      (firstPeriodCoefficients lambda)

/-- The normalized additive cover map into the actual global collar. -/
public noncomputable def additiveCuspCoverToGlobal
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  fun p ↦ actualPuncturedGlobalCuspPoint W p.1.2
    (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2 p.1.1

/-- The additive cusp map is exactly the composite of the two defining family quotients on the
normalized regular bundle chart. -/
public theorem additiveCuspCoverToGlobal_eq_quotientProjections
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    letI := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
    additiveCuspCoverToGlobal W p =
      (quotientProjection : RegularTotalSpace (assembledFuchsianPeriodFunctions E D) →
        PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D))
        ((projection
          (regularParameterMap (assembledFuchsianPeriodFunctions E D)) :
            RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace →
              RegularTotalSpace (assembledFuchsianPeriodFunctions E D))
          ((additiveCuspBundleHomeomorph W p).1)) := by
  let _ := regularFamilyDeckAction (assembledFuchsianPeriodFunctions E D)
  unfold additiveCuspCoverToGlobal actualPuncturedGlobalCuspPoint
    puncturedGlobalCuspPoint regularCuspFamilyPoint
  rw [TorusFamily.projection.eq_def, quotientProjection.eq_def]
  rfl

public theorem additiveCuspCoverToGlobal_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (additiveCuspCoverToGlobal W) := by
  let S := additiveCuspRadiusCover W.localWitness.radius
  have hlift : Continuous (fun p : S ↦ N.lift p.1.2) :=
    N.lift_holomorphic.continuousOn.comp_continuous
      (continuous_snd.comp continuous_subtype_val)
      (fun p ↦ additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
  have hbase : Continuous (fun p : S ↦
      (⟨N.lift p.1.2,
        W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2⟩ :
        RegularBase (U := E.modularParameter.toTriangleUniformization))) :=
    hlift.subtype_mk _
  have hbundle : Continuous (fun p : S ↦
      (regularCuspBundlePoint N p.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2) p.1.1)) :=
    hbase.prodMk (continuous_fst.comp continuous_subtype_val)
  change Continuous (fun p : S ↦ Quotient.mk _ (Quotient.mk _
    (regularCuspBundlePoint N p.1.2
      (W.lift_regular
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2) p.1.1)))
  exact continuous_quot_mk.comp (continuous_quot_mk.comp hbundle)

/-- The normalized additive cover map is locally biholomorphic: first by the normalized lift
into the open regular vector bundle, then through the period-lattice and Fuchsian deck
projections. -/
public theorem additiveCuspCoverToGlobal_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let F := assembledFuchsianPeriodFunctions E D
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        E.modularParameter.toTriangleUniformization_sourceAction
    let hsource := E.modularParameter.toTriangleUniformization_sourceAction
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a
        RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound
        (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
    let hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
      F hproper RegularSmoothnessOrder
    letI : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (RegularTotalSpace F) := hregular.1
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    letI := regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
    letI := regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
    letI := regularFamilyDeckAction_continuousConstSMul F hproper
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ)
        (additiveCuspRadiusCover W.localWitness.radius) :=
      (additiveCuspRadiusOpen W.localWitness.radius).instChartedSpace
    letI := regularCuspBundleRegionCharts W
    IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      GlobalDeckTotalModel RegularSmoothnessOrder (additiveCuspCoverToGlobal W) := by
  let F := assembledFuchsianPeriodFunctions E D
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let hsource := E.modularParameter.toTriangleUniformization_sourceAction
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound
      (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
  have hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    F hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace F) := hregular.1
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : IsCancelSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ)
      (additiveCuspRadiusCover W.localWitness.radius) :=
    (additiveCuspRadiusOpen W.localWitness.radius).instChartedSpace
  let _ := regularCuspBundleRegionCharts W
  have hglobal := puncturedGlobalFamily_isManifold_and_projection_isLocalDiffeomorph
    F hsource hproper
  let d := additiveCuspBundleDiffeomorph W
  let q₁ : RegularBase (U := E.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace → RegularTotalSpace F := quotientProjection
  let q₂ : RegularTotalSpace F → PuncturedGlobalFamily F := quotientProjection
  have hcomp : IsLocalDiffeomorph
      ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
      GlobalDeckTotalModel RegularSmoothnessOrder
      (q₂ ∘ q₁ ∘ Subtype.val ∘ fun p ↦ d.toEquiv p) := by
    intro p
    have hd := d.isLocalDiffeomorph p
    have hinc := openSubtypeVal_isLocalDiffeomorph_globalDeck
      (regularCuspBundleOpen W) (d.toEquiv p)
    have h₁ := hd.comp GlobalDeckTotalModel
      (RegularBase (U := E.modularParameter.toTriangleUniformization) × ComplexTwoSpace) hinc
    have h₂ := h₁.comp GlobalDeckTotalModel (RegularTotalSpace F)
      (hregular.2 ((d.toEquiv p).1))
    exact h₂.comp GlobalDeckTotalModel (PuncturedGlobalFamily F)
      (hglobal.2 (q₁ (d.toEquiv p).1))
  have heq : (q₂ ∘ q₁ ∘ Subtype.val ∘ fun p ↦ d.toEquiv p) =
      additiveCuspCoverToGlobal W := by
    funext p
    rfl
  rwa [heq] at hcomp

public theorem additiveCuspCoverToGlobal_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (additiveCuspCoverToGlobal W) := by
  let F := assembledFuchsianPeriodFunctions E D
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let _ := familyContinuousConstSMul (regularParameterMap F)
    (fun a ↦ (periodSection_contMDiff F a 0).continuous.comp continuous_subtype_val)
  let _ := regularFamilyDeckAction F
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  let _ : Setoid (RegularBase (U := E.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace) :=
    MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _
  let _ : Setoid (RegularTotalSpace F) :=
    MulAction.orbitRel Delta _
  let q₁ : RegularBase (U := E.modularParameter.toTriangleUniformization) ×
      ComplexTwoSpace → RegularTotalSpace F := quotientProjection
  let q₂ : RegularTotalSpace F → PuncturedGlobalFamily F := quotientProjection
  have hq₁ : IsOpenMap q₁ := by
    dsimp only [q₁]
    rw [quotientProjection.eq_def]
    change IsOpenMap (Quotient.mk' : _ →
      Quotient (MulAction.orbitRel (FamilyPeriodGroup (regularParameterMap F)) _))
    exact isOpenMap_quotient_mk'_mul
  have hq₂ : IsOpenMap q₂ := by
    dsimp only [q₂]
    rw [quotientProjection.eq_def]
    change IsOpenMap (Quotient.mk' : _ →
      Quotient (MulAction.orbitRel Delta (RegularTotalSpace F)))
    exact isOpenMap_quotient_mk'_mul
  have hopen := hq₂.comp (hq₁.comp (additiveCuspBundleMap_isOpenEmbedding W).isOpenMap)
  convert hopen using 1
  funext p
  rfl

public theorem additiveCuspCoverToGlobal_respects
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p q : additiveCuspRadiusCover W.localWitness.radius)
    (h : Setoid.ker (denseCuspExponentialRadius W.localWitness.radius) p q) :
    additiveCuspCoverToGlobal W p = additiveCuspCoverToGlobal W q := by
  have hdense : denseCuspExponentialCover p.1 = denseCuspExponentialCover q.1 :=
    congrArg Subtype.val h
  obtain ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂⟩ :=
    (denseCuspExponentialCover_eq_iff p.1 q.1).mp hdense
  let n : ParameterLattice := ![n₀, n₁]
  have hzeta : p.1.1 = q.1.1 + fun i ↦ (n i : ℂ) := by
    funext i
    fin_cases i
    · exact hn₀
    · exact hn₁
  have hsQ : q.1.2 ∈ cuspHalfPlane N.height :=
    additiveCuspRadiusCover_halfPlane W.localWitness.radius_le q
  have hqQ : ‖cuspQ q.1.2‖ < W.localWitness.radius := q.2
  have hsAdd : q.1.2 + n₂ ∈ cuspHalfPlane N.height :=
    cuspHalfPlane_add_int hsQ n₂
  have hqAdd : ‖cuspQ (q.1.2 + n₂)‖ < W.localWitness.radius := by
    have hc := cuspQ_add_int q.1.2 n₂
    exact congrArg norm hc ▸ hqQ
  calc
    additiveCuspCoverToGlobal W p =
        actualPuncturedGlobalCuspPoint W p.1.2
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2 q.1.1 := by
      rw [additiveCuspCoverToGlobal, hzeta]
      exact actualPuncturedGlobalCuspPoint_add_fibre_int W _ _ _ _ n
    _ = actualPuncturedGlobalCuspPoint W (q.1.2 + n₂) hsAdd hqAdd q.1.1 :=
      actualPuncturedGlobalCuspPoint_congr W _ _ _ _ _ hn₂
    _ = actualPuncturedGlobalCuspPoint W q.1.2 hsQ hqQ q.1.1 :=
      actualPuncturedGlobalCuspPoint_add_int W q.1.2 hsQ hqQ q.1.1 n₂ _ _
    _ = additiveCuspCoverToGlobal W q := rfl

/-- Descent of the normalized additive cover through its exact exponential-fibre relation. -/
public noncomputable def additiveCuspQuotientToGlobal
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Quotient (Setoid.ker (denseCuspExponentialRadius W.localWitness.radius)) →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  Quotient.lift (additiveCuspCoverToGlobal W) (additiveCuspCoverToGlobal_respects W)

public theorem additiveCuspQuotientToGlobal_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (additiveCuspQuotientToGlobal W) :=
  continuous_quot_lift (additiveCuspCoverToGlobal_respects W)
    (additiveCuspCoverToGlobal_continuous W)

public theorem additiveCuspQuotientToGlobal_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (additiveCuspQuotientToGlobal W) := by
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  convert additiveCuspCoverToGlobal_isOpenMap W using 1
  funext p
  rfl

@[simp]
public theorem additiveCuspQuotientToGlobal_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspQuotientToGlobal W (Quotient.mk _ p) =
      additiveCuspCoverToGlobal W p :=
  rfl

/-- The map descended through the exact exponential fibres is locally biholomorphic.  The proof
cancels the locally biholomorphic exponential quotient projection using its explicit local
inverse. -/
public theorem additiveCuspQuotientToGlobal_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let F := assembledFuchsianPeriodFunctions E D
    let r := W.localWitness.radius
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        E.modularParameter.toTriangleUniformization_sourceAction
    let hsource := E.modularParameter.toTriangleUniformization_sourceAction
    letI := denseTorusCharts
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
      denseTorus_isManifold
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
        (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
    letI := additiveCuspRadiusQuotientCharts r
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ)
        (additiveCuspRadiusCover r) := (additiveCuspRadiusOpen r).instChartedSpace
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a
        RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound
        (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
    let hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
      F hproper RegularSmoothnessOrder
    letI : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (RegularTotalSpace F) := hregular.1
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    letI := regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
    letI := regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
    letI := regularFamilyDeckAction_continuousConstSMul F hproper
    letI := regularCuspBundleRegionCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel) GlobalDeckTotalModel
      RegularSmoothnessOrder (additiveCuspQuotientToGlobal W) := by
  let F := assembledFuchsianPeriodFunctions E D
  let r := W.localWitness.radius
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let hsource := E.modularParameter.toTriangleUniformization_sourceAction
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorus_isManifold
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
  let _ := additiveCuspRadiusQuotientCharts r
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
    (additiveCuspRadiusOpen r).instChartedSpace
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound
      (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
  have hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    F hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace F) := hregular.1
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : IsCancelSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  let _ := regularCuspBundleRegionCharts W
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    GlobalDeckTotalModel RegularSmoothnessOrder (additiveCuspQuotientToGlobal W)
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : additiveCuspRadiusCover r →
        Quotient (Setoid.ker (denseCuspExponentialRadius r)) := Quotient.mk _
    have hπ := additiveCuspRadiusQuotient_projection_isLocalDiffeomorph r p
    let loc := hπ.localInverse
    have hloc : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
        ((modelWithCornersSelf ℂ ComplexTwoSpace).prod (modelWithCornersSelf ℂ ℂ))
        RegularSmoothnessOrder loc.toPartialEquiv.toFun (π p) := by
      simpa only [RegularSmoothnessOrder] using hπ.localInverse_isLocalDiffeomorphAt
    have hcomp : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
        GlobalDeckTotalModel RegularSmoothnessOrder
        (additiveCuspCoverToGlobal W ∘ loc.toPartialEquiv.toFun) (π p) :=
      hloc.comp GlobalDeckTotalModel (PuncturedGlobalFamily F)
        (additiveCuspCoverToGlobal_isLocalDiffeomorph W
          (loc.toPartialEquiv.toFun (π p)))
    have hright := hπ.localInverse_eventuallyEq_right
    have hevent : (additiveCuspCoverToGlobal W ∘ loc.toPartialEquiv.toFun) =ᶠ[nhds (π p)]
        additiveCuspQuotientToGlobal W := by
      filter_upwards [hright] with y hy
      calc
        additiveCuspCoverToGlobal W (loc.toPartialEquiv.toFun y) =
            additiveCuspQuotientToGlobal W (π (loc.toPartialEquiv.toFun y)) := rfl
        _ = additiveCuspQuotientToGlobal W y := congrArg _ hy
    exact isLocalDiffeomorphAt_congr_eventuallyEq_complexToGlobalDeck hcomp hevent

public theorem additiveToPuncturedLocalHomeomorph_mk
    (M : Model) (r : ℝ) (p : additiveCuspRadiusCover r) :
    ((additiveToPuncturedLocalHomeomorph M r (Quotient.mk _ p)).1 :
      LocalCarrier M r) =
      localCuspExponentialPoint M r p.1.1 p.1.2
        (mem_ball_zero_iff.mpr p.2) := by
  apply Subtype.ext
  rfl

/-- The analytic and topological constructions of the exact exponential quotient collar have
the same underlying map. -/
public theorem additiveToPuncturedLocalDiffeomorph_apply
    (M : Model) (r : ℝ)
    (q : Quotient (Setoid.ker (denseCuspExponentialRadius r))) :
    letI := denseTorusCharts
    letI := M.topology
    letI := M.charts
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
        (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
    letI := additiveCuspRadiusQuotientCharts r
    (additiveToPuncturedLocalDiffeomorph M r).toEquiv q =
      additiveToPuncturedLocalHomeomorph M r q := by
  let _ := denseTorusCharts
  let _ := M.topology
  let _ := M.charts
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
  let _ := additiveCuspRadiusQuotientCharts r
  induction q using Quotient.inductionOn with
  | _ p =>
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- Before dividing by the phase-corrected parameter-lattice action, the punctured local toric
carrier maps continuously to the global cusp collar. -/
public noncomputable def puncturedLocalCuspPrequotientMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  additiveCuspQuotientToGlobal W ∘
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).symm

/-- The punctured actual toric carrier maps locally biholomorphically to the global cusp collar
before the parameter-lattice quotient. -/
public theorem puncturedLocalCuspPrequotientMap_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let F := assembledFuchsianPeriodFunctions E D
    let r := W.localWitness.radius
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        E.modularParameter.toTriangleUniformization_sourceAction
    let hsource := E.modularParameter.toTriangleUniformization_sourceAction
    letI := M.topology
    letI := M.charts
    letI : ChartedSpace ComplexModel {p : LocalCarrier M r // M.t p ≠ 0} :=
      (puncturedLocalCarrierOpen M r).instChartedSpace
    letI := denseTorusCharts
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
      denseTorus_isManifold
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
        (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
    letI := additiveCuspRadiusQuotientCharts r
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ)
        (additiveCuspRadiusCover r) := (additiveCuspRadiusOpen r).instChartedSpace
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a
        RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound
        (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
    let hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
      F hproper RegularSmoothnessOrder
    letI : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (RegularTotalSpace F) := hregular.1
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    letI := regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
    letI := regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
    letI := regularFamilyDeckAction_continuousConstSMul F hproper
    letI := regularCuspBundleRegionCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel) GlobalDeckTotalModel
      RegularSmoothnessOrder (puncturedLocalCuspPrequotientMap W) := by
  let F := assembledFuchsianPeriodFunctions E D
  let r := W.localWitness.radius
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let hsource := E.modularParameter.toTriangleUniformization_sourceAction
  let _ := M.topology
  let _ := M.charts
  let _ : ChartedSpace ComplexModel {p : LocalCarrier M r // M.t p ≠ 0} :=
    (puncturedLocalCarrierOpen M r).instChartedSpace
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorus_isManifold
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
  let _ := additiveCuspRadiusQuotientCharts r
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
    (additiveCuspRadiusOpen r).instChartedSpace
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound
      (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
  have hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    F hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace F) := hregular.1
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : IsCancelSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  let _ := regularCuspBundleRegionCharts W
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    GlobalDeckTotalModel RegularSmoothnessOrder (puncturedLocalCuspPrequotientMap W)
  let d : Quotient (Setoid.ker (denseCuspExponentialRadius r))
      ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
        (modelWithCornersSelf ℂ ComplexModel)⟯
        {p : LocalCarrier M r // M.t p ≠ 0} :=
    additiveToPuncturedLocalDiffeomorph M r
  let e := additiveToPuncturedLocalHomeomorph M r
  have hinv : (fun p ↦ d.symm.toEquiv p) = e.symm := by
    funext p
    apply d.toEquiv.injective
    calc
      d.toEquiv (d.symm.toEquiv p) = p := d.toEquiv.apply_symm_apply p
      _ = d.toEquiv (e.symm p) := by
        change p = (additiveToPuncturedLocalDiffeomorph M r).toEquiv (e.symm p)
        rw [additiveToPuncturedLocalDiffeomorph_apply]
        exact (e.apply_symm_apply p).symm
  have hcomp : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      GlobalDeckTotalModel RegularSmoothnessOrder
      (additiveCuspQuotientToGlobal W ∘ fun p ↦ d.symm.toEquiv p) := by
    intro p
    exact (d.symm.isLocalDiffeomorph p).comp GlobalDeckTotalModel
      (PuncturedGlobalFamily F)
      (additiveCuspQuotientToGlobal_isLocalDiffeomorph W (d.symm.toEquiv p))
  have heq : (additiveCuspQuotientToGlobal W ∘ fun p ↦ d.symm.toEquiv p) =
      puncturedLocalCuspPrequotientMap W := by
    rw [hinv]
    rfl
  rwa [heq] at hcomp

public theorem puncturedLocalCuspPrequotientMap_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedLocalCuspPrequotientMap W) :=
  (additiveCuspQuotientToGlobal_continuous W).comp
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).symm.continuous

public theorem puncturedLocalCuspPrequotientMap_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (puncturedLocalCuspPrequotientMap W) :=
  (additiveCuspQuotientToGlobal_isOpenMap W).comp
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).symm.isOpenMap

/-- The actual phase-corrected action restricted to the punctured local carrier. -/
public noncomputable def puncturedPsiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (lambda : ParameterLattice) :
    {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} →
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
  fun p ↦ ⟨
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le).psiMap
        lambda p.1,
    by
      rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_preserves_t]
      exact p.2⟩

/-- The prequotient map is invariant under the actual phase-corrected parameter-lattice
action. -/
public theorem puncturedLocalCuspPrequotientMap_psiMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (lambda : ParameterLattice)
    (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    puncturedLocalCuspPrequotientMap W (puncturedPsiMap W lambda p) =
      puncturedLocalCuspPrequotientMap W p := by
  let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
  obtain ⟨q, rfl⟩ := e.surjective p
  induction q using Quotient.inductionOn with
  | _ a =>
    let zeta' :=
      (periodBlock (periodValues
        (assembledFuchsianPeriodFunctions E D).tau
        (assembledFuchsianPeriodFunctions E D).mu
        (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2))).mulVec
          (fun i ↦ (lambda i : ℂ)) + a.1.1
    let a' : additiveCuspRadiusCover W.localWitness.radius :=
      ⟨(zeta', a.1.2), by exact a.2⟩
    have hlocal : puncturedPsiMap W lambda (e (Quotient.mk _ a)) =
        e (Quotient.mk _ a') := by
      apply Subtype.ext
      change
        (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
            N M W.localWitness.radius W.localWitness.radius_pos
              W.localWitness.radius_le).psiMap lambda (e (Quotient.mk _ a)).1 =
          (e (Quotient.mk _ a')).1
      rw [show ((e (Quotient.mk _ a)).1 : LocalCarrier M W.localWitness.radius) =
          localCuspExponentialPoint M W.localWitness.radius a.1.1 a.1.2
            (mem_ball_zero_iff.mpr a.2) from
        additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius a,
        show ((e (Quotient.mk _ a')).1 : LocalCarrier M W.localWitness.radius) =
          localCuspExponentialPoint M W.localWitness.radius a'.1.1 a'.1.2
            (mem_ball_zero_iff.mpr a'.2) from
        additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius a']
      exact localCuspExponentialPoint_period_equivariant N M
        W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
        a.1.2 (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)
        (mem_ball_zero_iff.mpr a.2) a.1.1 lambda
    rw [hlocal]
    dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e]
    rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
    rw [additiveCuspQuotientToGlobal_mk, additiveCuspQuotientToGlobal_mk]
    exact actualPuncturedGlobalCuspPoint_periodBlock W a.1.2
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2 a.1.1 lambda

/-- The actual local cusp action on the complement of the central fibre. -/
@[instance_reducible] public noncomputable def puncturedPsiAction
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction (Multiplicative ParameterLattice)
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} where
  smul lambda p := puncturedPsiMap W (Multiplicative.toAdd lambda) p
  one_smul p := by
    apply Subtype.ext
    exact CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_zero _ _
  mul_smul lambda mu p := by
    apply Subtype.ext
    exact CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_add
      _ (Multiplicative.toAdd lambda) (Multiplicative.toAdd mu) p.1

/-- The orbit relation of the phase-corrected action on the punctured local carrier. -/
public noncomputable def puncturedPsiOrbitRel
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Setoid {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
  letI := puncturedPsiAction W
  MulAction.orbitRel (Multiplicative ParameterLattice) _

/-- The punctured part of the actual local cusp quotient. -/
public noncomputable abbrev puncturedLocalCuspQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :=
  Quotient (puncturedPsiOrbitRel W)

/-- The connected additive radius cover surjects onto the punctured phase quotient. -/
public noncomputable def additiveCuspRadiusToPuncturedLocalCuspQuotient
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    additiveCuspRadiusCover W.localWitness.radius → puncturedLocalCuspQuotient W :=
  fun a ↦ Quotient.mk _
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ a))

public theorem additiveCuspRadiusToPuncturedLocalCuspQuotient_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (additiveCuspRadiusToPuncturedLocalCuspQuotient W) :=
  continuous_quot_mk.comp
    ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius).continuous.comp
      continuous_quot_mk)

public theorem additiveCuspRadiusToPuncturedLocalCuspQuotient_surjective
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Function.Surjective (additiveCuspRadiusToPuncturedLocalCuspQuotient W) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    obtain ⟨u, rfl⟩ :=
      (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).surjective p
    induction u using Quotient.inductionOn with
    | _ a => exact ⟨a, rfl⟩

public theorem puncturedLocalCuspQuotient_connected
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ConnectedSpace (puncturedLocalCuspQuotient W) := by
  let _ : ConnectedSpace (additiveCuspRadiusCover W.localWitness.radius) :=
    additiveCuspRadiusCover_connected W.localWitness.radius_pos
  exact (additiveCuspRadiusToPuncturedLocalCuspQuotient_surjective W).connectedSpace
    (additiveCuspRadiusToPuncturedLocalCuspQuotient_continuous W)

/-- The noncentral torus locus remains dense after restriction to an open cusp neighborhood. -/
public theorem puncturedLocalCarrier_dense (M : Model) (r : ℝ) :
    Dense {p : LocalCarrier M r | M.t p ≠ 0} := by
  have hdense : Dense {p : M.Carrier | M.t p ≠ 0} := by
    rw [← M.torus_range]
    exact M.torus_dense
  change Dense (Subtype.val ⁻¹' {p : M.Carrier | M.t p ≠ 0})
  exact hdense.preimage (cuspNeighborhood M r).isOpen.isOpenMap_subtype_val

/-- The actual phase-corrected action on the full local toric cusp, including its central
fibre. -/
@[instance_reducible] public noncomputable def actualLocalPsiAction
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) where
  smul lambda p :=
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le).psiMap
        (Multiplicative.toAdd lambda) p
  one_smul p :=
    CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_zero _ p
  mul_smul lambda mu p :=
    CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_add _
      (Multiplicative.toAdd lambda) (Multiplicative.toAdd mu) p

public noncomputable def actualLocalPsiOrbitRel
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Setoid (LocalCarrier M W.localWitness.radius) :=
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  letI := (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  MulAction.orbitRel (Multiplicative ParameterLattice) _

/-- The full actual local cusp filling at the common quantitative radius. -/
public noncomputable abbrev actualLocalCuspFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :=
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  letI := (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  MulAction.orbitRel.Quotient (Multiplicative ParameterLattice)
    (LocalCarrier M W.localWitness.radius)

/-- The norm of the toric cusp coordinate is constant on the full local phase action. -/
public theorem actualLocalCuspFillingRadius_respects
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p q : LocalCarrier M W.localWitness.radius)
    (h : actualLocalPsiOrbitRel W p q) :
    ‖M.t p‖ = ‖M.t q‖ := by
  rw [actualLocalPsiOrbitRel] at h
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨lambda, hlambda⟩ := h
  rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl,
    (C.toCuspActionData W.localWitness.fixedPoint).psi_smul] at hlambda
  rw [← hlambda, ← C.psiMap_eq_generic W.localWitness.fixedPoint,
    CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_preserves_t]

/-- Radial coordinate on the full actual local cusp filling. -/
public noncomputable def actualLocalCuspFillingRadius
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    actualLocalCuspFilling W → ℝ := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  exact Quotient.lift (fun p ↦ ‖M.t p‖)
    (actualLocalCuspFillingRadius_respects W)

@[simp]
public theorem actualLocalCuspFillingRadius_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : LocalCarrier M W.localWitness.radius) :
    actualLocalCuspFillingRadius W (Quotient.mk _ p) = ‖M.t p‖ := by
  rw [actualLocalCuspFillingRadius.eq_def]
  rfl

/-- The descended cusp-filling radius is continuous. -/
public theorem actualLocalCuspFillingRadius_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (actualLocalCuspFillingRadius W) := by
  rw [actualLocalCuspFillingRadius.eq_def]
  exact continuous_quot_lift (actualLocalCuspFillingRadius_respects W)
    (continuous_norm.comp
      (M.t_holomorphic.continuous.comp continuous_subtype_val))

/-- The descended cusp-filling radius is nonnegative. -/
public theorem actualLocalCuspFillingRadius_nonneg
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (Q : actualLocalCuspFilling W) :
    0 ≤ actualLocalCuspFillingRadius W Q := by
  induction Q using Quotient.inductionOn with
  | _ p =>
      rw [actualLocalCuspFillingRadius_mk]
      exact norm_nonneg _

/-- The compact component indexed by zero, regarded as a subset of the open local cusp
carrier. -/
public def actualLocalCuspZeroComponent
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set (LocalCarrier M W.localWitness.radius) :=
  {p | (p : M.Carrier) ∈ M.centralComponent 0}

/-- The distinguished local central component remains compact after restriction to the open
cusp carrier. -/
public theorem actualLocalCuspZeroComponent_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsCompact (actualLocalCuspZeroComponent W) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have heq : Subtype.val '' actualLocalCuspZeroComponent W = M.centralComponent 0 := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      have hzero : M.t p = 0 := by
        have hpzero : p ∈ M.t ⁻¹' {0} := by
          rw [M.centralFiber_eq_iUnion]
          exact Set.mem_iUnion.2 ⟨0, hp⟩
        exact hpzero
      let q : LocalCarrier M W.localWitness.radius := ⟨p, by
        rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff, hzero, norm_zero]
        exact W.localWitness.radius_pos⟩
      exact ⟨q, hp, rfl⟩
  rw [heq]
  exact compact_centralComponent M 0

/-- The zero-radius fibre of the actual cusp filling is exactly the quotient image of one
compact toric component. -/
public theorem actualLocalCuspFilling_zeroFiber_eq_image_zeroComponent
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    actualLocalCuspFillingRadius W ⁻¹' {0} =
      (Quotient.mk _ : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) '' actualLocalCuspZeroComponent W := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  ext Q
  induction Q using Quotient.inductionOn with
  | _ p =>
      constructor
      · intro hzero
        change actualLocalCuspFillingRadius W (Quotient.mk _ p) = 0 at hzero
        rw [actualLocalCuspFillingRadius_mk] at hzero
        have ht : M.t p = 0 := norm_eq_zero.mp hzero
        obtain ⟨lambda, hlambda⟩ := central_orbit_meets_zero_component
          M C M.toTorusActionPreservesComponents p ht
        let q : LocalCarrier M W.localWitness.radius := C.psiMap lambda p
        refine ⟨q, hlambda, ?_⟩
        have hrel : MulAction.orbitRel (Multiplicative ParameterLattice)
            (LocalCarrier M W.localWitness.radius) q p := by
          rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
          refine ⟨Multiplicative.ofAdd lambda, ?_⟩
          rw [(C.toCuspActionData W.localWitness.fixedPoint).psi_smul,
            ← C.psiMap_eq_generic W.localWitness.fixedPoint]
        exact Quotient.sound hrel
      · rintro ⟨q, hq, hqp⟩
        change actualLocalCuspFillingRadius W (Quotient.mk _ p) = 0
        rw [← hqp, actualLocalCuspFillingRadius_mk]
        have hqzero : M.t q = 0 := by
          have hmem : (q : M.Carrier) ∈ M.t ⁻¹' {0} := by
            rw [M.centralFiber_eq_iUnion]
            exact Set.mem_iUnion.2 ⟨0, hq⟩
          exact hmem
        rw [hqzero, norm_zero]

/-- The entire central fibre of the actual local cusp quotient is compact. -/
public theorem actualLocalCuspFilling_zeroFiber_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsCompact (actualLocalCuspFillingRadius W ⁻¹' {0}) := by
  rw [actualLocalCuspFilling_zeroFiber_eq_image_zeroComponent W]
  exact (actualLocalCuspZeroComponent_isCompact W).image continuous_quot_mk

/-- A compact set of local representatives for a closed radial sublevel: the distinguished
central component together with the finitely many bounded-index unit polydiscs. -/
public def actualLocalCuspCompactRepresentatives
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (R : ℝ) :
    Set (LocalCarrier M W.localWitness.radius) :=
  actualLocalCuspZeroComponent W ∪
    {p | (p : M.Carrier) ∈ boundedClosedUnitToricPolydiscs M 7 ∧ ‖M.t p‖ ≤ R}

public theorem actualLocalCuspCompactRepresentatives_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) {R : ℝ}
    (hR : R < W.localWitness.radius) :
    IsCompact (actualLocalCuspCompactRepresentatives W R) := by
  apply (actualLocalCuspZeroComponent_isCompact W).union
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have heq : Subtype.val ''
      {p : LocalCarrier M W.localWitness.radius |
        (p : M.Carrier) ∈ boundedClosedUnitToricPolydiscs M 7 ∧ ‖M.t p‖ ≤ R} =
      boundedClosedUnitToricPolydiscs M 7 ∩ {p | ‖M.t p‖ ≤ R} := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · rintro ⟨hpbounded, hpR⟩
      let q : LocalCarrier M W.localWitness.radius := ⟨p, by
        rw [mem_cuspNeighborhood_iff, mem_ball_zero_iff]
        exact hpR.trans_lt hR⟩
      exact ⟨q, ⟨hpbounded, hpR⟩, rfl⟩
  rw [heq]
  exact (compact_boundedClosedUnitToricPolydiscs M 7).inter_right
    (isClosed_le (continuous_norm.comp M.t_holomorphic.continuous) continuous_const)

/-- Every local point in a closed radial sublevel has an orbit representative in the fixed
compact representative set. -/
public theorem exists_orbit_mem_actualLocalCuspCompactRepresentatives
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) {R : ℝ}
    (p : LocalCarrier M W.localWitness.radius) (hpR : ‖M.t p‖ ≤ R) :
    ∃ q ∈ actualLocalCuspCompactRepresentatives W R,
      (Quotient.mk _ q : actualLocalCuspFilling W) = Quotient.mk _ p := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  by_cases hp : M.t p = 0
  · obtain ⟨lambda, hlambda⟩ := central_orbit_meets_zero_component
      M C M.toTorusActionPreservesComponents p hp
    let q : LocalCarrier M W.localWitness.radius := C.psiMap lambda p
    refine ⟨q, Or.inl hlambda, ?_⟩
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) q p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨Multiplicative.ofAdd lambda, ?_⟩
    rw [(C.toCuspActionData W.localWitness.fixedPoint).psi_smul,
      ← C.psiMap_eq_generic W.localWitness.fixedPoint]
  · obtain ⟨lambda, hlambda⟩ := W.localWitness.exists_psiMap_positionL1_le_five p hp
    let q : LocalCarrier M W.localWitness.radius := C.psiMap lambda p
    have hqt : M.t q ≠ 0 := by
      rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_preserves_t]
      exact hp
    have hqnorm : ‖M.t q‖ < 1 := by
      exact (mem_ball_zero_iff.mp q.property).trans W.localWitness.radius_lt_one
    obtain ⟨upper, v, hqchart, hqcoord, hv⟩ :=
      exists_closedUnitToricPolydisc_with_index_bound M hqt hqnorm hlambda
    have hqbounded : (q : M.Carrier) ∈ boundedClosedUnitToricPolydiscs M 7 := by
      apply Set.mem_iUnion.2
      refine ⟨(upper, v), Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
      · change latticeL1 v ≤ 7
        norm_num at hv ⊢
        exact hv
      rw [closedToricPolydisc_eq]
      exact ⟨hqchart, hqcoord⟩
    have hqR : ‖M.t q‖ ≤ R := by
      rw [CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_preserves_t]
      exact hpR
    refine ⟨q, Or.inr ⟨hqbounded, hqR⟩, ?_⟩
    apply Quotient.sound
    change MulAction.orbitRel (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) q p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨Multiplicative.ofAdd lambda, ?_⟩
    rw [(C.toCuspActionData W.localWitness.fixedPoint).psi_smul,
      ← C.psiMap_eq_generic W.localWitness.fixedPoint]

/-- Every proper closed radial sublevel of the actual local cusp filling is compact. -/
public theorem actualLocalCuspFilling_sublevel_isCompact
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) {R : ℝ}
    (hRnonneg : 0 ≤ R) (hR : R < W.localWitness.radius) :
    IsCompact (actualLocalCuspFillingRadius W ⁻¹' Set.Iic R) := by
  have heq : actualLocalCuspFillingRadius W ⁻¹' Set.Iic R =
      (Quotient.mk _ : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) '' actualLocalCuspCompactRepresentatives W R := by
    ext Q
    induction Q using Quotient.inductionOn with
    | _ p =>
        constructor
        · intro hpR
          change actualLocalCuspFillingRadius W (Quotient.mk _ p) ≤ R at hpR
          rw [actualLocalCuspFillingRadius_mk] at hpR
          exact exists_orbit_mem_actualLocalCuspCompactRepresentatives W p hpR
        · rintro ⟨q, hq, hqp⟩
          change actualLocalCuspFillingRadius W (Quotient.mk _ p) ≤ R
          rw [← hqp, actualLocalCuspFillingRadius_mk]
          rcases hq with hqzero | hqbounded
          · have ht : M.t q = 0 := by
              have hmem : (q : M.Carrier) ∈ M.t ⁻¹' {0} := by
                rw [M.centralFiber_eq_iUnion]
                exact Set.mem_iUnion.2 ⟨0, hqzero⟩
              exact hmem
            rw [ht, norm_zero]
            exact hRnonneg
          · exact hqbounded.2
  rw [heq]
  exact (actualLocalCuspCompactRepresentatives_isCompact W hR).image continuous_quot_mk

/-- The full local cusp filling is Hausdorff: it is the quotient of the Hausdorff local toric
carrier by the properly discontinuous phase action supplied by the quantitative witness. -/
public theorem actualLocalCuspFilling_t2
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    T2Space (actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := ⟨by
    intro lambda
    rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl]
    change Continuous ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
      (Multiplicative.toAdd lambda))
    exact (C.genericPsiMap_holomorphic W.localWitness.fixedPoint _).continuous⟩
  let _ : ProperlyDiscontinuousSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    C.properlyDiscontinuous W.localWitness.fixedPoint W.localWitness.compactOverlap
  let _ : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel M.Carrier
  let _ : LocallyCompactSpace (LocalCarrier M W.localWitness.radius) :=
    (cuspNeighborhood M W.localWitness.radius).isOpen.locallyCompactSpace
  let _ : T2Space (LocalCarrier M W.localWitness.radius) := by infer_instance
  infer_instance

/-- The norm of the toric cusp coordinate is constant on the punctured local phase action. -/
public theorem puncturedLocalCuspRadius_respects
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p q : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0})
    (h : puncturedPsiOrbitRel W p q) :
    ‖M.t p.1‖ = ‖M.t q.1‖ := by
  rw [puncturedPsiOrbitRel] at h
  let _ : MulAction (Multiplicative ParameterLattice)
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} := puncturedPsiAction W
  change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at h
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  obtain ⟨lambda, hlambda⟩ := h
  change puncturedPsiMap W (Multiplicative.toAdd lambda) q = p at hlambda
  calc
    ‖M.t p.1‖ = ‖M.t (puncturedPsiMap W (Multiplicative.toAdd lambda) q).1‖ :=
      congrArg (fun x ↦ ‖M.t x.1‖) hlambda.symm
    _ = ‖M.t q.1‖ := by
      rw [puncturedPsiMap,
        CuspLocalPhaseAction.ExactLocalHolomorphicPhaseCoefficients.psiMap_preserves_t]

/-- Radial coordinate on the punctured actual cusp collar quotient. -/
public noncomputable def puncturedLocalCuspRadius
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    puncturedLocalCuspQuotient W → ℝ :=
  Quotient.lift (fun p ↦ ‖M.t p.1‖) (puncturedLocalCuspRadius_respects W)

@[simp]
public theorem puncturedLocalCuspRadius_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    puncturedLocalCuspRadius W (Quotient.mk _ p) = ‖M.t p.1‖ := by
  rw [puncturedLocalCuspRadius.eq_def]
  rfl

/-- The descended punctured cusp-collar radius is continuous. -/
public theorem puncturedLocalCuspRadius_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedLocalCuspRadius W) := by
  rw [puncturedLocalCuspRadius.eq_def]
  exact continuous_quot_lift (puncturedLocalCuspRadius_respects W)
    (continuous_norm.comp
      (M.t_holomorphic.continuous.comp
        (continuous_subtype_val.comp continuous_subtype_val)))

/-- Inclusion of the punctured collar quotient into the full local cusp filling. -/
public noncomputable def puncturedLocalCuspToFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    puncturedLocalCuspQuotient W → actualLocalCuspFilling W :=
  Quotient.lift (fun p ↦ Quotient.mk _ p.1) (by
    intro p q h
    let _ : MulAction (Multiplicative ParameterLattice)
        {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} := puncturedPsiAction W
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨lambda, hlambda⟩ := h
    apply Quotient.sound
    let C :=
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    let _ : MulAction (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius) :=
      (C.toCuspActionData W.localWitness.fixedPoint).psiAction
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p.1 q.1
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    refine ⟨lambda, ?_⟩
    change puncturedPsiMap W (Multiplicative.toAdd lambda) q = p at hlambda
    rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl,
      (C.toCuspActionData W.localWitness.fixedPoint).psi_smul,
      ← C.psiMap_eq_generic W.localWitness.fixedPoint]
    exact congrArg Subtype.val hlambda)

@[simp]
public theorem puncturedLocalCuspToFilling_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    puncturedLocalCuspToFilling W (Quotient.mk _ p) = Quotient.mk _ p.1 :=
  rfl

/-- The punctured and filled cusp radii agree under the filling-side collar map. -/
public theorem actualLocalCuspFillingRadius_puncturedLocalCuspToFilling
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (Q : puncturedLocalCuspQuotient W) :
    actualLocalCuspFillingRadius W (puncturedLocalCuspToFilling W Q) =
      puncturedLocalCuspRadius W Q := by
  induction Q using Quotient.inductionOn with
  | _ p =>
      rw [puncturedLocalCuspToFilling_mk,
        actualLocalCuspFillingRadius_mk, puncturedLocalCuspRadius_mk]

public theorem puncturedLocalCuspToFilling_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedLocalCuspToFilling W) :=
  continuous_quot_lift _ (continuous_quot_mk.comp continuous_subtype_val)

public theorem puncturedLocalCuspToFilling_injective
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Function.Injective (puncturedLocalCuspToFilling W) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q =>
      apply Quotient.sound
      have hrel := Quotient.exact hxy
      let C :=
        CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
          N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
      let _ : MulAction (Multiplicative ParameterLattice)
          (LocalCarrier M W.localWitness.radius) :=
        (C.toCuspActionData W.localWitness.fixedPoint).psiAction
      change MulAction.orbitRel (Multiplicative ParameterLattice) _ p.1 q.1 at hrel
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
      obtain ⟨lambda, hlambda⟩ := hrel
      rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl,
        (C.toCuspActionData W.localWitness.fixedPoint).psi_smul] at hlambda
      let _ : MulAction (Multiplicative ParameterLattice)
          {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} := puncturedPsiAction W
      change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
      refine ⟨lambda, ?_⟩
      apply Subtype.ext
      exact (C.psiMap_eq_generic W.localWitness.fixedPoint _ _).trans hlambda

public theorem puncturedLocalCuspToFilling_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (puncturedLocalCuspToFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) := ⟨by
    intro lambda
    rw [show lambda = Multiplicative.ofAdd (Multiplicative.toAdd lambda) from rfl]
    change Continuous ((C.toCuspActionData W.localWitness.fixedPoint).psiMap
      (Multiplicative.toAdd lambda))
    exact (C.genericPsiMap_holomorphic W.localWitness.fixedPoint _).continuous⟩
  let _ : Setoid (LocalCarrier M W.localWitness.radius) :=
    MulAction.orbitRel (Multiplicative ParameterLattice) _
  have ht : Continuous (fun p : LocalCarrier M W.localWitness.radius ↦ M.t p) :=
    M.t_holomorphic.continuous.comp continuous_subtype_val
  have hopen : IsOpen {p : LocalCarrier M W.localWitness.radius | M.t p ≠ 0} :=
    isOpen_compl_singleton.preimage ht
  have hpre : IsOpenMap (fun p :
      {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} ↦
        (Quotient.mk _ p.1 : actualLocalCuspFilling W)) := by
    have hquot : IsOpenMap (Quotient.mk' : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) := isOpenMap_quotient_mk'_mul
    exact hquot.comp hopen.isOpenMap_subtype_val
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  convert hpre using 1
  funext p
  rfl

public theorem puncturedLocalCuspToFilling_isOpenEmbedding
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenEmbedding (puncturedLocalCuspToFilling W) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (puncturedLocalCuspToFilling_continuous W)
    (puncturedLocalCuspToFilling_injective W)
    (puncturedLocalCuspToFilling_isOpenMap W)

/-- The punctured collar in the full local cusp filling. -/
public def actualLocalCuspFillingCollar
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set (actualLocalCuspFilling W) :=
  Set.range (puncturedLocalCuspToFilling W)

public theorem actualLocalCuspFillingCollar_isOpen
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpen (actualLocalCuspFillingCollar W) :=
  (puncturedLocalCuspToFilling_isOpenEmbedding W).isOpen_range

public theorem actualLocalCuspFillingCollar_eq_image
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    actualLocalCuspFillingCollar W =
      (Quotient.mk _ : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) ''
        {p : LocalCarrier M W.localWitness.radius | M.t p ≠ 0} := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.inductionOn with
    | _ p => exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨Quotient.mk _ ⟨p, hp⟩, rfl⟩

/-- The punctured filling collar is exactly the positive-radius locus of the full cusp filling. -/
public theorem actualLocalCuspFillingCollar_eq_positiveRadius
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    actualLocalCuspFillingCollar W =
      {Q | 0 < actualLocalCuspFillingRadius W Q} := by
  ext Q
  induction Q using Quotient.inductionOn with
  | _ p =>
    constructor
    · intro h
      rw [actualLocalCuspFillingCollar_eq_image W] at h
      obtain ⟨q, hq, hqp⟩ := h
      change 0 < actualLocalCuspFillingRadius W (Quotient.mk _ p)
      rw [← hqp, actualLocalCuspFillingRadius_mk]
      exact norm_pos_iff.mpr hq
    · intro h
      rw [actualLocalCuspFillingCollar_eq_image W]
      refine ⟨p, ?_, rfl⟩
      change 0 < actualLocalCuspFillingRadius W (Quotient.mk _ p) at h
      rw [actualLocalCuspFillingRadius_mk] at h
      exact norm_pos_iff.mp h

/-- The punctured collar is dense in the full local cusp filling. -/
public theorem actualLocalCuspFillingCollar_dense
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Dense (actualLocalCuspFillingCollar W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let π : LocalCarrier M W.localWitness.radius → actualLocalCuspFilling W := Quotient.mk _
  have hπ : DenseRange π := Quotient.mk_surjective.denseRange
  have himage := hπ.dense_image continuous_quot_mk
    (puncturedLocalCarrier_dense M W.localWitness.radius)
  rw [actualLocalCuspFillingCollar_eq_image W]
  exact himage

/-- The full local cusp filling is connected because its punctured collar is connected and
dense. -/
public theorem actualLocalCuspFilling_connected
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ConnectedSpace (actualLocalCuspFilling W) := by
  let _ : ConnectedSpace (puncturedLocalCuspQuotient W) :=
    puncturedLocalCuspQuotient_connected W
  have hcollar : IsConnected (actualLocalCuspFillingCollar W) := by
    exact isConnected_range (puncturedLocalCuspToFilling_continuous W)
  have hclosure := hcollar.closure
  rw [(actualLocalCuspFillingCollar_dense W).closure_eq] at hclosure
  exact connectedSpace_iff_univ.mpr hclosure

/-- The quotient atlas on the full local cusp filling. -/
@[instance_reducible]
public noncomputable def actualLocalCuspFillingCharts
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ChartedSpace ComplexModel (actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let hf := W.localWitness.quotient_isQuotientCoveringMap
  exact hf.isCoveringMap.isLocalHomeomorph.chartedSpace hf.surjective

public theorem actualLocalCuspFilling_isManifold
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := actualLocalCuspFillingCharts W
    IsManifold (modelWithCornersSelf ℂ ComplexModel)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) (actualLocalCuspFilling W) := by
  let _ := actualLocalCuspFillingCharts W
  exact W.localWitness.quotient_isManifold

public theorem actualLocalCuspFilling_projection_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := actualLocalCuspFillingCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (Quotient.mk _ : LocalCarrier M W.localWitness.radius →
        actualLocalCuspFilling W) := by
  let C :=
    CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
      N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
  let _ : MulAction (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    (C.toCuspActionData W.localWitness.fixedPoint).psiAction
  let _ : LocallyCompactSpace M.Carrier :=
    ChartedSpace.locallyCompactSpace ComplexModel M.Carrier
  let _ : LocallyCompactSpace (LocalCarrier M W.localWitness.radius) :=
    (cuspNeighborhood M W.localWitness.radius).isOpen.locallyCompactSpace
  let hf := W.localWitness.quotient_isQuotientCoveringMap
  let hdeck : ∀ gamma : Multiplicative ParameterLattice,
      ContMDiff (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : LocalCarrier M W.localWitness.radius ↦ gamma • p) := by
    intro gamma
    convert C.genericPsiMap_holomorphic W.localWitness.fixedPoint
      (Multiplicative.toAdd gamma) using 1
    funext p
    exact (C.toCuspActionData W.localWitness.fixedPoint).psi_smul
      (Multiplicative.toAdd gamma) p
  let _ : ContinuousConstSMul (Multiplicative ParameterLattice)
      (LocalCarrier M W.localWitness.radius) :=
    ⟨fun gamma ↦ (hdeck gamma).continuous⟩
  let _ := actualLocalCuspFillingCharts W
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel)
      (↑(⊤ : ℕ∞) : WithTop ℕ∞)
      (actualLocalCuspFilling W) := actualLocalCuspFilling_isManifold W
  exact CuspFilling.quotient_projection_isLocalDiffeomorph
    (modelWithCornersSelf ℂ ComplexModel) hf hdeck

/-- Complex charts on the punctured local cusp quotient, transported from its open image in the
actual toric filling.  This is the collar-source atlas used to compare both attaching maps. -/
@[instance_reducible]
public noncomputable def puncturedLocalCuspQuotientCharts
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ChartedSpace ComplexModel (puncturedLocalCuspQuotient W) := by
  let _ := actualLocalCuspFillingCharts W
  let V : TopologicalSpace.Opens (actualLocalCuspFilling W) :=
    ⟨Set.range (puncturedLocalCuspToFilling W),
      (puncturedLocalCuspToFilling_isOpenEmbedding W).isOpen_range⟩
  let e : puncturedLocalCuspQuotient W ≃ₜ V :=
    (puncturedLocalCuspToFilling_isOpenEmbedding W).isEmbedding.toHomeomorph
  exact transportChartedSpace e.symm

/-- For the transported collar-source atlas, inclusion of the punctured cusp quotient into the
full toric filling is locally biholomorphic. -/
public theorem puncturedLocalCuspToFilling_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    letI := puncturedLocalCuspQuotientCharts W
    letI := actualLocalCuspFillingCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞
      (puncturedLocalCuspToFilling W) := by
  let _ := actualLocalCuspFillingCharts W
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (actualLocalCuspFilling W) := actualLocalCuspFilling_isManifold W
  let V : TopologicalSpace.Opens (actualLocalCuspFilling W) :=
    ⟨Set.range (puncturedLocalCuspToFilling W),
      (puncturedLocalCuspToFilling_isOpenEmbedding W).isOpen_range⟩
  let e : puncturedLocalCuspQuotient W ≃ₜ V :=
    (puncturedLocalCuspToFilling_isOpenEmbedding W).isEmbedding.toHomeomorph
  let _ := puncturedLocalCuspQuotientCharts W
  let dback : V ≃ₘ^∞⟮(modelWithCornersSelf ℂ ComplexModel),
      (modelWithCornersSelf ℂ ComplexModel)⟯ puncturedLocalCuspQuotient W :=
    transportDiffeomorph e.symm
  let d := dback.symm
  have hval : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (Subtype.val : V →
        actualLocalCuspFilling W) := by
    intro y
    let _ : Nonempty V := ⟨y⟩
    let inc := V.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty V)
    let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) V (actualLocalCuspFilling W) ∞ :=
      { toPartialEquiv := inc.toPartialEquiv
        open_source := inc.open_source
        open_target := inc.open_target
        contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
        contMDiffOn_invFun := by
          intro z hz
          apply (ContMDiffWithinAt.subtypeVal_comp_iff V _ inc.target z).mp
          apply contMDiffAt_id.contMDiffWithinAt.congr_of_mem _ hz
          intro u hu
          change inc (inc.symm u) = u
          exact inc.right_inv hu }
    have hy : y ∈ Φ.source := by
      simp [Φ, inc]
    have hΦ := Φ.isLocalDiffeomorphAt
      (modelWithCornersSelf ℂ ComplexModel) (modelWithCornersSelf ℂ ComplexModel) ∞ hy
    have heq : (Φ : V → actualLocalCuspFilling W) = Subtype.val := by
      funext z
      rfl
    rwa [heq] at hΦ
  have hcomp : IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) ∞ (Subtype.val ∘ d) := by
    intro x
    exact (d.isLocalDiffeomorph x).comp (modelWithCornersSelf ℂ ComplexModel)
      (actualLocalCuspFilling W) (hval (d x))
  have heq : (Subtype.val ∘ d) = puncturedLocalCuspToFilling W := by
    funext x
    change ((e x : V) : actualLocalCuspFilling W) = puncturedLocalCuspToFilling W x
    exact Topology.IsEmbedding.toHomeomorph_apply_coe
      (puncturedLocalCuspToFilling_isOpenEmbedding W).isEmbedding x
  rwa [heq] at hcomp

/-- The restricted phase-action quotient projection is locally biholomorphic for the collar
atlas inherited from the full toric filling. -/
public theorem puncturedLocalCusp_projection_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let r := W.localWitness.radius
    letI := M.topology
    letI := M.charts
    letI := puncturedLocalCarrierCharts M r
    letI := actualLocalCuspFillingCharts W
    letI := puncturedLocalCuspQuotientCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (Quotient.mk _ : {p : LocalCarrier M r // M.t p ≠ 0} →
        puncturedLocalCuspQuotient W) := by
  let r := W.localWitness.radius
  let _ := M.topology
  let _ := M.charts
  let _ := puncturedLocalCarrierCharts M r
  let _ := actualLocalCuspFillingCharts W
  let _ := puncturedLocalCuspQuotientCharts W
  let π : {p : LocalCarrier M r // M.t p ≠ 0} →
      puncturedLocalCuspQuotient W := Quotient.mk _
  let πfull : LocalCarrier M r → actualLocalCuspFilling W := Quotient.mk _
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder π
  intro p
  have hinc : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (Subtype.val : {p : LocalCarrier M r // M.t p ≠ 0} → LocalCarrier M r) p := by
    let U := puncturedLocalCarrierOpen M r
    let _ : Nonempty U := ⟨p⟩
    let e := U.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
    let Φ : PartialDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel)
        {p : LocalCarrier M r // M.t p ≠ 0} (LocalCarrier M r)
        RegularSmoothnessOrder :=
      { toPartialEquiv := e.toPartialEquiv
        open_source := e.open_source
        open_target := e.open_target
        contMDiffOn_toFun := contMDiff_subtype_val.contMDiffOn
        contMDiffOn_invFun := by
          intro y hy
          apply (ContMDiffWithinAt.subtypeVal_comp_iff U _ e.target y).mp
          apply contMDiffAt_id.contMDiffWithinAt.congr_of_mem _ hy
          intro z hz
          change e (e.symm z) = z
          exact e.right_inv hz }
    have hp : p ∈ Φ.source := by
      change p ∈ Set.univ
      exact Set.mem_univ p
    have hΦ := Φ.isLocalDiffeomorphAt
      (modelWithCornersSelf ℂ ComplexModel) (modelWithCornersSelf ℂ ComplexModel)
      RegularSmoothnessOrder hp
    have heq : (Φ : {p : LocalCarrier M r // M.t p ≠ 0} → LocalCarrier M r) =
        Subtype.val := by
      funext y
      rfl
    rwa [heq] at hΦ
  have hfull : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder πfull p.1 := by
    simpa only [RegularSmoothnessOrder, πfull] using
      actualLocalCuspFilling_projection_isLocalDiffeomorph W p.1
  have htotal : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (πfull ∘ (Subtype.val : {p : LocalCarrier M r // M.t p ≠ 0} →
        LocalCarrier M r)) p :=
    hinc.comp (modelWithCornersSelf ℂ ComplexModel) (actualLocalCuspFilling W) hfull
  have htoFilling : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (puncturedLocalCuspToFilling W) (π p) := by
    simpa only [RegularSmoothnessOrder] using
      puncturedLocalCuspToFilling_isLocalDiffeomorph W (π p)
  let loc := htoFilling.localInverse
  have hloc : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      loc.toPartialEquiv.toFun (πfull p.1) := by
    have h := htoFilling.localInverse_isLocalDiffeomorphAt
    change IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      loc.toPartialEquiv.toFun (puncturedLocalCuspToFilling W (π p)) at h
    have hpoint : puncturedLocalCuspToFilling W (π p) = πfull p.1 := rfl
    rw [hpoint] at h
    exact h
  have hcomp : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
      (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
      (loc.toPartialEquiv.toFun ∘
        (πfull ∘ (Subtype.val : {p : LocalCarrier M r // M.t p ≠ 0} →
          LocalCarrier M r))) p :=
    htotal.comp (modelWithCornersSelf ℂ ComplexModel)
      (puncturedLocalCuspQuotient W) hloc
  have hmem : π ⁻¹' loc.target ∈ nhds p :=
    continuous_quot_mk.continuousAt
      (loc.open_target.mem_nhds htoFilling.localInverse_mem_target)
  have hevent : (loc.toPartialEquiv.toFun ∘
      (πfull ∘ (Subtype.val : {p : LocalCarrier M r // M.t p ≠ 0} →
        LocalCarrier M r))) =ᶠ[nhds p] π := by
    filter_upwards [hmem] with z hz
    change loc.toPartialEquiv.toFun (πfull z.1) = π z
    rw [show πfull z.1 = puncturedLocalCuspToFilling W (π z) by rfl]
    exact htoFilling.localInverse_left_inv hz
  exact isLocalDiffeomorphAt_congr_eventuallyEq_complexModel hcomp hevent

/-- The punctured local quotient map into the actual global family. -/
public noncomputable def puncturedLocalCuspQuotientMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    puncturedLocalCuspQuotient W →
      PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D) :=
  Quotient.lift (puncturedLocalCuspPrequotientMap W) (by
    intro p q h
    let _ := puncturedPsiAction W
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
    obtain ⟨lambda, hlambda⟩ := h
    change puncturedPsiMap W (Multiplicative.toAdd lambda) q = p at hlambda
    rw [← hlambda]
    exact puncturedLocalCuspPrequotientMap_psiMap W _ q)

@[simp]
public theorem puncturedLocalCuspQuotientMap_mk
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0}) :
    puncturedLocalCuspQuotientMap W (Quotient.mk _ p) =
      puncturedLocalCuspPrequotientMap W p :=
  rfl

/-- The phase-action quotient collar embeds locally biholomorphically in the actual punctured
global family. -/
public theorem puncturedLocalCuspQuotientMap_isLocalDiffeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    let F := assembledFuchsianPeriodFunctions E D
    let r := W.localWitness.radius
    let hproper : SourceActionProperlyDiscontinuous :=
      sourceActionProperlyDiscontinuous_of_eq
        E.modularParameter.toTriangleUniformization_sourceAction
    let hsource := E.modularParameter.toTriangleUniformization_sourceAction
    letI := M.topology
    letI := M.charts
    letI := puncturedLocalCarrierCharts M r
    letI := denseTorusCharts
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
      denseTorus_isManifold
    letI : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
      (denseTorusCuspOpen r).instChartedSpace
    letI : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
        (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
    letI := additiveCuspRadiusQuotientCharts r
    letI : ChartedSpace (ModelProd ComplexTwoSpace ℂ)
        (additiveCuspRadiusCover r) := (additiveCuspRadiusOpen r).instChartedSpace
    letI := regularBaseChartedSpace hproper
    letI : LocallyCompactSpace
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      (isOpen_isRegularBasePoint hproper).locallyCompactSpace
    letI : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
        (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
      regularBase_isManifold hproper
    letI := familyIsCancelSMul (regularParameterMap F)
    letI := familyContinuousConstSMul (regularParameterMap F)
      fun a ↦ (regularPeriodSection_contMDiff F hproper a
        RegularSmoothnessOrder).continuous
    letI := familyProperlyDiscontinuousSMul (regularParameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound
        (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
    let hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
      F hproper RegularSmoothnessOrder
    letI : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
        (RegularTotalSpace F) := hregular.1
    letI : LocallyCompactSpace (RegularTotalSpace F) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := regularFamilyDeckAction F
    letI := regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
    letI := regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
    letI := regularFamilyDeckAction_continuousConstSMul F hproper
    letI := regularCuspBundleRegionCharts W
    letI := actualLocalCuspFillingCharts W
    letI := puncturedLocalCuspQuotientCharts W
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel) GlobalDeckTotalModel
      RegularSmoothnessOrder (puncturedLocalCuspQuotientMap W) := by
  let F := assembledFuchsianPeriodFunctions E D
  let r := W.localWitness.radius
  let hproper : SourceActionProperlyDiscontinuous :=
    sourceActionProperlyDiscontinuous_of_eq
      E.modularParameter.toTriangleUniformization_sourceAction
  let hsource := E.modularParameter.toTriangleUniformization_sourceAction
  let _ := M.topology
  let _ := M.charts
  let _ := puncturedLocalCarrierCharts M r
  let _ := denseTorusCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ DenseTorus :=
    denseTorus_isManifold
  let _ : ChartedSpace ComplexModel (denseTorusCuspRegion r) :=
    (denseTorusCuspOpen r).instChartedSpace
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (denseTorusCuspRegion r) := denseTorusCuspRegion_isManifold r
  let _ := additiveCuspRadiusQuotientCharts r
  let _ : ChartedSpace (ModelProd ComplexTwoSpace ℂ) (additiveCuspRadiusCover r) :=
    (additiveCuspRadiusOpen r).instChartedSpace
  let _ := regularBaseChartedSpace hproper
  let _ : LocallyCompactSpace
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    (isOpen_isRegularBasePoint hproper).locallyCompactSpace
  let _ : IsManifold GlobalDeckBaseModel RegularSmoothnessOrder
      (RegularBase (U := E.modularParameter.toTriangleUniformization)) :=
    regularBase_isManifold hproper
  let _ := familyIsCancelSMul (regularParameterMap F)
  let _ := familyContinuousConstSMul (regularParameterMap F)
    fun a ↦ (regularPeriodSection_contMDiff F hproper a
      RegularSmoothnessOrder).continuous
  let _ := familyProperlyDiscontinuousSMul (regularParameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound
      (regularParameterMap F) (regularParameterMap_compactUniformLowerBound F))
  have hregular := regularTotalSpace_isManifold_and_projection_isLocalDiffeomorph
    F hproper RegularSmoothnessOrder
  let _ : IsManifold GlobalDeckTotalModel RegularSmoothnessOrder
      (RegularTotalSpace F) := hregular.1
  let _ : LocallyCompactSpace (RegularTotalSpace F) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  let _ := regularFamilyDeckAction F
  let _ : IsCancelSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_isCancelSMul_of_fuchsian F hsource hproper
  let _ : ProperlyDiscontinuousSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_properlyDiscontinuous_of_source F hproper
  let _ : ContinuousConstSMul Delta (RegularTotalSpace F) :=
    regularFamilyDeckAction_continuousConstSMul F hproper
  let _ := regularCuspBundleRegionCharts W
  let _ := actualLocalCuspFillingCharts W
  let _ := puncturedLocalCuspQuotientCharts W
  change IsLocalDiffeomorph (modelWithCornersSelf ℂ ComplexModel)
    GlobalDeckTotalModel RegularSmoothnessOrder (puncturedLocalCuspQuotientMap W)
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : {p : LocalCarrier M r // M.t p ≠ 0} →
        puncturedLocalCuspQuotient W := Quotient.mk _
    have hπ := puncturedLocalCusp_projection_isLocalDiffeomorph W p
    let loc := hπ.localInverse
    have hloc : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
        (modelWithCornersSelf ℂ ComplexModel) RegularSmoothnessOrder
        loc.toPartialEquiv.toFun (π p) :=
      hπ.localInverse_isLocalDiffeomorphAt
    have hcomp : IsLocalDiffeomorphAt (modelWithCornersSelf ℂ ComplexModel)
        GlobalDeckTotalModel RegularSmoothnessOrder
        (puncturedLocalCuspPrequotientMap W ∘ loc.toPartialEquiv.toFun) (π p) :=
      hloc.comp GlobalDeckTotalModel (PuncturedGlobalFamily F)
        (puncturedLocalCuspPrequotientMap_isLocalDiffeomorph W
          (loc.toPartialEquiv.toFun (π p)))
    have hright := hπ.localInverse_eventuallyEq_right
    have hevent : (puncturedLocalCuspPrequotientMap W ∘ loc.toPartialEquiv.toFun)
        =ᶠ[nhds (π p)] puncturedLocalCuspQuotientMap W := by
      filter_upwards [hright] with y hy
      calc
        puncturedLocalCuspPrequotientMap W (loc.toPartialEquiv.toFun y) =
            puncturedLocalCuspQuotientMap W (π (loc.toPartialEquiv.toFun y)) := rfl
        _ = puncturedLocalCuspQuotientMap W y := congrArg _ hy
    exact isLocalDiffeomorphAt_congr_eventuallyEq_complexToGlobalDeck hcomp hevent

public theorem puncturedLocalCuspQuotientMap_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (puncturedLocalCuspQuotientMap W) :=
  continuous_quot_lift _ (puncturedLocalCuspPrequotientMap_continuous W)

public theorem puncturedLocalCuspQuotientMap_isOpenMap
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenMap (puncturedLocalCuspQuotientMap W) := by
  apply IsOpenMap.of_comp continuous_quot_mk Quotient.mk_surjective
  convert puncturedLocalCuspPrequotientMap_isOpenMap W using 1
  funext p
  rfl

private theorem additiveCuspRepresentatives_deck_data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius)
    (h : additiveCuspCoverToGlobal W a = additiveCuspCoverToGlobal W b) :
    ∃ k : ℤ, N.lift (b.1.2 - k) = N.lift a.1.2 ∧
      regularFamilyDeckMap (assembledFuchsianPeriodFunctions E D) (g₀ ^ k)
          (regularCuspFamilyPoint N b.1.2
            (W.lift_regular
              (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1) =
        regularCuspFamilyPoint N a.1.2
          (W.lift_regular
            (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1 := by
  let F := assembledFuchsianPeriodFunctions E D
  let _ := regularFamilyDeckAction F
  have horbit := Quotient.exact h
  change MulAction.orbitRel Delta (RegularTotalSpace F) _ _ at horbit
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at horbit
  obtain ⟨g, hg⟩ := horbit
  change regularFamilyDeckMap F g
      (regularCuspFamilyPoint N b.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1) =
    regularCuspFamilyPoint N a.1.2
      (W.lift_regular
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1 at hg
  have hbase := congrArg (regularTotalSpaceBase F) hg
  simp only [regularCuspFamilyPoint] at hbase
  have hmeet :
      ((E.modularParameter.toTriangleUniformization.sourceAction g • ·) ''
          normalizedCuspRegion N W.localWitness.radius ∩
        normalizedCuspRegion N W.localWitness.radius).Nonempty := by
    refine ⟨N.lift a.1.2, ?_, ?_⟩
    · refine ⟨N.lift b.1.2, ⟨b.1.2, ⟨?_, b.2⟩, rfl⟩, ?_⟩
      · exact additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b
      · exact congrArg Subtype.val hbase
    · exact ⟨a.1.2,
        ⟨additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a, a.2⟩, rfl⟩
  obtain ⟨k, rfl⟩ := W.translates_meet_only_parabolic g hmeet
  refine ⟨k, ?_, hg⟩
  exact (lift_sub_int N b.1.2
    (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) k).trans
      (congrArg Subtype.val hbase)

private theorem additiveCuspRepresentatives_period_data
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius)
    (h : additiveCuspCoverToGlobal W a = additiveCuspCoverToGlobal W b) :
    ∃ k : ℤ, a.1.2 = b.1.2 - k ∧ ∃ n : IntegerPeriods,
      periodVector (periodValues
          (assembledFuchsianPeriodFunctions E D).tau
          (assembledFuchsianPeriodFunctions E D).mu
          (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2)) n + a.1.1 = b.1.1 := by
  obtain ⟨k, hlift, hdeck⟩ := additiveCuspRepresentatives_deck_data W a b h
  have hsSub : b.1.2 - k ∈ cuspHalfPlane N.height := by
    simpa [sub_eq_add_neg] using cuspHalfPlane_add_int
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) (-k)
  have hs : a.1.2 = b.1.2 - k := by
    calc
      a.1.2 = (((assembledFuchsianPeriodFunctions E D).tau (N.lift a.1.2) :
          UpperHalfPlane) : ℂ) :=
        (N.lift_tau a.1.2
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)).symm
      _ = (((assembledFuchsianPeriodFunctions E D).tau (N.lift (b.1.2 - k)) :
          UpperHalfPlane) : ℂ) := congrArg (fun z ↦
        (((assembledFuchsianPeriodFunctions E D).tau z : UpperHalfPlane) : ℂ)) hlift.symm
      _ = b.1.2 - k := N.lift_tau (b.1.2 - k) hsSub
  let F := assembledFuchsianPeriodFunctions E D
  have hinner := Quotient.exact hdeck
  change MulAction.orbitRel
      (FamilyPeriodGroup (regularParameterMap F)) _
      (regularDeckMap F (g₀ ^ k)
        (regularCuspBundlePoint N b.1.2
          (W.lift_regular
            (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le b) b.2) b.1.1))
      (regularCuspBundlePoint N a.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2) a.1.1) at hinner
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hinner
  obtain ⟨n, hn⟩ := hinner
  have hsnd := congrArg Prod.snd hn
  rw [family_smul_snd] at hsnd
  change periodVector (regularParameterMap F _).1 n.coeff + a.1.1 =
    periodTransport (g₀ ^ k) _ b.1.1 at hsnd
  rw [periodTransport_gZero_zpow] at hsnd
  refine ⟨k, hs, n.coeff, ?_⟩
  simpa [F, regularParameterMap, regularCuspBundlePoint,
    AnalyticTorusFamily.parameterMap] using hsnd

private theorem additiveCuspRepresentatives_psiOrbit
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (a b : additiveCuspRadiusCover W.localWitness.radius)
    (h : additiveCuspCoverToGlobal W a = additiveCuspCoverToGlobal W b) :
    puncturedPsiOrbitRel W
      (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ b))
      (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ a)) := by
  obtain ⟨k, hs, n, hn⟩ := additiveCuspRepresentatives_period_data W a b h
  let lambda := firstParameterCoefficients n
  let m := identityParameterCoefficients n
  let x := periodValues
    (assembledFuchsianPeriodFunctions E D).tau
    (assembledFuchsianPeriodFunctions E D).mu
    (assembledFuchsianPeriodFunctions E D).beta (N.lift a.1.2)
  have hv : periodVector x n =
      (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) + fun i ↦ (m i : ℂ) := by
    rw [integerPeriods_decompose n, periodVector_add,
      periodVector_firstPeriodCoefficients, periodVector_identityPeriodCoefficients]
  have hz0 : (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 0 + a.1.1 0 =
      b.1.1 0 + (-(m 0) : ℤ) := by
    have hi := congrFun hn 0
    rw [hv] at hi
    change (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 0 +
      (m 0 : ℂ) + a.1.1 0 = b.1.1 0 at hi
    push_cast
    linear_combination hi
  have hz1 : (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 1 + a.1.1 1 =
      b.1.1 1 + (-(m 1) : ℤ) := by
    have hi := congrFun hn 1
    rw [hv] at hi
    change (periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) 1 +
      (m 1 : ℂ) + a.1.1 1 = b.1.1 1 at hi
    push_cast
    linear_combination hi
  have hs' : a.1.2 = b.1.2 + (-k : ℤ) := by
    rw [hs]
    push_cast
    ring
  have hdense : denseCuspExponential
        ((periodBlock x).mulVec (fun i ↦ (lambda i : ℂ)) + a.1.1) a.1.2 =
      denseCuspExponential b.1.1 b.1.2 := by
    ext i
    fin_cases i
    · exact congrArg Units.val
        ((scaledExponentialUnit_eq_iff _ _).mpr ⟨-(m 0), hz0⟩)
    · exact congrArg Units.val
        ((scaledExponentialUnit_eq_iff _ _).mpr ⟨-(m 1), hz1⟩)
    · exact congrArg Units.val
        ((scaledExponentialUnit_eq_iff _ _).mpr ⟨-k, hs'⟩)
  let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
  have hlocal :
      (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
          N M W.localWitness.radius W.localWitness.radius_pos
            W.localWitness.radius_le).psiMap lambda (e (Quotient.mk _ a)).1 =
        (e (Quotient.mk _ b)).1 := by
    rw [show ((e (Quotient.mk _ a)).1 : LocalCarrier M W.localWitness.radius) =
        localCuspExponentialPoint M W.localWitness.radius a.1.1 a.1.2
          (mem_ball_zero_iff.mpr a.2) from
      additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius a,
      show ((e (Quotient.mk _ b)).1 : LocalCarrier M W.localWitness.radius) =
        localCuspExponentialPoint M W.localWitness.radius b.1.1 b.1.2
          (mem_ball_zero_iff.mpr b.2) from
      additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius b]
    rw [localCuspExponentialPoint_period_equivariant N M
      W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
      a.1.2 (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)
      (mem_ball_zero_iff.mpr a.2) a.1.1 lambda]
    apply Subtype.ext
    rw [localCuspExponentialPoint_coe, localCuspExponentialPoint_coe]
    exact congrArg M.torusEmbedding hdense
  let _ := puncturedPsiAction W
  change MulAction.orbitRel (Multiplicative ParameterLattice) _ _ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨Multiplicative.ofAdd lambda, ?_⟩
  apply Subtype.ext
  exact hlocal

public theorem puncturedLocalCuspQuotientMap_injective
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Function.Injective (puncturedLocalCuspQuotientMap W) := by
  intro x y hxy
  induction x using Quotient.inductionOn with
  | _ p =>
    induction y using Quotient.inductionOn with
    | _ q =>
      let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      obtain ⟨u, rfl⟩ := e.surjective p
      obtain ⟨v, rfl⟩ := e.surjective q
      induction u using Quotient.inductionOn with
      | _ a =>
        induction v using Quotient.inductionOn with
        | _ b =>
          apply Quotient.sound
          apply additiveCuspRepresentatives_psiOrbit W b a
          rw [puncturedLocalCuspQuotientMap_mk,
            puncturedLocalCuspQuotientMap_mk] at hxy
          dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e] at hxy
          rw [Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply,
            additiveCuspQuotientToGlobal_mk, additiveCuspQuotientToGlobal_mk] at hxy
          exact hxy.symm

public theorem puncturedLocalCuspQuotientMap_isOpenEmbedding
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    IsOpenEmbedding (puncturedLocalCuspQuotientMap W) :=
  IsOpenEmbedding.of_continuous_injective_isOpenMap
    (puncturedLocalCuspQuotientMap_continuous W)
    (puncturedLocalCuspQuotientMap_injective W)
    (puncturedLocalCuspQuotientMap_isOpenMap W)

public theorem puncturedLocalCuspPrequotientMap_range
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set.range (puncturedLocalCuspPrequotientMap W) =
      puncturedGlobalCuspCollar W := by
  ext y
  constructor
  · rintro ⟨p, rfl⟩
    let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
    let q := e.symm p
    have hp : p = e q := (e.apply_symm_apply p).symm
    rw [hp]
    induction q using Quotient.inductionOn with
    | _ a =>
      dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e]
      rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]
      exact actualPuncturedGlobalCuspPoint_mem_collar W a.1.2
        (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a) a.2 a.1.1
  · rintro ⟨x, hx, rfl⟩
    induction x using Quotient.inductionOn with
    | _ p =>
      rcases p with ⟨⟨b, hb⟩, zeta⟩
      change b ∈ normalizedCuspRegion N W.localWitness.radius at hx
      obtain ⟨s, ⟨hs, hq⟩, hlift⟩ := hx
      let a : additiveCuspRadiusCover W.localWitness.radius := ⟨(zeta, s), hq⟩
      let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
      refine ⟨e (Quotient.mk _ a), ?_⟩
      dsimp only [puncturedLocalCuspPrequotientMap, Function.comp_apply, e]
      rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]
      change puncturedGlobalCuspPoint N s _ zeta =
        Quotient.mk _ (Quotient.mk _ ((⟨b, hb⟩ : RegularBase) , zeta))
      subst b
      rfl

public theorem puncturedLocalCuspQuotientMap_range
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Set.range (puncturedLocalCuspQuotientMap W) =
      puncturedGlobalCuspCollar W := by
  rw [← puncturedLocalCuspPrequotientMap_range W]
  apply Set.Subset.antisymm
  · rintro y ⟨q, rfl⟩
    induction q using Quotient.inductionOn with
    | _ p => exact ⟨p, rfl⟩
  · rintro y ⟨p, rfl⟩
    exact ⟨Quotient.mk _ p, rfl⟩

public theorem puncturedLocalCarrier_nonempty
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} := by
  let a : ℂ := ((W.localWitness.radius / 2 : ℝ) : ℂ)
  have ha : a ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (ne_of_gt W.localWitness.radius_pos) (by norm_num))
  let x : DenseTorus := fun i ↦ if i = 2 then Units.mk0 a ha else 1
  have hx2 : ((x 2 : ℂˣ) : ℂ) = a := by simp [x]
  have ht : M.t (M.torusEmbedding x) = a := (M.t_torus x).trans hx2
  have hnorm : ‖M.t (M.torusEmbedding x)‖ < W.localWitness.radius := by
    rw [ht]
    change ‖((W.localWitness.radius / 2 : ℝ) : ℂ)‖ < W.localWitness.radius
    have hhalfpos : 0 < W.localWitness.radius / 2 :=
      div_pos W.localWitness.radius_pos (by norm_num)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhalfpos]
    linarith [W.localWitness.radius_pos]
  let p : LocalCarrier M W.localWitness.radius :=
    ⟨M.torusEmbedding x, mem_ball_zero_iff.mpr hnorm⟩
  exact ⟨⟨p, by simpa [p, ht] using ha⟩⟩

/-- The topological cusp collar identification, as an ambient open partial homeomorphism from
the punctured global family to the local toric filling. -/
public noncomputable def actualPuncturedCuspCollarOpenPartialHomeomorph
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    OpenPartialHomeomorph
      (PuncturedGlobalFamily (assembledFuchsianPeriodFunctions E D))
      (actualLocalCuspFilling W) := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  exact
    (puncturedLocalCuspQuotientMap_isOpenEmbedding W).toOpenPartialHomeomorph.symm.trans
      (puncturedLocalCuspToFilling_isOpenEmbedding W).toOpenPartialHomeomorph

public theorem actualPuncturedCuspCollarOpenPartialHomeomorph_source
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    (actualPuncturedCuspCollarOpenPartialHomeomorph W).source =
      puncturedGlobalCuspCollar W := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  simp only [actualPuncturedCuspCollarOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    Set.preimage_univ, Set.inter_univ,
    puncturedLocalCuspQuotientMap_range]

public theorem actualPuncturedCuspCollarOpenPartialHomeomorph_target
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    (actualPuncturedCuspCollarOpenPartialHomeomorph W).target =
      actualLocalCuspFillingCollar W := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  simp only [actualPuncturedCuspCollarOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.symm_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_target,
    IsOpenEmbedding.toOpenPartialHomeomorph_source,
    Set.preimage_univ, Set.inter_univ, actualLocalCuspFillingCollar]

public theorem actualPuncturedCuspCollarOpenPartialHomeomorph_apply
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (q : puncturedLocalCuspQuotient W) :
    actualPuncturedCuspCollarOpenPartialHomeomorph W
        (puncturedLocalCuspQuotientMap W q) =
      puncturedLocalCuspToFilling W q := by
  let _ : Nonempty {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} :=
    puncturedLocalCarrier_nonempty W
  let _ : Nonempty (puncturedLocalCuspQuotient W) :=
    ⟨Quotient.mk _ (puncturedLocalCarrier_nonempty W).some⟩
  rw [actualPuncturedCuspCollarOpenPartialHomeomorph,
    OpenPartialHomeomorph.trans_apply,
    (puncturedLocalCuspQuotientMap_isOpenEmbedding W).toOpenPartialHomeomorph_left_inv]
  exact congrFun
    ((puncturedLocalCuspToFilling_isOpenEmbedding W).toOpenPartialHomeomorph_apply) q

/-- Every source point has an open neighborhood avoided by all sufficiently deep translates of
the normalized cusp.  The proof transports a compact source neighborhood through the assembled
modular parameter and applies the integral modular height dichotomy. -/
public theorem exists_sourceNeighborhood_avoids_deep_cusp_translates
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) (z₀ : UpperHalfPlane) :
    ∃ U : Set UpperHalfPlane, IsOpen U ∧ z₀ ∈ U ∧
      ∃ r : ℝ, 0 < r ∧ r ≤ W.localWitness.radius ∧
        ∀ (g : Delta) (s : ℂ), ‖cuspQ s‖ < r →
          fuchsianSourceAction g • N.lift s ∉ U := by
  let F := assembledFuchsianPeriodFunctions E D
  let P : FuchsianModularParameter :=
    { tau := F.tau
      tau_holomorphic := F.tau_holomorphic
      transform_one := F.tau_equivariant_g1
      transform_two := F.tau_equivariant_g2 }
  obtain ⟨K, hKnhds, hKcompact, hKclosed⟩ :=
    exists_mem_nhds_isCompact_isClosed z₀
  obtain ⟨U, hUK, hUopen, hzU⟩ := mem_nhds_iff.mp hKnhds
  let L : Set UpperHalfPlane := F.tau '' K
  have hLcompact : IsCompact L := hKcompact.image F.tau_holomorphic.continuous
  obtain ⟨H, hH, hHavoid⟩ := exists_height_modularTranslates_avoid_compact hLcompact
  let r := min W.localWitness.radius (cuspRadius H)
  have hr : 0 < r := lt_min W.localWitness.radius_pos (Real.exp_pos _)
  refine ⟨U, hUopen, hzU, r, hr, min_le_left _ _, ?_⟩
  intro g s hsr hmem
  have hsN : s ∈ cuspHalfPlane N.height :=
    mem_cuspHalfPlane_of_norm_cuspQ_lt
      (min_le_left W.localWitness.radius (cuspRadius H) |>.trans
        W.localWitness.radius_le) hsr
  have hsH : s ∈ cuspHalfPlane H :=
    mem_cuspHalfPlane_of_norm_cuspQ_lt (min_le_right _ _) hsr
  have htau : ((F.tau (N.lift s) : UpperHalfPlane) : ℂ) = s := N.lift_tau s hsN
  have hheight : H < (F.tau (N.lift s)).im := by
    change H < ((F.tau (N.lift s) : UpperHalfPlane) : ℂ).im
    rw [htau]
    exact hsH
  have himage : F.tau (fuchsianSourceAction g • N.lift s) ∈ L :=
    ⟨fuchsianSourceAction g • N.lift s, hUK hmem, rfl⟩
  have hequiv : F.tau (fuchsianSourceAction g • N.lift s) =
      rhoTauReal g • F.tau (N.lift s) := P.equivariant g (N.lift s)
  rw [hequiv] at himage
  exact hHavoid (rhoTau g) (F.tau (N.lift s)) hheight himage

/-- Eventual assertions at the upper-half-plane cusp are exactly assertions holding above some
fixed imaginary height. -/
public theorem eventually_upperHalfPlaneAtInfinity_iff
    {P : UpperHalfPlane → Prop} :
    (∀ᶠ z in upperHalfPlaneAtInfinity, P z) ↔
      ∃ H : ℝ, ∀ z : UpperHalfPlane, H ≤ z.im → P z := by
  change {z | P z} ∈ Filter.comap UpperHalfPlane.im Filter.atTop ↔ _
  rw [(Filter.atTop_basis.comap UpperHalfPlane.im).mem_iff]
  simp only [true_and]
  constructor
  · rintro ⟨H, hH⟩
    exact ⟨H, fun z hz ↦ hH hz⟩
  · rintro ⟨H, hH⟩
    exact ⟨H, fun z hz ↦ hH z hz⟩

/-- The simple completed modular-cusp factor `q ↦ q u(q)` maps a neighborhood of zero
onto a neighborhood of zero.  This is the analytic inverse theorem applied using `u(0) ≠ 0`. -/
public theorem exists_cuspProduct_preimage_in_ball
    (J : ExactNormalizedModularJUniformization) (r : ℝ) (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ u ∈ Metric.ball (0 : ℂ) ε,
      ∃ q : ℂ, q ∈ Metric.ball 0 r ∧
        q * J.cusp.cuspUnit q = u := by
  let f : ℂ → ℂ := fun q ↦ q * J.cusp.cuspUnit q
  have huAnalytic : AnalyticAt ℂ J.cusp.cuspUnit 0 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [Metric.ball_mem_nhds 0 J.cusp.cuspRadius_pos] with q hq
    exact mdifferentiableAt_iff_differentiableAt.mp
      (J.cusp.cuspUnit_holomorphic q hq)
  have hfAnalytic : AnalyticAt ℂ f 0 := by
    exact (by fun_prop : AnalyticAt ℂ (fun q : ℂ ↦ q) 0).mul huAnalytic
  have hfDeriv : deriv f 0 = J.cusp.cuspUnit 0 := by
    rw [show f = fun q : ℂ ↦ q * J.cusp.cuspUnit q from rfl,
      deriv_fun_mul (by fun_prop) huAnalytic.differentiableAt]
    simp
  have hfStrict : HasStrictDerivAt f (J.cusp.cuspUnit 0) 0 := by
    rw [← hfDeriv]
    exact hfAnalytic.hasStrictDerivAt
  have hstrictEquiv :=
    hfStrict.hasStrictFDerivAt_equiv J.cusp.cuspUnit_zero_ne
  let e : OpenPartialHomeomorph ℂ ℂ :=
    hstrictEquiv.toOpenPartialHomeomorph f
  have hzeroSource : (0 : ℂ) ∈ e.source :=
    hstrictEquiv.mem_toOpenPartialHomeomorph_source
  have hzeroTarget : (0 : ℂ) ∈ e.target := by
    have h := e.map_source hzeroSource
    simpa [e, f] using h
  have hinvzero : e.symm (0 : ℂ) = 0 := by
    have h := e.left_inv hzeroSource
    simpa [e, f] using h
  have hpre : e.symm ⁻¹' Metric.ball (0 : ℂ) r ∈ nhds (0 : ℂ) := by
    apply (e.continuousAt_symm hzeroTarget).preimage_mem_nhds
    rw [hinvzero]
    exact Metric.ball_mem_nhds 0 hr
  have htarget : e.target ∈ nhds (0 : ℂ) :=
    e.open_target.mem_nhds hzeroTarget
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem htarget hpre)
  refine ⟨ε, hε, ?_⟩
  intro u hu
  have hut : u ∈ e.target := (hεsub hu).1
  have huq : e.symm u ∈ Metric.ball (0 : ℂ) r := (hεsub hu).2
  refine ⟨e.symm u, huq, ?_⟩
  have heq := e.right_inv hut
  change f (e.symm u) = u at heq
  simpa [f] using heq

/-- Every sufficiently large normalized modular coordinate has a representative in the selected
normalized cusp half-plane, with cusp radius inside the actual filling's compact half-core. -/
public theorem exists_normalizedModularCusp_preimage_of_large_coordinate
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, R < ‖w‖ →
      ∃ s : ℂ, s ∈ cuspHalfPlane N.height ∧
        ‖cuspQ s‖ < W.localWitness.radius / 2 ∧
        normalizedModularJCoordinate
            ((assembledFuchsianPeriodFunctions E D).tau (N.lift s)) = w := by
  let J : ExactNormalizedModularJUniformization :=
    Classical.choice establishedExactNormalizedModularJUniformization
  obtain ⟨H, hfactor⟩ :=
    (eventually_upperHalfPlaneAtInfinity_iff (P := fun z ↦
      (normalizedModularJCoordinate z)⁻¹ =
        modularCuspQ z * J.cusp.cuspUnit (modularCuspQ z))).mp
      J.cusp.reciprocal_factorization
  let r : ℝ := min (W.localWitness.radius / 2)
    (min J.cusp.cuspRadius (cuspRadius H))
  have hr : 0 < r := lt_min (half_pos W.localWitness.radius_pos)
    (lt_min J.cusp.cuspRadius_pos (Real.exp_pos _))
  obtain ⟨ε, hε, hsolve⟩ := exists_cuspProduct_preimage_in_ball J r hr
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro w hwLarge
  have hwNormPos : 0 < ‖w‖ := (inv_pos.mpr hε).trans hwLarge
  have hw : w ≠ 0 := norm_pos_iff.mp hwNormPos
  have hwinvNorm : ‖w⁻¹‖ < ε := by
    rw [norm_inv]
    exact (inv_lt_comm₀ hwNormPos hε).2 hwLarge
  obtain ⟨q, hqBall, hqProduct⟩ :=
    hsolve w⁻¹ (mem_ball_zero_iff.mpr hwinvNorm)
  have hqNorm : ‖q‖ < r := mem_ball_zero_iff.mp hqBall
  have hqNe : q ≠ 0 := by
    intro hq
    rw [hq, zero_mul] at hqProduct
    exact (inv_ne_zero hw) hqProduct.symm
  let s : ℂ := Function.Periodic.invQParam 1 q
  have hcuspQ : cuspQ s = q := by
    simpa [cuspQ, Function.Periodic.qParam] using
      (Function.Periodic.qParam_right_inv one_ne_zero hqNe)
  have hqHalf : ‖cuspQ s‖ < W.localWitness.radius / 2 := by
    rw [hcuspQ]
    exact hqNorm.trans_le (min_le_left _ _)
  have hqFull : ‖cuspQ s‖ < W.localWitness.radius :=
    hqHalf.trans (half_lt_self W.localWitness.radius_pos)
  have hsN : s ∈ cuspHalfPlane N.height :=
    mem_cuspHalfPlane_of_norm_cuspQ_lt W.localWitness.radius_le hqFull
  have hqH : ‖cuspQ s‖ < cuspRadius H := by
    rw [hcuspQ]
    exact hqNorm.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsH : s ∈ cuspHalfPlane H :=
    mem_cuspHalfPlane_of_norm_cuspQ_lt le_rfl hqH
  let F := assembledFuchsianPeriodFunctions E D
  have htau : ((F.tau (N.lift s) : UpperHalfPlane) : ℂ) = s :=
    N.lift_tau s hsN
  have hzHeight : H ≤ (F.tau (N.lift s)).im := by
    apply le_of_lt
    change H < ((F.tau (N.lift s) : UpperHalfPlane) : ℂ).im
    rw [htau]
    exact hsH
  have hmodularQ : modularCuspQ (F.tau (N.lift s)) = q := by
    rw [modularCuspQ, htau]
    exact Function.Periodic.qParam_right_inv one_ne_zero hqNe
  have hrecip := hfactor (F.tau (N.lift s)) hzHeight
  rw [hmodularQ, hqProduct] at hrecip
  have hcoordinate : normalizedModularJCoordinate (F.tau (N.lift s)) = w := by
    exact inv_injective hrecip
  exact ⟨s, hsN, hqHalf, hcoordinate⟩

/-- Two normalized cusp lifts representing the same full source orbit have the same `q`-radius.
Precise invariance of the selected horodisc reduces the intervening deck element to a power of
the parabolic generator. -/
public theorem norm_cuspQ_eq_of_lift_orbit_eq
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (s t : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (ht : t ∈ cuspHalfPlane N.height)
    (hqs : ‖cuspQ s‖ < W.localWitness.radius)
    (hqt : ‖cuspQ t‖ < W.localWitness.radius)
    (h : letI := FuchsianProperFreeness.triangleSourceMulAction
          E.modularParameter.toTriangleUniformization
      (Quotient.mk _ (N.lift s) :
          Quotient (MulAction.orbitRel Delta UpperHalfPlane)) =
        Quotient.mk _ (N.lift t)) :
    ‖cuspQ s‖ = ‖cuspQ t‖ := by
  let U := E.modularParameter.toTriangleUniformization
  let _ := FuchsianProperFreeness.triangleSourceMulAction U
  have hrel := Quotient.exact h
  change MulAction.orbitRel Delta UpperHalfPlane (N.lift s) (N.lift t) at hrel
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
  obtain ⟨g, hg⟩ := hrel
  have hmeet :
      ((fun z : UpperHalfPlane ↦ U.sourceAction g • z) ''
          normalizedCuspRegion N W.localWitness.radius ∩
        normalizedCuspRegion N W.localWitness.radius).Nonempty := by
    refine ⟨N.lift s, ?_, ?_⟩
    · exact ⟨N.lift t, ⟨t, ⟨ht, hqt⟩, rfl⟩, hg⟩
    · exact ⟨s, ⟨hs, hqs⟩, rfl⟩
  obtain ⟨k, rfl⟩ := W.translates_meet_only_parabolic g hmeet
  have htSub : t - k ∈ cuspHalfPlane N.height := by
    simpa [sub_eq_add_neg] using cuspHalfPlane_add_int ht (-k)
  have hlift : N.lift (t - k) = N.lift s := by
    exact (lift_sub_int N t ht k).trans hg
  have hst : s = t - k := by
    calc
      s = (((assembledFuchsianPeriodFunctions E D).tau (N.lift s) :
          UpperHalfPlane) : ℂ) := (N.lift_tau s hs).symm
      _ = (((assembledFuchsianPeriodFunctions E D).tau (N.lift (t - k)) :
          UpperHalfPlane) : ℂ) := congrArg (fun z ↦
            (((assembledFuchsianPeriodFunctions E D).tau z : UpperHalfPlane) : ℂ)) hlift.symm
      _ = t - k := N.lift_tau (t - k) htSub
  have hcusp : cuspQ s = cuspQ t := by
    rw [hst]
    simpa [sub_eq_add_neg] using cuspQ_add_int t (-k)
  exact congrArg norm hcusp

end SphereSixComplex.Geometry.CuspPuncturedCollarBridge
