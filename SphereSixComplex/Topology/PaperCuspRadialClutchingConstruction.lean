module

public import SphereSixComplex.Topology.PaperCuspGeometricSpecializationDefs
public import SphereSixComplex.Topology.PaperEllipticCollarFundamentalDomain
public import SphereSixComplex.Topology.ConnectedMayerVietorisDegreeZero
public import SphereSixComplex.Geometry.CuspRealPeriodDeckCoordinates

/-!
# The radial clutching datum of the actual cusp collar

The punctured cusp collar is a family of complex two-tori over a punctured disc.  Its period
lattice is monodromy invariant as a subgroup of `ℂ²`, but its *marking* is transported by the
parabolic monodromy matrix `M₀`.  Consequently the collar is an open radial interval times the
mapping torus of the descended real-linear automorphism of a single fibre torus induced by `M₀`.

This file builds that fibre and its clutching map, together with the integral homology
coordinates the geometric Wang splitting requires.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix Topology

namespace SphereSixComplex

namespace Geometry.CuspRadialClutchingConstruction

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.FamilyEquivariance
open SphereSixComplex.CircleMappingTorusHomologyBases
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.CyclicAngularFundamentalDomain
open CategoryTheory

/-- The real-linear automorphism of the fibre `ℂ²` which, in the canonical real period
coordinates at `x`, is the parabolic monodromy matrix `M₀`.  Unlike `periodTransport g₀ x` it
reads its target coordinates in the *same* period basis, so it is an automorphism of one fibre
rather than a map between two fibres. -/
public noncomputable def cuspFiberLift (x : PeriodDomain) :
    ComplexTwoSpace ≃ₗ[ℝ] ComplexTwoSpace :=
  ((fullRankDomain x).realEquiv.toLinearEquiv.symm.trans (rhoLambdaReal g₀)).trans
    (fullRankDomain x).realEquiv.toLinearEquiv

public theorem cuspFiberLift_apply (x : PeriodDomain) (z : ComplexTwoSpace) :
    cuspFiberLift x z =
      (fullRankDomain x).realEquiv (rhoLambdaReal g₀ (periodCoordinates x z)) := rfl

/-- The cusp fibre lift carries every period to the period prescribed by `M₀`. -/
public theorem cuspFiberLift_periodVector (x : PeriodDomain) (n : IntegerPeriods) :
    cuspFiberLift x (periodVector x.1 n) = periodVector x.1 (M₀ *ᵥ n) := by
  rw [cuspFiberLift_apply, periodCoordinates_periodVector, rhoLambdaReal_integer,
    (fullRankDomain x).map_integer, rhoLambda_g₀_apply]

/-- The descended cusp monodromy of a single period-torus fibre.  It is a homeomorphism of one
torus because the parabolic monodromy fixes the period *lattice* while moving its marking. -/
public noncomputable def cuspFiberClutching (x : PeriodDomain) :
    AdditiveTorus x.1 ≃ₜ AdditiveTorus x.1 :=
  Homeomorph.Quotient.congr (cuspFiberLift x).toContinuousLinearEquiv.toHomeomorph
    (orbitRel_iff_of_period_equivariant x.1 x.1 (rhoLambda g₀).toAddEquiv
      (cuspFiberLift x).toAddEquiv (fun n ↦ by
        change cuspFiberLift x (periodVector x.1 n) = periodVector x.1 (rhoLambda g₀ n)
        rw [cuspFiberLift_periodVector, rhoLambda_g₀_apply]))

@[simp]
public theorem cuspFiberClutching_mk (x : PeriodDomain) (z : ComplexTwoSpace) :
    cuspFiberClutching x (Quotient.mk _ z) = Quotient.mk _ (cuspFiberLift x z) := rfl

/-- The cusp clutching map as a descended affine automorphism with integral lattice map
`rhoLambda g₀`, that is `M₀`. -/
public noncomputable def cuspDescendedAffineTorusAutomorphism (x : PeriodDomain) :
    DescendedAffineTorusAutomorphism x.1 where
  latticeMap := rhoLambda g₀
  lift := (cuspFiberLift x).toAddEquiv
  lift_period n := by
    change cuspFiberLift x (periodVector x.1 n) = periodVector x.1 (rhoLambda g₀ n)
    rw [cuspFiberLift_periodVector, rhoLambda_g₀_apply]
  translation := 0
  map := ⟨cuspFiberClutching x, (cuspFiberClutching x).continuous⟩
  map_mk z := by
    change cuspFiberClutching x (Quotient.mk _ z) = Quotient.mk _ (cuspFiberLift x z) + 0
    rw [add_zero]
    rfl

/-! ## Integral homology coordinates of the cusp fibre -/

public theorem integralMatrix_rhoLambda_gZero :
    LinearMap.toMatrix' (rhoLambda g₀).toLinearMap = M₀ := by
  ext i j
  rw [LinearMap.toMatrix'_apply]
  convert congrFun (rhoLambda_g₀_apply (Pi.single j 1)) i using 1 <;> simp

public theorem exteriorSquareMatrix_rhoLambda_gZero :
    exteriorSquareMatrix (rhoLambda g₀) =
      SphereSixComplex.Topology.PaperCuspSpecializationAlgebra.mZeroExteriorTwoMatrix := by
  rw [exteriorSquareMatrix, integralMatrix_rhoLambda_gZero,
    SphereSixComplex.Topology.PaperCuspSpecializationAlgebra.mZeroExteriorTwoMatrix]

public theorem additiveTorusProjection_isOpenMap (p : Parameters) :
    IsOpenMap (additiveTorusProjection p) := by
  exact isOpenMap_quotient_mk'_mul

public theorem additiveTorus_pathConnected (p : Parameters) :
    PathConnectedSpace (AdditiveTorus p) :=
  Function.Surjective.pathConnectedSpace (f := Quotient.mk _)
    Quotient.mk_surjective continuous_quot_mk

/-- The standard integral bases of the cusp fibre, in which the descended cusp monodromy acts by
`M₀` in degree one and by its second compound in degree two. -/
public noncomputable def cuspMonodromyCoordinates (x : PeriodDomain) :
    letI := additiveTorus_pathConnected x.1
    CuspMonodromyCoordinates (cuspFiberClutching x) := by
  letI := additiveTorus_pathConnected x.1
  refine
    { degreeZero := pathConnectedIntegralHomologyZeroEquivInteger (AdditiveTorus x.1)
      degreeOne := (EstablishedTorusHomology.additiveTorusHomologyBasis x.1
        (fullRankDomain x)).degreeOne
      degreeTwo := (EstablishedTorusHomology.additiveTorusHomologyBasis x.1
        (fullRankDomain x)).degreeTwo
      degreeZero_monodromy := ?_
      degreeOne_monodromy := ?_
      degreeTwo_monodromy := ?_ }
  · intro y
    exact pathConnectedIntegralHomologyZeroEquivInteger_naturality
      (X := AdditiveTorus x.1) (Y := AdditiveTorus x.1)
      ⟨cuspFiberClutching x, (cuspFiberClutching x).continuous⟩ y
  · intro y
    have h := (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality x.1
      (fullRankDomain x) (cuspDescendedAffineTorusAutomorphism x)).1 y
    rw [show (cuspDescendedAffineTorusAutomorphism x).latticeMap = rhoLambda g₀ from rfl,
      rhoLambda_g₀_apply] at h
    exact h
  · intro y
    have h := (EstablishedTorusHomology.additiveTorusHomologyBasis_naturality x.1
      (fullRankDomain x) (cuspDescendedAffineTorusAutomorphism x)).2 y
    rw [show exteriorSquareMap (cuspDescendedAffineTorusAutomorphism x).latticeMap =
        (Matrix.toLin'
          (SphereSixComplex.Topology.PaperCuspSpecializationAlgebra.mZeroExteriorTwoMatrix)).toAddHom by
      rw [show (cuspDescendedAffineTorusAutomorphism x).latticeMap = rhoLambda g₀ from rfl,
        exteriorSquareMap, exteriorSquareMatrix_rhoLambda_gZero]] at h
    exact h

/-! ## Parabolic transport of real period coordinates

The cusp generator fixes the period lattice as a subgroup of `ℂ²` and moves only its marking.
In real period coordinates this says that changing the base point by `g₀` changes the
coordinates by `M₀`, with no fibrewise linear factor. -/

/-- The real period basis at `rhoParameters g₀ x` composed with `M₀` is the real period basis at
`x`.  This is the coordinate form of `cusp_periodVector`. -/
public theorem realEquiv_rhoParameters_gZero (x : PeriodDomain) (u : RealPeriods) :
    (fullRankDomain (rhoParameters g₀ x)).realEquiv (rhoLambdaReal g₀ u) =
      (fullRankDomain x).realEquiv u := by
  have hL : ((fullRankDomain (rhoParameters g₀ x)).realEquiv.toLinearMap.comp
        (rhoLambdaReal g₀).toLinearMap) =
      (fullRankDomain x).realEquiv.toLinearMap := by
    apply (Pi.basisFun ℝ (Fin 4)).ext
    intro i
    rw [← integerToReal_integralBasisVector]
    change (fullRankDomain (rhoParameters g₀ x)).realEquiv
        (rhoLambdaReal g₀ (integerToReal (integralBasisVector i))) =
      (fullRankDomain x).realEquiv (integerToReal (integralBasisVector i))
    rw [rhoLambdaReal_integer, (fullRankDomain (rhoParameters g₀ x)).map_integer,
      (fullRankDomain x).map_integer, rhoParameters_g₀_apply, rhoLambda_g₀_apply]
    rw [← m₀_apply]
    exact cusp_periodVector x.1 (integralBasisVector i)
  exact DFunLike.congr_fun hL u

/-- Changing the base point by the cusp generator transforms real period coordinates by `M₀`. -/
public theorem periodCoordinates_rhoParameters_gZero (x : PeriodDomain) (z : ComplexTwoSpace) :
    periodCoordinates (rhoParameters g₀ x) z = rhoLambdaReal g₀ (periodCoordinates x z) := by
  apply (fullRankDomain (rhoParameters g₀ x)).realEquiv.injective
  rw [realEquiv_rhoParameters_gZero]
  change (fullRankDomain (rhoParameters g₀ x)).realEquiv
      ((fullRankDomain (rhoParameters g₀ x)).realEquiv.symm z) =
    (fullRankDomain x).realEquiv ((fullRankDomain x).realEquiv.symm z)
  rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

/-- The identity map induces the identity on integral singular homology. -/
public theorem integralSingularHomologyMap_id_refl {X : Type} [TopologicalSpace X] (k : ℕ)
    (x : IntegralSingularHomology k X) :
    integralSingularHomologyMap k (ContinuousMap.id X) x = x := by
  change ConcreteCategory.hom
    (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom (ContinuousMap.id X))) x = x
  rw [show TopCat.ofHom (ContinuousMap.id X) = CategoryTheory.CategoryStruct.id (TopCat.of X) from
    rfl, CategoryTheory.Functor.map_id]
  rfl

/-- Two vectors have the same image in the period torus exactly when they differ by a period. -/
public theorem additiveTorusProjection_eq_iff (p : Parameters) (v w : ComplexTwoSpace) :
    additiveTorusProjection p v = additiveTorusProjection p w ↔
      ∃ m : IntegerPeriods, v = periodVector p m + w := by
  constructor
  · intro h
    have h' : MulAction.orbitRel (PeriodGroup p) ComplexTwoSpace v w := Quotient.exact h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h'
    obtain ⟨g, hg⟩ := h'
    obtain ⟨m, hm⟩ := g.toAdd.property
    exact ⟨m, by rw [show periodVector p m = (g.toAdd : ComplexTwoSpace) from hm]; exact hg.symm⟩
  · rintro ⟨m, rfl⟩
    apply Quotient.sound
    change MulAction.orbitRel (PeriodGroup p) ComplexTwoSpace _ w
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨Multiplicative.ofAdd ⟨periodVector p m, ⟨m, rfl⟩⟩, rfl⟩

/-- The descended clutching map is compatible with all integral powers of its lift. -/
public theorem additiveTorusProjection_cuspFiberLift_zpow (x : PeriodDomain) (j : ℤ) :
    ∀ w : ComplexTwoSpace,
      additiveTorusProjection x.1 ((cuspFiberLift x ^ j) w) =
        (cuspFiberClutching x ^ j) (additiveTorusProjection x.1 w) := by
  have hstep : ∀ w : ComplexTwoSpace,
      additiveTorusProjection x.1 (cuspFiberLift x w) =
        cuspFiberClutching x (additiveTorusProjection x.1 w) := fun _ ↦ rfl
  have hinv : ∀ w : ComplexTwoSpace,
      additiveTorusProjection x.1 ((cuspFiberLift x)⁻¹ w) =
        (cuspFiberClutching x)⁻¹ (additiveTorusProjection x.1 w) := by
    intro w
    apply (cuspFiberClutching x).injective
    rw [← hstep]
    change additiveTorusProjection x.1 ((cuspFiberLift x) ((cuspFiberLift x).symm w)) =
      (cuspFiberClutching x) ((cuspFiberClutching x).symm (additiveTorusProjection x.1 w))
    rw [(cuspFiberClutching x).apply_symm_apply, (cuspFiberLift x).apply_symm_apply]
  induction j using Int.induction_on with
  | zero => intro w; simp
  | succ n ih =>
      intro w
      rw [_root_.zpow_add_one, _root_.zpow_add_one, LinearEquiv.mul_apply,
        Homeomorph.mul_apply, ih (cuspFiberLift x w), hstep]
  | pred n ih =>
      intro w
      rw [_root_.zpow_sub_one, _root_.zpow_sub_one, LinearEquiv.mul_apply,
        Homeomorph.mul_apply, ih ((cuspFiberLift x)⁻¹ w), hinv w]

/-! ## The real mapping torus of the cusp fibre -/

/-- Real angular coordinate together with a fibre vector, projected to the real model of the
mapping torus of the cusp clutching map. -/
public noncomputable def realMappingTorusChart (x : PeriodDomain) :
    ℝ × ComplexTwoSpace → RealMappingTorus (cuspFiberClutching x) :=
  fun w ↦ Quotient.mk _ (w.1, additiveTorusProjection x.1 w.2)

public theorem realMappingTorusChart_continuous (x : PeriodDomain) :
    Continuous (realMappingTorusChart x) :=
  continuous_quot_mk.comp (continuous_fst.prodMk (continuous_quot_mk.comp continuous_snd))

public theorem realMappingTorusChart_isOpenMap (x : PeriodDomain) :
    IsOpenMap (realMappingTorusChart x) :=
  (isOpenMap_realMappingTorusMk _).comp
    (IsOpenMap.id.prodMap (additiveTorusProjection_isOpenMap x.1))

public theorem realMappingTorusChart_surjective (x : PeriodDomain) :
    Function.Surjective (realMappingTorusChart x) := by
  intro y
  obtain ⟨p, rfl⟩ := Quotient.mk_surjective y
  obtain ⟨v, hv⟩ := Quotient.mk_surjective p.2
  refine ⟨(p.1, v), ?_⟩
  change Quotient.mk _ (p.1, additiveTorusProjection x.1 v) = Quotient.mk _ p
  rw [show additiveTorusProjection x.1 v = p.2 from hv]

/-- Two angular-fibre pairs have the same class exactly when they differ by an integral shift of
the angle, the corresponding power of the clutching lift, and a period. -/
public theorem realMappingTorusChart_eq_iff (x : PeriodDomain) (w w' : ℝ × ComplexTwoSpace) :
    realMappingTorusChart x w = realMappingTorusChart x w' ↔
      ∃ (j : ℤ) (m : IntegerPeriods),
        w'.1 = w.1 - j ∧ w'.2 = periodVector x.1 m + (cuspFiberLift x ^ j) w.2 := by
  rw [realMappingTorusChart, realMappingTorusChart, realMappingTorusMk_eq_iff]
  constructor
  · rintro ⟨j, hj⟩
    have h1 : w'.1 = w.1 - j := congrArg Prod.fst hj
    have h2 : additiveTorusProjection x.1 w'.2 =
        (cuspFiberClutching x ^ j) (additiveTorusProjection x.1 w.2) := congrArg Prod.snd hj
    rw [← additiveTorusProjection_cuspFiberLift_zpow] at h2
    obtain ⟨m, hm⟩ := (additiveTorusProjection_eq_iff x.1 _ _).mp h2
    exact ⟨j, m, h1, hm⟩
  · rintro ⟨j, m, h1, h2⟩
    refine ⟨j, ?_⟩
    refine Prod.ext h1 ?_
    change additiveTorusProjection x.1 w'.2 =
      (cuspFiberClutching x ^ j) (additiveTorusProjection x.1 w.2)
    rw [h2, ← additiveTorusProjection_cuspFiberLift_zpow]
    exact (additiveTorusProjection_eq_iff x.1 _ _).mpr ⟨m, rfl⟩

/-! ## The fibre coordinate of the cusp collar -/

section Collar

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  (N : NormalizedFuchsianCuspCoordinate E D)

/-- The point of the period domain lying over the normalized cusp parameter `s`. -/
public noncomputable def cuspBasePoint (s : ℂ) : PeriodDomain :=
  parameterMap (assembledFuchsianPeriodFunctions E D) (N.lift s)

public theorem cuspBasePoint_val (s : ℂ) :
    (cuspBasePoint N s).1 = actualCuspCollarPeriodParameter N s := rfl

public theorem cuspBasePoint_shift (s : ℂ) (hs : s ∈ cuspHalfPlane N.height) :
    cuspBasePoint N (s - 1) = rhoParameters g₀ (cuspBasePoint N s) := by
  rw [cuspBasePoint, N.lift_shift s hs]
  exact parameterMap_equivariant (assembledFuchsianPeriodFunctions E D) g₀ (N.lift s)

/-- Reading the fibre over `s` in the real period basis at the marked parameter `s₀`. -/
public noncomputable def collarFiberEquiv (s₀ s : ℂ) :
    ComplexTwoSpace ≃ₗ[ℝ] ComplexTwoSpace :=
  (fullRankDomain (cuspBasePoint N s)).realEquiv.toLinearEquiv.symm.trans
    (fullRankDomain (cuspBasePoint N s₀)).realEquiv.toLinearEquiv

public theorem collarFiberEquiv_apply (s₀ s : ℂ) (zeta : ComplexTwoSpace) :
    collarFiberEquiv N s₀ s zeta =
      (fullRankDomain (cuspBasePoint N s₀)).realEquiv
        (periodCoordinates (cuspBasePoint N s) zeta) := rfl

/-- Every period of the fibre over `s` becomes the corresponding period of the marked fibre. -/
public theorem collarFiberEquiv_periodVector (s₀ s : ℂ) (m : IntegerPeriods) :
    collarFiberEquiv N s₀ s (periodVector (cuspBasePoint N s).1 m) =
      periodVector (cuspBasePoint N s₀).1 m := by
  rw [collarFiberEquiv_apply, periodCoordinates_periodVector,
    (fullRankDomain (cuspBasePoint N s₀)).map_integer]

/-- The one-step transport law: decreasing the normalized cusp parameter by one applies the
descended parabolic monodromy to the marked fibre coordinate. -/
public theorem collarFiberEquiv_sub_one (s₀ s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (zeta : ComplexTwoSpace) :
    collarFiberEquiv N s₀ (s - 1) zeta =
      cuspFiberLift (cuspBasePoint N s₀) (collarFiberEquiv N s₀ s zeta) := by
  rw [collarFiberEquiv_apply, collarFiberEquiv_apply, cuspFiberLift_apply,
    cuspBasePoint_shift N s hs, periodCoordinates_rhoParameters_gZero]
  congr 2
  change _ = (fullRankDomain (cuspBasePoint N s₀)).realEquiv.symm
      ((fullRankDomain (cuspBasePoint N s₀)).realEquiv
        (periodCoordinates (cuspBasePoint N s) zeta))
  rw [ContinuousLinearEquiv.symm_apply_apply]

/-- The integral transport law: the marked fibre coordinate over `s + k` is carried to the one
over `s` by the `k`-th power of the descended parabolic monodromy. -/
public theorem collarFiberEquiv_add_int (s₀ s : ℂ) (hs : s ∈ cuspHalfPlane N.height)
    (k : ℤ) (zeta : ComplexTwoSpace) :
    ((cuspFiberLift (cuspBasePoint N s₀)) ^ k)
        (collarFiberEquiv N s₀ (s + (k : ℂ)) zeta) =
      collarFiberEquiv N s₀ s zeta := by
  have hstep : ∀ t : ℂ, t ∈ cuspHalfPlane N.height →
      collarFiberEquiv N s₀ (t - 1) zeta =
        cuspFiberLift (cuspBasePoint N s₀) (collarFiberEquiv N s₀ t zeta) :=
    fun t ht ↦ collarFiberEquiv_sub_one N s₀ t ht zeta
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hmem : s + (((n : ℤ) + 1 : ℤ) : ℂ) ∈ cuspHalfPlane N.height :=
        cuspHalfPlane_add_int hs ((n : ℤ) + 1)
      have hsub : s + (((n : ℤ) + 1 : ℤ) : ℂ) - 1 = s + ((n : ℤ) : ℂ) := by
        push_cast; ring
      have h := hstep (s + (((n : ℤ) + 1 : ℤ) : ℂ)) hmem
      rw [hsub] at h
      rw [_root_.zpow_add_one, LinearEquiv.mul_apply, ← h]
      exact ih
  | pred n ih =>
      have hmem : s + ((-(n : ℤ) : ℤ) : ℂ) ∈ cuspHalfPlane N.height :=
        cuspHalfPlane_add_int hs (-(n : ℤ))
      have hsub : s + ((-(n : ℤ) : ℤ) : ℂ) - 1 = s + ((-(n : ℤ) - 1 : ℤ) : ℂ) := by
        push_cast; ring
      have h := hstep (s + ((-(n : ℤ) : ℤ) : ℂ)) hmem
      rw [hsub] at h
      rw [h, ← LinearEquiv.mul_apply, ← _root_.zpow_add_one, sub_add_cancel]
      exact ih

end Collar

/-! ## Polar coordinates on the normalized cusp parameter -/

section Polar

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge

/-- The normalized cusp parameter with prescribed cusp modulus and real part. -/
public noncomputable def cuspParameterOfPolar (rho x : ℝ) : ℂ :=
  ⟨x, -(Real.log rho) / (2 * Real.pi)⟩

public theorem norm_cuspQ_pos (s : ℂ) : 0 < ‖cuspQ s‖ := by
  rw [norm_cuspQ]
  exact Real.exp_pos _

public theorem norm_cuspQ_cuspParameterOfPolar (rho x : ℝ) (hrho : 0 < rho) :
    ‖cuspQ (cuspParameterOfPolar rho x)‖ = rho := by
  rw [norm_cuspQ]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have him : (cuspParameterOfPolar rho x).im = -(Real.log rho) / (2 * Real.pi) := rfl
  rw [him]
  rw [show -2 * Real.pi * (-(Real.log rho) / (2 * Real.pi)) = Real.log rho by
    field_simp]
  exact Real.exp_log hrho

public theorem cuspParameterOfPolar_norm_cuspQ (s : ℂ) :
    cuspParameterOfPolar ‖cuspQ s‖ s.re = s := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  apply Complex.ext
  · rfl
  · change -(Real.log ‖cuspQ s‖) / (2 * Real.pi) = s.im
    rw [norm_cuspQ, Real.log_exp]
    field_simp

public theorem cuspParameterOfPolar_eq (rho x : ℝ) :
    cuspParameterOfPolar rho x =
      (x : ℂ) + ((-(Real.log rho) / (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp only [cuspParameterOfPolar, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_I_re, Complex.mul_I_im, add_zero, zero_add, neg_zero]

public theorem continuous_cuspParameterOfPolar {r : ℝ} :
    Continuous (fun q : OpenRadialInterval r × ℝ ↦ cuspParameterOfPolar q.1.1 q.2) := by
  have hlog : Continuous (fun t : OpenRadialInterval r ↦ Real.log t.1) :=
    Real.continuousOn_log.comp_continuous continuous_subtype_val
      (fun t ↦ ne_of_gt t.2.1)
  simp only [cuspParameterOfPolar_eq]
  exact (Complex.continuous_ofReal.comp continuous_snd).add
    (((Complex.continuous_ofReal.comp
      (((hlog.comp continuous_fst).neg).div_const (2 * Real.pi)))).mul continuous_const)

end Polar

/-! ## The radial--angular--fibre trivialization of the additive cusp cover -/

section Trivialization

open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPuncturedCollarBridge
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPhaseEstimates
open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel
open SphereSixComplex.Geometry.EllipticRealPeriodProductTrivialization

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
  {N : NormalizedFuchsianCuspCoordinate E D}
  {M : Model}
  (W : ActualPuncturedCuspCollarWitness N M) (s₀ : ℂ)

public theorem mem_additiveCuspRadiusCover_iff (r : ℝ) (p : AdditiveCuspCover) :
    p ∈ additiveCuspRadiusCover r ↔ ‖cuspQ p.2‖ < r := Iff.rfl

public theorem collarFiberEquiv_eq_movingToFixed (s₀ s : ℂ) (zeta : ComplexTwoSpace) :
    collarFiberEquiv N s₀ s zeta =
      (movingToFixedCover (assembledFuchsianPeriodFunctions E D) (N.lift s₀)
        (N.lift s, zeta)).2 := rfl

public theorem collarFiberEquiv_symm_eq_fixedToMoving (s₀ s : ℂ) (w : ComplexTwoSpace) :
    (collarFiberEquiv N s₀ s).symm w =
      (fixedToMovingCover (assembledFuchsianPeriodFunctions E D) (N.lift s₀)
        (N.lift s, w)).2 := rfl

public theorem continuous_cuspQ : Continuous cuspQ :=
  Complex.continuous_exp.comp (continuous_const.mul continuous_id)

/-- Polar coordinates on the base together with the marked real-period basis on the fibre
trivialize the additive cusp cover. -/
public noncomputable def collarTrivialization :
    additiveCuspRadiusCover W.localWitness.radius ≃ₜ
      OpenRadialInterval W.localWitness.radius × ℝ × ComplexTwoSpace where
  toFun p := (⟨‖cuspQ p.1.2‖, ⟨norm_cuspQ_pos _, p.2⟩⟩, p.1.2.re,
    collarFiberEquiv N s₀ p.1.2 p.1.1)
  invFun q :=
    ⟨((collarFiberEquiv N s₀ (cuspParameterOfPolar q.1.1 q.2.1)).symm q.2.2,
        cuspParameterOfPolar q.1.1 q.2.1), by
      show ‖cuspQ (cuspParameterOfPolar q.1.1 q.2.1)‖ < W.localWitness.radius
      rw [norm_cuspQ_cuspParameterOfPolar _ _ q.1.2.1]
      exact q.1.2.2⟩
  left_inv p := by
    apply Subtype.ext
    have hs : cuspParameterOfPolar ‖cuspQ p.1.2‖ p.1.2.re = p.1.2 :=
      cuspParameterOfPolar_norm_cuspQ p.1.2
    simp only [hs]
    exact Prod.ext ((collarFiberEquiv N s₀ p.1.2).symm_apply_apply p.1.1) rfl
  right_inv q := by
    have hnorm : ‖cuspQ (cuspParameterOfPolar q.1.1 q.2.1)‖ = q.1.1 :=
      norm_cuspQ_cuspParameterOfPolar _ _ q.1.2.1
    refine Prod.ext (Subtype.ext hnorm) (Prod.ext rfl ?_)
    exact (collarFiberEquiv N s₀ (cuspParameterOfPolar q.1.1 q.2.1)).apply_symm_apply q.2.2
  continuous_toFun := by
    have hs : Continuous (fun p : additiveCuspRadiusCover W.localWitness.radius ↦ p.1.2) :=
      continuous_snd.comp continuous_subtype_val
    have hlift : Continuous (fun p : additiveCuspRadiusCover W.localWitness.radius ↦
        N.lift p.1.2) :=
      N.lift_holomorphic.continuousOn.comp_continuous hs
        (fun p ↦ additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p)
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)
    · exact ((continuous_norm.comp (continuous_cuspQ.comp hs))).subtype_mk _
    · exact Complex.continuous_re.comp hs
    · exact (continuous_snd.comp
        ((movingToFixedCover_continuous (assembledFuchsianPeriodFunctions E D)
          (N.lift s₀)).comp
          (hlift.prodMk (continuous_fst.comp continuous_subtype_val))))
  continuous_invFun := by
    have hpolar : Continuous (fun q : OpenRadialInterval W.localWitness.radius × ℝ ×
        ComplexTwoSpace ↦ cuspParameterOfPolar q.1.1 q.2.1) :=
      continuous_cuspParameterOfPolar.comp
        (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
    have hmem : ∀ q : OpenRadialInterval W.localWitness.radius × ℝ × ComplexTwoSpace,
        cuspParameterOfPolar q.1.1 q.2.1 ∈ cuspHalfPlane N.height := by
      intro q
      refine mem_cuspHalfPlane_of_norm_cuspQ_lt W.localWitness.radius_le ?_
      rw [norm_cuspQ_cuspParameterOfPolar _ _ q.1.2.1]
      exact q.1.2.2
    have hlift : Continuous (fun q : OpenRadialInterval W.localWitness.radius × ℝ ×
        ComplexTwoSpace ↦ N.lift (cuspParameterOfPolar q.1.1 q.2.1)) :=
      N.lift_holomorphic.continuousOn.comp_continuous hpolar hmem
    apply Continuous.subtype_mk
    refine Continuous.prodMk ?_ hpolar
    exact continuous_snd.comp
      ((fixedToMovingCover_continuous (assembledFuchsianPeriodFunctions E D)
        (N.lift s₀)).comp (hlift.prodMk (continuous_snd.comp continuous_snd)))

/-! ## The two quotient presentations of the punctured cusp collar -/

/-- Translating the additive fibre coordinate by a first-block period. -/
public noncomputable def psiTranslate (a : additiveCuspRadiusCover W.localWitness.radius)
    (lambda : ParameterLattice) : additiveCuspRadiusCover W.localWitness.radius :=
  ⟨((periodBlock (actualCuspCollarPeriodParameter N a.1.2)).mulVec
      (fun i ↦ (lambda i : ℂ)) + a.1.1, a.1.2), a.2⟩

public theorem psiTranslate_fst (a : additiveCuspRadiusCover W.localWitness.radius)
    (lambda : ParameterLattice) :
    (psiTranslate W a lambda).1.1 =
      periodVector (cuspBasePoint N a.1.2).1 (firstPeriodCoefficients lambda) + a.1.1 := by
  rw [psiTranslate, periodVector_firstPeriodCoefficients]
  rfl

public theorem psiTranslate_snd (a : additiveCuspRadiusCover W.localWitness.radius)
    (lambda : ParameterLattice) : (psiTranslate W a lambda).1.2 = a.1.2 := rfl

/-- The actual phase-corrected action reads, in additive coordinates, as translation by the
corresponding first-block period. -/
public theorem puncturedPsiMap_psiTranslate
    (a : additiveCuspRadiusCover W.localWitness.radius) (lambda : ParameterLattice) :
    puncturedPsiMap W lambda
        (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ a)) =
      additiveToPuncturedLocalHomeomorph M W.localWitness.radius
        (Quotient.mk _ (psiTranslate W a lambda)) := by
  let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
  apply Subtype.ext
  change
    (CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.localWitness.radius W.localWitness.radius_pos
          W.localWitness.radius_le).psiMap lambda (e (Quotient.mk _ a)).1 =
      (e (Quotient.mk _ (psiTranslate W a lambda))).1
  rw [show ((e (Quotient.mk _ a)).1 : LocalCarrier M W.localWitness.radius) =
      localCuspExponentialPoint M W.localWitness.radius a.1.1 a.1.2
        (mem_ball_zero_iff.mpr a.2) from
    additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius a,
    show ((e (Quotient.mk _ (psiTranslate W a lambda))).1 :
        LocalCarrier M W.localWitness.radius) =
      localCuspExponentialPoint M W.localWitness.radius (psiTranslate W a lambda).1.1
        (psiTranslate W a lambda).1.2
        (mem_ball_zero_iff.mpr (psiTranslate W a lambda).2) from
    additiveToPuncturedLocalHomeomorph_mk M W.localWitness.radius (psiTranslate W a lambda)]
  exact localCuspExponentialPoint_period_equivariant N M
    W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    a.1.2 (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a)
    (mem_ball_zero_iff.mpr a.2) a.1.1 lambda

/-- The additive cusp cover projected onto the punctured local cusp quotient. -/
public noncomputable def collarPeriodPointMap :
    additiveCuspRadiusCover W.localWitness.radius → puncturedLocalCuspQuotient W :=
  fun a ↦ Quotient.mk _
    (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ a))

public theorem collarPeriodPointMap_apply {s : ℂ}
    (hs : ‖cuspQ s‖ < W.localWitness.radius) (zeta : ComplexTwoSpace) :
    collarPeriodPointMap W ⟨(zeta, s), hs⟩ = actualCuspCollarPeriodPoint W hs zeta := rfl

public theorem collarPeriodPointMap_isQuotientMap :
    IsQuotientMap (collarPeriodPointMap W) := by
  have h1 : IsQuotientMap (fun a : additiveCuspRadiusCover W.localWitness.radius ↦
      (Quotient.mk (Setoid.ker (denseCuspExponentialRadius W.localWitness.radius)) a)) :=
    isQuotientMap_quotient_mk'
  have h2 := (additiveToPuncturedLocalHomeomorph M W.localWitness.radius).isQuotientMap
  have h3 : IsQuotientMap (fun p : {p : LocalCarrier M W.localWitness.radius // M.t p ≠ 0} ↦
      (Quotient.mk (puncturedPsiOrbitRel W) p)) := isQuotientMap_quotient_mk'
  exact (h3.comp h2).comp h1

/-- Two additive cusp coordinates define the same point of the punctured local cusp quotient
exactly when they differ by a first-block period, an integral fibre period, and an integral shift
of the normalized cusp parameter. -/
public theorem collarPeriodPointMap_eq_iff
    (a b : additiveCuspRadiusCover W.localWitness.radius) :
    collarPeriodPointMap W a = collarPeriodPointMap W b ↔
      ∃ (lambda n : ParameterLattice) (k : ℤ),
        periodVector (cuspBasePoint N b.1.2).1 (firstPeriodCoefficients lambda) + b.1.1 =
            a.1.1 + (fun i ↦ ((n i : ℤ) : ℂ)) ∧
          b.1.2 = a.1.2 + k := by
  let e := additiveToPuncturedLocalHomeomorph M W.localWitness.radius
  let _ := puncturedPsiAction W
  constructor
  · intro h
    have h' : MulAction.orbitRel (Multiplicative ParameterLattice) _
        (e (Quotient.mk _ a)) (e (Quotient.mk _ b)) := Quotient.exact h
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h'
    obtain ⟨g, hg⟩ := h'
    have hg' : puncturedPsiMap W (Multiplicative.toAdd g) (e (Quotient.mk _ b)) =
        e (Quotient.mk _ a) := hg
    rw [puncturedPsiMap_psiTranslate] at hg'
    have hquot : (Quotient.mk _ (psiTranslate W b (Multiplicative.toAdd g)) :
        Quotient (Setoid.ker (denseCuspExponentialRadius W.localWitness.radius))) =
        Quotient.mk _ a := e.injective hg'
    have hker : denseCuspExponentialRadius W.localWitness.radius
        (psiTranslate W b (Multiplicative.toAdd g)) =
        denseCuspExponentialRadius W.localWitness.radius a := Quotient.exact hquot
    have hdense : denseCuspExponentialCover (psiTranslate W b (Multiplicative.toAdd g)).1 =
        denseCuspExponentialCover a.1 := congrArg Subtype.val hker
    obtain ⟨n₀, n₁, n₂, hn₀, hn₁, hn₂⟩ := (denseCuspExponentialCover_eq_iff _ _).mp hdense
    refine ⟨Multiplicative.toAdd g, ![n₀, n₁], n₂, ?_, ?_⟩
    · rw [← psiTranslate_fst W b (Multiplicative.toAdd g)]
      funext i
      fin_cases i
      · exact hn₀
      · exact hn₁
    · exact hn₂
  · rintro ⟨lambda, n, k, hzeta, hs⟩
    have hdense : denseCuspExponentialCover (psiTranslate W b lambda).1 =
        denseCuspExponentialCover a.1 := by
      refine (denseCuspExponentialCover_eq_iff _ _).mpr ⟨n 0, n 1, k, ?_, ?_, ?_⟩
      · rw [psiTranslate_fst]
        exact congrFun hzeta 0
      · rw [psiTranslate_fst]
        exact congrFun hzeta 1
      · exact hs
    have hquot : (Quotient.mk _ (psiTranslate W b lambda) :
        Quotient (Setoid.ker (denseCuspExponentialRadius W.localWitness.radius))) =
        Quotient.mk _ a := Quotient.sound (Subtype.ext hdense)
    have hpsi : puncturedPsiMap W lambda (e (Quotient.mk _ b)) = e (Quotient.mk _ a) := by
      rw [puncturedPsiMap_psiTranslate, hquot]
    change (Quotient.mk _ (e (Quotient.mk _ a)) : puncturedLocalCuspQuotient W) =
      Quotient.mk _ (e (Quotient.mk _ b))
    refine Quotient.sound ?_
    change MulAction.orbitRel (Multiplicative ParameterLattice) _
      (e (Quotient.mk _ a)) (e (Quotient.mk _ b))
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    exact ⟨Multiplicative.ofAdd lambda, hpsi⟩

/-! ## Comparison of the two presentations -/

public theorem firstPeriodCoefficients_neg (c : ParameterLattice) :
    firstPeriodCoefficients (-c) = -firstPeriodCoefficients c := by
  funext i
  fin_cases i <;> simp [firstPeriodCoefficients]

public theorem im_eq_of_norm_cuspQ_eq {s t : ℂ} (h : ‖cuspQ s‖ = ‖cuspQ t‖) : s.im = t.im := by
  rw [norm_cuspQ, norm_cuspQ, Real.exp_eq_exp] at h
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have : (-2 * Real.pi) * s.im = (-2 * Real.pi) * t.im := h
  have hne : (-2 * Real.pi) ≠ 0 := by
    simp [hpi]
  exact mul_left_cancel₀ hne this

public theorem collarFiberEquiv_shift (s₀ s : ℂ) (hs : s ∈ cuspHalfPlane N.height) (k : ℤ)
    (zeta : ComplexTwoSpace) :
    collarFiberEquiv N s₀ (s + (k : ℂ)) zeta =
      ((cuspFiberLift (cuspBasePoint N s₀)) ^ (-k)) (collarFiberEquiv N s₀ s zeta) := by
  have h := collarFiberEquiv_add_int N s₀ s hs k zeta
  rw [← h, ← LinearEquiv.mul_apply, ← _root_.zpow_add, neg_add_cancel, zpow_zero]
  rfl

/-- The additive cusp cover projected onto the radial mapping-torus model. -/
public noncomputable def collarRadialMap :
    additiveCuspRadiusCover W.localWitness.radius →
      OpenRadialInterval W.localWitness.radius ×
        RealMappingTorus (cuspFiberClutching (cuspBasePoint N s₀)) :=
  Prod.map id (realMappingTorusChart (cuspBasePoint N s₀)) ∘ collarTrivialization W s₀

public theorem collarRadialMap_isQuotientMap :
    IsQuotientMap (collarRadialMap W s₀) := by
  have hopen : IsOpenMap (collarRadialMap W s₀) :=
    (IsOpenMap.id.prodMap (realMappingTorusChart_isOpenMap _)).comp
      (collarTrivialization W s₀).isOpenMap
  have hcont : Continuous (collarRadialMap W s₀) :=
    (continuous_id.prodMap (realMappingTorusChart_continuous _)).comp
      (collarTrivialization W s₀).continuous
  have hsurj : Function.Surjective (collarRadialMap W s₀) :=
    (Function.Surjective.prodMap Function.surjective_id
      (realMappingTorusChart_surjective _)).comp (collarTrivialization W s₀).surjective
  exact hopen.isQuotientMap hcont hsurj

public theorem periodVector_neg (x : Parameters) (a : IntegerPeriods) :
    periodVector x (-a) = -periodVector x a := (periodHom x).map_neg a

public theorem periodVector_sub (x : Parameters) (a b : IntegerPeriods) :
    periodVector x (a - b) = periodVector x a - periodVector x b := (periodHom x).map_sub a b

/-- The two presentations of the punctured cusp collar have exactly the same fibres. -/
public theorem collarPeriodPointMap_eq_iff_collarRadialMap
    (a b : additiveCuspRadiusCover W.localWitness.radius) :
    collarPeriodPointMap W a = collarPeriodPointMap W b ↔
      collarRadialMap W s₀ a = collarRadialMap W s₀ b := by
  have ha : a.1.2 ∈ cuspHalfPlane N.height :=
    additiveCuspRadiusCover_halfPlane W.localWitness.radius_le a
  have hRHS : (collarRadialMap W s₀ a = collarRadialMap W s₀ b) ↔
      (‖cuspQ a.1.2‖ = ‖cuspQ b.1.2‖ ∧
        realMappingTorusChart (cuspBasePoint N s₀)
            (a.1.2.re, collarFiberEquiv N s₀ a.1.2 a.1.1) =
          realMappingTorusChart (cuspBasePoint N s₀)
            (b.1.2.re, collarFiberEquiv N s₀ b.1.2 b.1.1)) := by
    constructor
    · intro h
      exact ⟨congrArg Subtype.val (congrArg Prod.fst h), congrArg Prod.snd h⟩
    · rintro ⟨h1, h2⟩
      exact Prod.ext (Subtype.ext h1) h2
  rw [hRHS, realMappingTorusChart_eq_iff, collarPeriodPointMap_eq_iff]
  constructor
  · rintro ⟨lambda, n, k, hzeta, hs⟩
    have hnorm : ‖cuspQ a.1.2‖ = ‖cuspQ b.1.2‖ := by
      rw [hs, cuspQ_add_int]
    refine ⟨hnorm, -k, identityPeriodCoefficients n - firstPeriodCoefficients lambda, ?_, ?_⟩
    · show b.1.2.re = a.1.2.re - ((-k : ℤ) : ℝ)
      rw [hs]
      simp
    · show collarFiberEquiv N s₀ b.1.2 b.1.1 =
        periodVector (cuspBasePoint N s₀).1
            (identityPeriodCoefficients n - firstPeriodCoefficients lambda) +
          ((cuspFiberLift (cuspBasePoint N s₀)) ^ (-k))
            (collarFiberEquiv N s₀ a.1.2 a.1.1)
      have hid : periodVector (cuspBasePoint N b.1.2).1 (identityPeriodCoefficients n) =
          fun i ↦ ((n i : ℤ) : ℂ) :=
        periodVector_identityPeriodCoefficients _ n
      have hzeta' : b.1.1 =
          periodVector (cuspBasePoint N b.1.2).1
            (identityPeriodCoefficients n - firstPeriodCoefficients lambda) + a.1.1 := by
        rw [periodVector_sub, hid]
        rw [show ((fun i ↦ ((n i : ℤ) : ℂ)) : ComplexTwoSpace) =
            periodVector (cuspBasePoint N b.1.2).1 (firstPeriodCoefficients lambda) + b.1.1 -
              a.1.1 by rw [hzeta]; abel]
        abel
      rw [hzeta', map_add, collarFiberEquiv_periodVector]
      congr 1
      rw [hs, collarFiberEquiv_shift s₀ a.1.2 ha k a.1.1]
  · rintro ⟨hnorm, j, m, hre, hu⟩
    have hre' : b.1.2.re = a.1.2.re - (j : ℝ) := hre
    have hu' : collarFiberEquiv N s₀ b.1.2 b.1.1 =
        periodVector (cuspBasePoint N s₀).1 m +
          ((cuspFiberLift (cuspBasePoint N s₀)) ^ j)
            (collarFiberEquiv N s₀ a.1.2 a.1.1) := hu
    have him : b.1.2.im = a.1.2.im := im_eq_of_norm_cuspQ_eq hnorm.symm
    have hs : b.1.2 = a.1.2 + ((-j : ℤ) : ℂ) := by
      apply Complex.ext
      · rw [hre']
        simp
        ring
      · rw [him]
        simp
    have hshift : ((cuspFiberLift (cuspBasePoint N s₀)) ^ j)
        (collarFiberEquiv N s₀ a.1.2 a.1.1) = collarFiberEquiv N s₀ b.1.2 a.1.1 := by
      rw [hs, collarFiberEquiv_shift s₀ a.1.2 ha (-j) a.1.1, neg_neg]
    have hzeta : b.1.1 = periodVector (cuspBasePoint N b.1.2).1 m + a.1.1 := by
      apply (collarFiberEquiv N s₀ b.1.2).injective
      rw [map_add, collarFiberEquiv_periodVector, hu', hshift]
    refine ⟨-(firstParameterCoefficients m), identityParameterCoefficients m, -j, ?_, hs⟩
    have hdec := integerPeriods_decompose m
    have hm : periodVector (cuspBasePoint N b.1.2).1 m =
        periodVector (cuspBasePoint N b.1.2).1
            (firstPeriodCoefficients (firstParameterCoefficients m)) +
          periodVector (cuspBasePoint N b.1.2).1
            (identityPeriodCoefficients (identityParameterCoefficients m)) := by
      conv_lhs => rw [hdec]
      rw [periodVector_add]
    rw [hzeta, firstPeriodCoefficients_neg, periodVector_neg, hm,
      periodVector_identityPeriodCoefficients]
    abel

/-! ## The radial mapping-torus presentation of the punctured cusp collar -/

public theorem homeomorphOfQuotientMaps_apply {Z A B : Type*} [TopologicalSpace Z]
    [TopologicalSpace A] [TopologicalSpace B] {f : Z → A} {g : Z → B}
    (hf : IsQuotientMap f) (hg : IsQuotientMap g)
    (hfibre : ∀ w w' : Z, f w = f w' ↔ g w = g w') (w : Z) :
    CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps hf hg hfibre (f w) = g w :=
  (hfibre _ _).mp (Function.surjInv_eq hf.surjective (f w))

public theorem realMappingTorusHomeomorph_symm_fiberInclusion {T : Type} [TopologicalSpace T]
    (phi : T ≃ₜ T) (y : T) :
    (realMappingTorusHomeomorph phi).symm
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) y) =
      Quotient.mk (realMappingTorusSetoid phi) ((0 : ℝ), y) := rfl

public theorem collarFiberEquiv_self (s₀ : ℂ) (zeta : ComplexTwoSpace) :
    collarFiberEquiv N s₀ s₀ zeta = zeta := by
  rw [collarFiberEquiv_apply]
  change (fullRankDomain (cuspBasePoint N s₀)).realEquiv
    ((fullRankDomain (cuspBasePoint N s₀)).realEquiv.symm zeta) = zeta
  rw [ContinuousLinearEquiv.apply_symm_apply]

/-- Polar coordinates on the base and the marked real period basis on the fibre identify the
punctured local cusp quotient with the open radial interval times the mapping torus of the
descended parabolic monodromy. -/
public noncomputable def puncturedLocalCuspQuotientHomeomorph :
    puncturedLocalCuspQuotient W ≃ₜ
      OpenRadialInterval W.localWitness.radius ×
        CircleMappingTorus (cuspFiberClutching (cuspBasePoint N s₀)) :=
  (CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
      (collarPeriodPointMap_isQuotientMap W) (collarRadialMap_isQuotientMap W s₀)
      (collarPeriodPointMap_eq_iff_collarRadialMap W s₀)).trans
    ((Homeomorph.refl (OpenRadialInterval W.localWitness.radius)).prodCongr
      (realMappingTorusHomeomorph _))

public theorem puncturedLocalCuspQuotientHomeomorph_apply
    (a : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspQuotientHomeomorph W s₀ (collarPeriodPointMap W a) =
      ((collarRadialMap W s₀ a).1,
        realMappingTorusHomeomorph _ (collarRadialMap W s₀ a).2) := by
  change ((Homeomorph.refl (OpenRadialInterval W.localWitness.radius)).prodCongr
      (realMappingTorusHomeomorph _))
    (CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
      (collarPeriodPointMap_isQuotientMap W) (collarRadialMap_isQuotientMap W s₀)
      (collarPeriodPointMap_eq_iff_collarRadialMap W s₀) (collarPeriodPointMap W a)) = _
  rw [homeomorphOfQuotientMaps_apply]
  rfl

public theorem realMappingTorusHomeomorph_mk_zero {T : Type} [TopologicalSpace T]
    (phi : T ≃ₜ T) (y : T) :
    realMappingTorusHomeomorph phi (Quotient.mk (realMappingTorusSetoid phi) ((0 : ℝ), y)) =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) y := by
  rw [← realMappingTorusHomeomorph_symm_fiberInclusion, Homeomorph.apply_symm_apply]

/-! ## The marked fibre -/

/-- The marked normalized cusp parameter: purely imaginary, halfway down the collar. -/
public noncomputable def markedCuspParameter : ℂ :=
  cuspParameterOfPolar (W.localWitness.radius / 2) 0

public theorem markedCuspParameter_norm :
    ‖cuspQ (markedCuspParameter W)‖ = W.localWitness.radius / 2 :=
  norm_cuspQ_cuspParameterOfPolar _ _ (by
    have := W.localWitness.radius_pos
    linarith)

public theorem markedCuspParameter_mem :
    ‖cuspQ (markedCuspParameter W)‖ < W.localWitness.radius := by
  rw [markedCuspParameter_norm]
  have := W.localWitness.radius_pos
  linarith

public theorem markedCuspParameter_re : (markedCuspParameter W).re = 0 := rfl

/-- The marked radial coordinate. -/
public noncomputable def markedCuspRadius : OpenRadialInterval W.localWitness.radius :=
  ⟨‖cuspQ (markedCuspParameter W)‖, ⟨norm_cuspQ_pos _, markedCuspParameter_mem W⟩⟩

/-- Over the marked fibre the radial mapping-torus presentation is the bare period
projection. -/
public theorem collarRadialMap_marked (zeta : ComplexTwoSpace) :
    collarRadialMap W (markedCuspParameter W)
        ⟨(zeta, markedCuspParameter W), markedCuspParameter_mem W⟩ =
      (markedCuspRadius W,
        Quotient.mk (realMappingTorusSetoid
            (cuspFiberClutching (cuspBasePoint N (markedCuspParameter W))))
          ((0 : ℝ),
            additiveTorusProjection (cuspBasePoint N (markedCuspParameter W)).1 zeta)) := by
  refine Prod.ext rfl ?_
  change Quotient.mk _ ((markedCuspParameter W).re,
      additiveTorusProjection (cuspBasePoint N (markedCuspParameter W)).1
        (collarFiberEquiv N (markedCuspParameter W) (markedCuspParameter W) zeta)) = _
  rw [markedCuspParameter_re, collarFiberEquiv_self]

/-! ## The radial clutching datum of the actual punctured cusp collar -/

/-- The radial fundamental-domain datum of the actual punctured cusp collar, with its fibre
marking normalized against the collar's own period coordinates. -/
public noncomputable def actualCuspRadialClutchingData :
    ActualCuspRadialClutchingData W where
  Fiber := AdditiveTorus (cuspBasePoint N (markedCuspParameter W)).1
  fiberTopology := instTopologicalSpaceQuotient
  clutching := cuspFiberClutching (cuspBasePoint N (markedCuspParameter W))
  totalHomeomorph := puncturedLocalCuspQuotientHomeomorph W (markedCuspParameter W)
  monodromyCoordinates := cuspMonodromyCoordinates (cuspBasePoint N (markedCuspParameter W))
  fiberParameter := (cuspBasePoint N (markedCuspParameter W)).1
  fiberFullRank := fullRankDomain (cuspBasePoint N (markedCuspParameter W))
  fiberHomeomorph := Homeomorph.refl _
  fiberMarkingCompatibility := by
    intro _ x
    change (EstablishedTorusHomology.additiveTorusHomologyBasis
        (cuspBasePoint N (markedCuspParameter W)).1
        (fullRankDomain (cuspBasePoint N (markedCuspParameter W)))).degreeOne
      (integralSingularHomologyMap 1 (ContinuousMap.id _) x) = _
    rw [integralSingularHomologyMap_id_refl]
    rfl
  fiberMarkingCompatibilityTwo := by
    intro _ x
    change (EstablishedTorusHomology.additiveTorusHomologyBasis
        (cuspBasePoint N (markedCuspParameter W)).1
        (fullRankDomain (cuspBasePoint N (markedCuspParameter W)))).degreeTwo
      (integralSingularHomologyMap 2 (ContinuousMap.id _) x) = _
    rw [integralSingularHomologyMap_id_refl]
    rfl
  markingParameter := markedCuspParameter W
  markingParameter_mem := markedCuspParameter_mem W
  markingRadius := markedCuspRadius W
  fiberParameter_eq := rfl
  fiberNormalization := by
    intro _ y zeta
    have hpoint : actualCuspCollarPeriodPoint W (markedCuspParameter_mem W) zeta =
        collarPeriodPointMap W
          ⟨(zeta, markedCuspParameter W), markedCuspParameter_mem W⟩ := rfl
    rw [Homeomorph.symm_apply_eq, hpoint, puncturedLocalCuspQuotientHomeomorph_apply,
      collarRadialMap_marked, realMappingTorusHomeomorph_mk_zero]
    constructor
    · intro h
      have h2 : finiteBouquetMappingTorusFiberInclusion
            (fun _ : Unit ↦ cuspFiberClutching (cuspBasePoint N (markedCuspParameter W))) y =
          finiteBouquetMappingTorusFiberInclusion
            (fun _ : Unit ↦ cuspFiberClutching (cuspBasePoint N (markedCuspParameter W)))
            (additiveTorusProjection (cuspBasePoint N (markedCuspParameter W)).1 zeta) :=
        congrArg Prod.snd h
      have h3 := congrArg (realMappingTorusHomeomorph
        (cuspFiberClutching (cuspBasePoint N (markedCuspParameter W)))).symm h2
      rw [realMappingTorusHomeomorph_symm_fiberInclusion,
        realMappingTorusHomeomorph_symm_fiberInclusion] at h3
      obtain ⟨k, hk⟩ := (realMappingTorusMk_eq_iff _ _ _).mp h3
      have hk1 : (0 : ℝ) - (k : ℝ) = 0 := (congrArg Prod.fst hk).symm
      have hk0 : k = 0 := by
        have : (k : ℝ) = 0 := by linarith
        exact_mod_cast this
      have hk2 := congrArg Prod.snd hk
      rw [hk0] at hk2
      change additiveTorusProjection (cuspBasePoint N (markedCuspParameter W)).1 zeta =
        ((cuspFiberClutching (cuspBasePoint N (markedCuspParameter W))) ^ (0 : ℤ)) y at hk2
      rw [zpow_zero] at hk2
      exact hk2.symm
    · intro h
      change y = additiveTorusProjection (cuspBasePoint N (markedCuspParameter W)).1 zeta at h
      rw [h]

end Trivialization

end Geometry.CuspRadialClutchingConstruction

end SphereSixComplex
