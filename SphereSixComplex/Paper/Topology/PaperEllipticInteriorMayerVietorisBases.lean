module

public import SphereSixComplex.Paper.Topology.CircleMappingTorusHomologyBases
public import SphereSixComplex.Paper.Topology.PaperEllipticTwoDiscCover

/-!
# Mayer–Vietoris for the elliptic two-disc cover

The degree-one difference matrix has a rank-one kernel and a primitive cokernel coordinate.
The actual open cover also supplies canonical Mayer–Vietoris connecting maps and exact
presentations in degrees one and two, without choosing degree-two bases for the interior.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology Matrix Set TopologicalSpace

namespace SphereSixComplex

/-- The actual degree-one difference matrix from the two reduced central fibres.  The first
coordinates carry the covering indices three and four; these factors cannot be removed by an
integral change of basis. -/
public def ellipticActualHOneDifferenceMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 3,  0,  0,  0;
      0,  2,  1,  3;
     -4,  0,  0,  0;
      0, -1, -1, -2]

/-- A primitive cokernel coordinate for the actual degree-one difference matrix. -/
public def ellipticActualHOneCokernelFunctional (x : Fin 4 → ℤ) : ℤ :=
  4 * x 0 + 3 * x 2

@[simp]
public theorem ellipticActualHOne_generator_mem_kernel :
    ellipticActualHOneDifferenceMatrix *ᵥ alphaOneKernelGenerator = 0 := by
  funext i
  fin_cases i <;>
    norm_num [ellipticActualHOneDifferenceMatrix, alphaOneKernelGenerator, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- The actual integral degree-one matrix has the same rank-one kernel as the normalized matrix. -/
public theorem ellipticActualHOne_kernel (x : Fin 4 → ℤ) :
    ellipticActualHOneDifferenceMatrix *ᵥ x = 0 ↔
      ∃ t : ℤ, x = t • alphaOneKernelGenerator := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    refine ⟨x 3, ?_⟩
    funext i
    fin_cases i <;>
      simp [ellipticActualHOneDifferenceMatrix, alphaOneKernelGenerator, Matrix.mulVec,
        dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3 ⊢ <;>
      omega
  · rintro ⟨t, rfl⟩
    rw [Matrix.mulVec_smul, ellipticActualHOne_generator_mem_kernel, smul_zero]

/-- The image of the actual degree-one matrix is the kernel of its primitive coordinate. -/
public theorem ellipticActualHOne_image_iff (x : Fin 4 → ℤ) :
    (∃ y : Fin 4 → ℤ, ellipticActualHOneDifferenceMatrix *ᵥ y = x) ↔
      ellipticActualHOneCokernelFunctional x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    simp [ellipticActualHOneDifferenceMatrix, ellipticActualHOneCokernelFunctional,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    ring
  · intro h
    refine ⟨![-x 0 - x 2, x 1 + x 3, -x 1 - 2 * x 3, 0], ?_⟩
    funext i
    fin_cases i <;>
      simp [ellipticActualHOneDifferenceMatrix, ellipticActualHOneCokernelFunctional,
        Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h ⊢ <;>
      omega

/-- The actual degree-one cokernel coordinate is primitive. -/
public theorem ellipticActualHOneCokernelFunctional_surjective :
    Function.Surjective ellipticActualHOneCokernelFunctional := by
  intro z
  refine ⟨![z, 0, -z, 0], ?_⟩
  simp [ellipticActualHOneCokernelFunctional]
  ring

def ellipticActualHOneLinear : (Fin 4 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
  ellipticActualHOneDifferenceMatrix.mulVecLin

def ellipticActualHOneFunctionalLinear : (Fin 4 → ℤ) →ₗ[ℤ] ℤ where
  toFun := ellipticActualHOneCokernelFunctional
  map_add' x y := by simp [ellipticActualHOneCokernelFunctional]; ring
  map_smul' n x := by simp [ellipticActualHOneCokernelFunctional]; ring

theorem range_ellipticActualHOneLinear_eq_ker :
    LinearMap.range ellipticActualHOneLinear =
      LinearMap.ker ellipticActualHOneFunctionalLinear := by
  ext x
  change (∃ y, ellipticActualHOneDifferenceMatrix *ᵥ y = x) ↔
    ellipticActualHOneCokernelFunctional x = 0
  exact ellipticActualHOne_image_iff x

noncomputable def ellipticActualHOneCokernelEquivInt :
    ((Fin 4 → ℤ) ⧸ LinearMap.range ellipticActualHOneLinear) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ range_ellipticActualHOneLinear_eq_ker).trans
    (ellipticActualHOneFunctionalLinear.quotKerEquivOfSurjective
      ellipticActualHOneCokernelFunctional_surjective)

theorem map_range_eq_of_comm
    {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup A'] [AddCommGroup B']
    (eA : A ≃ₗ[ℤ] A') (eB : B ≃ₗ[ℤ] B') (f : A →ₗ[ℤ] B) (g : A' →ₗ[ℤ] B')
    (h : eB.toLinearMap.comp f = g.comp eA.toLinearMap) :
    (LinearMap.range f).map eB.toLinearMap = LinearMap.range g := by
  ext y
  constructor
  · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
    exact ⟨eA a, (DFunLike.congr_fun h a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨eB.symm (g a), ⟨eA.symm a, ?_⟩, eB.apply_symm_apply _⟩
    apply eB.injective
    simpa using DFunLike.congr_fun h (eA.symm a)

noncomputable def cokernelEquivOfComm
    {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup A'] [AddCommGroup B']
    (eA : A ≃ₗ[ℤ] A') (eB : B ≃ₗ[ℤ] B') (f : A →ₗ[ℤ] B) (g : A' →ₗ[ℤ] B')
    (h : eB.toLinearMap.comp f = g.comp eA.toLinearMap) :
    (B ⧸ LinearMap.range f) ≃ₗ[ℤ] B' ⧸ LinearMap.range g :=
  Submodule.Quotient.equiv _ _ eB (map_range_eq_of_comm eA eB f g h)

def kernelEquivFinZeroOfInjective
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (f : A →ₗ[ℤ] B) (hf : Function.Injective f) :
    LinearMap.ker f ≃ₗ[ℤ] (Fin 0 → ℤ) where
  toFun _ i := Fin.elim0 i
  invFun _ := (0 : LinearMap.ker f)
  map_add' _ _ := by funext i; exact Fin.elim0 i
  map_smul' _ _ := by funext i; exact Fin.elim0 i
  left_inv x := by
    change (0 : LinearMap.ker f) = x
    apply Subtype.ext
    apply hf
    change f (0 : A) = f x
    rw [map_zero, LinearMap.mem_ker.mp x.2]
  right_inv x := by funext i; exact Fin.elim0 i

def intProdFinZeroEquivFinOne : (ℤ × (Fin 0 → ℤ)) ≃ₗ[ℤ] (Fin 1 → ℤ) where
  toFun x _ := x.1
  invFun x := (x 0, fun i ↦ Fin.elim0 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext i
      exact Fin.elim0 i
  right_inv x := by funext i; fin_cases i; rfl

namespace Geometry.AnalyticData

variable {A : AnalyticData}

namespace EllipticTwoDiscHomologyCoordinates

variable {D : A.EllipticTwoDiscCoverData}

/-- The order-three side as an open subspace of the elliptic interior. -/
public def orderThreeOpen (D : A.EllipticTwoDiscCoverData) :
    Opens (TopCat.of A.ellipticInterior) where
  carrier := D.orderThreeSide
  is_open' := D.orderThreeSide_isOpen

/-- The order-four side as an open subspace of the elliptic interior. -/
public def orderFourOpen (D : A.EllipticTwoDiscCoverData) :
    Opens (TopCat.of A.ellipticInterior) where
  carrier := D.orderFourSide
  is_open' := D.orderFourSide_isOpen

/-- The two paper sides form a binary open cover of the elliptic interior. -/
public theorem ellipticOpenCover (D : A.EllipticTwoDiscCoverData) :
    orderThreeOpen D ⊔ orderFourOpen D = ⊤ := by
  ext x
  simpa [orderThreeOpen, orderFourOpen] using Set.ext_iff.mp D.sides_cover x

/-- The canonical chain-level Mayer--Vietoris data for the elliptic two-disc cover. -/
public noncomputable def canonicalMayerVietorisData
    (D : A.EllipticTwoDiscCoverData) :=
  BinaryOpenCover.OpenCoverHomologyComparison.toIntegralMayerVietorisData
    (BinaryOpenCover.openCoverHomologyComparisonOfCover (ellipticOpenCover D))
    (ellipticOpenCover D)

/-- The canonical connecting map for the elliptic two-disc cover. -/
public noncomputable def canonicalBoundary
    (D : A.EllipticTwoDiscCoverData) (n : ℕ) :=
  (canonicalMayerVietorisData D).legacyBoundary n

noncomputable def presentationOne :
    WangHomologyPresentation
      (IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior))
      (IntegralSingularHomology 1 D.orderThreeSide ×
        IntegralSingularHomology 1 D.orderFourSide)
      (IntegralSingularHomology 1
        (D.orderThreeSide ∪ D.orderFourSide : Set A.ellipticInterior))
      (IntegralSingularHomology 0
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior))
      (IntegralSingularHomology 0 D.orderThreeSide ×
        IntegralSingularHomology 0 D.orderFourSide) := by
  let M := canonicalMayerVietorisData D
  have h := M.legacyBoundary_exact
  exact
    { highDifference := IntegralMayerVietoris.differenceMap
        D.orderThreeSide D.orderFourSide 1
      inclusion := IntegralMayerVietoris.sumMap D.orderThreeSide D.orderFourSide 1
      boundary := M.legacyBoundary 0
      lowDifference := IntegralMayerVietoris.differenceMap
        D.orderThreeSide D.orderFourSide 0
      exact_highDifference_inclusion := (h 1).2.2
      exact_inclusion_boundary := (h 0).1
      exact_boundary_lowDifference := (h 0).2.1 }

noncomputable def presentationTwo :
    WangHomologyPresentation
      (IntegralSingularHomology 2
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior))
      (IntegralSingularHomology 2 D.orderThreeSide ×
        IntegralSingularHomology 2 D.orderFourSide)
      (IntegralSingularHomology 2
        (D.orderThreeSide ∪ D.orderFourSide : Set A.ellipticInterior))
      (IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.ellipticInterior))
      (IntegralSingularHomology 1 D.orderThreeSide ×
        IntegralSingularHomology 1 D.orderFourSide) := by
  let M := canonicalMayerVietorisData D
  have h := M.legacyBoundary_exact
  exact
    { highDifference := IntegralMayerVietoris.differenceMap
        D.orderThreeSide D.orderFourSide 2
      inclusion := IntegralMayerVietoris.sumMap D.orderThreeSide D.orderFourSide 2
      boundary := M.legacyBoundary 1
      lowDifference := IntegralMayerVietoris.differenceMap
        D.orderThreeSide D.orderFourSide 1
      exact_highDifference_inclusion := (h 2).2.2
      exact_inclusion_boundary := (h 1).1
      exact_boundary_lowDifference := (h 1).2.1 }

end EllipticTwoDiscHomologyCoordinates

end Geometry.AnalyticData

end SphereSixComplex
