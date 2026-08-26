module

public import SphereSixComplex.Topology.CircleMappingTorusHomologyBases
public import SphereSixComplex.Topology.PaperEllipticTwoDiscCover

/-!
# Homology bases from the elliptic two-disc cover

This file performs the purely algebraic Mayer--Vietoris step behind Lemma 7.19.  Given bases in
which the two actual difference maps are the integral covering-index matrix in degree one and
`alphaTwoMatrix` in degree two, it constructs `H₁ ≅ ℤ` and `H₂ ≅ ℤ²` for the elliptic
interior.  No basis of the interior is assumed.
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

def alphaTwoLinear : (Fin 6 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) :=
  alphaTwoMatrix.mulVecLin

def ellipticActualHOneFunctionalLinear : (Fin 4 → ℤ) →ₗ[ℤ] ℤ where
  toFun := ellipticActualHOneCokernelFunctional
  map_add' x y := by simp [ellipticActualHOneCokernelFunctional]; ring
  map_smul' n x := by simp [ellipticActualHOneCokernelFunctional]; ring

def alphaTwoFunctionalLinear : (Fin 4 → ℤ) →ₗ[ℤ] ℤ where
  toFun := alphaTwoFunctional
  map_add' x y := by simp [alphaTwoFunctional]; ring
  map_smul' n x := by simp [alphaTwoFunctional]; ring

theorem range_ellipticActualHOneLinear_eq_ker :
    LinearMap.range ellipticActualHOneLinear =
      LinearMap.ker ellipticActualHOneFunctionalLinear := by
  ext x
  change (∃ y, ellipticActualHOneDifferenceMatrix *ᵥ y = x) ↔
    ellipticActualHOneCokernelFunctional x = 0
  exact ellipticActualHOne_image_iff x

theorem range_alphaTwoLinear_eq_ker :
    LinearMap.range alphaTwoLinear = LinearMap.ker alphaTwoFunctionalLinear := by
  ext x
  change (∃ y, alphaTwoMatrix *ᵥ y = x) ↔ alphaTwoFunctional x = 0
  exact alphaTwo_image_iff x

noncomputable def ellipticActualHOneCokernelEquivInt :
    ((Fin 4 → ℤ) ⧸ LinearMap.range ellipticActualHOneLinear) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ range_ellipticActualHOneLinear_eq_ker).trans
    (ellipticActualHOneFunctionalLinear.quotKerEquivOfSurjective
      ellipticActualHOneCokernelFunctional_surjective)

noncomputable def alphaTwoCokernelEquivInt :
    ((Fin 4 → ℤ) ⧸ LinearMap.range alphaTwoLinear) ≃ₗ[ℤ] ℤ :=
  (Submodule.quotEquivOfEq _ _ range_alphaTwoLinear_eq_ker).trans
    (alphaTwoFunctionalLinear.quotKerEquivOfSurjective alphaTwoFunctional_surjective)

def ellipticActualHOneKernelEquivInt : LinearMap.ker ellipticActualHOneLinear ≃ₗ[ℤ] ℤ where
  toFun x := x.1 3
  invFun n := ⟨n • alphaOneKernelGenerator, by
    rw [LinearMap.mem_ker]
    rw [map_smul]
    change n • (ellipticActualHOneDifferenceMatrix *ᵥ alphaOneKernelGenerator) = 0
    rw [ellipticActualHOne_generator_mem_kernel, smul_zero]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    apply Subtype.ext
    obtain ⟨n, hn⟩ := (ellipticActualHOne_kernel x.1).mp x.2
    have h3 := congrFun hn (3 : Fin 4)
    simp [alphaOneKernelGenerator] at h3
    simpa [h3] using hn.symm
  right_inv n := by simp [alphaOneKernelGenerator]

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

theorem map_ker_eq_of_comm
    {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup A'] [AddCommGroup B']
    (eA : A ≃ₗ[ℤ] A') (eB : B ≃ₗ[ℤ] B') (f : A →ₗ[ℤ] B) (g : A' →ₗ[ℤ] B')
    (h : eB.toLinearMap.comp f = g.comp eA.toLinearMap) :
    (LinearMap.ker f).map eA.toLinearMap = LinearMap.ker g := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    apply LinearMap.mem_ker.mpr
    have hh := DFunLike.congr_fun h a
    simp only [LinearMap.coe_comp, Function.comp_apply] at hh
    rw [← hh, LinearMap.mem_ker.mp ha, map_zero]
  · intro hx
    refine ⟨eA.symm x, ?_, eA.apply_symm_apply x⟩
    apply LinearMap.mem_ker.mpr
    apply eB.injective
    rw [eB.map_zero]
    have hh := DFunLike.congr_fun h (eA.symm x)
    simp only [LinearMap.coe_comp, Function.comp_apply] at hh
    exact hh.trans <| (congrArg g (eA.apply_symm_apply x)).trans (LinearMap.mem_ker.mp hx)

def kernelEquivOfComm
    {A B A' B' : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup A'] [AddCommGroup B']
    (eA : A ≃ₗ[ℤ] A') (eB : B ≃ₗ[ℤ] B') (f : A →ₗ[ℤ] B) (g : A' →ₗ[ℤ] B')
    (h : eB.toLinearMap.comp f = g.comp eA.toLinearMap) :
    LinearMap.ker f ≃ₗ[ℤ] LinearMap.ker g :=
  eA.ofSubmodules _ _ (map_ker_eq_of_comm eA eB f g h)

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

def intProdEquivFinTwo : (ℤ × ℤ) ≃ₗ[ℤ] (Fin 2 → ℤ) where
  toFun z := ![z.1, z.2]
  invFun f := (f 0, f 1)
  map_add' x y := by funext i; fin_cases i <;> rfl
  map_smul' n x := by funext i; fin_cases i <;> rfl
  left_inv z := by rcases z with ⟨x, y⟩; rfl
  right_inv f := by funext i; fin_cases i <;> rfl

namespace Geometry.PaperAnalyticData

variable {A : PaperAnalyticData}

/-- Exact coordinate input for the two-disc Mayer--Vietoris calculation.  It contains bases only
on the overlap and the two sides, not on their union. -/
public structure SectionSevenEllipticTwoDiscHomologyCoordinates
    (D : A.SectionSevenEllipticTwoDiscCoverData) where
  bandOne :
    IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃+
      (Fin 4 → ℤ)
  sidesOne :
    (IntegralSingularHomology 1 D.orderThreeSide ×
      IntegralSingularHomology 1 D.orderFourSide) ≃+ (Fin 4 → ℤ)
  differenceOne : ∀ x,
    sidesOne (IntegralMayerVietoris.differenceMap
      D.orderThreeSide D.orderFourSide 1 x) =
        ellipticActualHOneDifferenceMatrix *ᵥ bandOne x
  bandTwo :
    IntegralSingularHomology 2
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior) ≃+
      (Fin 6 → ℤ)
  sidesTwo :
    (IntegralSingularHomology 2 D.orderThreeSide ×
      IntegralSingularHomology 2 D.orderFourSide) ≃+ (Fin 4 → ℤ)
  differenceTwo : ∀ x,
    sidesTwo (IntegralMayerVietoris.differenceMap
      D.orderThreeSide D.orderFourSide 2 x) = alphaTwoMatrix *ᵥ bandTwo x
  differenceZero_injective : Function.Injective
    (IntegralMayerVietoris.differenceMap D.orderThreeSide D.orderFourSide 0)

namespace SectionSevenEllipticTwoDiscHomologyCoordinates

variable {D : A.SectionSevenEllipticTwoDiscCoverData}
  (B : A.SectionSevenEllipticTwoDiscHomologyCoordinates D)

/-- The order-three side as an open subspace of the elliptic interior. -/
public def orderThreeOpen (D : A.SectionSevenEllipticTwoDiscCoverData) :
    Opens (TopCat.of A.SectionSevenEllipticInterior) where
  carrier := D.orderThreeSide
  is_open' := D.orderThreeSide_isOpen

/-- The order-four side as an open subspace of the elliptic interior. -/
public def orderFourOpen (D : A.SectionSevenEllipticTwoDiscCoverData) :
    Opens (TopCat.of A.SectionSevenEllipticInterior) where
  carrier := D.orderFourSide
  is_open' := D.orderFourSide_isOpen

/-- The two paper sides form a binary open cover of the elliptic interior. -/
public theorem ellipticOpenCover (D : A.SectionSevenEllipticTwoDiscCoverData) :
    orderThreeOpen D ⊔ orderFourOpen D = ⊤ := by
  ext x
  simpa [orderThreeOpen, orderFourOpen] using Set.ext_iff.mp D.sides_cover x

/-- The canonical chain-level Mayer--Vietoris data for the elliptic two-disc cover. -/
public noncomputable def canonicalMayerVietorisData
    (D : A.SectionSevenEllipticTwoDiscCoverData) :=
  BinaryOpenCover.OpenCoverHomologyComparison.toIntegralMayerVietorisData
    (BinaryOpenCover.openCoverHomologyComparisonOfCover (ellipticOpenCover D))
    (ellipticOpenCover D)

/-- The canonical connecting map for the elliptic two-disc cover. -/
public noncomputable def canonicalBoundary
    (D : A.SectionSevenEllipticTwoDiscCoverData) (n : ℕ) :=
  (canonicalMayerVietorisData D).legacyBoundary n

theorem differenceOne_linear_comm :
    B.sidesOne.toIntLinearEquiv.toLinearMap.comp
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide 1).toIntLinearMap =
      ellipticActualHOneLinear.comp B.bandOne.toIntLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact B.differenceOne x

theorem differenceTwo_linear_comm :
    B.sidesTwo.toIntLinearEquiv.toLinearMap.comp
        (IntegralMayerVietoris.differenceMap
          D.orderThreeSide D.orderFourSide 2).toIntLinearMap =
      alphaTwoLinear.comp B.bandTwo.toIntLinearEquiv.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact B.differenceTwo x

theorem exactSequence :
    IntegralMayerVietoris.ExactSequence D.orderThreeSide D.orderFourSide :=
  establishedIntegralMayerVietorisExactSequence D.orderThreeSide D.orderFourSide
    D.orderThreeSide_isOpen D.orderFourSide_isOpen

noncomputable def presentationOne :
    WangHomologyPresentation
      (IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior))
      (IntegralSingularHomology 1 D.orderThreeSide ×
        IntegralSingularHomology 1 D.orderFourSide)
      (IntegralSingularHomology 1
        (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior))
      (IntegralSingularHomology 0
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior))
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
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior))
      (IntegralSingularHomology 2 D.orderThreeSide ×
        IntegralSingularHomology 2 D.orderFourSide)
      (IntegralSingularHomology 2
        (D.orderThreeSide ∪ D.orderFourSide : Set A.SectionSevenEllipticInterior))
      (IntegralSingularHomology 1
        (D.orderThreeSide ∩ D.orderFourSide : Set A.SectionSevenEllipticInterior))
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

/-- The degree-one presentation uses the canonical open-cover connecting map. -/
public theorem presentationOne_boundary :
    (presentationOne (D := D)).boundary = canonicalBoundary D 0 := by
  rfl

/-- The degree-two presentation uses the canonical open-cover connecting map. -/
public theorem presentationTwo_boundary :
    (presentationTwo (D := D)).boundary = canonicalBoundary D 1 := by
  rfl

/-- The two-disc coordinate calculation constructs `H₁(X°; ℤ) ≅ ℤ`. -/
public noncomputable def ellipticInteriorHomologyOneEquiv :
    IntegralSingularHomology 1 A.SectionSevenEllipticInterior ≃+ (Fin 1 → ℤ) := by
  let P := presentationOne (D := D)
  let coinvariants :=
    (cokernelEquivOfComm B.bandOne.toIntLinearEquiv B.sidesOne.toIntLinearEquiv
      P.highDifference.toIntLinearMap ellipticActualHOneLinear
        B.differenceOne_linear_comm).trans
      ellipticActualHOneCokernelEquivInt
  let invariants := kernelEquivFinZeroOfInjective P.lowDifference.toIntLinearMap
    B.differenceZero_injective
  let eUnion := (P.totalLinearEquivOfEndCoordinates coinvariants invariants).trans
    intProdFinZeroEquivFinOne
  let eTop := integralSingularHomologyEquiv 1
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  exact (eTop.symm.toIntLinearEquiv.trans eUnion).toAddEquiv

/-- The two-disc coordinate calculation constructs `H₂(X°; ℤ) ≅ ℤ²`. -/
public noncomputable def ellipticInteriorHomologyTwoEquiv :
    IntegralSingularHomology 2 A.SectionSevenEllipticInterior ≃+ (Fin 2 → ℤ) := by
  let P := presentationTwo (D := D)
  let coinvariants :=
    (cokernelEquivOfComm B.bandTwo.toIntLinearEquiv B.sidesTwo.toIntLinearEquiv
      P.highDifference.toIntLinearMap alphaTwoLinear B.differenceTwo_linear_comm).trans
      alphaTwoCokernelEquivInt
  let invariants :=
    (kernelEquivOfComm B.bandOne.toIntLinearEquiv B.sidesOne.toIntLinearEquiv
      P.lowDifference.toIntLinearMap ellipticActualHOneLinear
        B.differenceOne_linear_comm).trans
      ellipticActualHOneKernelEquivInt
  let eUnion := (P.totalLinearEquivOfEndCoordinates coinvariants invariants).trans
    intProdEquivFinTwo
  let eTop := integralSingularHomologyEquiv 2
    (topologicalSubsetHomeomorphOfEqUniv (TopCat.of A.SectionSevenEllipticInterior)
      (D.orderThreeSide ∪ D.orderFourSide) D.sides_cover)
  exact (eTop.symm.toIntLinearEquiv.trans eUnion).toAddEquiv

end SectionSevenEllipticTwoDiscHomologyCoordinates

end Geometry.PaperAnalyticData

end SphereSixComplex
