module

public import SphereSixComplex.Topology.SectionSevenLerayChainModel

/-!
# Finite-rank duality for the Section 7 Leray model

The unresolved coefficient in `sectionSevenLerayChainModel top` is the transpose of the fourth
possible Leray differential.  This file isolates the finite integer algebra by pairing the
complementary groups in degrees `(1,5)` and `(2,4)`.  The pairing matrices are explicit and
unimodular.  If the known degree-two boundary and the unresolved degree-five boundary are adjoint
up to the usual orientation sign, evaluation on basis vectors forces `top = ±1`.

No manifold, cap product, fundamental class, or topological Poincaré-duality assertion occurs here.
The only input is the displayed adjointness equation between homomorphisms of free abelian groups.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Matrix

namespace SphereSixComplex

/-- The standard perfect pairing between the rank-one groups in degrees one and five. -/
public def sectionSevenOneFivePairingMatrix : Matrix (Fin 1) (Fin 1) ℤ := !![1]

/-- The hyperbolic perfect pairing between the rank-two groups in degrees two and four. -/
public def sectionSevenTwoFourPairingMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![0, 1;
     1, 0]

@[simp]
public theorem sectionSevenOneFivePairingMatrix_det :
    sectionSevenOneFivePairingMatrix.det = 1 := by
  change (1 : ℤ) = 1
  rfl

@[simp]
public theorem sectionSevenTwoFourPairingMatrix_det :
    sectionSevenTwoFourPairingMatrix.det = -1 := by
  norm_num [sectionSevenTwoFourPairingMatrix, Matrix.det_fin_two]

public theorem sectionSevenOneFivePairingMatrix_square :
    sectionSevenOneFivePairingMatrix * sectionSevenOneFivePairingMatrix = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  norm_num [sectionSevenOneFivePairingMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem sectionSevenTwoFourPairingMatrix_square :
    sectionSevenTwoFourPairingMatrix * sectionSevenTwoFourPairingMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sectionSevenTwoFourPairingMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- Unimodularity of the degree `(1,5)` pairing, expressed on the underlying lattices. -/
public theorem sectionSevenOneFivePairingMatrix_bijective :
    Function.Bijective sectionSevenOneFivePairingMatrix.mulVec := by
  constructor
  · intro x y hxy
    have h := congrArg sectionSevenOneFivePairingMatrix.mulVec hxy
    simpa [Matrix.mulVec_mulVec, sectionSevenOneFivePairingMatrix_square] using h
  · intro y
    refine ⟨sectionSevenOneFivePairingMatrix.mulVec y, ?_⟩
    simp [Matrix.mulVec_mulVec, sectionSevenOneFivePairingMatrix_square]

/-- Unimodularity of the degree `(2,4)` pairing, expressed on the underlying lattices. -/
public theorem sectionSevenTwoFourPairingMatrix_bijective :
    Function.Bijective sectionSevenTwoFourPairingMatrix.mulVec := by
  constructor
  · intro x y hxy
    have h := congrArg sectionSevenTwoFourPairingMatrix.mulVec hxy
    simpa [Matrix.mulVec_mulVec, sectionSevenTwoFourPairingMatrix_square] using h
  · intro y
    refine ⟨sectionSevenTwoFourPairingMatrix.mulVec y, ?_⟩
    simp [Matrix.mulVec_mulVec, sectionSevenTwoFourPairingMatrix_square]

/-- The explicit integral pairing of degrees one and five. -/
public def sectionSevenOneFivePairing (x y : Fin 1 → ℤ) : ℤ :=
  dotProduct x (sectionSevenOneFivePairingMatrix.mulVec y)

/-- The explicit integral pairing of degrees two and four. -/
public def sectionSevenTwoFourPairing (x y : Fin 2 → ℤ) : ℤ :=
  dotProduct x (sectionSevenTwoFourPairingMatrix.mulVec y)

/-- Minimal algebraic duality data: the two fixed unimodular pairings make the known and unresolved
boundaries adjoint, up to an orientation sign. -/
public structure SectionSevenLerayAlgebraicDuality (top : ℤ) where
  /-- The orientation sign in the boundary-adjointness identity. -/
  sign : ℤ
  /-- An orientation sign is a unit with value `1` or `-1`. -/
  sign_eq_one_or_neg_one : sign = 1 ∨ sign = -1
  /-- Adjointness of the complementary boundaries under the explicit perfect pairings. -/
  boundary_adjoint : ∀ (x : Fin 2 → ℤ) (y : Fin 1 → ℤ),
    sectionSevenOneFivePairing (sectionSevenLerayBoundaryTwo x) y =
      sign * sectionSevenTwoFourPairing x (sectionSevenLerayBoundaryFive top y)

/-- The explicit unimodular adjointness equation forces the unresolved coefficient to be a unit. -/
public theorem SectionSevenLerayAlgebraicDuality.top_eq_one_or_neg_one
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    top = 1 ∨ top = -1 := by
  have hadj := h.boundary_adjoint ![1, 0] ![1]
  simp [sectionSevenOneFivePairing, sectionSevenTwoFourPairing,
    sectionSevenOneFivePairingMatrix, sectionSevenTwoFourPairingMatrix,
    sectionSevenLerayBoundaryTwo, sectionSevenLerayBoundaryFive,
    chosenLerayDifferential, twistObstruction, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ] at hadj
  rcases h.sign_eq_one_or_neg_one with hs | hs
  · right
    simp [hs] at hadj
    omega
  · left
    simp [hs] at hadj
    omega

/-- Algebraic duality supplies exactness of the model in degree four. -/
public theorem SectionSevenLerayAlgebraicDuality.exactAt_four
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    (sectionSevenLerayChainModel top).ExactAt 4 :=
  sectionSevenLerayChainModel_exactAt_four top h.top_eq_one_or_neg_one

/-- Algebraic duality supplies exactness of the model in degree five. -/
public theorem SectionSevenLerayAlgebraicDuality.exactAt_five
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    (sectionSevenLerayChainModel top).ExactAt 5 :=
  sectionSevenLerayChainModel_exactAt_five top h.top_eq_one_or_neg_one

/-- Algebraic duality makes the degree-four homology object zero. -/
public theorem SectionSevenLerayAlgebraicDuality.homology_four_isZero
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    IsZero ((sectionSevenLerayChainModel top).homology 4) :=
  h.exactAt_four.isZero_homology

/-- Algebraic duality makes the degree-five homology object zero. -/
public theorem SectionSevenLerayAlgebraicDuality.homology_five_isZero
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    IsZero ((sectionSevenLerayChainModel top).homology 5) :=
  h.exactAt_five.isZero_homology

/-- Algebraic duality forces every middle homology object of the finite model to vanish. -/
public theorem SectionSevenLerayAlgebraicDuality.middle_homology_isZero
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) (k : ℕ)
    (h1 : 1 ≤ k) (h5 : k ≤ 5) :
    IsZero ((sectionSevenLerayChainModel top).homology k) :=
  sectionSevenLerayChainModel_middle_homology_isZero top h.top_eq_one_or_neg_one k h1 h5

/-- The degree-zero homology of every member of the Leray-model family is infinite cyclic. -/
public noncomputable def sectionSevenLerayChainModel_homology_zero_equiv (top : ℤ) :
    (sectionSevenLerayChainModel top).homology 0 ≃+ ℤ := by
  let S := (sectionSevenLerayChainModel top).sc' 1 0 0
  have hf : S.f = 0 := by rfl
  have hg : S.g = 0 := by rfl
  let h := ShortComplex.HomologyData.ofZeros S hf hg
  exact
    ((ShortComplex.homologyMapIso
      ((sectionSevenLerayChainModel top).isoSc' 1 0 0 (by simp) (by simp))).trans
      h.left.homologyIso).addCommGroupIsoToAddEquiv.trans finOneIntegerAddEquiv

/-- Complete sphere-shaped homology of the finite model: `ℤ` in degrees zero and six, and zero
in every intervening degree. -/
public theorem SectionSevenLerayAlgebraicDuality.sphere_shaped_model_homology
    {top : ℤ} (h : SectionSevenLerayAlgebraicDuality top) :
    Nonempty ((sectionSevenLerayChainModel top).homology 0 ≃+ ℤ) ∧
      (∀ k : ℕ, 1 ≤ k → k ≤ 5 →
        IsZero ((sectionSevenLerayChainModel top).homology k)) ∧
      Nonempty ((sectionSevenLerayChainModel top).homology 6 ≃+ ℤ) :=
  ⟨⟨sectionSevenLerayChainModel_homology_zero_equiv top⟩,
    h.middle_homology_isZero, ⟨sectionSevenLerayChainModel_homology_six_equiv top⟩⟩

end SphereSixComplex
