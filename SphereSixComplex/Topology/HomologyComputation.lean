module

public import SphereSixComplex.Topology.HomologySphere
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The finite integral calculations in Section 7

The paper does not give a finite singular chain complex for the glued threefold.  It gives the
following presentation and specialization matrices and then uses Mayer--Vietoris exactness,
sweeping arguments, duality, and universal coefficients.  This file verifies the finite integer
algebra and records the remaining topological identification as an explicit realization contract.
-/

@[expose] public section

noncomputable section

open Matrix

namespace SphereSixComplex

/-- The obstruction `12ℓ₀ - 4ℓ₁ - 3ℓ₂` from Theorem 7.17. -/
public def twistObstruction (ℓ₀ ℓ₁ ℓ₂ : ℤ) : ℤ := 12 * ℓ₀ - 4 * ℓ₁ - 3 * ℓ₂

@[simp]
public theorem chosen_twistObstruction : twistObstruction 0 1 (-1) = -1 := by
  norm_num [twistObstruction]

/-- The two-generator relation matrix from Theorem 7.17, for twists `(0,1,-1)`. -/
public def twistRelationMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![3, -1;
     4, -1]

/-- An integral inverse to `twistRelationMatrix`. -/
public def twistRelationInverse : Matrix (Fin 2) (Fin 2) ℤ :=
  !![-1, 1;
     -4, 3]

@[simp]
public theorem twistRelationMatrix_det : twistRelationMatrix.det = 1 := by
  norm_num [twistRelationMatrix, Matrix.det_fin_two]

public theorem twistRelation_left_inverse :
    twistRelationInverse * twistRelationMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twistRelationInverse, twistRelationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

public theorem twistRelation_right_inverse :
    twistRelationMatrix * twistRelationInverse = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twistRelationInverse, twistRelationMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The relation map has zero kernel and full image, so its cokernel is trivial. -/
public theorem twistRelationMatrix_bijective :
    Function.Bijective twistRelationMatrix.mulVec := by
  constructor
  · intro x y h
    have h' := congrArg twistRelationInverse.mulVec h
    simpa [Matrix.mulVec_mulVec, twistRelation_left_inverse] using h'
  · intro y
    refine ⟨twistRelationInverse.mulVec y, ?_⟩
    simp [Matrix.mulVec_mulVec, twistRelation_right_inverse]

/-- The redundant `H₁` presentation in generators `(c, g₁, g₂)`. -/
public def firstHomologyRelationMatrix : Matrix (Fin 3) (Fin 2) ℤ :=
  !![-37, 1;
      3, 0;
      0, 4]

/-- The primitive functional `Φ₁=(12,148,-3)` in the corrected target basis. -/
public def firstHomologyFunctional (x : Fin 3 → ℤ) : ℤ :=
  12 * x 0 + 148 * x 1 - 3 * x 2

public theorem firstHomologyFunctional_relation (y : Fin 2 → ℤ) :
    firstHomologyFunctional (firstHomologyRelationMatrix.mulVec y) = 0 := by
  simp [firstHomologyFunctional, firstHomologyRelationMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- The relation lattice is exactly the kernel of `Φ₁`. -/
public theorem firstHomologyRelation_iff (x : Fin 3 → ℤ) :
    (∃ y : Fin 2 → ℤ, firstHomologyRelationMatrix.mulVec y = x) ↔
      firstHomologyFunctional x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact firstHomologyFunctional_relation y
  · intro h
    unfold firstHomologyFunctional at h
    have hbmod : x 1 % 3 = 0 := by
      omega
    obtain ⟨b, hb⟩ : ∃ b : ℤ, x 1 = 3 * b := ⟨x 1 / 3, by omega⟩
    have hcmod : x 2 % 4 = 0 := by
      omega
    obtain ⟨c, hc⟩ : ∃ c : ℤ, x 2 = 4 * c := ⟨x 2 / 4, by omega⟩
    refine ⟨![b, c], ?_⟩
    funext i
    fin_cases i <;>
      simp [firstHomologyRelationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
        at h hb hc ⊢ <;>
      ring_nf at h hb hc ⊢ <;>
      omega

public theorem firstHomologyPresentation_exact :
    Function.Exact firstHomologyRelationMatrix.mulVec firstHomologyFunctional := by
  intro x
  simpa only [Set.mem_range] using (firstHomologyRelation_iff x).symm

/-- `Φ₁` is onto; hence the presentation quotient is infinite cyclic. -/
public theorem firstHomologyFunctional_surjective :
    Function.Surjective firstHomologyFunctional := by
  intro z
  refine ⟨![-12 * z, z, z], ?_⟩
  simp [firstHomologyFunctional]
  ring

/-- The attaching class used in the paper maps to the obstruction `p=-1`. -/
@[simp]
public theorem firstHomologyFunctional_attachment :
    firstHomologyFunctional ![12, -1, -1] = -1 := by
  change 12 * 12 + 148 * (-1) - 3 * (-1) = -1
  norm_num

/-- The map `α₁` in the bases `(γ,u,w,δ)` used in Lemma 7.19. -/
public def alphaOneMatrix : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 1,  0,  0,  0;
      0,  2,  1,  3;
     -1,  0,  0,  0;
      0, -1, -1, -2]

/-- The generator `ν₀=(0,-1,-1,1)` of `ker α₁`. -/
public def alphaOneKernelGenerator : Fin 4 → ℤ := ![0, -1, -1, 1]

@[simp]
public theorem alphaOne_generator_mem_kernel :
    alphaOneMatrix.mulVec alphaOneKernelGenerator = 0 := by
  funext i
  fin_cases i <;>
    norm_num [alphaOneMatrix, alphaOneKernelGenerator, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- The paper's claimed kernel calculation `ker α₁ = ℤν₀`. -/
public theorem alphaOne_kernel (x : Fin 4 → ℤ) :
    alphaOneMatrix.mulVec x = 0 ↔
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
      simp [alphaOneMatrix, alphaOneKernelGenerator, Matrix.mulVec, dotProduct,
        Fin.sum_univ_succ] at h0 h1 h2 h3 ⊢ <;>
      omega
  · rintro ⟨t, rfl⟩
    rw [Matrix.mulVec_smul, alphaOne_generator_mem_kernel, smul_zero]

/-- The six displayed columns of `α₂` in Remark 7.20. -/
public def alphaTwoMatrix : Matrix (Fin 4) (Fin 6) ℤ :=
  !![ 2,  1,  3,  0, 0, 0;
     -4, -2,  0,  1, 0, 0;
     -2, -2, -4,  0, 0, 0;
      3,  3,  0, -1, 0, 0]

/-- The minor on rows `0,1,2` and columns `0,1,3`, displayed with determinant `2`. -/
public def alphaTwoMinorTwo : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ 2,  1, 0;
     -4, -2, 1;
     -2, -2, 0]

/-- The minor on rows `0,1,3` and columns `0,1,3`, displayed with determinant `-3`. -/
public def alphaTwoMinorMinusThree : Matrix (Fin 3) (Fin 3) ℤ :=
  !![ 2,  1,  0;
     -4, -2,  1;
      3,  3, -1]

@[simp]
public theorem alphaTwoMinorTwo_det : alphaTwoMinorTwo.det = 2 := by
  rw [Matrix.det_fin_three]
  norm_num [alphaTwoMinorTwo]
  decide

@[simp]
public theorem alphaTwoMinorMinusThree_det : alphaTwoMinorMinusThree.det = -3 := by
  rw [Matrix.det_fin_three]
  norm_num [alphaTwoMinorMinusThree]
  decide

/-- The primitive functional `Φ=(4,2,3,2)` annihilating the image of `α₂`. -/
public def alphaTwoFunctional (x : Fin 4 → ℤ) : ℤ :=
  4 * x 0 + 2 * x 1 + 3 * x 2 + 2 * x 3

public theorem alphaTwoFunctional_relation (y : Fin 6 → ℤ) :
    alphaTwoFunctional (alphaTwoMatrix.mulVec y) = 0 := by
  simp [alphaTwoFunctional, alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The image of `α₂` is exactly `ker Φ`; equivalently its cokernel is classified by `Φ`. -/
public theorem alphaTwo_image_iff (x : Fin 4 → ℤ) :
    (∃ y : Fin 6 → ℤ, alphaTwoMatrix.mulVec y = x) ↔ alphaTwoFunctional x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact alphaTwoFunctional_relation y
  · intro h
    unfold alphaTwoFunctional at h
    have hcmod : x 2 % 2 = 0 := by
      omega
    obtain ⟨s, hs⟩ : ∃ s : ℤ, x 2 = 2 * s := ⟨x 2 / 2, by omega⟩
    refine ⟨![x 0, -x 0 - 3 * s, s, -9 * s - x 3, 0, 0], ?_⟩
    funext i
    fin_cases i <;>
      simp [alphaTwoMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h hs ⊢ <;>
      ring_nf at h hs ⊢ <;>
      omega

public theorem alphaTwoPresentation_exact :
    Function.Exact alphaTwoMatrix.mulVec alphaTwoFunctional := by
  intro x
  simpa only [Set.mem_range] using (alphaTwo_image_iff x).symm

/-- `Φ` is onto, so the cokernel of `α₂` is infinite cyclic. -/
public theorem alphaTwoFunctional_surjective : Function.Surjective alphaTwoFunctional := by
  intro z
  refine ⟨![0, -z, z, 0], ?_⟩
  simp [alphaTwoFunctional]
  ring

/-- The degree-one specialization lattice at the order-three elliptic point. -/
public def specializationOneOrderThree : Matrix (Fin 2) (Fin 2) ℤ :=
  !![3, 0;
     0, 1]

/-- The degree-one specialization lattice at the order-four elliptic point. -/
public def specializationOneOrderFour : Matrix (Fin 2) (Fin 2) ℤ :=
  !![4, 0;
     0, 1]

/-- The degree-two order-four specialization lattice, with congruence `a ≡ b (mod 2)`. -/
public def specializationTwoOrderFour : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2, 1;
     0, 1]

@[simp]
public theorem specializationOneOrderThree_det : specializationOneOrderThree.det = 3 := by
  norm_num [specializationOneOrderThree, Matrix.det_fin_two]

@[simp]
public theorem specializationOneOrderFour_det : specializationOneOrderFour.det = 4 := by
  norm_num [specializationOneOrderFour, Matrix.det_fin_two]

@[simp]
public theorem specializationTwoOrderFour_det : specializationTwoOrderFour.det = 2 := by
  norm_num [specializationTwoOrderFour, Matrix.det_fin_two]

/-- The order-three specialization image is classified by divisibility of its first coordinate. -/
public theorem specializationOneOrderThree_image_iff (x : Fin 2 → ℤ) :
    (∃ y : Fin 2 → ℤ, specializationOneOrderThree.mulVec y = x) ↔ 3 ∣ x 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y 0, ?_⟩
    simp [specializationOneOrderThree, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rintro ⟨a, ha⟩
    refine ⟨![a, x 1], ?_⟩
    funext i
    fin_cases i <;>
      simp [specializationOneOrderThree, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at ha ⊢
    all_goals omega

/-- The order-four specialization image is classified by divisibility of its first coordinate. -/
public theorem specializationOneOrderFour_image_iff (x : Fin 2 → ℤ) :
    (∃ y : Fin 2 → ℤ, specializationOneOrderFour.mulVec y = x) ↔ 4 ∣ x 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y 0, ?_⟩
    simp [specializationOneOrderFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rintro ⟨a, ha⟩
    refine ⟨![a, x 1], ?_⟩
    funext i
    fin_cases i <;>
      simp [specializationOneOrderFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at ha ⊢
    all_goals omega

/-- The degree-two specialization image is the parity-congruence sublattice. -/
public theorem specializationTwoOrderFour_image_iff (x : Fin 2 → ℤ) :
    (∃ y : Fin 2 → ℤ, specializationTwoOrderFour.mulVec y = x) ↔ 2 ∣ x 0 - x 1 := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y 0, ?_⟩
    simp [specializationTwoOrderFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · rintro ⟨a, ha⟩
    refine ⟨![a, x 1], ?_⟩
    funext i
    fin_cases i <;>
      simp [specializationTwoOrderFour, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at ha ⊢
    all_goals omega

/-- The three normalized Leray differentials have coefficient `±p`. -/
public def chosenLerayDifferential (sign : ℤ) (x : ℤ) : ℤ :=
  sign * twistObstruction 0 1 (-1) * x

/-- Either possible common sign makes every chosen Leray differential an isomorphism. -/
public theorem chosenLerayDifferential_bijective (sign : ℤ)
    (hsign : sign = 1 ∨ sign = -1) : Function.Bijective (chosenLerayDifferential sign) := by
  rcases hsign with rfl | rfl <;> constructor
  · intro x y h
    simp [chosenLerayDifferential] at h
    exact h
  · intro y
    exact ⟨-y, by simp [chosenLerayDifferential]⟩
  · intro x y h
    simp [chosenLerayDifferential] at h
    exact h
  · intro y
    exact ⟨y, by simp [chosenLerayDifferential]⟩

/-- The graded abelian groups computed in Theorem 7.22 after substituting `p=-1`. -/
public def SectionSevenComputedHomology (k : ℕ) : Type :=
  if k = 0 ∨ k = 6 then ℤ else ZMod 1

public instance (k : ℕ) : AddCommGroup (SectionSevenComputedHomology k) := by
  unfold SectionSevenComputedHomology
  split <;> infer_instance

public theorem sectionSevenComputedHomology_middle_subsingleton (k : ℕ)
    (h0 : k ≠ 0) (h6 : k ≠ 6) : Subsingleton (SectionSevenComputedHomology k) := by
  simp only [SectionSevenComputedHomology, h0, h6, false_or, ↓reduceIte]
  infer_instance

/-- The missing bridge: identify actual singular homology with the finite Section 7 output. -/
public def SectionSevenHomologyRealization (X : Type) [TopologicalSpace X] : Prop :=
  ∀ k : ℕ, Nonempty (IntegralSingularHomology k X ≃+ SectionSevenComputedHomology k)

/-- Two realizations of the verified graded calculation give the required homology-sphere result. -/
public theorem hasIntegralHomologyOfSixSphere_of_sectionSevenRealizations
    {X : Type} [TopologicalSpace X]
    (hX : SectionSevenHomologyRealization X)
    (hSphere : SectionSevenHomologyRealization SixSphere) :
    HasIntegralHomologyOfSixSphere X := by
  intro k
  obtain ⟨eX⟩ := hX k
  obtain ⟨eSphere⟩ := hSphere k
  exact ⟨eX.trans eSphere.symm⟩

end SphereSixComplex
