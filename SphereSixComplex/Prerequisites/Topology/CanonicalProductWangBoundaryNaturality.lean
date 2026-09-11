module

public import SphereSixComplex.Prerequisites.Topology.FiniteCyclicMappingTorusWangNaturality

/-!
# Canonical mapping-torus boundary naturality

This module realizes the vertex/edge Mayer--Vietoris boundary through the canonical binary
open-cover comparison. Pulling the cover back along the normalized affine cyclic map then gives
the boundary naturality square directly, without choosing a witness of exactness.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory TopologicalSpace

namespace SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

open NormalizedAffineMappingTorusCover
open CircleProductIdentityMappingTorus
open CyclicMappingTorus

variable {m : ℕ} [NeZero m] {F : Type} [TopologicalSpace F]


/-- The normalized affine cover preserves the marked fibre over the circle origin. -/
public theorem normalizedAffineCover_fiber
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (x : F) :
    normalizedAffineCoverToCircleMappingTorus phi hpow (0, x) =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) x := by
  change CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi
      (CyclicMappingTorus.normalizedAffineCyclicQuotientRealMappingTorusHomeomorph phi hpow
        (Quotient.mk (CyclicMappingTorus.normalizedAffineCyclicSetoid (m := m) phi) (0, x))) = _
  have hreal :
      CyclicMappingTorus.normalizedAffineCyclicQuotientRealMappingTorusHomeomorph phi hpow
          (Quotient.mk (CyclicMappingTorus.normalizedAffineCyclicSetoid (m := m) phi) (0, x)) =
        Quotient.mk (CyclicAngularFundamentalDomain.realMappingTorusSetoid phi)
          ((0 : ℝ), x) := by
    unfold CyclicMappingTorus.normalizedAffineCyclicQuotientRealMappingTorusHomeomorph
    unfold CyclicAngularFundamentalDomain.homeomorphOfQuotientMaps
    dsimp only
    apply (CyclicMappingTorus.normalizedAffineQuotientMap_eq_iff phi hpow _ _).mp
    calc
      CyclicMappingTorus.normalizedAffineQuotientMap (m := m) phi
          (Function.surjInv (CyclicMappingTorus.normalizedAffineQuotientMap_surjective (m := m) phi)
            (Quotient.mk (CyclicMappingTorus.normalizedAffineCyclicSetoid (m := m) phi) (0, x))) =
        Quotient.mk (CyclicMappingTorus.normalizedAffineCyclicSetoid (m := m) phi) (0, x) :=
          Function.surjInv_eq (CyclicMappingTorus.normalizedAffineQuotientMap_surjective (m := m) phi) _
      _ = CyclicMappingTorus.normalizedAffineQuotientMap (m := m) phi ((0 : ℝ), x) := by
        simp [CyclicMappingTorus.normalizedAffineQuotientMap, CyclicMappingTorus.normalizedAffineBaseCover]
  rw [hreal]
  rw [← show
    (CyclicAngularFundamentalDomain.realMappingTorusHomeomorph phi).symm
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) x) =
      Quotient.mk (CyclicAngularFundamentalDomain.realMappingTorusSetoid phi)
        ((0 : ℝ), x) by rfl]
  exact Homeomorph.apply_symm_apply _ _

/-- The normalized affine cover composed with the product fibre inclusion is the mapping-torus
fibre inclusion. -/
public theorem normalizedAffineCover_comp_productFiberInclusion
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) :
    (normalizedAffineCoverToCircleMappingTorus phi hpow).comp
        (productFiberInclusion (X := F)) =
      finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi) := by
  ext x
  exact normalizedAffineCover_fiber phi hpow x

/-- The fibre square in finite cyclic Wang naturality follows by functoriality. -/
public theorem normalizedAffineCover_fiber_homology
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (n : ℕ)
    (x : IntegralSingularHomology n F) :
    integralSingularHomologyMap n
        (normalizedAffineCoverToCircleMappingTorus phi hpow)
        (integralSingularHomologyMap n (productFiberInclusion (X := F)) x) =
      integralSingularHomologyMap n
        (finiteBouquetMappingTorusFiberInclusion (fun _ : Unit ↦ phi)) x := by
  rw [integralSingularHomologyMap_comp_wang,
    normalizedAffineCover_comp_productFiberInclusion phi hpow]

/-- The fibre square in the exact form used by a finite cyclic Wang presentation. -/
public theorem normalizedAffineCover_fiber_square
    (phi : F ≃ₜ F) (hpow : phi ^ m = 1) (k : ℕ)
    (x : IntegralSingularHomology (k + 1) F) :
    integralSingularHomologyMap (k + 1)
        (normalizedAffineCoverToCircleMappingTorus phi hpow)
        (integralSingularHomologyMap (k + 1) (productFiberInclusion (X := F)) x) =
      (circleMappingTorusWangPresentationOfCover phi k).inclusion x :=
  normalizedAffineCover_fiber_homology phi hpow (k + 1) x

/-- The vertex member of the standard mapping-torus cover as an open subset. -/
public abbrev mappingTorusVertexOpen (phi : F ≃ₜ F) :
    Opens (TopCat.of (CircleMappingTorus phi)) :=
  coverVertexOpen (fun _ : Unit ↦ phi)

/-- The edge member of the standard mapping-torus cover as an open subset. -/
public abbrev mappingTorusEdgeOpen (phi : F ≃ₜ F) :
    Opens (TopCat.of (CircleMappingTorus phi)) :=
  coverEdgeOpen (fun _ : Unit ↦ phi)

/-- The vertex and edge opens cover the mapping torus. -/
public theorem mappingTorusOpenCover (phi : F ≃ₜ F) :
    mappingTorusVertexOpen phi ⊔ mappingTorusEdgeOpen phi = ⊤ :=
  coverOpen (fun _ : Unit ↦ phi)





/-- The canonical comparison for the mapping-torus vertex/edge cover. -/
public noncomputable def mappingTorusOpenCoverHomologyComparison (phi : F ≃ₜ F) :
    BinaryOpenCover.OpenCoverHomologyComparison
      (mappingTorusVertexOpen phi) (mappingTorusEdgeOpen phi) :=
  coverHomologyComparison (fun _ : Unit ↦ phi)








end SphereSixComplex.Topology.CanonicalProductWangBoundaryNaturality

end

end
