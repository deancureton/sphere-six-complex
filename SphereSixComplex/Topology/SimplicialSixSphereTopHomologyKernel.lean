module

public import SphereSixComplex.Topology.SimplicialSixSphereTopHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# The top normalized cycles of the boundary of the seven-simplex

This file compares the normalized chains of the boundary with those of the full standard
seven-simplex.  The latter is acyclic in positive degrees by its extra degeneracy, while its
unique nondegenerate seven-simplex supplies the orientation cycle.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Simplicial
  AlgebraicTopology HomologicalComplex

namespace SphereSixComplex

public noncomputable abbrev StandardSevenNormalizedIntegralChains :
    ChainComplex AddCommGrpCat ℕ :=
  (Δ[7] : SSet.{0}).normalizedChainComplex (AddCommGrpCat.of ℤ)

/-- The normalized chains of the full standard seven-simplex are exact in every positive
degree. -/
public theorem standardSeven_normalizedChains_exactAt (n : ℕ) (hn : n ≠ 0) :
    StandardSevenNormalizedIntegralChains.ExactAt n := by
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk 7)).map ((sigmaConst.obj (AddCommGrpCat.of ℤ)))
  let e := ed.homotopyEquiv
  have hchains : ((Δ[7] : SSet.{0}).chainComplex
      (AddCommGrpCat.of ℤ)).ExactAt n := by
    exact (exactAt_iff_of_quasiIsoAt e.hom n).mpr
      (exactAt_single_obj _ _ _ _ hn)
  exact (exactAt_iff_of_quasiIsoAt
    ((Δ[7] : SSet.{0}).toNormalizedChainComplex (AddCommGrpCat.of ℤ)) n).mp hchains

/-- In degrees below seven, send each nondegenerate simplex of the full simplex to the same
simplex, regarded as a simplex of the boundary. -/
public noncomputable def standardSevenNormalizedChainsToBoundary
    (n : ℕ) (hn : n < 7) :
    StandardSevenNormalizedIntegralChains.X n ⟶
      BoundarySevenNormalizedIntegralChains.X n :=
  ((Δ[7] : SSet.{0}).isColimitCofanNormalizedChainComplex
    (AddCommGrpCat.of ℤ) n).desc
      (Cofan.mk _ (fun x ↦
        (∂Δ[7] : SSet.{0}).ιNormalizedChainComplex
            ⟨x.1, by rw [SSet.boundary_obj_eq_univ n 7 hn]; trivial⟩))

public theorem ιNormalizedChainComplex_standardSevenNormalizedChainsToBoundary
    (n : ℕ) (hn : n < 7)
    (x : (Δ[7] : SSet.{0}).obj (Opposite.op (SimplexCategory.mk n)))
    (hx : x ∈ (Δ[7] : SSet.{0}).nonDegenerate n) :
    (Δ[7] : SSet.{0}).ιNormalizedChainComplex x ≫
        standardSevenNormalizedChainsToBoundary n hn =
      (∂Δ[7] : SSet.{0}).ιNormalizedChainComplex
        ⟨x, by rw [SSet.boundary_obj_eq_univ n 7 hn]; trivial⟩ := by
  exact ((Δ[7] : SSet.{0}).isColimitCofanNormalizedChainComplex
    (AddCommGrpCat.of ℤ) n).fac
      (Cofan.mk _ (fun x ↦
        (∂Δ[7] : SSet.{0}).ιNormalizedChainComplex
          ⟨x.1, by rw [SSet.boundary_obj_eq_univ n 7 hn]; trivial⟩)) ⟨x, hx⟩

/-- Below the top dimension, normalized chains of the boundary and of the full simplex agree. -/
public noncomputable def boundarySevenNormalizedChainsXIsoStandard
    (n : ℕ) (hn : n < 7) :
    BoundarySevenNormalizedIntegralChains.X n ≅
      StandardSevenNormalizedIntegralChains.X n where
  hom := (SSet.normalizedChainComplexMap
    (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
      (AddCommGrpCat.of ℤ)).f n
  inv := standardSevenNormalizedChainsToBoundary n hn
  hom_inv_id := by
    apply (∂Δ[7] : SSet.{0}).normalizedChainComplex_hom_ext
    intro x hx
    rw [← Category.assoc, SSet.ι_normalizedChainComplexMap_f, Category.comp_id]
    have hx' : x.1 ∈ (Δ[7] : SSet.{0}).nonDegenerate n := by
      rwa [← (SSet.boundary 7).mem_nonDegenerate_iff x]
    convert ιNormalizedChainComplex_standardSevenNormalizedChainsToBoundary
      n hn x.1 hx' using 1 <;> try rfl
  inv_hom_id := by
    apply (Δ[7] : SSet.{0}).normalizedChainComplex_hom_ext
    intro x hx
    rw [← Category.assoc, Category.comp_id]
    rw [ιNormalizedChainComplex_standardSevenNormalizedChainsToBoundary n hn x hx]
    calc
      _ = (Δ[7] : SSet.{0}).ιNormalizedChainComplex
          (((SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι).app _
            ⟨x, by rw [SSet.boundary_obj_eq_univ n 7 hn]; trivial⟩) :=
        SSet.ι_normalizedChainComplexMap_f
          (f := (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι)
          (R := AddCommGrpCat.of ℤ) _
      _ = _ := by congr

/-- The degree-six cycle kernels of the boundary and the full simplex agree, because their
normalized groups and differential agree in degrees six and five. -/
public noncomputable def boundarySevenTopCyclesIsoStandardSevenTopCycles :
    kernel (BoundarySevenNormalizedIntegralChains.d 6 5) ≅
      kernel (StandardSevenNormalizedIntegralChains.d 6 5) := by
  let f := SSet.normalizedChainComplexMap
    (SSet.boundary 7 : SSet.Subcomplex (Δ[7] : SSet.{0})).ι
      (AddCommGrpCat.of ℤ)
  let e₆ := boundarySevenNormalizedChainsXIsoStandard 6 (by omega)
  let e₅ := boundarySevenNormalizedChainsXIsoStandard 5 (by omega)
  letI : IsIso (f.f 6) := by
    change IsIso e₆.hom
    infer_instance
  letI : IsIso (f.f 5) := by
    change IsIso e₅.hom
    infer_instance
  let φ := (shortComplexFunctor' AddCommGrpCat (ComplexShape.down ℕ) 7 6 5).map f
  letI : IsIso φ.τ₂ := by
    dsimp [φ, shortComplexFunctor']
    infer_instance
  letI : IsIso φ.τ₃ := by
    dsimp [φ, shortComplexFunctor']
    infer_instance
  exact ((BoundarySevenNormalizedIntegralChains.sc' 7 6 5).cyclesIsoKernel).symm ≪≫
    asIso (ShortComplex.cyclesMap φ) ≪≫
      (StandardSevenNormalizedIntegralChains.sc' 7 6 5).cyclesIsoKernel

/-- The top normalized group of the full seven-simplex is one copy of `ℤ`, indexed by its
unique nondegenerate top simplex. -/
public noncomputable def standardSevenNormalizedChainsXSevenIsoInt :
    StandardSevenNormalizedIntegralChains.X 7 ≅ AddCommGrpCat.of ℤ := by
  let top : (Δ[7] : SSet.{0}).nonDegenerate 7 :=
    ⟨SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 7)),
      SSet.stdSimplex.objEquiv_symm_id_mem_nonDegenerate 7⟩
  letI : Unique ((Δ[7] : SSet.{0}).nonDegenerate 7) :=
    { default := top
      uniq := fun x ↦ by
        apply Subtype.ext
        have hx := x.2
        have hx' : x.1 ∈
            ({SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 7))} :
              Set ((Δ[7] : SSet.{0}).obj
                (Opposite.op (SimplexCategory.mk 7)))) := by
          rw [← SSet.stdSimplex.nonDegenerate_top_dim]
          exact hx
        simpa [top] using hx' }
  exact IsColimit.coconePointUniqueUpToIso
    ((Δ[7] : SSet.{0}).isColimitCofanNormalizedChainComplex
      (AddCommGrpCat.of ℤ) 7)
    (Cofan.isColimitMkOfUnique (Iso.refl (AddCommGrpCat.of ℤ))
      ((Δ[7] : SSet.{0}).nonDegenerate 7))

/-- Exactness in degree seven and vanishing in degree eight make the top differential of the
full simplex a monomorphism. -/
public theorem standardSeven_normalized_d_seven_six_mono :
    Mono (StandardSevenNormalizedIntegralChains.d 7 6) := by
  have h₇ := standardSeven_normalizedChains_exactAt 7 (by omega)
  have h₇' : (StandardSevenNormalizedIntegralChains.sc' 8 7 6).Exact :=
    ShortComplex.exact_of_iso
      (StandardSevenNormalizedIntegralChains.isoSc' 8 7 6 (by simp) (by simp)) h₇
  have h₈ : IsZero (StandardSevenNormalizedIntegralChains.X 8) :=
    (Δ[7] : SSet.{0}).isZero_normalizedChainComplex_X_of_hasDimensionLT
      (AddCommGrpCat.of ℤ) 8 8
  apply h₇'.mono_g
  exact h₈.eq_of_src _ _

/-- Exactness in degree six identifies the top differential with the kernel of the next
differential. -/
public noncomputable def standardSevenNormalizedChainsXSevenIsoTopCycles :
    StandardSevenNormalizedIntegralChains.X 7 ≅
      kernel (StandardSevenNormalizedIntegralChains.d 6 5) := by
  letI : Mono (StandardSevenNormalizedIntegralChains.d 7 6) :=
    standardSeven_normalized_d_seven_six_mono
  have h₆ := standardSeven_normalizedChains_exactAt 6 (by omega)
  have h₆' : (StandardSevenNormalizedIntegralChains.sc' 7 6 5).Exact :=
    ShortComplex.exact_of_iso
      (StandardSevenNormalizedIntegralChains.isoSc' 7 6 5 (by simp) (by simp)) h₆
  letI : Mono (StandardSevenNormalizedIntegralChains.sc' 7 6 5).f := by
    change Mono (StandardSevenNormalizedIntegralChains.d 7 6)
    exact standardSeven_normalized_d_seven_six_mono
  exact IsLimit.conePointUniqueUpToIso h₆'.fIsKernel
    (limit.isLimit (parallelPair (StandardSevenNormalizedIntegralChains.d 6 5) 0))

/-- The degree-six cycle kernel of the full seven-simplex is infinite cyclic, generated by the
boundary of its unique nondegenerate top simplex. -/
public noncomputable def standardSevenTopCyclesIsoInt :
    kernel (StandardSevenNormalizedIntegralChains.d 6 5) ≅ AddCommGrpCat.of ℤ :=
  standardSevenNormalizedChainsXSevenIsoTopCycles.symm ≪≫
    standardSevenNormalizedChainsXSevenIsoInt

/-- The normalized top cycles of the boundary of the seven-simplex form one infinite cyclic
group. -/
public theorem boundarySevenNormalizedTopCyclesOrientation :
    BoundarySevenNormalizedTopCyclesOrientation :=
  ⟨(boundarySevenTopCyclesIsoStandardSevenTopCycles ≪≫
    standardSevenTopCyclesIsoInt).addCommGroupIsoToAddEquiv⟩

/-- Therefore degree-six simplicial homology of the boundary of the seven-simplex is
unconditionally infinite cyclic. -/
public theorem boundarySevenSimplicialTopHomologyOrientation :
    BoundarySevenSimplicialTopHomologyOrientation :=
  boundarySevenSimplicialTopHomologyOrientation_of_normalizedCycles
    boundarySevenNormalizedTopCyclesOrientation

end SphereSixComplex
