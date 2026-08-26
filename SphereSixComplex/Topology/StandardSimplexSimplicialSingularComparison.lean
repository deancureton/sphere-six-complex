module

public import SphereSixComplex.Topology.SimplicialSingularComparison
public import SphereSixComplex.Topology.HomotopySphereHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Algebra.Homology.SingleHomology

/-!
# Simplicial--singular comparison for a standard simplex

The realization of a standard simplex is contractible.  Both its simplicial chains and its
singular chains therefore have zero positive-degree homology, while degree-zero homology is the
coefficient group.  The canonical adjunction unit respects the degree-zero augmentations, so its
chain map is a quasi-isomorphism in every degree.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- In a nonnegatively graded chain complex, degree-zero chains are canonically the degree-zero
cycles, since the outgoing differential vanishes. -/
public noncomputable def chainComplexXZeroIsoCyclesZero
    (K : ChainComplex AddCommGrpCat ℕ) : K.X 0 ≅ K.cycles 0 where
  hom := K.liftCycles (𝟙 _) 0 (by simp) (by simp)
  inv := K.iCycles 0
  hom_inv_id := by simp
  inv_hom_id := by
    rw [← cancel_mono (K.iCycles 0)]
    simp

/-- The canonical augmentation on degree-zero simplicial homology is natural in the simplicial
set.  This is the residual naturality calculation needed in the standard-simplex comparison. -/
public theorem simplicialHomologyZeroAugmentation_naturality
    {X Y : SSet.{0}} (f : X ⟶ Y) (R : AddCommGrpCat) :
    SSet.homologyMap f R 0 ≫ Y.homology₀ε R = X.homology₀ε R := by
  let K := X.chainComplex R
  let L := Y.chainComplex R
  let φ := SSet.chainComplexMap f R
  let e₀ := chainComplexXZeroIsoCyclesZero K
  apply (cancel_epi (K.homologyπ 0)).1
  apply (cancel_epi e₀.hom).1
  apply X.chainComplex_hom_ext
  intro x
  change X.ιChainComplex x ≫ e₀.hom ≫ K.homologyπ 0 ≫
      HomologicalComplex.homologyMap φ 0 ≫ Y.homology₀ε R =
    X.ιChainComplex x ≫ e₀.hom ≫ K.homologyπ 0 ≫ X.homology₀ε R
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  change X.ιChainComplex x ≫
      K.liftCycles (𝟙 _) 0 (by simp) (by simp) ≫
        HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0 ≫
          Y.homology₀ε R =
    X.ιChainComplex x ≫ K.liftCycles (𝟙 _) 0 (by simp) (by simp) ≫
      K.homologyπ 0 ≫ X.homology₀ε R
  simp only [← Category.assoc, HomologicalComplex.comp_liftCycles,
    Category.comp_id]
  simp only [HomologicalComplex.liftCycles_comp_cyclesMap]
  change L.liftCycles
      (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) ≫
        L.homologyπ 0 ≫ Y.homology₀ε R =
    K.liftCycles (X.ιChainComplex x) 0 (by simp) (by simp) ≫
      K.homologyπ 0 ≫ X.homology₀ε R
  have hlift : L.liftCycles
      (X.ιChainComplex x ≫ (SSet.chainComplexMap f R).f 0) 0 (by simp) (by simp) =
      L.liftCycles (Y.ιChainComplex (f.app _ x)) 0 (by simp) (by simp) := by
    apply (cancel_mono (L.iCycles 0)).1
    simpa only [HomologicalComplex.liftCycles_i] using
      SSet.ι_chainComplexMap_f X Y f R x
  rw [hlift]
  calc
    _ = 𝟙 R := by
      simpa only [] using
        Y.liftCycles_ιChainComplex_homologyπ_homology₀ε R (f.app _ x)
    _ = _ := by
      symm
      simpa only [] using
        X.liftCycles_ιChainComplex_homologyπ_homology₀ε R x

/-- Every standard simplex is connected as a simplicial set. -/
public theorem standardSimplex_isConnected (n : ℕ) :
    (SSet.stdSimplex.obj (SimplexCategory.mk n)).IsConnected := by
  rw [SSet.isConnected_iff]
  constructor
  · constructor
    intro a b
    induction a using SSet.π₀.rec with
    | mk x =>
      induction b using SSet.π₀.rec with
      | mk y =>
        let i := SSet.stdSimplex.obj₀Equiv x
        let j := SSet.stdSimplex.obj₀Equiv y
        rcases le_total i j with hij | hji
        · let s := SSet.stdSimplex.edge n i j hij
          have hs : SSet.π₀.mk x = SSet.π₀.mk y := by
            have hsrc : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 1 s = x := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            have htgt : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 0 s = y := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            simpa only [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
          exact hs
        · let s := SSet.stdSimplex.edge n j i hji
          have hs : SSet.π₀.mk y = SSet.π₀.mk x := by
            have hsrc : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 1 s = y := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            have htgt : (SSet.stdSimplex.obj (SimplexCategory.mk n)).δ 0 s = x := by
              apply SSet.stdSimplex.obj₀Equiv.injective
              rfl
            simpa only [hsrc, htgt] using SSet.π₀.sound (SSet.Edge.mk' s)
          exact hs.symm
  · exact ⟨SSet.stdSimplex.const n 0 _⟩

/-- The geometric realization of every standard simplex is contractible. -/
public theorem standardSimplexRealization_contractibleSpace (n : ℕ) :
    ContractibleSpace
      (SSet.toTop.obj (SSet.stdSimplex.obj (SimplexCategory.mk n)) : Type) := by
  let : ContractibleSpace (stdSimplex ℝ (Fin (n + 1))) :=
    (convex_stdSimplex ℝ (Fin (n + 1))).contractibleSpace
      ⟨stdSimplex.vertex (0 : Fin (n + 1)),
        (stdSimplex.vertex (0 : Fin (n + 1))).2⟩
  exact (SimplexCategory.toTopHomeo (SimplexCategory.mk n)).contractibleSpace

/-- Simplicial chains of a standard simplex are exact in every positive degree, by the canonical
extra degeneracy. -/
public theorem standardSimplex_simplicialChains_exactAt
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((Δ[n] : SSet.{0}).chainComplex R).ExactAt k := by
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk n)).map (sigmaConst.obj R)
  let e := ed.homotopyEquiv
  exact (exactAt_iff_of_quasiIsoAt e.hom k).mpr
    (HomologicalComplex.exactAt_single_obj _ _ _ _ hk)

/-- Singular chains of the realization of a standard simplex are exact in every positive degree,
by contractibility and homotopy invariance. -/
public theorem standardSimplexRealization_singularChains_exactAt
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((TopCat.toSSet.obj (SSet.toTop.obj (Δ[n] : SSet.{0}))).chainComplex R).ExactAt k := by
  let : ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
    standardSimplexRealization_contractibleSpace n
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type)
  have hunit := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat k R (TopCat.of Unit) hk
  have hzero := hunit.of_iso (singularHomologyIsoOfHomotopyEquiv
    R k e)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hzero

/-- The canonical realization/singular adjunction-unit chain map is a quasi-isomorphism for every
standard simplex. -/
public theorem standardSimplex_simplicialToRealizationSingularChainMap_quasiIso
    (R : AddCommGrpCat) (n : ℕ) :
    QuasiIso (simplicialToRealizationSingularChainMap
      (Δ[n] : SSet.{0}) R) := by
  rw [quasiIso_iff]
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [quasiIsoAt_iff_isIso_homologyMap]
    let : (SSet.stdSimplex.obj (SimplexCategory.mk n)).IsConnected :=
      standardSimplex_isConnected n
    let : ContractibleSpace
        (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
      standardSimplexRealization_contractibleSpace n
    let : PathConnectedSpace
        (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) := inferInstance
    let : (TopCat.toSSet.obj (SSet.toTop.obj (Δ[n] : SSet.{0}))).IsConnected :=
      inferInstance
    let φ := simplicialToRealizationSingularChainMap
      (Δ[n] : SSet.{0}) R
    have hε : HomologicalComplex.homologyMap φ 0 ≫
        (SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε
          R = (Δ[n] : SSet.{0}).homology₀ε R := by
      exact simplicialHomologyZeroAugmentation_naturality
        (sSetTopAdj.unit.app (Δ[n] : SSet.{0})) R
    let hsource : IsIso ((Δ[n] : SSet.{0}).homology₀ε R) := inferInstance
    let htarget : IsIso
        ((SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε
          R) :=
      inferInstanceAs (IsIso ((TopCat.toSSet.obj
        (SSet.toTop.obj (Δ[n] : SSet.{0}))).homology₀ε R))
    have hcomp : IsIso (HomologicalComplex.homologyMap φ 0 ≫
        (SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε
          R) := by
      rw [hε]
      exact hsource
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      (HomologicalComplex.homologyMap φ 0)
      ((SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε
        R) htarget hcomp
  · exact (quasiIsoAt_iff_exactAt _ k
      (standardSimplex_simplicialChains_exactAt R n k hk)).mpr
        (standardSimplexRealization_singularChains_exactAt R n k hk)

/-- In the terminology used by the project, every standard simplex satisfies the canonical
integral simplicial--singular comparison. -/
public theorem standardSimplex_integralComparison (n : ℕ) :
    SimplicialToSingularComparisonQuasiIsomorphism
      (Δ[n] : SSet.{0}) (AddCommGrpCat.of ℤ) :=
  standardSimplex_simplicialToRealizationSingularChainMap_quasiIso
    (AddCommGrpCat.of ℤ) n

end SphereSixComplex
