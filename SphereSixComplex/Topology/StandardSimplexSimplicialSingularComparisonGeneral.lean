module

public import SphereSixComplex.Topology.StandardSimplexSimplicialSingularComparison

/-!
# Simplicial--singular comparison for a standard simplex with arbitrary coefficients

The integral proof does not use a special property of `ℤ`.  This file records the coefficient-
general statement, including the degree-zero augmentation calculation.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- The degree-zero simplicial augmentation is natural for an arbitrary coefficient object. -/
public theorem simplicialHomologyZeroAugmentation_naturality_general
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

/-- Simplicial chains of a standard simplex are exact in positive degrees for arbitrary
coefficients. -/
public theorem standardSimplex_simplicialChains_exactAt_general
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((Δ[n] : SSet.{0}).chainComplex R).ExactAt k := by
  let ed := (SSet.Augmented.StandardSimplex.extraDegeneracy
    (SimplexCategory.mk n)).map (sigmaConst.obj R)
  let e := ed.homotopyEquiv
  exact (exactAt_iff_of_quasiIsoAt e.hom k).mpr
    (HomologicalComplex.exactAt_single_obj _ _ _ _ hk)

/-- Singular chains of the realization of a standard simplex are exact in positive degrees for
arbitrary coefficients. -/
public theorem standardSimplexRealization_singularChains_exactAt_general
    (R : AddCommGrpCat) (n k : ℕ) (hk : k ≠ 0) :
    ((TopCat.toSSet.obj (SSet.toTop.obj (Δ[n] : SSet.{0}))).chainComplex R).ExactAt k := by
  letI : ContractibleSpace (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
    standardSimplexRealization_contractibleSpace n
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit
    (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type)
  have hunit := AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    AddCommGrpCat k R (TopCat.of Unit) hk
  have hzero := hunit.of_iso (singularHomologyIsoOfHomotopyEquiv R k e)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hzero

/-- The canonical comparison for a standard simplex is a quasi-isomorphism with every
coefficient object in `AddCommGrpCat`. -/
public theorem standardSimplex_simplicialToRealizationSingularChainMap_quasiIso_general
    (R : AddCommGrpCat) (n : ℕ) :
    QuasiIso (simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R) := by
  rw [quasiIso_iff]
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [quasiIsoAt_iff_isIso_homologyMap]
    letI : (SSet.stdSimplex.obj (SimplexCategory.mk n)).IsConnected :=
      standardSimplex_isConnected n
    letI : ContractibleSpace
        (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) :=
      standardSimplexRealization_contractibleSpace n
    letI : PathConnectedSpace
        (SSet.toTop.obj (Δ[n] : SSet.{0}) : Type) := inferInstance
    letI : (TopCat.toSSet.obj (SSet.toTop.obj (Δ[n] : SSet.{0}))).IsConnected :=
      inferInstance
    let φ := simplicialToRealizationSingularChainMap (Δ[n] : SSet.{0}) R
    have hε : HomologicalComplex.homologyMap φ 0 ≫
        (SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R =
      (Δ[n] : SSet.{0}).homology₀ε R :=
      simplicialHomologyZeroAugmentation_naturality_general
        (sSetTopAdj.unit.app (Δ[n] : SSet.{0})) R
    let hsource : IsIso ((Δ[n] : SSet.{0}).homology₀ε R) := inferInstance
    let htarget : IsIso
        ((SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R) :=
      inferInstanceAs (IsIso ((TopCat.toSSet.obj
        (SSet.toTop.obj (Δ[n] : SSet.{0}))).homology₀ε R))
    have hcomp : IsIso (HomologicalComplex.homologyMap φ 0 ≫
        (SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R) := by
      rw [hε]
      exact hsource
    exact @IsIso.of_isIso_comp_right _ _ _ _ _
      (HomologicalComplex.homologyMap φ 0)
      ((SSet.toTop.obj (Δ[n] : SSet.{0})).singularHomology₀ε R) htarget hcomp
  · exact (quasiIsoAt_iff_exactAt _ k
      (standardSimplex_simplicialChains_exactAt_general R n k hk)).mpr
        (standardSimplexRealization_singularChains_exactAt_general R n k hk)

end SphereSixComplex
