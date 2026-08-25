module

public import SphereSixComplex.Topology.RelativeSingularHomology
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.ZMod.QuotientGroup

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- Multiplication by two on the integral coefficient object. -/
public def integralCoefficientTimesTwo :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ :=
  AddCommGrpCat.ofHom
    { toFun := fun z ↦ 2 * z
      map_zero' := by simp
      map_add' := by simp [mul_add] }

/-- Reduction of integral coefficients modulo two. -/
public def integralCoefficientReductionModTwo :
    AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of (ZMod 2) :=
  AddCommGrpCat.ofHom (Int.castAddHom (ZMod 2))

/-- The coefficient short complex `ℤ --2→ ℤ → ZMod 2`. -/
public noncomputable def integralModTwoCoefficientShortComplex :
    ShortComplex AddCommGrpCat :=
  ShortComplex.mk integralCoefficientTimesTwo
    integralCoefficientReductionModTwo (by
      ext
      simp [integralCoefficientTimesTwo,
        integralCoefficientReductionModTwo]
      decide)

/-- The standard integral-to-mod-two coefficient sequence is short exact. -/
public theorem integralModTwoCoefficientShortComplex_shortExact :
    integralModTwoCoefficientShortComplex.ShortExact := by
  refine
    { exact := ?_
      mono_f := ?_
      epi_g := ?_ }
  · rw [ShortComplex.ab_exact_iff]
    change ∀ z : ℤ, (z : ZMod 2) = 0 → ∃ y : ℤ, 2 * y = z
    intro z hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
    obtain ⟨y, rfl⟩ := hz
    exact ⟨y, by simp⟩
  · rw [AddCommGrpCat.mono_iff_injective]
    change Function.Injective (fun z : ℤ ↦ 2 * z)
    intro a b h
    nlinarith
  · rw [AddCommGrpCat.epi_iff_surjective]
    change Function.Surjective (fun z : ℤ ↦ (z : ZMod 2))
    exact ZMod.intCast_surjective

/-- The functor taking an abelian group to a coproduct of copies indexed by `I`. -/
public noncomputable def coefficientCoproductFunctor (I : Type) :
    CategoryTheory.Functor AddCommGrpCat AddCommGrpCat :=
  sigmaConst ⋙ (evaluation (Type) AddCommGrpCat).obj I

public instance (I : Type) : (coefficientCoproductFunctor I).Additive := by
  dsimp [coefficientCoproductFunctor]
  infer_instance

private noncomputable def coefficientCoproductFunctorExactModel (I : Type) :
    CategoryTheory.Functor AddCommGrpCat AddCommGrpCat :=
  (Functor.const (Discrete I) : CategoryTheory.Functor AddCommGrpCat
      (CategoryTheory.Functor (Discrete I) AddCommGrpCat)) ⋙ colim

private instance (I : Type) : PreservesFiniteLimits
    (coefficientCoproductFunctorExactModel I) := by
  dsimp [coefficientCoproductFunctorExactModel]
  infer_instance

private instance (I : Type) : PreservesFiniteColimits
    (coefficientCoproductFunctorExactModel I) := by
  dsimp [coefficientCoproductFunctorExactModel]
  infer_instance

private noncomputable def coefficientCoproductFunctorIso (I : Type) :
    coefficientCoproductFunctor I ≅ coefficientCoproductFunctorExactModel I :=
  NatIso.ofComponents
    (fun A ↦ Limits.Sigma.isoColimit ((Functor.const (Discrete I)).obj A)) (by
      intro A B f
      apply Limits.Sigma.hom_ext
      intro i
      simp only [coefficientCoproductFunctor, coefficientCoproductFunctorExactModel,
        Functor.comp_map, evaluation_obj_map, sigmaConst]
      rw [Limits.Sigma.ι_map_assoc]
      have hB :
          Limits.Sigma.ι (fun _ : I ↦ B) i ≫
            (Limits.Sigma.isoColimit ((Functor.const (Discrete I)).obj B)).hom =
          colimit.ι ((Functor.const (Discrete I)).obj B) ⟨i⟩ := by
        simpa only [Functor.const_obj_obj] using
          Limits.Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj B) i
      have hA :
          Limits.Sigma.ι (fun _ : I ↦ A) i ≫
            (Limits.Sigma.isoColimit ((Functor.const (Discrete I)).obj A)).hom =
          colimit.ι ((Functor.const (Discrete I)).obj A) ⟨i⟩ := by
        simpa only [Functor.const_obj_obj] using
          Limits.Sigma.ι_isoColimit_hom ((Functor.const (Discrete I)).obj A) i
      rw [hB, ← Category.assoc, hA]
      change f ≫ colimit.ι ((Functor.const (Discrete I)).obj B) ⟨i⟩ =
        colimit.ι ((Functor.const (Discrete I)).obj A) ⟨i⟩ ≫
          colimMap ((Functor.const (Discrete I)).map f)
      rw [ι_colimMap, Functor.const_map_app])

/-- A coproduct of copies preserves the integral-to-mod-two coefficient short exact sequence. -/
public theorem integralModTwoCoefficientShortComplex_map_coproduct_shortExact (I : Type) :
    (integralModTwoCoefficientShortComplex.map
      (coefficientCoproductFunctor I)).ShortExact := by
  have hG := integralModTwoCoefficientShortComplex_shortExact.map_of_exact
    (coefficientCoproductFunctorExactModel I)
  exact ShortComplex.shortExact_of_iso
    (integralModTwoCoefficientShortComplex.mapNatIso
      (coefficientCoproductFunctorIso I).symm) hG

/-- Singular chains of `X`, regarded as a functor of the coefficient object. -/
public noncomputable def singularChainComplexCoefficientFunctor (X : TopCat) :
    CategoryTheory.Functor AddCommGrpCat (ChainComplex AddCommGrpCat ℕ) :=
  singularChainComplexFunctor AddCommGrpCat ⋙
    (evaluation TopCat (ChainComplex AddCommGrpCat ℕ)).obj X

public instance (X : TopCat) :
    (singularChainComplexCoefficientFunctor X).Additive := by
  dsimp [singularChainComplexCoefficientFunctor]
  infer_instance

/-- Singular chains with mod-two coefficients. -/
public noncomputable abbrev ModTwoSingularChainComplexObj (X : TopCat) :
    ChainComplex AddCommGrpCat ℕ :=
  (singularChainComplexCoefficientFunctor X).obj (AddCommGrpCat.of (ZMod 2))

/-- The coefficient short complex after applying singular chains of `X`. -/
public noncomputable def integralModTwoSingularChainShortComplex (X : TopCat) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  integralModTwoCoefficientShortComplex.map
    (singularChainComplexCoefficientFunctor X)

/-- Singular chains preserve the integral-to-mod-two coefficient short exact sequence. -/
public theorem integralModTwoSingularChainShortComplex_shortExact (X : TopCat) :
    (integralModTwoSingularChainShortComplex X).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  unfold integralModTwoSingularChainShortComplex
  rw [← ShortComplex.map_comp]
  dsimp [singularChainComplexCoefficientFunctor, singularChainComplexFunctor,
    SSet.chainComplexFunctor]
  change (integralModTwoCoefficientShortComplex.map
    (sigmaConst ⋙ (evaluation (Type) AddCommGrpCat).obj
      ((TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))))).ShortExact
  exact integralModTwoCoefficientShortComplex_map_coproduct_shortExact _

/-- The Bockstein reduction at degree three, assuming the coefficient short complex remains short
exact after applying singular chains.  Vanishing of integral homology in degrees three and two
then forces vanishing with mod-two coefficients in degree three. -/
public theorem modTwoSingularHomologyThree_isZero_of_chainShortExact
    (X : TopCat)
    (hS : (integralModTwoSingularChainShortComplex X).ShortExact)
    (h₃ : IsZero ((IntegralSingularChainComplexObj X).homology 3))
    (h₂ : IsZero ((IntegralSingularChainComplexObj X).homology 2)) :
    IsZero ((ModTwoSingularChainComplexObj X).homology 3) := by
  have hexact := hS.homology_exact₃ 3 2
    (ComplexShape.down_mk 3 2 (by omega))
  have h₃' : IsZero ((integralModTwoSingularChainShortComplex X).X₂.homology 3) := by
    simpa [integralModTwoSingularChainShortComplex,
      integralModTwoCoefficientShortComplex,
      singularChainComplexCoefficientFunctor] using h₃
  have h₂' : IsZero ((integralModTwoSingularChainShortComplex X).X₁.homology 2) := by
    simpa [integralModTwoSingularChainShortComplex,
      integralModTwoCoefficientShortComplex,
      singularChainComplexCoefficientFunctor] using h₂
  exact hexact.isZero_X₂ (h₃'.eq_of_src _ _) (h₂'.eq_of_tgt _ _)

/-- Integral homology vanishing in degrees three and two forces mod-two singular homology to
vanish in degree three. -/
public theorem modTwoSingularHomologyThree_isZero
    (X : TopCat)
    (h₃ : IsZero ((IntegralSingularChainComplexObj X).homology 3))
    (h₂ : IsZero ((IntegralSingularChainComplexObj X).homology 2)) :
    IsZero ((ModTwoSingularChainComplexObj X).homology 3) :=
  modTwoSingularHomologyThree_isZero_of_chainShortExact X
    (integralModTwoSingularChainShortComplex_shortExact X) h₃ h₂

end SphereSixComplex
