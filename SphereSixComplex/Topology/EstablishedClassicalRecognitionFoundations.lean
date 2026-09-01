module

public import SphereSixComplex.Topology.HurewiczWhiteheadStages
public import SphereSixComplex.Topology.HigherHurewiczClassicalBoundary
public import SphereSixComplex.Topology.SmoothSixSphereClassification
public import SphereSixComplex.Topology.EstablishedSphereHomology
public import SphereSixComplex.Topology.FiniteDimensionalSmoothTriangulationBoundary

/-!
# Classical foundations for smooth six-sphere recognition

This module is the complete classical trust boundary for recognizing the standard smooth
six-sphere. The first two assumptions are source- and dimension-independent theorems of classical
topology. Smooth Poincare is necessarily dimension-specific. Their exact hypotheses are exposed
here so that none of the paper-specific geometry is hidden in the recognition step.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- The classical higher Hurewicz theorem, including its natural canonical transformation. This
is stated for arbitrary spaces and degrees; no application-specific sphere or homology class is
mentioned. -/
public axiom classicalHigherHurewiczTheory :
    ∃ H : HigherHurewiczMap, HigherHurewiczIsomorphismProperty H

/-- For a simply connected space whose positive integral homology vanishes below `n`, every
degree-`n` class is represented by a map from the standard `n`-sphere. This is the application
corollary of the general higher Hurewicz theorem. -/
public theorem generalHigherHurewiczClassSurjectivity
    (n : ℕ) (hn : 2 ≤ n)
    (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X]
    (hLower : ∀ k : ℕ, 0 < k → k < n →
      Subsingleton (IntegralSingularHomology k X)) :
    ∀ c : IntegralSingularHomology n X,
      ∃ f : C((TopCat.sphere n : Type), X),
        ∃ s : IntegralSingularHomology n (TopCat.sphere n : Type),
          integralSingularHomologyMap n f s = c := by
  obtain ⟨H, hH⟩ := classicalHigherHurewiczTheory
  exact generalHigherHurewiczClassSurjectivity_of_map H hH n hn X hLower

/-- The homological Whitehead theorem for simply connected spaces of classical CW type. The
simple-connectivity hypotheses are essential: the corresponding unrestricted integral-homology
statement is false. -/
public axiom simplyConnectedHomologicalWhitehead
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y]
    (hX : HasClassicalCWType X) (hY : HasClassicalCWType Y)
    (f : C(X, Y)) (hf : IsIntegralHomologyEquivalence f) :
    ∃ e : X ≃ₕ Y, e.toFun = f

/-- Smooth Poincare in dimension six for the specified smooth atlas. Equivalently, this is the
dimension-six generalized Poincare and h-cobordism argument together with the Kervaire--Milnor
calculation that the group of smooth homotopy six-spheres is trivial. -/
public axiom establishedSmoothPoincareSixStandardModel :
    SmoothPoincareSixStandardModel

private theorem intAddMonoidHom_bijective_of_one_mem_range
    (g : ℤ →+ ℤ) (h : ∃ z, g z = 1) :
    Function.Bijective g := by
  obtain ⟨z, hz⟩ := h
  have hmul : z * g 1 = 1 := by
    rw [AddMonoidHom.apply_int, zsmul_eq_mul] at hz
    exact hz
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul with hpos | hneg
  · have hg : ∀ x : ℤ, g x = x := by
      intro x
      rw [AddMonoidHom.apply_int, hpos.2]
      norm_num
    exact ⟨fun _ _ hxy ↦ by simpa only [hg] using hxy,
      fun y ↦ ⟨y, hg y⟩⟩
  · have hg : ∀ x : ℤ, g x = -x := by
      intro x
      rw [AddMonoidHom.apply_int, hneg.2]
      norm_num
    constructor
    · intro x y hxy
      have : -x = -y := by simpa only [hg] using hxy
      exact neg_injective this
    · intro y
      exact ⟨-y, by rw [hg]; simp⟩

private theorem addMonoidHom_bijective_of_infiniteCyclic_generator_mem_range
    {H K : Type*} [AddCommGroup H] [AddCommGroup K]
    (eH : H ≃+ ℤ) (eK : K ≃+ ℤ) (φ : H →+ K)
    (h : ∃ x : H, φ x = eK.symm 1) :
    Function.Bijective φ := by
  let g : ℤ →+ ℤ :=
    eK.toAddMonoidHom.comp (φ.comp eH.symm.toAddMonoidHom)
  have hgOne : ∃ z : ℤ, g z = 1 := by
    obtain ⟨x, hx⟩ := h
    refine ⟨eH x, ?_⟩
    change eK (φ (eH.symm (eH x))) = 1
    rw [eH.symm_apply_apply, hx, eK.apply_symm_apply]
  have hg := intAddMonoidHom_bijective_of_one_mem_range g hgOne
  constructor
  · intro x y hxy
    apply eH.injective
    apply hg.1
    change eK (φ (eH.symm (eH x))) = eK (φ (eH.symm (eH y)))
    simpa using congrArg eK hxy
  · intro y
    obtain ⟨z, hz⟩ := hg.2 (eK y)
    refine ⟨eH.symm z, ?_⟩
    apply eK.injective
    exact hz

/-- The general higher-Hurewicz theorem gives the degree-six interface used by recognition. -/
public theorem establishedHigherHurewiczSixGenerator
    (X : Type) [TopologicalSpace X] [SimplyConnectedSpace X]
    (hLower : ∀ n : ℕ, 0 < n → n < 6 → Subsingleton (IntegralSingularHomology n X))
    (hTop : Nonempty (IntegralSingularHomology 6 X ≃+ ℤ)) :
    HasTopDimensionalSphericalGenerator X := by
  let sourceOrientation :
      IntegralSingularHomology 6 (TopCat.sphere 6 : Type) ≃+ ℤ :=
    (integralSingularHomologyEquiv 6
      sixSphereHomeomorphTopCatSphereSix).symm.trans
        (Classical.choice establishedSixSpherePositiveHomologyInputs.degreeSix)
  let targetOrientation : IntegralSingularHomology 6 X ≃+ ℤ :=
    Classical.choice hTop
  obtain ⟨f, s, hs⟩ :=
    generalHigherHurewiczClassSurjectivity 6 (by norm_num) X hLower
      (targetOrientation.symm 1)
  have hfBijective :
      Function.Bijective (integralSingularHomologyMap 6 f) :=
    addMonoidHom_bijective_of_infiniteCyclic_generator_mem_range
      sourceOrientation targetOrientation
      (integralSingularHomologyMap 6 f) ⟨s, hs⟩
  have hf : IsIso (((singularHomologyFunctor AddCommGrpCat 6).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact hfBijective
  let h : C(SixSphere, (TopCat.sphere 6 : Type)) :=
    ⟨sixSphereHomeomorphTopCatSphereSix,
      sixSphereHomeomorphTopCatSphereSix.continuous⟩
  refine ⟨f.comp h, ?_⟩
  let _ := hf
  have hh : IsIso (((singularHomologyFunctor AddCommGrpCat 6).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom h)) := by
    exact (homotopyEquiv_isIntegralHomologyEquivalence
      sixSphereHomeomorphTopCatSphereSix.toHomotopyEquiv) 6
  change IsIso (((singularHomologyFunctor AddCommGrpCat 6).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom h ≫ TopCat.ofHom f))
  rw [Functor.map_comp]
  infer_instance

/-- The general smooth-manifold CW theorem gives the fixed six-dimensional interface. -/
public theorem establishedCompactSmoothSixManifoldClassicalCWType
    (X : Type) [TopologicalSpace X] [T2Space X] [SecondCountableTopology X]
    [ChartedSpace RealModel X]
    [IsManifold (modelWithCornersSelf ℝ RealModel) ∞ X] [CompactSpace X] :
    HasClassicalCWType X := by
  have hManifold : IsManifold (modelWithCornersSelf ℝ RealModel) 1 X :=
    inferInstance
  let M := compactCOneManifoldFiniteCWModelAtDimension RealModel X hManifold inferInstance
  let _ := M.topology
  let _ := M.cwComplex
  exact hasClassicalCWType_precomp_homotopyEquiv M.homotopyEquiv
    (hasClassicalCWType_of_cwComplex M.Carrier)

/-- The general homological Whitehead theorem gives the property-valued interface used here. -/
public theorem establishedSimplyConnectedClassicalCWIntegralHomologyWhitehead
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [SimplyConnectedSpace Y] :
    ClassicalCWIntegralHomologyWhiteheadProperty X Y := by
  intro hX hY f hf
  exact simplyConnectedHomologicalWhitehead X Y hX hY f hf

end SphereSixComplex
