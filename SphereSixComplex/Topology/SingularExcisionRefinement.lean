module

public import SphereSixComplex.Topology.SingularExcisionOpenCover

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicTopology Set
namespace SphereSixComplex

public theorem coverSmallSingularSubcomplex_mono {ι κ : Type} (X : TopCat)
    (U : ι → Set X) (V : κ → Set X) (r : ι → κ) (h : ∀ i, U i ⊆ V (r i)) :
    coverSmallSingularSubcomplex X U ≤ coverSmallSingularSubcomplex X V := by
  intro n x hx
  obtain ⟨i, a, ha⟩ := (mem_coverSmallSingularSubcomplex_iff_exists_preimage X U x).mp hx
  apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage X V x).mpr
  let f : TopCat.of (U i) ⟶ TopCat.of (V (r i)) :=
    TopCat.ofHom ⟨Set.inclusion (h i), continuous_inclusion _⟩
  refine ⟨r i, (TopCat.toSSet.map f).app n a, ?_⟩
  have hf : f ≫ topologicalSubsetInclusion X (V (r i)) = topologicalSubsetInclusion X (U i) := rfl
  have he := congrArg (fun g ↦ g.app n a) (congrArg TopCat.toSSet.map hf)
  simpa only [Functor.map_comp, NatTrans.comp_app, types_comp_apply] using he.trans ha

public def coverSmallRefinementChains {ι κ : Type} (X : TopCat)
    (U : ι → Set X) (V : κ → Set X) (r : ι → κ) (h : ∀ i, U i ⊆ V (r i)) :=
  SSet.chainComplexMap (SSet.Subcomplex.homOfLE (coverSmallSingularSubcomplex_mono X U V r h))
    (AddCommGrpCat.of ℤ)

public theorem coverSmallRefinementChains_comp_inclusion {ι κ : Type} (X : TopCat)
    (U : ι → Set X) (V : κ → Set X) (r : ι → κ) (h : ∀ i, U i ⊆ V (r i)) :
    coverSmallRefinementChains X U V r h ≫ coverSmallIntegralSingularChainInclusion X V =
      coverSmallIntegralSingularChainInclusion X U := by
  unfold coverSmallRefinementChains coverSmallIntegralSingularChainInclusion
  let F := (SSet.chainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)
  have hi : SSet.Subcomplex.homOfLE (coverSmallSingularSubcomplex_mono X U V r h) ≫
      (coverSmallSingularSubcomplex X V).ι = (coverSmallSingularSubcomplex X U).ι := rfl
  exact (F.map_comp _ _).symm.trans (congrArg F.map hi)

public theorem coverSmallEventuallySmall_of_refinement {ι κ : Type} (X : TopCat)
    (U : ι → Set X) (V : κ → Set X) (r : ι → κ) (h : ∀ i, U i ⊆ V (r i))
    (hU : CoverSmallAffineSubdivisionEventuallySmall X U) :
    CoverSmallAffineSubdivisionEventuallySmall X V := by
  intro n x
  obtain ⟨m, y, hy⟩ := hU n x
  refine ⟨m, (coverSmallRefinementChains X U V r h).f n y, ?_⟩
  have he := congrArg (fun f ↦ f.f n) (coverSmallRefinementChains_comp_inclusion X U V r h)
  exact (ConcreteCategory.congr_hom he y).trans hy

public theorem coverSmallChainApproximation_of_open_refinement {ι κ : Type} (X : TopCat)
    (U : ι → Set X) (V : κ → Set X) (r : ι → κ) (h : ∀ i, U i ⊆ V (r i))
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    CoverSmallChainApproximation X V :=
  coverSmallChainApproximation_of_eventuallySmall X V
    (coverSmallEventuallySmall_of_refinement X U V r h
      (coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover))

end SphereSixComplex
