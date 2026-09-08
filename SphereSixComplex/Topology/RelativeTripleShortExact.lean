module

public import SphereSixComplex.Topology.ContractingPrismSuspension
public import SphereSixComplex.Topology.CellularHomologyClassicalBoundary
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace SphereSixComplex

section Abelian
variable {C : Type*} [Category* C] [Abelian C] {A B D : C} (f : A ⟶ B) (g : B ⟶ D)

public def cokernelTripleShortComplex : ShortComplex C :=
  ShortComplex.mk (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) (by
      apply (cancel_epi (cokernel.π f)).mp
      simp)

public theorem cokernelTripleShortComplex_shortExact [Mono g] :
    (cokernelTripleShortComplex f g).ShortExact := by
  have h := kernelCokernelCompSequence_exact f g
  refine { exact := h.exact 3, mono_f := ?_, epi_g := ?_ }
  · exact (h.exact 2).mono_g ((isZero_kernel_of_mono g).eq_of_src _ _)
  · change Epi ((kernelCokernelCompSequence f g).map' 4 5)
    infer_instance
end Abelian

public def cwRelativeTripleRawShortComplex {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) :=
  cokernelTripleShortComplex (cwIntegralSingularChainMapObj i) (cwIntegralSingularChainMapObj j)

public theorem cwRelativeTripleRawShortComplex_shortExact
    {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) [Mono j] :
    (cwRelativeTripleRawShortComplex i j).ShortExact := by
  let : Mono (cwIntegralSingularChainMapObj j) := by
    dsimp [cwIntegralSingularChainMapObj]
    infer_instance
  exact cokernelTripleShortComplex_shortExact _ _

public def cwRelativeTripleMiddleIso {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) :
    (cwRelativeTripleRawShortComplex i j).X₂ ≅ CWRelativeIntegralSingularChainComplex (i ≫ j) :=
  cokernelIsoOfEq (cwIntegralSingularChainMapObj_comp i j).symm

public def cwRelativeTripleShortComplex {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk
    ((cwRelativeTripleRawShortComplex i j).f ≫ (cwRelativeTripleMiddleIso i j).hom)
    ((cwRelativeTripleMiddleIso i j).inv ≫ (cwRelativeTripleRawShortComplex i j).g) (by
      simp only [Category.assoc, Iso.hom_inv_id_assoc, ShortComplex.zero])

public def cwRelativeTripleShortComplexIso {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) :
    cwRelativeTripleRawShortComplex i j ≅ cwRelativeTripleShortComplex i j :=
  ShortComplex.isoMk (Iso.refl _) (cwRelativeTripleMiddleIso i j) (Iso.refl _)
    (by simp [cwRelativeTripleShortComplex]) (by simp [cwRelativeTripleShortComplex])

public theorem cwRelativeTripleShortComplex_shortExact
    {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) [Mono j] :
    (cwRelativeTripleShortComplex i j).ShortExact :=
  ShortComplex.shortExact_of_iso (cwRelativeTripleShortComplexIso i j)
    (cwRelativeTripleRawShortComplex_shortExact i j)

public theorem cwRelativeTripleShortComplex_f
    {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) :
    (cwRelativeTripleShortComplex i j).f = cwRelativeIntegralSingularChainMapOfPair
      (show CWTopologicalPairMap i (i ≫ j) from ⟨𝟙 _, j, by simp⟩) := by
  dsimp only [cwRelativeTripleShortComplex, cwRelativeTripleRawShortComplex,
    cokernelTripleShortComplex, cwRelativeTripleMiddleIso, CWRelativeIntegralSingularChainComplex]
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (cwIntegralSingularChainMapObj i))
  erw [← Category.assoc, cokernel.π_desc, Category.assoc, π_comp_cokernelIsoOfEq_hom]
  exact (cwRelativeIntegralSingularChainProjection_natural
    (show CWTopologicalPairMap i (i ≫ j) from ⟨𝟙 _, j, by simp⟩)).symm

public theorem cwRelativeTripleShortComplex_g
    {A B Y : TopCat} (i : A ⟶ B) (j : B ⟶ Y) :
    (cwRelativeTripleShortComplex i j).g = cwRelativeIntegralSingularChainMapOfPair
      (show CWTopologicalPairMap (i ≫ j) j from ⟨i, 𝟙 _, by simp⟩) := by
  dsimp only [cwRelativeTripleShortComplex, cwRelativeTripleRawShortComplex,
    cokernelTripleShortComplex, cwRelativeTripleMiddleIso, CWRelativeIntegralSingularChainComplex]
  apply Cofork.IsColimit.hom_ext (cokernelIsCokernel (cwIntegralSingularChainMapObj (i ≫ j)))
  erw [← Category.assoc, π_comp_cokernelIsoOfEq_inv, cokernel.π_desc, Category.id_comp]
  have h := cwRelativeIntegralSingularChainProjection_natural
    (show CWTopologicalPairMap (i ≫ j) j from ⟨i, 𝟙 _, by simp⟩)
  change _ = cwIntegralSingularChainMapObj (𝟙 _) ≫ _ at h
  rw [cwIntegralSingularChainMapObj_id, Category.id_comp] at h
  exact h.symm

end SphereSixComplex
