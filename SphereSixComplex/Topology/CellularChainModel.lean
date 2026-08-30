module

public import SphereSixComplex.Topology.CellularHomologyClassicalBoundary
public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Cellular chains of a CW complex

The cellular chain complex, its basis of cells, and its comparison with singular chains.  This is
general CW topology with no dependence on the paper's construction, so it sits upstream of both the
`A₂` cellular bridge and the Section 7 finite-CW models.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- The standard integral cellular chain complex of a CW complex, with one free generator for
each open cell and a comparison map to singular chains. -/
public structure IntegralCWCellularChainModel
    (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)] where
  chainComplex : ChainComplex AddCommGrpCat ℕ
  cellBasis : ∀ n,
    (Topology.CWComplex.cell (Set.univ : Set Y) n →₀ ℤ) ≃+ chainComplex.X n
  comparison : chainComplex ⟶ IntegralSingularChainComplex Y
  comparison_homology_isIso : ∀ n, IsIso (chainComplex.homologyMap comparison n)

variable (Y : Type) [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]

/-- The cellular chain group of a degree carrying no cells is a zero object. -/
public theorem isZero_cellularChain_of_isEmpty_cell
    (M : IntegralCWCellularHomologyModel Y) (n : ℕ)
    [IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n)] :
    IsZero (M.chainComplex.X n) := by
  have : Subsingleton (M.chainComplex.X n) := (M.cellBasis n).symm.injective.subsingleton
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- A Hausdorff CW complex has no `n`-th integral singular homology once it has no `n`-cells. -/
public theorem subsingleton_integralSingularHomology_of_isEmpty_cell (n : ℕ) [T2Space Y]
    [IsEmpty (Topology.CWComplex.cell (Set.univ : Set Y) n)] :
    Subsingleton (IntegralSingularHomology n Y) := by
  obtain M := EstablishedCellularHomology.integralCWCellularHomologyModel Y
  have hcell : IsZero (M.chainComplex.homology n) :=
    (HomologicalComplex.ExactAt.of_isZero
      (isZero_cellularChain_of_isEmpty_cell Y M n)).isZero_homology
  have : IsZero (AddCommGrpCat.of (IntegralSingularHomology n Y)) :=
    hcell.of_iso (M.homologyEquiv n).toAddCommGrpIso.symm
  exact AddCommGrpCat.subsingleton_of_isZero this

/-- Homology of a chain complex of finitely generated abelian groups is finitely generated: the
cycles are a subgroup of a finitely generated group, and the homology is a quotient of the
cycles. -/
public theorem module_finite_homology (C : ChainComplex AddCommGrpCat ℕ) (n : ℕ)
    (h : Module.Finite ℤ (C.X n)) : Module.Finite ℤ (C.homology n) := by
  have _inst := h
  let i : (C.cycles n : AddCommGrpCat) →+ (C.X n : AddCommGrpCat) :=
    ConcreteCategory.hom (HomologicalComplex.iCycles C n)
  have hinj : Function.Injective i := by
    rw [← AddCommGrpCat.mono_iff_injective]; infer_instance
  have hcyc : Module.Finite ℤ (C.cycles n) :=
    Module.Finite.of_injective i.toIntLinearMap hinj
  let q : (C.cycles n : AddCommGrpCat) →+ (C.homology n : AddCommGrpCat) :=
    ConcreteCategory.hom (HomologicalComplex.homologyπ C n)
  have hsurj : Function.Surjective q := by
    rw [← AddCommGrpCat.epi_iff_surjective]; infer_instance
  exact Module.Finite.of_surjective q.toIntLinearMap hsurj

end SphereSixComplex

end

end
