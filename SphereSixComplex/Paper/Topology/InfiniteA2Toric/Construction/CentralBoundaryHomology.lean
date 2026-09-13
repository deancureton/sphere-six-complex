module

public import SphereSixComplex.Paper.Topology.InfiniteA2Toric.Construction.CentralBoundaryCover
public import SphereSixComplex.Prerequisites.Topology.BinaryOpenCoverLegacyMayerVietoris
public import SphereSixComplex.Prerequisites.Topology.StandardSpherePositiveHomology
public import SphereSixComplex.Prerequisites.Topology.ComplexUnitsHomology
public import SphereSixComplex.Prerequisites.Topology.FiniteDiscreteProductHomology

@[expose] public section
noncomputable section
open Set Topology TopologicalSpace
open SphereSixComplex.Periods
open SphereSixComplex.BinaryOpenCover
namespace SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
open CuspCollar CuspFilling CuspLocalPhaseAction CuspPeriodExpansion CuspPhaseEstimates
variable {E : FuchsianModularLift} {D : FuchsianPeriodData E}
  {N : NormalizedFuchsianCuspCoordinate E D}

def finiteOpen : Opens (TopCat.of Spheres) := ⟨finitePart, isOpen_finitePart⟩
def reciprocalOpen : Opens (TopCat.of Spheres) := ⟨reciprocalPart, isOpen_reciprocalPart⟩

theorem finiteOpen_sup_reciprocalOpen : finiteOpen ⊔ reciprocalOpen = ⊤ :=
  SetLike.coe_injective finitePart_union_reciprocalPart

/-- The connecting map of the canonical ordered pole-complement cover. -/
def boundary (n : ℕ) :
    IntegralSingularHomology (n + 1) (finitePart ∪ reciprocalPart : Set Spheres) →+
      IntegralSingularHomology n (finitePart ∩ reciprocalPart : Set Spheres) :=
  ((openCoverHomologyComparisonOfCover finiteOpen_sup_reciprocalOpen).toIntegralMayerVietorisData
     finiteOpen_sup_reciprocalOpen).legacyBoundary n

theorem boundary_bijective (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (hn : n ≠ 0) : Function.Bijective (boundary n) := by
  let _ := contractibleSpace_reciprocalPart W
  let _ := subsingleton_integralSingularHomology_of_contractible (X := finitePart) n hn
  let _ := subsingleton_integralSingularHomology_of_contractible (X := reciprocalPart) n hn
  let _ := subsingleton_integralSingularHomology_of_contractible
    (X := finitePart) (n + 1) (Nat.succ_ne_zero n)
  let _ := subsingleton_integralSingularHomology_of_contractible
    (X := reciprocalPart) (n + 1) (Nat.succ_ne_zero n)
  have hex := ((openCoverHomologyComparisonOfCover finiteOpen_sup_reciprocalOpen).toIntegralMayerVietorisData
     finiteOpen_sup_reciprocalOpen).legacyBoundary_exact n
  change Function.Exact (IntegralMayerVietoris.sumMap finitePart reciprocalPart (n + 1))
    (boundary n) ∧ Function.Exact (boundary n)
      (IntegralMayerVietoris.differenceMap finitePart reciprocalPart n) ∧ _ at hex
  constructor
  · apply (injective_iff_map_eq_zero (boundary n)).mpr
    intro x hx
    obtain ⟨y, hy⟩ := (hex.1 x).mp hx
    have hy0 : y = 0 := Subsingleton.elim _ _
    simpa [hy0] using hy.symm
  · intro x
    apply (hex.2.1 x).mp
    exact Subsingleton.elim _ _

/-- Positive-degree boundary homology, with coordinates given by the three punctured charts. -/
def homologyEquiv (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (hn : n ≠ 0) :
    IntegralSingularHomology (n + 1) Spheres ≃+
      IntegralSingularHomology n (Fin 3 × ℂˣ) :=
  (integralSingularHomologyEquiv (n + 1)
    ((Homeomorph.setCongr finitePart_union_reciprocalPart).trans (Homeomorph.Set.univ _)).symm).trans
    ((AddEquiv.ofBijective (boundary n) (boundary_bijective W n hn)).trans
      (integralSingularHomologyEquiv n overlapHomeomorph).symm)

@[simp] theorem homologyEquiv_apply
    (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (hn : n ≠ 0) (x : IntegralSingularHomology (n + 1) Spheres) :
    integralSingularHomologyEquiv n overlapHomeomorph (homologyEquiv W n hn x) =
      boundary n (integralSingularHomologyEquiv (n + 1)
        ((Homeomorph.setCongr finitePart_union_reciprocalPart).trans
          (Homeomorph.Set.univ _)).symm x) := by
  exact (integralSingularHomologyEquiv n overlapHomeomorph).apply_symm_apply _

/-- Degree-two coordinates are winding numbers in the three punctured axis charts. -/
def homologyTwoEquiv (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IntegralSingularHomology 2 Spheres ≃+ (Fin 3 → ℤ) :=
  (homologyEquiv W 1 one_ne_zero).trans
    ((IntegralSingularHomology.discreteProductEquiv (Fin 3) ℂˣ 1).trans
      (AddEquiv.piCongrRight (fun _ => Complex.unitsHomologyOneEquiv)))

def actualHomologyTwoEquiv (W : ActualPuncturedCuspCollarWitness N constructedModel) :
    IntegralSingularHomology 2 ↥((singletonPhaseImage W)ᶜ) ≃+ (Fin 3 → ℤ) :=
  (integralSingularHomologyEquiv 2 (homeomorph W)).symm.trans (homologyTwoEquiv W)

theorem subsingleton_homology (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (hn : 2 < n) : Subsingleton (IntegralSingularHomology n Spheres) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let _ := Circle.subsingleton_homology k (by omega)
  let _ : Subsingleton (IntegralSingularHomology k ℂˣ) :=
    ⟨fun x y => (integralSingularHomologyEquivOfHomotopyEquiv k
      Complex.unitsHomotopyEquivCircle).injective (Subsingleton.elim _ _)⟩
  let e := (homologyEquiv W k (by omega)).trans
    (IntegralSingularHomology.discreteProductEquiv (Fin 3) ℂˣ k)
  exact ⟨fun x y => e.injective (Subsingleton.elim _ _)⟩

theorem subsingleton_actualHomology (W : ActualPuncturedCuspCollarWitness N constructedModel)
    (n : ℕ) (hn : 2 < n) :
    Subsingleton (IntegralSingularHomology n ↥((singletonPhaseImage W)ᶜ)) := by
  let _ := subsingleton_homology W n hn
  exact ⟨fun x y => (integralSingularHomologyEquiv n (homeomorph W)).symm.injective
    (Subsingleton.elim _ _)⟩

end SphereSixComplex.Geometry.InfiniteA2Toric.Construction.CentralBoundary
