module

public import SphereSixComplex.Topology.CellularChainModel
public import SphereSixComplex.Topology.CuspToricCellularAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Cellular-to-singular bridge for the standard `A₂` cusp fibre

This file keeps the geometric input at the incidence level.  A general cellular-homology
comparison supplies the integral cellular complex of a CW complex and a quasi-isomorphism to
singular chains.  For the standard periodic `A₂` decomposition, the additional datum below says
exactly that the cellular boundary, in the labelled cell bases, is the explicit incidence map from
`CuspToricCellularAlgebra` in degree one and is zero in every higher degree.  It contains no
homology ranks or homology equivalences.

Existence of that incidence datum for the toric decomposition is deliberately not asserted here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace SphereSixComplex

/-- The complete cellular differential determined by the cusp incidence calculation. -/
public def cuspToricCellularBoundary :
    (n : ℕ) → (cuspWCellIndex n.succ → ℤ) →+ (cuspWCellIndex n → ℤ)
  | 0 => cuspToricCellularBoundaryOne
  | _ + 1 => 0

public theorem cuspToricCellularBoundary_comp (n : ℕ) :
    (cuspToricCellularBoundary n).comp (cuspToricCellularBoundary n.succ) = 0 := by
  rcases n with _ | n
  · apply AddMonoidHom.ext
    intro x
    exact (cuspToricCellularBoundaryOne.map_zero).trans rfl
  · rfl

/-- The explicit integral cellular chain complex predicted by the labelled toric incidence data. -/
public def cuspToricCellularChainComplex : ChainComplex AddCommGrpCat ℕ :=
  ChainComplex.of
    (fun n ↦ AddCommGrpCat.of (cuspWCellIndex n → ℤ))
    (fun n ↦ AddCommGrpCat.ofHom (cuspToricCellularBoundary n))
    (by
      intro n
      apply AddCommGrpCat.hom_ext
      exact cuspToricCellularBoundary_comp n)

/-- The explicit cusp cellular model has first homology `ℤ²`. -/
public noncomputable def cuspToricCellularChainComplex_homologyOneEquiv :
    cuspToricCellularChainComplex.homology 1 ≃+ (Fin 2 → ℤ) := by
  let S := cuspToricCellularChainComplex.sc' 2 1 0
  have hf : S.f = 0 := by rfl
  have hrange : AddMonoidHom.range S.abToCycles = ⊥ := by
    rw [AddMonoidHom.range_eq_bot_iff]
    apply AddMonoidHom.ext
    intro x
    apply Subtype.ext
    change S.f x = 0
    rw [hf]
    rfl
  exact
    ((ShortComplex.homologyMapIso
      (cuspToricCellularChainComplex.isoSc' 2 1 0
        ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 2 1 (by omega)))
        ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 1 0 (by omega))))).trans
      S.abHomologyIso).addCommGroupIsoToAddEquiv.trans
      (QuotientAddGroup.quotientAddEquivOfEq hrange) |>.trans
      QuotientAddGroup.quotientBot |>.trans
      cuspToricCellularDegreeOneEquiv

/-- The explicit cusp cellular model has second homology `ℤ⁴`. -/
public noncomputable def cuspToricCellularChainComplex_homologyTwoEquiv :
    cuspToricCellularChainComplex.homology 2 ≃+ (Fin 4 → ℤ) := by
  let S := cuspToricCellularChainComplex.sc' 3 2 1
  have hf : S.f = 0 := by rfl
  have hg : S.g = 0 := by rfl
  let h := ShortComplex.HomologyData.ofZeros S hf hg
  exact
    ((ShortComplex.homologyMapIso
      (cuspToricCellularChainComplex.isoSc' 3 2 1
        ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 3 2 (by omega)))
        ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 2 1 (by omega))))).trans
      h.left.homologyIso).addCommGroupIsoToAddEquiv.trans
      cuspToricCellularDegreeTwoEquiv

/-- The explicit cusp cellular model has third homology `ℤ²`. -/
public noncomputable def cuspToricCellularChainComplex_homologyThreeEquiv :
    cuspToricCellularChainComplex.homology 3 ≃+ (Fin 2 → ℤ) := by
  let S := cuspToricCellularChainComplex.sc' 4 3 2
  have hf : S.f = 0 := by rfl
  have hg : S.g = 0 := by rfl
  let h := ShortComplex.HomologyData.ofZeros S hf hg
  exact
    ((ShortComplex.homologyMapIso
      (cuspToricCellularChainComplex.isoSc' 4 3 2
        ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 4 3 (by omega)))
        ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 3 2 (by omega))))).trans
      h.left.homologyIso).addCommGroupIsoToAddEquiv.trans
      cuspToricCellularDegreeThreeEquiv

/-- The explicit cusp cellular model has fourth homology `ℤ`. -/
public noncomputable def cuspToricCellularChainComplex_homologyFourEquiv :
    cuspToricCellularChainComplex.homology 4 ≃+ ℤ := by
  let S := cuspToricCellularChainComplex.sc' 5 4 3
  have hf : S.f = 0 := by rfl
  have hg : S.g = 0 := by rfl
  let h := ShortComplex.HomologyData.ofZeros S hf hg
  exact
    ((ShortComplex.homologyMapIso
      (cuspToricCellularChainComplex.isoSc' 5 4 3
        ((ComplexShape.down ℕ).prev_eq' (ComplexShape.down_mk 5 4 (by omega)))
        ((ComplexShape.down ℕ).next_eq' (ComplexShape.down_mk 4 3 (by omega))))).trans
      h.left.homologyIso).addCommGroupIsoToAddEquiv.trans
      cuspToricCellularDegreeFourEquiv

public theorem cuspWCellIndexFinite (n : ℕ) : Finite (cuspWCellIndex n) := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 3))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 4))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [cuspWCellIndex] using (inferInstance : Finite (Fin 1))
  · simpa [cuspWCellIndex] using (inferInstance : Finite Empty)

/-- Reindex integer-valued coordinates along an equivalence. -/
public def integerFunctionReindexAddEquiv {I J : Type} (e : I ≃ J) :
    (J → ℤ) ≃+ (I → ℤ) where
  toFun x i := x (e i)
  invFun x j := x (e.symm j)
  left_inv x := by funext j; simp
  right_inv x := by funext i; simp
  map_add' _ _ := rfl

/-- The cellular basis written in the selected standard `A₂` cell coordinates. -/
public noncomputable def labelledA2CellBasis
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n)
    (M : IntegralCWCellularChainModel Y) (n : ℕ) :
    (cuspWCellIndex n → ℤ) ≃+ M.chainComplex.X n := by
  letI : Finite (cuspWCellIndex n) := cuspWCellIndexFinite n
  letI : Finite (Topology.CWComplex.cell (Set.univ : Set Y) n) :=
    Finite.of_equiv _ (e n).symm
  exact
    (integerFunctionReindexAddEquiv (e n)).trans
      Finsupp.addEquivFunOnFinite.symm |>.trans (M.cellBasis n)

/-- Exact attaching-incidence data for a labelled standard `A₂` toric CW decomposition.
The field identifies the genuine cellular boundary in every degree; it neither states nor assumes
any homology calculation. -/
public structure StandardA2ToricCellularIncidenceData
    {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n)
    (M : IntegralCWCellularChainModel Y) : Prop where
  boundary_eq : ∀ (n : ℕ) (x : cuspWCellIndex n.succ → ℤ),
    M.chainComplex.d n.succ n (labelledA2CellBasis e M n.succ x) =
      labelledA2CellBasis e M n (cuspToricCellularBoundary n x)

namespace StandardA2ToricCellularIncidenceData

variable {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
variable {e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ cuspWCellIndex n}
variable {M : IntegralCWCellularChainModel Y}

/-- Exact incidence formulas identify the explicit cusp complex with the genuine cellular
complex. -/
public noncomputable def chainIso (I : StandardA2ToricCellularIncidenceData e M) :
    cuspToricCellularChainComplex ≅ M.chainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (labelledA2CellBasis e M n).toAddCommGrpIso)
    (by
      intro i j hij
      simp only [ComplexShape.down_Rel] at hij
      rcases hij with rfl
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      simp only [AddEquiv.toAddCommGrpIso_hom, AddCommGrpCat.hom_comp,
        cuspToricCellularChainComplex, ChainComplex.of_d,
        AddCommGrpCat.hom_ofHom]
      exact I.boundary_eq j x)

/-- The cellular comparison, after replacing cellular chains by the explicit incidence model. -/
public noncomputable def singularComparison
    (I : StandardA2ToricCellularIncidenceData e M) :
    cuspToricCellularChainComplex ⟶ IntegralSingularChainComplex Y :=
  I.chainIso.hom ≫ M.comparison

public noncomputable instance singularComparison_homology_isIso
    (I : StandardA2ToricCellularIncidenceData e M) (n : ℕ) :
    IsIso (cuspToricCellularChainComplex.homologyMap I.singularComparison n) := by
  dsimp [singularComparison]
  rw [HomologicalComplex.homologyMap_comp]
  let _ := M.comparison_homology_isIso n
  infer_instance

/-- The labelled incidence formulas compute the carrier's first singular homology as `ℤ²`. -/
public noncomputable def integralSingularHomologyOneEquiv
    (I : StandardA2ToricCellularIncidenceData e M) :
    IntegralSingularHomology 1 Y ≃+ (Fin 2 → ℤ) :=
  (asIso (cuspToricCellularChainComplex.homologyMap I.singularComparison 1)).symm
    |>.addCommGroupIsoToAddEquiv.trans
      cuspToricCellularChainComplex_homologyOneEquiv

/-- The labelled incidence formulas compute the carrier's second singular homology as `ℤ⁴`. -/
public noncomputable def integralSingularHomologyTwoEquiv
    (I : StandardA2ToricCellularIncidenceData e M) :
    IntegralSingularHomology 2 Y ≃+ (Fin 4 → ℤ) :=
  (asIso (cuspToricCellularChainComplex.homologyMap I.singularComparison 2)).symm
    |>.addCommGroupIsoToAddEquiv.trans
      cuspToricCellularChainComplex_homologyTwoEquiv

/-- The labelled incidence formulas compute the carrier's third singular homology as `ℤ²`. -/
public noncomputable def integralSingularHomologyThreeEquiv
    (I : StandardA2ToricCellularIncidenceData e M) :
    IntegralSingularHomology 3 Y ≃+ (Fin 2 → ℤ) :=
  (asIso (cuspToricCellularChainComplex.homologyMap I.singularComparison 3)).symm
    |>.addCommGroupIsoToAddEquiv.trans
      cuspToricCellularChainComplex_homologyThreeEquiv

/-- The labelled incidence formulas compute the carrier's fourth singular homology as `ℤ`. -/
public noncomputable def integralSingularHomologyFourEquiv
    (I : StandardA2ToricCellularIncidenceData e M) :
    IntegralSingularHomology 4 Y ≃+ ℤ :=
  (asIso (cuspToricCellularChainComplex.homologyMap I.singularComparison 4)).symm
    |>.addCommGroupIsoToAddEquiv.trans
      cuspToricCellularChainComplex_homologyFourEquiv

end StandardA2ToricCellularIncidenceData

namespace StandardA2ToricCentralFiberCWDecomposition

variable {X : Type} [TopologicalSpace X]

/-- The standard cellular chain model selected for the carrier of a geometric toric CW
decomposition. -/
public noncomputable def establishedIntegralCellularChainModel
    (D : StandardA2ToricCentralFiberCWDecomposition X) :
    let _ := D.topology
    let _ := D.cwComplex
    IntegralCWCellularChainModel D.Carrier := by
  letI := D.topology
  letI := D.cwComplex
  exact EstablishedCellularHomology.integralCWCellularChainModel D.Carrier

/-- The exact boundary-formula input still required for the concrete standard toric CW
decomposition. -/
public abbrev CellularIncidenceData
    (D : StandardA2ToricCentralFiberCWDecomposition X) :=
  let _ := D.topology
  let _ := D.cwComplex
  StandardA2ToricCellularIncidenceData D.cellEquiv D.establishedIntegralCellularChainModel

/-- Conditional on the exact attaching incidences, the CW carrier has first homology `ℤ²`. -/
public noncomputable def carrierIntegralSingularHomologyOneEquiv
    (D : StandardA2ToricCentralFiberCWDecomposition X) (I : D.CellularIncidenceData) :
    let _ := D.topology
    IntegralSingularHomology 1 D.Carrier ≃+ (Fin 2 → ℤ) := by
  letI := D.topology
  letI := D.cwComplex
  exact I.integralSingularHomologyOneEquiv

/-- Conditional on the exact attaching incidences, the CW carrier has second homology `ℤ⁴`. -/
public noncomputable def carrierIntegralSingularHomologyTwoEquiv
    (D : StandardA2ToricCentralFiberCWDecomposition X) (I : D.CellularIncidenceData) :
    let _ := D.topology
    IntegralSingularHomology 2 D.Carrier ≃+ (Fin 4 → ℤ) := by
  letI := D.topology
  letI := D.cwComplex
  exact I.integralSingularHomologyTwoEquiv

/-- Conditional on the exact attaching incidences, the CW carrier has third homology `ℤ²`. -/
public noncomputable def carrierIntegralSingularHomologyThreeEquiv
    (D : StandardA2ToricCentralFiberCWDecomposition X) (I : D.CellularIncidenceData) :
    let _ := D.topology
    IntegralSingularHomology 3 D.Carrier ≃+ (Fin 2 → ℤ) := by
  letI := D.topology
  letI := D.cwComplex
  exact I.integralSingularHomologyThreeEquiv

/-- Conditional on the exact attaching incidences, the CW carrier has fourth homology `ℤ`. -/
public noncomputable def carrierIntegralSingularHomologyFourEquiv
    (D : StandardA2ToricCentralFiberCWDecomposition X) (I : D.CellularIncidenceData) :
    let _ := D.topology
    IntegralSingularHomology 4 D.Carrier ≃+ ℤ := by
  letI := D.topology
  letI := D.cwComplex
  exact I.integralSingularHomologyFourEquiv

end StandardA2ToricCentralFiberCWDecomposition

end SphereSixComplex
