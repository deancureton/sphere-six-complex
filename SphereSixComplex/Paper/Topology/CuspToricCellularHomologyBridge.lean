module

public import SphereSixComplex.Paper.Topology.CuspToricCellularAlgebra
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Cellular-to-singular bridge for the standard `A₂` cusp fibre

This file keeps the geometric input at the incidence level.  A general cellular-homology
comparison supplies the integral cellular complex of a CW complex and a quasi-isomorphism to
singular chains.  For the standard periodic `A₂` decomposition, the boundary equation below says
exactly that the cellular boundary, in the labelled cell bases, is the explicit incidence map from
`CuspToricCellularAlgebra` in degree one and is zero in every higher degree.  It contains no
homology ranks or homology equivalences.

Existence of that incidence equation for the toric decomposition is deliberately not asserted here.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set

namespace SphereSixComplex

/-- The complete cellular differential determined by the cusp incidence calculation. -/
public def cuspToricCellularBoundary :
    (n : ℕ) → (CuspWCellIndex n.succ → ℤ) →+ (CuspWCellIndex n → ℤ)
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
    (fun n ↦ AddCommGrpCat.of (CuspWCellIndex n → ℤ))
    (fun n ↦ AddCommGrpCat.ofHom (cuspToricCellularBoundary n))
    (by
      intro n
      apply AddCommGrpCat.hom_ext
      exact cuspToricCellularBoundary_comp n)


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



public theorem cuspWCellIndexFinite (n : ℕ) : Finite (CuspWCellIndex n) := by
  rcases n with (_ | _ | _ | _ | _ | n)
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 3))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 4))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 2))
  · simpa [CuspWCellIndex] using (inferInstance : Finite (Fin 1))
  · simpa [CuspWCellIndex] using (inferInstance : Finite Empty)

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
    (e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ CuspWCellIndex n)
    (M : IntegralCWCellularHomologyModel Y) (n : ℕ) :
    (CuspWCellIndex n → ℤ) ≃+ M.chainComplex.X n := by
  letI : Finite (CuspWCellIndex n) := cuspWCellIndexFinite n
  letI : Finite (Topology.CWComplex.cell (Set.univ : Set Y) n) :=
    Finite.of_equiv _ (e n).symm
  exact
    (integerFunctionReindexAddEquiv (e n)).trans
      Finsupp.addEquivFunOnFinite.symm |>.trans (M.cellBasis n)

namespace CuspToricCellular

variable {Y : Type} [TopologicalSpace Y] [Topology.CWComplex (Set.univ : Set Y)]
variable {e : ∀ n, Topology.CWComplex.cell (Set.univ : Set Y) n ≃ CuspWCellIndex n}
variable {M : IntegralCWCellularHomologyModel Y}

/-- Exact incidence formulas identify the explicit cusp complex with the genuine cellular
complex. -/
public noncomputable def chainIso (I : ∀ (n : ℕ) (x : CuspWCellIndex n.succ → ℤ),
      M.chainComplex.d n.succ n (labelledA2CellBasis e M n.succ x) =
        labelledA2CellBasis e M n (cuspToricCellularBoundary n x)) :
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
      exact I j x)

/-- The incidence isomorphism and classical cellular homology identify singular homology with the
homology of the explicit incidence complex. -/
public noncomputable def integralSingularHomologyEquiv
    (I : ∀ (n : ℕ) (x : CuspWCellIndex n.succ → ℤ),
      M.chainComplex.d n.succ n (labelledA2CellBasis e M n.succ x) =
        labelledA2CellBasis e M n (cuspToricCellularBoundary n x)) (n : ℕ) :
    IntegralSingularHomology n Y ≃+ cuspToricCellularChainComplex.homology n := by
  let _ : IsIso (cuspToricCellularChainComplex.homologyMap (chainIso I).hom n) := by
    infer_instance
  exact (M.homologyEquiv n).symm.trans
    ((asIso (cuspToricCellularChainComplex.homologyMap (chainIso I).hom n)).symm
      |>.addCommGroupIsoToAddEquiv)


/-- The labelled incidence formulas compute the carrier's second singular homology as `ℤ⁴`. -/
public noncomputable def integralSingularHomologyTwoEquiv
    (I : ∀ (n : ℕ) (x : CuspWCellIndex n.succ → ℤ),
      M.chainComplex.d n.succ n (labelledA2CellBasis e M n.succ x) =
        labelledA2CellBasis e M n (cuspToricCellularBoundary n x)) :
    IntegralSingularHomology 2 Y ≃+ (Fin 4 → ℤ) :=
  (integralSingularHomologyEquiv I 2).trans
    cuspToricCellularChainComplex_homologyTwoEquiv



end CuspToricCellular

namespace StandardA2ToricCentralFiberCWDecomposition

variable {X : Type} [TopologicalSpace X]

/-- The standard cellular chain model selected for the carrier of a geometric toric CW
decomposition. -/
public noncomputable def establishedIntegralCellularChainModel
    (D : StandardA2ToricCentralFiberCWDecomposition X) :
    let _ := D.topology
    let _ := D.cwComplex
    IntegralCWCellularHomologyModel D.Carrier := by
  letI := D.topology
  letI := D.t2
  letI := D.cwComplex
  exact CellularHomology.normalizedModel D.Carrier

/-- Conditional on the exact attaching incidences, the CW carrier has second homology `ℤ⁴`. -/
public noncomputable def carrierIntegralSingularHomologyTwoEquiv
    (D : StandardA2ToricCentralFiberCWDecomposition X) (I : let _ := D.topology
      let _ := D.cwComplex
      ∀ (n : ℕ) (x : CuspWCellIndex n.succ → ℤ),
        D.establishedIntegralCellularChainModel.chainComplex.d n.succ n
            (labelledA2CellBasis D.cellEquiv D.establishedIntegralCellularChainModel n.succ x) =
          labelledA2CellBasis D.cellEquiv D.establishedIntegralCellularChainModel n
            (cuspToricCellularBoundary n x)) :
    let _ := D.topology
    IntegralSingularHomology 2 D.Carrier ≃+ (Fin 4 → ℤ) := by
  letI := D.topology
  letI := D.cwComplex
  exact CuspToricCellular.integralSingularHomologyTwoEquiv I



end StandardA2ToricCentralFiberCWDecomposition

end SphereSixComplex
