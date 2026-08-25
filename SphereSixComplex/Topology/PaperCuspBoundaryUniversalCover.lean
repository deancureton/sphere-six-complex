module

public import SphereSixComplex.Topology.PaperCuspActualAffineFillingCoverSquare
public import SphereSixComplex.Topology.EstablishedUnwrappedAffineFillings

/-!
# The unwrapped boundary cover of the actual cusp filling

The angular logarithm coordinate has nontrivial monodromy on the rank-four period lattice.
Consequently, the boundary deck group is the semidirect product by `m₀`, rather than the direct
product of translations and the angular meridian.  This file defines that group and its explicit
translation and angular transformations on the normalized additive cusp cover.
-/

@[expose] public section

noncomputable section

open Matrix Set Topology

namespace SphereSixComplex

open Geometry Geometry.ComplexTorus Geometry.CuspPuncturedCollarBridge
open Geometry.StandardInfiniteA2ToricModel

namespace Topology

open LatticeData TriangleGroup

/-- The parabolic monodromy on the rank-four integral period lattice. -/
public noncomputable def paperCuspMonodromy : AddAut Lattice :=
  m₀.toAddEquiv

/-- The actual cusp boundary deck group: lattice translations semidirect the angular meridian. -/
public abbrev paperCuspBoundaryDeck :=
  CanonicalCyclicAffineBoundaryDeck paperCuspMonodromy

/-- The rank-four translation subgroup of the actual cusp boundary deck group. -/
public noncomputable def paperCuspBoundaryTranslation :
    Lattice →+ Additive paperCuspBoundaryDeck :=
  canonicalCyclicAffineTranslation paperCuspMonodromy

/-- The positive angular meridian of the actual cusp boundary deck group. -/
public noncomputable def paperCuspBoundaryMeridian : paperCuspBoundaryDeck :=
  canonicalCyclicAffineMeridian paperCuspMonodromy

/-- The algebraic deck data for the actual toric cusp boundary. -/
public noncomputable def paperCuspBoundaryDeckData :
    UnwrappedToricBoundaryDeckData Lattice paperToricSubgroup paperCuspBoundaryDeck where
  translation := paperCuspBoundaryTranslation
  translation_injective := canonicalCyclicAffineTranslation_injective paperCuspMonodromy
  meridian := paperCuspBoundaryMeridian
  vanishing := paperCuspVanishing
  generators_generate := canonicalCyclicAffine_generators_generate paperCuspMonodromy

@[simp]
public theorem paperCuspMonodromy_apply (v : Lattice) :
    paperCuspMonodromy v = M₀ *ᵥ v := by
  exact m₀_apply v

/-- Conjugating a boundary translation by the angular meridian applies `M₀`. -/
public theorem paperCuspBoundaryMeridian_conjugate (v : Lattice) :
    paperCuspBoundaryMeridian *
          Additive.toMul (paperCuspBoundaryTranslation v) *
        paperCuspBoundaryMeridian⁻¹ =
      Additive.toMul (paperCuspBoundaryTranslation (M₀ *ᵥ v)) := by
  rw [← paperCuspMonodromy_apply]
  exact canonicalCyclicAffine_conjugate paperCuspMonodromy v

end Topology

namespace Geometry.CuspPuncturedCollarBridge

open SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open SphereSixComplex.LatticeData
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspPhaseEstimates.CuspPeriodExpansion
open SphereSixComplex.Geometry.FamilyEquivariance

variable {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
variable {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}

/-- Translation of normalized additive coordinates by a rank-four period vector. -/
public noncomputable def cuspBoundaryLatticeTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (v : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspRadiusCover W.localWitness.radius :=
  ⟨(periodVector (periodValues
      (assembledFuchsianPeriodFunctions E D).tau
      (assembledFuchsianPeriodFunctions E D).mu
      (assembledFuchsianPeriodFunctions E D).beta (N.lift p.1.2)) v + p.1.1, p.1.2),
    p.2⟩

/-- Translation of the logarithm coordinate by the negative of an integer. -/
public noncomputable def cuspBoundaryAngularTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (k : ℤ)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspRadiusCover W.localWitness.radius :=
  ⟨(p.1.1, p.1.2 - k), by
    change ‖cuspQ (p.1.2 - k)‖ < W.localWitness.radius
    have hsub : p.1.2 - (k : ℂ) = p.1.2 + (-k : ℤ) := by
      push_cast
      ring
    rw [hsub, cuspQ_add_int]
    exact p.2⟩

@[simp]
public theorem cuspBoundaryLatticeTranslate_zero
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryLatticeTranslate W 0 p = p := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simp [cuspBoundaryLatticeTranslate, periodVector, Matrix.mulVec]
  · rfl

@[simp]
public theorem cuspBoundaryLatticeTranslate_add
    (W : ActualPuncturedCuspCollarWitness N M) (v w : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryLatticeTranslate W (v + w) p =
      cuspBoundaryLatticeTranslate W v (cuspBoundaryLatticeTranslate W w p) := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simp only [cuspBoundaryLatticeTranslate, periodVector, Pi.add_apply,
      Int.cast_add]
    rw [show (fun j ↦ (v j : ℂ) + (w j : ℂ)) =
        (fun j ↦ (v j : ℂ)) + fun j ↦ (w j : ℂ) from rfl,
      Matrix.mulVec_add]
    simp only [Pi.add_apply]
    abel
  · rfl

@[simp]
public theorem cuspBoundaryAngularTranslate_zero
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryAngularTranslate W 0 p = p := by
  apply Subtype.ext
  simp [cuspBoundaryAngularTranslate]

@[simp]
public theorem cuspBoundaryAngularTranslate_add
    (W : ActualPuncturedCuspCollarWitness N M) (k l : ℤ)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryAngularTranslate W (k + l) p =
      cuspBoundaryAngularTranslate W k (cuspBoundaryAngularTranslate W l p) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change p.1.2 - ((k + l : ℤ) : ℂ) =
      (p.1.2 - (l : ℂ)) - (k : ℂ)
    push_cast
    ring

/-- The rank-four translation lattice acts on the normalized additive cusp cover. -/
@[instance_reducible] public noncomputable def cuspBoundaryLatticeAction
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction (Multiplicative Lattice)
      (additiveCuspRadiusCover W.localWitness.radius) where
  smul v p := cuspBoundaryLatticeTranslate W v.toAdd p
  one_smul := cuspBoundaryLatticeTranslate_zero W
  mul_smul v w p := cuspBoundaryLatticeTranslate_add W v.toAdd w.toAdd p

/-- The angular logarithm lattice acts on the normalized additive cusp cover. -/
@[instance_reducible] public noncomputable def cuspBoundaryAngularAction
    (W : ActualPuncturedCuspCollarWitness N M) :
    MulAction (Multiplicative ℤ)
      (additiveCuspRadiusCover W.localWitness.radius) where
  smul k p := cuspBoundaryAngularTranslate W k.toAdd p
  one_smul := cuspBoundaryAngularTranslate_zero W
  mul_smul k l p := cuspBoundaryAngularTranslate_add W k.toAdd l.toAdd p

/-- One positive angular turn conjugates a lattice translation by the parabolic monodromy. -/
public theorem cuspBoundaryAngularTranslate_one_latticeTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (v : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    cuspBoundaryAngularTranslate W 1 (cuspBoundaryLatticeTranslate W v p) =
      cuspBoundaryLatticeTranslate W (M₀ *ᵥ v) (cuspBoundaryAngularTranslate W 1 p) := by
  let F := assembledFuchsianPeriodFunctions E D
  let x := periodValues F.tau F.mu F.beta (N.lift p.1.2)
  have hs : p.1.2 ∈ cuspHalfPlane N.height :=
    additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p
  have hlift : N.lift (p.1.2 - 1) =
      E.modularParameter.toTriangleUniformization.sourceAction g₀ • N.lift p.1.2 :=
    N.lift_shift p.1.2 hs
  have hx : periodValues F.tau F.mu F.beta (N.lift (p.1.2 - 1)) = transformCusp x := by
    rw [hlift]
    exact F.transform_cusp (N.lift p.1.2)
  have hperiod :
      periodVector (periodValues F.tau F.mu F.beta (N.lift (p.1.2 - 1))) (M₀ *ᵥ v) =
        periodVector x v := by
    rw [hx, ← m₀_apply]
    exact cusp_periodVector x v
  apply Subtype.ext
  apply Prod.ext
  · simp only [cuspBoundaryAngularTranslate, cuspBoundaryLatticeTranslate]
    simpa only [F, x, Int.cast_one] using
      congrArg (fun z ↦ z + p.1.1) hperiod.symm
  · simp only [cuspBoundaryAngularTranslate, cuspBoundaryLatticeTranslate]

/-- Every rank-four period translation is invisible in the actual global cusp collar. -/
public theorem additiveCuspCoverToGlobal_latticeTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (v : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspCoverToGlobal W (cuspBoundaryLatticeTranslate W v p) =
      additiveCuspCoverToGlobal W p := by
  unfold additiveCuspCoverToGlobal cuspBoundaryLatticeTranslate
  change Quotient.mk _
      (regularCuspFamilyPoint N p.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2)
        (periodVector (periodValues
          (assembledFuchsianPeriodFunctions E D).tau
          (assembledFuchsianPeriodFunctions E D).mu
          (assembledFuchsianPeriodFunctions E D).beta (N.lift p.1.2)) v + p.1.1)) =
    Quotient.mk _
      (regularCuspFamilyPoint N p.1.2
        (W.lift_regular
          (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2) p.1.1)
  apply congrArg (Quotient.mk _)
  exact regularCuspFamilyPoint_period N p.1.2
    (W.lift_regular
      (additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p) p.2) p.1.1 v

/-- Every integral logarithm translation is invisible in the actual global cusp collar. -/
public theorem additiveCuspCoverToGlobal_angularTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (k : ℤ)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspCoverToGlobal W (cuspBoundaryAngularTranslate W k p) =
      additiveCuspCoverToGlobal W p := by
  have hs : p.1.2 ∈ cuspHalfPlane N.height :=
    additiveCuspRadiusCover_halfPlane W.localWitness.radius_le p
  have hq : ‖cuspQ (p.1.2 + (-k : ℤ))‖ < W.localWitness.radius := by
    rw [cuspQ_add_int]
    exact p.2
  simpa only [additiveCuspCoverToGlobal, cuspBoundaryAngularTranslate,
    sub_eq_add_neg, Int.cast_neg] using
      actualPuncturedGlobalCuspPoint_add_int W p.1.2 hs p.2 p.1.1 (-k)
        (cuspHalfPlane_add_int hs (-k)) hq

/-- The square's boundary projection followed by the established collar identification is the
explicit global additive projection. -/
public theorem puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection
    (W : ActualPuncturedCuspCollarWitness N M)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    puncturedLocalCuspQuotientMap W (additiveCuspBoundaryProjection W p) =
      additiveCuspCoverToGlobal W p := by
  change puncturedLocalCuspQuotientMap W
      (Quotient.mk _ (additiveCuspCoverToPuncturedCarrier W p)) =
    additiveCuspCoverToGlobal W p
  rw [puncturedLocalCuspQuotientMap_mk]
  dsimp only [additiveCuspCoverToPuncturedCarrier, puncturedLocalCuspPrequotientMap,
    Function.comp_apply]
  change additiveCuspQuotientToGlobal W
      ((additiveToPuncturedLocalHomeomorph M W.localWitness.radius).symm
        (additiveToPuncturedLocalHomeomorph M W.localWitness.radius (Quotient.mk _ p))) =
    additiveCuspCoverToGlobal W p
  rw [Homeomorph.symm_apply_apply, additiveCuspQuotientToGlobal_mk]

/-- The actual boundary projection is invariant under every rank-four lattice translation. -/
public theorem additiveCuspBoundaryProjection_latticeTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (v : Lattice)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspBoundaryProjection W (cuspBoundaryLatticeTranslate W v p) =
      additiveCuspBoundaryProjection W p := by
  apply puncturedLocalCuspQuotientMap_injective W
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection,
    puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection,
    additiveCuspCoverToGlobal_latticeTranslate]

/-- The actual boundary projection is invariant under every angular logarithm translation. -/
public theorem additiveCuspBoundaryProjection_angularTranslate
    (W : ActualPuncturedCuspCollarWitness N M) (k : ℤ)
    (p : additiveCuspRadiusCover W.localWitness.radius) :
    additiveCuspBoundaryProjection W (cuspBoundaryAngularTranslate W k p) =
      additiveCuspBoundaryProjection W p := by
  apply puncturedLocalCuspQuotientMap_injective W
  rw [puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection,
    puncturedLocalCuspQuotientMap_additiveCuspBoundaryProjection,
    additiveCuspCoverToGlobal_angularTranslate]

end Geometry.CuspPuncturedCollarBridge

end SphereSixComplex

end
