module

public import SphereSixComplex.Geometry.CompactTorusFamilyOverBase
public import SphereSixComplex.Geometry.CuspCollarPairProperness
public import SphereSixComplex.Geometry.StarCompactCover

/-!
# Compact radial cores in the three filling pieces

The two elliptic filling cores are compact because the varying torus family is proper over its
base and compactness descends through the finite orbit quotient.  The pointwise theorem at the
end records the exact filling-side coverage condition needed by `OpenEmbeddingStarData`.
-/

open CategoryTheory TopologicalSpace Topology

namespace SphereSixComplex.Geometry

open Set SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open CuspFilling CuspLocalPhaseAction CuspPuncturedCollarBridge
open EllipticCayleyHomeomorph EllipticVaryingFamilyQuotient
open EllipticLinearCollarGlobalDescent
open EllipticPuncturedCollarGaugeHomeomorph
open EllipticWholeFiberCompactCover TorusFamily

noncomputable section

/-- A compact radial band in a source remains compact after passage to any quotient. -/
public theorem quotientRadialBand_isCompact
    {X : Type*} [TopologicalSpace X] (r : Setoid X) (rho : X → ℝ)
    (rhoQ : Quotient r → ℝ) (a b : ℝ)
    (hrhoQ : ∀ x, rhoQ (Quotient.mk r x) = rho x)
    (hband : IsCompact {x | a ≤ rho x ∧ rho x ≤ b}) :
    IsCompact {q | a ≤ rhoQ q ∧ rhoQ q ≤ b} := by
  have himage : IsCompact
      (Quotient.mk r '' {x | a ≤ rho x ∧ rho x ≤ b}) :=
    hband.image continuous_quot_mk
  convert himage using 1
  ext q
  constructor
  · intro hq
    induction q using Quotient.inductionOn with
    | _ x =>
        refine ⟨x, ?_, rfl⟩
        change a ≤ rhoQ (Quotient.mk r x) ∧ rhoQ (Quotient.mk r x) ≤ b at hq
        change a ≤ rho x ∧ rho x ≤ b
        simpa only [hrhoQ] using hq
  · rintro ⟨x, hx, rfl⟩
    change a ≤ rhoQ (Quotient.mk r x) ∧ rhoQ (Quotient.mk r x) ≤ b
    rw [hrhoQ]
    exact hx

namespace PaperAnalyticData

variable (P : PaperAnalyticData)

/-- The exact remaining compactness boundary on the phase-corrected toric cusp quotient.  It is
local at the missing central fibre: every closed radial sublevel strictly inside the chosen open
filling radius must be compact. -/
@[expose] public def ActualLocalCuspRadialCoreCompactness : Prop :=
  ∀ a, a < P.starCuspWitness.localWitness.radius →
    IsCompact {y : actualLocalCuspFilling P.starCuspWitness |
      actualLocalCuspFillingRadius P.starCuspWitness y ≤ a}

/-- The closed radial sublevel selected inside each filling piece. -/
@[expose] public noncomputable def starFillingRadialCore (a : Fin 3 → ℝ) (i : Fin 3) :
    Set (P.starFillingType i) :=
  {y | P.starFillingRadius i y ≤ a i}

/-- Closed radial sublevels in the actual order-three filling are compact. -/
public theorem orderThreeFillingRadialCore_isCompact
    (a : ℝ) (ha : a < P.starSeparation.orderThree.radius) :
    IsCompact {y : P.OrderThreeVaryingFilling P.starSeparation.orderThree.radius |
      P.orderThreeFillingRadius P.starSeparation.orderThree.radius y ≤ a} := by
  let r := P.starSeparation.orderThree.radius
  let _ := P.orderThreeFillingAction r
  have hsource : IsCompact {q : P.orderThreeFillingOpen r |
      0 ≤ orderThreeFamilyRadius P.periods q ∧
        orderThreeFamilyRadius P.periods q ≤ a} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert P.orderThreeFamilyRadiusBand_isCompact 0 a
      (ha.trans P.starSeparation.orderThree.radius_lt_one) using 1
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨norm_nonneg _, hx.2⟩
    · intro hq
      refine ⟨⟨q, ?_⟩, ⟨norm_nonneg _, hq.2⟩, rfl⟩
      exact hq.2.trans_lt ha
  have hquot : IsCompact {y : P.OrderThreeVaryingFilling r |
      0 ≤ P.orderThreeFillingRadius r y ∧ P.orderThreeFillingRadius r y ≤ a} :=
    quotientRadialBand_isCompact
      (MulAction.orbitRel (FiniteCyclic 3) (P.orderThreeFillingOpen r))
      (fun q : P.orderThreeFillingOpen r ↦ orderThreeFamilyRadius P.periods q)
      (P.orderThreeFillingRadius r) 0 a (fun _ ↦ rfl) hsource
  convert hquot using 1
  ext y
  constructor
  · intro hy
    refine ⟨?_, hy⟩
    induction y using Quotient.inductionOn with
    | _ q => exact norm_nonneg _
  · intro hy
    exact hy.2

/-- Closed radial sublevels in the actual order-four filling are compact. -/
public theorem orderFourFillingRadialCore_isCompact
    (a : ℝ) (ha : a < P.starSeparation.orderFour.radius) :
    IsCompact {y : P.OrderFourVaryingFilling P.starSeparation.orderFour.radius |
      P.orderFourFillingRadius P.starSeparation.orderFour.radius y ≤ a} := by
  let r := P.starSeparation.orderFour.radius
  let _ := P.orderFourFillingAction r
  have hsource : IsCompact {q : P.orderFourFillingOpen r |
      0 ≤ orderFourFamilyRadius P.periods q ∧
        orderFourFamilyRadius P.periods q ≤ a} := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert P.orderFourFamilyRadiusBand_isCompact 0 a
      (ha.trans P.starSeparation.orderFour.radius_lt_one) using 1
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨norm_nonneg _, hx.2⟩
    · intro hq
      refine ⟨⟨q, ?_⟩, ⟨norm_nonneg _, hq.2⟩, rfl⟩
      exact hq.2.trans_lt ha
  have hquot : IsCompact {y : P.OrderFourVaryingFilling r |
      0 ≤ P.orderFourFillingRadius r y ∧ P.orderFourFillingRadius r y ≤ a} :=
    quotientRadialBand_isCompact
      (MulAction.orbitRel (FiniteCyclic 4) (P.orderFourFillingOpen r))
      (fun q : P.orderFourFillingOpen r ↦ orderFourFamilyRadius P.periods q)
      (P.orderFourFillingRadius r) 0 a (fun _ ↦ rfl) hsource
  convert hquot using 1
  ext y
  constructor
  · intro hy
    refine ⟨?_, hy⟩
    induction y using Quotient.inductionOn with
    | _ q => exact norm_nonneg _
  · intro hy
    exact hy.2

public theorem starFillingRadialCore_orderThree_isCompact
    (a : Fin 3 → ℝ) (ha : a 1 < P.starOuterRadius 1) :
    IsCompact (P.starFillingRadialCore a 1) := by
  exact P.orderThreeFillingRadialCore_isCompact (a 1) ha

public theorem starFillingRadialCore_orderFour_isCompact
    (a : Fin 3 → ℝ) (ha : a 2 < P.starOuterRadius 2) :
    IsCompact (P.starFillingRadialCore a 2) := by
  exact P.orderFourFillingRadialCore_isCompact (a 2) ha

public theorem starFillingRadialCore_cusp_isCompact
    (hcusp : P.ActualLocalCuspRadialCoreCompactness)
    (a : Fin 3 → ℝ) (ha : a 0 < P.starOuterRadius 0) :
    IsCompact (P.starFillingRadialCore a 0) :=
  hcusp (a 0) ha

/-- The three radial cores are compact once the isolated toric cusp sublevel theorem is
available.  The order-three and order-four cases are unconditional. -/
public theorem starFillingRadialCore_isCompact
    (hcusp : P.ActualLocalCuspRadialCoreCompactness)
    (a : Fin 3 → ℝ) (ha : ∀ i, a i < P.starOuterRadius i) :
    ∀ i, IsCompact (P.starFillingRadialCore a i) := by
  intro i
  fin_cases i
  · exact P.starFillingRadialCore_cusp_isCompact hcusp a (ha 0)
  · exact P.starFillingRadialCore_orderThree_isCompact a (ha 1)
  · exact P.starFillingRadialCore_orderFour_isCompact a (ha 2)

/-- Outside the selected radial sublevel, every filling point has an exact collar preimage whose
radial coordinate is above the selected threshold. -/
public theorem starFilling_mem_radialCore_or_exists_collar
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∀ (i : Fin 3) (y : P.starFillingType i),
      y ∈ P.starFillingRadialCore a i ∨
        ∃ s : P.starCollarSourceType i, P.starToFilling i s = y ∧
          a i < P.starCollarRadius i s := by
  intro i
  fin_cases i
  · intro y
    by_cases hy : actualLocalCuspFillingRadius P.starCuspWitness y ≤ a 0
    · exact Or.inl hy
    · right
      induction y using Quotient.inductionOn with
      | _ q =>
          have hqnorm : a 0 < ‖P.toricModel.t q‖ := by
            change ¬ ‖P.toricModel.t q‖ ≤ a 0 at hy
            exact lt_of_not_ge hy
          have hqt : P.toricModel.t q ≠ 0 := by
            exact norm_ne_zero_iff.mp (ne_of_gt ((ha 0).trans_lt hqnorm))
          let s : puncturedLocalCuspQuotient P.starCuspWitness := Quotient.mk _
            (⟨q, hqt⟩ : {p : LocalCarrier P.toricModel
              P.starCuspWitness.localWitness.radius //
                P.toricModel.t p ≠ 0})
          refine ⟨s, ?_, ?_⟩
          · exact puncturedLocalCuspToFilling_mk P.starCuspWitness _
          · exact hqnorm
  · intro y
    by_cases hy : P.orderThreeFillingRadius P.starSeparation.orderThree.radius y ≤ a 1
    · exact Or.inl hy
    · right
      induction y using Quotient.inductionOn with
      | _ q =>
          have hqradius : a 1 < orderThreeFamilyRadius P.periods q := by
            change a 1 < P.orderThreeFillingRadius
              P.starSeparation.orderThree.radius (Quotient.mk _ q) at *
            exact lt_of_not_ge hy
          have hqpos : 0 < orderThreeFamilyRadius P.periods q :=
            (ha 1).trans_lt hqradius
          let s : (orderThreeAffinePuncturedCarrier P.periods
              P.modular.modularParameter.toTriangleUniformization_sourceAction
              P.starSeparation.orderThree.radius).carrier :=
            ⟨q, ⟨hqpos, q.property⟩⟩
          refine ⟨Quotient.mk _ s, ?_, ?_⟩
          · exact P.orderThreePuncturedCollarToFilling_mk _ s
          · exact hqradius
  · intro y
    by_cases hy : P.orderFourFillingRadius P.starSeparation.orderFour.radius y ≤ a 2
    · exact Or.inl hy
    · right
      induction y using Quotient.inductionOn with
      | _ q =>
          have hqradius : a 2 < orderFourFamilyRadius P.periods q := by
            change a 2 < P.orderFourFillingRadius
              P.starSeparation.orderFour.radius (Quotient.mk _ q) at *
            exact lt_of_not_ge hy
          have hqpos : 0 < orderFourFamilyRadius P.periods q :=
            (ha 2).trans_lt hqradius
          let s : (orderFourAffinePuncturedCarrier P.periods
              P.modular.modularParameter.toTriangleUniformization_sourceAction
              P.starSeparation.orderFour.radius).carrier :=
            ⟨q, ⟨hqpos, q.property⟩⟩
          refine ⟨Quotient.mk _ s, ?_, ?_⟩
          · exact P.orderFourPuncturedCollarToFilling_mk _ s
          · exact hqradius

/-- Exact filling-side field of `CompactCoverData`, reduced to membership of the outer collar
band in the chosen central compact subset. -/
public theorem starFilling_covers_radialCore
    (a : Fin 3 → ℝ) (ha : ∀ i, 0 ≤ a i) (K : Set P.CentralFamily)
    (hK : ∀ (i : Fin 3) (s : P.starCollarSourceType i),
      a i < P.starCollarRadius i s → P.starToCentral i s ∈ K) :
    ∀ (i : Fin 3) (y : P.openEmbeddingStarData.filling i),
      y ∈ P.starFillingRadialCore a i ∨
        ∃ s : P.openEmbeddingStarData.collarSource i,
          P.openEmbeddingStarData.toFilling i s = y ∧
            P.openEmbeddingStarData.toCentral i s ∈ K := by
  intro i y
  rcases P.starFilling_mem_radialCore_or_exists_collar a ha i y with hy | ⟨s, hsy, hs⟩
  · exact Or.inl hy
  · exact Or.inr ⟨s, hsy, hK i s hs⟩

/-- Package the radial filling cores into the exact common-source compact-cover interface.  All
central-piece work is explicit in `hcentralCompact`, `hcentralCovers`, and `houterCentral`; the
only remaining filling-side boundary is `hcusp`. -/
public noncomputable def openEmbeddingStarCompactCoverData_of_radialCores
    (hcusp : P.ActualLocalCuspRadialCoreCompactness)
    (a : Fin 3 → ℝ) (ha0 : ∀ i, 0 ≤ a i)
    (haOuter : ∀ i, a i < P.starOuterRadius i)
    (K : Set P.CentralFamily) (hcentralCompact : IsCompact K)
    (hcentralCovers : ∀ x : P.CentralFamily, x ∈ K ∨
      ∃ (i : Fin 3) (s : P.starCollarSourceType i),
        P.starToCentral i s = x ∧ P.starToFilling i s ∈ P.starFillingRadialCore a i)
    (houterCentral : ∀ (i : Fin 3) (s : P.starCollarSourceType i),
      a i < P.starCollarRadius i s → P.starToCentral i s ∈ K) :
    P.openEmbeddingStarData.CompactCoverData where
  centralSubset := K
  fillingSubset := P.starFillingRadialCore a
  centralSubset_isCompact := hcentralCompact
  fillingSubset_isCompact := P.starFillingRadialCore_isCompact hcusp a haOuter
  central_covers := hcentralCovers
  filling_covers := P.starFilling_covers_radialCore a ha0 K houterCentral

end PaperAnalyticData

end

end SphereSixComplex.Geometry
