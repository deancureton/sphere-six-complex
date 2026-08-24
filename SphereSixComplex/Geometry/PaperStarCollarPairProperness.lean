module

public import SphereSixComplex.Geometry.PaperStarClosedRelationReduction
public import SphereSixComplex.Geometry.PaperStarPieceHausdorff
public import SphereSixComplex.Geometry.PaperStarComplexStructures
public import SphereSixComplex.Geometry.CompactTorusFamilyOverBase
public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Properness criteria for paired collar maps

A paired collar is proper once compact subsets of the two adjacent pieces trap its radial
coordinate in a compact middle band.  This separates the two ends: compact subsets of the
central piece stay away from the filled end, while compact subsets of the filling stay away from
the outer boundary of the chosen filling carrier.
-/

open CategoryTheory TopologicalSpace Topology
open scoped ContDiff Manifold

namespace SphereSixComplex

noncomputable section

/-- A two-ended radial compactness criterion for the product of two maps. -/
public theorem isProperMap_prod_of_compact_radial_traps
    {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactlyCoherentSpace (X × Y)]
    (f : S → X) (g : S → Y) (rho : S → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hband : ∀ a b : ℝ, IsCompact {s | a ≤ rho s ∧ rho s ≤ b})
    (hleft : ∀ K : Set X, IsCompact K →
      ∃ a : ℝ, ∀ s, f s ∈ K → a ≤ rho s)
    (hright : ∀ K : Set Y, IsCompact K →
      ∃ b : ℝ, ∀ s, g s ∈ K → rho s ≤ b) :
    IsProperMap (fun s ↦ (f s, g s)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hf.prodMk hg, ?_⟩
  intro K hK
  have hKx : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hKy : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  obtain ⟨a, ha⟩ := hleft _ hKx
  obtain ⟨b, hb⟩ := hright _ hKy
  apply (hband a b).of_isClosed_subset
  · exact hK.isClosed.preimage (hf.prodMk hg)
  · intro s hs
    exact ⟨ha s ⟨_, hs, rfl⟩, hb s ⟨_, hs, rfl⟩⟩

/-- Endpoint-aware form of the radial criterion.  Only positive lower bounds and upper bounds
strictly below the outer radius need compact middle bands. -/
public theorem isProperMap_prod_of_twoEnded_radial_traps
    {S X Y : Type*} [TopologicalSpace S] [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [CompactlyCoherentSpace (X × Y)]
    (f : S → X) (g : S → Y) (rho : S → ℝ) (r : ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hband : ∀ a b : ℝ, 0 < a → b < r →
      IsCompact {s | a ≤ rho s ∧ rho s ≤ b})
    (hleft : ∀ K : Set X, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s, f s ∈ K → a ≤ rho s)
    (hright : ∀ K : Set Y, IsCompact K →
      ∃ b : ℝ, b < r ∧ ∀ s, g s ∈ K → rho s ≤ b) :
    IsProperMap (fun s ↦ (f s, g s)) := by
  rw [isProperMap_iff_isCompact_preimage]
  refine ⟨hf.prodMk hg, ?_⟩
  intro K hK
  have hKx : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hKy : IsCompact (Prod.snd '' K) := hK.image continuous_snd
  obtain ⟨a, ha, haK⟩ := hleft _ hKx
  obtain ⟨b, hb, hbK⟩ := hright _ hKy
  apply (hband a b ha hb).of_isClosed_subset
  · exact hK.isClosed.preimage (hf.prodMk hg)
  · intro s hs
    exact ⟨haK s ⟨_, hs, rfl⟩, hbK s ⟨_, hs, rfl⟩⟩

/-- A continuous real-valued function on the left target supplies the compact lower trap. -/
public theorem compact_lower_radial_trap_of_factorsThrough
    {S X : Type*} [TopologicalSpace S] [TopologicalSpace X]
    (f : S → X) (rho : S → ℝ) (R : X → ℝ) (hR : Continuous R)
    (heq : ∀ s, rho s = R (f s)) :
    ∀ K : Set X, IsCompact K → ∃ a : ℝ, ∀ s, f s ∈ K → a ≤ rho s := by
  intro K hK
  have hb : BddBelow (R '' K) := (hK.image hR).bddBelow
  obtain ⟨a, ha⟩ := hb
  refine ⟨a, ?_⟩
  intro s hs
  rw [heq]
  exact ha ⟨f s, hs, rfl⟩

/-- A continuous real-valued function on the right target supplies the compact upper trap. -/
public theorem compact_upper_radial_trap_of_factorsThrough
    {S Y : Type*} [TopologicalSpace S] [TopologicalSpace Y]
    (g : S → Y) (rho : S → ℝ) (R : Y → ℝ) (hR : Continuous R)
    (heq : ∀ s, rho s = R (g s)) :
    ∀ K : Set Y, IsCompact K → ∃ b : ℝ, ∀ s, g s ∈ K → rho s ≤ b := by
  intro K hK
  have hb : BddAbove (R '' K) := (hK.image hR).bddAbove
  obtain ⟨b, hb⟩ := hb
  refine ⟨b, ?_⟩
  intro s hs
  rw [heq]
  exact hb ⟨g s, hs, rfl⟩

/-- If the target radius is everywhere below an outer radius, compact subsets admit an upper
bound still strictly below that radius. -/
public theorem compact_upper_radial_trap_lt_of_factorsThrough
    {S Y : Type*} [TopologicalSpace S] [TopologicalSpace Y]
    (g : S → Y) (rho : S → ℝ) (R : Y → ℝ) (r : ℝ) (hR : Continuous R)
    (heq : ∀ s, rho s = R (g s)) (hlt : ∀ y, R y < r) :
    ∀ K : Set Y, IsCompact K →
      ∃ b : ℝ, b < r ∧ ∀ s, g s ∈ K → rho s ≤ b := by
  intro K hK
  by_cases hKn : K.Nonempty
  · obtain ⟨y, -, hymax⟩ := hK.exists_isMaxOn hKn hR.continuousOn
    refine ⟨R y, hlt y, ?_⟩
    intro s hs
    rw [heq]
    exact hymax hs
  · refine ⟨r - 1, by linarith, ?_⟩
    intro s hs
    exact False.elim (hKn ⟨g s, hs⟩)

namespace OpenEmbeddingStarData

variable (A : OpenEmbeddingStarData)

/-- Radial traps make one paired collar map proper. -/
public theorem collarPairMap_isProper_of_radialTraps
    (i : Fin 3) [T2Space A.central] [T2Space (A.filling i)]
    [CompactlyCoherentSpace (A.central × A.filling i)]
    (rho : A.collarSource i → ℝ)
    (hband : ∀ a b : ℝ, IsCompact {s | a ≤ rho s ∧ rho s ≤ b})
    (hcentral : ∀ K : Set A.central, IsCompact K →
      ∃ a : ℝ, ∀ s, A.toCentral i s ∈ K → a ≤ rho s)
    (hfilling : ∀ K : Set (A.filling i), IsCompact K →
      ∃ b : ℝ, ∀ s, A.toFilling i s ∈ K → rho s ≤ b) :
    IsProperMap (A.collarPairMap i) := by
  exact isProperMap_prod_of_compact_radial_traps
    (A.toCentral i) (A.toFilling i) rho
    (A.toCentral_isOpenEmbedding i).continuous
    (A.toFilling_isOpenEmbedding i).continuous hband hcentral hfilling

/-- Endpoint-aware radial traps make one paired collar map proper. -/
public theorem collarPairMap_isProper_of_twoEndedRadialTraps
    (i : Fin 3) [T2Space A.central] [T2Space (A.filling i)]
    [CompactlyCoherentSpace (A.central × A.filling i)]
    (rho : A.collarSource i → ℝ) (r : ℝ)
    (hband : ∀ a b : ℝ, 0 < a → b < r →
      IsCompact {s | a ≤ rho s ∧ rho s ≤ b})
    (hcentral : ∀ K : Set A.central, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s, A.toCentral i s ∈ K → a ≤ rho s)
    (hfilling : ∀ K : Set (A.filling i), IsCompact K →
      ∃ b : ℝ, b < r ∧ ∀ s, A.toFilling i s ∈ K → rho s ≤ b) :
    IsProperMap (A.collarPairMap i) := by
  exact isProperMap_prod_of_twoEnded_radial_traps
    (A.toCentral i) (A.toFilling i) rho r
    (A.toCentral_isOpenEmbedding i).continuous
    (A.toFilling_isOpenEmbedding i).continuous hband hcentral hfilling

/-- Radial traps for all three collars supply the exact closed-pair datum used by the finite
gluing criterion. -/
public theorem closedCollarPairData_of_radialTraps
    [T2Space A.central] [∀ i, T2Space (A.filling i)]
    [∀ i, CompactlyCoherentSpace (A.central × A.filling i)]
    (rho : ∀ i, A.collarSource i → ℝ)
    (hband : ∀ i a b, IsCompact {s | a ≤ rho i s ∧ rho i s ≤ b})
    (hcentral : ∀ i (K : Set A.central), IsCompact K →
      ∃ a : ℝ, ∀ s, A.toCentral i s ∈ K → a ≤ rho i s)
    (hfilling : ∀ i (K : Set (A.filling i)), IsCompact K →
      ∃ b : ℝ, ∀ s, A.toFilling i s ∈ K → rho i s ≤ b) :
    A.ClosedCollarPairData := by
  apply A.closedCollarPairData_of_isProperMap
  intro i
  exact A.collarPairMap_isProper_of_radialTraps i (rho i)
    (hband i) (hcentral i) (hfilling i)

end OpenEmbeddingStarData

namespace Geometry

open Set Topology SphereSixComplex.Periods SphereSixComplex.TriangleGroup
open CuspPuncturedCollarBridge CuspPhaseEstimates CuspPeriodExpansion
open CuspFilling CuspLocalPhaseAction StandardInfiniteA2ToricModel
open EllipticVaryingFamilyQuotient EllipticPuncturedCollarGaugeHomeomorph
open EllipticWholeFiberCompactCover
open EllipticCayleyHomeomorph TorusFamily
open EllipticLocalCoordinates
open EquivariantQuotientHomeomorph

/-- An ambient compact radial band remains compact after restriction to an invariant carrier
and passage to its orbit quotient. -/
public theorem restrictedOrbitQuotientRadiusBand_isCompact
    {G M : Type*} [Group G] [TopologicalSpace M] [MulAction G M]
    (A : MulAction G M) (C : InvariantOpenCarrier A)
    (rho : M → ℝ)
    (rhoQ : Quotient (restrictedOrbitRel A C) → ℝ)
    (a b : ℝ)
    (hrhoQ : ∀ x : C.carrier, rhoQ (Quotient.mk _ x) = rho x)
    (hband : IsCompact {x : M | a ≤ rho x ∧ rho x ≤ b})
    (hinside : ∀ x : M, a ≤ rho x ∧ rho x ≤ b → x ∈ C.carrier) :
    IsCompact {q : Quotient (restrictedOrbitRel A C) |
      a ≤ rhoQ q ∧ rhoQ q ≤ b} := by
  let B : Set C.carrier := {x | a ≤ rho x ∧ rho x ≤ b}
  have hB : IsCompact B := by
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
    convert hband using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hinside x hx⟩, hx, rfl⟩
  have himage : IsCompact (Quotient.mk (restrictedOrbitRel A C) '' B) :=
    hB.image continuous_quot_mk
  convert himage using 1
  ext q
  constructor
  · intro hq
    induction q using Quotient.inductionOn with
    | _ x =>
        exact ⟨x, by simpa only [B, Set.mem_ofPred_eq, hrhoQ] using hq, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    simpa only [B, Set.mem_ofPred_eq, hrhoQ] using hx

/-- A closed radial band strictly inside the complex unit disc is compact. -/
public theorem complexUnitDiscRadiusBand_isCompact
    (a b : ℝ) (hb : b < 1) :
    IsCompact {w : ComplexUnitDisc | a ≤ ‖(w : ℂ)‖ ∧ ‖(w : ℂ)‖ ≤ b} := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have hclosed : IsClosed {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  have hcomp : IsCompact {z : ℂ | a ≤ ‖z‖ ∧ ‖z‖ ≤ b} := by
    apply (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset hclosed
    intro z hz
    exact mem_closedBall_zero_iff.mpr hz.2
  convert hcomp using 1
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    have hz1 : ‖z‖ < 1 := hz.2.trans_lt hb
    exact ⟨⟨z, hz1⟩, hz, rfl⟩

public theorem orderThreeCayleyRadiusBand_isCompact
    (a b : ℝ) (hb : b < 1) :
    IsCompact {z : UpperHalfPlane |
      a ≤ ‖(orderThreeCayleyHomeomorph z).1‖ ∧
        ‖(orderThreeCayleyHomeomorph z).1‖ ≤ b} :=
  orderThreeCayleyHomeomorph.isProperMap.isCompact_preimage
    (complexUnitDiscRadiusBand_isCompact a b hb)

public theorem orderFourCayleyRadiusBand_isCompact
    (a b : ℝ) (hb : b < 1) :
    IsCompact {z : UpperHalfPlane |
      a ≤ ‖(orderFourCayleyHomeomorph z).1‖ ∧
        ‖(orderFourCayleyHomeomorph z).1‖ ≤ b} :=
  orderFourCayleyHomeomorph.isProperMap.isCompact_preimage
    (complexUnitDiscRadiusBand_isCompact a b hb)

/-- Absolute value of the height coordinate on the actual local cusp filling. -/
@[expose] public noncomputable def actualLocalCuspFillingRadius
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    actualLocalCuspFilling W → ℝ :=
  Quotient.lift (fun p : LocalCarrier M W.localWitness.radius ↦ ‖M.t p‖) (by
    intro p q hpq
    let C :=
      CuspPhaseEstimates.CuspPeriodExpansion.NormalizedFuchsianCuspCoordinate.restrictedActualLocalPhaseCoefficients
        N M W.localWitness.radius W.localWitness.radius_pos W.localWitness.radius_le
    let _ : MulAction (Multiplicative ParameterLattice)
        (LocalCarrier M W.localWitness.radius) :=
      (C.toCuspActionData W.localWitness.fixedPoint).psiAction
    change MulAction.orbitRel (Multiplicative ParameterLattice) _ p q at hpq
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
    obtain ⟨gamma, rfl⟩ := hpq
    exact congrArg norm
      ((C.toCuspActionData W.localWitness.fixedPoint).preserves_t gamma q))

public theorem actualLocalCuspFillingRadius_continuous
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M) :
    Continuous (actualLocalCuspFillingRadius W) := by
  apply continuous_quot_lift
  exact continuous_norm.comp
    (M.t_holomorphic.continuous.comp continuous_subtype_val)

public theorem actualLocalCuspFillingRadius_lt
    {E : EstablishedFuchsianModularParameter} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model}
    (W : ActualPuncturedCuspCollarWitness N M)
    (y : actualLocalCuspFilling W) :
    actualLocalCuspFillingRadius W y < W.localWitness.radius := by
  induction y using Quotient.inductionOn with
  | _ p => exact mem_ball_zero_iff.mp p.property

namespace PaperAnalyticData

variable (P : PaperAnalyticData)

public theorem orderThreeFamilyRadiusBand_isCompact
    (a b : ℝ) (hb : b < 1) :
    IsCompact (familyTotalSpaceBase P.periods ⁻¹'
    {z : UpperHalfPlane | a ≤ ‖(orderThreeCayleyHomeomorph z).1‖ ∧
      ‖(orderThreeCayleyHomeomorph z).1‖ ≤ b}) :=
  (familyTotalSpaceBase_isProperMap P.periods).isCompact_preimage
    (orderThreeCayleyRadiusBand_isCompact a b hb)

public theorem orderFourFamilyRadiusBand_isCompact
    (a b : ℝ) (hb : b < 1) :
    IsCompact (familyTotalSpaceBase P.periods ⁻¹'
    {z : UpperHalfPlane | a ≤ ‖(orderFourCayleyHomeomorph z).1‖ ∧
      ‖(orderFourCayleyHomeomorph z).1‖ ≤ b}) :=
  (familyTotalSpaceBase_isProperMap P.periods).isCompact_preimage
    (orderFourCayleyRadiusBand_isCompact a b hb)

/-- The invariant order-three elliptic radius descended to the finite filling quotient. -/
@[expose] public noncomputable def orderThreeFillingRadius (r : ℝ) :
    P.OrderThreeVaryingFilling r → ℝ :=
  Quotient.lift (fun q : P.orderThreeFillingOpen r ↦
    orderThreeFamilyRadius P.periods q) (by
      intro p q hpq
      let _ := P.orderThreeFillingAction r
      change MulAction.orbitRel (FiniteCyclic 3) _ p q at hpq
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
      obtain ⟨g, rfl⟩ := hpq
      exact orderThreeFamilyRadius_representation P.periods
        P.modular.modularParameter.toTriangleUniformization_sourceAction g q)

public theorem orderThreeFillingRadius_continuous (r : ℝ) :
    Continuous (P.orderThreeFillingRadius r) := by
  apply continuous_quot_lift
  exact (orderThreeFamilyRadius_continuous P.periods).comp continuous_subtype_val

public theorem orderThreeFillingRadius_lt (r : ℝ)
    (y : P.OrderThreeVaryingFilling r) :
    P.orderThreeFillingRadius r y < r := by
  induction y using Quotient.inductionOn with
  | _ q => exact q.property

/-- The invariant order-four elliptic radius descended to the finite filling quotient. -/
@[expose] public noncomputable def orderFourFillingRadius (r : ℝ) :
    P.OrderFourVaryingFilling r → ℝ :=
  Quotient.lift (fun q : P.orderFourFillingOpen r ↦
    orderFourFamilyRadius P.periods q) (by
      intro p q hpq
      let _ := P.orderFourFillingAction r
      change MulAction.orbitRel (FiniteCyclic 4) _ p q at hpq
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hpq
      obtain ⟨g, rfl⟩ := hpq
      exact orderFourFamilyRadius_representation P.periods
        P.modular.modularParameter.toTriangleUniformization_sourceAction g q)

public theorem orderFourFillingRadius_continuous (r : ℝ) :
    Continuous (P.orderFourFillingRadius r) := by
  apply continuous_quot_lift
  exact (orderFourFamilyRadius_continuous P.periods).comp continuous_subtype_val

public theorem orderFourFillingRadius_lt (r : ℝ)
    (y : P.OrderFourVaryingFilling r) :
    P.orderFourFillingRadius r y < r := by
  induction y using Quotient.inductionOn with
  | _ q => exact q.property

/-- Compact radial bands in the concrete order-three collar quotient. -/
public theorem orderThreePuncturedCollarRadiusBand_isCompact
    (r a b : ℝ) (ha : 0 < a) (hb : b < r) (hr : r < 1) :
    IsCompact {s : Quotient (restrictedOrbitRel
        (orderThreeAffineFamilyAction P.periods)
        (orderThreeAffinePuncturedCarrier P.periods
          P.modular.modularParameter.toTriangleUniformization_sourceAction r)) |
      a ≤ (P.orderThreeFillingRadius r ∘
          P.orderThreePuncturedCollarToFilling r) s ∧
        (P.orderThreeFillingRadius r ∘
          P.orderThreePuncturedCollarToFilling r) s ≤ b} := by
  let _ := orderThreeAffineFamilyAction P.periods
  apply restrictedOrbitQuotientRadiusBand_isCompact
    (orderThreeAffineFamilyAction P.periods)
    (orderThreeAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction r)
    (fun q ↦ ‖(orderThreeCayleyHomeomorph
      (familyTotalSpaceBase P.periods q)).1‖)
    (P.orderThreeFillingRadius r ∘
      P.orderThreePuncturedCollarToFilling r) a b
  · intro x
    change P.orderThreeFillingRadius r
      (P.orderThreePuncturedCollarToFilling r (Quotient.mk _ x)) = _
    rw [P.orderThreePuncturedCollarToFilling_mk]
    rfl
  · exact P.orderThreeFamilyRadiusBand_isCompact a b (hb.trans hr)
  · intro q hq
    change q ∈ orderThreePuncturedFamilyCollar P.periods r
    rw [orderThreePuncturedFamilyCollar.eq_def]
    exact ⟨ha.trans_le hq.1, hq.2.trans_lt hb⟩

/-- Compact radial bands in the concrete order-four collar quotient. -/
public theorem orderFourPuncturedCollarRadiusBand_isCompact
    (r a b : ℝ) (ha : 0 < a) (hb : b < r) (hr : r < 1) :
    IsCompact {s : Quotient (restrictedOrbitRel
        (orderFourAffineFamilyAction P.periods)
        (orderFourAffinePuncturedCarrier P.periods
          P.modular.modularParameter.toTriangleUniformization_sourceAction r)) |
      a ≤ (P.orderFourFillingRadius r ∘
          P.orderFourPuncturedCollarToFilling r) s ∧
        (P.orderFourFillingRadius r ∘
          P.orderFourPuncturedCollarToFilling r) s ≤ b} := by
  let _ := orderFourAffineFamilyAction P.periods
  apply restrictedOrbitQuotientRadiusBand_isCompact
    (orderFourAffineFamilyAction P.periods)
    (orderFourAffinePuncturedCarrier P.periods
      P.modular.modularParameter.toTriangleUniformization_sourceAction r)
    (fun q ↦ ‖(orderFourCayleyHomeomorph
      (familyTotalSpaceBase P.periods q)).1‖)
    (P.orderFourFillingRadius r ∘
      P.orderFourPuncturedCollarToFilling r) a b
  · intro x
    change P.orderFourFillingRadius r
      (P.orderFourPuncturedCollarToFilling r (Quotient.mk _ x)) = _
    rw [P.orderFourPuncturedCollarToFilling_mk]
    rfl
  · exact P.orderFourFamilyRadiusBand_isCompact a b (hb.trans hr)
  · intro q hq
    change q ∈ orderFourPuncturedFamilyCollar P.periods r
    rw [orderFourPuncturedFamilyCollar.eq_def]
    exact ⟨ha.trans_le hq.1, hq.2.trans_lt hb⟩

/-- The radius on each of the three concrete filling pieces. -/
@[expose] public noncomputable def starFillingRadius :
    ∀ i, P.starFillingType i → ℝ :=
  Fin.cases (actualLocalCuspFillingRadius P.starCuspWitness) fun i ↦
    Fin.cases
      (P.orderThreeFillingRadius P.starSeparation.orderThree.radius)
      (fun _ ↦ P.orderFourFillingRadius P.starSeparation.orderFour.radius) i

/-- The common radial coordinate on a collar, read through its filling embedding. -/
@[expose] public noncomputable def starCollarRadius (i : Fin 3) :
    P.starCollarSourceType i → ℝ :=
  P.starFillingRadius i ∘ P.starToFilling i

/-- The selected outer radius for each concrete filling carrier. -/
@[expose] public noncomputable def starOuterRadius : Fin 3 → ℝ :=
  Fin.cases P.starCuspWitness.localWitness.radius fun i ↦
    Fin.cases P.starSeparation.orderThree.radius
      (fun _ ↦ P.starSeparation.orderFour.radius) i

public theorem starFillingRadius_continuous (i : Fin 3) :
    Continuous (P.starFillingRadius i) := by
  fin_cases i
  · exact actualLocalCuspFillingRadius_continuous P.starCuspWitness
  · exact P.orderThreeFillingRadius_continuous P.starSeparation.orderThree.radius
  · exact P.orderFourFillingRadius_continuous P.starSeparation.orderFour.radius

public theorem starFillingRadius_lt_outer (i : Fin 3)
    (y : P.starFillingType i) :
    P.starFillingRadius i y < P.starOuterRadius i := by
  fin_cases i
  · exact actualLocalCuspFillingRadius_lt P.starCuspWitness y
  · exact P.orderThreeFillingRadius_lt P.starSeparation.orderThree.radius y
  · exact P.orderFourFillingRadius_lt P.starSeparation.orderFour.radius y

/-- Compact middle bands in the order-three collar of the concrete star. -/
public theorem orderThreeStarCollarRadiusBand_isCompact
    (a b : ℝ) (ha : 0 < a)
    (hb : b < P.starSeparation.orderThree.radius) :
    IsCompact {s : P.starCollarSourceType (1 : Fin 3) |
      a ≤ P.starCollarRadius (1 : Fin 3) s ∧
        P.starCollarRadius (1 : Fin 3) s ≤ b} := by
  change IsCompact {s : Quotient (restrictedOrbitRel
      (orderThreeAffineFamilyAction P.periods)
      (orderThreeAffinePuncturedCarrier P.periods
        P.modular.modularParameter.toTriangleUniformization_sourceAction
        P.starSeparation.orderThree.radius)) |
    a ≤ (P.orderThreeFillingRadius P.starSeparation.orderThree.radius ∘
      P.orderThreePuncturedCollarToFilling
        P.starSeparation.orderThree.radius) s ∧
    (P.orderThreeFillingRadius P.starSeparation.orderThree.radius ∘
      P.orderThreePuncturedCollarToFilling
        P.starSeparation.orderThree.radius) s ≤ b}
  exact P.orderThreePuncturedCollarRadiusBand_isCompact
    P.starSeparation.orderThree.radius a b ha hb
    P.starSeparation.orderThree.radius_lt_one

/-- Compact middle bands in the order-four collar of the concrete star. -/
public theorem orderFourStarCollarRadiusBand_isCompact
    (a b : ℝ) (ha : 0 < a)
    (hb : b < P.starSeparation.orderFour.radius) :
    IsCompact {s : P.starCollarSourceType (2 : Fin 3) |
      a ≤ P.starCollarRadius (2 : Fin 3) s ∧
        P.starCollarRadius (2 : Fin 3) s ≤ b} := by
  change IsCompact {s : Quotient (restrictedOrbitRel
      (orderFourAffineFamilyAction P.periods)
      (orderFourAffinePuncturedCarrier P.periods
        P.modular.modularParameter.toTriangleUniformization_sourceAction
        P.starSeparation.orderFour.radius)) |
    a ≤ (P.orderFourFillingRadius P.starSeparation.orderFour.radius ∘
      P.orderFourPuncturedCollarToFilling
        P.starSeparation.orderFour.radius) s ∧
    (P.orderFourFillingRadius P.starSeparation.orderFour.radius ∘
      P.orderFourPuncturedCollarToFilling
        P.starSeparation.orderFour.radius) s ≤ b}
  exact P.orderFourPuncturedCollarRadiusBand_isCompact
    P.starSeparation.orderFour.radius a b ha hb
    P.starSeparation.orderFour.radius_lt_one

/-- Compact subsets of every concrete filling give the upper radial trap automatically. -/
public theorem starCollarRadius_compact_upperTrap (i : Fin 3) :
    ∀ K : Set (P.starFillingType i), IsCompact K →
      ∃ b : ℝ, ∀ s, P.starToFilling i s ∈ K → P.starCollarRadius i s ≤ b := by
  apply compact_upper_radial_trap_of_factorsThrough
    (P.starToFilling i) (P.starCollarRadius i) (P.starFillingRadius i)
    (P.starFillingRadius_continuous i)
  intro s
  rfl

/-- The filling-side upper trap can be chosen strictly below the selected outer radius. -/
public theorem starCollarRadius_compact_upperTrap_lt (i : Fin 3) :
    ∀ K : Set (P.starFillingType i), IsCompact K →
      ∃ b : ℝ, b < P.starOuterRadius i ∧
        ∀ s, P.starToFilling i s ∈ K → P.starCollarRadius i s ≤ b := by
  apply compact_upper_radial_trap_lt_of_factorsThrough
    (P.starToFilling i) (P.starCollarRadius i) (P.starFillingRadius i)
    (P.starOuterRadius i) (P.starFillingRadius_continuous i)
  · intro s
    rfl
  · exact P.starFillingRadius_lt_outer i

/-- Properness of the order-three collar pair is reduced to its central-end escape estimate;
the compact-band and filling-end estimates are concrete. -/
public theorem orderThreeCollarPairMap_isProper_of_centralLowerTrap
    (hcentral : ∀ K : Set P.CentralFamily, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s : P.starCollarSourceType (1 : Fin 3),
        P.starToCentral (1 : Fin 3) s ∈ K →
          a ≤ P.starCollarRadius (1 : Fin 3) s) :
    IsProperMap (P.openEmbeddingStarData.collarPairMap (1 : Fin 3)) := by
  let _ := P.starCentralCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ P.CentralFamily :=
    P.starCentral_isManifold
  let _ : LocallyCompactSpace P.CentralFamily :=
    Manifold.locallyCompact_of_finiteDimensional
      (modelWithCornersSelf ℂ ComplexModel)
  let _ := P.starFillingCharts (1 : Fin 3)
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (P.starFillingType (1 : Fin 3)) := P.starFilling_isManifold (1 : Fin 3)
  let _ : LocallyCompactSpace (P.starFillingType (1 : Fin 3)) :=
    Manifold.locallyCompact_of_finiteDimensional
      (modelWithCornersSelf ℂ ComplexModel)
  let _ : T2Space P.openEmbeddingStarData.central := by
    change T2Space P.CentralFamily
    exact P.centralFamily_t2
  let _ : T2Space (P.openEmbeddingStarData.filling (1 : Fin 3)) := by
    change T2Space (P.starFillingType (1 : Fin 3))
    exact P.starFilling_t2 (1 : Fin 3)
  let _ : LocallyCompactSpace P.openEmbeddingStarData.central := by
    change LocallyCompactSpace P.CentralFamily
    infer_instance
  let _ : LocallyCompactSpace
      (P.openEmbeddingStarData.filling (1 : Fin 3)) := by
    change LocallyCompactSpace (P.starFillingType (1 : Fin 3))
    infer_instance
  apply P.openEmbeddingStarData.collarPairMap_isProper_of_twoEndedRadialTraps
    (1 : Fin 3) (P.starCollarRadius (1 : Fin 3))
    P.starSeparation.orderThree.radius
  · exact P.orderThreeStarCollarRadiusBand_isCompact
  · exact hcentral
  · exact P.starCollarRadius_compact_upperTrap_lt (1 : Fin 3)

/-- Properness of the order-four collar pair is reduced to its central-end escape estimate;
the compact-band and filling-end estimates are concrete. -/
public theorem orderFourCollarPairMap_isProper_of_centralLowerTrap
    (hcentral : ∀ K : Set P.CentralFamily, IsCompact K →
      ∃ a : ℝ, 0 < a ∧ ∀ s : P.starCollarSourceType (2 : Fin 3),
        P.starToCentral (2 : Fin 3) s ∈ K →
          a ≤ P.starCollarRadius (2 : Fin 3) s) :
    IsProperMap (P.openEmbeddingStarData.collarPairMap (2 : Fin 3)) := by
  let _ := P.starCentralCharts
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞ P.CentralFamily :=
    P.starCentral_isManifold
  let _ : LocallyCompactSpace P.CentralFamily :=
    Manifold.locallyCompact_of_finiteDimensional
      (modelWithCornersSelf ℂ ComplexModel)
  let _ := P.starFillingCharts (2 : Fin 3)
  let _ : IsManifold (modelWithCornersSelf ℂ ComplexModel) ∞
      (P.starFillingType (2 : Fin 3)) := P.starFilling_isManifold (2 : Fin 3)
  let _ : LocallyCompactSpace (P.starFillingType (2 : Fin 3)) :=
    Manifold.locallyCompact_of_finiteDimensional
      (modelWithCornersSelf ℂ ComplexModel)
  let _ : T2Space P.openEmbeddingStarData.central := by
    change T2Space P.CentralFamily
    exact P.centralFamily_t2
  let _ : T2Space (P.openEmbeddingStarData.filling (2 : Fin 3)) := by
    change T2Space (P.starFillingType (2 : Fin 3))
    exact P.starFilling_t2 (2 : Fin 3)
  let _ : LocallyCompactSpace P.openEmbeddingStarData.central := by
    change LocallyCompactSpace P.CentralFamily
    infer_instance
  let _ : LocallyCompactSpace
      (P.openEmbeddingStarData.filling (2 : Fin 3)) := by
    change LocallyCompactSpace (P.starFillingType (2 : Fin 3))
    infer_instance
  apply P.openEmbeddingStarData.collarPairMap_isProper_of_twoEndedRadialTraps
    (2 : Fin 3) (P.starCollarRadius (2 : Fin 3))
    P.starSeparation.orderFour.radius
  · exact P.orderFourStarCollarRadiusBand_isCompact
  · exact hcentral
  · exact P.starCollarRadius_compact_upperTrap_lt (2 : Fin 3)

end PaperAnalyticData

end Geometry

end

end SphereSixComplex
