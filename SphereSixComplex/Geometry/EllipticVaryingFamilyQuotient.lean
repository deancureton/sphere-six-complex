module

public import SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
public import SphereSixComplex.Geometry.GlobalDeckSmoothness
public import SphereSixComplex.Geometry.GlobalDeckQuotient
public import SphereSixComplex.Geometry.EllipticCayleyHomeomorph
public import SphereSixComplex.Geometry.ProperlyDiscontinuousSlice
public import SphereSixComplex.TriangleGroup.FreeProductTorsion
public import Mathlib.Geometry.Manifold.Algebra.SMul
import all SphereSixComplex.Geometry.GlobalTorusFamily
import all SphereSixComplex.Geometry.Quotient
import all SphereSixComplex.Geometry.TorusFamily

/-!
# Affine cyclic actions on the varying elliptic torus families

The elliptic pieces are finite quotients of the varying torus family itself.  This file begins
that construction directly, without identifying the family holomorphically with a product by one
fixed torus.
-/

open scoped Manifold ContDiff

namespace SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient

open Filter Set SphereSixComplex.Geometry
open SphereSixComplex.Geometry.ComplexTorus
open SphereSixComplex.Geometry.TorusFamily
open SphereSixComplex.Geometry.AnalyticTorusFamily
open SphereSixComplex.Geometry.GlobalTorusFamily
open SphereSixComplex.Geometry.FamilyEquivariance
open SphereSixComplex.Geometry.EllipticWholeFiberTrivialization
open SphereSixComplex.Geometry.EllipticWholeFiberCompactCover
open SphereSixComplex.Geometry.EllipticFamilySpecialization
open SphereSixComplex.Geometry.EllipticFixedPointCriterion
open SphereSixComplex.Geometry.EllipticCayleyHomeomorph
open SphereSixComplex.Geometry.EllipticLocalCoordinates
open SphereSixComplex.LatticeData
open SphereSixComplex.TriangleGroup SphereSixComplex.Periods

noncomputable section

variable {U : TriangleUniformization} (F : PeriodFunctions U)

/-- Translation by a base-dependent vector section on the vector-bundle cover. -/
@[expose] public def familyTranslationCover
    (s : UpperHalfPlane → ComplexTwoSpace)
    (p : UpperHalfPlane × ComplexTwoSpace) : UpperHalfPlane × ComplexTwoSpace :=
  (p.1, s p.1 + p.2)

/-- Translation by a base-dependent vector section as an equivalence of the vector-bundle
cover, before taking the varying period-lattice quotient. -/
@[expose] public def familyTranslationCoverEquiv
    (s : UpperHalfPlane → ComplexTwoSpace) :
    Equiv.Perm (UpperHalfPlane × ComplexTwoSpace) where
  toFun := familyTranslationCover s
  invFun := familyTranslationCover (-s)
  left_inv p := by
    apply Prod.ext
    · rfl
    · simp [familyTranslationCover]
  right_inv p := by
    apply Prod.ext
    · rfl
    · simp [familyTranslationCover]

@[simp]
public theorem familyTranslationCoverEquiv_apply
    (s : UpperHalfPlane → ComplexTwoSpace)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    familyTranslationCoverEquiv s p = familyTranslationCover s p :=
  rfl

/-- Iteration on the vector-bundle cover records the actual accumulated translation rather than
discarding it modulo the period lattice. -/
public theorem familyTranslationCoverEquiv_pow_apply
    (s : UpperHalfPlane → ComplexTwoSpace) (k : ℕ)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    (familyTranslationCoverEquiv s ^ k) p =
      (p.1, k • s p.1 + p.2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, familyTranslationCoverEquiv_apply]
      change (familyTranslationCoverEquiv s ^ k)
        (p.1, s p.1 + p.2) = _
      rw [ih]
      apply Prod.ext
      · rfl
      · change k • s p.1 + (s p.1 + p.2) = (k + 1) • s p.1 + p.2
        simp only [add_nsmul, one_nsmul]
        abel

/-- Deck transport commutes with a cover translation whose section is transported naturally. -/
public theorem deckEquiv_commutes_familyTranslationCoverEquiv
    (g : Delta) (s : UpperHalfPlane → ComplexTwoSpace)
    (hnatural : ∀ z, periodTransport g (parameterMap F z) (s z) =
      s (U.sourceAction g • z)) :
    Commute (deckEquiv F g) (familyTranslationCoverEquiv s) := by
  apply Equiv.ext
  intro p
  apply Prod.ext
  · rfl
  · change periodTransport g (parameterMap F p.1) (s p.1 + p.2) =
      s (U.sourceAction g • p.1) +
        periodTransport g (parameterMap F p.1) p.2
    rw [map_add, hnatural]

/-- A fibrewise translation preserves the varying period-lattice orbit relation. -/
public theorem familyTranslationCover_orbitRel
    (s : UpperHalfPlane → ComplexTwoSpace)
    (p q : UpperHalfPlane × ComplexTwoSpace)
    (h : MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _ p q) :
    MulAction.orbitRel (FamilyPeriodGroup (parameterMap F)) _
      (familyTranslationCover s p) (familyTranslationCover s q) := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
  obtain ⟨g, hg⟩ := h
  refine ⟨g, ?_⟩
  have hbase : p.1 = q.1 := by
    simpa only [family_smul_fst] using congrArg Prod.fst hg.symm
  apply Prod.ext
  · simpa [familyTranslationCover] using congrArg Prod.fst hg
  · have hsnd := congrArg Prod.snd hg
    simp only [family_smul_snd] at hsnd ⊢
    simp only [familyTranslationCover, hbase]
    rw [← hsnd]
    abel

/-- Fibrewise translation descended to the varying torus quotient. -/
@[expose] public noncomputable def familyTranslationMap
    (s : UpperHalfPlane → ComplexTwoSpace) :
    TotalSpace (parameterMap F) → TotalSpace (parameterMap F) :=
  Quotient.map (familyTranslationCover s)
    (fun p q h ↦ familyTranslationCover_orbitRel F s p q h)

@[simp]
public theorem familyTranslationMap_mk
    (s : UpperHalfPlane → ComplexTwoSpace)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    familyTranslationMap F s (Quotient.mk _ p) =
      Quotient.mk _ (familyTranslationCover s p) :=
  rfl

/-- Every base-dependent fibre translation is an equivalence of the varying quotient. -/
@[expose] public noncomputable def familyTranslationEquiv
    (s : UpperHalfPlane → ComplexTwoSpace) :
    Equiv.Perm (TotalSpace (parameterMap F)) where
  toFun := familyTranslationMap F s
  invFun := familyTranslationMap F (-s)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ p =>
      simp only [familyTranslationMap_mk, familyTranslationCover.eq_def,
        Pi.neg_apply, neg_add_cancel_left]
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ p =>
      simp only [familyTranslationMap_mk, familyTranslationCover.eq_def,
        Pi.neg_apply]
      congr 2
      abel

@[simp]
public theorem familyTranslationEquiv_apply
    (s : UpperHalfPlane → ComplexTwoSpace)
    (q : TotalSpace (parameterMap F)) :
    familyTranslationEquiv F s q = familyTranslationMap F s q :=
  rfl

/-- Iterating a fibre translation adds the corresponding natural-number multiple of its section. -/
public theorem familyTranslationEquiv_pow_apply
    (s : UpperHalfPlane → ComplexTwoSpace) (k : ℕ)
    (p : UpperHalfPlane × ComplexTwoSpace) :
    (familyTranslationEquiv F s ^ k) (Quotient.mk _ p) =
      Quotient.mk _ (p.1, k • s p.1 + p.2) := by
  induction k generalizing p with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, familyTranslationEquiv_apply,
        familyTranslationMap_mk]
      change (familyTranslationEquiv F s ^ k)
        (Quotient.mk _ (p.1, s p.1 + p.2)) = _
      rw [ih]
      congr 2
      simp only [add_nsmul]
      abel

/-- If an integral multiple of a section is a period section, the corresponding power of its
translation equivalence is the identity on the varying quotient. -/
public theorem familyTranslationEquiv_pow_eq_one
    (s : UpperHalfPlane → ComplexTwoSpace) (k : ℕ)
    (hperiod : ∀ z, ∃ n : IntegerPeriods,
      k • s z = periodVector (parameterMap F z).1 n) :
    familyTranslationEquiv F s ^ k = 1 := by
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    rw [familyTranslationEquiv_pow_apply]
    obtain ⟨n, hn⟩ := hperiod p.1
    apply Quotient.sound
    change MulAction.orbitRel (FamilyPeriodGroup (parameterMap F))
      (UpperHalfPlane × ComplexTwoSpace) (p.1, k • s p.1 + p.2) p
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
    let g : FamilyPeriodGroup (parameterMap F) := Multiplicative.ofAdd n
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · change periodVector (parameterMap F p.1).1 n + p.2 =
        k • s p.1 + p.2
      rw [hn]

/-- The varying one-third-period twist used at the order-three elliptic piece. -/
@[expose] public noncomputable def orderThreeTwistSection
    (z : UpperHalfPlane) : ComplexTwoSpace :=
  (3 : ℂ)⁻¹ • periodVector (parameterMap F z).1 epsilon

/-- The varying one-quarter-period twist used at the order-four elliptic piece. -/
@[expose] public noncomputable def orderFourTwistSection
    (z : UpperHalfPlane) : ComplexTwoSpace :=
  (4 : ℂ)⁻¹ • periodVector (parameterMap F z).1 (-epsilon')

public theorem orderThreeTwistSection_nsmul (z : UpperHalfPlane) :
    3 • orderThreeTwistSection F z =
      periodVector (parameterMap F z).1 epsilon := by
  ext i
  simp [orderThreeTwistSection]

public theorem orderFourTwistSection_nsmul (z : UpperHalfPlane) :
    4 • orderFourTwistSection F z =
      periodVector (parameterMap F z).1 (-epsilon') := by
  ext i
  simp [orderFourTwistSection]

public theorem orderThreeFamilyTranslation_pow :
    familyTranslationEquiv F (orderThreeTwistSection F) ^ 3 = 1 :=
  familyTranslationEquiv_pow_eq_one F (orderThreeTwistSection F) 3
    fun z ↦ ⟨epsilon, orderThreeTwistSection_nsmul F z⟩

public theorem orderFourFamilyTranslation_pow :
    familyTranslationEquiv F (orderFourTwistSection F) ^ 4 = 1 :=
  familyTranslationEquiv_pow_eq_one F (orderFourTwistSection F) 4
    fun z ↦ ⟨-epsilon', orderFourTwistSection_nsmul F z⟩

public theorem orderThreeTwistSection_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ComplexTwoSpace) n
      (orderThreeTwistSection F) := by
  have hc : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun _ : UpperHalfPlane ↦ (3 : ℂ)⁻¹) := contMDiff_const
  exact hc.smul (periodSection_contMDiff F epsilon n)

public theorem orderFourTwistSection_contMDiff (n : WithTop ℕ∞) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ComplexTwoSpace) n
      (orderFourTwistSection F) := by
  have hc : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) n
      (fun _ : UpperHalfPlane ↦ (4 : ℂ)⁻¹) := contMDiff_const
  exact hc.smul (periodSection_contMDiff F (-epsilon') n)

public theorem familyTranslationCover_contMDiff
    (s : UpperHalfPlane → ComplexTwoSpace)
    (hs : ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n s) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (familyTranslationCover s) := by
  exact contMDiff_fst.prodMk ((hs.comp contMDiff_fst).add contMDiff_snd)

/-- Smooth fibre translations on the cover descend through the locally biholomorphic family
projection. -/
public theorem familyTranslationMap_contMDiff_of_projection_isLocalDiffeomorph
    (s : UpperHalfPlane → ComplexTwoSpace)
    (hs : ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ ComplexTwoSpace) n s)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n (familyTranslationMap F s) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    let π : UpperHalfPlane × ComplexTwoSpace → TotalSpace (parameterMap F) :=
      projection (parameterMap F)
    let loc := (hprojection p).localInverse
    have hlocal : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n loc (π p) :=
      (hprojection p).localInverse_contMDiffAt
    have hlocalp : loc (π p) = p :=
      (hprojection p).localInverse_left_inv (hprojection p).localInverse_mem_target
    have hcover : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n
        (familyTranslationCover s ∘ loc) (π p) :=
      (familyTranslationCover_contMDiff s hs).contMDiffAt.comp (π p) hlocal
    have hrhs : ContMDiffAt GlobalDeckTotalModel GlobalDeckTotalModel n
        (π ∘ familyTranslationCover s ∘ loc) (π p) :=
      (hprojection (familyTranslationCover s p)).contMDiffAt.comp_of_eq hcover (by
        simp [hlocalp])
    have hright := (hprojection p).localInverse_eventuallyEq_right
    have hevent : familyTranslationMap F s =ᶠ[nhds (π p)]
        (π ∘ familyTranslationCover s ∘ loc) := by
      filter_upwards [hright] with x hx
      calc
        familyTranslationMap F s x = familyTranslationMap F s (π (loc x)) :=
          congrArg _ hx.symm
        _ = π (familyTranslationCover s (loc x)) :=
          familyTranslationMap_mk F s (loc x)
    exact hrhs.congr_of_eventuallyEq hevent

/-- The first deck transport carries the varying one-third-period section to itself over the
transformed base. -/
public theorem periodTransport_orderThreeTwistSection (z : UpperHalfPlane) :
    periodTransport g₁ (parameterMap F z) (orderThreeTwistSection F z) =
      orderThreeTwistSection F (U.sourceAction g₁ • z) := by
  have hparam := parameterMap_equivariant F g₁
  rw [ParameterEquivariant.eq_def] at hparam
  rw [orderThreeTwistSection.eq_def, orderThreeTwistSection.eq_def,
    hparam z, rhoParameters_g₁_apply, periodTransport_gOne (parameterMap F z)]
  change rightOneLinearEquiv (parameterMap F z).1 (parameterMap F z).tau_ne_zero
      ((3 : ℂ)⁻¹ • periodVector (parameterMap F z).1 epsilon) =
    (3 : ℂ)⁻¹ • periodVector (transformOne (parameterMap F z).1) epsilon
  rw [map_smul, rightOneLinearEquiv_apply,
    ← generatorOne_periodVector (parameterMap F z).1
      (parameterMap F z).tau_ne_zero epsilon]
  congr 2
  rw [a₁_apply, A₁_epsilon]

/-- The second deck transport preserves the varying one-quarter-period section. -/
public theorem periodTransport_orderFourTwistSection (z : UpperHalfPlane) :
    periodTransport g₂ (parameterMap F z) (orderFourTwistSection F z) =
      orderFourTwistSection F (U.sourceAction g₂ • z) := by
  have hparam := parameterMap_equivariant F g₂
  rw [ParameterEquivariant.eq_def] at hparam
  rw [orderFourTwistSection.eq_def, orderFourTwistSection.eq_def,
    hparam z, rhoParameters_g₂_apply, periodTransport_gTwo (parameterMap F z)]
  change rightTwoLinearEquiv (parameterMap F z).1 (parameterMap F z).tau_ne_zero
      ((4 : ℂ)⁻¹ • periodVector (parameterMap F z).1 (-epsilon')) =
    (4 : ℂ)⁻¹ • periodVector (transformTwo (parameterMap F z).1) (-epsilon')
  rw [map_smul, rightTwoLinearEquiv_apply,
    ← generatorTwo_periodVector (parameterMap F z).1
      (parameterMap F z).tau_ne_zero (-epsilon')]
  congr 2
  rw [a₂_apply, Matrix.mulVec_neg, A₂_epsilon']

/-- The order-three affine generator lifted all the way to the vector-bundle cover.  Unlike the
descended finite cyclic action, its third power retains the accumulated integral period. -/
@[expose] public noncomputable def orderThreeAffineFamilyCoverGenerator :
    Equiv.Perm (UpperHalfPlane × ComplexTwoSpace) :=
  familyTranslationCoverEquiv (orderThreeTwistSection F) * deckEquiv F g₁

/-- The analogous order-four affine generator on the vector-bundle cover. -/
@[expose] public noncomputable def orderFourAffineFamilyCoverGenerator :
    Equiv.Perm (UpperHalfPlane × ComplexTwoSpace) :=
  familyTranslationCoverEquiv (orderFourTwistSection F) * deckEquiv F g₂

@[simp]
public theorem orderThreeAffineFamilyCoverGenerator_apply
    (p : UpperHalfPlane × ComplexTwoSpace) :
    orderThreeAffineFamilyCoverGenerator F p =
      (U.sourceAction g₁ • p.1,
        orderThreeTwistSection F (U.sourceAction g₁ • p.1) +
          periodTransport g₁ (parameterMap F p.1) p.2) :=
  rfl

@[simp]
public theorem orderFourAffineFamilyCoverGenerator_apply
    (p : UpperHalfPlane × ComplexTwoSpace) :
    orderFourAffineFamilyCoverGenerator F p =
      (U.sourceAction g₂ • p.1,
        orderFourTwistSection F (U.sourceAction g₂ • p.1) +
          periodTransport g₂ (parameterMap F p.1) p.2) :=
  rfl

/-- The lifted order-three affine generator is continuous before quotienting by the period
lattice. -/
public theorem orderThreeAffineFamilyCoverGenerator_continuous :
    Continuous (orderThreeAffineFamilyCoverGenerator F) := by
  change Continuous (fun p =>
    familyTranslationCover (orderThreeTwistSection F) (deckMap F g₁ p))
  exact (familyTranslationCover_contMDiff
      (orderThreeTwistSection F) (orderThreeTwistSection_contMDiff F 0)).continuous.comp
    (deckMap_contMDiff F g₁ 0).continuous

/-- The lifted order-four affine generator is likewise continuous. -/
public theorem orderFourAffineFamilyCoverGenerator_continuous :
    Continuous (orderFourAffineFamilyCoverGenerator F) := by
  change Continuous (fun p =>
    familyTranslationCover (orderFourTwistSection F) (deckMap F g₂ p))
  exact (familyTranslationCover_contMDiff
      (orderFourTwistSection F) (orderFourTwistSection_contMDiff F 0)).continuous.comp
    (deckMap_contMDiff F g₂ 0).continuous

/-- Three iterations of the lifted affine generator return to the original base and translate
the fibre by the exact period vector `epsilon`.  This is the universal-cover endpoint behind the
order-three van Kampen power relation. -/
public theorem orderThreeAffineFamilyCoverGenerator_pow_apply
    (p : UpperHalfPlane × ComplexTwoSpace) :
    (orderThreeAffineFamilyCoverGenerator F ^ 3) p =
      (p.1, periodVector (parameterMap F p.1).1 epsilon + p.2) := by
  let T := familyTranslationCoverEquiv (orderThreeTwistSection F)
  let D := deckEquiv F g₁
  have hcomm : Commute T D :=
    (deckEquiv_commutes_familyTranslationCoverEquiv F g₁
      (orderThreeTwistSection F) (periodTransport_orderThreeTwistSection F)).symm
  change ((T * D) ^ 3) p = _
  rw [hcomm.mul_pow]
  have hD : D ^ 3 = 1 := by
    change ((deckRepresentation F) g₁) ^ 3 = 1
    rw [← map_pow (deckRepresentation F) g₁, g₁_pow_three, map_one]
  rw [hD, mul_one, familyTranslationCoverEquiv_pow_apply,
    orderThreeTwistSection_nsmul]

/-- Four iterations of the lifted affine generator return to the original base and translate
the fibre by the exact period vector `-epsilon'`.  This is the universal-cover endpoint behind
the order-four van Kampen power relation. -/
public theorem orderFourAffineFamilyCoverGenerator_pow_apply
    (p : UpperHalfPlane × ComplexTwoSpace) :
    (orderFourAffineFamilyCoverGenerator F ^ 4) p =
      (p.1, periodVector (parameterMap F p.1).1 (-epsilon') + p.2) := by
  let T := familyTranslationCoverEquiv (orderFourTwistSection F)
  let D := deckEquiv F g₂
  have hcomm : Commute T D :=
    (deckEquiv_commutes_familyTranslationCoverEquiv F g₂
      (orderFourTwistSection F) (periodTransport_orderFourTwistSection F)).symm
  change ((T * D) ^ 4) p = _
  rw [hcomm.mul_pow]
  have hD : D ^ 4 = 1 := by
    change ((deckRepresentation F) g₂) ^ 4 = 1
    rw [← map_pow (deckRepresentation F) g₂, g₂_pow_four, map_one]
  rw [hD, mul_one, familyTranslationCoverEquiv_pow_apply,
    orderFourTwistSection_nsmul]

/-- A deck equivalence commutes with a fibre translation when its section is transported
naturally. -/
public theorem familyDeckEquiv_commutes_familyTranslationEquiv
    (g : Delta) (s : UpperHalfPlane → ComplexTwoSpace)
    (hnatural : ∀ z, periodTransport g (parameterMap F z) (s z) =
      s (U.sourceAction g • z)) :
    Commute (familyDeckEquiv F g) (familyTranslationEquiv F s) := by
  change familyDeckEquiv F g * familyTranslationEquiv F s =
    familyTranslationEquiv F s * familyDeckEquiv F g
  apply Equiv.ext
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    simp only [Equiv.Perm.mul_apply, familyDeckEquiv_apply,
      familyTranslationEquiv_apply, familyTranslationMap_mk, familyDeckMap_mk]
    apply congrArg (Quotient.mk _)
    apply Prod.ext
    · rfl
    · change periodTransport g (parameterMap F p.1) (s p.1 + p.2) =
        s (U.sourceAction g • p.1) +
          periodTransport g (parameterMap F p.1) p.2
      rw [map_add, hnatural]

/-- The affine generator on the actual varying order-three torus family. -/
@[expose] public noncomputable def orderThreeAffineFamilyGenerator :
    Equiv.Perm (TotalSpace (parameterMap F)) :=
  familyTranslationEquiv F (orderThreeTwistSection F) * familyDeckEquiv F g₁

/-- The affine generator on the actual varying order-four torus family. -/
@[expose] public noncomputable def orderFourAffineFamilyGenerator :
    Equiv.Perm (TotalSpace (parameterMap F)) :=
  familyTranslationEquiv F (orderFourTwistSection F) * familyDeckEquiv F g₂

public theorem orderThreeAffineFamilyGenerator_pow :
    orderThreeAffineFamilyGenerator F ^ 3 = 1 := by
  let T := familyTranslationEquiv F (orderThreeTwistSection F)
  let D := familyDeckEquiv F g₁
  have hcomm : Commute T D :=
    (familyDeckEquiv_commutes_familyTranslationEquiv F g₁
      (orderThreeTwistSection F) (periodTransport_orderThreeTwistSection F)).symm
  change (T * D) ^ 3 = 1
  rw [hcomm.mul_pow, orderThreeFamilyTranslation_pow]
  have hD : D ^ 3 = 1 := by
    change ((familyDeckRepresentation F) g₁) ^ 3 = 1
    rw [← map_pow (familyDeckRepresentation F) g₁, g₁_pow_three, map_one]
  rw [hD, mul_one]

public theorem orderFourAffineFamilyGenerator_pow :
    orderFourAffineFamilyGenerator F ^ 4 = 1 := by
  let T := familyTranslationEquiv F (orderFourTwistSection F)
  let D := familyDeckEquiv F g₂
  have hcomm : Commute T D :=
    (familyDeckEquiv_commutes_familyTranslationEquiv F g₂
      (orderFourTwistSection F) (periodTransport_orderFourTwistSection F)).symm
  change (T * D) ^ 4 = 1
  rw [hcomm.mul_pow, orderFourFamilyTranslation_pow]
  have hD : D ^ 4 = 1 := by
    change ((familyDeckRepresentation F) g₂) ^ 4 = 1
    rw [← map_pow (familyDeckRepresentation F) g₂, g₂_pow_four, map_one]
  rw [hD, mul_one]

/-- The direct affine cyclic action on the varying order-three family. -/
@[expose] public noncomputable def orderThreeAffineFamilyRepresentation :
    FiniteCyclic 3 →* Equiv.Perm (TotalSpace (parameterMap F)) :=
  cyclicRepresentation 3 (orderThreeAffineFamilyGenerator F)
    (orderThreeAffineFamilyGenerator_pow F)

/-- The direct affine cyclic action on the varying order-four family. -/
@[expose] public noncomputable def orderFourAffineFamilyRepresentation :
    FiniteCyclic 4 →* Equiv.Perm (TotalSpace (parameterMap F)) :=
  cyclicRepresentation 4 (orderFourAffineFamilyGenerator F)
    (orderFourAffineFamilyGenerator_pow F)

@[expose, instance_reducible] public noncomputable def orderThreeAffineFamilyAction :
    MulAction (FiniteCyclic 3) (TotalSpace (parameterMap F)) where
  smul g q := orderThreeAffineFamilyRepresentation F g q
  one_smul q := by
    change orderThreeAffineFamilyRepresentation F 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    change orderThreeAffineFamilyRepresentation F (g * h) q =
      orderThreeAffineFamilyRepresentation F g
        (orderThreeAffineFamilyRepresentation F h q)
    rw [map_mul]
    rfl

@[expose, instance_reducible] public noncomputable def orderFourAffineFamilyAction :
    MulAction (FiniteCyclic 4) (TotalSpace (parameterMap F)) where
  smul g q := orderFourAffineFamilyRepresentation F g q
  one_smul q := by
    change orderFourAffineFamilyRepresentation F 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    change orderFourAffineFamilyRepresentation F (g * h) q =
      orderFourAffineFamilyRepresentation F g
        (orderFourAffineFamilyRepresentation F h q)
    rw [map_mul]
    rfl

public theorem orderThreeAffineFamilyGenerator_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (orderThreeAffineFamilyGenerator F) := by
  exact (familyTranslationMap_contMDiff_of_projection_isLocalDiffeomorph F
    (orderThreeTwistSection F) (orderThreeTwistSection_contMDiff F n) hprojection).comp
      (familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph F n hprojection g₁)

public theorem orderFourAffineFamilyGenerator_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (orderFourAffineFamilyGenerator F) := by
  exact (familyTranslationMap_contMDiff_of_projection_isLocalDiffeomorph F
    (orderFourTwistSection F) (orderFourTwistSection_contMDiff F n) hprojection).comp
      (familyDeckMap_contMDiff_of_projection_isLocalDiffeomorph F n hprojection g₂)

public theorem orderThreeAffineFamilyRepresentation_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (g : FiniteCyclic 3) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (orderThreeAffineFamilyRepresentation F g) := by
  rw [cyclic_eq_generator_pow g, map_pow]
  change ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
    ((orderThreeAffineFamilyGenerator F) ^ (Multiplicative.toAdd g).val)
  simpa only [Equiv.Perm.iterate_eq_pow] using
    (orderThreeAffineFamilyGenerator_contMDiff F hprojection).iterate
      (Multiplicative.toAdd g).val

public theorem orderFourAffineFamilyRepresentation_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (g : FiniteCyclic 4) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (orderFourAffineFamilyRepresentation F g) := by
  rw [cyclic_eq_generator_pow g, map_pow]
  change ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
    ((orderFourAffineFamilyGenerator F) ^ (Multiplicative.toAdd g).val)
  simpa only [Equiv.Perm.iterate_eq_pow] using
    (orderFourAffineFamilyGenerator_contMDiff F hprojection).iterate
      (Multiplicative.toAdd g).val

/-- The fixed period torus over `z` embedded as the corresponding fibre of the varying family. -/
@[expose] public noncomputable def fixedFiberToFamily (z : UpperHalfPlane) :
    AdditiveTorus (parameterMap F z).1 → TotalSpace (parameterMap F) :=
  Quotient.map (fun v : ComplexTwoSpace ↦ (z, v)) fun a b h ↦ by
    change MulAction.orbitRel (PeriodGroup (parameterMap F z).1)
      ComplexTwoSpace a b at h
    change MulAction.orbitRel (FamilyPeriodGroup (parameterMap F))
      (UpperHalfPlane × ComplexTwoSpace) (z, a) (z, b)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨g, hg⟩ := h
    obtain ⟨v, hv⟩ := g.toAdd.2
    let G : FamilyPeriodGroup (parameterMap F) := Multiplicative.ofAdd v
    refine ⟨G, ?_⟩
    apply Prod.ext
    · rfl
    · change periodHom (parameterMap F z).1 v + b = a
      change g.toAdd.1 + b = a at hg
      rw [hv]
      exact hg

@[simp]
public theorem fixedFiberToFamily_mk (z : UpperHalfPlane) (v : ComplexTwoSpace) :
    fixedFiberToFamily F z (Quotient.mk _ v) = Quotient.mk _ (z, v) :=
  rfl

public theorem fixedFiberToFamily_injective (z : UpperHalfPlane) :
    Function.Injective (fixedFiberToFamily F z) := by
  intro q r hqr
  induction q using Quotient.inductionOn with
  | _ q =>
    induction r using Quotient.inductionOn with
    | _ r =>
      rw [fixedFiberToFamily_mk, fixedFiberToFamily_mk] at hqr
      rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqr ⊢
      obtain ⟨g, hg⟩ := hqr
      let v : periodLattice (parameterMap F z).1 :=
        ⟨periodVector (parameterMap F z).1 g.coeff, ⟨g.coeff, rfl⟩⟩
      refine ⟨Multiplicative.ofAdd v, ?_⟩
      change periodVector (parameterMap F z).1 g.coeff + r = q
      simpa only [family_smul_snd] using congrArg Prod.snd hg

@[simp]
public theorem familyTotalSpaceBase_fixedFiberToFamily
    (z : UpperHalfPlane) (q : AdditiveTorus (parameterMap F z).1) :
    familyTotalSpaceBase F (fixedFiberToFamily F z q) = z := by
  induction q using Quotient.inductionOn with
  | _ v => exact familyTotalSpaceBase_mk F (z, v)

public theorem familyTotalSpaceBase_familyTranslationMap
    (s : UpperHalfPlane → ComplexTwoSpace)
    (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (familyTranslationMap F s q) = familyTotalSpaceBase F q := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

public theorem familyTotalSpaceBase_familyDeckMap
    (g : Delta) (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (familyDeckMap F g q) =
      U.sourceAction g • familyTotalSpaceBase F q := by
  induction q using Quotient.inductionOn with
  | _ p => rfl

public theorem orderThreeGenerator_fixedFiber_intertwining
    (q : AdditiveTorus (parameterMap F U.zOne).1) :
    orderThreeAffineFamilyGenerator F (fixedFiberToFamily F U.zOne q) =
      fixedFiberToFamily F U.zOne
        (affineEquiv (orderThreeFiberAutomorphism F)
          (orderThreeTranslation (parameterMap F U.zOne).1) q) := by
  induction q using Quotient.inductionOn with
  | _ v =>
    rw [fixedFiberToFamily_mk]
    simp only [orderThreeAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
      familyDeckEquiv_apply, familyDeckMap_mk, deckMap.eq_def,
      familyTranslationEquiv_apply, familyTranslationMap_mk,
      familyTranslationCover.eq_def, affineEquiv_apply,
      orderThreeFiberAutomorphism_mk, orderThreeTranslation.eq_def,
      additiveTorusProjection.eq_def, orderThreeTwistSection.eq_def]
    rw [U.zOne_fixed, ← additiveTorus_mk_add, fixedFiberToFamily_mk]
    congr 2
    exact add_comm _ _

public theorem orderFourGenerator_fixedFiber_intertwining
    (q : AdditiveTorus (parameterMap F U.zTwo).1) :
    orderFourAffineFamilyGenerator F (fixedFiberToFamily F U.zTwo q) =
      fixedFiberToFamily F U.zTwo
        (affineEquiv (orderFourFiberAutomorphism F)
          (orderFourTranslation (parameterMap F U.zTwo).1) q) := by
  induction q using Quotient.inductionOn with
  | _ v =>
    rw [fixedFiberToFamily_mk]
    simp only [orderFourAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
      familyDeckEquiv_apply, familyDeckMap_mk, deckMap.eq_def,
      familyTranslationEquiv_apply, familyTranslationMap_mk,
      familyTranslationCover.eq_def, affineEquiv_apply,
      orderFourFiberAutomorphism_mk, orderFourTranslation.eq_def,
      additiveTorusProjection.eq_def, orderFourTwistSection.eq_def]
    rw [U.zTwo_fixed, ← additiveTorus_mk_add, fixedFiberToFamily_mk]
    congr 2
    exact add_comm _ _

public theorem orderThreeGenerator_pow_fixedFiber_intertwining
    (k : ℕ) (q : AdditiveTorus (parameterMap F U.zOne).1) :
    (orderThreeAffineFamilyGenerator F ^ k) (fixedFiberToFamily F U.zOne q) =
      fixedFiberToFamily F U.zOne
        ((affineEquiv (orderThreeFiberAutomorphism F)
          (orderThreeTranslation (parameterMap F U.zOne).1) ^ k) q) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ih]
    exact orderThreeGenerator_fixedFiber_intertwining F _

public theorem orderFourGenerator_pow_fixedFiber_intertwining
    (k : ℕ) (q : AdditiveTorus (parameterMap F U.zTwo).1) :
    (orderFourAffineFamilyGenerator F ^ k) (fixedFiberToFamily F U.zTwo q) =
      fixedFiberToFamily F U.zTwo
        ((affineEquiv (orderFourFiberAutomorphism F)
          (orderFourTranslation (parameterMap F U.zTwo).1) ^ k) q) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply, ih]
    exact orderFourGenerator_fixedFiber_intertwining F _

public theorem familyTotalSpaceBase_orderThreeGenerator
    (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (orderThreeAffineFamilyGenerator F q) =
      U.sourceAction g₁ • familyTotalSpaceBase F q := by
  rw [orderThreeAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
    familyTranslationEquiv_apply, familyTotalSpaceBase_familyTranslationMap,
    familyDeckEquiv_apply, familyTotalSpaceBase_familyDeckMap]

public theorem familyTotalSpaceBase_orderFourGenerator
    (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F (orderFourAffineFamilyGenerator F q) =
      U.sourceAction g₂ • familyTotalSpaceBase F q := by
  rw [orderFourAffineFamilyGenerator.eq_def, Equiv.Perm.mul_apply,
    familyTranslationEquiv_apply, familyTotalSpaceBase_familyTranslationMap,
    familyDeckEquiv_apply, familyTotalSpaceBase_familyDeckMap]

public theorem familyTotalSpaceBase_orderThreeGenerator_pow
    (k : ℕ) (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F ((orderThreeAffineFamilyGenerator F ^ k) q) =
      U.sourceAction (g₁ ^ k) • familyTotalSpaceBase F q := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, familyTotalSpaceBase_orderThreeGenerator, ih,
      map_pow, pow_succ']
    rw [← mul_smul, ← map_pow, ← map_mul]

public theorem familyTotalSpaceBase_orderFourGenerator_pow
    (k : ℕ) (q : TotalSpace (parameterMap F)) :
    familyTotalSpaceBase F ((orderFourAffineFamilyGenerator F ^ k) q) =
      U.sourceAction (g₂ ^ k) • familyTotalSpaceBase F q := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, familyTotalSpaceBase_orderFourGenerator, ih,
      map_pow, pow_succ']
    rw [← mul_smul, ← map_pow, ← map_mul]

public theorem exists_fixedFiberToFamily_of_base_eq
    {z : UpperHalfPlane} {q : TotalSpace (parameterMap F)}
    (hq : familyTotalSpaceBase F q = z) :
    ∃ x : AdditiveTorus (parameterMap F z).1, fixedFiberToFamily F z x = q := by
  induction q using Quotient.inductionOn with
  | _ p =>
    rcases p with ⟨w, v⟩
    change w = z at hq
    subst w
    exact ⟨Quotient.mk _ v, rfl⟩

public theorem orderThreeGenerator_pow_fixed_base
    (hsource : U.sourceAction = fuchsianSourceAction)
    (k : ℕ) (hk : 0 < k) (hkm : k < 3)
    {q : TotalSpace (parameterMap F)}
    (hq : (orderThreeAffineFamilyGenerator F ^ k) q = q) :
    familyTotalSpaceBase F q = U.zOne := by
  have hbase := congrArg (familyTotalSpaceBase F) hq
  rw [familyTotalSpaceBase_orderThreeGenerator_pow] at hbase
  have hzOne : U.zOne = fuchsianOneFixedPoint := by
    apply (SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_gOne_fixed_iff U.zOne).mp
    simpa only [← hsource] using U.zOne_fixed
  have hk_cases : k = 1 ∨ k = 2 := by omega
  rcases hk_cases with rfl | rfl
  · have hz :=
      (SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_gOne_fixed_iff
        (familyTotalSpaceBase F q)).mp (by simpa only [hsource, pow_one] using hbase)
    exact hz.trans hzOne.symm
  · have hz :=
      (SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_gOne_sq_fixed_iff
        (familyTotalSpaceBase F q)).mp (by simpa only [hsource] using hbase)
    exact hz.trans hzOne.symm

public theorem orderFourGenerator_pow_fixed_base
    (hsource : U.sourceAction = fuchsianSourceAction)
    (k : ℕ) (hk : 0 < k) (hkm : k < 4)
    {q : TotalSpace (parameterMap F)}
    (hq : (orderFourAffineFamilyGenerator F ^ k) q = q) :
    familyTotalSpaceBase F q = U.zTwo := by
  have hbase := congrArg (familyTotalSpaceBase F) hq
  rw [familyTotalSpaceBase_orderFourGenerator_pow] at hbase
  have hzTwo : U.zTwo = fuchsianTwoFixedPoint := by
    apply (SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_gTwo_fixed_iff U.zTwo).mp
    simpa only [← hsource] using U.zTwo_fixed
  have hk_cases : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk_cases with rfl | rfl | rfl
  · have hz :=
      (SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_gTwo_fixed_iff
        (familyTotalSpaceBase F q)).mp (by simpa only [hsource, pow_one] using hbase)
    exact hz.trans hzTwo.symm
  · have hz :=
      (SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_gTwo_sq_fixed_iff
        (familyTotalSpaceBase F q)).mp (by simpa only [hsource] using hbase)
    exact hz.trans hzTwo.symm
  · have hz :=
      (SphereSixComplex.TriangleGroup.FreeProductTorsion.fuchsianSourceAction_gTwo_cube_fixed_iff
        (familyTotalSpaceBase F q)).mp (by simpa only [hsource] using hbase)
    exact hz.trans hzTwo.symm

public theorem orderThreeAffineFamilyGenerator_pow_no_fixed
    (hsource : U.sourceAction = fuchsianSourceAction)
    (k : ℕ) (hk : 0 < k) (hkm : k < 3) :
    ¬ ∃ q : TotalSpace (parameterMap F),
      (orderThreeAffineFamilyGenerator F ^ k) q = q := by
  rintro ⟨q, hq⟩
  have hbase := orderThreeGenerator_pow_fixed_base F hsource k hk hkm hq
  obtain ⟨x, hx⟩ := exists_fixedFiberToFamily_of_base_eq F hbase
  subst q
  have hinter := orderThreeGenerator_pow_fixedFiber_intertwining F k x
  apply orderThree_affine_pow_no_fixed F k hk hkm
  refine ⟨x, fixedFiberToFamily_injective F U.zOne ?_⟩
  exact hinter.symm.trans hq

public theorem orderFourAffineFamilyGenerator_pow_no_fixed
    (hsource : U.sourceAction = fuchsianSourceAction)
    (k : ℕ) (hk : 0 < k) (hkm : k < 4) :
    ¬ ∃ q : TotalSpace (parameterMap F),
      (orderFourAffineFamilyGenerator F ^ k) q = q := by
  rintro ⟨q, hq⟩
  have hbase := orderFourGenerator_pow_fixed_base F hsource k hk hkm hq
  obtain ⟨x, hx⟩ := exists_fixedFiberToFamily_of_base_eq F hbase
  subst q
  have hinter := orderFourGenerator_pow_fixedFiber_intertwining F k x
  apply orderFour_affine_pow_no_fixed F k hk hkm
  refine ⟨x, fixedFiberToFamily_injective F U.zTwo ?_⟩
  exact hinter.symm.trans hq

public theorem orderThree_generator_pow_smul
    (k : ℕ) (q : TotalSpace (parameterMap F)) :
    letI := orderThreeAffineFamilyAction F
    cyclicGenerator 3 ^ k • q = (orderThreeAffineFamilyGenerator F ^ k) q := by
  change orderThreeAffineFamilyRepresentation F (cyclicGenerator 3 ^ k) q = _
  rw [map_pow]
  change ((cyclicRepresentation 3 (orderThreeAffineFamilyGenerator F)
    (orderThreeAffineFamilyGenerator_pow F)) (Multiplicative.ofAdd 1) ^ k) q = _
  rw [cyclicRepresentation_generator]

public theorem orderFour_generator_pow_smul
    (k : ℕ) (q : TotalSpace (parameterMap F)) :
    letI := orderFourAffineFamilyAction F
    cyclicGenerator 4 ^ k • q = (orderFourAffineFamilyGenerator F ^ k) q := by
  change orderFourAffineFamilyRepresentation F (cyclicGenerator 4 ^ k) q = _
  rw [map_pow]
  change ((cyclicRepresentation 4 (orderFourAffineFamilyGenerator F)
    (orderFourAffineFamilyGenerator_pow F)) (Multiplicative.ofAdd 1) ^ k) q = _
  rw [cyclicRepresentation_generator]

public theorem orderThreeAffineFamilyAction_free
    (hsource : U.sourceAction = fuchsianSourceAction) :
    letI := orderThreeAffineFamilyAction F
    IsCancelSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) := by
  let _ := orderThreeAffineFamilyAction F
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g q hq
  let k := (Multiplicative.toAdd g).val
  by_cases hk : k = 0
  · rw [cyclic_eq_generator_pow g, show (Multiplicative.toAdd g).val = k from rfl, hk,
      pow_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hklt : k < 3 := ZMod.val_lt _
    exfalso
    apply orderThreeAffineFamilyGenerator_pow_no_fixed F hsource k hkpos hklt
    refine ⟨q, ?_⟩
    rw [← orderThree_generator_pow_smul F]
    rwa [← cyclic_eq_generator_pow g]

public theorem orderFourAffineFamilyAction_free
    (hsource : U.sourceAction = fuchsianSourceAction) :
    letI := orderFourAffineFamilyAction F
    IsCancelSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) := by
  let _ := orderFourAffineFamilyAction F
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g q hq
  let k := (Multiplicative.toAdd g).val
  by_cases hk : k = 0
  · rw [cyclic_eq_generator_pow g, show (Multiplicative.toAdd g).val = k from rfl, hk,
      pow_zero]
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    have hklt : k < 4 := ZMod.val_lt _
    exfalso
    apply orderFourAffineFamilyGenerator_pow_no_fixed F hsource k hkpos hklt
    refine ⟨q, ?_⟩
    rw [← orderFour_generator_pow_smul F]
    rwa [← cyclic_eq_generator_pow g]

public theorem orderThreeAffineFamilyAction_properlyDiscontinuous :
    letI := orderThreeAffineFamilyAction F
    ProperlyDiscontinuousSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) := by
  let _ := orderThreeAffineFamilyAction F
  infer_instance

public theorem orderFourAffineFamilyAction_properlyDiscontinuous :
    letI := orderFourAffineFamilyAction F
    ProperlyDiscontinuousSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) := by
  let _ := orderFourAffineFamilyAction F
  infer_instance

/-- The order-three quotient of the varying torus family is a complex manifold, provided with
the canonical family manifold structure. -/
public theorem orderThreeVaryingFamilyQuotient_isManifold
    (hsource : U.sourceAction = fuchsianSourceAction)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    letI := orderThreeAffineFamilyAction F
    letI := orderThreeAffineFamilyAction_free F hsource
    letI := orderThreeAffineFamilyAction_properlyDiscontinuous F
    letI : ContinuousConstSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) :=
      ⟨fun g ↦ (orderThreeAffineFamilyRepresentation_contMDiff F hprojection g).continuous⟩
    IsManifold GlobalDeckTotalModel n
        (OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3)) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
        (quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3)) := by
  let _ := orderThreeAffineFamilyAction F
  let _ : IsCancelSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) :=
    orderThreeAffineFamilyAction_free F hsource
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) :=
    orderThreeAffineFamilyAction_properlyDiscontinuous F
  let _ : ContinuousConstSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) :=
    ⟨fun g ↦ (orderThreeAffineFamilyRepresentation_contMDiff F hprojection g).continuous⟩
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel n
      (orderThreeAffineFamilyRepresentation_contMDiff F hprojection)

/-- The analogous order-four finite quotient is a complex manifold with locally biholomorphic
quotient projection. -/
public theorem orderFourVaryingFamilyQuotient_isManifold
    (hsource : U.sourceAction = fuchsianSourceAction)
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    [T2Space (TotalSpace (parameterMap F))]
    [LocallyCompactSpace (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    letI := orderFourAffineFamilyAction F
    letI := orderFourAffineFamilyAction_free F hsource
    letI := orderFourAffineFamilyAction_properlyDiscontinuous F
    letI : ContinuousConstSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) :=
      ⟨fun g ↦ (orderFourAffineFamilyRepresentation_contMDiff F hprojection g).continuous⟩
    IsManifold GlobalDeckTotalModel n
        (OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4)) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
        (quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4)) := by
  let _ := orderFourAffineFamilyAction F
  let _ : IsCancelSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) :=
    orderFourAffineFamilyAction_free F hsource
  let _ : ProperlyDiscontinuousSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) :=
    orderFourAffineFamilyAction_properlyDiscontinuous F
  let _ : ContinuousConstSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) :=
    ⟨fun g ↦ (orderFourAffineFamilyRepresentation_contMDiff F hprojection g).continuous⟩
  exact orbitQuotient_isManifold_and_projection_isLocalDiffeomorph_of_contMDiff_smul
    GlobalDeckTotalModel n
      (orderFourAffineFamilyRepresentation_contMDiff F hprojection)

/-- Unconditional complex-manifold construction of the direct order-three varying-family
quotient.  The only geometric identification is that the source action is the explicit Fuchsian
one. -/
public theorem orderThreeVaryingFamilyQuotient_isManifold_actual
    (hsource : U.sourceAction = fuchsianSourceAction) :
    letI := familyIsCancelSMul (parameterMap F)
    letI := familyContinuousConstSMul (parameterMap F)
      fun a ↦ (periodSection_contMDiff F a ω).continuous
    letI := familyProperlyDiscontinuousSMul (parameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
        (parameterMap_compactUniformLowerBound F))
    letI : IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F)) :=
      (totalSpace_isManifold_and_projection_isLocalDiffeomorph F ω).1
    letI : LocallyCompactSpace (TotalSpace (parameterMap F)) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := orderThreeAffineFamilyAction F
    letI := orderThreeAffineFamilyAction_free F hsource
    letI := orderThreeAffineFamilyAction_properlyDiscontinuous F
    letI : ContinuousConstSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) :=
      ⟨fun g ↦ (orderThreeAffineFamilyRepresentation_contMDiff F
        (totalSpace_isManifold_and_projection_isLocalDiffeomorph F ω).2 g).continuous⟩
    IsManifold GlobalDeckTotalModel ω
        (OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3)) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
        (quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3)) := by
  let _ := familyIsCancelSMul (parameterMap F)
  let _ := familyContinuousConstSMul (parameterMap F)
    fun a ↦ (periodSection_contMDiff F a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
      (parameterMap_compactUniformLowerBound F))
  have htotal := totalSpace_isManifold_and_projection_isLocalDiffeomorph F ω
  let _ : IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F)) := htotal.1
  let _ : LocallyCompactSpace (TotalSpace (parameterMap F)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  exact orderThreeVaryingFamilyQuotient_isManifold F hsource htotal.2

/-- Unconditional complex-manifold construction of the direct order-four varying-family
quotient. -/
public theorem orderFourVaryingFamilyQuotient_isManifold_actual
    (hsource : U.sourceAction = fuchsianSourceAction) :
    letI := familyIsCancelSMul (parameterMap F)
    letI := familyContinuousConstSMul (parameterMap F)
      fun a ↦ (periodSection_contMDiff F a ω).continuous
    letI := familyProperlyDiscontinuousSMul (parameterMap F)
      (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
        (parameterMap_compactUniformLowerBound F))
    letI : IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F)) :=
      (totalSpace_isManifold_and_projection_isLocalDiffeomorph F ω).1
    letI : LocallyCompactSpace (TotalSpace (parameterMap F)) :=
      Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
    letI := orderFourAffineFamilyAction F
    letI := orderFourAffineFamilyAction_free F hsource
    letI := orderFourAffineFamilyAction_properlyDiscontinuous F
    letI : ContinuousConstSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) :=
      ⟨fun g ↦ (orderFourAffineFamilyRepresentation_contMDiff F
        (totalSpace_isManifold_and_projection_isLocalDiffeomorph F ω).2 g).continuous⟩
    IsManifold GlobalDeckTotalModel ω
        (OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4)) ∧
      IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel ω
        (quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4)) := by
  let _ := familyIsCancelSMul (parameterMap F)
  let _ := familyContinuousConstSMul (parameterMap F)
    fun a ↦ (periodSection_contMDiff F a ω).continuous
  let _ := familyProperlyDiscontinuousSMul (parameterMap F)
    (compactlyUniformPeriods_of_compactUniformLowerBound (parameterMap F)
      (parameterMap_compactUniformLowerBound F))
  have htotal := totalSpace_isManifold_and_projection_isLocalDiffeomorph F ω
  let _ : IsManifold GlobalDeckTotalModel ω (TotalSpace (parameterMap F)) := htotal.1
  let _ : LocallyCompactSpace (TotalSpace (parameterMap F)) :=
    Manifold.locallyCompact_of_finiteDimensional GlobalDeckTotalModel
  exact orderFourVaryingFamilyQuotient_isManifold F hsource htotal.2

public theorem familyTotalSpaceBase_continuous :
    Continuous (familyTotalSpaceBase F) :=
  continuous_quot_lift (familyTotalSpaceBase_respects F) continuous_fst

/-- Cayley radius on the actual varying family near the order-three elliptic fibre. -/
@[expose] public noncomputable def orderThreeFamilyRadius
    (q : TotalSpace (parameterMap F)) : ℝ :=
  ‖(orderThreeCayleyHomeomorph (familyTotalSpaceBase F q)).1‖

/-- Cayley radius on the actual varying family near the order-four elliptic fibre. -/
@[expose] public noncomputable def orderFourFamilyRadius
    (q : TotalSpace (parameterMap F)) : ℝ :=
  ‖(orderFourCayleyHomeomorph (familyTotalSpaceBase F q)).1‖

public theorem orderThreeFamilyRadius_continuous :
    Continuous (orderThreeFamilyRadius F) :=
  continuous_norm.comp
    (continuous_subtype_val.comp
      (orderThreeCayleyHomeomorph.continuous.comp (familyTotalSpaceBase_continuous F)))

public theorem orderFourFamilyRadius_continuous :
    Continuous (orderFourFamilyRadius F) :=
  continuous_norm.comp
    (continuous_subtype_val.comp
      (orderFourCayleyHomeomorph.continuous.comp (familyTotalSpaceBase_continuous F)))

/-- A closed order-three radial neighborhood strictly inside the Cayley disc is compact in the
full varying-torus family. -/
public theorem orderThreeFamilyRadius_le_isCompact
    {r : ℝ} (hr : r < 1) :
    IsCompact {q : TotalSpace (parameterMap F) | orderThreeFamilyRadius F q ≤ r} := by
  have hbase : IsCompact
      {z : UpperHalfPlane | ‖(orderThreeCayleyHomeomorph z).1‖ ≤ r} := by
    rw [orderThreeCayleyHomeomorph.eq_def]
    exact isCompact_cayleyClosedDisc fuchsianOneFixedPoint hr
  have hpreimage := (familyTotalSpaceBase_isProperMap F).isCompact_preimage hbase
  convert hpreimage using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, orderThreeFamilyRadius.eq_def]

/-- A closed order-four radial neighborhood strictly inside the Cayley disc is compact in the
full varying-torus family. -/
public theorem orderFourFamilyRadius_le_isCompact
    {r : ℝ} (hr : r < 1) :
    IsCompact {q : TotalSpace (parameterMap F) | orderFourFamilyRadius F q ≤ r} := by
  have hbase : IsCompact
      {z : UpperHalfPlane | ‖(orderFourCayleyHomeomorph z).1‖ ≤ r} := by
    rw [orderFourCayleyHomeomorph.eq_def]
    exact isCompact_cayleyClosedDisc fuchsianTwoFixedPoint hr
  have hpreimage := (familyTotalSpaceBase_isProperMap F).isCompact_preimage hbase
  convert hpreimage using 1
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, orderFourFamilyRadius.eq_def]

/-- Closed order-three collar annuli are compact as long as their outer radius stays inside the
unit Cayley disc. -/
public theorem orderThreeFamilyClosedAnnulus_isCompact
    (s : ℝ) {r : ℝ} (hr : r < 1) :
    IsCompact {q : TotalSpace (parameterMap F) |
      s ≤ orderThreeFamilyRadius F q ∧ orderThreeFamilyRadius F q ≤ r} := by
  have hclosed : IsClosed {q : TotalSpace (parameterMap F) |
      s ≤ orderThreeFamilyRadius F q} :=
    isClosed_Ici.preimage (orderThreeFamilyRadius_continuous F)
  have h := (orderThreeFamilyRadius_le_isCompact F hr).inter_right hclosed
  convert h using 1
  ext q
  simp [and_comm]

/-- Closed order-four collar annuli are compact as long as their outer radius stays inside the
unit Cayley disc. -/
public theorem orderFourFamilyClosedAnnulus_isCompact
    (s : ℝ) {r : ℝ} (hr : r < 1) :
    IsCompact {q : TotalSpace (parameterMap F) |
      s ≤ orderFourFamilyRadius F q ∧ orderFourFamilyRadius F q ≤ r} := by
  have hclosed : IsClosed {q : TotalSpace (parameterMap F) |
      s ≤ orderFourFamilyRadius F q} :=
    isClosed_Ici.preimage (orderFourFamilyRadius_continuous F)
  have h := (orderFourFamilyRadius_le_isCompact F hr).inter_right hclosed
  convert h using 1
  ext q
  simp [and_comm]

public theorem orderThreeFamilyRadius_generator
    (hsource : U.sourceAction = fuchsianSourceAction)
    (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F (orderThreeAffineFamilyGenerator F q) =
      orderThreeFamilyRadius F q := by
  rw [orderThreeFamilyRadius.eq_def, familyTotalSpaceBase_orderThreeGenerator,
    hsource, orderThreeCayleyHomeomorph_generator]
  change ‖orderThreeMultiplier *
    (orderThreeCayleyHomeomorph (familyTotalSpaceBase F q)).1‖ = _
  rw [norm_mul, norm_orderThreeMultiplier, one_mul]
  rfl

public theorem orderFourFamilyRadius_generator
    (hsource : U.sourceAction = fuchsianSourceAction)
    (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F (orderFourAffineFamilyGenerator F q) =
      orderFourFamilyRadius F q := by
  rw [orderFourFamilyRadius.eq_def, familyTotalSpaceBase_orderFourGenerator,
    hsource, orderFourCayleyHomeomorph_generator]
  change ‖orderFourMultiplier *
    (orderFourCayleyHomeomorph (familyTotalSpaceBase F q)).1‖ = _
  rw [norm_mul, norm_orderFourMultiplier, one_mul]
  rfl

public theorem orderThreeFamilyRadius_generator_pow
    (hsource : U.sourceAction = fuchsianSourceAction)
    (k : ℕ) (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F ((orderThreeAffineFamilyGenerator F ^ k) q) =
      orderThreeFamilyRadius F q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, orderThreeFamilyRadius_generator F hsource, ih]

public theorem orderFourFamilyRadius_generator_pow
    (hsource : U.sourceAction = fuchsianSourceAction)
    (k : ℕ) (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F ((orderFourAffineFamilyGenerator F ^ k) q) =
      orderFourFamilyRadius F q := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, orderFourFamilyRadius_generator F hsource, ih]

public theorem orderThreeFamilyRadius_representation
    (hsource : U.sourceAction = fuchsianSourceAction)
    (g : FiniteCyclic 3) (q : TotalSpace (parameterMap F)) :
    orderThreeFamilyRadius F (orderThreeAffineFamilyRepresentation F g q) =
      orderThreeFamilyRadius F q := by
  rw [cyclic_eq_generator_pow g, map_pow]
  exact orderThreeFamilyRadius_generator_pow F hsource _ q

public theorem orderFourFamilyRadius_representation
    (hsource : U.sourceAction = fuchsianSourceAction)
    (g : FiniteCyclic 4) (q : TotalSpace (parameterMap F)) :
    orderFourFamilyRadius F (orderFourAffineFamilyRepresentation F g q) =
      orderFourFamilyRadius F q := by
  rw [cyclic_eq_generator_pow g, map_pow]
  exact orderFourFamilyRadius_generator_pow F hsource _ q

/-- The punctured radial collar in the varying order-three family. -/
@[expose] public def orderThreePuncturedFamilyCollar (r : ℝ) :
    Set (TotalSpace (parameterMap F)) :=
  {q | 0 < orderThreeFamilyRadius F q ∧ orderThreeFamilyRadius F q < r}

/-- The punctured radial collar in the varying order-four family. -/
@[expose] public def orderFourPuncturedFamilyCollar (r : ℝ) :
    Set (TotalSpace (parameterMap F)) :=
  {q | 0 < orderFourFamilyRadius F q ∧ orderFourFamilyRadius F q < r}

public theorem orderThreePuncturedFamilyCollar_isOpen (r : ℝ) :
    IsOpen (orderThreePuncturedFamilyCollar F r) :=
  (isOpen_lt continuous_const (orderThreeFamilyRadius_continuous F)).inter
    (isOpen_lt (orderThreeFamilyRadius_continuous F) continuous_const)

public theorem orderFourPuncturedFamilyCollar_isOpen (r : ℝ) :
    IsOpen (orderFourPuncturedFamilyCollar F r) :=
  (isOpen_lt continuous_const (orderFourFamilyRadius_continuous F)).inter
    (isOpen_lt (orderFourFamilyRadius_continuous F) continuous_const)

public theorem orderThreePuncturedFamilyCollar_invariant
    (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (g : FiniteCyclic 3) (q : TotalSpace (parameterMap F)) :
    orderThreeAffineFamilyRepresentation F g q ∈ orderThreePuncturedFamilyCollar F r ↔
      q ∈ orderThreePuncturedFamilyCollar F r := by
  simp only [orderThreePuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
    orderThreeFamilyRadius_representation F hsource]

public theorem orderFourPuncturedFamilyCollar_invariant
    (hsource : U.sourceAction = fuchsianSourceAction)
    (r : ℝ) (g : FiniteCyclic 4) (q : TotalSpace (parameterMap F)) :
    orderFourAffineFamilyRepresentation F g q ∈ orderFourPuncturedFamilyCollar F r ↔
      q ∈ orderFourPuncturedFamilyCollar F r := by
  simp only [orderFourPuncturedFamilyCollar.eq_def, Set.mem_ofPred_eq,
    orderFourFamilyRadius_representation F hsource]

/-- The image of the punctured order-three collar in its direct finite quotient. -/
@[expose] public noncomputable def orderThreePuncturedCollarQuotientRegion (r : ℝ) :
    letI := orderThreeAffineFamilyAction F
    Set (OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3)) := by
  let _ := orderThreeAffineFamilyAction F
  exact quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3) ''
    orderThreePuncturedFamilyCollar F r

/-- The image of the punctured order-four collar in its direct finite quotient. -/
@[expose] public noncomputable def orderFourPuncturedCollarQuotientRegion (r : ℝ) :
    letI := orderFourAffineFamilyAction F
    Set (OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4)) := by
  let _ := orderFourAffineFamilyAction F
  exact quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4) ''
    orderFourPuncturedFamilyCollar F r

public theorem orderThreePuncturedCollarQuotientRegion_isOpen
    (r : ℝ)
    (hcontinuous : letI := orderThreeAffineFamilyAction F
      ContinuousConstSMul (FiniteCyclic 3) (TotalSpace (parameterMap F))) :
    letI := orderThreeAffineFamilyAction F
    IsOpen (orderThreePuncturedCollarQuotientRegion F r) := by
  let _ := orderThreeAffineFamilyAction F
  let _ : ContinuousConstSMul (FiniteCyclic 3) (TotalSpace (parameterMap F)) := hcontinuous
  exact isOpenMap_quotient_mk'_mul _ (orderThreePuncturedFamilyCollar_isOpen F r)

public theorem orderFourPuncturedCollarQuotientRegion_isOpen
    (r : ℝ)
    (hcontinuous : letI := orderFourAffineFamilyAction F
      ContinuousConstSMul (FiniteCyclic 4) (TotalSpace (parameterMap F))) :
    letI := orderFourAffineFamilyAction F
    IsOpen (orderFourPuncturedCollarQuotientRegion F r) := by
  let _ := orderFourAffineFamilyAction F
  let _ : ContinuousConstSMul (FiniteCyclic 4) (TotalSpace (parameterMap F)) := hcontinuous
  exact isOpenMap_quotient_mk'_mul _ (orderFourPuncturedFamilyCollar_isOpen F r)

/-- The open quotient region has precisely the punctured order-three collar as its preimage. -/
public theorem orderThreePuncturedCollarQuotientRegion_preimage
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := orderThreeAffineFamilyAction F
    quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3) ⁻¹'
        orderThreePuncturedCollarQuotientRegion F r =
      orderThreePuncturedFamilyCollar F r := by
  let _ := orderThreeAffineFamilyAction F
  ext q
  constructor
  · rintro ⟨x, hx, heq⟩
    change Quotient.mk _ x = Quotient.mk _ q at heq
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at heq
    obtain ⟨g, hg⟩ := heq
    apply (orderThreePuncturedFamilyCollar_invariant F hsource r g q).mp
    change orderThreeAffineFamilyRepresentation F g q = x at hg
    rw [hg]
    exact hx
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- The open quotient region has precisely the punctured order-four collar as its preimage. -/
public theorem orderFourPuncturedCollarQuotientRegion_preimage
    (hsource : U.sourceAction = fuchsianSourceAction) (r : ℝ) :
    letI := orderFourAffineFamilyAction F
    quotientProjection (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4) ⁻¹'
        orderFourPuncturedCollarQuotientRegion F r =
      orderFourPuncturedFamilyCollar F r := by
  let _ := orderFourAffineFamilyAction F
  ext q
  constructor
  · rintro ⟨x, hx, heq⟩
    change Quotient.mk _ x = Quotient.mk _ q at heq
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at heq
    obtain ⟨g, hg⟩ := heq
    apply (orderFourPuncturedFamilyCollar_invariant F hsource r g q).mp
    change orderFourAffineFamilyRepresentation F g q = x at hg
    rw [hg]
    exact hx
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- The honest affine action of the full free-product triangle group.  It is obtained by the
universal property of `C₃ ∗ C₄`, not by modifying the existing linear deck action. -/
@[expose] public noncomputable def affineGlobalFamilyRepresentation :
    Delta →* Equiv.Perm (TotalSpace (parameterMap F)) :=
  Monoid.Coprod.lift (orderThreeAffineFamilyRepresentation F)
    (orderFourAffineFamilyRepresentation F)

@[simp]
public theorem affineGlobalFamilyRepresentation_inl (a : CyclicThree) :
    affineGlobalFamilyRepresentation F (Monoid.Coprod.inl a) =
      orderThreeAffineFamilyRepresentation F a :=
  rfl

@[simp]
public theorem affineGlobalFamilyRepresentation_inr (a : CyclicFour) :
    affineGlobalFamilyRepresentation F (Monoid.Coprod.inr a) =
      orderFourAffineFamilyRepresentation F a :=
  rfl

public theorem affineGlobalFamilyRepresentation_contMDiff
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) (g : Delta) :
    ContMDiff GlobalDeckTotalModel GlobalDeckTotalModel n
      (affineGlobalFamilyRepresentation F g) := by
  induction g using Monoid.Coprod.induction_on with
  | inl a =>
      rw [affineGlobalFamilyRepresentation_inl]
      exact orderThreeAffineFamilyRepresentation_contMDiff F hprojection a
  | inr a =>
      rw [affineGlobalFamilyRepresentation_inr]
      exact orderFourAffineFamilyRepresentation_contMDiff F hprojection a
  | mul g h hg hh =>
      rw [map_mul]
      exact hg.comp hh

@[expose, instance_reducible] public noncomputable def affineGlobalFamilyAction :
    MulAction Delta (TotalSpace (parameterMap F)) where
  smul g q := affineGlobalFamilyRepresentation F g q
  one_smul q := by
    change affineGlobalFamilyRepresentation F 1 q = q
    rw [map_one]
    rfl
  mul_smul g h q := by
    change affineGlobalFamilyRepresentation F (g * h) q =
      affineGlobalFamilyRepresentation F g (affineGlobalFamilyRepresentation F h q)
    rw [map_mul]
    rfl

public theorem affineGlobalFamilyAction_continuousConstSmul
    [ChartedSpace (ModelProd ℂ ComplexTwoSpace) (TotalSpace (parameterMap F))]
    [IsManifold GlobalDeckTotalModel n (TotalSpace (parameterMap F))]
    (hprojection : IsLocalDiffeomorph GlobalDeckTotalModel GlobalDeckTotalModel n
      (projection (parameterMap F))) :
    letI := affineGlobalFamilyAction F
    ContinuousConstSMul Delta (TotalSpace (parameterMap F)) := by
  let _ := affineGlobalFamilyAction F
  exact ⟨fun g ↦ (affineGlobalFamilyRepresentation_contMDiff F hprojection g).continuous⟩

/-- The full affine varying-family quotient, distinct from the previously constructed linear
deck quotient. -/
public abbrev AffineGlobalFamilyQuotient :=
  letI := affineGlobalFamilyAction F
  OrbitQuotient (M := TotalSpace (parameterMap F)) (G := Delta)

/-- The order-three finite quotient maps canonically to the full affine free-product quotient. -/
@[expose] public noncomputable def orderThreeFiniteToAffineGlobalQuotient :
    letI := orderThreeAffineFamilyAction F
    OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 3) →
      AffineGlobalFamilyQuotient F := by
  let _ := orderThreeAffineFamilyAction F
  let _ := affineGlobalFamilyAction F
  exact Quotient.map id fun q x h ↦ by
    change MulAction.orbitRel (FiniteCyclic 3) (TotalSpace (parameterMap F)) q x at h
    change MulAction.orbitRel Delta (TotalSpace (parameterMap F)) q x
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨Monoid.Coprod.inl a, ?_⟩
    change affineGlobalFamilyRepresentation F (Monoid.Coprod.inl a) x = q
    rw [affineGlobalFamilyRepresentation_inl]
    exact ha

/-- The order-four finite quotient maps canonically to the full affine free-product quotient. -/
@[expose] public noncomputable def orderFourFiniteToAffineGlobalQuotient :
    letI := orderFourAffineFamilyAction F
    OrbitQuotient (M := TotalSpace (parameterMap F)) (G := FiniteCyclic 4) →
      AffineGlobalFamilyQuotient F := by
  let _ := orderFourAffineFamilyAction F
  let _ := affineGlobalFamilyAction F
  exact Quotient.map id fun q x h ↦ by
    change MulAction.orbitRel (FiniteCyclic 4) (TotalSpace (parameterMap F)) q x at h
    change MulAction.orbitRel Delta (TotalSpace (parameterMap F)) q x
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨a, ha⟩ := h
    refine ⟨Monoid.Coprod.inr a, ?_⟩
    change affineGlobalFamilyRepresentation F (Monoid.Coprod.inr a) x = q
    rw [affineGlobalFamilyRepresentation_inr]
    exact ha

@[simp]
public theorem orderThreeFiniteToAffineGlobalQuotient_mk
    (q : TotalSpace (parameterMap F)) :
    letI := orderThreeAffineFamilyAction F
    orderThreeFiniteToAffineGlobalQuotient F (Quotient.mk _ q) =
      (letI := affineGlobalFamilyAction F; Quotient.mk _ q) :=
  by
    rw [orderThreeFiniteToAffineGlobalQuotient.eq_def]
    rfl

@[simp]
public theorem orderFourFiniteToAffineGlobalQuotient_mk
    (q : TotalSpace (parameterMap F)) :
    letI := orderFourAffineFamilyAction F
    orderFourFiniteToAffineGlobalQuotient F (Quotient.mk _ q) =
      (letI := affineGlobalFamilyAction F; Quotient.mk _ q) :=
  by
    rw [orderFourFiniteToAffineGlobalQuotient.eq_def]
    rfl

/-- Exact remaining small-neighborhood theorem at the order-three point.  It says that two
points of the punctured Cayley collar can be related by the full affine triangle action only by
an element of the order-three factor. -/
@[expose] public def OrderThreeAffineCollarOrbitSeparation (r : ℝ) : Prop :=
  ∀ q ∈ orderThreePuncturedFamilyCollar F r,
    ∀ x ∈ orderThreePuncturedFamilyCollar F r,
      ∀ g : Delta, affineGlobalFamilyRepresentation F g x = q →
        ∃ a : CyclicThree, g = Monoid.Coprod.inl a

/-- Exact remaining small-neighborhood theorem at the order-four point. -/
@[expose] public def OrderFourAffineCollarOrbitSeparation (r : ℝ) : Prop :=
  ∀ q ∈ orderFourPuncturedFamilyCollar F r,
    ∀ x ∈ orderFourPuncturedFamilyCollar F r,
      ∀ g : Delta, affineGlobalFamilyRepresentation F g x = q →
        ∃ a : CyclicFour, g = Monoid.Coprod.inr a

/-- The exact remaining order-three geometric existence theorem: a positive punctured Cayley
collar on which full affine orbits are separated by the order-three factor.  The general slice
theorem `exists_open_stabilizer_slice` supplies the open-slice part once proper discontinuity and
the central stabilizer calculation are installed. -/
@[expose] public def OrderThreeSmallAffineCollarOrbitSeparation : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ OrderThreeAffineCollarOrbitSeparation F r

/-- The analogous exact order-four small-collar theorem. -/
@[expose] public def OrderFourSmallAffineCollarOrbitSeparation : Prop :=
  ∃ r : ℝ, 0 < r ∧ r < 1 ∧ OrderFourAffineCollarOrbitSeparation F r

/-- Orbit separation is exactly enough to make the order-three collar inject into the full
affine quotient. -/
public theorem orderThreeFiniteToAffineGlobalQuotient_injOn_collar
    (hsep : OrderThreeAffineCollarOrbitSeparation F r) :
    letI := orderThreeAffineFamilyAction F
    Set.InjOn (orderThreeFiniteToAffineGlobalQuotient F)
      (orderThreePuncturedCollarQuotientRegion F r) := by
  let _ := orderThreeAffineFamilyAction F
  let _ := affineGlobalFamilyAction F
  intro Q hQ R hR hQR
  rcases hQ with ⟨q, hq, rfl⟩
  rcases hR with ⟨x, hx, rfl⟩
  change Quotient.mk _ q = Quotient.mk _ x at hQR
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hQR
  obtain ⟨g, hg⟩ := hQR
  obtain ⟨a, rfl⟩ := hsep q hq x hx g hg
  apply Quotient.sound
  change MulAction.orbitRel (FiniteCyclic 3) (TotalSpace (parameterMap F)) q x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨a, ?_⟩
  change orderThreeAffineFamilyRepresentation F a x = q
  change affineGlobalFamilyRepresentation F (Monoid.Coprod.inl a) x = q at hg
  rw [affineGlobalFamilyRepresentation_inl] at hg
  exact hg

/-- Orbit separation is exactly enough to make the order-four collar inject into the full
affine quotient. -/
public theorem orderFourFiniteToAffineGlobalQuotient_injOn_collar
    (hsep : OrderFourAffineCollarOrbitSeparation F r) :
    letI := orderFourAffineFamilyAction F
    Set.InjOn (orderFourFiniteToAffineGlobalQuotient F)
      (orderFourPuncturedCollarQuotientRegion F r) := by
  let _ := orderFourAffineFamilyAction F
  let _ := affineGlobalFamilyAction F
  intro Q hQ R hR hQR
  rcases hQ with ⟨q, hq, rfl⟩
  rcases hR with ⟨x, hx, rfl⟩
  change Quotient.mk _ q = Quotient.mk _ x at hQR
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hQR
  obtain ⟨g, hg⟩ := hQR
  obtain ⟨a, rfl⟩ := hsep q hq x hx g hg
  apply Quotient.sound
  change MulAction.orbitRel (FiniteCyclic 4) (TotalSpace (parameterMap F)) q x
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨a, ?_⟩
  change orderFourAffineFamilyRepresentation F a x = q
  change affineGlobalFamilyRepresentation F (Monoid.Coprod.inr a) x = q at hg
  rw [affineGlobalFamilyRepresentation_inr] at hg
  exact hg

/-- A proved small-neighborhood theorem selects an actual positive order-three collar whose
finite quotient injects into the affine global quotient. -/
public theorem exists_orderThree_injective_affine_collar
    (hsep : OrderThreeSmallAffineCollarOrbitSeparation F) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (letI := orderThreeAffineFamilyAction F;
        Set.InjOn (orderThreeFiniteToAffineGlobalQuotient F)
          (orderThreePuncturedCollarQuotientRegion F r)) := by
  obtain ⟨r, hr, hr1, hsep⟩ := hsep
  exact ⟨r, hr, hr1, orderThreeFiniteToAffineGlobalQuotient_injOn_collar F hsep⟩

/-- A proved small-neighborhood theorem selects an actual positive order-four collar whose
finite quotient injects into the affine global quotient. -/
public theorem exists_orderFour_injective_affine_collar
    (hsep : OrderFourSmallAffineCollarOrbitSeparation F) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      (letI := orderFourAffineFamilyAction F;
        Set.InjOn (orderFourFiniteToAffineGlobalQuotient F)
          (orderFourPuncturedCollarQuotientRegion F r)) := by
  obtain ⟨r, hr, hr1, hsep⟩ := hsep
  exact ⟨r, hr, hr1, orderFourFiniteToAffineGlobalQuotient_injOn_collar F hsep⟩

end

end SphereSixComplex.Geometry.EllipticVaryingFamilyQuotient
