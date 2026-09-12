module

public import SphereSixComplex.Paper.Topology.StandardInfiniteA2PolarPhaseDeck

/-!
# Established phase spreading for the standard infinite `A₂` toric model

This boundary records only the standard toric orbit, deck, and stabilizer compatibility package.
It contains no quotient retraction, homology, Euler-characteristic, or global paper conclusion.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.Geometry.InfiniteA2Toric

open SphereSixComplex.Periods
open SphereSixComplex.Geometry.CuspFilling
open SphereSixComplex.Geometry.CuspLocalPhaseAction
open SphereSixComplex.Geometry.CuspPeriodExpansion
open SphereSixComplex.Geometry.CuspStraighteningRetraction
open SphereSixComplex.Geometry.CuspStraightening
open SphereSixComplex.Geometry.CuspToricPhaseAction

/-- The positive real complex unit with the same norm as a given complex unit. -/
public def positiveRadialPart (z : ℂˣ) : ℂˣ :=
  Units.mk0 (‖(z : ℂ)‖ : ℂ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero z)))

public theorem positiveRadialPart_re (z : ℂˣ) :
    0 < ((positiveRadialPart z : ℂˣ) : ℂ).re := by
  change 0 < ‖(z : ℂ)‖
  exact norm_pos_iff.mpr (Units.ne_zero z)

public theorem positiveRadialPart_im (z : ℂˣ) :
    ((positiveRadialPart z : ℂˣ) : ℂ).im = 0 := by
  rfl

public theorem norm_positiveRadialPart (z : ℂˣ) :
    ‖((positiveRadialPart z : ℂˣ) : ℂ)‖ = ‖(z : ℂ)‖ := by
  change ‖(‖(z : ℂ)‖ : ℂ)‖ = ‖(z : ℂ)‖
  exact Complex.norm_of_nonneg (norm_nonneg _)

public theorem positiveRadialPart_mul (z w : ℂˣ) :
    positiveRadialPart (z * w) = positiveRadialPart z * positiveRadialPart w := by
  apply Units.ext
  simp [positiveRadialPart]

/-- The coordinatewise positive radial part of the normalized frozen cusp multiplier. -/
public def normalizedCuspPositiveTwist
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) :
    ParameterLattice → DenseTorus :=
  fun lambda i ↦ positiveRadialPart
    (phaseEmbedding (N.phaseCoefficient lambda 0) i)

@[simp]
public theorem normalizedCuspPositiveTwist_zero
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) :
    normalizedCuspPositiveTwist N 0 = 1 := by
  funext i
  simp [normalizedCuspPositiveTwist, positiveRadialPart]

public theorem normalizedCuspPositiveTwist_add
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda mu : ParameterLattice) :
    normalizedCuspPositiveTwist N (lambda + mu) =
      normalizedCuspPositiveTwist N lambda * normalizedCuspPositiveTwist N mu := by
  funext i
  change positiveRadialPart (phaseEmbedding (N.phaseCoefficient (lambda + mu) 0) i) =
    positiveRadialPart (phaseEmbedding (N.phaseCoefficient lambda 0) i) *
      positiveRadialPart (phaseEmbedding (N.phaseCoefficient mu 0) i)
  rw [N.phaseCoefficient_add, map_mul, Pi.mul_apply, positiveRadialPart_mul]

@[simp]
public theorem normalizedCuspPositiveTwist_last
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) :
    normalizedCuspPositiveTwist N lambda 2 = 1 := by
  apply Units.ext
  simp [normalizedCuspPositiveTwist, positiveRadialPart]

public theorem normalizedCuspPositiveTwist_real
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) (i : Fin 3) :
    0 < ((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ).re ∧
      ((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ).im = 0 :=
  ⟨positiveRadialPart_re _, positiveRadialPart_im _⟩

/-- The canonical positive twist has exactly the frozen cusp multiplier's radial norm. -/
public theorem norm_normalizedCuspPositiveTwist
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda : ParameterLattice) (i : Fin 3) :
    ‖((normalizedCuspPositiveTwist N lambda i : ℂˣ) : ℂ)‖ =
      ‖((phaseEmbedding (N.phaseCoefficient lambda 0) i : ℂˣ) : ℂ)‖ :=
  norm_positiveRadialPart _

/-- Fan shear fixes the canonical positive twist because its height coordinate is one. -/
public theorem denseTorusShear_normalizedCuspPositiveTwist
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (lambda mu : ParameterLattice) :
    denseTorusShear lambda (normalizedCuspPositiveTwist N mu) =
      normalizedCuspPositiveTwist N mu := by
  ext i
  fin_cases i <;>
    simp [denseTorusShear, normalizedCuspPositiveTwist_last]

/-- The canonical positive deck formula on the ambient toric carrier. -/
public def normalizedPositiveDeckCarrierMap
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model)
    (lambda : ParameterLattice) (p : M.Carrier) : M.Carrier :=
  M.torusAction (normalizedCuspPositiveTwist N lambda)
    (Additive.toMul (M.fanShear lambda) p)

@[simp]
public theorem normalizedPositiveDeckCarrierMap_zero
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (p : M.Carrier) :
    normalizedPositiveDeckCarrierMap N M 0 p = p := by
  simp [normalizedPositiveDeckCarrierMap, normalizedCuspPositiveTwist_zero]

public theorem normalizedPositiveDeckCarrierMap_add
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model)
    (lambda mu : ParameterLattice) (p : M.Carrier) :
    normalizedPositiveDeckCarrierMap N M (lambda + mu) p =
      normalizedPositiveDeckCarrierMap N M lambda
        (normalizedPositiveDeckCarrierMap N M mu p) := by
  simp only [normalizedPositiveDeckCarrierMap, map_add, normalizedCuspPositiveTwist_add]
  rw [fanShear_torusAction, denseTorusShear_normalizedCuspPositiveTwist]
  simp

/-- The canonical positive deck formula restricted to a height sublevel. -/
public def normalizedPositiveDeckLocalMap
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ)
    (lambda : ParameterLattice) (p : localCarrier M r) : localCarrier M r :=
  ⟨normalizedPositiveDeckCarrierMap N M lambda (p : M.Carrier), by
    change M.t (normalizedPositiveDeckCarrierMap N M lambda (p : M.Carrier)) ∈ Metric.ball 0 r
    rw [normalizedPositiveDeckCarrierMap, M.t_torusAction,
      normalizedCuspPositiveTwist_last]
    simp only [Units.val_one, one_mul]
    rw [M.fanShear_preserves_t]
    exact p.property⟩

/-- The compact phase-orbit map is proper.  The positive part is closed because its modulus map
is a retraction, and the orbit map factors through the compact-torus action homeomorphism
followed by projection away from the compact torus. -/
public theorem compactPhaseOrbit_isProper
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) :
    IsProperMap (compactPhaseOrbit M r P.positivePart) := by
  let J := continuous_torusAction M
  let localAction : CompactTorus × localCarrier M r → localCarrier M r :=
    fun z ↦ ⟨M.torusAction (compactTorusEmbedding z.1) z.2, by
      change M.t (M.torusAction (compactTorusEmbedding z.1) z.2) ∈ Metric.ball 0 r
      rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
      change ‖(z.1 2 : ℂ)‖ * ‖M.t z.2‖ < r
      rw [Circle.norm_coe, one_mul]
      simpa only [dist_zero_right] using Metric.mem_ball.mp z.2.property⟩
  have hlocalAction : Continuous localAction := by
    rw [continuous_induced_rng]
    exact J.comp ((continuous_compactTorusEmbedding.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))
  let localActionInv : CompactTorus × localCarrier M r → localCarrier M r :=
    fun z ↦ ⟨M.torusAction (compactTorusEmbedding z.1)⁻¹ z.2, by
      change M.t (M.torusAction (compactTorusEmbedding z.1)⁻¹ z.2) ∈ Metric.ball 0 r
      rw [Metric.mem_ball, dist_zero_right, M.t_torusAction, norm_mul]
      rw [show ‖((((compactTorusEmbedding z.1)⁻¹ 2 : ℂˣ) : ℂ))‖ = 1 by
        rw [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv]
        change ‖(z.1 2 : ℂ)‖⁻¹ = 1
        rw [Circle.norm_coe, inv_one], one_mul]
      simpa only [dist_zero_right] using Metric.mem_ball.mp z.2.property⟩
  have hlocalActionInv : Continuous localActionInv := by
    rw [continuous_induced_rng]
    exact J.comp ((continuous_inv.comp
        (continuous_compactTorusEmbedding.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  let actionHomeomorph : CompactTorus × localCarrier M r ≃ₜ
      CompactTorus × localCarrier M r := {
    toFun := fun z ↦ (z.1, localAction z)
    invFun := fun z ↦ (z.1, localActionInv z)
    left_inv := by
      intro z
      ext <;> simp [localAction, localActionInv]
    right_inv := by
      intro z
      ext <;> simp [localAction, localActionInv]
    continuous_toFun := continuous_fst.prodMk hlocalAction
    continuous_invFun := continuous_fst.prodMk hlocalActionInv }
  have hclosed : IsClosed P.positivePart := by
    have hrange : P.positivePart =
        Set.range (fun q : P.positivePart ↦ (q : localCarrier M r)) := by
      ext x
      simp
    rw [hrange]
    exact (show Function.LeftInverse P.modulus
      (fun q : P.positivePart ↦ (q : localCarrier M r)) from P.modulus_fixed).isClosed_range
        P.modulus.continuous continuous_subtype_val
  have hinclusion : Topology.IsClosedEmbedding
      (fun z : CompactTorus × P.positivePart ↦
        (z.1, (z.2 : localCarrier M r))) := by
    exact Topology.IsClosedEmbedding.id.prodMap
      hclosed.isClosedEmbedding_subtypeVal
  have hj : IsProperMap (fun z : CompactTorus × P.positivePart ↦
      actionHomeomorph (z.1, (z.2 : localCarrier M r))) :=
    actionHomeomorph.isProperMap.comp hinclusion.isProperMap
  have hproper : IsProperMap (fun z : CompactTorus × P.positivePart ↦
      (actionHomeomorph (z.1, (z.2 : localCarrier M r))).2) :=
    isProperMap_snd_of_compactSpace.comp hj
  convert hproper using 1
  funext z
  apply Subtype.ext
  rfl

/-- The polar decomposition already proves surjectivity of the compact phase orbit map. -/
public theorem compactPhaseOrbit_surjective
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) :
    Function.Surjective (compactPhaseOrbit M r P.positivePart) := by
  intro p
  obtain ⟨phi, hphi⟩ := P.polar_surjective p
  refine ⟨(phi, P.modulus p), ?_⟩
  apply Subtype.ext
  exact hphi

/-- Properness and polar surjectivity give the exact product quotient map used to descend the
phase-spread homotopy. -/
public theorem compactPhaseOrbit_prod_isQuotientMap
    (M : Model) (r : ℝ) (P : PolarHoneycombData M r) :
    Topology.IsQuotientMap
      (Prod.map (id : unitInterval → unitInterval)
        (compactPhaseOrbit M r P.positivePart)) := by
  have hproper : IsProperMap
      (Prod.map (id : unitInterval → unitInterval)
        (compactPhaseOrbit M r P.positivePart)) :=
    isProperMap_id.prodMap (compactPhaseOrbit_isProper M r P)
  exact hproper.isClosedMap.isQuotientMap hproper.continuous
    (Function.Surjective.prodMap Function.surjective_id
      (compactPhaseOrbit_surjective M r P))



/-- The genuinely independent input for a polar honeycomb.  Positivity of the height on the
positive part follows from the modulus identities, while contractibility of the central
honeycomb follows from its displayed Euclidean homeomorphism. -/
public structure PolarHoneycombConstructionData (M : Model) (r : ℝ) where
  positivePart : Set (localCarrier M r)
  modulus : C(localCarrier M r, positivePart)
  modulus_fixed : ∀ q : positivePart, modulus q = q
  modulus_t : ∀ p, M.t (modulus p) = (‖M.t p‖ : ℝ)
  polar_surjective : ∀ p : localCarrier M r, ∃ phi : CompactTorus,
    M.torusAction (compactTorusEmbedding phi) (modulus p) = p
  central : Set positivePart
  central_eq : central = {q : positivePart | M.t (q : localCarrier M r) = 0}
  honeycomb : (Fin 2 → ℝ) ≃ₜ central
  positiveTwist : ParameterLattice → DenseTorus
  positiveTwist_zero : positiveTwist 0 = 1
  positiveTwist_add : ∀ lambda mu,
    positiveTwist (lambda + mu) = positiveTwist lambda * positiveTwist mu
  positiveTwist_last : ∀ lambda, positiveTwist lambda 2 = 1
  positiveTwist_real : ∀ lambda i,
    0 < ((positiveTwist lambda i : ℂˣ) : ℂ).re ∧
      ((positiveTwist lambda i : ℂˣ) : ℂ).im = 0
  positiveDeckAction : MulAction (Multiplicative ParameterLattice) positivePart
  positiveDeck_coe : ∀ lambda q,
    ((((Multiplicative.ofAdd lambda) • q : positivePart) : localCarrier M r) : M.Carrier) =
      M.torusAction (positiveTwist lambda)
        (Additive.toMul (M.fanShear lambda) (q : M.Carrier))
  quotientCovering :
    letI := positiveDeckAction
    IsQuotientCoveringMap
      (PolarHoneycombData.orbitProjection positivePart)
      (Multiplicative ParameterLattice)
  positive_contractible : ContractibleSpace positivePart
  quotient_relativeCW :
    letI := positiveDeckAction
    Topology.RelCWComplex
      (Set.univ : Set (PolarHoneycombData.OrbitQuotient positivePart))
      (PolarHoneycombData.orbitCore central)
  quotient_t2 :
    letI := positiveDeckAction
    T2Space (PolarHoneycombData.OrbitQuotient positivePart)

/-- The displayed formula for the deck action makes each deck transformation continuous. -/
public theorem PolarHoneycombConstructionData.positiveDeckContinuous
    {M : Model} {r : ℝ} (Q : PolarHoneycombConstructionData M r) :
    letI := Q.positiveDeckAction
    ContinuousConstSMul (Multiplicative ParameterLattice) Q.positivePart := by
  let _ := Q.positiveDeckAction
  constructor
  intro g
  rw [continuous_induced_rng, continuous_induced_rng]
  let lambda := Multiplicative.toAdd g
  have heq :
      (fun q : Q.positivePart ↦
        ((((g • q : Q.positivePart) : localCarrier M r)) : M.Carrier)) =
      fun q : Q.positivePart ↦ M.torusAction (Q.positiveTwist lambda)
        (Additive.toMul (M.fanShear lambda) (q : M.Carrier)) := by
    funext q
    simpa [lambda] using Q.positiveDeck_coe lambda q
  change Continuous (fun q : Q.positivePart ↦
    ((((g • q : Q.positivePart) : localCarrier M r)) : M.Carrier))
  rw [heq]
  exact (M.torusAction_holomorphic (Q.positiveTwist lambda)).continuous.comp
    ((M.fanShear_holomorphic lambda).continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val))

/-- The central honeycomb is saturated under the deck action because the action preserves the
height coordinate. -/
public theorem PolarHoneycombConstructionData.central_preimage
    {M : Model} {r : ℝ} (Q : PolarHoneycombConstructionData M r) :
    letI := Q.positiveDeckAction
    PolarHoneycombData.orbitProjection Q.positivePart ⁻¹'
        PolarHoneycombData.orbitCore Q.central = Q.central := by
  let _ := Q.positiveDeckAction
  have hmem (lambda : ParameterLattice) (q : Q.positivePart) :
      (Multiplicative.ofAdd lambda) • q ∈ Q.central ↔ q ∈ Q.central := by
    rw [Q.central_eq]
    change M.t ((((Multiplicative.ofAdd lambda) • q : Q.positivePart) :
      localCarrier M r)) = 0 ↔ M.t (q : localCarrier M r) = 0
    rw [Q.positiveDeck_coe, M.t_torusAction, Q.positiveTwist_last,
      M.fanShear_preserves_t]
    simp
  ext q
  constructor
  · rintro ⟨c, hc, hqc⟩
    change Quotient.mk _ c = Quotient.mk _ q at hqc
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hqc
    obtain ⟨g, hg⟩ := hqc
    rw [← hg] at hc
    simpa using (hmem (Multiplicative.toAdd g) q).mp hc
  · intro hq
    exact ⟨q, hq, rfl⟩

/-- Assemble the full interface, deriving its four redundant geometric fields. -/
public noncomputable def PolarHoneycombConstructionData.toPolarHoneycombData
    {M : Model} {r : ℝ} (Q : PolarHoneycombConstructionData M r) :
    PolarHoneycombData M r where
  positivePart := Q.positivePart
  modulus := Q.modulus
  modulus_fixed := Q.modulus_fixed
  positive_t := by
    intro q
    have h := Q.modulus_t (q : localCarrier M r)
    rw [Q.modulus_fixed q] at h
    rw [h]
    exact ⟨by simp, norm_nonneg _⟩
  modulus_t := Q.modulus_t
  polar_surjective := Q.polar_surjective
  central := Q.central
  central_eq := Q.central_eq
  honeycomb := Q.honeycomb
  positiveTwist := Q.positiveTwist
  positiveTwist_zero := Q.positiveTwist_zero
  positiveTwist_add := Q.positiveTwist_add
  positiveTwist_last := Q.positiveTwist_last
  positiveTwist_real := Q.positiveTwist_real
  positiveDeckAction := Q.positiveDeckAction
  positiveDeck_coe := Q.positiveDeck_coe
  positiveDeckContinuous := Q.positiveDeckContinuous
  quotientCovering := Q.quotientCovering
  central_preimage := Q.central_preimage
  positive_contractible := Q.positive_contractible
  central_contractible := Q.honeycomb.symm.contractibleSpace
  quotient_relativeCW := Q.quotient_relativeCW
  quotient_t2 := Q.quotient_t2

/-- The canonical positive deck action on any positive part preserved by the ambient formula. -/
@[instance_reducible] public def normalizedPositiveDeckAction
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) {r : ℝ}
    (positivePart : Set (localCarrier M r))
    (positiveDeck_mem : ∀ lambda (q : positivePart),
      normalizedPositiveDeckLocalMap N M r lambda (q : localCarrier M r) ∈ positivePart) :
    MulAction (Multiplicative ParameterLattice) positivePart where
  smul g q :=
    ⟨normalizedPositiveDeckLocalMap N M r (Multiplicative.toAdd g) q,
      positiveDeck_mem (Multiplicative.toAdd g) q⟩
  one_smul q := by
    apply Subtype.ext
    change normalizedPositiveDeckLocalMap N M r 0 (q : localCarrier M r) =
      (q : localCarrier M r)
    exact Subtype.ext (normalizedPositiveDeckCarrierMap_zero N M (q : M.Carrier))
  mul_smul g h q := by
    apply Subtype.ext
    change normalizedPositiveDeckLocalMap N M r
        (Multiplicative.toAdd (g * h)) (q : localCarrier M r) =
      normalizedPositiveDeckLocalMap N M r (Multiplicative.toAdd g)
        (normalizedPositiveDeckLocalMap N M r (Multiplicative.toAdd h)
          (q : localCarrier M r))
    apply Subtype.ext
    change normalizedPositiveDeckCarrierMap N M
        (Multiplicative.toAdd g + Multiplicative.toAdd h) (q : M.Carrier) =
      normalizedPositiveDeckCarrierMap N M (Multiplicative.toAdd g)
        (normalizedPositiveDeckCarrierMap N M (Multiplicative.toAdd h) (q : M.Carrier))
    exact normalizedPositiveDeckCarrierMap_add N M
      (Multiplicative.toAdd g) (Multiplicative.toAdd h) (q : M.Carrier)

/-- The narrowed geometric residue.  The positive twist and deck action are now canonical;
only preservation of the positive part and the genuinely global quotient properties remain. -/
public structure NormalizedPolarHoneycombConstructionData
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    (N : NormalizedFuchsianCuspCoordinate E D) (M : Model) (r : ℝ) where
  positivePart : Set (localCarrier M r)
  modulus : C(localCarrier M r, positivePart)
  modulus_fixed : ∀ q : positivePart, modulus q = q
  modulus_t : ∀ p, M.t (modulus p) = (‖M.t p‖ : ℝ)
  polar_surjective : ∀ p : localCarrier M r, ∃ phi : CompactTorus,
    M.torusAction (compactTorusEmbedding phi) (modulus p) = p
  honeycomb : (Fin 2 → ℝ) ≃ₜ {q : positivePart | M.t (q : localCarrier M r) = 0}
  positiveDeck_mem : ∀ lambda (q : positivePart),
    normalizedPositiveDeckLocalMap N M r lambda (q : localCarrier M r) ∈ positivePart
  quotientCovering :
    letI := normalizedPositiveDeckAction N M positivePart positiveDeck_mem
    IsQuotientCoveringMap
      (PolarHoneycombData.orbitProjection positivePart)
      (Multiplicative ParameterLattice)
  positive_contractible : ContractibleSpace positivePart
  quotient_relativeCW :
    letI := normalizedPositiveDeckAction N M positivePart positiveDeck_mem
    Topology.RelCWComplex
      (Set.univ : Set (PolarHoneycombData.OrbitQuotient positivePart))
      (PolarHoneycombData.orbitCore
        {q : positivePart | M.t (q : localCarrier M r) = 0})
  quotient_t2 :
    letI := normalizedPositiveDeckAction N M positivePart positiveDeck_mem
    T2Space (PolarHoneycombData.OrbitQuotient positivePart)

/-- The central honeycomb is canonically the zero locus of the height coordinate. -/
public def NormalizedPolarHoneycombConstructionData.central
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r) : Set Q.positivePart :=
  {q : Q.positivePart | M.t (q : localCarrier M r) = 0}

/-- Build the previous construction interface from the normalized geometric residue. -/
public noncomputable def
    NormalizedPolarHoneycombConstructionData.toPolarHoneycombConstructionData
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r) :
    PolarHoneycombConstructionData M r where
  positivePart := Q.positivePart
  modulus := Q.modulus
  modulus_fixed := Q.modulus_fixed
  modulus_t := Q.modulus_t
  polar_surjective := Q.polar_surjective
  central := Q.central
  central_eq := rfl
  honeycomb := Q.honeycomb
  positiveTwist := normalizedCuspPositiveTwist N
  positiveTwist_zero := normalizedCuspPositiveTwist_zero N
  positiveTwist_add := normalizedCuspPositiveTwist_add N
  positiveTwist_last := normalizedCuspPositiveTwist_last N
  positiveTwist_real := normalizedCuspPositiveTwist_real N
  positiveDeckAction :=
    normalizedPositiveDeckAction N M Q.positivePart Q.positiveDeck_mem
  positiveDeck_coe := by
    intro lambda q
    change ((((normalizedPositiveDeckAction N M Q.positivePart Q.positiveDeck_mem).smul
        (Multiplicative.ofAdd lambda) q : Q.positivePart) : localCarrier M r) : M.Carrier) =
      M.torusAction (normalizedCuspPositiveTwist N lambda)
        (Additive.toMul (M.fanShear lambda) (q : M.Carrier))
    rfl
  quotientCovering := Q.quotientCovering
  positive_contractible := Q.positive_contractible
  quotient_relativeCW := Q.quotient_relativeCW
  quotient_t2 := Q.quotient_t2

/-- The full polar-honeycomb datum determined by normalized construction data. -/
public noncomputable def NormalizedPolarHoneycombConstructionData.toPolarHoneycombData
    {E : FuchsianModularLift} {D : FuchsianPeriodLocalData E}
    {N : NormalizedFuchsianCuspCoordinate E D} {M : Model} {r : ℝ}
    (Q : NormalizedPolarHoneycombConstructionData N M r) :
    PolarHoneycombData M r :=
  Q.toPolarHoneycombConstructionData.toPolarHoneycombData


end SphereSixComplex.Geometry.InfiniteA2Toric
