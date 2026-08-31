/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import SphereSixComplex.Geometry.StandardInfiniteA2ToricCarrierGeometryAssembly
public import SphereSixComplex.Topology.StandardInfiniteA2PositiveRetraction

/-!
# Polar modulus on the constructed infinite `A₂` toric carrier

This module descends coordinatewise complex modulus through the Laurent gluing of the explicit
carrier.  It proves the height, compact-phase, and polar-surjectivity formulas directly in the
constructed affine charts.
-/

@[expose] public section

noncomputable section

open Function Set Topology

namespace SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction

open SphereSixComplex.Geometry.StandardInfiniteA2ToricModel

/-- Coordinatewise complex modulus, regarded again as a complex affine coordinate. -/
public def coordinateModulus (z : RawCoordinates) : RawCoordinates :=
  fun i ↦ (‖z i‖ : ℂ)

public theorem coordinateModulus_continuous : Continuous coordinateModulus := by
  exact continuous_pi fun i ↦ Complex.continuous_ofReal.comp (continuous_apply i).norm

@[simp]
public theorem coordinateModulus_idempotent (z : RawCoordinates) :
    coordinateModulus (coordinateModulus z) = coordinateModulus z := by
  funext i
  simp [coordinateModulus]

/-- The nonnegative real locus in one affine chart. -/
public def nonnegativeCoordinates : Set RawCoordinates :=
  {z | ∃ u : Fin 3 → ℝ, (∀ i, 0 ≤ u i) ∧ z = fun i ↦ (u i : ℂ)}

public theorem coordinateModulus_eq_self_iff (z : RawCoordinates) :
    coordinateModulus z = z ↔ z ∈ nonnegativeCoordinates := by
  constructor
  · intro hz
    exact ⟨fun i ↦ ‖z i‖, fun i ↦ norm_nonneg _, hz.symm⟩
  · rintro ⟨u, hu, rfl⟩
    funext i
    exact congrArg Complex.ofReal (Complex.norm_of_nonneg (hu i))

@[simp]
public theorem coordinateModulus_mem_monomialDomain_iff
    (A : Matrix (Fin 3) (Fin 3) ℤ) (z : RawCoordinates) :
    coordinateModulus z ∈ monomialDomain A ↔ z ∈ monomialDomain A := by
  simp [monomialDomain, coordinateModulus]

public theorem monomial_coordinateModulus
    (A : Matrix (Fin 3) (Fin 3) ℤ) (z : RawCoordinates) :
    monomial A (coordinateModulus z) = coordinateModulus (monomial A z) := by
  funext i
  simp [monomial, coordinateModulus, norm_prod, norm_zpow]

public theorem coordinateModulus_mul (z w : RawCoordinates) :
    coordinateModulus (z * w) = coordinateModulus z * coordinateModulus w := by
  funext i
  simp [coordinateModulus]

public theorem chartChange_coordinateModulus (a b : ChartIndex) (z : RawCoordinates) :
    chartChange a b (coordinateModulus z) = coordinateModulus (chartChange a b z) :=
  monomial_coordinateModulus (transitionMatrix a b) z

/-- Coordinatewise modulus descended to the glued carrier. -/
public noncomputable def carrierModulus (x : Carrier) : Carrier :=
  inclusion (preferredChart x) (coordinateModulus (preferredCoordinates x))

@[simp]
public theorem carrierModulus_inclusion (a : ChartIndex) (z : RawCoordinates) :
    carrierModulus (inclusion a z) = inclusion a (coordinateModulus z) := by
  let b := preferredChart (inclusion a z)
  let w := preferredCoordinates (inclusion a z)
  have he : inclusion b w = inclusion a z := inclusion_preferredCoordinates _
  have hchange := (inclusion_eq_iff b a w z).mp he
  apply (inclusion_eq_iff b a _ _).mpr
  refine ⟨?_, ?_⟩
  · rw [chartChange_source] at hchange ⊢
    exact (coordinateModulus_mem_monomialDomain_iff _ _).mpr hchange.1
  · rw [chartChange_coordinateModulus, hchange.2]

public theorem carrierModulus_continuous : Continuous carrierModulus := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  apply
    ((parametrization a).continuousAt_iff_continuousAt_comp_right
      (show inclusion a z ∈ (parametrization a).target by simp)).mpr
  have h : carrierModulus ∘ parametrization a = inclusion a ∘ coordinateModulus := by
    funext w
    exact carrierModulus_inclusion a w
  rw [h]
  exact ((inclusion_isOpenEmbedding a).continuous.comp coordinateModulus_continuous).continuousAt

@[simp]
public theorem carrierModulus_idempotent (x : Carrier) :
    carrierModulus (carrierModulus x) = carrierModulus x := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  simp only [carrierModulus_inclusion, coordinateModulus_idempotent]

/-- The global nonnegative locus, defined as the fixed-point set of the polar modulus. -/
public def carrierPositivePart : Set Carrier :=
  {x | carrierModulus x = x}

public theorem carrierPositivePart_isClosed : IsClosed carrierPositivePart := by
  let _ : T2Space Carrier := t2Space
  exact isClosed_eq carrierModulus_continuous continuous_id

@[simp]
public theorem carrierModulus_mem_positivePart (x : Carrier) :
    carrierModulus x ∈ carrierPositivePart :=
  carrierModulus_idempotent x

@[simp]
public theorem inclusion_mem_carrierPositivePart_iff (a : ChartIndex) (z : RawCoordinates) :
    inclusion a z ∈ carrierPositivePart ↔ z ∈ nonnegativeCoordinates := by
  change carrierModulus (inclusion a z) = inclusion a z ↔ _
  rw [carrierModulus_inclusion, (inclusion_isOpenEmbedding a).injective.eq_iff,
    coordinateModulus_eq_self_iff]

@[simp]
public theorem carrierHeight_modulus (x : Carrier) :
    carrierHeight (carrierModulus x) = (‖carrierHeight x‖ : ℂ) := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  rw [carrierModulus_inclusion, carrierHeight_inclusion, carrierHeight_inclusion]
  simp [rawHeight, coordinateModulus]

/-- Coordinatewise modulus on the intrinsic dense algebraic torus. -/
public def denseTorusModulus (g : DenseTorus) : DenseTorus :=
  fun i ↦ Units.mk0 (‖(g i : ℂ)‖ : ℂ) (by
    simpa only [Complex.ofReal_ne_zero, norm_ne_zero_iff] using Units.ne_zero (g i))

public theorem denseRawCoordinates_modulus (g : DenseTorus) :
    denseRawCoordinates (denseTorusModulus g) = coordinateModulus (denseRawCoordinates g) :=
  rfl

public theorem denseTorusModulus_eq_self_of_positive (g : DenseTorus)
    (hg : ∀ i, 0 < (g i : ℂ).re ∧ (g i : ℂ).im = 0) :
    denseTorusModulus g = g := by
  funext i
  apply Units.ext
  change (‖(g i : ℂ)‖ : ℂ) = (g i : ℂ)
  have hreal : (g i : ℂ) = ((g i : ℂ).re : ℂ) :=
    Complex.ext rfl (hg i).2
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hg i).1]

public theorem torusChartCoordinates_denseTorusModulus (a : ChartIndex) (g : DenseTorus) :
    torusChartCoordinates a (denseTorusModulus g) =
      coordinateModulus (torusChartCoordinates a g) := by
  change monomial (dualMatrix a) (denseRawCoordinates (denseTorusModulus g)) =
    coordinateModulus (monomial (dualMatrix a) (denseRawCoordinates g))
  rw [denseRawCoordinates_modulus, monomial_coordinateModulus]

public theorem carrierModulus_torusAction (g : DenseTorus) (x : Carrier) :
    carrierModulus (carrierTorusAction g x) =
      carrierTorusAction (denseTorusModulus g) (carrierModulus x) := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  change carrierModulus (carrierTorusActionFun g (inclusion a z)) =
    carrierTorusActionFun (denseTorusModulus g) (carrierModulus (inclusion a z))
  rw [carrierTorusActionFun_inclusion, carrierModulus_inclusion,
    carrierModulus_inclusion, carrierTorusActionFun_inclusion,
    torusChartCoordinates_denseTorusModulus, ← coordinateModulus_mul]

public theorem carrierModulus_fanShear
    (lambda : CuspFilling.ParameterLattice) (x : Carrier) :
    carrierModulus (carrierFanShearFun lambda x) =
      carrierFanShearFun lambda (carrierModulus x) := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  rw [carrierFanShearFun_inclusion, carrierModulus_inclusion,
    carrierModulus_inclusion, carrierFanShearFun_inclusion]

public theorem carrierPositivePart_torusAction_fanShear
    (g : DenseTorus) (hg : ∀ i, 0 < (g i : ℂ).re ∧ (g i : ℂ).im = 0)
    (lambda : CuspFilling.ParameterLattice) {x : Carrier} (hx : x ∈ carrierPositivePart) :
    carrierTorusAction g (carrierFanShearFun lambda x) ∈ carrierPositivePart := by
  change carrierModulus (carrierTorusAction g (carrierFanShearFun lambda x)) =
    carrierTorusAction g (carrierFanShearFun lambda x)
  rw [carrierModulus_torusAction, denseTorusModulus_eq_self_of_positive g hg,
    carrierModulus_fanShear, hx]

public theorem torusChartCoordinates_compactTorus_norm
    (a : ChartIndex) (phi : CompactTorus) (i : Fin 3) :
    ‖torusChartCoordinates a (compactTorusEmbedding phi) i‖ = 1 := by
  simp [torusChartCoordinates, monomial, denseRawCoordinates, compactTorusEmbedding,
    norm_prod, norm_zpow, Circle.norm_coe]

public theorem coordinateModulus_compactTorus_mul
    (a : ChartIndex) (phi : CompactTorus) (z : RawCoordinates) :
    coordinateModulus (torusChartCoordinates a (compactTorusEmbedding phi) * z) =
      coordinateModulus z := by
  funext i
  simp [coordinateModulus, torusChartCoordinates_compactTorus_norm]

@[simp]
public theorem carrierModulus_compactTorusAction (phi : CompactTorus) (x : Carrier) :
    carrierModulus (carrierTorusAction (compactTorusEmbedding phi) x) = carrierModulus x := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  change carrierModulus
      (carrierTorusActionFun (compactTorusEmbedding phi) (inclusion a z)) =
    carrierModulus (inclusion a z)
  rw [carrierTorusActionFun_inclusion, carrierModulus_inclusion,
    carrierModulus_inclusion, coordinateModulus_compactTorus_mul]

public theorem exists_compactTorus_chart_mul_modulus (a : ChartIndex) (z : RawCoordinates) :
    ∃ phi : CompactTorus,
      torusChartCoordinates a (compactTorusEmbedding phi) * coordinateModulus z = z := by
  have hphase (c : ℂ) : ∃ w : ℂ, ‖w‖ = 1 ∧ w * (‖c‖ : ℂ) = c := by
    by_cases hc : c = 0
    · exact ⟨1, norm_one, by simp [hc]⟩
    · refine ⟨c / (‖c‖ : ℂ), ?_, ?_⟩
      · rw [norm_div, Complex.norm_real, norm_norm,
          div_self (norm_ne_zero_iff.mpr hc)]
      · exact div_mul_cancel₀ _
          (by simpa only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero] using hc)
  choose w hw hmul using fun i ↦ hphase (z i)
  have hw0 : w ∈ coordinateTorus := by
    intro i hi
    have h := hw i
    rw [hi, norm_zero] at h
    exact zero_ne_one h
  let rawIntrinsic := monomial (a2ConeMatrix a.1 a.2) w
  have hrawIntrinsic : rawIntrinsic ∈ coordinateTorus :=
    monomial_mapsTo_coordinateTorus _ hw0
  let g := denseTorusOfCoordinateTorus rawIntrinsic hrawIntrinsic
  have hchart : torusChartCoordinates a g = w := by
    change monomial (dualMatrix a) (denseRawCoordinates g) = w
    rw [denseRawCoordinates_denseTorusOfCoordinateTorus]
    change monomial (dualMatrix a) (monomial (a2ConeMatrix a.1 a.2) w) = w
    rw [monomial_comp_on_coordinateTorus _ _ hw0, dualMatrix_mul_coneMatrix, monomial_one]
  have hg (i : Fin 3) : ‖(g i : ℂ)‖ = 1 := by
    change ‖rawIntrinsic i‖ = 1
    simp [rawIntrinsic, monomial, norm_prod, norm_zpow, hw]
  let phi : CompactTorus := fun i ↦
    ⟨(g i : ℂ), mem_sphere_zero_iff_norm.mpr (hg i)⟩
  refine ⟨phi, ?_⟩
  have hphi : compactTorusEmbedding phi = g := by
    funext i
    apply Units.ext
    rfl
  rw [hphi, hchart]
  funext i
  exact hmul i

public theorem exists_compactTorusAction_modulus (x : Carrier) :
    ∃ phi : CompactTorus,
      carrierTorusAction (compactTorusEmbedding phi) (carrierModulus x) = x := by
  obtain ⟨a, z, rfl⟩ := inclusion_jointly_surjective x
  obtain ⟨phi, hphi⟩ := exists_compactTorus_chart_mul_modulus a z
  refine ⟨phi, ?_⟩
  change carrierTorusActionFun (compactTorusEmbedding phi)
      (carrierModulus (inclusion a z)) = inclusion a z
  rw [carrierModulus_inclusion, carrierTorusActionFun_inclusion, hphi]

open SphereSixComplex.Geometry.CuspLocalPhaseAction

public theorem carrierModulus_mem_cuspNeighborhood_iff (r : ℝ) (x : Carrier) :
    carrierModulus x ∈ cuspNeighborhood constructedModel r ↔
      x ∈ cuspNeighborhood constructedModel r := by
  change carrierHeight (carrierModulus x) ∈ Metric.ball 0 r ↔
    carrierHeight x ∈ Metric.ball 0 r
  rw [carrierHeight_modulus]
  simp only [Metric.mem_ball, dist_zero_right, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _)]

/-- The polar modulus restricted to a constructed cusp neighbourhood. -/
public def constructedLocalModulus (r : ℝ)
    (p : LocalCarrier constructedModel r) : LocalCarrier constructedModel r :=
  ⟨carrierModulus (show Carrier from p.1),
    (carrierModulus_mem_cuspNeighborhood_iff r (show Carrier from p.1)).mpr p.property⟩

public theorem constructedLocalModulus_continuous (r : ℝ) :
    Continuous (constructedLocalModulus r) := by
  rw [continuous_induced_rng]
  exact carrierModulus_continuous.comp continuous_subtype_val

@[simp]
public theorem constructedLocalModulus_coe (r : ℝ) (p : LocalCarrier constructedModel r) :
    (show Carrier from (constructedLocalModulus r p).1) =
      carrierModulus (show Carrier from p.1) :=
  rfl

@[simp]
public theorem constructedLocalModulus_idempotent (r : ℝ)
    (p : LocalCarrier constructedModel r) :
    constructedLocalModulus r (constructedLocalModulus r p) = constructedLocalModulus r p := by
  apply Subtype.ext
  exact carrierModulus_idempotent (show Carrier from p.1)

/-- The fixed-point set of the local modulus. -/
public def constructedLocalPositivePart (r : ℝ) :
    Set (LocalCarrier constructedModel r) :=
  {p | constructedLocalModulus r p = p}

public theorem constructedLocalPositivePart_isClosed (r : ℝ) :
    IsClosed (constructedLocalPositivePart r) := by
  exact isClosed_eq (constructedLocalModulus_continuous r) continuous_id

public theorem mem_constructedLocalPositivePart_iff (r : ℝ)
    (p : LocalCarrier constructedModel r) :
    p ∈ constructedLocalPositivePart r ↔
      (show Carrier from p.1) ∈ carrierPositivePart := by
  change constructedLocalModulus r p = p ↔
    carrierModulus (show Carrier from p.1) = (show Carrier from p.1)
  rw [Subtype.ext_iff]
  rfl

/-- The local modulus as a continuous retraction onto its fixed-point set. -/
public def constructedLocalModulusRetraction (r : ℝ) :
    C(LocalCarrier constructedModel r, constructedLocalPositivePart r) where
  toFun p := ⟨constructedLocalModulus r p, constructedLocalModulus_idempotent r p⟩
  continuous_toFun := (constructedLocalModulus_continuous r).subtype_mk _

public theorem constructedLocalModulusRetraction_fixed (r : ℝ)
    (q : constructedLocalPositivePart r) :
    constructedLocalModulusRetraction r q = q := by
  apply Subtype.ext
  exact q.property

public theorem constructedLocalModulusRetraction_t (r : ℝ)
    (p : LocalCarrier constructedModel r) :
    constructedModel.t (constructedLocalModulusRetraction r p) =
      (‖constructedModel.t p‖ : ℝ) := by
  exact carrierHeight_modulus (show Carrier from p.1)

public theorem constructedLocalModulusRetraction_polar_surjective (r : ℝ)
    (p : LocalCarrier constructedModel r) :
    ∃ phi : CompactTorus,
      constructedModel.torusAction (compactTorusEmbedding phi)
        (constructedLocalModulusRetraction r p) = p := by
  exact exists_compactTorusAction_modulus (show Carrier from p.1)

/-! ## Positive affine charts -/

/-- The closed nonnegative orthant underlying one positive affine chart. -/
public abbrev PositiveOrthant := {u : Fin 3 → ℝ // ∀ i, 0 ≤ u i}

/-- Coordinatewise real inclusion identifies the orthant with the nonnegative complex locus. -/
public def positiveOrthantHomeomorph : PositiveOrthant ≃ₜ nonnegativeCoordinates where
  toFun u := ⟨fun i ↦ (u.1 i : ℂ), ⟨u.1, u.2, rfl⟩⟩
  invFun z := ⟨fun i ↦ (z.1 i).re, by
    obtain ⟨u, hu, hzu⟩ := z.2
    intro i
    change 0 ≤ (z.1 i).re
    rw [show z.1 i = (u i : ℂ) from congrFun hzu i]
    exact hu i⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    simp
  right_inv z := by
    apply Subtype.ext
    obtain ⟨u, _hu, hzu⟩ := z.2
    funext i
    change ((z.1 i).re : ℂ) = z.1 i
    rw [show z.1 i = (u i : ℂ) from congrFun hzu i]
    simp
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact continuous_pi fun i ↦ Complex.continuous_ofReal.comp
      ((continuous_apply i).comp continuous_subtype_val)
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_pi fun i ↦ Complex.continuous_re.comp
      ((continuous_apply i).comp continuous_subtype_val)

/-- The orthant is the exact preimage of the global positive part in every affine chart. -/
public def positiveChartDomainHomeomorph (a : ChartIndex) :
    PositiveOrthant ≃ₜ (inclusion a ⁻¹' carrierPositivePart) :=
  positiveOrthantHomeomorph.trans (Homeomorph.setCongr (Set.ext fun z ↦
    (inclusion_mem_carrierPositivePart_iff a z).symm))

/-- A positive affine chart, obtained by restricting the ambient toric chart. -/
public def carrierPositiveChart (a : ChartIndex) : PositiveOrthant → carrierPositivePart :=
  carrierPositivePart.restrictPreimage (inclusion a) ∘ positiveChartDomainHomeomorph a

public theorem carrierPositiveChart_isOpenEmbedding (a : ChartIndex) :
    IsOpenEmbedding (carrierPositiveChart a) := by
  exact ((inclusion_isOpenEmbedding a).restrictPreimage carrierPositivePart).comp
    (positiveChartDomainHomeomorph a).isOpenEmbedding

/-- The positive affine charts jointly cover the global positive part. -/
public theorem carrierPositiveChart_jointly_surjective (x : carrierPositivePart) :
    ∃ (a : ChartIndex) (u : PositiveOrthant), carrierPositiveChart a u = x := by
  obtain ⟨a, z, hz⟩ := inclusion_jointly_surjective (x : Carrier)
  have hzpos : z ∈ nonnegativeCoordinates := by
    rw [← inclusion_mem_carrierPositivePart_iff a]
    simpa only [hz] using x.property
  let u := positiveOrthantHomeomorph.symm ⟨z, hzpos⟩
  refine ⟨a, u, ?_⟩
  apply Subtype.ext
  change inclusion a ((positiveChartDomainHomeomorph a u :
    inclusion a ⁻¹' carrierPositivePart) : RawCoordinates) = (x : Carrier)
  rw [show ((positiveChartDomainHomeomorph a u :
    inclusion a ⁻¹' carrierPositivePart) : RawCoordinates) = z by
      change ((positiveOrthantHomeomorph u : nonnegativeCoordinates) : RawCoordinates) = z
      simp [u]]
  exact hz

end SphereSixComplex.Geometry.StandardInfiniteA2ToricModel.Construction
