module

public import SphereSixComplex.Topology.SpecialOrthogonalSevenLocalSections

/-!
# Short-step transport for the `SO(7) → S⁶` Stiefel projection

This file constructs a continuous special-orthogonal transformation carrying one point of the
six-sphere to another whenever the two points are not antipodal.  The transformation is the
product of two Householder reflections and specializes to the identity on the diagonal.

It also proves that a homotopy on a compact five-cube admits a uniform finite time mesh on which
consecutive sphere values are non-antipodal.  Together, these results are the local ingredients
for the relative homotopy-lifting argument at `π₅(SO(7))`.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups RealInnerProductSpace Topology Topology.Homotopy unitInterval

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

public theorem rawSphere_ne_zero (x : Sphere6) : rawSphere x ≠ 0 := by
  intro h
  have hu := rawSphere_dot_self x
  rw [h] at hu
  norm_num [dotProduct] at hu

public theorem householder_two_smul (v : V7) (hv : v ≠ 0) :
    householder ((2 : ℝ) • v) = householder v := by
  have hd : dotProduct v v ≠ 0 := dot_self_ne_zero hv
  ext i j
  simp only [householder, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    smul_dotProduct, dotProduct_smul]
  field_simp

/-- Ordered pairs of unit vectors which are not antipodal. -/
public abbrev NonAntipodalPair :=
  {p : Sphere6 × Sphere6 // rawSphere p.1 + rawSphere p.2 ≠ 0}

public def pairSum (p : NonAntipodalPair) : {v : V7 // v ≠ 0} :=
  ⟨rawSphere p.1.1 + rawSphere p.1.2, p.2⟩

public def pairFirst (p : NonAntipodalPair) : {v : V7 // v ≠ 0} :=
  ⟨rawSphere p.1.1, rawSphere_ne_zero p.1.1⟩

public theorem continuous_pairSum : Continuous pairSum :=
  continuous_induced_rng.mpr
    ((continuous_rawSphere.comp (continuous_fst.comp continuous_subtype_val)).add
      (continuous_rawSphere.comp (continuous_snd.comp continuous_subtype_val)))

public theorem continuous_pairFirst : Continuous pairFirst :=
  continuous_induced_rng.mpr
    (continuous_rawSphere.comp (continuous_fst.comp continuous_subtype_val))

/-- The product of Householder reflections which carries the first vector to the second. -/
public def sphereTransportMatrix (p : NonAntipodalPair) : Matrix (Fin 7) (Fin 7) ℝ :=
  householder (pairSum p).1 * householder (pairFirst p).1

public theorem continuous_sphereTransportMatrix : Continuous sphereTransportMatrix :=
  (continuous_householderNonzero.comp continuous_pairSum).mul
    (continuous_householderNonzero.comp continuous_pairFirst)

public theorem sphereTransportMatrix_orthogonal (p : NonAntipodalPair) :
    (sphereTransportMatrix p)ᵀ * sphereTransportMatrix p = 1 := by
  rw [sphereTransportMatrix, Matrix.transpose_mul]
  calc
    (householder (pairFirst p).1)ᵀ * (householder (pairSum p).1)ᵀ *
          (householder (pairSum p).1 * householder (pairFirst p).1) =
        (householder (pairFirst p).1)ᵀ *
          ((householder (pairSum p).1)ᵀ * householder (pairSum p).1) *
            householder (pairFirst p).1 := by simp only [Matrix.mul_assoc]
    _ = (householder (pairFirst p).1)ᵀ * 1 * householder (pairFirst p).1 := by
      rw [householder_orthogonal (pairSum p).2]
    _ = 1 := by simpa using householder_orthogonal (pairFirst p).2

public theorem sphereTransportMatrix_det (p : NonAntipodalPair) :
    (sphereTransportMatrix p).det = 1 := by
  rw [sphereTransportMatrix, Matrix.det_mul,
    householder_det (pairSum p).2, householder_det (pairFirst p).2]
  norm_num

public theorem householder_sum_maps_neg_first (u v : Sphere6)
    (huv : rawSphere u + rawSphere v ≠ 0) :
    householder (rawSphere u + rawSphere v) *ᵥ (-rawSphere u) = rawSphere v := by
  rw [householder_mulVec]
  have hu := rawSphere_dot_self u
  have hv := rawSphere_dot_self v
  have hd := dot_self_ne_zero huv
  ext i
  simp only [add_dotProduct, dotProduct_add, dotProduct_neg,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  simp only [add_dotProduct, dotProduct_add, hu, hv] at hd ⊢
  rw [dotProduct_comm (rawSphere u) (rawSphere v)] at hd ⊢
  field_simp [hd]
  ring

public theorem sphereTransportMatrix_mulVec_first (p : NonAntipodalPair) :
    sphereTransportMatrix p *ᵥ rawSphere p.1.1 = rawSphere p.1.2 := by
  rw [sphereTransportMatrix, ← Matrix.mulVec_mulVec]
  change householder (rawSphere p.1.1 + rawSphere p.1.2) *ᵥ
      (householder (rawSphere p.1.1) *ᵥ rawSphere p.1.1) = rawSphere p.1.2
  rw [householder_mulVec_self (rawSphere_ne_zero p.1.1)]
  exact householder_sum_maps_neg_first p.1.1 p.1.2 p.2

@[simp] public theorem sphereTransportMatrix_self (x : Sphere6) :
    sphereTransportMatrix ⟨(x, x), by
      simpa [two_smul ℝ (rawSphere x)] using
        (smul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (rawSphere_ne_zero x))⟩ = 1 := by
  change householder (rawSphere x + rawSphere x) * householder (rawSphere x) = 1
  rw [← two_smul ℝ (rawSphere x)]
  change householder ((2 : ℝ) • rawSphere x) * householder (rawSphere x) = 1
  rw [householder_two_smul _ (rawSphere_ne_zero x),
    householder_mul_self (rawSphere_ne_zero x)]

public theorem sphereTransportMatrix_mem (p : NonAntipodalPair) :
    sphereTransportMatrix p ∈ SO7 := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨by
    rw [Matrix.mem_orthogonalGroup_iff']
    exact sphereTransportMatrix_orthogonal p,
    sphereTransportMatrix_det p⟩

/-- Continuous special-orthogonal transport between non-antipodal sphere points. -/
public def sphereTransport (p : NonAntipodalPair) : SO7 :=
  ⟨sphereTransportMatrix p, sphereTransportMatrix_mem p⟩

public theorem continuous_sphereTransport : Continuous sphereTransport :=
  continuous_induced_rng.mpr continuous_sphereTransportMatrix

public theorem rawSphere_firstColumn (Q : SO7) :
    rawSphere (firstColumn Q) = Matrix.col (Q : Matrix (Fin 7) (Fin 7) ℝ) 0 := by
  apply WithLp.toLp_injective 2
  rw [toLp_rawSphere]
  rfl

/-- Left multiplication by sphere transport carries a lift of the first point to a lift of the
second point. -/
public theorem firstColumn_sphereTransport_mul (p : NonAntipodalPair) (Q : SO7)
    (hQ : firstColumn Q = p.1.1) :
    firstColumn (sphereTransport p * Q) = p.1.2 := by
  apply Subtype.ext
  change WithLp.toLp 2
      (Matrix.col (((sphereTransport p * Q : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) 0) =
    p.1.2.1
  rw [show (((sphereTransport p * Q : SO7) : Matrix (Fin 7) (Fin 7) ℝ)) =
      sphereTransportMatrix p * (Q : Matrix (Fin 7) (Fin 7) ℝ) by rfl]
  change WithLp.toLp 2
      (sphereTransportMatrix p *ᵥ Matrix.col (Q : Matrix (Fin 7) (Fin 7) ℝ) 0) = p.1.2.1
  rw [← rawSphere_firstColumn Q, hQ, sphereTransportMatrix_mulVec_first,
    toLp_rawSphere]

/-- Transport from a sphere point to itself is the identity. -/
@[simp] public theorem sphereTransport_self (x : Sphere6) :
    sphereTransport ⟨(x, x), by
      simpa [two_smul ℝ (rawSphere x)] using
        (smul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (rawSphere_ne_zero x))⟩ = 1 := by
  apply Subtype.ext
  exact sphereTransportMatrix_self x

public theorem dist_eq_two_of_rawSphere_add_eq_zero (u v : Sphere6)
    (h : rawSphere u + rawSphere v = 0) : dist u v = 2 := by
  have hraw : rawSphere v = -rawSphere u := by
    exact eq_neg_of_add_eq_zero_right h
  have hv : v.1 = -u.1 := by
    rw [← toLp_rawSphere v, hraw]
    change -WithLp.toLp 2 (rawSphere u) = -u.1
    rw [toLp_rawSphere]
  rw [Subtype.dist_eq, hv, dist_eq_norm, sub_neg_eq_add, ← two_smul ℝ u.1,
    norm_smul]
  have hu : ‖u.1‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.2
  rw [hu]
  norm_num

/-- A continuous sphere homotopy admits one fixed time mesh whose consecutive points are
non-antipodal, uniformly over the whole five-cube. -/
public theorem exists_uniform_nonAntipodal_time_mesh
    (H : C(I × I^(Fin 5), Sphere6)) :
    ∃ n : ℕ, 0 < n ∧
      ∀ {t s : I} {a : I^(Fin 5)},
        dist (t : ℝ) (s : ℝ) ≤ ((n : ℝ)⁻¹) →
        rawSphere (H (t, a)) + rawSphere (H (s, a)) ≠ 0 := by
  have huc : UniformContinuous H :=
    CompactSpace.uniformContinuous_of_continuous H.continuous
  obtain ⟨δ, hδ, hH⟩ := Metric.uniformContinuous_iff.mp huc 1 (by norm_num)
  obtain ⟨n, hnpos, hnδ⟩ := Real.exists_nat_pos_inv_lt hδ
  refine ⟨n, hnpos, ?_⟩
  intro t s a hts hantipodal
  have hdom : dist (t, a) (s, a) < δ := by
    rw [Prod.dist_eq]
    rw [dist_self, max_eq_left dist_nonneg]
    simpa only [Subtype.dist_eq] using hts.trans_lt hnδ
  have hout : dist (H (t, a)) (H (s, a)) < 1 := hH hdom
  have heq : dist (H (t, a)) (H (s, a)) = 2 :=
    dist_eq_two_of_rawSphere_add_eq_zero _ _ hantipodal
  linarith

end SphereSixComplex.SpecialOrthogonalSevenStiefel
