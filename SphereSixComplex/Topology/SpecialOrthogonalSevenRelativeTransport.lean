module

public import SphereSixComplex.Topology.SpecialOrthogonalSevenSphereTransport

/-!
# Relative five-cube lifting for the `SO(7) → S⁶` Stiefel projection

This file lifts relative homotopies of maps from the five-cube through the first-column projection.
A compactness argument from the preceding sphere-transport module supplies a uniform time mesh.
On each mesh slab, the explicit non-antipodal Householder transport lifts the base homotopy.  The
short lifts fix the cube boundary and concatenate to a relative homotopy with the requested
endpoint.

The resulting endpoint-transport theorem is precisely the geometric input needed for exactness at
`π₅(SO(7))`; it does not assert a general homotopy-lifting property.
-/

@[expose] public section

noncomputable section

open ContinuousMap Matrix Set Topology
open scoped Classical MatrixGroups RealInnerProductSpace Topology Topology.Homotopy unitInterval

namespace SphereSixComplex.SpecialOrthogonalSevenStiefel

universe u

section ShortLift

variable {X : Type u} [TopologicalSpace X]
variable {b₀ b₁ : C(X, Sphere6)} {S : Set X}

/-- The non-antipodal pair controlling a short lifted homotopy. -/
public def shortTransportPair (K : b₀.HomotopyRel b₁ S)
    (hne : ∀ z : I × X, rawSphere (b₀ z.2) + rawSphere (K z) ≠ 0)
    (z : I × X) : NonAntipodalPair :=
  ⟨(b₀ z.2, K z), hne z⟩

public theorem continuous_shortTransportPair (K : b₀.HomotopyRel b₁ S)
    (hne : ∀ z : I × X, rawSphere (b₀ z.2) + rawSphere (K z) ≠ 0) :
    Continuous (shortTransportPair K hne) :=
  continuous_induced_rng.mpr
    ((b₀.continuous.comp continuous_snd).prodMk K.continuous)

/-- Endpoint obtained by transporting `e₀` along a short non-antipodal base homotopy. -/
public def shortLiftEndpoint (K : b₀.HomotopyRel b₁ S)
    (hne : ∀ z : I × X, rawSphere (b₀ z.2) + rawSphere (K z) ≠ 0)
    (e₀ : C(X, SO7)) : C(X, SO7) where
  toFun x := sphereTransport (shortTransportPair K hne (1, x)) * e₀ x
  continuous_toFun :=
    (continuous_sphereTransport.comp
      ((continuous_shortTransportPair K hne).comp
        (continuous_const.prodMk continuous_id))).mul e₀.continuous

/-- Explicit lift of a short non-antipodal base homotopy, relative to `S`. -/
public def shortLiftHomotopy (K : b₀.HomotopyRel b₁ S)
    (hne : ∀ z : I × X, rawSphere (b₀ z.2) + rawSphere (K z) ≠ 0)
    (e₀ : C(X, SO7)) :
    e₀.HomotopyRel (shortLiftEndpoint K hne e₀) S where
  toFun z := sphereTransport (shortTransportPair K hne z) * e₀ z.2
  continuous_toFun :=
    (continuous_sphereTransport.comp (continuous_shortTransportPair K hne)).mul
      (e₀.continuous.comp continuous_snd)
  map_zero_left x := by
    have hpair : shortTransportPair K hne (0, x) =
        ⟨(b₀ x, b₀ x), by
          simpa [two_smul ℝ (rawSphere (b₀ x))] using
            (smul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (rawSphere_ne_zero (b₀ x)))⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact K.apply_zero x
    rw [hpair, sphereTransport_self, one_mul]
  map_one_left _ := rfl
  prop' t x hx := by
    have hpair : shortTransportPair K hne (t, x) =
        ⟨(b₀ x, b₀ x), by
          simpa [two_smul ℝ (rawSphere (b₀ x))] using
            (smul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (rawSphere_ne_zero (b₀ x)))⟩ := by
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact K.eq_fst t hx
    change sphereTransport (shortTransportPair K hne (t, x)) * e₀ x = e₀ x
    rw [hpair, sphereTransport_self, one_mul]

/-- The short lifted homotopy projects to the given base homotopy at every time. -/
public theorem firstColumn_shortLiftHomotopy (K : b₀.HomotopyRel b₁ S)
    (hne : ∀ z : I × X, rawSphere (b₀ z.2) + rawSphere (K z) ≠ 0)
    (e₀ : C(X, SO7)) (he₀ : firstColumnMap.comp e₀ = b₀) :
    firstColumnMap.comp (shortLiftHomotopy K hne e₀).toContinuousMap =
      K.toContinuousMap := by
  apply ContinuousMap.ext
  intro z
  change firstColumn
      (sphereTransport (shortTransportPair K hne z) * e₀ z.2) = K z
  have he₀z := ContinuousMap.congr_fun he₀ z.2
  change firstColumn (e₀ z.2) = b₀ z.2 at he₀z
  exact firstColumn_sphereTransport_mul _ _ (by
    simpa [shortTransportPair] using he₀z)

public theorem firstColumn_shortLiftEndpoint (K : b₀.HomotopyRel b₁ S)
    (hne : ∀ z : I × X, rawSphere (b₀ z.2) + rawSphere (K z) ≠ 0)
    (e₀ : C(X, SO7)) (he₀ : firstColumnMap.comp e₀ = b₀) :
    firstColumnMap.comp (shortLiftEndpoint K hne e₀) = b₁ := by
  apply ContinuousMap.ext
  intro x
  change firstColumn (sphereTransport (shortTransportPair K hne (1, x)) * e₀ x) = b₁ x
  have he₀x := ContinuousMap.congr_fun he₀ x
  change firstColumn (e₀ x) = b₀ x at he₀x
  calc
    _ = K (1, x) := firstColumn_sphereTransport_mul _ _ (by
      simpa [shortTransportPair] using he₀x)
    _ = b₁ x := K.apply_one x

/-- A short non-antipodal relative base homotopy transports any lift to a lift of its endpoint. -/
public theorem exists_short_relative_lift (K : b₀.HomotopyRel b₁ S)
    (hne : ∀ z : I × X, rawSphere (b₀ z.2) + rawSphere (K z) ≠ 0)
    (e₀ : C(X, SO7)) (he₀ : firstColumnMap.comp e₀ = b₀) :
    ∃ e₁ : C(X, SO7), firstColumnMap.comp e₁ = b₁ ∧ e₀.HomotopicRel e₁ S :=
  ⟨shortLiftEndpoint K hne e₀, firstColumn_shortLiftEndpoint K hne e₀ he₀,
    ⟨shortLiftHomotopy K hne e₀⟩⟩

end ShortLift

public abbrev Cube5 := I^(Fin 5)

/-- The `k`-th point of the uniform mesh with step `1 / n`, clamped to the unit interval. -/
public def meshTime (n k : ℕ) : I :=
  Set.Icc.addNSMul (show (0 : ℝ) ≤ 1 by norm_num) ((n : ℝ)⁻¹) k

@[simp] public theorem meshTime_zero (n : ℕ) : meshTime n 0 = 0 := by
  apply Subtype.ext
  exact Set.Icc.addNSMul_zero (show (0 : ℝ) ≤ 1 by norm_num)

@[simp] public theorem meshTime_self {n : ℕ} (hn : 0 < n) : meshTime n n = 1 := by
  apply Subtype.ext
  simp [meshTime, Set.Icc.addNSMul, nsmul_eq_mul, hn.ne']

public theorem monotone_meshTime (n : ℕ) : Monotone (meshTime n) :=
  Set.Icc.monotone_addNSMul (show (0 : ℝ) ≤ 1 by norm_num)
    (inv_nonneg.mpr (Nat.cast_nonneg n))

/-- Linear traversal of the `k`-th mesh slab. -/
public def meshSlabTime (n k : ℕ) (t : I) : I :=
  Set.Icc.convexComb (meshTime n k) (meshTime n (k + 1)) t

public theorem continuous_meshSlabTime (n k : ℕ) : Continuous (meshSlabTime n k) := by
  apply Continuous.subtype_mk
  change Continuous fun t : I ↦
    (1 - (t : ℝ)) * (meshTime n k : ℝ) +
      (t : ℝ) * (meshTime n (k + 1) : ℝ)
  fun_prop

@[simp] public theorem meshSlabTime_zero (n k : ℕ) :
    meshSlabTime n k 0 = meshTime n k :=
  Set.Icc.convexComb_zero _ _

@[simp] public theorem meshSlabTime_one (n k : ℕ) :
    meshSlabTime n k 1 = meshTime n (k + 1) :=
  Set.Icc.convexComb_one _ _

public theorem meshSlabTime_mem_meshInterval (n k : ℕ) (t : I) :
    meshSlabTime n k t ∈ Set.Icc (meshTime n k) (meshTime n (k + 1)) := by
  have hab : (meshTime n k : ℝ) ≤ meshTime n (k + 1) :=
    Subtype.coe_le_coe.mpr (monotone_meshTime n (Nat.le_succ k))
  constructor
  · change (meshTime n k : ℝ) ≤ (meshSlabTime n k t : ℝ)
    rw [meshSlabTime, Set.Icc.coe_convexComb]
    have hnonneg : 0 ≤ (t : ℝ) *
        ((meshTime n (k + 1) : ℝ) - (meshTime n k : ℝ)) :=
      mul_nonneg t.2.1 (sub_nonneg.mpr hab)
    nlinarith
  · change (meshSlabTime n k t : ℝ) ≤ (meshTime n (k + 1) : ℝ)
    rw [meshSlabTime, Set.Icc.coe_convexComb]
    have hnonneg : 0 ≤ (1 - (t : ℝ)) *
        ((meshTime n (k + 1) : ℝ) - (meshTime n k : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr t.2.2) (sub_nonneg.mpr hab)
    nlinarith

public theorem dist_meshTime_meshSlabTime_le (n k : ℕ) (t : I) :
    dist (meshTime n k : ℝ) (meshSlabTime n k t : ℝ) ≤ ((n : ℝ)⁻¹) := by
  rw [Real.dist_eq, abs_sub_comm]
  exact Set.Icc.abs_sub_addNSMul_le (show (0 : ℝ) ≤ 1 by norm_num)
    (inv_nonneg.mpr (Nat.cast_nonneg n)) k (meshSlabTime_mem_meshInterval n k t)

/-- The base map at the `k`-th mesh time. -/
public def homotopySlice {b₀ b₁ : C(Cube5, Sphere6)}
    (H : b₀.HomotopyRel b₁ (Cube.boundary (Fin 5))) (n k : ℕ) : C(Cube5, Sphere6) :=
  H.toHomotopy.curry (meshTime n k)

/-- Restriction of a relative homotopy to one affine mesh slab. -/
public def meshSlabHomotopy {b₀ b₁ : C(Cube5, Sphere6)}
    (H : b₀.HomotopyRel b₁ (Cube.boundary (Fin 5))) (n k : ℕ) :
    (homotopySlice H n k).HomotopyRel (homotopySlice H n (k + 1))
      (Cube.boundary (Fin 5)) where
  toFun z := H (meshSlabTime n k z.1, z.2)
  continuous_toFun := H.continuous.comp
    ((continuous_meshSlabTime n k).comp continuous_fst |>.prodMk continuous_snd)
  map_zero_left x := by simp [homotopySlice]
  map_one_left x := by simp [homotopySlice]
  prop' t x hx := by
    change H (meshSlabTime n k t, x) = H (meshTime n k, x)
    rw [H.eq_fst _ hx, H.eq_fst _ hx]

public theorem meshSlabHomotopy_nonAntipodal {b₀ b₁ : C(Cube5, Sphere6)}
    (H : b₀.HomotopyRel b₁ (Cube.boundary (Fin 5)))
    {n : ℕ}
    (hmesh : ∀ {t s : I} {a : Cube5},
      dist (t : ℝ) (s : ℝ) ≤ ((n : ℝ)⁻¹) →
      rawSphere (H (t, a)) + rawSphere (H (s, a)) ≠ 0)
    (k : ℕ) (z : I × Cube5) :
    rawSphere (homotopySlice H n k z.2) +
      rawSphere (meshSlabHomotopy H n k z) ≠ 0 := by
  apply hmesh (dist_meshTime_meshSlabTime_le n k z.1)

/-- Inductively transport a lift through the first `k` slabs of a fixed uniform mesh. -/
public theorem exists_lift_at_meshTime {b₀ b₁ : C(Cube5, Sphere6)}
    (H : b₀.HomotopyRel b₁ (Cube.boundary (Fin 5)))
    (n : ℕ)
    (hmesh : ∀ {t s : I} {a : Cube5},
      dist (t : ℝ) (s : ℝ) ≤ ((n : ℝ)⁻¹) →
      rawSphere (H (t, a)) + rawSphere (H (s, a)) ≠ 0)
    (e₀ : C(Cube5, SO7)) (he₀ : firstColumnMap.comp e₀ = b₀) :
    ∀ (k : ℕ), k ≤ n →
      ∃ eₖ : C(Cube5, SO7),
        firstColumnMap.comp eₖ = homotopySlice H n k ∧
          e₀.HomotopicRel eₖ (Cube.boundary (Fin 5)) := by
  intro k
  induction k with
  | zero =>
      intro _
      refine ⟨e₀, ?_, (ContinuousMap.HomotopicRel.refl e₀ :
        e₀.HomotopicRel e₀ (Cube.boundary (Fin 5)))⟩
      simpa [homotopySlice] using he₀
  | succ k ih =>
      intro hk
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      obtain ⟨eₖ, heₖ, hrelₖ⟩ := ih hk'
      let K := meshSlabHomotopy H n k
      let hne : ∀ z : I × Cube5,
          rawSphere (homotopySlice H n k z.2) + rawSphere (K z) ≠ 0 :=
        meshSlabHomotopy_nonAntipodal H hmesh k
      obtain ⟨eₖ₁, heₖ₁, hshort⟩ :=
        exists_short_relative_lift K hne eₖ heₖ
      exact ⟨eₖ₁, heₖ₁, hrelₖ.trans hshort⟩

/-- The scoped relative endpoint-transport property needed for exactness at `π₅(SO(7))`. -/
public def FiveCubeStiefelRelativeTransport : Prop :=
  ∀ {b₀ b₁ : C(Cube5, Sphere6)},
    b₀.HomotopicRel b₁ (Cube.boundary (Fin 5)) →
    ∀ (e₀ : C(Cube5, SO7)), firstColumnMap.comp e₀ = b₀ →
      ∃ e₁ : C(Cube5, SO7),
        firstColumnMap.comp e₁ = b₁ ∧
          e₀.HomotopicRel e₁ (Cube.boundary (Fin 5))

/-- The first-column Stiefel projection transports relative five-cube lifts through any relative
base homotopy. -/
public theorem fiveCubeStiefelRelativeTransport : FiveCubeStiefelRelativeTransport := by
  intro b₀ b₁ hH e₀ he₀
  let H := hH.some
  obtain ⟨n, hn, hmesh⟩ :=
    exists_uniform_nonAntipodal_time_mesh H.toContinuousMap
  obtain ⟨e₁, he₁, hrel⟩ :=
    exists_lift_at_meshTime H n hmesh e₀ he₀ n le_rfl
  refine ⟨e₁, ?_, hrel⟩
  calc
    firstColumnMap.comp e₁ = homotopySlice H n n := he₁
    _ = b₁ := by
      apply ContinuousMap.ext
      intro a
      simp [homotopySlice, meshTime_self hn]

end SphereSixComplex.SpecialOrthogonalSevenStiefel
