module

public import SphereSixComplex.Topology.SingularAffineSubdivisionMesh

/-!
# Relative mesh estimates for affine barycentric subdivision

This file proves the relative (rather than merely intrinsic) mesh estimate.  If the vertices of
an affine parent simplex are `p i`, then the images of the barycenters in any flag of nested
nonempty faces have diameter at most `n / (n + 1)` times the diameter of the parent vertices.
The result is stated first in an arbitrary real normed vector space and then specialized to the
affine self-maps used by iterated singular subdivision.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits PartialOrder Set Simplicial

namespace SphereSixComplex

/-- The centroid of the vertices indexed by a nonempty face. -/
public noncomputable def affineParentFaceCentroid
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Fin (n + 1) → E)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) : E :=
  A.finset.centroid ℝ (fun i ↦ p i.down)

public theorem affineParentFaceCentroid_eq_smul_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Fin (n + 1) → E)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    affineParentFaceCentroid p A =
      (A.finset.card : ℝ)⁻¹ • ∑ i ∈ A.finset, p i.down := by
  unfold affineParentFaceCentroid
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination]
  · simp only [Finset.centroidWeights_apply, Finset.smul_sum]
  · exact A.finset.sum_centroidWeights_eq_one_of_nonempty ℝ A.nonempty

/-- A face centroid belongs to the convex hull of the parent vertices. -/
public theorem affineParentFaceCentroid_mem_convexHull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Fin (n + 1) → E)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    affineParentFaceCentroid p A ∈ convexHull ℝ (Set.range p) := by
  unfold affineParentFaceCentroid
  rw [Finset.centroid_def]
  have h := affineCombination_mem_convexHull
    (s := A.finset) (v := fun i ↦ p i.down)
    (w := A.finset.centroidWeights ℝ)
    (fun i hi ↦ by simp only [Finset.centroidWeights_apply]; positivity)
    (A.finset.sum_centroidWeights_eq_one_of_nonempty ℝ A.nonempty)
  have hrange : Set.range (fun i : ULift.{0} (Fin (n + 1)) ↦ p i.down) =
      Set.range p := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.down, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨ULift.up i, rfl⟩
  rwa [hrange] at h

/-- Translation formula for a parent-face centroid, in vector-space notation. -/
public theorem affineParentFaceCentroid_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Fin (n + 1) → E)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) (c : E) :
    affineParentFaceCentroid p A - c =
      (A.finset.card : ℝ)⁻¹ • ∑ i ∈ A.finset, (p i.down - c) := by
  calc
    affineParentFaceCentroid p A - c =
        affineParentFaceCentroid (fun i ↦ p i - c) A := by
      unfold affineParentFaceCentroid
      simpa only [vsub_eq_sub] using
        (A.finset.centroid_vsub_const ℝ
          (p := fun i ↦ p i.down) (p₀ := c) A.nonempty)
    _ = _ := affineParentFaceCentroid_eq_smul_sum _ _

/-- The unnormalized displacement vectors from a face centroid sum to zero. -/
public theorem sum_sub_affineParentFaceCentroid_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Fin (n + 1) → E)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    ∑ i ∈ A.finset, (p i.down - affineParentFaceCentroid p A) = 0 := by
  have h : (A.finset.card : ℝ)⁻¹ •
      (∑ i ∈ A.finset, (p i.down - affineParentFaceCentroid p A)) = 0 := by
    rw [← affineParentFaceCentroid_sub]
    exact sub_self _
  have hcard : (A.finset.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt A.nonempty.card_pos)
  simpa [hcard] using h

/-- The proportion of vertices introduced between nested nonempty faces is bounded by the
barycentric contraction factor. -/
public theorem card_sub_div_card_le_barycentricContractionFactor
    (n a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ n + 1) :
    ((b - a : ℕ) : ℝ) / (b : ℝ) ≤ barycentricContractionFactor n := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbR : (b : ℝ) ≤ n + 1 := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le zero_lt_one (haR.trans habR)
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hone_div_b_le : (1 : ℝ) / b ≤ a / b :=
    div_le_div_of_nonneg_right haR hbpos.le
  have hone_div_N_le : (1 : ℝ) / (n + 1) ≤ 1 / b := by
    exact one_div_le_one_div_of_le hbpos hbR
  have hratio : (1 : ℝ) / (n + 1) ≤ a / b :=
    hone_div_N_le.trans hone_div_b_le
  have hcast : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by
    exact_mod_cast (Nat.cast_sub hab : ((b - a : ℕ) : ℝ) = b - a)
  have hlhs : ((b : ℝ) - a) / b = 1 - a / b := by
    field_simp
  have hrhs : barycentricContractionFactor n = 1 - 1 / (n + 1 : ℝ) := by
    unfold barycentricContractionFactor
    field_simp
    ring
  rw [hcast, hlhs, hrhs]
  linarith

/-- Centroids of two nested nonempty faces contract by the standard barycentric factor, measured
relative to the diameter of the arbitrary affine parent vertex family. -/
public theorem dist_affineParentFaceCentroid_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (p : Fin (n + 1) → E)
    (A B : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) (hAB : A ≤ B) :
    dist (affineParentFaceCentroid p A) (affineParentFaceCentroid p B) ≤
      barycentricContractionFactor n * Metric.diam (Set.range p) := by
  classical
  let cA := affineParentFaceCentroid p A
  let D := Metric.diam (Set.range p)
  have hbpos : (0 : ℝ) < B.finset.card := by
    exact_mod_cast B.nonempty.card_pos
  have hbinv : 0 ≤ (B.finset.card : ℝ)⁻¹ := by positivity
  have hAsum : ∑ i ∈ A.finset, (p i.down - cA) = 0 := by
    exact sum_sub_affineParentFaceCentroid_eq_zero p A
  have hBsum : ∑ i ∈ B.finset, (p i.down - cA) =
      ∑ i ∈ B.finset \ A.finset, (p i.down - cA) := by
    rw [← Finset.sum_sdiff hAB, hAsum, add_zero]
  have hconvexBounded : Bornology.IsBounded (convexHull ℝ (Set.range p)) := by
    rw [isBounded_convexHull]
    exact (Set.finite_range p).isBounded
  have hterm (i : ULift.{0} (Fin (n + 1))) :
      ‖p i.down - cA‖ ≤ D := by
    have hp : p i.down ∈ convexHull ℝ (Set.range p) :=
      (subset_convexHull ℝ (Set.range p)) (Set.mem_range_self i.down)
    have hc : cA ∈ convexHull ℝ (Set.range p) :=
      affineParentFaceCentroid_mem_convexHull p A
    have hdist := Metric.dist_le_diam_of_mem hconvexBounded hp hc
    rw [convexHull_diam] at hdist
    simpa only [dist_eq_norm] using hdist
  rw [dist_comm, dist_eq_norm, affineParentFaceCentroid_sub, hBsum, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos)]
  calc
    (B.finset.card : ℝ)⁻¹ *
          ‖∑ i ∈ B.finset \ A.finset, (p i.down - cA)‖ ≤
        (B.finset.card : ℝ)⁻¹ *
          ∑ i ∈ B.finset \ A.finset, ‖p i.down - cA‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) hbinv
    _ ≤ (B.finset.card : ℝ)⁻¹ *
          ∑ _i ∈ B.finset \ A.finset, D := by
      apply mul_le_mul_of_nonneg_left _ hbinv
      exact Finset.sum_le_sum fun i _ ↦ hterm i
    _ = (((B.finset \ A.finset).card : ℝ) / B.finset.card) * D := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ = (((B.finset.card - A.finset.card : ℕ) : ℝ) /
          B.finset.card) * D := by
      rw [Finset.card_sdiff_of_subset hAB]
    _ ≤ barycentricContractionFactor n * D := by
      apply mul_le_mul_of_nonneg_right _ (Metric.diam_nonneg)
      exact card_sub_div_card_le_barycentricContractionFactor n
        A.finset.card B.finset.card A.nonempty.card_pos
        (Finset.card_le_card hAB) (by simpa using B.finset.card_le_univ)

/-- The affine combination of a family in a real normed vector space. -/
public noncomputable def normedAffineCombination
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] (p : I → E) (w : stdSimplex ℝ I) : E :=
  ∑ i, w i • p i

/-- Evaluating an affine parent on a face barycenter gives the centroid of the corresponding
parent vertices. -/
public theorem normedAffineCombination_nonemptyFiniteChainBarycenter
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (p : Fin (n + 1) → E)
    (A : NonemptyFiniteChains (ULift.{0} (Fin (n + 1)))) :
    normedAffineCombination p (nonemptyFiniteChainBarycenter A) =
      affineParentFaceCentroid p A := by
  classical
  rw [affineParentFaceCentroid_eq_smul_sum]
  unfold normedAffineCombination
  simp only [nonemptyFiniteChainBarycenter_apply, ite_smul, zero_smul]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  rw [Finset.smul_sum]
  rw [← A.finset.sum_attach]
  symm
  apply Finset.sum_bij (fun i _ ↦ i.1.down)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact i.2
  · intro i₁ hi₁ i₂ hi₂ h
    apply Subtype.ext
    exact ULift.down_injective h
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨⟨ULift.up i, hi⟩, Finset.mem_attach _ _, rfl⟩
  · intro i hi
    rfl

/-- Applying an affine parent after a flag simplex is the affine combination of the images of
the flag's barycenter vertices. -/
public theorem normedAffineCombination_affineFlagContinuousMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n k : ℕ) (p : Fin (n + 1) → E)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k)))
    (w : stdSimplex ℝ (Fin (k + 1))) :
    normedAffineCombination p (affineFlagContinuousMap n k F w) =
      normedAffineCombination
        (fun j ↦ affineParentFaceCentroid p (F.obj j)) w := by
  classical
  unfold normedAffineCombination affineFlagContinuousMap
  change (∑ i, (∑ j, w j * nonemptyFiniteChainBarycenter (F.obj j) i) • p i) =
    ∑ j, w j • affineParentFaceCentroid p (F.obj j)
  simp_rw [← normedAffineCombination_nonemptyFiniteChainBarycenter p (F.obj _)]
  unfold normedAffineCombination
  simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

/-- The parent images of the barycenter vertices in an affine flag. -/
public noncomputable def affineParentFlagVertexSet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n k : ℕ) (p : Fin (n + 1) → E)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) : Set E :=
  Set.range fun j ↦ affineParentFaceCentroid p (F.obj j)

/-- The vertices of a subdivided affine parent satisfy the relative mesh estimate. -/
public theorem diam_affineParentFlagVertexSet_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n k : ℕ) (p : Fin (n + 1) → E)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (affineParentFlagVertexSet n k p F) ≤
      barycentricContractionFactor n * Metric.diam (Set.range p) := by
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (barycentricContractionFactor_nonneg n) Metric.diam_nonneg)
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rcases le_total i j with hij | hji
  · exact dist_affineParentFaceCentroid_le n p _ _
      (CategoryTheory.leOfHom (F.map (CategoryTheory.homOfLE hij)))
  · simpa [dist_comm] using
      dist_affineParentFaceCentroid_le n p _ _
        (CategoryTheory.leOfHom (F.map (CategoryTheory.homOfLE hji)))

/-- Every point in the subdivided affine parent lies in the convex hull of its new vertices. -/
public theorem normedAffineCombination_affineFlag_mem_convexHull_vertices
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n k : ℕ) (p : Fin (n + 1) → E)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k)))
    (w : stdSimplex ℝ (Fin (k + 1))) :
    normedAffineCombination p (affineFlagContinuousMap n k F w) ∈
      convexHull ℝ (affineParentFlagVertexSet n k p F) := by
  rw [normedAffineCombination_affineFlagContinuousMap]
  unfold normedAffineCombination
  have hmem := (convex_convexHull ℝ (affineParentFlagVertexSet n k p F)).sum_mem
    (t := Finset.univ) (w := fun j ↦ w j)
    (z := fun j ↦ affineParentFaceCentroid p (F.obj j))
    (fun j _ ↦ w.2.1 j) w.2.2
    (fun j _ ↦ subset_convexHull ℝ
      (affineParentFlagVertexSet n k p F) ⟨j, rfl⟩)
  simpa only [smul_eq_mul] using hmem

/-- Diameter form of the relative mesh estimate for an arbitrary affine parent in a normed
vector space. -/
public theorem diam_range_normedAffineCombination_affineFlag_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n k : ℕ) (p : Fin (n + 1) → E)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (Set.range fun w ↦
      normedAffineCombination p (affineFlagContinuousMap n k F w)) ≤
      barycentricContractionFactor n * Metric.diam (Set.range p) := by
  calc
    Metric.diam (Set.range fun w ↦
        normedAffineCombination p (affineFlagContinuousMap n k F w)) ≤
        Metric.diam (convexHull ℝ (affineParentFlagVertexSet n k p F)) := by
      apply Metric.diam_mono
      · rintro _ ⟨w, rfl⟩
        exact normedAffineCombination_affineFlag_mem_convexHull_vertices n k p F w
      · rw [isBounded_convexHull]
        exact (Set.finite_range fun j ↦ affineParentFaceCentroid p (F.obj j)).isBounded
    _ = Metric.diam (affineParentFlagVertexSet n k p F) :=
      convexHull_diam _
    _ ≤ _ := diam_affineParentFlagVertexSet_le n k p F

/-- An affine combination evaluated at a standard-simplex vertex returns that vertex's image. -/
@[simp]
public theorem stdSimplexAffineCombination_vertex
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
    (p : X → stdSimplex ℝ Y) (i : X) :
    stdSimplexAffineCombination p (stdSimplex.vertex i) = p i := by
  classical
  ext y
  simp [stdSimplexAffineCombination_apply, Pi.single_apply]

/-- Coercing a standard-simplex affine combination to its ambient vector space gives the
corresponding normed-space affine combination. -/
public theorem coe_stdSimplexAffineCombination_eq_normedAffineCombination
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → stdSimplex ℝ Y) (w : stdSimplex ℝ X) :
    (stdSimplexAffineCombination p w : Y → ℝ) =
      normedAffineCombination (fun i ↦ (p i : Y → ℝ)) w := by
  ext y
  simp only [stdSimplexAffineCombination_apply, normedAffineCombination,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The affine map determined by vertices in a standard simplex. -/
public noncomputable def affineParentContinuousMap
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X → stdSimplex ℝ Y) :
    C(stdSimplex ℝ X, stdSimplex ℝ Y) :=
  ⟨stdSimplexAffineCombination p, continuous_stdSimplexAffineCombination p⟩

/-- Subdividing an arbitrary affine parent simplex contracts its image diameter by at most the
standard barycentric factor. -/
public theorem diam_range_affineParentContinuousMap_comp_affineFlag_le
    (n k : ℕ) (p : Fin (n + 1) → stdSimplex ℝ (Fin (n + 1)))
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    Metric.diam (Set.range
      ((affineParentContinuousMap p).comp (affineFlagContinuousMap n k F))) ≤
      barycentricContractionFactor n *
        Metric.diam (Set.range (affineParentContinuousMap p)) := by
  classical
  let p' : Fin (n + 1) → (Fin (n + 1) → ℝ) :=
    fun i ↦ (p i : Fin (n + 1) → ℝ)
  let s : Set (Fin (n + 1) → ℝ) := Set.range fun w ↦
    normedAffineCombination p' (affineFlagContinuousMap n k F w)
  have hsbounded : Bornology.IsBounded s := by
    apply (show Bornology.IsBounded
      (convexHull ℝ (affineParentFlagVertexSet n k p' F)) by
        rw [isBounded_convexHull]
        exact (Set.finite_range fun j ↦
          affineParentFaceCentroid p' (F.obj j)).isBounded).subset
    rintro _ ⟨w, rfl⟩
    exact normedAffineCombination_affineFlag_mem_convexHull_vertices n k p' F w
  have hpoint (w w' : stdSimplex ℝ (Fin (k + 1))) :
      dist (normedAffineCombination p' (affineFlagContinuousMap n k F w))
          (normedAffineCombination p' (affineFlagContinuousMap n k F w')) ≤
        barycentricContractionFactor n * Metric.diam (Set.range p') := by
    exact (Metric.dist_le_diam_of_mem hsbounded ⟨w, rfl⟩ ⟨w', rfl⟩).trans
      (diam_range_normedAffineCombination_affineFlag_le n k p' F)
  have hpdiam : Metric.diam (Set.range p') = Metric.diam (Set.range p) := by
    have himage :
        (Subtype.val : stdSimplex ℝ (Fin (n + 1)) → Fin (n + 1) → ℝ) ''
            Set.range p = Set.range p' := by
      ext x
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨p i, ⟨i, rfl⟩, rfl⟩
    rw [← himage, isometry_subtype_coe.diam_image]
  have hvertices : Set.range p ⊆ Set.range (affineParentContinuousMap p) := by
    rintro _ ⟨i, rfl⟩
    exact ⟨stdSimplex.vertex i, stdSimplexAffineCombination_vertex p i⟩
  have hparentdiam : Metric.diam (Set.range p) ≤
      Metric.diam (Set.range (affineParentContinuousMap p)) := by
    apply Metric.diam_mono hvertices
    exact isCompact_univ.isBounded.subset (Set.subset_univ _)
  apply Metric.diam_le_of_forall_dist_le
    (mul_nonneg (barycentricContractionFactor_nonneg n) Metric.diam_nonneg)
  rintro _ ⟨w, rfl⟩ _ ⟨w', rfl⟩
  change dist
      (stdSimplexAffineCombination p (affineFlagContinuousMap n k F w) :
        Fin (n + 1) → ℝ)
      (stdSimplexAffineCombination p (affineFlagContinuousMap n k F w') :
        Fin (n + 1) → ℝ) ≤ _
  rw [coe_stdSimplexAffineCombination_eq_normedAffineCombination,
    coe_stdSimplexAffineCombination_eq_normedAffineCombination]
  change dist
      (normedAffineCombination p' (affineFlagContinuousMap n k F w))
      (normedAffineCombination p' (affineFlagContinuousMap n k F w')) ≤ _
  exact (hpoint w w').trans <| by
    rw [hpdiam]
    exact mul_le_mul_of_nonneg_left hparentdiam
      (barycentricContractionFactor_nonneg n)

/-- Associativity of standard-simplex affine combinations. -/
public theorem stdSimplexAffineCombination_assoc
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (p : I → stdSimplex ℝ K) (q : J → stdSimplex ℝ I)
    (w : stdSimplex ℝ J) :
    stdSimplexAffineCombination p (stdSimplexAffineCombination q w) =
      stdSimplexAffineCombination
        (fun j ↦ stdSimplexAffineCombination p (q j)) w := by
  classical
  ext z
  simp only [stdSimplexAffineCombination_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Composition of two explicitly affine standard-simplex maps is explicitly affine. -/
public theorem affineParentContinuousMap_comp
    {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (p : I → stdSimplex ℝ K) (q : J → stdSimplex ℝ I) :
    (affineParentContinuousMap p).comp (affineParentContinuousMap q) =
      affineParentContinuousMap
        (fun j ↦ affineParentContinuousMap p (q j)) := by
  apply ContinuousMap.ext
  intro w
  exact stdSimplexAffineCombination_assoc p q w

/-- The flag map itself is the affine map determined by its face-barycenter vertices. -/
public theorem affineFlagContinuousMap_eq_affineParentContinuousMap
    (n k : ℕ)
    (F : (SimplexCategory.sd.{0}.obj (SimplexCategory.mk n)).obj
      (Opposite.op (SimplexCategory.mk k))) :
    affineFlagContinuousMap n k F =
      affineParentContinuousMap
        (fun j ↦ nonemptyFiniteChainBarycenter (F.obj j)) :=
  rfl

/-- An iterated affine cell is still the affine map determined by the images of the original
vertices. -/
public theorem iteratedAffineCellMap_eq_affineParentContinuousMap_vertices
    (n : ℕ) (ancestry : List (TopAffineFlag n)) :
    iteratedAffineCellMap n ancestry =
      affineParentContinuousMap
        (fun i ↦ iteratedAffineCellMap n ancestry (stdSimplex.vertex i)) := by
  classical
  induction ancestry with
  | nil =>
      apply ContinuousMap.ext
      intro w
      ext y
      simp [affineParentContinuousMap, stdSimplexAffineCombination_apply,
        Pi.single_apply]
  | cons F ancestry ih =>
      rw [iteratedAffineCellMap_cons, ih,
        affineFlagContinuousMap_eq_affineParentContinuousMap,
        affineParentContinuousMap_comp]
      congr 1
      funext i
      simp [affineParentContinuousMap]

/-- The relative mesh contraction property required by the iterated-cell argument holds
unconditionally for every positive-dimensional standard simplex. -/
public theorem affineFlagRelativeMeshContraction
    (n : ℕ) : AffineFlagRelativeMeshContraction n := by
  intro ancestry F
  rw [iteratedAffineCellMap_eq_affineParentContinuousMap_vertices n ancestry]
  exact diam_range_affineParentContinuousMap_comp_affineFlag_le n n
    (fun i ↦ iteratedAffineCellMap n ancestry (stdSimplex.vertex i)) F

/-- Every iterated affine cell satisfies the power-law diameter bound, with no relative-mesh
hypothesis left to discharge. -/
public theorem diam_range_iteratedAffineCellMap_le_pow_unconditional
    (n : ℕ) (hn : 1 ≤ n) (ancestry : List (TopAffineFlag n)) :
    Metric.diam (Set.range (iteratedAffineCellMap n ancestry)) ≤
      barycentricContractionFactor n ^ ancestry.length :=
  diam_range_iteratedAffineCellMap_le_pow n hn
    (affineFlagRelativeMeshContraction n) ancestry

/-- At a common sufficiently large ancestry depth, every iterated affine cell of a singular
simplex is subordinate to a prescribed open cover. -/
public theorem exists_iteratedAffineCell_depth_subordinate_unconditional
    {ι : Type} (X : TopCat.{0}) (U : ι → Set X)
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ)
    (n : ℕ) (hn : 1 ≤ n)
    (x : (TopCat.toSSet.obj X).obj
      (Opposite.op (SimplexCategory.mk n))) :
    ∃ m : ℕ, ∀ ancestry : List (TopAffineFlag n), ancestry.length = m →
      ∃ i, X.toSSetObjEquiv _ x ''
        Set.range (iteratedAffineCellMap n ancestry) ⊆ U i :=
  exists_iteratedAffineCell_depth_subordinate X U hUopen hUcover n hn
    (affineFlagRelativeMeshContraction n) x

end SphereSixComplex
